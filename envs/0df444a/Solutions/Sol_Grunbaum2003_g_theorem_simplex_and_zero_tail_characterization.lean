-- Prove2me | solution 1 for Grunbaum2003.g_theorem_simplex_and_zero_tail_characterization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:29:00.619638+00:00
-- url     : https://prove2.me/submissions/85b5ab53-7f0f-440f-80f8-941c0f868f0b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_columns_mSequence_and_simplex_realization
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators Classical

namespace Grunbaum2003

lemma isMSequence_succ_eq_zero_of_eq_zero {m : ℕ} {g : ℕ → ℕ}
    (hg : IsMSequence m g) {k : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ m)
    (hprev : g (k - 1) = 0) :
    g k = 0 := by
  rcases hg.2 k hk_pos hk_le with hzero | ⟨i, a, hi_pos, hik, hia, _, _, hbound⟩
  · exact hzero
  · exfalso
    have hi_mem : i ∈ Finset.Icc i k := Finset.mem_Icc.2 ⟨le_rfl, hik⟩
    have hchoose_pos : 0 < Nat.choose (a i - 1) (i - 1) :=
      Nat.choose_pos (Nat.sub_le_sub_right hia 1)
    have hle_sum : Nat.choose (a i - 1) (i - 1) ≤
        ∑ r ∈ Finset.Icc i k, Nat.choose (a r - 1) (r - 1) :=
      Finset.single_le_sum (f := fun r => Nat.choose (a r - 1) (r - 1))
        (fun _ _ => Nat.zero_le _) hi_mem
    omega

lemma isMSequence_eq_zero_of_le {m : ℕ} {g : ℕ → ℕ}
    (hg : IsMSequence m g) {k₀ : ℕ} (hk₀ : g k₀ = 0) :
    ∀ k : ℕ, k₀ ≤ k → k ≤ m → g k = 0 := by
  intro k hk₀k hkm
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk₀k
  induction t with
  | zero => simpa using hk₀
  | succ t ih =>
    have ht_le : k₀ + t ≤ m := by omega
    have hprev : g (k₀ + t) = 0 := ih (Nat.le_add_right k₀ t) ht_le
    have hpos : 0 < k₀ + (t + 1) := by omega
    have hsub : k₀ + (t + 1) - 1 = k₀ + t := by omega
    have hstep := isMSequence_succ_eq_zero_of_eq_zero hg hpos hkm
    rw [hsub] at hstep
    exact hstep hprev

lemma g_theorem_sufficiency_of_g1_eq_zero (d : ℕ) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : g 1 = 0) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  have hBridge := Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
  obtain ⟨P, g₀, hP, hg₀, hg₀1, hP_f⟩ := hBridge.2.2.2.2.2.1 d
  refine ⟨P, hP, fun j => ?_⟩
  rw [hP_f j]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · rw [hg.1, hg₀.1]
  · have hgi : g i = 0 := isMSequence_eq_zero_of_le hg hg1 i hi_pos hi_le
    have hg₀i : g₀ i = 0 := isMSequence_eq_zero_of_le hg₀ hg₀1 i hi_pos hi_le
    rw [hgi, hg₀i]

lemma g_theorem_necessity_of_vertex_count_le (d : ℕ) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_le : faceCount P 0 ≤ d + 1) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP.1
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P
  have hSimplex := Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose
  have hBridge := Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
  have hV_ge : d + 1 ≤ faceCount P 0 := hVBound.2 hP.1
  have hV_eq : faceCount P 0 = d + 1 := le_antisymm hV_le hV_ge
  let V_set : Set (Fin d → ℝ) := {x : Fin d → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  let V : Finset (Fin d → ℝ) := hV_fin.toFinset
  have hV_coe : (V : Set (Fin d → ℝ)) = V_set := hV_fin.coe_toFinset
  have hV_card : V.card = d + 1 := by
    rw [← Set.ncard_eq_toFinset_card V_set hV_fin, ← hVBound.1, hV_eq]
  have hP_eq_V : P = convexHull ℝ (V : Set (Fin d → ℝ)) := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    have hsub : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
    rw [Set.inter_eq_self_of_subset_right hsub, ← hV_coe] at h1
    exact h1
  let eV : Fin (d + 1) ≃ V := (Finset.equivFinOfCardEq hV_card).symm
  let v : Fin (d + 1) → Fin d → ℝ := fun i => (eV i).val
  have hRange_v : Set.range v = (V : Set (Fin d → ℝ)) := by
    ext x
    simp only [Set.mem_range, v]
    constructor
    · rintro ⟨i, rfl⟩; exact (eV i).property
    · intro hx; exact ⟨eV.symm ⟨x, hx⟩, by simp⟩
  have hAff : AffineIndependent ℝ v := by
    have hSpanP : affineSpan ℝ P = ⊤ := hP.1.2
    rw [hP_eq_V, affineSpan_convexHull, ← hRange_v] at hSpanP
    rw [affineIndependent_iff_linearIndependent_vsub ℝ v 0]
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · have hdir : (affineSpan ℝ (Set.range v)).direction = ⊤ := by
        rw [hSpanP]; exact AffineSubspace.direction_top ℝ (Fin d → ℝ) (Fin d → ℝ)
      rw [direction_affineSpan,
        vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self (0 : Fin (d + 1)))] at hdir
      rw [← hdir]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i = 0
      · subst hi; simp
      · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique,
        Module.finrank_fin_fun]
      omega
  have hFaceChoose : ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1) := by
    intro k
    rw [hP_eq_V, ← hRange_v]
    exact (hSimplex.2.2.1 d v hAff).2 k
  let g : ℕ → ℕ := fun j => if j = 0 then 1 else if j = 1 then 0 else 0
  have hg_mseq : IsMSequence (d / 2) g := hBridge.2.2.2.1 (d / 2) 0
  have hg1 : g 1 = 0 := rfl
  refine ⟨g, hg_mseq, fun j => ?_⟩
  rw [hFaceChoose j.val]
  have hSum_eq : ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val =
      (g 0 : ℤ) * gTheoremMatrix d 0 j.succ.val := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro i hi hi0
      have hi_le : i ≤ d / 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have hgi : g i = 0 := isMSequence_eq_zero_of_le hg_mseq hg1 i hi_pos hi_le
      simp [hgi]
    · intro h0_not
      exfalso
      exact h0_not (Finset.mem_range.2 (Nat.succ_pos _))
  rw [hSum_eq]
  have hg0 : g 0 = 1 := rfl
  rw [hg0, Int.ofNat_one, one_mul, hBridge.1 d j.succ]
  rfl

end Grunbaum2003

open Grunbaum2003

theorem solution :
    (∀ {m : ℕ} {g : ℕ → ℕ}, IsMSequence m g →
      ∀ {k₀ : ℕ}, g k₀ = 0 → ∀ k : ℕ, k₀ ≤ k → k ≤ m → g k = 0) ∧
    (∀ (d : ℕ) (g : ℕ → ℕ), IsMSequence (d / 2) g → g 1 = 0 →
      ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) ∧
    (∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      IsSimplicialDPolytope P → faceCount P 0 ≤ d + 1 →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) :=
  ⟨fun hg _ hk₀ => isMSequence_eq_zero_of_le hg hk₀,
   g_theorem_sufficiency_of_g1_eq_zero,
   g_theorem_necessity_of_vertex_count_le⟩
