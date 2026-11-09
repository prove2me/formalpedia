-- Prove2me | solution 1 for Grunbaum2003.simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:41:14.85022+00:00
-- url     : https://prove2.me/submissions/9fafe8fb-0f89-4d41-b2f5-e3b3d9391975

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_simplicial_facet_exposed_vertices_and_cardinality
import Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
import Theorems.Thm_Grunbaum2003_improving_edge_and_global_facet_from_ridge_pairs
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

set_option autoImplicit false
open scoped BigOperators
open Classical

namespace Grunbaum2003

lemma exposed_eq_convexHull_filter_3d {n : ℕ} (s : Finset (Fin n → ℝ)) {F : Set (Fin n → ℝ)}
    [DecidablePred (· ∈ F)]
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F) :
    F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨l, hFl⟩ := hF ⟨x, hx⟩
    have hxP : x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := by
      rw [hFl] at hx; exact hx.1
    have hxl : ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x := by
      rw [hFl] at hx; exact hx.2
    rw [Finset.convexHull_eq] at hxP ⊢
    rcases hxP with ⟨w, hw0, hw1, hcm⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id hw1] at hcm
    have hcm' : ∑ z ∈ s, w z • z = x := hcm
    have h_zero : ∀ y ∈ s, y ∉ F → w y = 0 := by
      intro y hy hyF
      by_contra hwy
      have hwy_pos : 0 < w y := lt_of_le_of_ne (hw0 y hy) (Ne.symm hwy)
      have hyP : y ∈ convexHull ℝ (s : Set (Fin n → ℝ)) := subset_convexHull ℝ _ hy
      have hlt : l y < l x := by
        refine lt_of_le_of_ne (hxl y hyP) (fun heq => hyF ?_)
        rw [hFl]
        exact ⟨hyP, fun z hz => by linarith [hxl z hz]⟩
      have hsum_lt : ∑ z ∈ s, w z * l z < ∑ z ∈ s, w z * l x := by
        apply Finset.sum_lt_sum
        · intro z hz
          exact mul_le_mul_of_nonneg_left (hxl z (subset_convexHull ℝ _ hz)) (hw0 z hz)
        · exact ⟨y, hy, mul_lt_mul_of_pos_left hlt hwy_pos⟩
      have hsum_eq : ∑ z ∈ s, w z * l z = l x := by
        calc ∑ z ∈ s, w z * l z = ∑ z ∈ s, l (w z • z) := by
              refine Finset.sum_congr rfl (fun z _ => ?_)
              rw [l.map_smul, smul_eq_mul]
          _ = l (∑ z ∈ s, w z • z) := (map_sum l _ _).symm
          _ = l x := by rw [hcm']
      have hsum_rhs : ∑ z ∈ s, w z * l x = l x := by
        rw [← Finset.sum_mul, hw1, one_mul]
      linarith
    have h_sum1 : ∑ y ∈ s.filter (· ∈ F), w y = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' =>
        h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)))
    refine ⟨w, fun y hy => hw0 y (Finset.mem_of_mem_filter y hy), h_sum1, ?_⟩
    rw [Finset.centerMass_eq_of_sum_1 _ id h_sum1]
    change ∑ y ∈ s.filter (· ∈ F), w y • y = x
    rw [← hcm']
    exact Finset.sum_subset (Finset.filter_subset _ s) (fun y hy hy' => by
      rw [h_zero y hy (fun h => hy' (Finset.mem_filter.2 ⟨hy, h⟩)), zero_smul])
  · refine convexHull_min ?_ (hF.convex (convex_convexHull ℝ _))
    intro x hx
    exact (Finset.mem_filter.1 hx).2

lemma isExposed_of_eq_max_on_finset_3d {n : ℕ} (s : Finset (Fin n → ℝ))
    (l : StrongDual ℝ (Fin n → ℝ)) (M : ℝ)
    (hle : ∀ y ∈ s, l y ≤ M) (hm : ∃ y₀ ∈ s, l y₀ = M) :
    let P := convexHull ℝ (s : Set (Fin n → ℝ))
    let F := convexHull ℝ ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
    (∀ x ∈ P, l x ≤ M) ∧
    F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} ∧
    IsExposed ℝ P F := by
  intro P F
  rcases hm with ⟨y₀, hy₀, hy₀M⟩
  have hP_le : ∀ x ∈ P, l x ≤ M := by
    have hsub : (s : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | l x ≤ M} := fun y hy => hle y hy
    have hconv : Convex ℝ {x : Fin n → ℝ | l x ≤ M} :=
      convex_halfSpace_le (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_sub_P : F ⊆ P := convexHull_mono (by
    intro y hy
    exact (Finset.mem_filter.1 hy).1)
  have hF_eq_M : ∀ x ∈ F, l x = M := by
    have hsub : ((s.filter (fun y => l y = M) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | l x = M} := fun y hy => (Finset.mem_filter.1 hy).2
    have hconv : Convex ℝ {x : Fin n → ℝ | l x = M} :=
      convex_hyperplane (l : (Fin n → ℝ) →ₗ[ℝ] ℝ).isLinear M
    exact fun x hx => convexHull_min hsub hconv hx
  have hF_eq : F = {x ∈ P | ∀ y ∈ P, l y ≤ l x} := by
    apply Set.Subset.antisymm
    · intro x hx
      refine ⟨hF_sub_P hx, fun y hy => ?_⟩
      linarith [hP_le y hy, hF_eq_M x hx]
    · intro x hx
      have hExp : IsExposed ℝ P {z ∈ P | ∀ y ∈ P, l y ≤ l z} := fun _ => ⟨l, rfl⟩
      have hfilt := exposed_eq_convexHull_filter_3d s hExp
      rw [hfilt] at hx
      refine convexHull_mono ?_ hx
      intro y hy
      have hy' := Finset.mem_filter.1 hy
      refine Finset.mem_filter.2 ⟨hy'.1, le_antisymm (hle y hy'.1) ?_⟩
      have h1 : l y₀ ≤ l y := hy'.2.2 y₀ (subset_convexHull ℝ _ hy₀)
      linarith
  refine ⟨hP_le, hF_eq, fun _ => ⟨l, hF_eq⟩⟩

lemma isExposed_trans_of_convexHull_3d {n : ℕ} (s : Finset (Fin n → ℝ))
    {F G : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) F)
    (hG : IsExposed ℝ F G) :
    IsExposed ℝ (convexHull ℝ (s : Set (Fin n → ℝ))) G := by
  intro hGne
  have hGF : G ⊆ F := hG.subset
  have hFne : F.Nonempty := hGne.mono hGF
  have hFs : F = convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    exposed_eq_convexHull_filter_3d s hF
  have hGs : G = convexHull ℝ (((s.filter (· ∈ F)).filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    have hG' : IsExposed ℝ (convexHull ℝ ((s.filter (· ∈ F) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))) G := by
      rwa [← hFs]
    exact exposed_eq_convexHull_filter_3d (s.filter (· ∈ F)) hG'
  have hfilt_eq : (s.filter (· ∈ F)).filter (· ∈ G) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_assoc, and_congr_right_iff]
    intro _
    exact ⟨fun h => h.2, fun h => ⟨hGF h, h⟩⟩
  have hGs' : G = convexHull ℝ ((s.filter (· ∈ G) : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    hGs.trans (by rw [hfilt_eq])
  have hsG_ne : (s.filter (· ∈ G)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hGs', hemp, Finset.coe_empty, convexHull_empty] at hGne
    exact Set.not_nonempty_empty hGne
  rcases hsG_ne with ⟨y₀, hy₀⟩
  have hy₀_mem : y₀ ∈ s ∧ y₀ ∈ G := Finset.mem_filter.1 hy₀
  have hy₀F : y₀ ∈ F := hGF hy₀_mem.2
  obtain ⟨l, hFl⟩ := hF hFne
  obtain ⟨m, hGm⟩ := hG hGne
  let M_l : ℝ := l y₀
  let M_m : ℝ := m y₀
  have hl_le : ∀ y ∈ s, l y ≤ M_l := by
    intro y hy
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ z ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l z ≤ l x} := by
      rw [← hFl]; exact hy₀F
    exact hy₀'.2 y (subset_convexHull ℝ _ hy)
  have hl_lt : ∀ y ∈ s, y ∉ F → l y < M_l := by
    intro y hy hyF
    refine lt_of_le_of_ne (hl_le y hy) (fun heq => hyF ?_)
    rw [hFl]
    refine ⟨subset_convexHull ℝ _ hy, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hy₀F
    linarith [hy₀'.2 z hz]
  have hl_eq : ∀ y ∈ s, y ∈ F → l y = M_l := by
    intro y hy hyF
    have hy' : y ∈ {x ∈ convexHull ℝ (s : Set (Fin n → ℝ)) | ∀ w ∈ convexHull ℝ (s : Set (Fin n → ℝ)), l w ≤ l x} := by
      rw [← hFl]; exact hyF
    exact le_antisymm (hl_le y hy) (hy'.2 y₀ (subset_convexHull ℝ _ hy₀_mem.1))
  have hm_le : ∀ y ∈ s, y ∈ F → m y ≤ M_m := by
    intro y _ hyF
    have hy₀' : y₀ ∈ {x ∈ F | ∀ z ∈ F, m z ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    exact hy₀'.2 y hyF
  have hm_lt : ∀ y ∈ s, y ∈ F → y ∉ G → m y < M_m := by
    intro y hy hyF hyG
    refine lt_of_le_of_ne (hm_le y hy hyF) (fun heq => hyG ?_)
    rw [hGm]
    refine ⟨hyF, fun z hz => ?_⟩
    have hy₀' : y₀ ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hy₀_mem.2
    linarith [hy₀'.2 z hz]
  have hm_eq : ∀ y ∈ s, y ∈ G → m y = M_m := by
    intro y hy hyG
    have hy' : y ∈ {x ∈ F | ∀ w ∈ F, m w ≤ m x} := by
      rw [← hGm]; exact hyG
    exact le_antisymm (hm_le y hy (hGF hyG)) (hy'.2 y₀ hy₀F)
  let term : (Fin n → ℝ) → ℝ := fun z => (1 + (m z - M_m) ^ 2) / (M_l - l z)
  let C : ℝ := 1 + ∑ y ∈ s.filter (· ∉ F), term y
  let h : StrongDual ℝ (Fin n → ℝ) := C • l + m
  have hh_val : ∀ y ∈ s, (y ∈ G → h y = C * M_l + M_m) ∧ (y ∉ G → h y < C * M_l + M_m) := by
    intro y hy
    change (y ∈ G → C * l y + m y = C * M_l + M_m) ∧ (y ∉ G → C * l y + m y < C * M_l + M_m)
    refine ⟨fun hyG => by rw [hl_eq y hy (hGF hyG), hm_eq y hy hyG], fun hyG => ?_⟩
    by_cases hyF : y ∈ F
    · rw [hl_eq y hy hyF]
      linarith [hm_lt y hy hyF hyG]
    · have hy_mem : y ∈ s.filter (· ∉ F) := Finset.mem_filter.2 ⟨hy, hyF⟩
      have hpos : 0 < M_l - l y := sub_pos.2 (hl_lt y hy hyF)
      have hterm_le : term y ≤ ∑ z ∈ s.filter (· ∉ F), term z := by
        refine Finset.single_le_sum (fun z hz => ?_) hy_mem
        have hz' := Finset.mem_filter.1 hz
        have hzpos : 0 < M_l - l z := sub_pos.2 (hl_lt z hz'.1 hz'.2)
        dsimp [term]
        positivity
      have hC_gt : (1 + (m y - M_m) ^ 2) / (M_l - l y) < C := by
        change term y < 1 + ∑ z ∈ s.filter (· ∉ F), term z
        linarith
      have hmul : 1 + (m y - M_m) ^ 2 < C * (M_l - l y) :=
        (div_lt_iff₀ hpos).1 hC_gt
      have hsq : m y - M_m < 1 + (m y - M_m) ^ 2 := by
        nlinarith [(sq_nonneg (m y - M_m - 1 / 2))]
      linarith
  have hh_le : ∀ y ∈ s, h y ≤ C * M_l + M_m := by
    intro y hy
    by_cases hyG : y ∈ G
    · exact le_of_eq ((hh_val y hy).1 hyG)
    · exact le_of_lt ((hh_val y hy).2 hyG)
  have hh_eq_G : s.filter (fun y => h y = C * M_l + M_m) = s.filter (· ∈ G) := by
    ext y
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hy
    exact ⟨fun heq => by_contra (fun hyG => ne_of_lt ((hh_val y hy).2 hyG) heq),
      fun hyG => (hh_val y hy).1 hyG⟩
  have hexp := isExposed_of_eq_max_on_finset_3d s h (C * M_l + M_m) hh_le
    ⟨y₀, hy₀_mem.1, (hh_val y₀ hy₀_mem.1).1 hy₀_mem.2⟩
  rcases hexp with ⟨_, _, hExp⟩
  rw [hh_eq_G, ← hGs'] at hExp
  exact hExp hGne

/-- For any finite set of distinct pairs, there exists a continuous linear functional separating
every pair in the set. -/
lemma exists_linear_separating_pairs {n : ℕ}
    (pairs : Finset ((Fin n → ℝ) × (Fin n → ℝ)))
    (hpairs : ∀ p ∈ pairs, p.1 ≠ p.2) :
    ∃ l : StrongDual ℝ (Fin n → ℝ), ∀ p ∈ pairs, l p.1 ≠ l p.2 := by
  induction pairs using Finset.induction_on with
  | empty => exact ⟨0, fun p hp => by simp at hp⟩
  | @insert p₀ s hp₀ ih =>
    have hp₀_ne : p₀.1 ≠ p₀.2 := hpairs p₀ (Finset.mem_insert_self p₀ s)
    obtain ⟨l', hl'⟩ := ih (fun p hp => hpairs p (Finset.mem_insert_of_mem hp))
    by_cases hl'p₀ : l' p₀.1 ≠ l' p₀.2
    · refine ⟨l', fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hps
      · exact hl'p₀
      · exact hl' p hps
    · have hl'p₀_eq : l' p₀.1 = l' p₀.2 := not_ne_iff.1 hl'p₀
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hp₀_ne
      let m : StrongDual ℝ (Fin n → ℝ) := ContinuousLinearMap.proj i
      have hmp₀ : m p₀.1 ≠ m p₀.2 := hi
      let term : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
        fun p => |m p.1 - m p.2| / |l' p.1 - l' p.2|
      let C : ℝ := 1 + ∑ p ∈ s, term p
      refine ⟨C • l' + m, fun p hp => ?_⟩
      change C * l' p.1 + m p.1 ≠ C * l' p.2 + m p.2
      rcases Finset.mem_insert.1 hp with rfl | hps
      · rw [hl'p₀_eq]
        intro heq
        apply hmp₀
        linarith
      · have hne : l' p.1 - l' p.2 ≠ 0 := sub_ne_zero.2 (hl' p hps)
        have hpos : 0 < |l' p.1 - l' p.2| := abs_pos.2 hne
        have hterm_le : term p ≤ ∑ q ∈ s, term q := by
          refine Finset.single_le_sum (fun q hq => ?_) hps
          dsimp [term]
          positivity
        have hC_gt : |m p.1 - m p.2| / |l' p.1 - l' p.2| < C := by
          change term p < 1 + ∑ q ∈ s, term q
          linarith
        have hC_pos : 0 < C := by
          have h0 : 0 ≤ |m p.1 - m p.2| / |l' p.1 - l' p.2| := by positivity
          linarith
        have hmul : |m p.1 - m p.2| < C * |l' p.1 - l' p.2| :=
          (div_lt_iff₀ hpos).1 hC_gt
        have habs : |C * (l' p.1 - l' p.2)| = C * |l' p.1 - l' p.2| := by
          rw [abs_mul, abs_of_pos hC_pos]
        intro heq
        have heq' : C * (l' p.1 - l' p.2) = -(m p.1 - m p.2) := by linarith
        have habs_eq : |C * (l' p.1 - l' p.2)| = |m p.1 - m p.2| := by
          rw [heq', abs_neg]
        linarith

/-- For any finite subset `V ⊆ ℝⁿ`, there exists a continuous linear functional that is
injective on `V`. -/
lemma exists_injective_linear_on_finset {n : ℕ} (V : Finset (Fin n → ℝ)) :
    ∃ l : StrongDual ℝ (Fin n → ℝ), ∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y := by
  let pairs := (V ×ˢ V).filter (fun p => p.1 ≠ p.2)
  obtain ⟨l, hl⟩ := exists_linear_separating_pairs pairs (fun p hp => (Finset.mem_filter.1 hp).2)
  refine ⟨l, fun x hx y hy heq => ?_⟩
  by_contra hne
  exact hl (x, y) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hx, hy⟩, hne⟩) heq

lemma sum_filter_card_eq_mul_card {α β : Type*} (A : Finset α) (B : Finset β)
    (R : α → β → Prop) [∀ a, DecidablePred (R a)] [∀ b, DecidablePred (fun a => R a b)] (k : ℕ)
    (hB : ∀ b ∈ B, (A.filter (fun a => R a b)).card = k) :
    ∑ a ∈ A, (B.filter (fun b => R a b)).card = k * B.card := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert b₀ s hb₀ ih =>
    have hs : ∀ b ∈ s, (A.filter (fun a => R a b)).card = k :=
      fun b hb => hB b (Finset.mem_insert_of_mem hb)
    have hb₀_card : (A.filter (fun a => R a b₀)).card = k :=
      hB b₀ (Finset.mem_insert_self b₀ s)
    have hstep : ∀ a ∈ A,
        ((insert b₀ s).filter (fun b => R a b)).card =
          (if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card := by
      intro a _
      rw [Finset.filter_insert]
      split_ifs with hR
      · rw [Finset.card_insert_of_notMem (fun hm => hb₀ (Finset.mem_of_mem_filter b₀ hm))]
        omega
      · omega
    calc ∑ a ∈ A, ((insert b₀ s).filter (fun b => R a b)).card
        = ∑ a ∈ A, ((if R a b₀ then 1 else 0) + (s.filter (fun b => R a b)).card) :=
          Finset.sum_congr rfl hstep
      _ = (∑ a ∈ A, if R a b₀ then 1 else 0) + ∑ a ∈ A, (s.filter (fun b => R a b)).card :=
          Finset.sum_add_distrib
      _ = (A.filter (fun a => R a b₀)).card + k * s.card := by
          rw [← Finset.card_filter, ih hs]
      _ = k * (insert b₀ s).card := by
          rw [hb₀_card, Finset.card_insert_of_notMem hb₀]
          ring

lemma sum_le_two_eq_two_mul_card_two_add_card_one {α : Type*} (s : Finset α) (d : α → ℕ)
    (hd : ∀ x ∈ s, d x ≤ 2) :
    ∑ x ∈ s, d x =
      2 * (s.filter (fun x => d x = 2)).card + (s.filter (fun x => d x = 1)).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ x ∈ s, d x ≤ 2 := fun x hx => hd x (Finset.mem_insert_of_mem hx)
    have hda : d a ≤ 2 := hd a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, ih hs, Finset.filter_insert, Finset.filter_insert]
    have hda_cases : d a = 0 ∨ d a = 1 ∨ d a = 2 := by omega
    rcases hda_cases with h0 | h1 | h2
    · simp [h0]
    · simp [h1, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega
    · simp [h2, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_of_mem_filter a hm))]
      omega

lemma card_unique_max_on_filter_eq_one {n : ℕ} (V : Finset (Fin n → ℝ))
    (l : StrongDual ℝ (Fin n → ℝ))
    (hl_inj : ∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y)
    (X : Set (Fin n → ℝ))
    [DecidablePred (· ∈ X)]
    [DecidablePred (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x)]
    (hX : (V.filter (· ∈ X)).Nonempty) :
    (V.filter (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x)).card = 1 := by
  obtain ⟨x₀, hx₀, hmax⟩ := (V.filter (· ∈ X)).exists_max_image l hX
  have hx₀' : x₀ ∈ V ∧ x₀ ∈ X := Finset.mem_filter.1 hx₀
  have hfilt : V.filter (fun x => x ∈ X ∧ ∀ w ∈ V, w ∈ X → l w ≤ l x) = {x₀} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxV, hxX, hle⟩
      have h1 : l x ≤ l x₀ := hmax x (Finset.mem_filter.2 ⟨hxV, hxX⟩)
      have h2 : l x₀ ≤ l x := hle x₀ hx₀'.1 hx₀'.2
      exact hl_inj x hxV x₀ hx₀'.1 (le_antisymm h1 h2)
    · rintro rfl
      exact ⟨hx₀'.1, hx₀'.2, fun w hwV hwX => hmax w (Finset.mem_filter.2 ⟨hwV, hwX⟩)⟩
  rw [hfilt, Finset.card_singleton]

def dot3 (x y : Fin 3 → ℝ) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2

lemma exists_dual_eq_on_pair_lt_third {P : Set (Fin 3 → ℝ)}
    (v : Fin 3 → Fin 3 → ℝ)
    (hv_inj : Function.Injective v)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ m : StrongDual ℝ (Fin 3 → ℝ), m (v j) = m (v i) ∧ m (v k) < m (v i) := by
  have hSub := (@Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.1
    3 P v hv_inj hv_exp).1
  let d₁ : Fin 3 → ℝ := v j - v i
  let d₂ : Fin 3 → ℝ := v k - v i
  have hd₁_ne : d₁ ≠ 0 := sub_ne_zero.2 (hv_inj.ne hij.symm)
  have hd₁_pos : 0 < dot3 d₁ d₁ := by
    by_contra hle
    have h0 : d₁ 0 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    have h1 : d₁ 1 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    have h2 : d₁ 2 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (d₁ 0), sq_nonneg (d₁ 1), sq_nonneg (d₁ 2)]
    apply hd₁_ne
    ext r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
  let t : ℝ := dot3 d₁ d₂ / dot3 d₁ d₁
  let w : Fin 3 → ℝ := d₂ - t • d₁
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hd₂_eq : d₂ = t • d₁ := sub_eq_zero.1 hw0
    have hvk_eq : v k = (1 - t) • v i + t • v j := by
      ext r
      have hr := congr_fun hd₂_eq r
      change v k r - v i r = t * (v j r - v i r) at hr
      change v k r = (1 - t) * v i r + t * v j r
      linarith
    have hnot_in : ∀ (a b c : Fin 3), a ≠ b → c ≠ a → c ≠ b →
        v c ∉ convexHull ℝ (v '' (({a, b} : Finset (Fin 3)) : Set (Fin 3))) := by
      intro a b c hab hca hcb hmem
      have h_inter : v c ∈ convexHull ℝ (v '' (({a, b} : Finset (Fin 3)) : Set (Fin 3))) ∩
          {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hmem, hv_exp c⟩
      rw [hSub {a, b}] at h_inter
      rcases h_inter with ⟨r, hr, hvr⟩
      have hrc : r = c := hv_inj hvr
      subst hrc
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact hca rfl
      · exact hcb rfl
    rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
    · let s : ℝ := -t / (1 - t)
      have h1mt : 0 < 1 - t := by linarith
      have hs0 : 0 ≤ s := div_nonneg (by linarith) (le_of_lt h1mt)
      have hs1 : 0 ≤ 1 - s := by
        have h_eq : 1 - s = 1 / (1 - t) := by
          dsimp [s]
          field_simp [ne_of_gt h1mt]
          ring
        rw [h_eq]
        positivity
      have hvi_eq : v i = (1 - s) • v k + s • v j := by
        ext r
        have hr := congr_fun hvk_eq r
        change v k r = (1 - t) * v i r + t * v j r at hr
        change v i r = (1 - s) * v k r + s * v j r
        dsimp [s]
        field_simp [ne_of_gt h1mt]
        linarith
      have hvi_mem : v i ∈ convexHull ℝ (v '' (({k, j} : Finset (Fin 3)) : Set (Fin 3))) := by
        rw [hvi_eq]
        refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
          hs1 hs0 (by ring))
        · exact ⟨k, by simp, rfl⟩
        · exact ⟨j, by simp, rfl⟩
      exact hnot_in k j i hjk.symm hik hij hvi_mem
    · rw [ht_zero, sub_zero, one_smul, zero_smul, add_zero] at hvk_eq
      exact hik (hv_inj hvk_eq.symm)
    · rcases le_or_gt t 1 with ht_le1 | ht_gt1
      · have hvk_mem : v k ∈ convexHull ℝ (v '' (({i, j} : Finset (Fin 3)) : Set (Fin 3))) := by
          rw [hvk_eq]
          refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
            (by linarith) (le_of_lt ht_pos) (by ring))
          · exact ⟨i, by simp, rfl⟩
          · exact ⟨j, by simp, rfl⟩
        exact hnot_in i j k hij hik.symm hjk.symm hvk_mem
      · let s : ℝ := 1 / t
        have hs0 : 0 ≤ s := by positivity
        have hs1 : 0 ≤ 1 - s := by
          have h_eq : 1 - s = (t - 1) / t := by
            dsimp [s]
            field_simp [ne_of_gt ht_pos]
          rw [h_eq]
          exact div_nonneg (by linarith) (le_of_lt ht_pos)
        have hvj_eq : v j = (1 - s) • v i + s • v k := by
          ext r
          have hr := congr_fun hvk_eq r
          change v k r = (1 - t) * v i r + t * v j r at hr
          change v j r = (1 - s) * v i r + s * v k r
          dsimp [s]
          field_simp [ne_of_gt ht_pos]
          linarith
        have hvj_mem : v j ∈ convexHull ℝ (v '' (({i, k} : Finset (Fin 3)) : Set (Fin 3))) := by
          rw [hvj_eq]
          refine (convex_convexHull ℝ _ (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
            hs1 hs0 (by ring))
          · exact ⟨i, by simp, rfl⟩
          · exact ⟨k, by simp, rfl⟩
        exact hnot_in i k j hik hij.symm hjk hvj_mem
  have hw_pos : 0 < dot3 w w := by
    by_contra hle
    have h0 : w 0 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h1 : w 1 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    have h2 : w 2 = 0 := by
      dsimp [dot3] at hle
      nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]
    apply hw_ne
    ext r
    fin_cases r
    · exact h0
    · exact h1
    · exact h2
  let m : StrongDual ℝ (Fin 3 → ℝ) :=
    -w 0 • ContinuousLinearMap.proj 0 - w 1 • ContinuousLinearMap.proj 1 -
      w 2 • ContinuousLinearMap.proj 2
  have hm_val : ∀ x : Fin 3 → ℝ, m x = -dot3 w x := by
    intro x
    change -w 0 * x 0 - w 1 * x 1 - w 2 * x 2 = -(w 0 * x 0 + w 1 * x 1 + w 2 * x 2)
    ring
  have htmul : t * dot3 d₁ d₁ = dot3 d₁ d₂ := div_mul_cancel₀ _ (ne_of_gt hd₁_pos)
  have hwd₁ : dot3 w d₁ = 0 := by
    change (d₂ 0 - t * d₁ 0) * d₁ 0 + (d₂ 1 - t * d₁ 1) * d₁ 1 + (d₂ 2 - t * d₁ 2) * d₁ 2 = 0
    dsimp [dot3] at htmul
    linarith
  have hwd₂ : dot3 w d₂ = dot3 w w := by
    calc dot3 w d₂
        = (d₂ 0 - t * d₁ 0) * d₂ 0 + (d₂ 1 - t * d₁ 1) * d₂ 1 + (d₂ 2 - t * d₁ 2) * d₂ 2 := rfl
      _ = ((d₂ 0 - t * d₁ 0) ^ 2 + (d₂ 1 - t * d₁ 1) ^ 2 + (d₂ 2 - t * d₁ 2) ^ 2) +
          t * ((d₂ 0 - t * d₁ 0) * d₁ 0 + (d₂ 1 - t * d₁ 1) * d₁ 1 + (d₂ 2 - t * d₁ 2) * d₁ 2) := by ring
      _ = dot3 w w + t * dot3 w d₁ := by dsimp [dot3, w]; ring
      _ = dot3 w w := by rw [hwd₁, mul_zero, add_zero]
  refine ⟨m, ?_, ?_⟩
  · have hdiff : m (v j) - m (v i) = -dot3 w d₁ := by
      rw [hm_val (v j), hm_val (v i)]
      dsimp [dot3, d₁]
      ring
    linarith
  · have hdiff : m (v k) - m (v i) = -dot3 w d₂ := by
      rw [hm_val (v k), hm_val (v i)]
      dsimp [dot3, d₂]
      ring
    linarith

lemma exists_third_fin3 (i j : Fin 3) (hij : i ≠ j) :
    ∃ k : Fin 3, i ≠ k ∧ j ≠ k ∧ ∀ r : Fin 3, r = i ∨ r = j ∨ r = k := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · refine ⟨2, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨1, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨2, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · exact False.elim (hij rfl)
  · refine ⟨0, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨1, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · refine ⟨0, by decide, by decide, fun r => ?_⟩; fin_cases r <;> decide
  · exact False.elim (hij rfl)

lemma simplicial_facet_pair_is_edge {P : Set (Fin 3 → ℝ)} (V : Finset (Fin 3 → ℝ))
    (hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)))
    {F : Set (Fin 3 → ℝ)} (hF_exp : IsExposed ℝ P F)
    (v : Fin 3 → Fin 3 → ℝ) (hv_inj : Function.Injective v)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (hF_eq : F = convexHull ℝ (Set.range v))
    (i j : Fin 3) (hij : i ≠ j) :
    let E := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
    E.Nonempty ∧ IsExposed ℝ P E ∧
    Module.finrank ℝ (affineSpan ℝ E).direction = 1 ∧
    E ⊆ F ∧
    E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = {v i, v j} := by
  intro E
  obtain ⟨k, hik, hjk, hall⟩ := exists_third_fin3 i j hij
  obtain ⟨m, hmj, hmk⟩ := exists_dual_eq_on_pair_lt_third v hv_inj hv_exp i j k hij hik hjk
  let s_F : Finset (Fin 3 → ℝ) := Finset.univ.image v
  have hs_F_coe : (s_F : Set (Fin 3 → ℝ)) = Set.range v := by
    simp [s_F]
  have hF_sF : F = convexHull ℝ (s_F : Set (Fin 3 → ℝ)) := by
    rw [hF_eq, hs_F_coe]
  have hm_le : ∀ y ∈ s_F, m y ≤ m (v i) := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨r, _, rfl⟩
    rcases hall r with rfl | rfl | rfl
    · exact le_rfl
    · exact le_of_eq hmj
    · exact le_of_lt hmk
  have hfilt : s_F.filter (fun y => m y = m (v i)) = {v i, v j} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, heq⟩
      rcases Finset.mem_image.1 hy with ⟨r, _, rfl⟩
      rcases hall r with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (ne_of_lt hmk heq)
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_image_of_mem v (Finset.mem_univ i), rfl⟩
      · exact ⟨Finset.mem_image_of_mem v (Finset.mem_univ j), hmj⟩
  have hexp_F := (isExposed_of_eq_max_on_finset_3d s_F m (m (v i)) hm_le
    ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i), rfl⟩).2.2
  rw [← hF_sF, hfilt] at hexp_F
  simp only [Finset.coe_insert, Finset.coe_singleton] at hexp_F
  have hF_exp_V : IsExposed ℝ (convexHull ℝ (V : Set (Fin 3 → ℝ))) F := by
    rwa [← hP_eq_V]
  have hE_exp_P : IsExposed ℝ P E := by
    rw [hP_eq_V]
    exact isExposed_trans_of_convexHull_3d V hF_exp_V hexp_F
  have hE_ne : E.Nonempty := ⟨v i, subset_convexHull ℝ _ (by simp)⟩
  have hE_dim : Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
    dsimp [E]
    rw [affineSpan_convexHull, direction_affineSpan, vectorSpan_pair ℝ (v i) (v j)]
    exact finrank_span_singleton (vsub_ne_zero.2 (hv_inj.ne hij))
  have hE_sub_F : E ⊆ F := by
    rw [hF_eq]
    refine convexHull_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
  have hSub := (@Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.1
    3 P v hv_inj hv_exp).1 {i, j}
  have h_img : v '' (({i, j} : Finset (Fin 3)) : Set (Fin 3)) = ({v i, v j} : Set (Fin 3 → ℝ)) := by
    ext x
    simp [eq_comm]
  rw [h_img] at hSub
  exact ⟨hE_ne, hE_exp_P, hE_dim, hE_sub_F, hSub⟩

lemma simplicial_facet_incident_edge_dichotomy {P : Set (Fin 3 → ℝ)}
    (hHull : {x : Fin 3 → ℝ | IsExposed ℝ P {x}}.Finite ∧
      ∀ E : PolytopeFace P,
        E.val = convexHull ℝ (E.val ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}}))
    {F : Set (Fin 3 → ℝ)}
    (v : Fin 3 → Fin 3 → ℝ)
    (hv_exp : ∀ r : Fin 3, IsExposed ℝ P {v r})
    (hFV : F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = Set.range v)
    (i j k : Fin 3)
    (hall : ∀ r : Fin 3, r = i ∨ r = j ∨ r = k)
    {E : Set (Fin 3 → ℝ)}
    (hE : E.Nonempty ∧ IsExposed ℝ P E ∧ Module.finrank ℝ (affineSpan ℝ E).direction = 1)
    (hEF : E ⊆ F) (hviE : v i ∈ E) :
    E = convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ)) ∨
      E = convexHull ℝ ({v i, v k} : Set (Fin 3 → ℝ)) := by
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  obtain ⟨a, b, ha, hb, hab, hEV, hE_eq⟩ := (hEdgePair hHull E hE.2.1).1 ⟨hE.1, hE.2.2⟩
  have hvi_in : v i ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hviE, hv_exp i⟩
  rw [hEV] at hvi_in
  have hex_u : ∃ u : Fin 3 → ℝ, u ≠ v i ∧
      u ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} ∧
      E = convexHull ℝ ({v i, u} : Set (Fin 3 → ℝ)) := by
    rcases Set.mem_insert_iff.1 hvi_in with hvia | hvib
    · subst hvia
      refine ⟨b, hab.symm, ?_, hE_eq⟩
      rw [hEV]; simp
    · have hvib' : v i = b := Set.mem_singleton_iff.1 hvib
      subst hvib'
      refine ⟨a, hab, ?_, ?_⟩
      · rw [hEV]; simp
      · rw [Set.pair_comm (v i) a]; exact hE_eq
  rcases hex_u with ⟨u, hu_ne, hu_EV, hE_u⟩
  have hu_FV : u ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := ⟨hEF hu_EV.1, hu_EV.2⟩
  rw [hFV] at hu_FV
  rcases hu_FV with ⟨r, rfl⟩
  rcases hall r with rfl | rfl | rfl
  · exact False.elim (hu_ne rfl)
  · exact Or.inl hE_u
  · exact Or.inr hE_u

lemma simplicial_facet_three_edges_and_vertex_degree {P : Set (Fin 3 → ℝ)}
    (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ))
    (hV_coe : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)))
    (ℰ : Finset (Set (Fin 3 → ℝ)))
    (hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    {F : Set (Fin 3 → ℝ)}
    (hF : F.Nonempty ∧ IsExposed ℝ P F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 2) :
    (ℰ.filter (fun E => E ⊆ F)).card = 3 ∧
    ∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
      let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
      (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
      ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
        (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)) := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  obtain ⟨v, _, hv_inj, hv_exp, hF_eq, hFV, _⟩ :=
    Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality hP hHull F
      hF.1 hF.2.1 (by omega)
  have hPair : ∀ i j : Fin 3, i ≠ j →
      let E := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
      E ∈ ℰ ∧ E ⊆ F ∧ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} = {v i, v j} := by
    intro i j hij
    have hp := simplicial_facet_pair_is_edge V hP_eq_V hF.2.1 v hv_inj hv_exp hF_eq i j hij
    have hmem : convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ)) ∈ ℰ := by
      rw [← Finset.mem_coe, hℰ_coe]
      exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    exact ⟨hmem, hp.2.2.2.1, hp.2.2.2.2⟩
  let E₀₁ := convexHull ℝ ({v 0, v 1} : Set (Fin 3 → ℝ))
  let E₀₂ := convexHull ℝ ({v 0, v 2} : Set (Fin 3 → ℝ))
  let E₁₂ := convexHull ℝ ({v 1, v 2} : Set (Fin 3 → ℝ))
  have h01 := hPair 0 1 (by decide)
  have h02 := hPair 0 2 (by decide)
  have h12 := hPair 1 2 (by decide)
  have hne_01_02 : E₀₁ ≠ E₀₂ := by
    intro heq
    have h1 : v 1 ∈ E₀₁ ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [h01.2.2]; simp
    rw [heq, h02.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h | h
    · exact (by decide : (1 : Fin 3) ≠ 0) (hv_inj h)
    · exact (by decide : (1 : Fin 3) ≠ 2) (hv_inj h)
  have hne_01_12 : E₀₁ ≠ E₁₂ := by
    intro heq
    have h0 : v 0 ∈ E₀₁ ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [h01.2.2]; simp
    rw [heq, h12.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] at h0
    rcases h0 with h | h
    · exact (by decide : (0 : Fin 3) ≠ 1) (hv_inj h)
    · exact (by decide : (0 : Fin 3) ≠ 2) (hv_inj h)
  have hne_02_12 : E₀₂ ≠ E₁₂ := by
    intro heq
    have h0 : v 0 ∈ E₀₂ ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [h02.2.2]; simp
    rw [heq, h12.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] at h0
    rcases h0 with h | h
    · exact (by decide : (0 : Fin 3) ≠ 1) (hv_inj h)
    · exact (by decide : (0 : Fin 3) ≠ 2) (hv_inj h)
  have hfilt_F : ℰ.filter (fun E => E ⊆ F) = {E₀₁, E₀₂, E₁₂} := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hE_mem, hEF⟩
      have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
          Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE_mem
        exact hE_mem
      by_cases hv0 : v 0 ∈ E
      · have hdic := simplicial_facet_incident_edge_dichotomy hHull v hv_exp hFV
          0 1 2 (fun r => by fin_cases r <;> decide) hE_set hEF hv0
        rcases hdic with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · by_cases hv1 : v 1 ∈ E
        · have hdic := simplicial_facet_incident_edge_dichotomy hHull v hv_exp hFV
            1 0 2 (fun r => by fin_cases r <;> decide) hE_set hEF hv1
          rcases hdic with h | h
          · left
            rw [Set.pair_comm (v 1) (v 0)] at h
            exact h
          · exact Or.inr (Or.inr h)
        · obtain ⟨a, b, _, _, hab, hEV, _⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
          have ha_FV : a ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
            have ha_EV : a ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hEV]; simp
            exact ⟨hEF ha_EV.1, ha_EV.2⟩
          have hb_FV : b ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
            have hb_EV : b ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hEV]; simp
            exact ⟨hEF hb_EV.1, hb_EV.2⟩
          rw [hFV] at ha_FV hb_FV
          rcases ha_FV with ⟨ra, rfl⟩
          rcases hb_FV with ⟨rb, rfl⟩
          have hra : v ra ∈ E := by
            have h : v ra ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hEV]; simp
            exact h.1
          have hrb : v rb ∈ E := by
            have h : v rb ∈ E ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hEV]; simp
            exact h.1
          fin_cases ra <;> fin_cases rb
          · exact False.elim (hab rfl)
          · exact False.elim (hv0 hra)
          · exact False.elim (hv0 hra)
          · exact False.elim (hv1 hra)
          · exact False.elim (hab rfl)
          · exact False.elim (hv1 hra)
          · exact False.elim (hv0 hrb)
          · exact False.elim (hv1 hrb)
          · exact False.elim (hab rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨h01.1, h01.2.1⟩
      · exact ⟨h02.1, h02.2.1⟩
      · exact ⟨h12.1, h12.2.1⟩
  have hcard3 : (ℰ.filter (fun E => E ⊆ F)).card = 3 := by
    rw [hfilt_F]
    rw [Finset.card_insert_of_notMem (by simp [hne_01_02, hne_01_12]),
      Finset.card_pair hne_02_12]
  refine ⟨hcard3, fun l x hxV => ?_⟩
  intro ℰ_x
  by_cases hxF : x ∈ F
  · have hx_FV : x ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
      refine ⟨hxF, ?_⟩
      rw [← hV_coe]
      exact hxV
    rw [hFV] at hx_FV
    rcases hx_FV with ⟨i, rfl⟩
    let j : Fin 3 := if i = 0 then 1 else 0
    have hij : i ≠ j := by fin_cases i <;> decide
    obtain ⟨k, hik, hjk, hall⟩ := exists_third_fin3 i j hij
    let E₁ := convexHull ℝ ({v i, v j} : Set (Fin 3 → ℝ))
    let E₂ := convexHull ℝ ({v i, v k} : Set (Fin 3 → ℝ))
    have hE₁ := hPair i j hij
    have hE₂ := hPair i k hik
    have hE₁₂_ne : E₁ ≠ E₂ := by
      intro heq
      have hj_in : v j ∈ E₁ ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by rw [hE₁.2.2]; simp
      rw [heq, hE₂.2.2, Set.mem_insert_iff, Set.mem_singleton_iff] at hj_in
      rcases hj_in with h | h
      · exact hij (hv_inj h).symm
      · exact hjk (hv_inj h)
    have hsub : ℰ_x.filter (fun E => E ⊆ F) ⊆ {E₁, E₂} := by
      intro E hE
      simp only [Finset.mem_filter, ℰ_x] at hE
      have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
          Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE
        exact hE.1.1
      have hdic := simplicial_facet_incident_edge_dichotomy hHull v hv_exp hFV
        i j k hall hE_set hE.2 hE.1.2.1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hdic
    have hcard_le2 : (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 := by
      calc (ℰ_x.filter (fun E => E ⊆ F)).card
          ≤ ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))).card := Finset.card_le_card hsub
        _ = 2 := Finset.card_pair hE₁₂_ne
    refine ⟨hcard_le2, ?_⟩
    constructor
    · intro hcard2
      have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hE₁₂_ne, hcard2])
      have hE₁_in : E₁ ∈ ℰ_x.filter (fun E => E ⊆ F) := by rw [heq_pair]; simp
      have hE₂_in : E₂ ∈ ℰ_x.filter (fun E => E ⊆ F) := by rw [heq_pair]; simp
      simp only [Finset.mem_filter, ℰ_x] at hE₁_in hE₂_in
      have hvj_V : v j ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hv_exp j
      have hvk_V : v k ∈ V := by rw [← Finset.mem_coe, hV_coe]; exact hv_exp k
      have hlj : l (v j) ≤ l (v i) :=
        hE₁_in.1.2.2 (v j) hvj_V (subset_convexHull ℝ _ (by simp))
      have hlk : l (v k) ≤ l (v i) :=
        hE₂_in.1.2.2 (v k) hvk_V (subset_convexHull ℝ _ (by simp))
      refine ⟨hxF, fun w hwV hwF => ?_⟩
      have hw_FV : w ∈ F ∩ {x : Fin 3 → ℝ | IsExposed ℝ P {x}} := by
        refine ⟨hwF, ?_⟩
        rw [← hV_coe]; exact hwV
      rw [hFV] at hw_FV
      rcases hw_FV with ⟨r, rfl⟩
      rcases hall r with rfl | rfl | rfl
      · exact le_rfl
      · exact hlj
      · exact hlk
    · rintro ⟨_, hle_F⟩
      have hpair_sub : ({E₁, E₂} : Finset (Set (Fin 3 → ℝ))) ⊆ ℰ_x.filter (fun E => E ⊆ F) := by
        intro E hE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hE
        simp only [Finset.mem_filter, ℰ_x]
        rcases hE with rfl | rfl
        · refine ⟨⟨hE₁.1, subset_convexHull ℝ _ (by simp), fun w hwV hwE => ?_⟩, hE₁.2.1⟩
          exact hle_F w hwV (hE₁.2.1 hwE)
        · refine ⟨⟨hE₂.1, subset_convexHull ℝ _ (by simp), fun w hwV hwE => ?_⟩, hE₂.2.1⟩
          exact hle_F w hwV (hE₂.2.1 hwE)
      have heq_pair : ℰ_x.filter (fun E => E ⊆ F) = {E₁, E₂} :=
        Finset.Subset.antisymm hsub hpair_sub
      rw [heq_pair, Finset.card_pair hE₁₂_ne]
  · have hemp : ℰ_x.filter (fun E => E ⊆ F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro E hE hEF
      simp only [Finset.mem_filter, ℰ_x] at hE
      exact hxF (hEF hE.2.1)
    rw [hemp, Finset.card_empty]
    exact ⟨by omega, ⟨by omega, fun h => False.elim (hxF h.1)⟩⟩

end Grunbaum2003

open Grunbaum2003

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (hLocal :
      ∀ (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ))),
        (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}} →
        (ℰ : Set (Set (Fin 3 → ℝ))) =
          {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
            Module.finrank ℝ (affineSpan ℝ E).direction = 1} →
        (ℱ : Set (Set (Fin 3 → ℝ))) =
          {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
            Module.finrank ℝ (affineSpan ℝ F).direction = 2} →
        (∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) ∧
        (∀ (l : StrongDual ℝ (Fin 3 → ℝ)),
          (∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y) →
          ∀ x ∈ V,
            (∃ E_down ∈ ℰ, x ∈ E_down ∧ ∃ u ∈ V, u ∈ E_down ∧ l u < l x) →
            (∃ E_up ∈ ℰ, x ∈ E_up ∧ ∃ u ∈ V, u ∈ E_up ∧ l x < l u) →
            (ℱ.filter (fun F =>
              ((ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)).filter
                (fun E => E ⊆ F)).card = 1)).card = 2)) :
    faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices 3 P hP.1
  have hVBound := Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound 3 P
  have hEdgePair := @Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 3 P
  have hImpEdge := @Grunbaum2003.improving_edge_and_global_facet_from_ridge_pairs.1 3 P hP.1
  let V_set : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | IsExposed ℝ P {x}}
  have hV_fin : V_set.Finite := hHull.1
  let V : Finset (Fin 3 → ℝ) := hV_fin.toFinset
  have hV_coe : (V : Set (Fin 3 → ℝ)) = V_set := hV_fin.coe_toFinset
  have hV_sub_P : V_set ⊆ P := fun x hx => hx.subset (Set.mem_singleton x)
  have hP_eq_V : P = convexHull ℝ (V : Set (Fin 3 → ℝ)) := by
    have h1 := hHull.2 ⟨P, IsExposed.refl P⟩
    change P = convexHull ℝ (P ∩ V_set) at h1
    rw [Set.inter_eq_self_of_subset_right hV_sub_P, ← hV_coe] at h1
    exact h1
  have hCardV : faceCount P 0 = V.card := by
    rw [hVBound.1, Set.ncard_eq_toFinset_card V_set hV_fin]
  have hV_ge4 : 4 ≤ V.card := by
    rw [← hCardV]
    exact hVBound.2 hP.1
  have hFace_fin : ∀ k : ℕ,
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = k}.Finite := by
    intro k
    refine ((V.powerset.finite_toSet).image
      (fun s : Finset (Fin 3 → ℝ) => convexHull ℝ (s : Set (Fin 3 → ℝ)))).subset ?_
    intro F hF
    refine ⟨V.filter (· ∈ F), ?_, ?_⟩
    · simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
      exact Finset.filter_subset _ V
    · symm
      have hFE := hHull.2 ⟨F, hF.2.1⟩
      change F = convexHull ℝ (F ∩ V_set) at hFE
      conv_lhs => rw [hFE]
      congr 1
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
      rw [hV_fin.mem_toFinset]
      exact and_comm
  have hE_fin := hFace_fin 1
  have hF_fin := hFace_fin 2
  let ℰ : Finset (Set (Fin 3 → ℝ)) := hE_fin.toFinset
  let ℱ : Finset (Set (Fin 3 → ℝ)) := hF_fin.toFinset
  have hℰ_coe : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1} := hE_fin.coe_toFinset
  have hℱ_coe : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2} := hF_fin.coe_toFinset
  have hCardE : faceCount P 1 = ℰ.card := by
    unfold faceCount
    exact Set.ncard_eq_toFinset_card _ hE_fin
  have hCardF : faceCount P 2 = ℱ.card := by
    unfold faceCount
    exact Set.ncard_eq_toFinset_card _ hF_fin
  obtain ⟨hTwoFacets, hTwoCrossings⟩ := hLocal V ℰ ℱ hV_coe hℰ_coe hℱ_coe
  have hFacetProp : ∀ F ∈ ℱ,
      (ℰ.filter (fun E => E ⊆ F)).card = 3 ∧
      ∀ (l : StrongDual ℝ (Fin 3 → ℝ)) (x : Fin 3 → ℝ), x ∈ V →
        let ℰ_x := ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
        (ℰ_x.filter (fun E => E ⊆ F)).card ≤ 2 ∧
        ((ℰ_x.filter (fun E => E ⊆ F)).card = 2 ↔
          (x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)) := by
    intro F hF
    have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
      rw [← Finset.mem_coe, hℱ_coe] at hF
      exact hF
    exact simplicial_facet_three_edges_and_vertex_degree hP V hV_coe hP_eq_V ℰ hℰ_coe hF_set
  have h3F_2E : 3 * ℱ.card = 2 * ℰ.card :=
    @Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.2.2.2
      (Set (Fin 3 → ℝ)) (Set (Fin 3 → ℝ)) ℱ ℰ (fun F E => E ⊆ F)
      (fun F hF => (hFacetProp F hF).1) hTwoFacets
  rw [hCardV, hCardE, hCardF]
  refine ⟨?_, h3F_2E⟩
  obtain ⟨l, hl_inj⟩ := exists_injective_linear_on_finset V
  have hV_ne : V.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨v_min, hv_min, hl_min⟩ := V.exists_min_image l hV_ne
  obtain ⟨v_max, hv_max, hl_max⟩ := V.exists_max_image l hV_ne
  have hv_min_ne_max : v_min ≠ v_max := by
    intro heq
    have hsub : V ⊆ {v_max} := by
      intro x hx
      rw [Finset.mem_singleton]
      have h1 : l v_min ≤ l x := hl_min x hx
      have h2 : l x ≤ l v_max := hl_max x hx
      rw [heq] at h1
      exact hl_inj x hx v_max hv_max (le_antisymm h2 h1)
    have hcard_le := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard_le
    omega
  let ℰ_x : (Fin 3 → ℝ) → Finset (Set (Fin 3 → ℝ)) :=
    fun x => ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)
  let ℱ_x : (Fin 3 → ℝ) → Finset (Set (Fin 3 → ℝ)) :=
    fun x => ℱ.filter (fun F => x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x)
  let q : (Fin 3 → ℝ) → ℕ := fun x => (ℰ_x x).card
  let r : (Fin 3 → ℝ) → ℕ := fun x => (ℱ_x x).card
  let c : (Fin 3 → ℝ) → ℕ :=
    fun x => (ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 1)).card
  have hsum_q : ∑ x ∈ V, q x = ℰ.card := by
    have h1 := sum_filter_card_eq_mul_card V ℰ
      (fun x E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x) 1 ?_
    · rw [one_mul] at h1
      exact h1
    · intro E hE
      have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
          Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
        rw [← Finset.mem_coe, hℰ_coe] at hE; exact hE
      obtain ⟨a, b, ha, _, _, hEV, _⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
      have haV : a ∈ V := hV_fin.mem_toFinset.2 ha
      have haE : a ∈ E := by
        have h : a ∈ E ∩ V_set := by rw [hEV]; simp
        exact h.1
      exact card_unique_max_on_filter_eq_one V l hl_inj E ⟨a, Finset.mem_filter.2 ⟨haV, haE⟩⟩
  have hsum_r : ∑ x ∈ V, r x = ℱ.card := by
    have h1 := sum_filter_card_eq_mul_card V ℱ
      (fun x F => x ∈ F ∧ ∀ w ∈ V, w ∈ F → l w ≤ l x) 1 ?_
    · rw [one_mul] at h1
      exact h1
    · intro F hF
      have hF_set : F.Nonempty ∧ IsExposed ℝ P F ∧
          Module.finrank ℝ (affineSpan ℝ F).direction = 2 := by
        rw [← Finset.mem_coe, hℱ_coe] at hF; exact hF
      obtain ⟨v, _, _, hv_exp, _, hFV, _⟩ :=
        Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality hP hHull F
          hF_set.1 hF_set.2.1 (by omega)
      have hv0_V : v 0 ∈ V := hV_fin.mem_toFinset.2 (hv_exp 0)
      have hv0_F : v 0 ∈ F := by
        have h : v 0 ∈ F ∩ V_set := by rw [hFV]; exact ⟨0, rfl⟩
        exact h.1
      exact card_unique_max_on_filter_eq_one V l hl_inj F ⟨v 0, Finset.mem_filter.2 ⟨hv0_V, hv0_F⟩⟩
  have h_double : ∀ x ∈ V, 2 * q x = 2 * r x + c x := by
    intro x hxV
    have h_lhs : ∑ F ∈ ℱ, ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2 * q x :=
      sum_filter_card_eq_mul_card ℱ (ℰ_x x) (fun F E => E ⊆ F) 2
        (fun E hE => hTwoFacets E (Finset.mem_of_mem_filter E hE))
    have h_rhs : ∑ F ∈ ℱ, ((ℰ_x x).filter (fun E => E ⊆ F)).card =
        2 * (ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2)).card + c x :=
      sum_le_two_eq_two_mul_card_two_add_card_one ℱ
        (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card)
        (fun F hF => ((hFacetProp F hF).2 l x hxV).1)
    have h_filt_eq : ℱ.filter (fun F => ((ℰ_x x).filter (fun E => E ⊆ F)).card = 2) = ℱ_x x := by
      ext F
      simp only [Finset.mem_filter, ℱ_x, and_congr_right_iff]
      intro hF
      exact ((hFacetProp F hF).2 l x hxV).2
    rw [h_filt_eq] at h_rhs
    dsimp [r]
    omega
  have h_local_sweep : ∀ x ∈ V,
      1 + r x = q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0) := by
    intro x hxV
    have hd := h_double x hxV
    by_cases hxmin : x = v_min
    · subst x
      have hq_min : q v_min = 0 := by
        dsimp [q, ℰ_x]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro E hE h_in
        have hE_set : E.Nonempty ∧ IsExposed ℝ P E ∧
            Module.finrank ℝ (affineSpan ℝ E).direction = 1 := by
          rw [← Finset.mem_coe, hℰ_coe] at hE; exact hE
        obtain ⟨a, b, ha, hb, hab, hEV, _⟩ := (hEdgePair hHull E hE_set.2.1).1 ⟨hE_set.1, hE_set.2.2⟩
        have haV : a ∈ V := hV_fin.mem_toFinset.2 ha
        have hbV : b ∈ V := hV_fin.mem_toFinset.2 hb
        have haE : a ∈ E := by
          have h : a ∈ E ∩ V_set := by rw [hEV]; simp
          exact h.1
        have hbE : b ∈ E := by
          have h : b ∈ E ∩ V_set := by rw [hEV]; simp
          exact h.1
        by_cases hav : a = v_min
        · subst a
          have h1 : l b ≤ l v_min := h_in.2 b hbV hbE
          have h2 : l v_min ≤ l b := hl_min b hbV
          exact hab (hl_inj v_min hv_min b hbV (le_antisymm h2 h1))
        · have h1 : l a ≤ l v_min := h_in.2 a haV haE
          have h2 : l v_min ≤ l a := hl_min a haV
          exact hav (hl_inj a haV v_min hv_min (le_antisymm h1 h2))
      rw [hq_min] at hd ⊢
      simp only [↓reduceIte, hv_min_ne_max]
      omega
    · by_cases hxmax : x = v_max
      · subst x
        have hc_max : c v_max = 0 := by
          dsimp [c]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro F hF hcard1
          by_cases hvF : v_max ∈ F
          · have hcard2 : ((ℰ_x v_max).filter (fun E => E ⊆ F)).card = 2 :=
              (((hFacetProp F hF).2 l v_max hv_max).2).2 ⟨hvF, fun w hwV _ => hl_max w hwV⟩
            omega
          · have hemp : (ℰ_x v_max).filter (fun E => E ⊆ F) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro E hE hEF
              simp only [Finset.mem_filter, ℰ_x] at hE
              exact hvF (hEF hE.2.1)
            rw [hemp, Finset.card_empty] at hcard1
            omega
        rw [hc_max] at hd
        simp only [hxmin, ↓reduceIte]
        omega
      · have hxExp : IsExposed ℝ P {x} := hV_fin.mem_toFinset.1 hxV
        have hxP : x ∈ P := hV_sub_P hxExp
        have hl_lt_max : l x < l v_max :=
          lt_of_le_of_ne (hl_max x hxV) (fun heq => hxmax (hl_inj x hxV v_max hv_max heq))
        have hl_min_lt : l v_min < l x :=
          lt_of_le_of_ne (hl_min x hxV) (fun heq => hxmin (hl_inj x hxV v_min hv_min heq.symm))
        have hv_max_P : v_max ∈ P := hV_sub_P (hV_fin.mem_toFinset.1 hv_max)
        have hv_min_P : v_min ∈ P := hV_sub_P (hV_fin.mem_toFinset.1 hv_min)
        obtain ⟨E_up, u_up, hE_up_ne, hE_up_dim, _, hu_up_exp, hx_E_up, hu_E_up, hl_up⟩ :=
          hImpEdge ⟨P, IsExposed.refl P⟩ x hxExp hxP l ⟨v_max, hv_max_P, hl_lt_max⟩
        have hE_up_mem : E_up.val ∈ ℰ := by
          rw [← Finset.mem_coe, hℰ_coe]
          exact ⟨hE_up_ne, E_up.property, hE_up_dim⟩
        have hu_up_V : u_up ∈ V := hV_fin.mem_toFinset.2 hu_up_exp
        have hmin_neg : (-l) x < (-l) v_min := by
          change -l x < -l v_min; linarith
        obtain ⟨E_dn, u_dn, hE_dn_ne, hE_dn_dim, _, hu_dn_exp, hx_E_dn, hu_E_dn, hl_dn⟩ :=
          hImpEdge ⟨P, IsExposed.refl P⟩ x hxExp hxP (-l) ⟨v_min, hv_min_P, hmin_neg⟩
        have hE_dn_mem : E_dn.val ∈ ℰ := by
          rw [← Finset.mem_coe, hℰ_coe]
          exact ⟨hE_dn_ne, E_dn.property, hE_dn_dim⟩
        have hu_dn_V : u_dn ∈ V := hV_fin.mem_toFinset.2 hu_dn_exp
        have hl_dn' : l u_dn < l x := by
          change -l x < -l u_dn at hl_dn; linarith
        have hc2 : c x = 2 :=
          hTwoCrossings l hl_inj x hxV
            ⟨E_dn.val, hE_dn_mem, hx_E_dn, u_dn, hu_dn_V, hu_E_dn, hl_dn'⟩
            ⟨E_up.val, hE_up_mem, hx_E_up, u_up, hu_up_V, hu_E_up, hl_up⟩
        rw [hc2] at hd
        simp only [hxmin, hxmax, ↓reduceIte]
        omega
  have hsum_sweep : ∑ x ∈ V, (1 + r x) =
      ∑ x ∈ V, (q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0)) :=
    Finset.sum_congr rfl h_local_sweep
  have hsum_lhs : ∑ x ∈ V, (1 + r x) = V.card + ℱ.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hsum_r]
  have hsum_min : (∑ x ∈ V, if x = v_min then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hfilt : V.filter (fun x => x = v_min) = {v_min} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
      rintro rfl; exact hv_min
    rw [hfilt, Finset.card_singleton]
  have hsum_max : (∑ x ∈ V, if x = v_max then 1 else 0) = 1 := by
    rw [← Finset.card_filter]
    have hfilt : V.filter (fun x => x = v_max) = {v_max} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_right_iff_imp]
      rintro rfl; exact hv_max
    rw [hfilt, Finset.card_singleton]
  have hsum_rhs : ∑ x ∈ V, (q x + (if x = v_min then 1 else 0) + (if x = v_max then 1 else 0)) =
      ℰ.card + 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_q, hsum_min, hsum_max]
  omega
