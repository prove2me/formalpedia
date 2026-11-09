-- Prove2me | solution 1 for Grunbaum2003.polytope_edge_count_and_second_g_coefficient_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:46:29.853185+00:00
-- url     : https://prove2.me/submissions/dbaa8ed1-c8c4-4312-8199-3b300ffa4021

import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_isMSequence_two_iff_choose_bound
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped Classical
open Grunbaum2003

/-- A polytope has at most one edge for each unordered pair of exposed vertices. -/
private theorem edge_bound {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 ≤ Nat.choose (faceCount P 0) 2 := by
  have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP
  have hCount := (Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P).1
  let Vset : Set (Fin d → ℝ) := {x | IsExposed ℝ P {x}}
  have hVfin : Vset.Finite := hHull.1
  let V : Finset (Fin d → ℝ) := hVfin.toFinset
  have hVcard : V.card = faceCount P 0 := by
    rw [hCount]
    exact (Set.ncard_eq_toFinset_card Vset hVfin).symm
  let Eset : Set (Set (Fin d → ℝ)) :=
    {F | F.Nonempty ∧ IsExposed ℝ P F ∧
      Module.finrank ℝ (affineSpan ℝ F).direction = 1}
  let hull : Finset (Fin d → ℝ) → Set (Fin d → ℝ) :=
    fun s => convexHull ℝ (s : Set (Fin d → ℝ))
  have hSub : Eset ⊆ hull '' (V.powersetCard 2 : Set (Finset (Fin d → ℝ))) := by
    intro F hF
    obtain ⟨a, b, ha, hb, hab, _, hFab⟩ :=
      (Grunbaum2003.exposed_edge_pair_and_simplex_faceCount_choose.1 hHull F hF.2.1).1
        ⟨hF.1, hF.2.2⟩
    refine ⟨{a, b}, ?_, ?_⟩
    · apply Finset.mem_powersetCard.2
      refine ⟨?_, by simp [hab]⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hVfin.mem_toFinset.2 ha
      · have hxb : x = b := Finset.mem_singleton.1 hx
        subst x
        exact hVfin.mem_toFinset.2 hb
    · dsimp only [hull]
      simpa only [Finset.coe_pair] using hFab.symm
  calc
    faceCount P 1 = Eset.ncard := rfl
    _ ≤ (hull '' (V.powersetCard 2 : Set (Finset (Fin d → ℝ)))).ncard :=
      Set.ncard_le_ncard hSub ((V.powersetCard 2).finite_toSet.image hull)
    _ ≤ (V.powersetCard 2 : Set (Finset (Fin d → ℝ))).ncard :=
      Set.ncard_image_le (V.powersetCard 2).finite_toSet
    _ = Nat.choose (faceCount P 0) 2 := by
      rw [Set.ncard_coe_finset, Finset.card_powersetCard, hVcard]


private lemma two_mul_choose_two_int (n : ℕ) :
    2 * (Nat.choose n 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have h_even : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have h_mul : 2 * Nat.choose n 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' h_even
  rcases n with _ | n
  · simp
  · have h_mul' : 2 * Nat.choose (n + 1) 2 = (n + 1) * n := by
      simpa using h_mul
    have h_int : (2 * Nat.choose (n + 1) 2 : ℤ) = ((n + 1) * n : ℤ) := by
      exact_mod_cast h_mul'
    push_cast at h_int ⊢
    linarith

/-- The graph upper bound gives the degree-two Macaulay upper bound for the
signed g-coefficient computed from the first two face counts. -/
private theorem signed_bound {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 ≤ Nat.choose (faceCount P 0) 2 ∧
    (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) -
        (d : ℤ) * ((faceCount P 0 - (d + 1) : ℕ) : ℤ) ≤
      (Nat.choose (faceCount P 0 - d) 2 : ℤ) := by
  have hEdge := edge_bound P hP
  have hV := (Grunbaum2003.polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound d P).2 hP
  refine ⟨hEdge, ?_⟩
  have hEdgeZ : (faceCount P 1 : ℤ) ≤ (Nat.choose (faceCount P 0) 2 : ℤ) := by
    exact_mod_cast hEdge
  have h1 := two_mul_choose_two_int (faceCount P 0)
  have h2 := two_mul_choose_two_int (d + 1)
  have h3 := two_mul_choose_two_int (faceCount P 0 - d)
  have hsub : ((faceCount P 0 - d : ℕ) : ℤ) = (faceCount P 0 : ℤ) - (d : ℤ) := by omega
  have hsub' : ((faceCount P 0 - (d + 1) : ℕ) : ℤ) =
      (faceCount P 0 : ℤ) - (d : ℤ) - 1 := by omega
  push_cast at h2
  rw [hsub] at h3
  rw [hsub']
  nlinarith


/-- Edge counting supplies the degree-two upper Macaulay inequality for the
canonical signed coefficient, and hence the length-two M-sequence condition
whenever the first two coefficients are nonnegative natural numbers. -/
theorem solution {d : ℕ} (P : Set (Fin d → ℝ)) (hP : IsDPolytope P) :
    faceCount P 1 ≤ Nat.choose (faceCount P 0) 2 ∧
    ((faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) -
        (d : ℤ) * ((faceCount P 0 - (d + 1) : ℕ) : ℤ) ≤
      (Nat.choose (faceCount P 0 - d) 2 : ℤ)) ∧
    (∀ g : ℕ → ℕ, g 0 = 1 →
      faceCount P 0 = d + 1 + g 1 →
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 →
      IsMSequence 2 g) := by
  have hBase := signed_bound P hP
  refine ⟨hBase.1, hBase.2, ?_⟩
  intro g hg0 hV hE
  apply (Grunbaum2003.isMSequence_two_iff_choose_bound g).2
  refine ⟨hg0, ?_⟩
  have hG2 := hBase.2
  rw [hV] at hG2
  have hSub : d + 1 + g 1 - (d + 1) = g 1 := by omega
  have hSub' : d + 1 + g 1 - d = g 1 + 1 := by omega
  rw [hSub, hSub', hE] at hG2
  push_cast at hG2
  have hG2' : (g 2 : ℤ) ≤ (Nat.choose (g 1 + 1) 2 : ℤ) := by linarith
  exact_mod_cast hG2'
