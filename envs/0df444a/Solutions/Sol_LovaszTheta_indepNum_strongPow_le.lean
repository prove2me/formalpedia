-- Prove2me | solution 1 for LovaszTheta.indepNum_strongPow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:59:13.124257+00:00
-- url     : https://prove2.me/submissions/0aaf5291-5257-4763-a669-21cd6afd7739

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_indepNum_le_gen
public import Theorems.Thm_LovaszTheta_dotProduct_tensor

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution [Finite V] (G : SimpleGraph V) {d : ℕ} {u : V → Fin d → ℝ}
    (hu : IsOrthonormalRep G u) {c : Fin d → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) (k : ℕ) :
    ((strongPow G k).indepNum : ℝ) ≤ t ^ k := by
  classical
  refine indepNum_le_gen (strongPow G k) (ι := Fin k → Fin d) (fun x j => ∏ i, u (x i) (j i)) ?_ ?_
    (c := fun j : Fin k → Fin d => ∏ i, c (j i)) ?_ (pow_nonneg ht0 k) ?_
  · intro x
    rw [dotProduct_tensor (fun i => u (x i)) (fun i => u (x i))]
    simp [hu.1]
  · intro x y hxy hadj
    rw [dotProduct_tensor (fun i => u (x i)) (fun i => u (y i))]
    have : ∃ i, x i ≠ y i ∧ ¬ G.Adj (x i) (y i) := by
      by_contra h
      push Not at h
      exact hadj ⟨hxy, fun i => by
        by_cases hi : x i = y i
        · exact Or.inl hi
        · exact Or.inr (h i hi)⟩
    obtain ⟨i, hi1, hi2⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hu.2 _ _ hi1 hi2)
  · rw [dotProduct_tensor (fun _ => c) (fun _ => c)]
    simp [hc]
  · intro x
    rw [dotProduct_tensor (fun _ => c) (fun i => u (x i)), ← Finset.prod_pow,
      ← Fin.prod_const, ← Finset.prod_mul_distrib]
    calc (1 : ℝ) = ∏ _i : Fin k, (1 : ℝ) := by simp
      _ ≤ _ := by gcongr with i; exact ht (x i)
end LovaszTheta
