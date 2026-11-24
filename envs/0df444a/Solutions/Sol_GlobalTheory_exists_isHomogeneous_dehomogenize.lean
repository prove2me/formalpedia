-- Prove2me | solution 1 for GlobalTheory.exists_isHomogeneous_dehomogenize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:38.479874+00:00
-- url     : https://prove2.me/submissions/911623a8-af06-40f4-a279-e50b1c51d57d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ),
    T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧
      ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 →
        aeval a T = aeval (fun j => a j.succ) T₀ := by
  intro D T₀ q hq
  refine ⟨∑ d ∈ Finset.range (q + 1),
    X 0 ^ (q - d) * rename Fin.succ (homogeneousComponent d T₀), ?_, ?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hdq : d ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have h := (isHomogeneous_X_pow (R := ℤ) (0 : Fin (D + 1)) (q - d)).mul
      ((homogeneousComponent_isHomogeneous d T₀).rename_isHomogeneous (f := Fin.succ))
    rwa [Nat.sub_add_cancel hdq] at h
  · intro R _ a ha
    have hsum : ∑ d ∈ Finset.range (q + 1), homogeneousComponent d T₀ = T₀ := by
      conv_rhs => rw [← sum_homogeneousComponent T₀]
      symm
      refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hq)) ?_
      intro x _ hx
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hx
      omega
    conv_rhs => rw [← hsum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    intro d _
    simp only [map_mul, map_pow, aeval_X, ha, one_pow, one_mul, aeval_rename]
    rfl
end GlobalTheory
