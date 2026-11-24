-- Prove2me | solution 1 for GlobalTheory.MinorNorm.sum_pol_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:59.201352+00:00
-- url     : https://prove2.me/submissions/fe984e1d-61f3-46ad-aca9-689c4f4535c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_deriv_det
import Theorems.Thm_GlobalTheory_MinorNorm_det_cons
import Theorems.Thm_GlobalTheory_MinorNorm_det_cons_update
import Theorems.Thm_GlobalTheory_MinorNorm_polarisationOperator_apply_variable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (ρ : Fin m → Fin k) (I : Fin (m + 1) → Fin k) (j : Fin k) :
    ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
        pol x d (I s) j (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det =
      -(m * ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) *
        (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det) := by
  rw [← det_cons (fun s => if I s = j then (1 : R) else 0) (fun t u => x (ρ t) (I u))]
  simp only [deriv_det, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ t : Fin m, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
      ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).updateRow t fun u =>
        pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)).det =
      -(Matrix.of (Fin.cons (fun s => if I s = j then (1 : R) else 0) (fun t u => x (ρ t) (I u)) :
        Fin (m + 1) → Fin (m + 1) → R)).det := by
    intro t
    rw [← det_cons_update (fun t u => x (ρ t) (I u)) t, det_cons]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_assoc]
    congr 1
    have e : (fun u => pol x d (I s) j ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))) t u)) =
        x (ρ t) (I s) • fun u => if I (s.succAbove u) = j then (1 : R) else 0 := by
      ext u
      simp [polarisationOperator_apply_variable hd]
    rw [e, det_updateRow_smul]
    congr 2
    ext t' u
    by_cases ht : t' = t
    · subst ht; simp
    · simp [updateRow_ne ht, Function.update_of_ne ht]
  simp only [this]
  simp
end GlobalTheory.MinorNorm
