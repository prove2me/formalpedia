-- Prove2me | solution 1 for GlobalTheory.MinorNorm.pol_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:48:58.147447+00:00
-- url     : https://prove2.me/submissions/75560656-6542-447c-bb4c-4efca33e451f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_deriv_det
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
variable {R : Type} [CommRing R] [Algebra ℂ R] {k : ℕ} {x : Fin k → Fin k → R}
  {d : Fin k → Fin k → Derivation ℂ R R}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) {m : ℕ}
    (hm : m ≤ k) (i j : Fin k) (hij : i ≤ j) :
    pol x d i j (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det =
      (if i = j ∧ (j : ℕ) < m then 1 else 0) *
        (Matrix.of fun r c : Fin m => x (Fin.castLE hm r) (Fin.castLE hm c)).det := by
  rw [← det_transpose, deriv_det]
  simp only [transpose_apply, of_apply, polarisationOperator_apply_variable hd]
  by_cases hj : (j : ℕ) < m
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]
    · have e : Fin.castLE hm ⟨j, hj⟩ = j := rfl
      simp only [e, if_true]
      by_cases h : i = j
      · subst h
        rw [if_pos ⟨rfl, hj⟩, one_mul]
        congr 1
        exact updateRow_eq_self _ _
      · rw [if_neg (fun h' => h h'.1), zero_mul]
        have hi : (i : ℕ) < j := lt_of_le_of_ne hij (fun h' => h (Fin.ext h'))
        refine det_zero_of_row_eq (i := ⟨j, hj⟩) (j := ⟨i, hi.trans hj⟩)
          (fun h' => hi.ne' (Fin.mk.inj h')) ?_
        rw [updateRow_self, updateRow_ne (fun h' => hi.ne (Fin.mk.inj h'))]
        rfl
    · intro t _ ht
      refine det_eq_zero_of_row_eq_zero t fun u => ?_
      rw [updateRow_self, if_neg]
      intro h
      exact ht (Fin.ext (congrArg Fin.val h :))
    · simp
  · rw [if_neg (fun h => hj h.2), zero_mul]
    refine Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_
    rw [updateRow_self, if_neg]
    intro h
    apply hj
    rw [← h]
    exact t.2
end GlobalTheory.MinorNorm
