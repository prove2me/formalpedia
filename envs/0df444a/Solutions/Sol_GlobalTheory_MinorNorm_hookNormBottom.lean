-- Prove2me | solution 1 for GlobalTheory.MinorNorm.hookNormBottom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:55.073441+00:00
-- url     : https://prove2.me/submissions/b0aa2cdc-7e05-4963-99b8-07821d3c92a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_fock_int_left
import Theorems.Thm_GlobalTheory_MinorNorm_fock_int_right
import Theorems.Thm_GlobalTheory_MinorNorm_fock_del

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
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}
variable {σ : Type} (v : Fin l → Fin l → σ)
variable {v}
namespace GlobalTheory.MinorNorm
theorem _root_.solution : HookNormBottom := by
  intro n l h a ha
  have hf := fock_del (v := fun r c => ((Fin.castLE h r).rev, c))
    (fun r c s e hh => ⟨Fin.castLE_injective _ (Fin.rev_injective (Prod.mk.inj hh).1),
      (Prod.mk.inj hh).2⟩) a ha
  have e : ∀ i : Fin l, bottomMinor h i =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) : ℤ) : MvPolynomial (Fin n × Fin l) ℂ) *
        minor (fun r c => ((Fin.castLE h r).rev, c)) i := by
    intro i
    unfold minor bottomMinor
    rw [← det_permute]
    congr 1
    refine Matrix.ext fun r c => ?_
    simp only [of_apply, submatrix_apply, id]
    refine congrArg X (Prod.ext (Fin.ext ?_) rfl)
    have := r.2
    have := i.2
    simp only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
    omega
  have e2 : delBottom h a = (((∏ i : Fin l, Equiv.Perm.sign
      (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^ (a i - nextPart a i) : ℤˣ) : ℤ) :
        MvPolynomial (Fin n × Fin l) ℂ) * del (fun r c => ((Fin.castLE h r).rev, c)) a := by
    unfold delBottom del
    simp only [e, mul_pow, Finset.prod_mul_distrib]
    simp
  rw [e2, fock_int_left, fock_int_right, hf, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul,
    Int.units_mul_self]
  simp
end GlobalTheory.MinorNorm
