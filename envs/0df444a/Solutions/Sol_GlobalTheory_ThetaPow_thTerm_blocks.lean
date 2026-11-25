-- Prove2me | solution 1 for GlobalTheory.ThetaPow.thTerm_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:27.086298+00:00
-- url     : https://prove2.me/submissions/096cf75f-8088-4f85-b9fd-718a57108284

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
import Theorems.Thm_GlobalTheory_ThetaPow_dotProduct_blocks
import Theorems.Thm_GlobalTheory_ThetaPow_mulVec_blocks
import Theorems.Thm_GlobalTheory_ThetaPow_blockEquiv_apply
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaPow
variable {j g G : ℕ}
namespace GlobalTheory.ThetaPow
theorem _root_.solution (e : Fin j × Fin g ≃ Fin G) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin G → ℂ) (m : Fin G → ℤ) :
    CanTh.thTerm (Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        τ (e.symm p).2 (e.symm q).2 else 0) (fun p => a (e.symm p).2) (fun p => b (e.symm p).2) z m =
      ∏ i : Fin j, CanTh.thTerm τ a b (fun k => z (e (i, k))) (blockEquiv e m i) := by
  unfold CanTh.thTerm
  rw [← Complex.exp_sum, dotProduct_blocks e, dotProduct_blocks e (y := z + _), Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_blocks]
  simp only [Pi.add_def, Equiv.symm_apply_apply, blockEquiv_apply]
end GlobalTheory.ThetaPow
