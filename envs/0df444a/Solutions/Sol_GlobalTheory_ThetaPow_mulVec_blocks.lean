-- Prove2me | solution 1 for GlobalTheory.ThetaPow.mulVec_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:44.001421+00:00
-- url     : https://prove2.me/submissions/f95c6898-c147-41fb-a269-0f25270a9899

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaCharBlockDiagonal
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
theorem _root_.solution {R : Type*} [CommRing R] (e : Fin j × Fin g ≃ Fin G)
    (M : Matrix (Fin g) (Fin g) R) (y : Fin G → R) (i : Fin j) :
    (fun k => ((Matrix.of fun p q => if (e.symm p).1 = (e.symm q).1 then
        M (e.symm p).2 (e.symm q).2 else 0 : Matrix (Fin G) (Fin G) R) *ᵥ y) (e (i, k))) =
      M *ᵥ fun k => y (e (i, k)) := by
  funext k
  simp only [mulVec, dotProduct, of_apply]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]
  · simp
end GlobalTheory.ThetaPow
