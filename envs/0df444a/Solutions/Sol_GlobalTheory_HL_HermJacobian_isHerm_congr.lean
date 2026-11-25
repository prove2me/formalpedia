-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.isHerm_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:53.30377+00:00
-- url     : https://prove2.me/submissions/25bf4f7a-f2da-4509-80b6-ef8a8237b241

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
import Theorems.Thm_GlobalTheory_HL_HermJacobian_cT_mul
import Theorems.Thm_GlobalTheory_HL_HermJacobian_cT_cT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.HermJacobian
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.HermJacobian
theorem _root_.solution (L : LocE F E) {m : ℕ} (A X : Matrix (Fin m) (Fin m) E) (hX : IsHerm L X) :
    IsHerm L (cT L A * X * A) := by
  unfold IsHerm at hX ⊢
  rw [cT_mul, cT_mul, cT_cT, hX, Matrix.mul_assoc]
end GlobalTheory.HL.HermJacobian
