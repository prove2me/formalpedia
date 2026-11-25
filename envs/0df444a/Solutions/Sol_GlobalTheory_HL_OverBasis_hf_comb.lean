-- Prove2me | solution 1 for GlobalTheory.HL.OverBasis.hf_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:14.158251+00:00
-- url     : https://prove2.me/submissions/e20e22ed-0e53-43d8-ba0b-7c026d6748ba

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LinearIndependentOfGram
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_SelfDual_hf_sum_l
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OverBasis
open Matrix GlobalTheory.HL.SelfDual
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.OverBasis
theorem _root_.solution (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin m → Fin n → E)
    (c : Fin m → E) : (fun a => hf L Hm (∑ b, c b • y b) (y a)) = gramT L Hm y *ᵥ c := by
  funext a
  rw [hf_sum_l]
  simp [gramT, Matrix.mulVec, dotProduct, mul_comm]
end GlobalTheory.HL.OverBasis
