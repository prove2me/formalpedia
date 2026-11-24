-- Prove2me | solution 1 for GlobalTheory.QNorm.NormOpen.continuous_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:38:39.572376+00:00
-- url     : https://prove2.me/submissions/38ebab43-3160-480e-baff-d5c4aac439da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSupersetMemSUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticFormIdeleValuesMemNhdsOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Topology
open GlobalTheory GlobalTheory.QNorm
open GlobalTheory.QNorm.NormOpen
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.QNorm.NormOpen
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun a : FiniteAdeleRing (𝓞 F) F => a v) := by
  exact RestrictedProduct.continuous_eval v
end GlobalTheory.QNorm.NormOpen
