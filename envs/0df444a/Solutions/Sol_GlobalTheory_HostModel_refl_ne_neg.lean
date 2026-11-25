-- Prove2me | solution 1 for GlobalTheory.HostModel.refl_ne_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:39.572263+00:00
-- url     : https://prove2.me/submissions/844b151d-e86e-4cb7-941b-5b7e54cf095f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
omit [IsCMField E]
namespace GlobalTheory.HostModel
theorem _root_.solution : LinearEquiv.refl (𝓞 E) (𝓞 E) ≠ (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) := fun h => by
  have h1 : (1 : 𝓞 E) = -1 := congrArg (fun e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E => e 1) h
  exact one_ne_zero (self_eq_neg.1 h1)
end GlobalTheory.HostModel
