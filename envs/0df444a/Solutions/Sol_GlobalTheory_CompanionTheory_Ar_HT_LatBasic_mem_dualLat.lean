-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.mem_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:38.154077+00:00
-- url     : https://prove2.me/submissions/ebf27722-220e-4867-bfe4-5b5b45120d9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution {V' : Type} [AddCommGroup V'] [Module C V'] [Module O V']
    [IsScalarTower O C V'] {B : V →ₗ[C] V' →ₗ[C] C} {L : Submodule O V} {y : V'} :
    y ∈ dualLat B L ↔ ∀ x ∈ L, B x y ∈ (algebraMap O C).range := Iff.rfl
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
