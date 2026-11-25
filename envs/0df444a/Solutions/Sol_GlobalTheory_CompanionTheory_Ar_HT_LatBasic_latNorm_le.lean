-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.latNorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:32:54.959178+00:00
-- url     : https://prove2.me/submissions/6aee02fe-5c51-487c-b859-4fafbf49b7fe

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
omit [Algebra O C] [IsScalarTower O C V]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution {L : Submodule O V} (a : C) {y : V} (hy : y ∈ L) :
    latNorm v L (a • y) ≤ v a :=
  csInf_le (OrderBot.bddBelow _) ⟨a, rfl, y, hy, rfl⟩
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
