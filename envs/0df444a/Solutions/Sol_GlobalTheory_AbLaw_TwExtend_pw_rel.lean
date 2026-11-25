-- Prove2me | solution 1 for GlobalTheory.AbLaw.TwExtend.pw_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:07:14.717329+00:00
-- url     : https://prove2.me/submissions/36ad19ab-e3a5-4aee-8d9b-b532a5477c02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsTwExtendPowMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.TwExtend
variable {Y : Scheme.{0}}
namespace GlobalTheory.AbLaw.TwExtend
theorem _root_.solution {H : LB Y} {d : ℤ} (σ : LB.Sec (pw H d)) (u : ∀ l, Γ(Y, H.U l))
    (hu : ∀ l, u l = σ.f l) (l m : H.ι) {O : Y.Opens}
    (hl : O ≤ H.U l) (hm : O ≤ H.U m) (h : O ≤ H.U l ⊓ H.U m) :
    rs Y hl (u l) = (res h (H.g l m) ^ d).val * rs Y hm (u m) := by
  rw [← map_zpow, hu, hu]
  exact GlobalTheory.LB.sec_rel σ l m hl hm h
end GlobalTheory.AbLaw.TwExtend
