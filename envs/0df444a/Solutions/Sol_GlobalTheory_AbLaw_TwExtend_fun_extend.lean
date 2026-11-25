-- Prove2me | solution 1 for GlobalTheory.AbLaw.TwExtend.fun_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:18:27.011278+00:00
-- url     : https://prove2.me/submissions/3b0226f0-5ab3-4fed-a6a7-308283cdfe8d

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
theorem _root_.solution {W O : Y.Opens} (hW : IsAffineOpen W) (f : Γ(Y, W)) (hO : Y.basicOpen f = O)
    (h : O ≤ W) (z : Γ(Y, O)) : ∃ (n : ℕ) (x : Γ(Y, W)), rs Y h x = rs Y h f ^ n * z := by
  subst hO
  exact exists_eq_pow_mul_of_isAffineOpen Y W hW f z
end GlobalTheory.AbLaw.TwExtend
