-- Prove2me | solution 1 for GlobalTheory.AbLaw.TwExtend.fun_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:54.613109+00:00
-- url     : https://prove2.me/submissions/1bde4e57-fffc-4a37-b294-c0b61a42662a

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
theorem _root_.solution {W O : Y.Opens} (hW : IsCompact (W : Set Y)) (f x : Γ(Y, W))
    (hO : Y.basicOpen f = O) (h : O ≤ W) (hx : rs Y h x = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  subst hO
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y hW x f hx
end GlobalTheory.AbLaw.TwExtend
