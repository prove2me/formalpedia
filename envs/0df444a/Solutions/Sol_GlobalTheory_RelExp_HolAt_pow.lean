-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:36.005126+00:00
-- url     : https://prove2.me/submissions/84275aaa-5074-42b3-b462-be1a41daa580

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_mul
import Theorems.Thm_GlobalTheory_RelExp_HolAt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.RelExp
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {Z Y : Scheme.{0}}
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : E → (Sp ℂ ⟶ X)} {w₀ : E}
namespace GlobalTheory.RelExp
namespace HolAt
theorem _root_.solution {a : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀) (n : ℕ) :
    HolAt (Z := G.left) (fun w => (a w ^ n).left) w₀ := by
  induction n with
  | zero => simpa only [pow_zero, mul_inv_cancel] using ha.mul ha.inv
  | succ n ih => simpa only [pow_succ] using ih.mul ha
end HolAt
end GlobalTheory.RelExp
