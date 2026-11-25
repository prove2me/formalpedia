-- Prove2me | solution 1 for GlobalTheory.RelExp.HolAt.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:48.132073+00:00
-- url     : https://prove2.me/submissions/4aea1722-5345-4769-9182-990a286c76cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EventuallyEqOfAdditiveOfHasFDerivAt
import Theorems.Thm_GlobalTheory_RelExp_HolAt_congr
import Theorems.Thm_GlobalTheory_RelExp_HolAt_post
import Theorems.Thm_GlobalTheory_RelExp_holAt_of_isPullback

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
theorem _root_.solution {a b : ∀ w, Over.mk (y w) ⟶ G} (ha : HolAt (Z := G.left) (fun w => (a w).left) w₀)
    (hb : HolAt (Z := G.left) (fun w => (b w).left) w₀) :
    HolAt (Z := G.left) (fun w => (a w * b w).left) w₀ := by
  have h1 : ∀ w, (lift (a w) (b w)).left ≫ (fst G G).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have h2 : ∀ w, (lift (a w) (b w)).left ≫ (snd G G).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  have H : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback G.hom G.hom
  exact (holAt_of_isPullback H (c := fun w => (lift (a w) (b w)).left)
    (ha.congr (Eventually.of_forall fun w => (h1 w).symm))
    (hb.congr (Eventually.of_forall fun w => (h2 w).symm))).post μ[G].left
end HolAt
end GlobalTheory.RelExp
