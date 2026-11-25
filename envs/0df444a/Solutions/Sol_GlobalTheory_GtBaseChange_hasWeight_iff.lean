-- Prove2me | solution 1 for GlobalTheory.GtBaseChange.hasWeight_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:10:45.371798+00:00
-- url     : https://prove2.me/submissions/fe75796f-fef3-4862-95f3-2a6e31bc034d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GlobalTheory.GtBaseChange
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
namespace GlobalTheory.GtBaseChange
theorem _root_.solution (i : splitTorus S X ⟶ G) (U : G.left.Opens) (u : Γ(G.left, U)ˣ) (χ : X)
    (hle : (snd (splitTorus S X) G).left ⁻¹ᵁ U ≤
      (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left ⁻¹ᵁ U)
    (hT : (snd (splitTorus S X) G).left ⁻¹ᵁ U ≤ (fst (splitTorus S X) G).left ⁻¹ᵁ ⊤) :
    HasWeight i U u χ ↔
      res hle (pullU (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left _ u) =
        res hT (pullU (fst (splitTorus S X) G).left ⊤ (charUnit S X χ)) *
        pullU (snd (splitTorus S X) G).left _ u := by
  constructor
  · intro h
    refine unit_ext fun y hy => ?_
    rw [map_mul, gm_res_pullU' _ y hle hy, gm_res_pullU' _ y _ hy, gm_pull (𝟙 _) _ y U hy, Category.id_comp]
    exact h _ _ _ y hy
  · intro h Z t g z hz
    have e₁ : (lift t g).left ≫ (fst (splitTorus S X) G).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    have e₂ : (lift t g).left ≫ (snd (splitTorus S X) G).left = g.left := by
      rw [← Over.comp_left, lift_snd]
    have e₃ : (lift t g).left ≫ (lift (fst (splitTorus S X) G ≫ i) (snd (splitTorus S X) G) ≫ μ[G]).left =
        ((t ≫ i) * g).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd, Hom.mul_def]
    have hm : (lift t g).left z ∈ (snd (splitTorus S X) G).left ⁻¹ᵁ U := by
      change ((lift t g).left ≫ (snd (splitTorus S X) G).left) z ∈ U
      rw [e₂]; exact hz
    have e := congrArg (gm (lift t g).left z _) h
    rwa [map_mul, gm_res_pullU _ _ z hle hm, gm_res_pullU _ _ z _ hm, gm_pull _ _ z U hm, e₁, e₂, e₃] at e
end GlobalTheory.GtBaseChange
