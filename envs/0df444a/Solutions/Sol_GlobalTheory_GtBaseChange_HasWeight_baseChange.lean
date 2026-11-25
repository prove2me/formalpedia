-- Prove2me | solution 1 for GlobalTheory.GtBaseChange.HasWeight.baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:26.422506+00:00
-- url     : https://prove2.me/submissions/9e6de0f1-cec5-4dc0-b3ee-15f0644ad983

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
variable {S S' : Scheme.{0}} (f : S' ⟶ S)
namespace GlobalTheory.GtBaseChange
namespace HasWeight
theorem _root_.solution {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G}
    {U : G.left.Opens} {u : Γ(G.left, U)ˣ} {χ : X} (hu : HasWeight i U u χ)
    (i' : splitTorus S' X ⟶ (Over.pullback f).obj G) (τ : (splitTorus S' X).left ⟶ (splitTorus S X).left)
    (hτ : τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f)
    (hi : i'.left ≫ pullback.fst G.hom f = τ ≫ i.left)
    (hc : τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val)
    {U' : ((Over.pullback f).obj G).left.Opens} (le : U' ≤ pullback.fst G.hom f ⁻¹ᵁ U)
    (hU' : ∀ (Z : Over S') (t : Z ⟶ splitTorus S' X) (g : Z ⟶ (Over.pullback f).obj G) (z : Z.left),
      g.left z ∈ U' → ((t ≫ i') * g).left z ∈ U') :
    HasWeight i' U' (res le (pullU (pullback.fst G.hom f) U u)) χ := by
  intro Z t g z hz
  have h := isGrpPullback_pullback G f
  have e := hu _ (pushPt hτ t) (pushPt h.1.w g) z (le hz)
  have e₁ := h.2 Z (t ≫ i') g (pushPt hτ t ≫ i) (pushPt h.1.w g) (by
    change (t.left ≫ τ) ≫ i.left = (t.left ≫ i'.left) ≫ _
    rw [Category.assoc, Category.assoc, hi]) rfl
  rw [e₁] at e
  have e₂ : charUnit S' X χ = pullU τ ⊤ (charUnit S X χ) := Units.ext hc.symm
  refine (gm_res_pullU _ _ z le (hU' Z t g z hz) u).trans (e.trans (congrArg₂ (· * ·) ?_
    (gm_res_pullU _ _ z le hz u).symm))
  rw [e₂]
  exact (gm_pull t.left τ z ⊤ trivial _).symm
end HasWeight
end GlobalTheory.GtBaseChange
