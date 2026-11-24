-- Prove2me | solution 1 for GlobalTheory.ThickDiv.cst_dvd_gs_of_app_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:03.994815+00:00
-- url     : https://prove2.me/submissions/b80186d0-6c17-4389-a37d-4b64151d364b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Theorems.Thm_GlobalTheory_ThickDiv_dvd_of_app_eq_zero_of_isAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_constFn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickDiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
namespace GlobalTheory.ThickDiv
theorem _root_.solution (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W))
    (hf : ((fstG (maximalIdeal V) e X).left.app W).hom f = 0) (x : X.left) (hx : x ∈ W) :
    cst X.hom x (ϖ ^ (e + 1)) ∣ gs (𝟙 X.left) x W f := by
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens hx
  have hr : ((fstG (maximalIdeal V) e X).left.app U).hom
      ((X.left.presheaf.map (homOfLE hUW).op).hom f) = 0 := by
    have hn := congrArg (fun φ => φ.hom f) ((fstG (maximalIdeal V) e X).left.naturality (homOfLE hUW).op)
    refine hn.trans ?_
    change (_ : _ →+* _) (((fstG (maximalIdeal V) e X).left.app W).hom f) = 0
    rw [hf, map_zero]
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero_of_isAffineOpen hϖ X e hU _ hr
  have hgerm := gs_appLE (𝟙 X.left) W U hUW (𝟙 X.left) x hxU f
  rw [Category.id_comp] at hgerm
  have hres : (Scheme.Hom.appLE (𝟙 X.left) W U hUW).hom f = (X.left.presheaf.map (homOfLE hUW).op).hom f := rfl
  rw [← hgerm, hres, hg, gs_mul _ _ _ hxU, gs_constFn _ _ _ _ hxU, Category.id_comp]
  exact dvd_mul_right _ _
end GlobalTheory.ThickDiv
