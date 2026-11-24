-- Prove2me | solution 1 for GlobalTheory.ThickDiv.app_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:03.618931+00:00
-- url     : https://prove2.me/submissions/ee2ee12c-7c19-49a0-b80c-c563a84a95f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Theorems.Thm_GlobalTheory_ThickDiv_resTop_scal
import Theorems.Thm_GlobalTheory_ThickDiv_app_constFn_eq_zero
import Theorems.Thm_GlobalTheory_ThickDiv_cst_dvd_gs_of_app_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_div


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
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W)) :
    ((fstG (maximalIdeal V) e X).left.app W).hom f = 0 ↔
      ∃ g : Γ(X.left, W), f = Out.resTop W (scal X.hom (ϖ ^ (e + 1))) * g := by
  rw [resTop_scal]
  constructor
  · intro hf
    exact exists_div X.hom (pow_ne_zero _ hϖ.ne_zero) W f
      (fun x hx => cst_dvd_gs_of_app_eq_zero hϖ X e W f hf x hx)
  · rintro ⟨g, rfl⟩
    rw [map_mul, app_constFn_eq_zero (maximalIdeal V) e X W
      (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) _), zero_mul]
end GlobalTheory.ThickDiv
