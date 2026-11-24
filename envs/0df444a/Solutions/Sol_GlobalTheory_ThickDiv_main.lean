-- Prove2me | solution 1 for GlobalTheory.ThickDiv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:05.222749+00:00
-- url     : https://prove2.me/submissions/31b09e03-e7b8-4a38-a4d2-5375b83a8919

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Theorems.Thm_GlobalTheory_ThickDiv_resTop_scal
import Theorems.Thm_GlobalTheory_ThickDiv_cst_dvd_gs_of_app_eq_zero
import Theorems.Thm_GlobalTheory_ThickDiv_app_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_div_sec


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
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Over (Spec (CommRingCat.of V))) [Flat X.hom] (N : LB X.left) (σ : LB.Sec N) (e : ℕ), (∀ j, ((fstG (maximalIdeal V) e X).left.app _).hom (σ.f j) = 0) ↔ ∃ τ : LB.Sec N, SecIsMul X.hom (ϖ ^ (e + 1)) σ τ := by
  intro V _ _ _ ϖ hϖ X _ N σ e
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := exists_div_sec X.hom (pow_ne_zero (e + 1) hϖ.ne_zero) σ
      (fun j x hx => cst_dvd_gs_of_app_eq_zero hϖ X e (N.U j) (σ.f j) (h j) x hx)
    exact ⟨τ, fun j => by rw [hτ j, resTop_scal]⟩
  · rintro ⟨τ, hτ⟩ j
    exact (app_eq_zero_iff hϖ X e (N.U j) (σ.f j)).2 ⟨τ.f j, hτ j⟩
end GlobalTheory.ThickDiv
