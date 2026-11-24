-- Prove2me | solution 1 for GlobalTheory.FlatThickenings.flat_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:12.650858+00:00
-- url     : https://prove2.me/submissions/eb5bea8e-51e7-42fa-83a0-e6b99fe97183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient
import Theorems.Thm_GlobalTheory_FlatThickenings_flat_of_flat_quotient
import Theorems.Thm_GlobalTheory_NilpotentLift_isPushout_quotient_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings
namespace GlobalTheory.FlatThickenings
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {B : Scheme.{0}} (f : B ⟶ Spec (CommRingCat.of V)) [LocallyOfFiniteType f]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (b : ∀ e, (Y e).left ⟶ B)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick V (IsLocalRing.maximalIdeal V) e))
    (hY : ∀ e, Flat (Y e).hom) {C : CommRingCat.{0}} (u : Spec C ⟶ B) [IsOpenImmersion u] :
    Flat (u ≫ f) := by
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (u ≫ f)
  have hft : LocallyOfFiniteType (Spec.map σ) := by rw [hσ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType.{0})] at hft
  have hN : IsNoetherianRing C := by
    let _ : Algebra V C := σ.hom.toAlgebra
    have : Algebra.FiniteType V C := hft
    exact Algebra.FiniteType.isNoetherianRing V C
  rw [← hσ, HasRingHomProperty.Spec_iff (P := @Flat.{0})]
  refine flat_of_flat_quotient σ.hom fun e => ?_
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (NilpotentLift.isPushout_quotient_map (IsLocalRing.maximalIdeal V ^ (e + 1)) σ)
  have H' := (IsPullback.of_hasPullback (b e) u).flip.paste_vert (hb e)
  rw [← hσ] at H'
  have := hY e
  have hf : Flat ((H.isoIsPullback _ _ H').hom ≫ pullback.fst (b e) u ≫ (Y e).hom) := inferInstance
  rw [IsPullback.isoIsPullback_hom_snd, HasRingHomProperty.Spec_iff (P := @Flat.{0})] at hf
  exact hf
end GlobalTheory.FlatThickenings
