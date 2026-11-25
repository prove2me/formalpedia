-- Prove2me | solution 1 for GlobalTheory.LieChart.exists_chart_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:47.675135+00:00
-- url     : https://prove2.me/submissions/11e536cb-3c6f-4f25-9446-9f9b64aa446b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_GlobalTheory_LieChart_unit_comp_of_isGrpPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
namespace GlobalTheory.LieChart
theorem _root_.solution {X : Scheme.{0}} (G : Over X) [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U)
    {V : G.left.Opens} (hV : IsAffineOpen V) (e : V ≤ G.hom ⁻¹ᵁ U) (hs : U ≤ (η[G]).left ⁻¹ᵁ V)
    (h : (G.hom.appLE U V e).hom.IsStandardSmooth) (G₀ : Over (Spec (CommRingCat.of Γ(X, U)))) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (hφ : IsGrpPullback G₀ G hU.fromSpec φ) :
    ∃ C : Chart G₀, (alg0 C).IsStandardSmooth := by
  haveI : IsOpenImmersion φ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have hr : V ≤ φ.opensRange := by
    intro y hy
    have h1 : G.hom y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact e hy
    have h2 : y ∈ Set.range (pullback.fst G.hom hU.fromSpec) := by rwa [Scheme.Pullback.range_fst]
    obtain ⟨z, rfl⟩ := h2
    exact ⟨hφ.1.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, hφ.1.isoPullback_inv_fst]⟩
  let C : Chart G₀ := ⟨φ ⁻¹ᵁ V, hV.preimage_of_isOpenImmersion φ hr, fun y _ => by
    show φ ((η[G₀]).left y) ∈ V
    rw [← Scheme.Hom.comp_apply, unit_comp_of_isGrpPullback hφ, Scheme.Hom.comp_apply]
    exact hs (hU.range_fromSpec.subset (Set.mem_range_self _))⟩
  refine ⟨C, ?_⟩
  have key : CommRingCat.ofHom (alg0 C) = G.hom.appLE U V e ≫ φ.appLE V (φ ⁻¹ᵁ V) le_rfl := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, ← fromSpec_over C, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e, ← Category.assoc (Spec.map _),
      IsAffineOpen.SpecMap_appLE_fromSpec φ hV C.hU le_rfl, Category.assoc, hφ.1.w]
  haveI := φ.isIso_app V hr
  have k2 : alg0 C = (φ.app V).hom.comp (G.hom.appLE U V e).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg CommRingCat.Hom.hom key
  rw [k2]
  exact RingHom.isStandardSmooth_respectsIso.1 _ (asIso (φ.app V)).commRingCatIsoToRingEquiv h
end GlobalTheory.LieChart
