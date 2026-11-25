-- Prove2me | solution 1 for GlobalTheory.TorsionPres.exists_pt_of_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:49.069498+00:00
-- url     : https://prove2.me/submissions/138278f3-1ae8-4ec9-a80b-91dad7a4ac9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NilpotentCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroup
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionPres
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Sp O)} [GrpObj G]
namespace GlobalTheory.TorsionPres
theorem _root_.solution (C : Chart.Chart G) {A : Type} [CommRing A] [Algebra O A] (α : A →ₐ[O] O)
    (hα : ∀ a, IsUnit (α a) → IsUnit a) (z : specO O A ⟶ G) (hz : ptMap α ≫ z = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[O] A, z = Chart.pt C h ∧ α.comp h = Chart.eps C := by
  haveI : IsLocalHom α.toRingHom := ⟨hα⟩
  haveI : IsLocalRing A := RingHom.domain_isLocalRing α.toRingHom
  have hz' : Chart.spMap α ≫ z = Chart.pt C ((Algebra.ofId O O).comp (Chart.eps C)) :=
    hz.trans (Chart.pt_eps C O).symm
  have hU : ⊤ ≤ z.left ⁻¹ᵁ C.U := by
    intro p _
    have hsp : (p : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum A).isPrime.ne_top)
    refine hsp.mem_open (z.left ⁻¹ᵁ C.U).isOpen ?_
    let p₀ : ↥(Spec (CommRingCat.of O)) := IsLocalRing.closedPoint O
    have hp : (Spec.map (CommRingCat.ofHom α.toRingHom)).base p₀ = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint α.toRingHom
    have e := congrArg (fun y : Chart.sp O ⟶ G => y.left.base p₀) hz'
    simp only [Over.comp_left, Chart.spMap_left, Chart.pt_left, Scheme.Hom.comp_apply] at e
    show z.left (IsLocalRing.closedPoint A) ∈ C.U
    rw [← hp, e]
    exact C.hU.range_fromSpec.subset (Set.mem_range_self _)
  obtain ⟨h, rfl⟩ := Chart.exists_pt C z hU
  refine ⟨h, rfl, ?_⟩
  rw [Chart.spMap_pt] at hz'
  exact Chart.pt_injective C hz'
end GlobalTheory.TorsionPres
