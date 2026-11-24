-- Prove2me | solution 1 for GlobalTheory.SectionKernel.gs_mul_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:14.934927+00:00
-- url     : https://prove2.me/submissions/1eaa1b5d-c63f-4eaf-9d9d-54da376a8810

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Theorems.Thm_GlobalTheory_SectionKernel_app_rs
import Theorems.Thm_GlobalTheory_SectionKernel_gs_of_app_eq_zero
import Theorems.Thm_GlobalTheory_SectionKernel_exists_rs_eq_zero
import Theorems.Thm_GlobalTheory_SectionKernel_mul_eq_zero_iff_app

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SectionKernel
variable {X Y : Scheme.{0}}
variable {A A₀ : Type} [CommRing A] [CommRing A₀] {g₀ : A →+* A₀} {a : A}
  {f : X ⟶ Spec (CommRingCat.of A)} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)} {j : Y ⟶ X}
namespace GlobalTheory.SectionKernel
theorem _root_.solution (hg : Function.Surjective g₀)
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g₀) [Flat f]
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g₀))) {W : X.Opens} (z : Y) (hz : j z ∈ W)
    (u : Γ(X, W)) : gs (𝟙 X) (j z) W (cst f W a * u) = 0 ↔ gs j z W u = 0 := by
  constructor
  · intro h
    rw [gs_eq (𝟙 X) (j z) W hz] at h
    obtain ⟨V, hV, hx, e⟩ := exists_rs_eq_zero hz (cst f W a * u) h
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx
    have e' := congrArg (rs X hle) e
    rw [rs_rs, map_mul, rs_cst, map_zero] at e'
    rw [← gs_res j z (hle.trans hV) hx']
    exact gs_of_app_eq_zero j z V' hx' _ ((mul_eq_zero_iff_app hg ha P hA _).1 e')
  · intro h
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g₀)) :=
      IsClosedImmersion.spec_of_surjective _ hg
    have : IsClosedImmersion j := MorphismProperty.of_isPullback P.flip this
    rw [gs_eq _ _ W hz] at h
    obtain ⟨O, hO, hx, e⟩ := exists_rs_eq_zero (U := j ⁻¹ᵁ W) hz _ h
    obtain ⟨D, hD, hD'⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp O.isOpen
    have hx₁ : j z ∈ W ⊓ ⟨D, hD⟩ := ⟨hz, show z ∈ j ⁻¹' D from hD' ▸ hx⟩
    obtain ⟨V', hA, hx', hle⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hx₁
    have l : j ⁻¹ᵁ V' ≤ O := fun y hy => by
      have : y ∈ j ⁻¹' D := (hle hy).2
      rwa [hD'] at this
    have e' := congrArg (rs Y l) e
    rw [rs_rs, map_zero] at e'
    have h₂ := (mul_eq_zero_iff_app hg ha P hA (rs X (hle.trans inf_le_left) u)).2
      ((app_rs j _ u).trans e')
    rw [← gs_res (𝟙 X) (j z) (hle.trans inf_le_left) hx']
    refine gs_of_app_eq_zero (𝟙 X) (j z) V' hx' _ ?_
    change rs X _ _ = 0
    rw [map_mul, rs_cst, h₂]
end GlobalTheory.SectionKernel
