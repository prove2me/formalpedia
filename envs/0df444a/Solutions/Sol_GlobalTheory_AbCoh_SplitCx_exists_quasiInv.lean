-- Prove2me | solution 1 for GlobalTheory.AbCoh.SplitCx.exists_quasiInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:17:23.61575+00:00
-- url     : https://prove2.me/submissions/330d92fe-5e87-4120-9e7b-c5a127c810b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomSplitBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SplitCx
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbCoh.SplitCx
theorem _root_.solution {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (d : M →ₗ[R] N) (hQ : Module.Projective R (N ⧸ LinearMap.range d)) :
    ∃ b : N →ₗ[R] M, ∀ x, d (b (d x)) = d x := by
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  have hmem : ∀ y : N, y - t ((LinearMap.range d).mkQ y) ∈ LinearMap.range d := by
    intro y
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun ht ((LinearMap.range d).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let r : N →ₗ[R] LinearMap.range d :=
    LinearMap.codRestrict _ (LinearMap.id - t ∘ₗ (LinearMap.range d).mkQ) hmem
  have hr : ∀ y : LinearMap.range d, r y = y := by
    intro y
    apply Subtype.ext
    simp only [r, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply]
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 y.2, map_zero, sub_zero]
  haveI : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype r (LinearMap.ext hr)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    (LinearMap.surjective_rangeRestrict d)
  refine ⟨s ∘ₗ r, fun x => ?_⟩
  have h1 := LinearMap.congr_fun hs (r (d x))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  have h2 := congrArg Subtype.val h1
  have h3 : (r (d x) : N) = d x := congrArg Subtype.val (hr ⟨d x, LinearMap.mem_range_self d x⟩)
  exact h2.trans h3
end GlobalTheory.AbCoh.SplitCx
