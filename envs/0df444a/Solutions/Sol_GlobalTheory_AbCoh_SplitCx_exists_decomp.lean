-- Prove2me | solution 1 for GlobalTheory.AbCoh.SplitCx.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:08:28.088607+00:00
-- url     : https://prove2.me/submissions/33da18ef-e674-4638-8dc7-27457fcfc7e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomSplitBaseChange
import Theorems.Thm_GlobalTheory_AbCoh_SplitCx_exists_quasiInv
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
theorem _root_.solution {M0 M1 M2 : Type} [AddCommGroup M0] [Module R M0] [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2] [Module.Projective R M1] [Module.Projective R M2]
    (d0 : M0 →ₗ[R] M1) (d1 : M1 →ₗ[R] M2) (h : ∀ x, d1 (d0 x) = 0)
    (hQ1 : Module.Projective R (M1 ⧸ LinearMap.range d0))
    (hQ2 : Module.Projective R (M2 ⧸ LinearMap.range d1)) :
    ∃ (e : M1 →ₗ[R] M1) (a : M1 →ₗ[R] M0) (b : M2 →ₗ[R] M1),
      e ∘ₗ e = e ∧ e ∘ₗ d0 = 0 ∧ d1 ∘ₗ e = 0 ∧ LinearMap.id = e + d0 ∘ₗ a + b ∘ₗ d1 := by
  obtain ⟨b, hb⟩ := exists_quasiInv d1 hQ2
  obtain ⟨b', hb'⟩ := exists_quasiInv d0 hQ1
  set a : M1 →ₗ[R] M0 := b' ∘ₗ (LinearMap.id - b ∘ₗ d1) with ha
  set e : M1 →ₗ[R] M1 := LinearMap.id - d0 ∘ₗ a - b ∘ₗ d1 with he0
  have he : ∀ y, e y = y - d0 (b' (y - b (d1 y))) - b (d1 y) := fun y => by
    simp [e, a]
  have k1 : ∀ x, d1 (e x) = 0 := fun x => by
    rw [he]; simp only [map_sub, h, hb]; abel
  have k2 : ∀ x, d0 (b' (e x)) = 0 := fun x => by
    rw [he]; simp only [map_sub, hb']; abel
  refine ⟨e, a, b, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [LinearMap.comp_apply]
    simp only [he (e x), k1, map_zero, sub_zero, k2]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    simp only [he, h, map_zero, sub_zero, hb', sub_self]
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, k1]
  · ext x
    simp only [e, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel
end GlobalTheory.AbCoh.SplitCx
