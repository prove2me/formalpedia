-- Prove2me | solution 1 for GlobalTheory.AbCoh.CohBaseChange.liftsAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:17:21.399671+00:00
-- url     : https://prove2.me/submissions/7d1fee86-c132-42fd-bd3d-f7d09b44abb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
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
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}
namespace GlobalTheory.AbCoh.CohBaseChange
theorem _root_.solution (M : Model s K) (hU : UConst s) {R' k : Type} [CommRing R'] [Algebra R R']
    [CommRing k] [Algebra R k] (α : R' →ₐ[R] k) (hα : Function.Surjective α) : LiftsAt K α 0 := by
  intro z hz
  have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
  have h₀ := IsPullback.of_hasPullback s (spMap (algebraMap R k))
  obtain ⟨e', -⟩ := M.θ0_one h'
  obtain ⟨e₀, he₀⟩ := M.θ0_one h₀
  obtain ⟨r, hr, -⟩ := hU k _ _ _ h₀ (M.θ0 h₀ ⟨z, hz⟩).1 (M.θ0 h₀ ⟨z, hz⟩).2
  have hz' : (⟨z, hz⟩ : LinearMap.ker (dB K k 0 1)) = r • ⟨_, e₀⟩ := by
    apply (M.θ0 h₀).injective
    rw [map_smul]
    refine Subtype.ext (funext fun T ↦ ?_)
    rw [hr T, Algebra.algebraMap_eq_smul_one, ← he₀ T]
    rfl
  obtain ⟨r', rfl⟩ := hα r
  refine ⟨r' • ((1 : R') ⊗ₜ[R] M.one), 0, ?_, ?_⟩
  · rw [map_smul]
    exact (congrArg (r' • ·) (LinearMap.mem_ker.1 e')).trans (smul_zero _)
  · have := congrArg Subtype.val hz'
    simp only [Submodule.coe_smul] at this
    rw [this, map_zero, add_zero, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
end GlobalTheory.AbCoh.CohBaseChange
