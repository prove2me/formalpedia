-- Prove2me | solution 1 for GlobalTheory.AbCoh.mem_map_of_smul_eq_zero_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:31.317794+00:00
-- url     : https://prove2.me/submissions/a60b8dba-8590-474c-928a-2a3afdff6683

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullSurjectiveAndKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveDeformationAffineSections
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
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
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) (hb : t • b = 0) :
    b ∈ J.map (algebraMap R S) := by
  let f : J →ₗ[R] R := J.subtype
  let g : R →ₗ[R] R := LinearMap.mulLeft R t
  have ex : Function.Exact f g := by
    intro y
    change t * y = 0 ↔ y ∈ Set.range f
    rw [_root_.mul_comm, ← hJ]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have ex' := Module.Flat.lTensor_exact S ex
  have h0 : g.lTensor S (b ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change b ⊗ₜ[R] (t * 1) = 0
    rw [_root_.mul_one, ← _root_.mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul, hb,
      TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := (ex' _).1 h0
  have key : ∀ y : S ⊗[R] J, TensorProduct.rid R S (f.lTensor S y) ∈ J.map (algebraMap R S) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x z hx hz => rw [map_add, map_add]; exact add_mem hx hz
  have := key y
  rwa [hy, TensorProduct.rid_tmul, _root_.one_smul] at this
end GlobalTheory.AbCoh
