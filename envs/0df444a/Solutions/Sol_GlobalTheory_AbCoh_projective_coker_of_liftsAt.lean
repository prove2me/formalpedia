-- Prove2me | solution 1 for GlobalTheory.AbCoh.projective_coker_of_liftsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:28:16.041751+00:00
-- url     : https://prove2.me/submissions/6b4350ba-f413-4756-b76c-47f0b975b36e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_krullDimLE_isLocalRing_quot_pow
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_one_tmul_eq_zero_iff
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_exists_one_tmul
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_projective_coker_of_approx
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
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
open GlobalTheory.AbCoh.LowBaseChange
namespace GlobalTheory.AbCoh
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ),
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) →
      (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R']
        (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) →
      ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom) := by
  intro R _ _ K hK _ hL i hi
  haveI := (hK (i + 1)).1
  haveI := (hK (i + 1)).2
  refine projective_coker_of_approx (K.d i (i + 1)).hom ?_
  intro m _ n a ha
  obtain ⟨h0, h1⟩ := krullDimLE_isLocalRing_quot_pow m n
  haveI := h1
  haveI : IsArtinianRing (R ⧸ m ^ (n + 1)) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, h0⟩
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hle : m ^ (n + 1) ≤ m := Ideal.pow_le_self (Nat.succ_ne_zero n)
  let α : (R ⧸ m ^ (n + 1)) →ₐ[R] (R ⧸ m) := Ideal.Quotient.factorₐ R hle
  have hα : Function.Surjective α := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hz : dB K (R ⧸ m) i (i + 1) ((1 : R ⧸ m) ⊗ₜ[R] a) = 0 := by
    rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff]
    exact ha
  obtain ⟨y, b, hy, hyb⟩ := hL i hi (R ⧸ m ^ (n + 1)) (R ⧸ m) α hα _ hz
  obtain ⟨y₀, rfl⟩ := exists_one_tmul _ y
  obtain ⟨b₀, rfl⟩ := exists_one_tmul _ b
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at hy
  refine ⟨y₀, hy, ?_⟩
  rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one,
    ← TensorProduct.tmul_add] at hyb
  have hdd : (K.d i (i + 1)).hom ((K.d (i - 1) i).hom b₀) = 0 := by
    have := congrArg (fun g => g.hom b₀) (K.d_comp_d (i - 1) i (i + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using this
  have hm : a - (y₀ + (K.d (i - 1) i).hom b₀) ∈ m • (⊤ : Submodule R (K.X i)) := by
    rw [← one_tmul_eq_zero_iff, TensorProduct.tmul_sub, ← hyb, sub_self]
  have := Submodule.mem_map_of_mem (f := (K.d i (i + 1)).hom) hm
  rw [Submodule.map_smul'', ← LinearMap.range_eq_map, map_sub, map_add, hdd, add_zero] at this
  exact this
end GlobalTheory.AbCoh
