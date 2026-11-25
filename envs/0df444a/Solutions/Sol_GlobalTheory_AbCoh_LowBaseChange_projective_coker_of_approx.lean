-- Prove2me | solution 1 for GlobalTheory.AbCoh.LowBaseChange.projective_coker_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:04.410226+00:00
-- url     : https://prove2.me/submissions/05d4f241-a33a-46cc-ab58-6af3c438cacf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimLEIsLocalRingQuotPow
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_one_tmul_eq_zero_iff
import Theorems.Thm_GlobalTheory_AbCoh_LowBaseChange_exists_one_tmul
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_exact_lTensor_iff_residueField
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_split_injective_of_forall_lTensor_residueField_injective
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
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.LowBaseChange
variable {R : Type} [CommRing R]
namespace GlobalTheory.AbCoh.LowBaseChange
theorem _root_.solution [IsNoetherianRing R] {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B] (f : A →ₗ[R] B)
    (hyp : ∀ (m : Ideal R) [m.IsMaximal] (n : ℕ) (a : A), f a ∈ m • (⊤ : Submodule R B) →
      ∃ y : A, f y ∈ m ^ (n + 1) • (⊤ : Submodule R B) ∧ f a - f y ∈ m • LinearMap.range f) :
    Module.Projective R (B ⧸ LinearMap.range f) := by
  haveI : IsNoetherian R B := isNoetherian_of_isNoetherianRing_of_finite R B
  have hinjq : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor (R ⧸ m)) := by
    intro m _
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨⟨_, a, rfl⟩, rfl⟩ := exists_one_tmul m t
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, one_tmul_eq_zero_iff] at ht
    set N := B ⧸ (m • LinearMap.range f)
    have hq : (m • LinearMap.range f).mkQ (f a) ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R N) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨y, hy, hay⟩ := hyp m n a ht
      have e : (m • LinearMap.range f).mkQ (f a) = (m • LinearMap.range f).mkQ (f y) := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hay
      rw [e]
      have hle : m ^ (n + 1) • (⊤ : Submodule R B) ≤
          (m ^ n • (⊤ : Submodule R N)).comap (m • LinearMap.range f).mkQ := by
        refine Submodule.smul_le.2 fun r hr x _ => ?_
        rw [Submodule.mem_comap, map_smul]
        exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (Nat.le_succ n) hr) Submodule.mem_top
      exact hle hy
    obtain ⟨r, hr⟩ := (m.mem_iInf_smul_pow_eq_bot_iff _).1 hq
    have h1 : f a - (r : R) • f a ∈ m • LinearMap.range f := by
      rw [← Submodule.Quotient.eq, Submodule.Quotient.mk_smul]
      exact hr.symm
    have hsplit : (⟨f a, LinearMap.mem_range_self f a⟩ : LinearMap.range f) =
        ⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a) (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ +
          (r : R) • ⟨f a, LinearMap.mem_range_self f a⟩ := by
      ext; simp
    rw [hsplit, TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
    have h2 : (1 : R ⧸ m) ⊗ₜ[R] (⟨f a - (r : R) • f a, Submodule.sub_mem _ (LinearMap.mem_range_self f a)
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self f a))⟩ : LinearMap.range f) = 0 := by
      rw [one_tmul_eq_zero_iff, Submodule.mem_smul_top_iff]; exact h1
    rw [h2, zero_add, Algebra.smul_def, _root_.mul_one,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 r.2, TensorProduct.zero_tmul]
  have hinj : ∀ (m : Ideal R) [m.IsMaximal],
      Function.Injective ((LinearMap.range f).subtype.lTensor m.ResidueField) := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have hL : RingHom.ker (algebraMap R (R ⧸ m)) = m := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have := GlobalTheory.exact_lTensor_iff_residueField m (R ⧸ m) hL
      (0 : PUnit →ₗ[R] LinearMap.range f) (LinearMap.range f).subtype
    rw [LinearMap.lTensor_zero, LinearMap.lTensor_zero, LinearMap.exact_zero_iff_injective,
      LinearMap.exact_zero_iff_injective] at this
    exact this.1 (hinjq m)
  obtain ⟨l, hl⟩ := GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
    (LinearMap.range f).subtype hinj
  have hex := (Function.Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
  obtain ⟨s, hs⟩ := hex.2 ⟨l, hl⟩
  exact Module.Projective.of_split s _ hs
end GlobalTheory.AbCoh.LowBaseChange
