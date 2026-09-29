-- Prove2me | solution 1 for NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4cc5bb57-c115-5281-a28a-344e67778529

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_exists_valuation_units_Kw
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

theorem prime_eq_of_natCast_mem {R : Type} [CommRing R] (I : Ideal R) [hI : I.IsPrime] (p₁ p₂ : ℕ)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (h₁ : (p₁ : R) ∈ I) (h₂ : (p₂ : R) ∈ I) : p₁ = p₂ := by
  by_contra hne
  have hcop : Nat.Coprime p₁ p₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
  obtain ⟨a, b, hab⟩ := hcop.isCoprime
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one]
  have : ((a * p₁ + b * p₂ : ℤ) : R) = 1 := by rw [hab]; simp
  rw [← this]
  push_cast
  exact I.add_mem (I.mul_mem_left _ h₁) (I.mul_mem_left _ h₂)

section Isometry
variable (q : ℕ) [Fact q.Prime]

theorem mem_Rw_iff_norm_le (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (x : K) :
    x ∈ Rw q K ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  change algebraMap K (PadicAlgCl q) x ∈ padicIntegers q ↔ _
  rw [mem_padicIntegers_iff, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  rfl

theorem norm_coe_units_ne_zero (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (x : (↥K)ˣ) :
    ‖((x : K) : PadicAlgCl q)‖ ≠ 0 := by
  simp only [ne_eq, norm_eq_zero, ZeroMemClass.coe_eq_zero, Units.ne_zero, not_false_eq_true]

theorem exists_forall_norm_eq_zpow (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] :
    ∃ (ϖ : (↥K)ˣ) (k : (↥K)ˣ → ℤ), ∀ x : (↥K)ˣ,
      ‖((x : K) : PadicAlgCl q)‖ = ‖((ϖ : K) : PadicAlgCl q)‖ ^ (k x) ∧
      ‖(((x * ϖ ^ (-(k x)) : (↥K)ˣ) : K) : PadicAlgCl q)‖ = 1 := by
  obtain ⟨v, hsurj, hv, -, -⟩ := ExtCitation.LocalLevel.exists_valuation_units_Kw q K
  have hone : ∀ x : (↥K)ˣ, v x = 1 → ‖((x : K) : PadicAlgCl q)‖ = 1 := by
    intro x hx
    rw [hv, mem_Rw_iff_norm_le, mem_Rw_iff_norm_le] at hx
    have hinv : (((x⁻¹ : (↥K)ˣ) : K) : PadicAlgCl q) = (((x : K) : PadicAlgCl q))⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; rfl
    rw [hinv, norm_inv] at hx
    have hpos : 0 < ‖((x : K) : PadicAlgCl q)‖ := norm_pos_iff.mpr (by simp)
    have := (inv_le_one₀ hpos).mp hx.2
    linarith [hx.1]
  have coe_zpow : ∀ (x : (↥K)ˣ) (k : ℤ), (((x ^ k : (↥K)ˣ) : K) : PadicAlgCl q) = (((x : K) : PadicAlgCl q)) ^ k := by
    intro x k
    rw [Units.val_zpow_eq_zpow_val]
    exact map_zpow₀ (algebraMap K (PadicAlgCl q)) _ _
  have coe_mul : ∀ (x y : (↥K)ˣ), (((x * y : (↥K)ˣ) : K) : PadicAlgCl q) = ((x : K) : PadicAlgCl q) * ((y : K) : PadicAlgCl q) := by
    intro x y; rw [Units.val_mul]; rfl
  obtain ⟨ϖ, hϖ⟩ := hsurj (Multiplicative.ofAdd 1)
  refine ⟨ϖ, fun x => Multiplicative.toAdd (v x), fun x => ?_⟩
  have h1 : v (x * ϖ ^ (-Multiplicative.toAdd (v x))) = 1 := by
    rw [map_mul, map_zpow, hϖ, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_neg, ofAdd_toAdd, mul_inv_cancel]
  have h2 := hone _ h1
  refine ⟨?_, h2⟩
  rw [coe_mul, coe_zpow, norm_mul, norm_zpow, zpow_neg] at h2
  have hϖ0 : ‖((ϖ : K) : PadicAlgCl q)‖ ^ Multiplicative.toAdd (v x) ≠ 0 :=
    zpow_ne_zero _ (norm_coe_units_ne_zero q K ϖ)
  field_simp at h2
  linarith [h2]

theorem norm_map_eq_of_forall_norm_le_one_iff (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q))
    [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂] (α : L₁ ≃+* L₂)
    (hball : ∀ x : L₁, ‖(x : PadicAlgCl q)‖ ≤ 1 ↔ ‖((α x : L₂) : PadicAlgCl q)‖ ≤ 1) (x : L₁) :
    ‖((α x : L₂) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ := by
  by_cases hx : x = 0
  · subst hx; simp

  set αu : (↥L₁)ˣ →* (↥L₂)ˣ := Units.map α.toMonoidHom with hαu
  have hαu_coe : ∀ y : (↥L₁)ˣ, (((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q) = ((α (y : L₁) : L₂) : PadicAlgCl q) := fun y => rfl

  have hone : ∀ y : (↥L₁)ˣ, ‖((y : L₁) : PadicAlgCl q)‖ = 1 → ‖(((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ = 1 := by
    intro y hy
    have h1 : ‖(((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ ≤ 1 := (hball _).1 hy.le
    have h2 : ‖(((αu y⁻¹ : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ ≤ 1 := by
      apply (hball _).1
      have : (((y⁻¹ : (↥L₁)ˣ) : L₁) : PadicAlgCl q) = (((y : L₁) : PadicAlgCl q))⁻¹ := by
        rw [Units.val_inv_eq_inv_val]; rfl
      rw [this, norm_inv, hy, inv_one]
    rw [map_inv] at h2
    have : (((((αu y)⁻¹ : (↥L₂)ˣ)) : L₂) : PadicAlgCl q) = ((((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q))⁻¹ := by
      rw [Units.val_inv_eq_inv_val]; rfl
    rw [this, norm_inv] at h2
    have hpos : 0 < ‖(((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ := norm_pos_iff.mpr (by simp)
    have := (inv_le_one₀ hpos).mp h2
    linarith
  obtain ⟨ϖ, k, hk⟩ := exists_forall_norm_eq_zpow q L₁
  have coe_zpow₂ : ∀ (z : (↥L₂)ˣ) (n : ℤ), (((z ^ n : (↥L₂)ˣ) : L₂) : PadicAlgCl q) = (((z : L₂) : PadicAlgCl q)) ^ n := by
    intro z n; rw [Units.val_zpow_eq_zpow_val]; exact map_zpow₀ (algebraMap L₂ (PadicAlgCl q)) _ _
  have coe_mul₂ : ∀ (z z' : (↥L₂)ˣ), (((z * z' : (↥L₂)ˣ) : L₂) : PadicAlgCl q) = ((z : L₂) : PadicAlgCl q) * ((z' : L₂) : PadicAlgCl q) := by
    intro z z'; rw [Units.val_mul]; rfl

  have hall : ∀ y : (↥L₁)ˣ, ‖(((αu y : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ = ‖(((αu ϖ : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ ^ (k y) := by
    intro y
    have h := hone _ (hk y).2
    rw [map_mul, map_zpow, coe_mul₂, coe_zpow₂, norm_mul, norm_zpow, zpow_neg] at h
    have hϖ0 : ‖(((αu ϖ : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ ^ (k y) ≠ 0 := zpow_ne_zero _ (norm_coe_units_ne_zero q L₂ _)
    field_simp at h
    linarith [h]

  have hq0 : ((q : ℕ) : L₁) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  set qu : (↥L₁)ˣ := Units.mk0 ((q : ℕ) : L₁) hq0 with hqu
  have hqnorm : ‖((qu : L₁) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
    change ‖(((q : ℕ) : L₁) : PadicAlgCl q)‖ = _
    have : (((q : ℕ) : L₁) : PadicAlgCl q) = ((q : ℕ) : ℚ_[q]) := by push_cast; rfl
    rw [this, PadicAlgCl.norm_extends, Padic.norm_p]
  have hαq : (((αu qu : (↥L₂)ˣ) : L₂) : PadicAlgCl q) = ((qu : L₁) : PadicAlgCl q) := by
    rw [hαu_coe]
    change ((α ((q : ℕ) : L₁) : L₂) : PadicAlgCl q) = (((q : ℕ) : L₁) : PadicAlgCl q)
    rw [map_natCast]; push_cast; rfl
  have hkq : k qu ≠ 0 := by
    intro h0
    have := (hk qu).1
    rw [h0, zpow_zero, hqnorm] at this
    have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
    have : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    linarith
  have hϖeq : ‖(((αu ϖ : (↥L₂)ˣ) : L₂) : PadicAlgCl q)‖ = ‖((ϖ : L₁) : PadicAlgCl q)‖ := by
    have e1 := hall qu
    rw [hαq, (hk qu).1] at e1
    exact ((zpow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hkq).1 e1).symm

  have hxu : ((Units.mk0 x hx : (↥L₁)ˣ) : L₁) = x := rfl
  have := hall (Units.mk0 x hx)
  rw [hϖeq, ← (hk (Units.mk0 x hx)).1, hαu_coe] at this
  exact this

end Isometry

section Linear
variable (q : ℕ) [Fact q.Prime]

theorem apply_algebraMap_eq_of_norm_eq (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q))
    [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂] (α : L₁ ≃+* L₂)
    (hiso : ∀ x : L₁, ‖((α x : L₂) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖) (y : ℚ_[q]) :
    α (algebraMap ℚ_[q] L₁ y) = algebraMap ℚ_[q] L₂ y := by
  let f : ℚ_[q] →+ PadicAlgCl q :=
    { toFun := fun y => ((α (algebraMap ℚ_[q] L₁ y) : L₂) : PadicAlgCl q)
      map_zero' := by simp
      map_add' := by intros; simp [map_add] }
  have hf : Continuous f := by
    apply AddMonoidHomClass.continuous_of_bound f 1
    intro z
    rw [one_mul]
    change ‖((α (algebraMap ℚ_[q] L₁ z) : L₂) : PadicAlgCl q)‖ ≤ ‖z‖
    rw [hiso]
    change ‖algebraMap ℚ_[q] (PadicAlgCl q) z‖ ≤ ‖z‖
    rw [norm_algebraMap']
  have hg : Continuous (fun z : ℚ_[q] => algebraMap ℚ_[q] (PadicAlgCl q) z) :=
    (continuous_algebraMap ℚ_[q] (PadicAlgCl q))
  have heq := (Padic.denseRange_ratCast (p := q)).equalizer hf hg (by
    funext r
    change ((α (algebraMap ℚ_[q] L₁ (r : ℚ_[q])) : L₂) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) (r : ℚ_[q])
    rw [map_ratCast, map_ratCast, map_ratCast]
    push_cast
    rfl)
  have := congrFun heq y
  apply Subtype.ext
  exact this

theorem exists_algEquiv_extends (L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q))
    [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂] (α : L₁ ≃+* L₂)
    (hlin : ∀ y : ℚ_[q], α (algebraMap ℚ_[q] L₁ y) = algebraMap ℚ_[q] L₂ y) :
    ∃ β : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q, ∀ x : L₁, β (x : PadicAlgCl q) = ((α x : L₂) : PadicAlgCl q) := by
  haveI : IsAlgClosure L₁ (PadicAlgCl q) := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[q]) L₁⟩
  haveI : IsAlgClosure L₂ (PadicAlgCl q) := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[q]) L₂⟩
  let β₀ : PadicAlgCl q ≃+* PadicAlgCl q := IsAlgClosure.equivOfEquiv (PadicAlgCl q) (PadicAlgCl q) α
  have hβ₀ : ∀ x : L₁, β₀ (x : PadicAlgCl q) = ((α x : L₂) : PadicAlgCl q) := fun x =>
    IsAlgClosure.equivOfEquiv_algebraMap (PadicAlgCl q) (PadicAlgCl q) α x
  refine ⟨AlgEquiv.ofRingEquiv (f := β₀) (fun y => ?_), fun x => hβ₀ x⟩
  change β₀ (((algebraMap ℚ_[q] L₁ y : L₁) : PadicAlgCl q)) = ((algebraMap ℚ_[q] L₂ y : L₂) : PadicAlgCl q)
  rw [hβ₀, hlin]

theorem norm_algEquiv_padicAlgCl (β : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (x : PadicAlgCl q) : ‖β x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv β x).symm

end Linear

end ExtCitation.LocalLevel.Transport

section EngP2
p2m_open "groupCohomology ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

variable {q : ℕ} [Fact q.Prime] (σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (M : IntermediateField ℚ_[q] (PadicAlgCl q))

noncomputable abbrev eM : ↥M ≃ₐ[ℚ_[q]] ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) :=
  IntermediateField.equivMap M (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)

theorem coe_eM (x : M) : ((eM σ M x : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) : PadicAlgCl q) = σ (x : PadicAlgCl q) := rfl

theorem coe_eM_symm (y : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) :
    (((eM σ M).symm y : M) : PadicAlgCl q) = σ.symm (y : PadicAlgCl q) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← coe_eM σ M ((eM σ M).symm y), AlgEquiv.apply_symm_apply]

theorem mem_map_iff (y : PadicAlgCl q) : y ∈ M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q) ↔ σ.symm y ∈ M := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨σ.symm y, h, by simp⟩

section Action

variable {H : Type} [Group H] [MulSemiringAction H M]

noncomputable scoped instance smulMap : SMul H ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) :=
  ⟨fun h y => eM σ M (h • (eM σ M).symm y)⟩

theorem smul_def (h : H) (y : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) :
    h • y = eM σ M (h • (eM σ M).symm y) := rfl

noncomputable scoped instance mulSemiringActionMap : MulSemiringAction H ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) where
  one_smul y := by rw [smul_def, one_smul, AlgEquiv.apply_symm_apply]
  mul_smul g h y := by rw [smul_def, smul_def, smul_def, mul_smul, AlgEquiv.symm_apply_apply]
  smul_zero h := by rw [smul_def, map_zero, smul_zero, map_zero]
  smul_add h x y := by rw [smul_def, smul_def, smul_def, map_add, smul_add, map_add]
  smul_one h := by rw [smul_def, map_one, smul_one, map_one]
  smul_mul h x y := by rw [smul_def, smul_def, smul_def, map_mul, smul_mul', map_mul]

theorem eM_smul (h : H) (x : M) : eM σ M (h • x) = h • eM σ M x := by
  rw [smul_def, AlgEquiv.symm_apply_apply]

theorem eM_symm_smul (h : H) (y : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) :
    (eM σ M).symm (h • y) = h • (eM σ M).symm y := by
  rw [smul_def, AlgEquiv.symm_apply_apply]

scoped instance faithfulSMulMap [FaithfulSMul H M] : FaithfulSMul H ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) :=
  ⟨fun {g h} hgh => FaithfulSMul.eq_of_smul_eq_smul (α := ↥M) fun x => by
    have h1 := hgh (eM σ M x)
    rw [← eM_smul, ← eM_smul] at h1
    exact (eM σ M).injective h1⟩

noncomputable scoped instance mulDistribMulActionUnitsMap : MulDistribMulAction H (↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ :=
  Units.mulDistribMulActionRight

private theorem _root_.ExtCitation.LocalLevel.Transport.coe_smul_units (h : H) (u : (↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) :
    ((h • u : (↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) =
      h • (u : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) := rfl

p2m_export "ExtCitation.LocalLevel.Transport" "coe_smul_units"

noncomputable abbrev uM : (↥M)ˣ →* (↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ :=
  Units.map ((eM σ M : ↥M ≃ₐ[ℚ_[q]] _) : ↥M →* ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))

theorem coe_uM (u : (↥M)ˣ) :
    ((uM σ M u : (↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) = eM σ M (u : M) := rfl

theorem uM_smul [MulDistribMulAction H (↥M)ˣ] (hc : ∀ (h : H) (u : (↥M)ˣ), ((h • u : (↥M)ˣ) : M) = h • (u : M))
    (h : H) (u : (↥M)ˣ) : uM σ M (h • u) = h • uM σ M u := by
  apply Units.ext
  rw [coe_smul_units, coe_uM, coe_uM, hc, eM_smul]

theorem uM_bijective : Function.Bijective (uM σ M) :=
  (Units.mapEquiv ((eM σ M : ↥M ≃ₐ[ℚ_[q]] _) : ↥M ≃* ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))).bijective

end Action

end ExtCitation.LocalLevel.Transport
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

section Residue

variable {q : ℕ} [Fact q.Prime] (σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (hσ : ∀ x : PadicAlgCl q, ‖σ x‖ = ‖x‖)
  (K K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] [FiniteDimensional ℚ_[q] K']
  (hKK' : ∀ x : PadicAlgCl q, x ∈ K' ↔ σ.symm x ∈ K)

noncomputable def eK : ↥K ≃+* ↥K' where
  toFun x := ⟨σ x, (hKK' _).mpr (by rw [AlgEquiv.symm_apply_apply]; exact x.2)⟩
  invFun y := ⟨σ.symm y, (hKK' _).mp y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul σ _ _)
  map_add' x y := Subtype.ext (map_add σ _ _)

theorem coe_eK (x : K) : ((eK σ K K' hKK' x : K') : PadicAlgCl q) = σ x := rfl

include hσ in
theorem nnnorm_σ (x : PadicAlgCl q) : ‖σ x‖₊ = ‖x‖₊ := NNReal.eq (hσ x)

include hσ hKK' in

theorem exists_ringEquiv_Rw : Nonempty (↥(Rw q K) ≃+* ↥(Rw q K')) := by
  refine ⟨{ toFun := fun x => ⟨eK σ K K' hKK' x, ?_⟩
            invFun := fun y => ⟨(eK σ K K' hKK').symm y, ?_⟩
            left_inv := fun x => Subtype.ext (RingEquiv.symm_apply_apply _ _)
            right_inv := fun y => Subtype.ext (RingEquiv.apply_symm_apply _ _)
            map_mul' := fun x y => Subtype.ext (map_mul _ _ _)
            map_add' := fun x y => Subtype.ext (map_add _ _ _) }⟩
  · show ‖σ ((x : K) : PadicAlgCl q)‖₊ ≤ 1
    rw [nnnorm_σ σ hσ]
    exact x.2
  · show ‖(((eK σ K K' hKK').symm y : K) : PadicAlgCl q)‖₊ ≤ 1
    have h1 : (((eK σ K K' hKK').symm y : K) : PadicAlgCl q) = σ.symm ((y : K') : PadicAlgCl q) := rfl
    rw [h1, ← nnnorm_σ σ hσ, AlgEquiv.apply_symm_apply]
    exact y.2

include hσ hKK' in
theorem natCard_residueField_eq :
    Nat.card (IsLocalRing.ResidueField ↥(Rw q K')) = Nat.card (IsLocalRing.ResidueField ↥(Rw q K)) := by
  obtain ⟨e⟩ := exists_ringEquiv_Rw σ hσ K K' hKK'
  exact (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv).symm

end Residue
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

section Datum

variable {q : ℕ} [Fact q.Prime] (σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (hσ : ∀ x : PadicAlgCl q, ‖σ x‖ = ‖x‖)
    {L L' : IntermediateField ℚ_[q] (PadicAlgCl q)} {G : Type} [Group G]
    [MulSemiringAction G L] [MulSemiringAction G L']
    (αL : ↥L ≃+* ↥L') (hαL : ∀ y : L, ((αL y : L') : PadicAlgCl q) = σ (y : PadicAlgCl q))
    (hαG : ∀ (g : G) (y : L), αL (g • y) = g • αL y)
    {K K' : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K] [FiniteDimensional ℚ_[q] K']
    (hKK' : ∀ x : PadicAlgCl q, x ∈ K' ↔ σ.symm x ∈ K)
    {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] {hLM : L ≤ M}
    {H : Type} [Group H] [Finite H] [MulSemiringAction H M] [FaithfulSMul H M] [MulDistribMulAction H (↥M)ˣ]
    {NL Nn : Subgroup H} [NL.Normal] [Nn.Normal] {e : G ≃* H ⧸ NL} {φ : H} {π : (↥M)ˣ}

include hαL in
theorem mem_layer_iff_symm_mem (x : PadicAlgCl q) : x ∈ L' ↔ σ.symm x ∈ L := by
  constructor
  · intro hx
    have h1 := hαL (αL.symm ⟨x, hx⟩)
    rw [RingEquiv.apply_symm_apply] at h1
    have h2 : σ.symm x = ((αL.symm ⟨x, hx⟩ : L) : PadicAlgCl q) := σ.symm_apply_eq.mpr h1
    rw [h2]
    exact (αL.symm ⟨x, hx⟩).2
  · intro hx
    have h1 := hαL ⟨σ.symm x, hx⟩
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact (αL ⟨σ.symm x, hx⟩).2

include hαL in
theorem le_map (hLM : L ≤ M) : L' ≤ M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q) := by
  intro x hx
  rw [mem_map_iff]
  exact hLM ((mem_layer_iff_symm_mem σ αL hαL x).mp hx)

include hσ hαL hαG hKK' in

theorem isUnramOverlayerDatum_map (d : IsUnramOverlayerDatum q L G K M hLM H NL Nn e φ π)
    (hLM' : L' ≤ M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) :
    IsUnramOverlayerDatum q L' G K' (M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) hLM' H NL Nn e φ (uM σ M π) where
  smul_algebraMap h x := by
    rw [smul_def, show (eM σ M).symm (algebraMap ℚ_[q] _ x) = algebraMap ℚ_[q] (↥M) x from (eM σ M).symm.commutes x,
      d.smul_algebraMap, AlgEquiv.commutes]
  coe_smul_units h u := rfl
  mem_base_iff x := by
    rw [hKK', ← coe_eM_symm, d.mem_base_iff]
    constructor
    · intro h1 h
      have h2 := congrArg (eM σ M) (h1 h)
      rwa [← smul_def, AlgEquiv.apply_symm_apply] at h2
    · intro h1 h
      apply (eM σ M).injective
      rw [← smul_def, AlgEquiv.apply_symm_apply]
      exact h1 h
  mem_layer_iff x := by
    rw [mem_layer_iff_symm_mem σ αL hαL, ← coe_eM_symm, d.mem_layer_iff]
    constructor
    · intro h1 h hh
      have h2 := congrArg (eM σ M) (h1 h hh)
      rwa [← smul_def, AlgEquiv.apply_symm_apply] at h2
    · intro h1 h hh
      apply (eM σ M).injective
      rw [← smul_def, AlgEquiv.apply_symm_apply]
      exact h1 h hh
  coe_smul_eq g h hgh x := by
    set x₀ : ↥L := αL.symm x with hx₀
    have hx : x = αL x₀ := by rw [hx₀, RingEquiv.apply_symm_apply]
    have h1 : ((g • x : L') : PadicAlgCl q) = σ (((h • (⟨(x₀ : PadicAlgCl q), hLM x₀.2⟩ : ↥M)) : ↥M) : PadicAlgCl q) := by
      rw [hx, ← hαG, hαL, d.coe_smul_eq g h hgh x₀]
    have h2 : (⟨(x : PadicAlgCl q), hLM' x.2⟩ : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) =
        eM σ M ⟨(x₀ : PadicAlgCl q), hLM x₀.2⟩ := by
      apply Subtype.ext
      rw [coe_eM]
      show (x : PadicAlgCl q) = σ (x₀ : PadicAlgCl q)
      rw [hx, hαL]
    rw [h1, h2, ← eM_smul, coe_eM]
  card_quotient := d.card_quotient
  mem_zpowers := d.mem_zpowers
  frobenius x hx hx1 := by
    set x₀ : ↥M := (eM σ M).symm x with hx₀
    have hxx : (x : PadicAlgCl q) = σ (x₀ : PadicAlgCl q) := by
      rw [hx₀, coe_eM_symm, AlgEquiv.apply_symm_apply]
    have hfix : ∀ h ∈ Nn, h • x₀ = x₀ := fun h hh => by rw [hx₀, ← eM_symm_smul, hx h hh]
    have hx1' : ‖(x₀ : PadicAlgCl q)‖ ≤ 1 := by rw [← hσ, ← hxx]; exact hx1
    have key := d.frobenius x₀ hfix hx1'
    have hφx : ((φ • x : ↥(M.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) : PadicAlgCl q) = σ ((φ • x₀ : ↥M) : PadicAlgCl q) := by
      rw [show φ • x = eM σ M (φ • x₀) from rfl, coe_eM]
    rw [natCard_residueField_eq σ hσ K K' hKK', hφx, hxx, ← map_pow, ← map_sub, hσ]
    exact key
  smul_pi h := by rw [← uM_smul σ M d.coe_smul_units, d.smul_pi]
  pi_mem := by
    show σ (((π : (↥M)ˣ) : ↥M) : PadicAlgCl q) ∈ K'
    rw [hKK', AlgEquiv.symm_apply_apply]
    exact d.pi_mem
  norm_pi_lt := by
    show ‖σ (((π : (↥M)ˣ) : ↥M) : PadicAlgCl q)‖ < 1
    rw [hσ]
    exact d.norm_pi_lt
  norm_le_norm_pi y hy hy1 := by
    set y₀ : ↥M := (eM σ M).symm y with hy₀
    have hyy : (y : PadicAlgCl q) = σ (y₀ : PadicAlgCl q) := by
      rw [hy₀, coe_eM_symm, AlgEquiv.apply_symm_apply]
    have hfix : ∀ h ∈ Nn, h • y₀ = y₀ := fun h hh => by rw [hy₀, ← eM_symm_smul, hy h hh]
    rw [hyy, hσ] at hy1 ⊢
    show ‖(y₀ : PadicAlgCl q)‖ ≤ ‖σ (((π : (↥M)ˣ) : ↥M) : PadicAlgCl q)‖
    rw [hσ]
    exact d.norm_le_norm_pi y₀ hfix hy1

end Datum
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

end ExtCitation.LocalLevel.Transport
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

section CohomologyHelpers

theorem map_id_comp_map {G H : Type} [Group G] [Group H] {A B : Rep ℤ G} {C : Rep ℤ H}
    (ψ : H →* G) (γ : A ⟶ B) (ι : Rep.res ψ B ⟶ C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) γ n ≫ groupCohomology.map ψ ι n =
      groupCohomology.map ψ ((Rep.resFunctor ψ).map γ ≫ ι) n :=
  (groupCohomology.map_comp (MonoidHom.id G) ψ γ ι n).symm

theorem map_comp_map_id {G H : Type} [Group G] [Group H] {A : Rep ℤ G} {B C : Rep ℤ H}
    (ψ : H →* G) (ι : Rep.res ψ A ⟶ B) (φ : B ⟶ C) (n : ℕ) :
    groupCohomology.map ψ ι n ≫ groupCohomology.map (MonoidHom.id H) φ n = groupCohomology.map ψ (ι ≫ φ) n :=
  (groupCohomology.map_comp ψ (MonoidHom.id H) ι φ n).symm

theorem map_id_H2π_carryFun {Q : Type} [Group Q] (t : Q) (ht : ∀ g : Q, g ∈ Subgroup.zpowers t) (hfin : IsOfFinOrder t)
    (A B : Rep ℤ Q) (φ : A ⟶ B) (a : A) (ha : A.ρ t a = a)
    (hza : carryFun t ht hfin a ∈ cocycles₂ A) (hzb : carryFun t ht hfin (φ.hom a) ∈ cocycles₂ B) :
    (groupCohomology.map (MonoidHom.id Q) φ 2).hom ((H2π A).hom ⟨carryFun t ht hfin a, hza⟩) =
      (H2π B).hom ⟨carryFun t ht hfin (φ.hom a), hzb⟩ := by
  have h := groupCohomology.map_carry_H2pi_eq_smul_carry (MonoidHom.id Q) Function.injective_id t ht hfin 1 t
    (by rw [pow_one]; rfl) ht hfin A B φ a ha hza hzb
  rwa [Nat.gcd_one_right, Nat.div_one, one_smul] at h

end CohomologyHelpers
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

end ExtCitation.LocalLevel.Transport
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

section RepHom

variable {G : Type} [Group G] {X Y : Type} [CommGroup X] [CommGroup Y] [MulDistribMulAction G X] [MulDistribMulAction G Y]

noncomputable def repHom (f : X →* Y) (hf : ∀ (g : G) (m : X), f (g • m) = g • f m) :
    Rep.ofMulDistribMulAction G X ⟶ Rep.ofMulDistribMulAction G Y :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun g => LinearMap.ext fun x => by
    change Additive.ofMul (f (g • Additive.toMul x)) = Additive.ofMul (g • f (Additive.toMul x))
    rw [hf]⟩

@[scoped simp] theorem repHom_hom_apply (f : X →* Y) (hf : ∀ (g : G) (m : X), f (g • m) = g • f m) (x : Additive X) :
    (repHom f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

end RepHom
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

end ExtCitation.LocalLevel.Transport
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
p2m_open "ExtCitation.LocalLevel ExtCitation"

open ExtCitation.LocalLevel.Transport

set_option maxHeartbeats 1600000 in

theorem IsLocalFundamentalClass.transport_of_isometry
    (q : ℕ) [Fact q.Prime]
    (β : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) (hβ : ∀ x : PadicAlgCl q, ‖β x‖ = ‖x‖)
    {L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L₁] [FiniteDimensional ℚ_[q] L₂]
    {G : Type} [Group G] [Finite G]
    [MulSemiringAction G L₁] [FaithfulSMul G L₁] [MulDistribMulAction G (↥L₁)ˣ]
    [MulSemiringAction G L₂] [FaithfulSMul G L₂] [MulDistribMulAction G (↥L₂)ˣ]
    (hG₁ : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L₁ x = algebraMap ℚ_[q] L₁ x)
    (hG₂ : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L₂ x = algebraMap ℚ_[q] L₂ x)
    (hcompat₁ : ∀ (g : G) (v : (↥L₁)ˣ), ((g • v : (↥L₁)ˣ) : L₁) = g • (v : L₁))
    (hcompat₂ : ∀ (g : G) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂))
    (α : L₁ ≃+* L₂) (hαβ : ∀ y : L₁, ((α y : L₂) : PadicAlgCl q) = β (y : PadicAlgCl q))
    (hα : ∀ (g : G) (y : L₁), α (g • y) = g • α y)
    {K₀₁ K₀₂ : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] K₀₁] [FiniteDimensional ℚ_[q] K₀₂]
    (hK₁ : IsBase q L₁ G K₀₁) (hK₂ : IsBase q L₂ G K₀₂)
    (γ : Rep.ofMulDistribMulAction G (↥L₁)ˣ ⟶ Rep.ofMulDistribMulAction G (↥L₂)ˣ)
    (hγ : ∀ v : (↥L₁)ˣ, (Additive.toMul (γ.hom (Additive.ofMul v)) : (↥L₂)ˣ) = Units.map α.toMonoidHom v)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L₁)ˣ)) (hu : IsLocalFundamentalClass q L₁ G K₀₁ u) :
    IsLocalFundamentalClass q L₂ G K₀₂ ((groupCohomology.map (MonoidHom.id G) γ 2).hom u) := by
  intro M₂ _ hLM₂ H _ _ _ _ _ NL Nn _ _ e φ π₂ d₂ ι₂ hι₂ hfin hc

  set σ : PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q := β.symm with hσdef
  have hσ : ∀ x : PadicAlgCl q, ‖σ x‖ = ‖x‖ := fun x => by
    rw [← hβ (σ x), hσdef, AlgEquiv.apply_symm_apply]
  have hαL : ∀ y : L₂, ((α.symm y : L₁) : PadicAlgCl q) = σ (y : PadicAlgCl q) := fun y => by
    apply β.injective
    rw [← hαβ, RingEquiv.apply_symm_apply, hσdef, AlgEquiv.apply_symm_apply]
  have hαG' : ∀ (g : G) (y : L₂), α.symm (g • y) = g • α.symm y := fun g y => by
    apply α.injective
    rw [RingEquiv.apply_symm_apply, hα, RingEquiv.apply_symm_apply]
  have hKK : ∀ x : PadicAlgCl q, x ∈ K₀₁ ↔ σ.symm x ∈ K₀₂ := by
    intro x
    rw [hσdef, AlgEquiv.symm_symm]
    constructor
    · intro hx
      have hxL : x ∈ L₁ := hK₁.le hx
      have h1 := (hK₁.mem_iff ⟨x, hxL⟩).mp hx
      have h2 : ∀ g : G, g • α ⟨x, hxL⟩ = α ⟨x, hxL⟩ := fun g => by rw [← hα, h1 g]
      have h3 := (hK₂.mem_iff (α ⟨x, hxL⟩)).mpr h2
      rwa [hαβ] at h3
    · intro hx
      have hxL2 : β x ∈ L₂ := hK₂.le hx
      have hxL : x ∈ L₁ := by
        rw [mem_layer_iff_symm_mem σ α.symm hαL x, hσdef, AlgEquiv.symm_symm]
        exact hxL2
      have h1 := (hK₂.mem_iff ⟨β x, hxL2⟩).mp hx
      have h2 : (⟨β x, hxL2⟩ : ↥L₂) = α ⟨x, hxL⟩ := Subtype.ext (by rw [hαβ])
      rw [h2] at h1
      have h3 : ∀ g : G, g • (⟨x, hxL⟩ : ↥L₁) = ⟨x, hxL⟩ := fun g => α.injective (by rw [hα, h1 g])
      exact (hK₁.mem_iff ⟨x, hxL⟩).mpr h3
  have hLM₁ : L₁ ≤ (M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) := le_map σ α.symm hαL hLM₂
  have d₁ := isUnramOverlayerDatum_map σ hσ α.symm hαL hαG' hKK d₂ hLM₁

  let f₂₁ : (↥M₂)ˣ →* (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ := uM σ M₂
  let f₁₂ : (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ →* (↥M₂)ˣ :=
    Units.map (((eM σ M₂).symm : ↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) ≃ₐ[ℚ_[q]] ↥M₂) : ↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) →* ↥M₂)
  have hf₂₁ : ∀ (h : H) (w : (↥M₂)ˣ), f₂₁ (h • w) = h • f₂₁ w := uM_smul σ M₂ d₂.coe_smul_units
  have hf₁₂ : ∀ (h : H) (w : (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ), f₁₂ (h • w) = h • f₁₂ w := by
    intro h w
    apply Units.ext
    rw [d₂.coe_smul_units]
    show (eM σ M₂).symm ((h • w : (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) : ↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) = h • (eM σ M₂).symm (w : ↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))
    rw [Transport.coe_smul_units, eM_symm_smul]
  have hf₁₂₂₁ : ∀ w : (↥M₂)ˣ, f₁₂ (f₂₁ w) = w := fun w => Units.ext ((eM σ M₂).symm_apply_apply _)
  have hf₂₁₁₂ : ∀ w : (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ, f₂₁ (f₁₂ w) = w := fun w => Units.ext ((eM σ M₂).apply_symm_apply _)
  let B : (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) ⟶ (Rep.ofMulDistribMulAction H (↥M₂)ˣ) := repHom f₁₂ hf₁₂
  let B' : (Rep.ofMulDistribMulAction H (↥M₂)ˣ) ⟶ (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) := repHom f₂₁ hf₂₁
  have hB'B : B' ≫ B = 𝟙 _ := by
    refine Rep.hom_ext ?_
    ext w
    rw [Rep.hom_comp, Rep.hom_id]
    show B.hom (B'.hom w) = w
    rw [repHom_hom_apply, repHom_hom_apply, toMul_ofMul, hf₁₂₂₁, ofMul_toMul]

  let ψ : H →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' NL)
  let ι₁ : Rep.res ψ (Rep.ofMulDistribMulAction G (↥L₁)ˣ) ⟶ (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) := (Rep.resFunctor ψ).map γ ≫ (ι₂ ≫ B')
  have hι₁ : ∀ v : (↥L₁)ˣ, (((Additive.toMul (ι₁.hom (Additive.ofMul v)) : (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ) : ↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q))) : PadicAlgCl q) =
      ((v : L₁) : PadicAlgCl q) := by
    intro v
    have h1 : ι₁.hom (Additive.ofMul v) = B'.hom (ι₂.hom (γ.hom (Additive.ofMul v))) := rfl
    have h2 : γ.hom (Additive.ofMul v) = Additive.ofMul (Units.map α.toMonoidHom v) := by rw [← hγ, ofMul_toMul]
    rw [h1, repHom_hom_apply, toMul_ofMul, h2]
    show σ ((((Additive.toMul (ι₂.hom (Additive.ofMul (Units.map α.toMonoidHom v))) : (↥M₂)ˣ) : ↥M₂) : PadicAlgCl q)) = _
    rw [hι₂ (Units.map α.toMonoidHom v)]
    show σ (((α (v : L₁)) : L₂) : PadicAlgCl q) = _
    rw [hαβ, hσdef, AlgEquiv.symm_apply_apply]

  have hfix₁ : ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn).ρ (QuotientGroup.mk' Nn φ) d₁.piInv = d₁.piInv := by
    apply Subtype.ext
    change ((Representation.ofQuotient ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).ρ.toInvariants Nn) Nn (φ : H ⧸ Nn)) d₁.piInv).1 = _
    rw [Representation.ofQuotient_coe_apply]
    change (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).ρ φ (d₁.piInv.1) = _
    rw [IsUnramOverlayerDatum.piInv_val, Rep.ofMulDistribMulAction_ρ_apply_apply]
    exact congrArg Additive.ofMul (d₁.smul_pi φ)
  have hc₁ : carryFun (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv ∈ cocycles₂ ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn) :=
    groupCohomology.carryFun_mem_cocycles2 (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv hfix₁

  have key := hu (M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)) hLM₁ H NL Nn e φ (uM σ M₂ π₂) d₁ ι₁ hι₁ hfin hc₁

  have hLHS : (groupCohomology.map ψ ι₁ 2).hom u =
      (groupCohomology.map (MonoidHom.id H) B' 2).hom ((groupCohomology.map ψ ι₂ 2).hom ((groupCohomology.map (MonoidHom.id G) γ 2).hom u)) := by
    have E := (map_id_comp_map ψ γ (ι₂ ≫ B') 2).symm
    rw [← map_comp_map_id ψ ι₂ B' 2] at E
    have h := congrArg (fun T => (ModuleCat.Hom.hom T) u) E
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

  have hback : ∀ y : groupCohomology (Rep.ofMulDistribMulAction H (↥M₂)ˣ) 2,
      (groupCohomology.map (MonoidHom.id H) B 2).hom ((groupCohomology.map (MonoidHom.id H) B' 2).hom y) = y := by
    intro y
    have h := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp B' B 2)
    simp only [hB'B, groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    exact h.symm

  have hpi : ((Rep.quotientToInvariantsFunctor ℤ Nn).map B).hom d₁.piInv = d₂.piInv := by
    apply Subtype.ext
    show Additive.ofMul (f₁₂ (f₂₁ π₂)) = Additive.ofMul π₂
    rw [hf₁₂₂₁]
  have hzb : carryFun (QuotientGroup.mk' Nn φ) d₂.mem_zpowers hfin (((Rep.quotientToInvariantsFunctor ℤ Nn).map B).hom d₁.piInv) ∈
      cocycles₂ ((Rep.ofMulDistribMulAction H (↥M₂)ˣ).quotientToInvariants Nn) := by
    rw [hpi]; exact hc
  have hcarry := map_id_H2π_carryFun (QuotientGroup.mk' Nn φ) d₂.mem_zpowers hfin
    ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn) ((Rep.ofMulDistribMulAction H (↥M₂)ˣ).quotientToInvariants Nn) ((Rep.quotientToInvariantsFunctor ℤ Nn).map B)
    d₁.piInv hfix₁ hc₁ hzb
  have e2 : (⟨carryFun (QuotientGroup.mk' Nn φ) d₂.mem_zpowers hfin (((Rep.quotientToInvariantsFunctor ℤ Nn).map B).hom d₁.piInv), hzb⟩ :
      cocycles₂ ((Rep.ofMulDistribMulAction H (↥M₂)ˣ).quotientToInvariants Nn)) = ⟨carryFun (QuotientGroup.mk' Nn φ) d₂.mem_zpowers hfin d₂.piInv, hc⟩ :=
    Subtype.ext (congrArg (carryFun (QuotientGroup.mk' Nn φ) d₂.mem_zpowers hfin) hpi)
  have hcarry' := hcarry.trans (congrArg ((H2π ((Rep.ofMulDistribMulAction H (↥M₂)ˣ).quotientToInvariants Nn)).hom) e2)
  have hnat : ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥M₂)ˣ)).hom
        ((groupCohomology.map (MonoidHom.id (H ⧸ Nn)) ((Rep.quotientToInvariantsFunctor ℤ Nn).map B) 2).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv, hc₁⟩)) =
      (groupCohomology.map (MonoidHom.id H) B 2).hom
        (((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv, hc₁⟩)) :=
    congrArg (fun T => (ModuleCat.Hom.hom T)
      ((H2π ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv, hc₁⟩))
      ((infNatTrans ℤ Nn 2).naturality B)

  have X1def : (groupCohomology.map (MonoidHom.id H) B 2).hom ((groupCohomology.map ψ ι₁ 2).hom u) =
      (groupCohomology.map (MonoidHom.id H) B 2).hom
        (((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ)).hom
          ((H2π ((Rep.ofMulDistribMulAction H (↥(M₂.map (σ : PadicAlgCl q →ₐ[ℚ_[q]] PadicAlgCl q)))ˣ).quotientToInvariants Nn)).hom ⟨carryFun (QuotientGroup.mk' Nn φ) d₁.mem_zpowers hfin d₁.piInv, hc₁⟩)) :=
    congrArg _ key
  have s1 : (groupCohomology.map ψ ι₂ 2).hom ((groupCohomology.map (MonoidHom.id G) γ 2).hom u) =
      (groupCohomology.map (MonoidHom.id H) B 2).hom ((groupCohomology.map (MonoidHom.id H) B' 2).hom
        ((groupCohomology.map ψ ι₂ 2).hom ((groupCohomology.map (MonoidHom.id G) γ 2).hom u))) := (hback _).symm
  have s2 : (groupCohomology.map (MonoidHom.id H) B 2).hom ((groupCohomology.map (MonoidHom.id H) B' 2).hom
        ((groupCohomology.map ψ ι₂ 2).hom ((groupCohomology.map (MonoidHom.id G) γ 2).hom u))) =
      (groupCohomology.map (MonoidHom.id H) B 2).hom ((groupCohomology.map ψ ι₁ 2).hom u) := by rw [← hLHS]
  exact s1.trans (s2.trans (X1def.trans (hnat.symm.trans (congrArg _ hcarry'))))

end ExtCitation.LocalLevel
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

end EngP2
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.IsBase LocalLevel.IsLocalFundamentalClass LocalLevel.existsUnique_isLocalFundamentalClass LocalLevel.exists_valuation_units_Kw LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "IsBase IsUnramOverlayerDatum IsUnramOverlayerDatum.piInv_val IsLocalFundamentalClass Rw existsUnique_isLocalFundamentalClass exists_valuation_units_Kw finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Transport
p2m_open "ExtCitation.LocalLevel ExtCitation"

section Solvable
p2m_open "ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel"

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

section Assembly
p2m_open "groupCohomology ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel"

noncomputable def unitsRepHom {q : ℕ} [Fact q.Prime] {L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)}
    {G : Type} [Group G] [MulSemiringAction G L₁] [MulDistribMulAction G (↥L₁)ˣ]
    [MulSemiringAction G L₂] [MulDistribMulAction G (↥L₂)ˣ]
    (hcompat₁ : ∀ (g : G) (v : (↥L₁)ˣ), ((g • v : (↥L₁)ˣ) : L₁) = g • (v : L₁))
    (hcompat₂ : ∀ (g : G) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂))
    (α : L₁ ≃+* L₂) (hα : ∀ (g : G) (y : L₁), α (g • y) = g • α y) :
    Rep.ofMulDistribMulAction G (↥L₁)ˣ ⟶ Rep.ofMulDistribMulAction G (↥L₂)ˣ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (MonoidHom.toAdditive (Units.map α.toMonoidHom)).toIntLinearMap (fun g v => by
      change Additive.ofMul (Units.map α.toMonoidHom (Additive.toMul ((Rep.ofMulDistribMulAction G (↥L₁)ˣ).ρ g v))) =
        (Rep.ofMulDistribMulAction G (↥L₂)ˣ).ρ g (Additive.ofMul (Units.map α.toMonoidHom (Additive.toMul v)))
      rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul]
      congr 1
      apply Units.ext
      change α ((g • Additive.toMul (α := (↥L₁)ˣ) v : (↥L₁)ˣ) : L₁) =
        ((g • Units.map α.toMonoidHom (Additive.toMul (α := (↥L₁)ˣ) v) : (↥L₂)ˣ) : L₂)
      rw [hcompat₁, hcompat₂, Units.coe_map]
      exact hα g _))

theorem unitsRepHom_apply {q : ℕ} [Fact q.Prime] {L₁ L₂ : IntermediateField ℚ_[q] (PadicAlgCl q)}
    {G : Type} [Group G] [MulSemiringAction G L₁] [MulDistribMulAction G (↥L₁)ˣ]
    [MulSemiringAction G L₂] [MulDistribMulAction G (↥L₂)ˣ]
    (hcompat₁ : ∀ (g : G) (v : (↥L₁)ˣ), ((g • v : (↥L₁)ˣ) : L₁) = g • (v : L₁))
    (hcompat₂ : ∀ (g : G) (v : (↥L₂)ˣ), ((g • v : (↥L₂)ˣ) : L₂) = g • (v : L₂))
    (α : L₁ ≃+* L₂) (hα : ∀ (g : G) (y : L₁), α (g • y) = g • α y) (v : (↥L₁)ˣ) :
    (Additive.toMul ((unitsRepHom hcompat₁ hcompat₂ α hα).hom (Additive.ofMul v)) : (↥L₂)ˣ) = Units.map α.toMonoidHom v := rfl

theorem aux
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (q₁ : ℕ) [Fact q₁.Prime] (hq₁ : ((q₁ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] L₁]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₁] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₁]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ]
    (Φ₁ : w.adicCompletion K ≃+* L₁)
    (hG₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₁]), g • algebraMap ℚ_[q₁] L₁ y = algebraMap ℚ_[q₁] L₁ y)
    (hc₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₁)ˣ), ((g • y : (↥L₁)ˣ) : L₁) = g • (y : L₁))
    (hΦ₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₁ (g • y) = g • Φ₁ y)
    (K₀₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] K₀₁]
    (hK₁ : ExtCitation.LocalLevel.IsBase q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁)
    (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hθ₁ : ∀ y : (↥L₁)ˣ, ((Additive.toMul ((θ₁).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₁).symm (y : L₁))
    (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ))
    (hu₁ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁ u₁)
    (q₂ : ℕ) [Fact q₂.Prime] (hq₂ : ((q₂ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] L₂]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₂] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₂]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ]
    (Φ₂ : w.adicCompletion K ≃+* L₂)
    (hG₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₂]), g • algebraMap ℚ_[q₂] L₂ y = algebraMap ℚ_[q₂] L₂ y)
    (hc₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₂)ˣ), ((g • y : (↥L₂)ˣ) : L₂) = g • (y : L₂))
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₂ (g • y) = g • Φ₂ y)
    (K₀₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] K₀₂]
    (hK₂ : ExtCitation.LocalLevel.IsBase q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂)
    (θ₂ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hθ₂ : ∀ y : (↥L₂)ˣ, ((Additive.toMul ((θ₂).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₂).symm (y : L₂))
    (u₂ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ))
    (hu₂ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂ u₂) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₁ 2).hom u₁ =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₂ 2).hom u₂ := by

  haveI : w.asIdeal.IsPrime := w.isPrime
  obtain rfl : q₁ = q₂ := prime_eq_of_natCast_mem w.asIdeal q₁ q₂ Fact.out Fact.out hq₁ hq₂

  set α : L₁ ≃+* L₂ := Φ₁.symm.trans Φ₂ with hαdef
  have hαΦ : ∀ y, α (Φ₁ y) = Φ₂ y := fun y => by simp [hαdef]
  have hα : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : L₁), α (g • y) = g • α y := by
    intro g y
    obtain ⟨z, rfl⟩ := Φ₁.surjective y
    rw [← hΦ₁, hαΦ, hαΦ, hΦ₂]
  obtain ⟨hball₁, -⟩ :=
    NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv K w q₁ L₁ Φ₁
  obtain ⟨hball₂, -⟩ :=
    NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv K w q₁ L₂ Φ₂
  have hball : ∀ x : L₁, ‖(x : PadicAlgCl q₁)‖ ≤ 1 ↔ ‖((α x : L₂) : PadicAlgCl q₁)‖ ≤ 1 := by
    intro x
    obtain ⟨z, rfl⟩ := Φ₁.surjective x
    rw [← hball₁ z, hαΦ, ← hball₂ z]
  have hiso := norm_map_eq_of_forall_norm_le_one_iff q₁ L₁ L₂ α hball
  have hlin := apply_algebraMap_eq_of_norm_eq q₁ L₁ L₂ α hiso

  obtain ⟨β, hβα⟩ := exists_algEquiv_extends q₁ L₁ L₂ α hlin
  have hβiso := norm_algEquiv_padicAlgCl q₁ β

  set γ := unitsRepHom hc₁ hc₂ α hα with hγdef
  have hT := IsLocalFundamentalClass.transport_of_isometry q₁ β hβiso hG₁ hG₂ hc₁ hc₂ α (fun y => (hβα y).symm) hα hK₁ hK₂
    γ (unitsRepHom_apply hc₁ hc₂ α hα) u₁ hu₁

  have hsolv := isSolvable_layer q₁ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) hG₂ K₀₂ hK₂
  obtain ⟨u, -, huniq⟩ := ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q₁ L₂
    (↥(NumberField.PlaceDecomp.decomp E K w)) hG₂ hc₂ hsolv K₀₂ hK₂
  have hequ : (groupCohomology.map (MonoidHom.id _) γ 2).hom u₁ = u₂ := (huniq _ hT).trans (huniq _ hu₂).symm

  have hθ : θ₁ = γ ≫ θ₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rw [Rep.hom_comp]
    change θ₁.hom x = θ₂.hom (γ.hom x)
    apply Additive.toMul.injective
    apply Units.ext
    have e1 := hθ₁ (Additive.toMul x)
    have e2 := hθ₂ (Units.map α.toMonoidHom (Additive.toMul x))
    have e3 : γ.hom x = Additive.ofMul (Units.map α.toMonoidHom (Additive.toMul x)) :=
      congrArg Additive.ofMul (unitsRepHom_apply hc₁ hc₂ α hα (Additive.toMul x))
    rw [e3]
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [Units.coe_map]
    change Φ₁.symm _ = Φ₂.symm (α _)
    rw [hαdef, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  rw [hθ, ← hequ, groupCohomology.map_id_comp]
  rfl

end Assembly
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

end ExtCitation.LocalLevel.Transport
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion.ExtCitation.LocalLevel.Transport"

open ExtCitation.LocalLevel.Transport in

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (w : HeightOneSpectrum (𝓞 K))
    (q₁ : ℕ) [Fact q₁.Prime] (_ : ((q₁ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] L₁]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₁] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₁]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ]
    (Φ₁ : w.adicCompletion K ≃+* L₁)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₁]), g • algebraMap ℚ_[q₁] L₁ y = algebraMap ℚ_[q₁] L₁ y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₁)ˣ), ((g • y : (↥L₁)ˣ) : L₁) = g • (y : L₁))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₁ (g • y) = g • Φ₁ y)
    (K₀₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] K₀₁]
    (_ : ExtCitation.LocalLevel.IsBase q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁)
    (θ₁ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L₁)ˣ, ((Additive.toMul ((θ₁).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₁).symm (y : L₁))
    (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₁)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₁ L₁ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₁ u₁)
    (q₂ : ℕ) [Fact q₂.Prime] (_ : ((q₂ : ℕ) : 𝓞 K) ∈ w.asIdeal) (L₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] L₂]
    [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L₂] [FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L₂]
    [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ]
    (Φ₂ : w.adicCompletion K ≃+* L₂)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q₂]), g • algebraMap ℚ_[q₂] L₂ y = algebraMap ℚ_[q₂] L₂ y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L₂)ˣ), ((g • y : (↥L₂)ˣ) : L₂) = g • (y : L₂))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ₂ (g • y) = g • Φ₂ y)
    (K₀₂ : IntermediateField ℚ_[q₂] (PadicAlgCl q₂)) [FiniteDimensional ℚ_[q₂] K₀₂]
    (_ : ExtCitation.LocalLevel.IsBase q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂)
    (θ₂ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L₂)ˣ, ((Additive.toMul ((θ₂).hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = (Φ₂).symm (y : L₂))
    (u₂ : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L₂)ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₂ L₂ (↥(NumberField.PlaceDecomp.decomp E K w)) K₀₂ u₂) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₁ 2).hom u₁ =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ₂ 2).hom u₂ := by
  exact aux E K w q₁ ‹_› L₁ Φ₁ ‹_› ‹_› ‹_› K₀₁ ‹_› θ₁ ‹_› u₁ ‹_› q₂ ‹_› L₂ Φ₂ ‹_› ‹_› ‹_› K₀₂ ‹_› θ₂ ‹_› u₂ ‹_›

end S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
end P2MW
export P2MW.S_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion (solution)
