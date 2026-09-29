-- Prove2me | solution 1 for NumberField.exists_lift_mem_inertia_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/219bb7b4-2c6c-57de-9834-f87a61c9d497

import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Invariant.Profinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_lift_mem_inertia_integralClosure

open scoped NumberField Pointwise

set_option autoImplicit false

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝔅" => integralClosure ℤ (AlgebraicClosure ℚ)

theorem solution
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsMaximal] {q : ℕ}
    (hqQ : (q : NumberField.RingOfIntegers L) ∈ Q) (τ : L ≃ₐ[ℚ] L)
    (hτ : τ ∈ Q.inertia (L ≃ₐ[ℚ] L)) :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), AlgEquiv.restrictNormalHom L σ = τ ∧
      ∃ 𝔔 : Ideal (integralClosure ℤ (AlgebraicClosure ℚ)), 𝔔.IsMaximal ∧
        (q : integralClosure ℤ (AlgebraicClosure ℚ)) ∈ 𝔔 ∧
        ∀ b : integralClosure ℤ (AlgebraicClosure ℚ), ∃ c ∈ 𝔔,
          (c : AlgebraicClosure ℚ) = σ b - b := by
  classical

  haveI hnormQ : Normal ℚ ℚ̄ := by
    have h : @Normal ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI halgQ : Algebra.IsAlgebraic ℚ ℚ̄ := by
    have h : @Algebra.IsAlgebraic ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI hsepQ : Algebra.IsSeparable ℚ ℚ̄ := by
    have h : @Algebra.IsSeparable ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  haveI : Algebra.IsAlgebraic L ℚ̄ := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  haveI : Algebra.IsIntegral L ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  haveI : Normal L ℚ̄ := Normal.tower_top_of_normal ℚ L ℚ̄
  haveI : Algebra.IsSeparable L ℚ̄ := Algebra.isSeparable_tower_top_of_isSeparable ℚ L ℚ̄
  haveI : IsGalois L ℚ̄ := ⟨⟩
  have hτ' : ∀ x : 𝓞 L, τ • x - x ∈ Q := fun x => (AddSubgroup.mem_inertia.mp hτ) x
  have hstabτ : τ • Q = Q := Ideal.inertia_le_stabilizer Q hτ

  letI actG : MulSemiringAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) 𝔅 := inferInstance
  letI actGI : DistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := Ideal.pointwiseDistribMulAction
  letI mulActGI : MulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribMulAction.toMulAction
  letI dsmulGI : DistribSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribMulAction.toDistribSMul
  letI smulzGI : SMulZeroClass (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := DistribSMul.toSMulZeroClass
  letI smulGI : SMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal 𝔅) := SMulZeroClass.toSMul

  let f : 𝓞 L →+* 𝔅 := (algebraMap (𝓞 L) ℚ̄).codRestrict (integralClosure ℤ ℚ̄) fun x =>
    (map_isIntegral_int (algebraMap (𝓞 L) ℚ̄) (Algebra.IsIntegral.isIntegral x))
  letI algOB : Algebra (𝓞 L) 𝔅 := f.toAlgebra
  have hf_coe : ∀ x : 𝓞 L, ((algebraMap (𝓞 L) 𝔅 x : 𝔅) : ℚ̄) = algebraMap L ℚ̄ (x : L) :=
    fun x => rfl
  haveI : IsScalarTower (𝓞 L) 𝔅 ℚ̄ := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hf_inj : Function.Injective (algebraMap (𝓞 L) 𝔅) := by
    intro x y hxy
    have h := congrArg (fun z : 𝔅 => (z : ℚ̄)) hxy
    simp only [hf_coe] at h
    exact NumberField.RingOfIntegers.coe_injective ((algebraMap L ℚ̄).injective h)

  have hres : ∀ (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : 𝓞 L),
      σ • algebraMap (𝓞 L) 𝔅 x = algebraMap (𝓞 L) 𝔅 ((AlgEquiv.restrictNormalHom L σ) • x) := by
    intro σ x
    apply Subtype.ext
    change σ (algebraMap L ℚ̄ (x : L)) = algebraMap L ℚ̄ ((σ.restrictNormal L) (x : L))
    exact (AlgEquiv.restrictNormal_commutes σ L (x : L)).symm

  let rsh : (ℚ̄ ≃ₐ[L] ℚ̄) →* (ℚ̄ ≃ₐ[ℚ] ℚ̄) :=
    { toFun := fun g => g.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hrsh_apply : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (x : ℚ̄), rsh g x = g x := fun _ _ => rfl

  have hresL : ∀ g : ℚ̄ ≃ₐ[L] ℚ̄, AlgEquiv.restrictNormalHom L (rsh g) = 1 := by
    intro g
    refine AlgEquiv.ext fun x => (algebraMap L ℚ̄).injective ?_
    change algebraMap L ℚ̄ (((rsh g).restrictNormal L) x) = algebraMap L ℚ̄ x
    rw [AlgEquiv.restrictNormal_commutes, hrsh_apply]
    exact g.commutes x
  letI actL : MulSemiringAction (ℚ̄ ≃ₐ[L] ℚ̄) 𝔅 := MulSemiringAction.compHom 𝔅 rsh
  letI actLI : DistribMulAction (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := Ideal.pointwiseDistribMulAction
  letI mulActLI : MulAction (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribMulAction.toMulAction
  letI dsmulLI : DistribSMul (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribMulAction.toDistribSMul
  letI smulzLI : SMulZeroClass (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := DistribSMul.toSMulZeroClass
  letI smulLI : SMul (ℚ̄ ≃ₐ[L] ℚ̄) (Ideal 𝔅) := SMulZeroClass.toSMul
  have hrs : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (b : 𝔅), g • b = rsh g • b := fun _ _ => rfl
  have hrsI : ∀ (g : ℚ̄ ≃ₐ[L] ℚ̄) (J : Ideal 𝔅), g • J = rsh g • J := by
    intro g J
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, hrs]

  haveI : SMulCommClass (ℚ̄ ≃ₐ[L] ℚ̄) (𝓞 L) 𝔅 := ⟨fun g a b => by
    apply Subtype.ext
    change g ((algebraMap L ℚ̄ (a : L)) * (b : ℚ̄)) = algebraMap L ℚ̄ (a : L) * g (b : ℚ̄)
    rw [map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace 𝔅 := ⊥
  haveI : DiscreteTopology 𝔅 := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[L] ℚ̄) 𝔅 := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional L (IntermediateField.adjoin L {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin L {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self L (b : ℚ̄))
  haveI : Algebra.IsInvariant (𝓞 L) 𝔅 (ℚ̄ ≃ₐ[L] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap L ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : 𝔅 => (z : ℚ̄)) (hb g)
    obtain ⟨y, hy⟩ := hb'

    have hyint : IsIntegral ℤ y := by
      obtain ⟨p, hp, hp0⟩ := (b.2 : IsIntegral ℤ (b : ℚ̄))
      refine ⟨p, hp, (algebraMap L ℚ̄).injective ?_⟩
      rw [Polynomial.hom_eval₂, map_zero, hy]
      convert hp0 using 2
      rfl
      rfl
    refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
    rw [hf_coe]
    exact hy⟩

  haveI : Algebra.IsIntegral (𝓞 L) 𝔅 :=
    Algebra.IsInvariant.isIntegral_of_profinite (G := ℚ̄ ≃ₐ[L] ℚ̄)

  obtain ⟨𝔔, h𝔔max, h𝔔Q⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝔅) Q (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := hf_inj (by rw [hx, map_zero])
    rw [hx0]
    exact Q.zero_mem)
  haveI h𝔔prime : 𝔔.IsPrime := h𝔔max.isPrime
  haveI h𝔔lies : 𝔔.LiesOver Q := ⟨by rw [Ideal.under_def, h𝔔Q]⟩
  have hmemQ : ∀ x : 𝓞 L, algebraMap (𝓞 L) 𝔅 x ∈ 𝔔 ↔ x ∈ Q := fun x => by
    rw [← Ideal.mem_comap, h𝔔Q]

  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := L) ℚ̄ τ
  have hunder : Ideal.under (𝓞 L) (σ₀ • 𝔔 : Ideal 𝔅) = Ideal.under (𝓞 L) 𝔔 := by
    ext x
    rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hres,
      hmemQ, hmemQ, map_inv, hσ₀]
    conv_rhs => rw [← hstabτ]
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := 𝓞 L) (G := ℚ̄ ≃ₐ[L] ℚ̄) (σ₀ • 𝔔 : Ideal 𝔅) 𝔔 hunder

  have hσ₁𝔔 : (rsh g * σ₀) • 𝔔 = 𝔔 := by rw [mul_smul, ← hrsI, ← hg]
  have hσ₁L : AlgEquiv.restrictNormalHom L (rsh g * σ₀) = τ := by
    rw [map_mul, hresL, one_mul, hσ₀]

  have hσ₁stab : rsh g * σ₀ ∈ MulAction.stabilizer (ℚ̄ ≃ₐ[ℚ] ℚ̄) 𝔔 := hσ₁𝔔
  let φ₀ : (𝔅 ⧸ 𝔔) ≃ₐ[ℤ ⧸ 𝔔.under ℤ] (𝔅 ⧸ 𝔔) :=
    Ideal.Quotient.stabilizerHom 𝔔 (𝔔.under ℤ) (ℚ̄ ≃ₐ[ℚ] ℚ̄) ⟨rsh g * σ₀, hσ₁stab⟩
  have hφ₀ : ∀ b : 𝔅, φ₀ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  have hστQ : ∀ x : 𝓞 L, Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • algebraMap (𝓞 L) 𝔅 x) =
      Ideal.Quotient.mk 𝔔 (algebraMap (𝓞 L) 𝔅 x) := by
    intro x
    rw [Ideal.Quotient.eq, hres, hσ₁L, ← map_sub, hmemQ]
    exact hτ' x
  let φ : (𝔅 ⧸ 𝔔) ≃ₐ[𝓞 L ⧸ Q] (𝔅 ⧸ 𝔔) :=
    AlgEquiv.ofRingEquiv (f := (φ₀ : (𝔅 ⧸ 𝔔) ≃+* (𝔅 ⧸ 𝔔))) (by
      intro a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
      exact hστQ x)
  have hφ : ∀ b : 𝔅, φ (Ideal.Quotient.mk 𝔔 b) = Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) :=
    fun b => rfl
  obtain ⟨t, ht⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := ℚ̄ ≃ₐ[L] ℚ̄) Q 𝔔 φ
  have ht' : ∀ b : 𝔅, Ideal.Quotient.mk 𝔔 ((t : ℚ̄ ≃ₐ[L] ℚ̄) • b) =
      Ideal.Quotient.mk 𝔔 ((rsh g * σ₀) • b) := by
    intro b
    have h := congrArg (fun e => e (Ideal.Quotient.mk 𝔔 b)) ht
    simp only [Ideal.Quotient.stabilizerHom_apply, hφ] at h
    exact h

  refine ⟨(rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀), ?_, 𝔔, h𝔔max, ?_, ?_⟩
  · rw [map_mul, map_inv, hresL, inv_one, one_mul, hσ₁L]
  · have h : algebraMap (𝓞 L) 𝔅 (q : 𝓞 L) ∈ 𝔔 := (hmemQ _).mpr hqQ
    simpa only [map_natCast] using h
  · intro b
    refine ⟨((rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀)) • b - b, ?_, rfl⟩
    have h1 : (rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b ∈ 𝔔 := by
      rw [← Ideal.Quotient.eq]
      exact (ht' b).symm
    have h2 : ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄) •
        ((rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b) ∈ 𝔔 := by
      have hmem := (Ideal.smul_mem_pointwise_smul_iff
        (a := ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄))).mpr h1
      rwa [MulAction.mem_stabilizer_iff.mp (t⁻¹).2] at hmem
    have h3 : ((t⁻¹ : MulAction.stabilizer (ℚ̄ ≃ₐ[L] ℚ̄) 𝔔) : ℚ̄ ≃ₐ[L] ℚ̄) •
        ((rsh g * σ₀) • b - (t : ℚ̄ ≃ₐ[L] ℚ̄) • b) =
        ((rsh (t : ℚ̄ ≃ₐ[L] ℚ̄))⁻¹ * (rsh g * σ₀)) • b - b := by
      rw [Subgroup.coe_inv, smul_sub, inv_smul_smul, hrs, map_inv]
      simp only [mul_smul]
    rw [← h3]
    exact h2

end S_NumberField_exists_lift_mem_inertia_integralClosure
end P2MW
export P2MW.S_NumberField_exists_lift_mem_inertia_integralClosure (solution)
