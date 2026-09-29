-- Prove2me | solution 1 for ModularCurve.exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8df232f1-c3a4-5fd0-a489-4fec2387278c

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.FieldTheory.Galois.Basic
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false

attribute [local instance] Ideal.Quotient.field

open scoped Pointwise
open IntermediateField

theorem frobAuxRestrictNormalDecompStep
    (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ M] [IsGalois ℚ M]
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL₀M : L₀ ≤ M) :
    ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ A.inertiaSubgroupIn ℚ ∧
        (φ ^ n * τ)⁻¹ * σ ∈ L₀.fixingSubgroup := by
  classical
  haveI hNormalM : Normal ℚ (↥M) := IsGalois.to_normal
  obtain ⟨Q, hQmax, hQfin, hqQ, hle, hmem, hinert, -, -⟩ :=
    ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom M A hq hA
  haveI : Q.IsMaximal := hQmax
  haveI : Finite (NumberField.RingOfIntegers ↥M ⧸ Q) := hQfin
  haveI hQlies : Q.LiesOver (Ideal.under ℤ Q) := ⟨rfl⟩

  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hq.ne_zero
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hspanprime : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq0).mpr hqZ
  have hspanmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    IsPrime.to_maximal_ideal (by simpa [Ideal.span_singleton_eq_bot] using hq0)
  have hspanle : Ideal.span {(q : ℤ)} ≤ Ideal.under ℤ Q := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hqQ
  have hunder : Ideal.under ℤ Q = Ideal.span {(q : ℤ)} :=
    (hspanmax.eq_of_le (Ideal.comap_ne_top _ hQmax.ne_top) hspanle).symm
  haveI hpmax : (Ideal.under ℤ Q).IsMaximal := hunder ▸ hspanmax

  haveI : NeZero q := ⟨hq.ne_zero⟩
  have eqv : (ℤ ⧸ Ideal.under ℤ Q) ≃+* ZMod q :=
    (Ideal.quotEquivOfEq hunder).trans (Int.quotientSpanNatEquivZMod q)
  haveI : Finite (ℤ ⧸ Ideal.under ℤ Q) := Finite.of_equiv _ eqv.toEquiv.symm
  haveI : Fintype (ℤ ⧸ Ideal.under ℤ Q) := Fintype.ofFinite _
  have hcard : Fintype.card (ℤ ⧸ Ideal.under ℤ Q) = q := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eqv.toEquiv, Nat.card_zmod]

  have hmemA : ∀ x : NumberField.RingOfIntegers ↥M,
      algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M) ∈ A := fun x =>
    (A.valuation_le_one_iff _).mp (hle x)

  have hstab : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      g ∈ A.decompositionSubgroup ℚ →
      AlgEquiv.restrictNormalHom M g ∈ MulAction.stabilizer (↥M ≃ₐ[ℚ] ↥M) Q := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem]
    have hcoe : algebraMap (↥M) (AlgebraicClosure ℚ)
        ((((AlgEquiv.restrictNormalHom M g)⁻¹ • x : NumberField.RingOfIntegers ↥M)) : ↥M)
        = g⁻¹ (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M)) := by
      have h1 : (((AlgEquiv.restrictNormalHom M g)⁻¹ • x :
            NumberField.RingOfIntegers ↥M) : ↥M)
          = (AlgEquiv.restrictNormalHom M (g⁻¹)) ((x : ↥M)) := by
        rw [← map_inv]; rfl
      rw [h1]
      exact AlgEquiv.restrictNormal_commutes (g⁻¹) (↥M) (x : ↥M)
    rw [hcoe,
      ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A (inv_mem hg)]

  have hφcong : ∀ x : NumberField.RingOfIntegers ↥M,
      AlgEquiv.restrictNormalHom M φ • x - x ^ q ∈ Q := by
    intro x
    rw [hmem]
    have ha : algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M) ∈ A := hmemA x
    have key : A.valuation (φ (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M))
        - (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M)) ^ q) < 1 := by
      have hres0 : IsLocalRing.residue A
          ((⟨φ, hφ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) •
              (⟨algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M), ha⟩ : A)
            - (⟨algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M), ha⟩ : A) ^ q) = 0 := by
        rw [map_sub, map_pow, IsLocalRing.ResidueField.residue_smul,
          hφ.smul_residue_eq, sub_self]
      have hmax := (IsLocalRing.residue_eq_zero_iff _).mp hres0
      have hval := (A.valuation_lt_one_iff _).mp hmax
      have hco : ((((⟨φ, hφ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) •
              (⟨algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M), ha⟩ : A)
            - (⟨algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M), ha⟩ : A) ^ q : A)) :
            AlgebraicClosure ℚ)
          = φ (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M))
            - (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M)) ^ q := rfl
      rwa [hco] at hval
    have hcoe : algebraMap (↥M) (AlgebraicClosure ℚ)
        (((AlgEquiv.restrictNormalHom M φ • x - x ^ q : NumberField.RingOfIntegers ↥M)) : ↥M)
        = φ (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M))
          - (algebraMap (↥M) (AlgebraicClosure ℚ) (x : ↥M)) ^ q := by
      have h1 : ((AlgEquiv.restrictNormalHom M φ • x - x ^ q :
            NumberField.RingOfIntegers ↥M) : ↥M)
          = (AlgEquiv.restrictNormalHom M φ) ((x : ↥M)) - ((x : ↥M)) ^ q := rfl
      rw [h1, map_sub, map_pow]
      congr 1
      exact AlgEquiv.restrictNormal_commutes φ (↥M) (x : ↥M)
    rw [hcoe]
    exact key

  haveI : Algebra.IsAlgebraic (ℤ ⧸ Ideal.under ℤ Q) (NumberField.RingOfIntegers ↥M ⧸ Q) :=
    Algebra.IsAlgebraic.of_finite _ _

  have hφres : Ideal.Quotient.stabilizerHom Q (Ideal.under ℤ Q) (↥M ≃ₐ[ℚ] ↥M)
        ⟨AlgEquiv.restrictNormalHom M φ, hstab φ hφ.mem_decompositionSubgroup⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ Ideal.under ℤ Q)
        (NumberField.RingOfIntegers ↥M ⧸ Q) := by
    apply AlgEquiv.ext
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : (Ideal.Quotient.stabilizerHom Q (Ideal.under ℤ Q) (↥M ≃ₐ[ℚ] ↥M)
          ⟨AlgEquiv.restrictNormalHom M φ, hstab φ hφ.mem_decompositionSubgroup⟩)
          (Ideal.Quotient.mk Q x)
        = Ideal.Quotient.mk Q (AlgEquiv.restrictNormalHom M φ • x) := rfl
    have h2 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ Ideal.under ℤ Q)
          (NumberField.RingOfIntegers ↥M ⧸ Q)) (Ideal.Quotient.mk Q x)
        = (Ideal.Quotient.mk Q x) ^ Fintype.card (ℤ ⧸ Ideal.under ℤ Q) := rfl
    rw [h1, h2, hcard, ← map_pow, Ideal.Quotient.eq]
    exact hφcong x

  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ℤ ⧸ Ideal.under ℤ Q) (NumberField.RingOfIntegers ↥M ⧸ Q)).2
      (Ideal.Quotient.stabilizerHom Q (Ideal.under ℤ Q) (↥M ≃ₐ[ℚ] ↥M)
        ⟨AlgEquiv.restrictNormalHom M σ, hstab σ hσ⟩)

  have hker : (⟨AlgEquiv.restrictNormalHom M φ,
        hstab φ hφ.mem_decompositionSubgroup⟩ ^ (n : ℕ))⁻¹ *
        ⟨AlgEquiv.restrictNormalHom M σ, hstab σ hσ⟩ ∈
      (Ideal.Quotient.stabilizerHom Q (Ideal.under ℤ Q) (↥M ≃ₐ[ℚ] ↥M)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hφres]
    exact inv_mul_eq_one.mpr hn
  have hQin : (AlgEquiv.restrictNormalHom M φ ^ (n : ℕ))⁻¹ * AlgEquiv.restrictNormalHom M σ ∈
      Q.inertia (↥M ≃ₐ[ℚ] ↥M) := by
    rw [← Ideal.Quotient.map_ker_stabilizer_subtype Q (Ideal.under ℤ Q) (↥M ≃ₐ[ℚ] ↥M)]
    exact Subgroup.mem_map.mpr ⟨_, hker, rfl⟩

  rw [← hinert] at hQin
  obtain ⟨τ, hτI, hτeq⟩ := Subgroup.mem_map.mp hQin
  refine ⟨(n : ℕ), τ, hτI, ?_⟩
  have hEQ : AlgEquiv.restrictNormalHom M ((φ ^ (n : ℕ) * τ)⁻¹ * σ) = 1 := by
    have hmap : AlgEquiv.restrictNormalHom M ((φ ^ (n : ℕ) * τ)⁻¹ * σ) =
        (AlgEquiv.restrictNormalHom M φ ^ (n : ℕ) * AlgEquiv.restrictNormalHom M τ)⁻¹ *
          AlgEquiv.restrictNormalHom M σ := by
      rw [map_mul, map_inv, map_mul, map_pow]
    rw [hmap, hτeq]
    group
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 := AlgEquiv.restrictNormal_commutes ((φ ^ (n : ℕ) * τ)⁻¹ * σ) (↥M)
    (⟨x, hL₀M hx⟩ : ↥M)
  have hEQ' : ((φ ^ (n : ℕ) * τ)⁻¹ * σ).restrictNormal (↥M) = 1 := hEQ
  rw [hEQ'] at h1
  simpa using h1.symm

theorem solution (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (L₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L₀] :
    ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ A.inertiaSubgroupIn ℚ ∧ (φ ^ n * τ)⁻¹ * σ ∈ L₀.fixingSubgroup := by
  haveI hQbarNormal : Normal ℚ (AlgebraicClosure ℚ) := IsGalois.to_normal
  haveI hNcNormal : Normal ℚ ↥(normalClosure ℚ (↥L₀) (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ (↥L₀) (AlgebraicClosure ℚ)
  haveI hNcSep : Algebra.IsSeparable ℚ ↥(normalClosure ℚ (↥L₀) (AlgebraicClosure ℚ)) :=
    inferInstance
  haveI : IsGalois ℚ ↥(normalClosure ℚ (↥L₀) (AlgebraicClosure ℚ)) := ⟨⟩
  exact frobAuxRestrictNormalDecompStep q hq A hA φ hφ σ hσ
    (normalClosure ℚ (↥L₀) (AlgebraicClosure ℚ)) L₀ L₀.le_normalClosure

end S_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
end P2MW
export P2MW.S_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup (solution)
