-- Prove2me | solution 1 for NumberField.SUnits.exists_sLevel_forall_sUnitsRep_map_val_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/84bb6052-a5c3-5be3-bfa6-2d37ea814692

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_M4aHerbrand_finrank_sUnit_eq
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Theorems.Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_IntermediateField_isUnramifiedOutside_normalClosure__721fcc
import Theorems.Thm_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"
set_option autoImplicit false
p2m_open "NumberField P2MW.S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow.NumberField IsDedekindDomain ExtCitation"

namespace NumberField
p2m_export "NumberField" "place SUnits.sUnitsRep SUnits.val SUnits.val_mem placesOverPrimes mem_placesOverPrimes_iff SUnits.sUnits_eq_unit SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one"
namespace SUnits
p2m_export "NumberField.SUnits" "placesAbove mem_placesAbove sUnits sUnitsRep val val_mem sUnits_eq_unit algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime"
namespace KummerSLevel
p2m_open "NumberField.SUnits NumberField"

lemma finite_placesAbove (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Finite (placesAbove ℚ ↥F Sℚ) := by
  have hfib : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      {w : HeightOneSpectrum (𝓞 ↥F) | w.under (𝓞 ℚ) = v}.Finite := by
    intro v
    haveI := v.isMaximal
    have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 ↥F) => w.asIdeal)
        ((fun w : HeightOneSpectrum (𝓞 ↥F) => w.asIdeal) ⁻¹' (v.asIdeal.primesOver (𝓞 ↥F))) :=
      fun _ _ _ _ h => HeightOneSpectrum.ext h
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 ↥F)).preimage hinj).subset fun w hw => ?_
    have hw' : w.under (𝓞 ℚ) = v := hw
    exact ⟨w.isPrime, ⟨by rw [← hw']; rfl⟩⟩
  have hsub : placesAbove ℚ ↥F Sℚ ⊆ ⋃ v ∈ (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))),
      {w : HeightOneSpectrum (𝓞 ↥F) | w.under (𝓞 ℚ) = v} := fun w hw =>
    Set.mem_biUnion ((mem_placesAbove ℚ ↥F Sℚ w).1 hw) rfl
  exact ((Sℚ.finite_toSet.biUnion fun v _ => hfib v).subset hsub).to_subtype

lemma exists_prime_natCast_mem (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
  haveI := w.isMaximal
  haveI : Finite (𝓞 ↥F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 ↥F ⧸ w.asIdeal)
  refine ⟨q, CharP.char_is_prime (𝓞 ↥F ⧸ w.asIdeal) q, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ q

lemma exists_prime_not_mem (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F)) (hw : w ∉ placesAbove ℚ ↥F Sℚ) :
    ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
  obtain ⟨q, hq, hqw⟩ := exists_prime_natCast_mem F w
  refine ⟨⟨q, hq⟩, fun hqS => hw ?_, hqw⟩
  rw [mem_placesAbove, ← Finset.mem_coe, hSℚ, NumberField.mem_placesOverPrimes_iff]
  refine ⟨⟨q, hq⟩, hqS, ?_⟩
  change algebraMap (𝓞 ℚ) (𝓞 ↥F) ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  rwa [map_natCast]

lemma mem_sUnits_of_forall_mem_and_inv_mem (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] (x : (↥F)ˣ)
    (hx : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((x : ↥F) : AlgebraicClosure ℚ) ∈ A ∧ ((x : ↥F) : AlgebraicClosure ℚ)⁻¹ ∈ A) :
    x ∈ sUnits ℚ ↥F Sℚ := by
  rw [NumberField.SUnits.sUnits_eq_unit]
  simp only [Set.unit]
  intro w hw
  obtain ⟨q, hqS, hqw⟩ := exists_prime_not_mem S Sℚ hSℚ F w hw
  obtain ⟨B, hB⟩ := NumberField.exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one F w
  have hq0 : ((q : ℕ) : ↥F) ≠ 0 := by exact_mod_cast q.2.ne_zero

  have hvq : w.valuation ↥F ((q : ℕ) : ↥F) < 1 := by
    have h := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥F) w ((q : ℕ) : 𝓞 ↥F)).2 hqw
    simpa using h

  have hBq : B.LiesOverPrime (q : ℕ) := by
    change ((q : ℕ) : AlgebraicClosure ℚ) ∈ B.nonunits
    rw [ValuationSubring.mem_nonunits_iff]
    have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ B := by
      exact (hB ((q : ℕ) : ↥F)).2 hvq.le
    refine lt_of_le_of_ne ((B.valuation_le_one_iff _).2 hmem) fun h1 => ?_
    have hinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ B := by
      apply B.mem_of_valuation_le_one
      rw [map_inv₀, h1, inv_one]
    have hinv' : w.valuation ↥F ((q : ℕ) : ↥F)⁻¹ ≤ 1 := by
      refine (hB _).1 ?_
      simpa using hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hq0))] at hinv'
    exact not_lt.2 hinv' hvq

  obtain ⟨h1, h2⟩ := hx q hqS B hBq
  have hle : w.valuation ↥F (x : ↥F) ≤ 1 := (hB _).1 h1
  have hle' : w.valuation ↥F (x : ↥F)⁻¹ ≤ 1 := (hB _).1 (by simpa using h2)
  have hx0 : w.valuation ↥F (x : ↥F) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero x)
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 hx0)] at hle'
  exact le_antisymm hle hle'

lemma zpow_mem_of_mem_of_inv_mem {K : Type*} [Field K] {σ : Type*} [SetLike σ K] [SubringClass σ K]
    {s : σ} {x : K} (h1 : x ∈ s) (h2 : x⁻¹ ∈ s) (n : ℤ) : x ^ n ∈ s := by
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    rw [zpow_natCast]
    exact pow_mem h1 n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem h2 m

lemma mem_and_inv_mem_of_pow_eq {K : Type*} [Field K] (A : ValuationSubring K) {p : ℕ} (hp : 0 < p)
    {α g : K} (hα : α ^ p = g) (hg : g ∈ A) (hg' : g⁻¹ ∈ A) : α ∈ A ∧ α⁻¹ ∈ A := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.sub_add_cancel hp).symm⟩
  by_cases h0 : α = 0
  · subst h0
    rw [inv_zero]
    exact ⟨A.zero_mem, A.zero_mem⟩
  rcases A.mem_or_inv_mem α with h | h
  · refine ⟨h, ?_⟩
    have : α⁻¹ = g⁻¹ * α ^ k := by
      rw [← hα, hk, pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k h0), mul_one]
    rw [this]
    exact A.mul_mem _ _ hg' (A.pow_mem h k)
  · refine ⟨?_, h⟩
    have : α = g * α⁻¹ ^ k := by
      rw [← hα, hk, pow_succ, inv_pow, mul_assoc, mul_comm α, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k h0),
        one_mul]
    rw [this]
    exact A.mul_mem _ _ hg (A.pow_mem h k)

lemma isUnramifiedOutside_sup_finsetSup (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S)
    {ι : Type} [DecidableEq ι] (T : Finset ι) (g α : ι → AlgebraicClosure ℚ) (hg : ∀ i ∈ T, g i ∈ F)
    (hgS : ∀ i ∈ T, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → g i ∈ A ∧ (g i)⁻¹ ∈ A)
    (hα : ∀ i ∈ T, α i ^ (p : ℕ) = g i) :
    (F ⊔ T.sup fun i => IntermediateField.adjoin ℚ {α i}).IsUnramifiedOutside S := by
  induction T using Finset.induction_on with
  | empty => rwa [Finset.sup_empty, sup_bot_eq]
  | insert a s ha ih =>
    have ih' := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hgS i (Finset.mem_insert_of_mem hi)) (fun i hi => hα i (Finset.mem_insert_of_mem hi))
    rw [Finset.sup_insert, sup_comm (IntermediateField.adjoin ℚ {α a}), ← sup_assoc]
    exact IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S p hp _ ih' (g a)
      ((le_sup_left : F ≤ F ⊔ s.sup fun i => IntermediateField.adjoin ℚ {α i}) (hg a (Finset.mem_insert_self a s)))
      (hgS a (Finset.mem_insert_self a s)) (α a) (hα a (Finset.mem_insert_self a s))

lemma exists_sUnit_pow_eq_prod (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    {p : ℕ} (hp : 0 < p) (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃]
    {ι : Type} (T : Finset ι) (g α : ι → AlgebraicClosure ℚ) (f : ι → ℤ)
    (hgS : ∀ i ∈ T, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → g i ∈ A ∧ (g i)⁻¹ ∈ A)
    (hα : ∀ i ∈ T, α i ^ p = g i) (hg0 : ∀ i ∈ T, g i ≠ 0) (hαF : ∀ i ∈ T, α i ∈ F₃) :
    ∃ v : (↥F₃)ˣ, v ∈ sUnits ℚ ↥F₃ Sℚ ∧ ((v : ↥F₃) : AlgebraicClosure ℚ) ^ p = ∏ i ∈ T, g i ^ f i := by
  classical
  have hα0 : ∀ i ∈ T, α i ≠ 0 := fun i hi h => hg0 i hi (by rw [← hα i hi, h, zero_pow hp.ne'])
  have hαinv : ∀ i ∈ T, (α i)⁻¹ ∈ F₃ := fun i hi => inv_mem (hαF i hi)
  set y : AlgebraicClosure ℚ := ∏ i ∈ T, α i ^ f i with hy
  have hyF : y ∈ F₃ := prod_mem fun i hi => zpow_mem_of_mem_of_inv_mem (hαF i hi) (hαinv i hi) _
  have hy0 : y ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hα0 i hi)
  have hy0' : (⟨y, hyF⟩ : ↥F₃) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  refine ⟨Units.mk0 ⟨y, hyF⟩ hy0', ?_, ?_⟩
  · apply mem_sUnits_of_forall_mem_and_inv_mem S Sℚ hSℚ F₃
    intro q hq A hA
    have hu : ∀ i ∈ T, α i ∈ A ∧ (α i)⁻¹ ∈ A := fun i hi =>
      mem_and_inv_mem_of_pow_eq A hp (hα i hi) (hgS i hi q hq A hA).1 (hgS i hi q hq A hA).2
    change y ∈ A ∧ y⁻¹ ∈ A
    refine ⟨prod_mem fun i hi => zpow_mem_of_mem_of_inv_mem (hu i hi).1 (hu i hi).2 _, ?_⟩
    rw [hy, ← Finset.prod_inv_distrib]
    exact prod_mem fun i hi => by
      rw [← zpow_neg]
      exact zpow_mem_of_mem_of_inv_mem (hu i hi).1 (hu i hi).2 _
  · change y ^ p = _
    rw [hy, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [← hα i hi, ← zpow_natCast (α i ^ f i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem main {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ F₁' : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₁' ∧ FiniteDimensional ℚ ↥F₁' ∧ IsGalois ℚ ↥F₁' ∧
      F₁'.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃], F₁' ≤ F₃ →
        ∀ u : (↥F₁)ˣ, u ∈ sUnits ℚ ↥F₁ Sℚ →
          ∃ v : (↥F₃)ˣ, v ∈ sUnits ℚ ↥F₃ Sℚ ∧
            ((u : ↥F₁) : AlgebraicClosure ℚ) = ((v : ↥F₃) : AlgebraicClosure ℚ) ^ p := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  haveI := finite_placesAbove F₁ Sℚ
  obtain ⟨hfg, -⟩ := M4aHerbrand.finrank_sUnit_eq ↥F₁ (placesAbove ℚ ↥F₁ Sℚ)
  obtain ⟨T, hT⟩ := Module.finite_def.1 hfg

  let ψ : ↥((placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁) →* (AlgebraicClosure ℚ)ˣ :=
    (Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ)).comp (Subgroup.subtype _)
  let g : Additive ↥((placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁) → AlgebraicClosure ℚ := fun t => (ψ (Additive.toMul t) : AlgebraicClosure ℚ)
  have hg0 : ∀ t, g t ≠ 0 := fun t => Units.ne_zero _
  have hgF : ∀ t, g t ∈ F₁ := fun t => SetLike.coe_mem _
  have hroot : ∀ t, ∃ a : AlgebraicClosure ℚ, a ^ p = g t := fun t => IsAlgClosed.exists_pow_nat_eq _ hp
  choose α hα using hroot
  have hgunit : ∀ t : Additive ↥((placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁),
      ((Additive.toMul t : ↥((placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁)) : (↥F₁)ˣ) ∈ sUnits ℚ ↥F₁ Sℚ := fun t => by
    rw [NumberField.SUnits.sUnits_eq_unit]
    exact (Additive.toMul t).2
  have hgS : ∀ t, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      g t ∈ A ∧ (g t)⁻¹ ∈ A := fun t q hq A hA =>
    NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime S Sℚ hSℚ F₁ _ (hgunit t) q hq A hA

  have hF' : (F₁ ⊔ T.sup fun t => IntermediateField.adjoin ℚ {α t}).IsUnramifiedOutside S :=
    isUnramifiedOutside_sup_finsetSup S (pPrime p) hpS F₁ hF₁ T g α (fun t _ => hgF t) (fun t _ => hgS t)
      (fun t _ => hα t)
  obtain ⟨hle, hfd, hgal, hur⟩ :=
    IntermediateField.isUnramifiedOutside_normalClosure S (F₁ ⊔ T.sup fun t => IntermediateField.adjoin ℚ {α t}) hF'
  refine ⟨_, le_sup_left.trans hle, hfd, hgal, hur, ?_⟩
  intro F₃ _ h3 u hu

  have hαF₃ : ∀ t ∈ T, α t ∈ F₃ := fun t ht =>
    h3 (hle (le_sup_right (b := T.sup fun t => IntermediateField.adjoin ℚ {α t})
      (Finset.le_sup (f := fun t => IntermediateField.adjoin ℚ {α t}) ht
        (IntermediateField.mem_adjoin_simple_self ℚ (α t)))))

  have hu' : u ∈ (placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁ := by rwa [NumberField.SUnits.sUnits_eq_unit] at hu
  have hmem : Additive.ofMul (⟨u, hu'⟩ : ↥((placesAbove ℚ ↥F₁ Sℚ).unit ↥F₁)) ∈ Submodule.span ℤ (↑T : Set _) := by
    rw [hT]; trivial
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hmem
  have huprod : ((u : ↥F₁) : AlgebraicClosure ℚ) = ∏ t ∈ T, g t ^ f t := by
    have h1 := congrArg (fun m => ((ψ (Additive.toMul m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) hf
    simp only [toMul_sum, toMul_zsmul, map_prod, map_zpow, Units.coe_prod, toMul_ofMul] at h1
    have h2 : ((u : ↥F₁) : AlgebraicClosure ℚ) = ((ψ ⟨u, hu'⟩ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := rfl
    rw [h2, ← h1]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Units.val_zpow_eq_zpow_val]
    try rfl
  obtain ⟨v, hv, hvp⟩ := exists_sUnit_pow_eq_prod S Sℚ hSℚ hp F₃ T g α f (fun t _ => hgS t) (fun t _ => hα t)
    (fun t _ => hg0 t) hαF₃
  exact ⟨v, hv, huprod.trans hvp.symm⟩

end NumberField.SUnits.KummerSLevel

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S) :
    ∃ F₁' : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₁' ∧ FiniteDimensional ℚ ↥F₁' ∧ IsGalois ℚ ↥F₁' ∧ F₁'.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] (_ : F₁' ≤ F₃)
        (e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ),
        ∃ e' : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ,
          Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ e) =
            (Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ e')) ^ p := by
  obtain ⟨F₁', h1, h2, h3, h4, h5⟩ := NumberField.SUnits.KummerSLevel.main S hpS Sℚ hSℚ F₁ hF₁
  refine ⟨F₁', h1, h2, h3, h4, fun F₃ _ hF₃ e => ?_⟩
  obtain ⟨v, hv, hvp⟩ := h5 F₃ hF₃ (NumberField.SUnits.val ℚ ↥F₁ Sℚ e) (NumberField.SUnits.val_mem ℚ ↥F₁ Sℚ e)
  refine ⟨⟨Additive.ofMul v, hv⟩, Units.ext ?_⟩
  simp at hvp ⊢
  exact hvp

end S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow
end P2MW
export P2MW.S_NumberField_SUnits_exists_sLevel_forall_sUnitsRep_map_val_eq_pow (solution)
