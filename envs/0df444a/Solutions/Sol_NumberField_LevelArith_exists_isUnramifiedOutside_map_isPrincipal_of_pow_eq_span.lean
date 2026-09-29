-- Prove2me | solution 1 for NumberField.LevelArith.exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a700a1d2-2fe6-5f96-af22-10686825eaf0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_NumberField_LevelArith_inertia_apply_eq_of_dvd_valuation
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open CategoryTheory Module groupCohomology ExtCitation NumberField NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith
open scoped Pointwise

local instance A5loc.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance A5loc.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance A5loc.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
local instance A5loc.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace CapInj

section L1
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

lemma exists_eq_spanSingleton_mul_of_mk_eq (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ)
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    ∃ x : K, x ≠ 0 ∧ (I : FractionalIdeal (nonZeroDivisors R) K) = FractionalIdeal.spanSingleton (nonZeroDivisors R) x * J := by
  have h1 : ClassGroup.mk K (I * J⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  refine ⟨x, fun hx0 => ?_, ?_⟩
  · rw [hx0, FractionalIdeal.spanSingleton_zero] at hx
    exact (I * J⁻¹).ne_zero hx
  · have : ((I * J⁻¹ : (FractionalIdeal (nonZeroDivisors R) K)ˣ) : FractionalIdeal (nonZeroDivisors R) K) * J = I := by
      rw [Units.val_mul, Units.inv_mul_cancel_right]
    rw [← this, hx]

lemma valuation_eq_exp_neg_count (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x))) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  have hsK : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r / algebraMap R K s) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx
  have heq : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r / algebraMap R K s) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal (nonZeroDivisors R) K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v hI heq, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hr0, v.intValuation_if_neg hs0, ← WithZero.exp_sub]
  congr 1
  push_cast
  ring

end L1

section L3
variable (F : Type) [Field F] [NumberField F] (S : Set Nat.Primes)

lemma exists_sSupported_of_mem_closure (c : ClassGroup (𝓞 F))
    (hc : c ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S)) :
    ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ, ClassGroup.mk F I = c ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ placesOverPrimes F S → FractionalIdeal.count F w (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w₀, hw₀, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 F ⟨w₀.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using w₀.ne_bot)⟩, ?_, fun w hw => ?_⟩
    · rw [ClassGroup.mk_mk0]; rfl
    · have hne : w₀ ≠ w := fun h => hw (h ▸ hw₀)
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.count_maximal_coprime F w hne
  | one => exact ⟨1, map_one _, fun w _ => by rw [Units.val_one, FractionalIdeal.count_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun w hw => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul F w I.ne_zero J.ne_zero, hI w hw, hJ w hw, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun w hw => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI w hw, neg_zero]

end L3

end CapInj

namespace CycBaseCAP
section helpersX
open IsDedekindDomain NumberField

lemma natCast_mem_unique' {K : Type} [Field K] [NumberField K] {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (h : ((q : 𝓞 K)) ∈ w.asIdeal) (h' : ((q' : 𝓞 K)) ∈ w.asIdeal) : q = q' := by
  by_contra hne
  have hcop : IsCoprime ((q : 𝓞 K)) ((q' : 𝓞 K)) := by
    have := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne)).map (Int.castRingHom (𝓞 K))
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

lemma inv_natCast_not_mem' {q : ℕ} (hq : q.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) :
    ((q : AlgebraicClosure ℚ))⁻¹ ∉ A := by
  intro h
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have h1 : A.valuation ((q : AlgebraicClosure ℚ))⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 h
  have h2 : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hq0))] at h1
  exact absurd h2 (not_lt.2 h1)

end helpersX
end CycBaseCAP

namespace CycBaseCAP
section torsProof

open IsDedekindDomain NumberField

lemma toAdd_valuationOfNeZero_eq_neg_count (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : HeightOneSpectrum (𝓞 ↥K)) (x : ↥K) (hx : x ≠ 0) :
    Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 x hx)) =
      -FractionalIdeal.count ↥K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) x) := by
  have h := HeightOneSpectrum.valuationOfNeZero_eq w (Units.mk0 x hx)
  rw [Units.val_mk0, CapInj.valuation_eq_exp_neg_count ↥K w x hx, WithZero.exp] at h
  have h' := WithZero.coe_injective h
  rw [h', toAdd_ofAdd]

lemma exists_kummer_level {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (x : ↥L) (hx : x ≠ 0)
    (hdiv : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 x hx)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = (x : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ F ∧ y ∈ F ∧ F.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F ∧ FiniteDimensional ℚ ↥F := by

  have hyint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {y}) := IntermediateField.adjoin.finiteDimensional hyint
  let E₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {y}
  haveI hE₀fd : FiniteDimensional ℚ ↥E₀ := IntermediateField.finiteDimensional_sup L _

  have hE₀ : E₀.IsUnramifiedOutside S := by
    refine ⟨hE₀fd, fun q hq A hA σ hσ => ?_⟩
    have hσL : σ ∈ L.fixingSubgroup := hL.2 q hq A hA hσ
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨hσL, ?_⟩

    have hAF : ∃ z : ↥L, algebraMap ↥L (AlgebraicClosure ℚ) z ∉ A :=
      ⟨(((q : Nat.Primes) : ℕ) : ↥L)⁻¹, by rw [map_inv₀, map_natCast]; exact inv_natCast_not_mem' (q : Nat.Primes).2 hA⟩
    obtain ⟨w, hw⟩ := (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥L
      (algebraMap ↥L (AlgebraicClosure ℚ)) A hAF).exists
    have hvq : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) < 1 := by
      by_contra hge
      rw [not_lt] at hge
      have hle : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) ≤ 1 := (hw _).1 (by rw [map_natCast]; exact natCast_mem A _)
      have heq : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) = 1 := le_antisymm hle hge
      have hmem : algebraMap ↥L (AlgebraicClosure ℚ) ((((q : Nat.Primes) : ℕ) : ↥L))⁻¹ ∈ A := (hw _).2 (by rw [map_inv₀, heq, inv_one])
      rw [map_inv₀, map_natCast] at hmem
      exact inv_natCast_not_mem' (q : Nat.Primes).2 hA hmem
    have hqw : (((q : Nat.Primes) : ℕ) : 𝓞 ↥L) ∈ w.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := ↥L)]
      rw [show (((q : Nat.Primes) : ℕ) : ↥L) = algebraMap (𝓞 ↥L) ↥L (((q : Nat.Primes) : ℕ) : 𝓞 ↥L) from (map_natCast _ _).symm] at hvq
      exact hvq
    have hwS : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) := by
      rintro ⟨q', hq'S, hq'w⟩
      exact hq ((show q = q' from Subtype.ext (natCast_mem_unique' (q : Nat.Primes).2 (q' : Nat.Primes).2 w hqw hq'w)) ▸ hq'S)
    have hqp : ((q : Nat.Primes) : ℕ) ≠ p := fun h => hq (by
      have : q = pPrime p := Subtype.ext h
      rw [this]; exact hpS)
    have hσy : σ y = y :=
      NumberField.LevelArith.inertia_apply_eq_of_dvd_valuation p L (Units.mk0 x hx) w ((q : Nat.Primes) : ℕ) (q : Nat.Primes).2 hqp hqw
        (hdiv w hwS) y (by rw [Units.val_mk0]; exact hy) A (fun z => hw z) σ hσ
        (fun z => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _ z.2)
    show σ ∈ (IntermediateField.adjoin ℚ {y}).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem t ht => rw [Set.mem_singleton_iff] at ht; subst ht; exact hσy
    | algebraMap r => exact AlgEquiv.commutes σ r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

  have hyE₀ : y ∈ E₀ := (le_sup_right : IntermediateField.adjoin ℚ {y} ≤ E₀) (IntermediateField.subset_adjoin ℚ {y} (Set.mem_singleton y))
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥E₀) (AlgebraicClosure ℚ)) := normalClosure.normal ℚ (↥E₀) (AlgebraicClosure ℚ)
  exact ⟨IntermediateField.normalClosure ℚ (↥E₀) (AlgebraicClosure ℚ), le_sup_left.trans (IntermediateField.le_normalClosure E₀),
    IntermediateField.le_normalClosure E₀ hyE₀, IntermediateField.IsUnramifiedOutside.normalClosure hE₀, ⟨⟩, inferInstance⟩

end torsProof
end CycBaseCAP

namespace CycBaseCAP
section A5
open IsDedekindDomain NumberField

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)

noncomputable abbrev φ {F E : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ E) : 𝓞 ↥F →+* 𝓞 ↥E :=
  RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom

lemma φ_comp {F E E' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ E) (h' : E ≤ E') :
    (φ h').comp (φ h) = φ (h.trans h') := by
  ext x
  rfl

lemma coe_φ {F E : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ E) (x : 𝓞 ↥F) :
    (((φ h x : 𝓞 ↥E) : ↥E) : AlgebraicClosure ℚ) = ((x : ↥F) : AlgebraicClosure ℚ) := rfl

lemma span_eq_pow_of_pow_eq {F E : IntermediateField ℚ (AlgebraicClosure ℚ)} [FiniteDimensional ℚ ↥F] [FiniteDimensional ℚ ↥E] (h : F ≤ E)
    (I : Ideal (𝓞 ↥F)) (k j : ℕ) (hjk : j ≤ k) (a : 𝓞 ↥F) (hI : I ^ p ^ k = Ideal.span {a})
    (y : 𝓞 ↥E) (hy : y ^ p ^ j = φ h a) :
    Ideal.span {y} = (I.map (φ h)) ^ p ^ (k - j) := by
  have hp : p.Prime := Fact.out
  have hne : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
  apply pow_left_injective hne
  dsimp only
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hjk, ← Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, hy]

end A5
end CycBaseCAP

namespace CycBaseCAP
section A5b
open IsDedekindDomain NumberField

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)

lemma dvd_ord_of_span_eq_pow (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥E]
    (y : 𝓞 ↥E) (hy0 : (y : ↥E) ≠ 0) (J : Ideal (𝓞 ↥E)) (n : ℕ) (hn : p ∣ n) (hJ : Ideal.span {y} = J ^ n)
    (w : HeightOneSpectrum (𝓞 ↥E)) :
    (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 (y : ↥E) hy0)) := by
  rw [toAdd_valuationOfNeZero_eq_neg_count E w (y : ↥E) hy0]
  have : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥E)) (y : ↥E) = ((J ^ n : Ideal (𝓞 ↥E)) : FractionalIdeal (nonZeroDivisors (𝓞 ↥E)) ↥E) := by
    rw [← hJ, FractionalIdeal.coeIdeal_span_singleton]
  rw [this, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]
  obtain ⟨m, rfl⟩ := hn
  rw [dvd_neg]
  push_cast
  rw [mul_assoc]
  exact dvd_mul_right _ _

end A5b
end CycBaseCAP

namespace CycBaseCAP
section A5c
open IsDedekindDomain NumberField

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)

include hpS in

theorem exists_level_root (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F) (ha : a ≠ 0) (hI : I ^ p ^ k = Ideal.span {a}) :
    ∀ j : ℕ, j ≤ k → ∃ (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hFE : F ≤ E), E.IsUnramifiedOutside S ∧
      ∃ (_ : FiniteDimensional ℚ ↥E) (y : 𝓞 ↥E), y ^ p ^ j = φ hFE a
  | 0, _ => ⟨F, le_rfl, hF, inferInstance, φ le_rfl a, by rw [pow_zero, pow_one]⟩
  | j + 1, hj => by
    have hp : p.Prime := Fact.out
    obtain ⟨E, hFE, hE, hfd, y, hy⟩ := exists_level_root F hF I k a ha hI j (Nat.le_of_succ_le hj)
    haveI := hfd

    have ha' : ((a : ↥F) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; apply ha; apply Subtype.ext; apply Subtype.ext; (simp at h ⊢; exact h)
    have hyval : (((y : 𝓞 ↥E) : ↥E) : AlgebraicClosure ℚ) ^ p ^ j = ((a : ↥F) : AlgebraicClosure ℚ) := by
      have := congrArg (fun t : 𝓞 ↥E => ((t : ↥E) : AlgebraicClosure ℚ)) hy
      simpa using this
    have hy0 : ((y : 𝓞 ↥E) : ↥E) ≠ 0 := by
      intro h
      apply ha'
      rw [← hyval, show (((y : 𝓞 ↥E) : ↥E) : AlgebraicClosure ℚ) = 0 from by rw [h]; rfl, zero_pow (pow_ne_zero _ hp.ne_zero)]

    have hJ := span_eq_pow_of_pow_eq (p := p) hFE I k j (Nat.le_of_succ_le hj) a hI y hy
    have hdvd : p ∣ p ^ (k - j) := dvd_pow_self p (by omega)
    have hdiv := dvd_ord_of_span_eq_pow (p := p) E y hy0 _ _ hdvd hJ

    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (((y : 𝓞 ↥E) : ↥E) : AlgebraicClosure ℚ) hp.pos
    obtain ⟨E', hEE', hzE', hE', -, hfd'⟩ := exists_kummer_level S hpS E hE ((y : 𝓞 ↥E) : ↥E) hy0 (fun w _ => hdiv w) z hz
    haveI := hfd'

    have hzp : (⟨z, hzE'⟩ : ↥E') ^ p = ((φ hEE' y : 𝓞 ↥E') : ↥E') := by
      apply Subtype.ext
      simpa using hz
    have hint : IsIntegral ℤ (⟨z, hzE'⟩ : ↥E') := by
      apply IsIntegral.of_pow hp.pos
      rw [hzp]
      exact RingOfIntegers.isIntegral_coe _
    refine ⟨E', hFE.trans hEE', hE', hfd', ⟨⟨z, hzE'⟩, hint⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change z ^ p ^ (j + 1) = ((a : ↥F) : AlgebraicClosure ℚ)
    rw [pow_succ', pow_mul, hz, hyval]

include hpS in

theorem a5 (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F) (ha : a ≠ 0) (hI : I ^ p ^ k = Ideal.span {a}) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'), F'.IsUnramifiedOutside S ∧
      (I.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom)).IsPrincipal := by
  obtain ⟨E, hFE, hE, hfd, y, hy⟩ := exists_level_root S hpS F hF I k a ha hI k le_rfl
  haveI := hfd
  have hJ := span_eq_pow_of_pow_eq (p := p) hFE I k k le_rfl a hI y hy
  rw [Nat.sub_self, pow_zero, pow_one] at hJ
  exact ⟨E, hFE, hE, ⟨y, by rw [← hJ, Ideal.submodule_span_eq]⟩⟩

end A5c
end CycBaseCAP

open NumberField ExtCitation in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (I : Ideal (𝓞 ↥F)) (k : ℕ) (a : 𝓞 ↥F) (ha : a ≠ 0) (hI : I ^ p ^ k = Ideal.span {a}) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'), F'.IsUnramifiedOutside S ∧
      (I.map (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom)).IsPrincipal :=
  CycBaseCAP.a5 S hpS F hF I k a ha hI

end S_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span
end P2MW
export P2MW.S_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span (solution)
