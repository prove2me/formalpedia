-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.polynomialCurve_principal_divisor_balance_finite_parameter_degree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T10:47:46.422313+00:00
-- url     : https://prove2.me/submissions/95abf377-2d8c-49d7-af53-1691e6db991d

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
open Polynomial

namespace S39FS

theorem nonneg_of_root {E : Type} [Field E] {R : Type} [CommRing R] (i : R →+* E)
    (nu : AddValuation E (WithTop ℤ))
    (p : R[X]) (x : E) (hx : p.eval₂ i x = 0)
    (hlead : nu (i p.leadingCoeff) = 0) (hcoeff : ∀ j, 0 ≤ nu (i (p.coeff j))) : 0 ≤ nu x := by
  by_contra hneg
  push_neg at hneg
  have hx0 : x ≠ 0 := by rintro rfl; simp at hneg
  have hxt : nu x ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact hx0
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hxt
  rw [← hk] at hneg
  have hk0 : k < 0 := by exact_mod_cast hneg
  set n := p.natDegree
  rw [eval₂_eq_sum_range, Finset.sum_range_succ] at hx
  have htop : nu (i (p.coeff n) * x ^ n) = ((n * k : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk]
    have : i (p.coeff n) = i p.leadingCoeff := rfl
    rw [this, hlead, zero_add]
    norm_cast
  have hlow : ((n * k + 1 : ℤ) : WithTop ℤ) ≤ nu (∑ j ∈ Finset.range n, i (p.coeff j) * x ^ j) := by
    apply AddValuation.map_le_sum
    intro j hj
    rw [Finset.mem_range] at hj
    rw [AddValuation.map_mul, AddValuation.map_pow, ← hk]
    have h1 : ((n * k + 1 : ℤ) : WithTop ℤ) ≤ j • ((k : ℤ) : WithTop ℤ) := by
      have : (j • (k : WithTop ℤ)) = ((j * k : ℤ) : WithTop ℤ) := by norm_cast
      rw [this, WithTop.coe_le_coe]
      have : (j : ℤ) + 1 ≤ n := by exact_mod_cast hj
      nlinarith
    exact le_trans h1 (le_add_of_nonneg_left (hcoeff j))
  have hlt : nu (i (p.coeff n) * x ^ n) < nu (∑ j ∈ Finset.range n, i (p.coeff j) * x ^ j) := by
    rw [htop]
    refine lt_of_lt_of_le ?_ hlow
    rw [WithTop.coe_lt_coe]; omega
  have := AddValuation.map_add_eq_of_lt_left nu hlt
  rw [add_comm, hx, htop] at this
  rw [AddValuation.map_zero] at this
  exact WithTop.top_ne_coe this


section Inj
variable {C : Type} [CommRing C] [IsDomain C] [IsDedekindDomain C] {E : Type} [Field E]
  [Algebra C E] [IsFractionRing C E]

def Good (P : Ideal C) (nu : AddValuation E (WithTop ℤ)) : Prop :=
  (∀ c : C, 0 ≤ nu (algebraMap C E c)) ∧ (∀ c : C, 0 < nu (algebraMap C E c) ↔ c ∈ P) ∧
    (∀ k : ℤ, ∃ f, nu f = k)

theorem good_eq (P : Ideal C) [hPp : P.IsPrime] (hP : P ≠ ⊥) (nu1 nu2 : AddValuation E (WithTop ℤ))
    (h1 : Good P nu1) (h2 : Good P nu2) : nu1 = nu2 := by
  classical
  let R := Localization.AtPrime P
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C hP R
  have hinjCE : Function.Injective (algebraMap C E) := IsFractionRing.injective C E
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap C E y) := by
    intro y
    apply IsUnit.mk0
    rw [Ne, ← map_zero (algebraMap C E), hinjCE.eq_iff]
    intro h0; apply y.2; rw [h0]; exact P.zero_mem
  let φ : R →+* E := IsLocalization.lift (M := P.primeCompl) hunit
  have hφ : ∀ c : C, φ (algebraMap C R c) = algebraMap C E c := IsLocalization.lift_eq hunit
  have hinjCR : Function.Injective (algebraMap C R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  -- every element of E is a quotient of elements of R
  have hdiv : ∀ x : E, x ≠ 0 → ∃ r1 r2 : R, r1 ≠ 0 ∧ r2 ≠ 0 ∧ x = φ r1 / φ r2 := by
    intro x hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) x
    refine ⟨algebraMap C R a, algebraMap C R b, ?_, ?_, by rw [hφ, hφ]⟩
    · intro h; apply hx; rw [← map_zero (algebraMap C R), hinjCR.eq_iff] at h; simp [h]
    · intro h; rw [← map_zero (algebraMap C R), hinjCR.eq_iff] at h
      exact nonZeroDivisors.ne_zero hb h
  -- valuation facts for a good valuation
  have key : ∀ nu : AddValuation E (WithTop ℤ), Good P nu →
      ∀ (u : Rˣ) (k : ℕ), nu (φ (↑u * ϖ ^ k)) = ((k : ℤ) : WithTop ℤ) := by
    intro nu hnu
    obtain ⟨hnn, hpos, hsurj⟩ := hnu
    have hs0 : ∀ s : P.primeCompl, nu (algebraMap C E s) = 0 := by
      intro s
      refine le_antisymm ?_ (hnn s)
      by_contra h; push_neg at h
      exact s.2 ((hpos s).mp h)
    have hmk : ∀ (c : C) (s : P.primeCompl), nu (φ (IsLocalization.mk' R c s)) = nu (algebraMap C E c) := by
      intro c s
      have e := IsLocalization.mk'_spec R c s
      have e2 : φ (IsLocalization.mk' R c s) * algebraMap C E s = algebraMap C E c := by
        rw [← hφ, ← hφ, ← map_mul, e]
      rw [← e2, AddValuation.map_mul, hs0, add_zero]
    have hR0 : ∀ r : R, 0 ≤ nu (φ r) := by
      intro r
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
      rw [hmk]; exact hnn c
    have hunitv : ∀ u : Rˣ, nu (φ u) = 0 := by
      intro u
      have h1 := hR0 u
      have h2 := hR0 ↑u⁻¹
      have h3 : nu (φ u) + nu (φ ↑u⁻¹) = 0 := by
        rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
      have hne1 : nu (φ u) ≠ ⊤ := by intro h; rw [h, top_add] at h3; exact WithTop.top_ne_zero h3
      have hne2 : nu (φ ↑u⁻¹) ≠ ⊤ := by intro h; rw [h, add_top] at h3; exact WithTop.top_ne_zero h3
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne1
      obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne2
      rw [← ha, ← hb] at h3
      rw [← ha] at h1 ⊢
      rw [← hb] at h2
      have : a + b = 0 := by exact_mod_cast h3
      have : 0 ≤ a := by exact_mod_cast h1
      have : 0 ≤ b := by exact_mod_cast h2
      have : a = 0 := by omega
      rw [this]; rfl
    -- valuation of the uniformizer
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective P.primeCompl ϖ
    dsimp only at hcs
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [IsLocalization.mk'_zero] at hcs; exact hϖ.ne_zero hcs.symm
    have hcP : c ∈ P := by
      by_contra hc
      apply hϖ.not_isUnit
      rw [← hcs, IsLocalization.AtPrime.isUnit_mk'_iff]; exact hc
    have hϖv : nu (φ ϖ) = nu (algebraMap C E c) := by rw [← hcs, hmk]
    have hct : nu (algebraMap C E c) ≠ ⊤ := by
      rw [Ne, AddValuation.top_iff, ← map_zero (algebraMap C E), hinjCE.eq_iff]; exact hc0
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hct
    have hm0 : 0 < m := by
      have := (hpos c).mpr hcP; rw [← hm] at this; exact_mod_cast this
    have hval' : ∀ (u : Rˣ) (k : ℕ), nu (φ (↑u * ϖ ^ k)) = (((k : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro u k
      rw [map_mul, AddValuation.map_mul, hunitv, zero_add, map_pow, AddValuation.map_pow, hϖv, ← hm]
      norm_cast
    have hval : ∀ r : R, r ≠ 0 → ∃ k : ℕ, nu (φ r) = (((k : ℤ) * m : ℤ) : WithTop ℤ) := by
      intro r hr
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
      exact ⟨k, hval' u k⟩
    -- m = 1 from surjectivity
    have hm1 : m = 1 := by
      obtain ⟨y, hy⟩ := hsurj 1
      have hy0 : y ≠ 0 := by rintro rfl; simp at hy
      obtain ⟨r1, r2, hr1, hr2, rfl⟩ := hdiv y hy0
      obtain ⟨k1, hk1⟩ := hval r1 hr1
      obtain ⟨k2, hk2⟩ := hval r2 hr2
      rw [AddValuation.map_div, hk1, hk2] at hy
      have : ((k1 : ℤ) * m - (k2 : ℤ) * m : ℤ) = 1 := by
        have := hy; norm_cast at this
      have : ((k1 : ℤ) - k2) * m = 1 := by linarith
      exact Int.eq_one_of_mul_eq_one_left (by omega) this
    intro u k
    rw [hval' u k, hm1, mul_one]
  -- conclude
  ext x
  by_cases hx : x = 0
  · rw [hx, AddValuation.map_zero, AddValuation.map_zero]
  obtain ⟨r1, r2, hr1, hr2, rfl⟩ := hdiv x hx
  obtain ⟨k1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr1 hϖ
  obtain ⟨k2, u2, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr2 hϖ
  rw [AddValuation.map_div, AddValuation.map_div, key nu1 h1, key nu1 h1, key nu2 h2, key nu2 h2]

end Inj

theorem wt_add_pos {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      have : (0 : ℤ) ≤ a := by exact_mod_cast ha
      have : (0 : ℤ) < b := by exact_mod_cast hb
      exact_mod_cast (by omega : (0 : ℤ) < a + b)

theorem wt_pos_or {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a + b) : 0 < a ∨ 0 < b := by
  by_contra hc
  push_neg at hc
  have h1 : a = 0 := le_antisymm hc.1 ha
  have h2 : b = 0 := le_antisymm hc.2 hb
  rw [h1, h2, add_zero] at h
  exact lt_irrefl _ h

theorem core {E : Type} [Field E] {A K : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Algebra A E] [Algebra K E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (a : A) (ha : a ≠ 0)
    (S : Set (AddValuation E (WithTop ℤ)))
    (hS : ∀ nu ∈ S, (∀ b : A, 0 ≤ nu (algebraMap A E b)) ∧ 0 < nu (algebraMap A E a) ∧
      ∀ k : ℤ, ∃ f, nu f = k) : S.Finite := by
  classical
  let C := integralClosure A E
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing C E := IsIntegralClosure.isFractionRing_of_finite_extension A K E C
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hnn : ∀ nu ∈ S, ∀ c : C, 0 ≤ nu (algebraMap C E c) := by
    intro nu hnu c
    obtain ⟨p, hmon, hp⟩ := c.2
    exact nonneg_of_root (algebraMap A E) nu p _ hp
      (by rw [hmon.leadingCoeff, map_one, AddValuation.map_one]) (fun j => (hS nu hnu).1 _)
  let P : ∀ nu : AddValuation E (WithTop ℤ), (∀ c : C, 0 ≤ nu (algebraMap C E c)) → Ideal C :=
    fun nu hn =>
    { carrier := {c : C | 0 < nu (algebraMap C E c)}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
        exact lt_of_lt_of_le (lt_min hx hy) (AddValuation.map_add nu _ _)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hx ⊢
        exact wt_add_pos (hn c) hx }
  have hmemP : ∀ nu hn c, c ∈ P nu hn ↔ 0 < nu (algebraMap C E c) := fun _ _ _ => Iff.rfl
  have hprime : ∀ nu hn, (P nu hn).IsPrime := by
    intro nu hn
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmemP nu hn, map_one, AddValuation.map_one]; exact lt_irrefl _
    · intro x y hxy
      rw [hmemP nu hn, map_mul, AddValuation.map_mul] at hxy
      exact wt_pos_or (hn x) (hn y) hxy
  set aC : C := algebraMap A C a with haC
  have haCE : algebraMap C E aC = algebraMap A E a := by
    rw [haC, ← IsScalarTower.algebraMap_apply]
  have haC0 : aC ≠ 0 := by
    intro h
    apply ha
    apply hAE
    rw [← haCE, h, map_zero, map_zero]
  have hmemA : ∀ nu (hnu : nu ∈ S), aC ∈ P nu (hnn nu hnu) := by
    intro nu hnu
    rw [hmemP nu (hnn nu hnu), haCE]; exact (hS nu hnu).2.1
  let v : S → IsDedekindDomain.HeightOneSpectrum C := fun nu =>
    { asIdeal := P nu.1 (hnn nu.1 nu.2)
      isPrime := hprime nu.1 (hnn nu.1 nu.2)
      ne_bot := by
        intro h
        have := hmemA nu.1 nu.2
        rw [h, Ideal.mem_bot] at this
        exact haC0 this }
  have hT := Ideal.finite_factors (R := C) (I := Ideal.span {aC})
    (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact haC0)
  rw [← Set.finite_coe_iff] at hT ⊢
  let v' : S → {w : IsDedekindDomain.HeightOneSpectrum C | w.asIdeal ∣ Ideal.span {aC}} :=
    fun nu => ⟨v nu, by
      simp only [Set.mem_ofPred_eq]
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hmemA nu.1 nu.2⟩
  refine Finite.of_injective v' ?_
  intro nu1 nu2 h
  have hP : P nu1.1 (hnn nu1.1 nu1.2) = P nu2.1 (hnn nu2.1 nu2.2) := by
    have := congrArg (fun w => (Subtype.val w).asIdeal) h
    exact this
  haveI := hprime nu1.1 (hnn nu1.1 nu1.2)
  apply Subtype.ext
  refine good_eq (P nu1.1 (hnn nu1.1 nu1.2)) ?_ nu1.1 nu2.1
    ⟨hnn nu1.1 nu1.2, fun c => Iff.rfl, (hS nu1.1 nu1.2).2.2⟩
    ⟨hnn nu2.1 nu2.2, fun c => by rw [hP]; exact Iff.rfl, (hS nu2.1 nu2.2).2.2⟩
  intro h0
  have := hmemA nu1.1 nu1.2
  rw [h0, Ideal.mem_bot] at this
  exact haC0 this

open OAI.PiExponent.FormalInterpolation in
theorem finite_pos (E : Type) [Field E] [Algebra ℂ E] (g : E) (hg : Transcendental ℂ g)
    (hfin : FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    {nu : PolynomialCurvePlace E | 0 < nu.1 g}.Finite := by
  classical
  let K := IntermediateField.adjoin ℂ {g}
  let g' : K := ⟨g, IntermediateField.mem_adjoin_simple_self ℂ g⟩
  letI : Algebra ℂ[X] K := (aeval g').toRingHom.toAlgebra
  letI : Algebra ℂ[X] E := (aeval g).toRingHom.toAlgebra
  have hKE : ∀ p : ℂ[X], ((aeval g' p : K) : E) = aeval g p := by
    intro p
    exact (aeval_algHom_apply K.val g' p).symm
  haveI : IsScalarTower ℂ[X] K E := IsScalarTower.of_algebraMap_eq fun p => (hKE p).symm
  have hinj : Function.Injective (algebraMap ℂ[X] K) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply hg
    refine ⟨p, hp0, ?_⟩
    rw [← hKE]
    have : aeval g' p = 0 := hp
    rw [this]; rfl
  haveI : FaithfulSMul ℂ[X] K := (faithfulSMul_iff_algebraMap_injective ℂ[X] K).mpr hinj
  haveI : IsFractionRing ℂ[X] K := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (z : E)).mp z.2
    refine ⟨r, s, ?_⟩
    apply Subtype.ext
    rw [hz, IntermediateField.coe_div]
    show _ = ((aeval g' r : K) : E) / ((aeval g' s : K) : E)
    rw [hKE, hKE]
  haveI : FiniteDimensional K E := hfin
  have hS := core (A := ℂ[X]) (K := K) (E := E) X X_ne_zero
    (Subtype.val '' {nu : PolynomialCurvePlace E | 0 < nu.1 g}) (by
      rintro _ ⟨nu, hnu, rfl⟩
      refine ⟨fun b => ?_, ?_, nu.2.2⟩
      · show 0 ≤ nu.1 (aeval g b)
        rw [aeval_eq_sum_range]
        apply AddValuation.map_le_sum
        intro i _
        rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow]
        have h1 : 0 ≤ nu.1 (algebraMap ℂ E (b.coeff i)) := by
          by_cases hb : b.coeff i = 0
          · rw [hb, map_zero, AddValuation.map_zero]; exact le_top
          · rw [nu.2.1 _ hb]
        have h2 : 0 ≤ i • nu.1 g := nsmul_nonneg (le_of_lt hnu) i
        exact le_trans h2 (le_add_of_nonneg_left h1)
      · show 0 < nu.1 (aeval g X)
        rw [aeval_X]; exact hnu)
  exact Set.Finite.of_finite_image hS Subtype.val_injective.injOn

theorem wt_neg_pos {a : WithTop ℤ} (ha : a < 0) : 0 < -a := by
  induction a using WithTop.recTopCoe with
  | top => simp at ha
  | coe a =>
    have : a < 0 := by exact_mod_cast ha
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
    exact_mod_cast (by omega : (0 : ℤ) < -a)

open OAI.PiExponent.FormalInterpolation in
theorem main (E : Type) [Field E] [Algebra ℂ E] (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
    (ht : Transcendental ℂ t) (f : E) :
    {nu : PolynomialCurvePlace E | polynomialCurveOrder nu f ≠ 0}.Finite := by
  classical
  let Z : E → Set (PolynomialCurvePlace E) := fun x => {nu | nu.1 x ≠ 0}
  have hmul : ∀ x y, (Z x).Finite → (Z y).Finite → (Z (x * y)).Finite := by
    intro x y hx hy
    refine (hx.union hy).subset fun nu hnu => ?_
    by_contra h
    simp only [Set.mem_union, not_or, Z, Set.mem_ofPred_eq, not_not] at h hnu
    rw [AddValuation.map_mul, h.1, h.2, add_zero] at hnu
    exact hnu rfl
  have hinv : ∀ x, (Z x).Finite → (Z x⁻¹).Finite := by
    intro x hx
    refine hx.subset fun nu hnu => ?_
    simp only [Z, Set.mem_ofPred_eq] at hnu ⊢
    intro h; apply hnu; rw [AddValuation.map_inv, h, neg_zero]
  have hconst : ∀ c : ℂ, c ≠ 0 → (Z (algebraMap ℂ E c)).Finite := by
    intro c hc
    refine Set.finite_empty.subset fun nu hnu => ?_
    exact hnu (nu.2.1 c hc)
  -- the linear factors
  have hlin : ∀ c : ℂ, (Z (t - algebraMap ℂ E c)).Finite := by
    intro c
    have heq1 : IntermediateField.adjoin ℂ {t - algebraMap ℂ E c} = IntermediateField.adjoin ℂ {t} := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact sub_mem (IntermediateField.mem_adjoin_simple_self ℂ t) (IntermediateField.algebraMap_mem _ c)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have := add_mem (IntermediateField.mem_adjoin_simple_self ℂ (t - algebraMap ℂ E c))
          (IntermediateField.algebraMap_mem (IntermediateField.adjoin ℂ {t - algebraMap ℂ E c}) c)
        simpa using this
    have heq2 : IntermediateField.adjoin ℂ {t⁻¹} = IntermediateField.adjoin ℂ {t} := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t)
      · rw [IntermediateField.adjoin_simple_le_iff]
        simpa using inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t⁻¹)
    have hf1 : FiniteDimensional (IntermediateField.adjoin ℂ {t - algebraMap ℂ E c}) E := by
      rw [heq1]; exact hfinite
    have hf2 : FiniteDimensional (IntermediateField.adjoin ℂ {t⁻¹}) E := by
      rw [heq2]; exact hfinite
    have ht1 : Transcendental ℂ (t - algebraMap ℂ E c) := by
      intro halg
      apply ht
      have := (halg.isIntegral.add (isIntegral_algebraMap (x := c))).isAlgebraic
      simpa using this
    have ht2 : Transcendental ℂ t⁻¹ := fun h => ht (IsAlgebraic.inv_iff.mp h)
    refine ((finite_pos E _ ht1 hf1).union (finite_pos E _ ht2 hf2)).subset fun nu hnu => ?_
    simp only [Z, Set.mem_ofPred_eq] at hnu
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases lt_or_gt_of_ne hnu with hneg | hpos
    · right
      rw [AddValuation.map_inv]
      apply wt_neg_pos
      by_contra h0
      push_neg at h0
      have hc0 : 0 ≤ nu.1 (algebraMap ℂ E c) := by
        by_cases hc : c = 0
        · rw [hc, map_zero, AddValuation.map_zero]; exact le_top
        · rw [nu.2.1 c hc]
      have := AddValuation.map_sub nu.1 t (algebraMap ℂ E c)
      exact absurd (lt_of_le_of_lt (le_trans (le_min h0 hc0) this) hneg) (lt_irrefl _)
    · left; exact hpos
  -- polynomials in t
  have hpoly : ∀ n : ℕ, ∀ p : ℂ[X], p.natDegree = n → p ≠ 0 → (Z (aeval t p)).Finite := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro p hpn hp0
      by_cases hdeg : p.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero hdeg, aeval_C]
        apply hconst
        intro h; apply hp0
        rw [eq_C_of_natDegree_eq_zero hdeg, h, map_zero]
      · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
          intro h; apply hdeg; rw [natDegree_eq_zero_iff_degree_le_zero, h])
        have hfac := mul_divByMonic_eq_iff_isRoot.mpr ha
        set q := p /ₘ (X - C a)
        have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hfac; exact hp0 hfac.symm
        have hqdeg : q.natDegree < n := by
          rw [← hpn, ← hfac, natDegree_mul (X_sub_C_ne_zero a) hq0, natDegree_X_sub_C]; omega
        rw [← hfac, map_mul, map_sub, aeval_X, aeval_C]
        exact hmul _ _ (hlin a) (ih _ hqdeg q rfl hq0)
  have hK : ∀ x : E, x ∈ IntermediateField.adjoin ℂ {t} → x ≠ 0 → (Z x).Finite := by
    intro x hx hx0
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ x).mp hx
    have hr : r ≠ 0 := by rintro rfl; simp at hx0
    have hs : s ≠ 0 := by rintro rfl; simp at hx0
    rw [div_eq_mul_inv]
    exact hmul _ _ (hpoly _ r rfl hr) (hinv _ (hpoly _ s rfl hs))
  -- the function f
  by_cases hf : f = 0
  · refine Set.finite_empty.subset fun nu hnu => ?_
    simp only [Set.mem_ofPred_eq, polynomialCurveOrder, hf, AddValuation.map_zero] at hnu
    exact hnu rfl
  let K := IntermediateField.adjoin ℂ {t}
  have hint : IsIntegral K f := IsIntegral.of_finite K f
  set p := minpoly K f with hp
  have hmon : p.Monic := minpoly.monic hint
  have hc0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf
  have hfin : (⋃ j ∈ p.support, Z (algebraMap K E (p.coeff j))).Finite := by
    refine Set.Finite.biUnion p.support.finite_toSet fun j hj => ?_
    apply hK _ (p.coeff j).2
    exact fun h => mem_support_iff.mp hj (Subtype.ext h)
  refine hfin.subset fun nu hnu => ?_
  by_contra hout
  apply hnu
  simp only [Set.mem_iUnion, not_exists, Z, Set.mem_ofPred_eq, not_not] at hout
  have hcoef : ∀ j, 0 ≤ nu.1 (algebraMap K E (p.coeff j)) := by
    intro j
    by_cases hj : j ∈ p.support
    · rw [hout j hj]
    · rw [notMem_support_iff.mp hj, map_zero, AddValuation.map_zero]; exact le_top
  have h1 : 0 ≤ nu.1 f := by
    refine nonneg_of_root (algebraMap K E) nu.1 p f ?_ ?_ hcoef
    · rw [← aeval_def]; exact minpoly.aeval K f
    · rw [hmon.leadingCoeff, map_one, AddValuation.map_one]
  have h2 : 0 ≤ nu.1 f⁻¹ := by
    letI : Invertible f := invertibleOfNonzero hf
    refine nonneg_of_root (algebraMap K E) nu.1 p.reverse f⁻¹ ?_ ?_ ?_
    · have e := eval₂_reverse_mul_pow (algebraMap K E) f p
      have e0 : eval₂ (algebraMap K E) f p = 0 := by rw [← aeval_def]; exact minpoly.aeval K f
      rw [invOf_eq_inv, e0] at e
      rcases mul_eq_zero.mp e with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff'.mp h).1 hf
    · rw [reverse_leadingCoeff, trailingCoeff, natTrailingDegree_eq_zero.mpr (Or.inr hc0)]
      exact hout 0 (mem_support_iff.mpr hc0)
    · intro j; rw [coeff_reverse]; exact hcoef _
  have h3 : nu.1 f = 0 := by
    rw [AddValuation.map_inv] at h2
    have hne : nu.1 f ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact hf
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hk] at h1 h2 ⊢
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg] at h2
    have a1 : 0 ≤ k := by exact_mod_cast h1
    have a2 : 0 ≤ -k := by exact_mod_cast h2
    have : k = 0 := by omega
    rw [this]; rfl
  show polynomialCurveOrder nu f = 0
  rw [polynomialCurveOrder, h3]; rfl

end S39FS

open Polynomial

namespace S39FS

noncomputable def Lg (z : WithZero (Multiplicative ℤ)) : WithTop ℤ :=
  if z = 0 then ⊤ else ((-WithZero.log z : ℤ) : WithTop ℤ)

theorem Lg_anti {a b : WithZero (Multiplicative ℤ)} (h : a ≤ b) : Lg b ≤ Lg a := by
  unfold Lg
  by_cases ha : a = 0
  · simp [ha]
  have hb : b ≠ 0 := by
    intro hb; rw [hb] at h; exact ha (le_antisymm h zero_le')
  rw [if_neg ha, if_neg hb, WithTop.coe_le_coe]
  have := (WithZero.log_le_log ha hb).mpr h
  omega

theorem Lg_mul (a b : WithZero (Multiplicative ℤ)) : Lg (a * b) = Lg a + Lg b := by
  unfold Lg
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, WithZero.log_mul ha hb]
  norm_cast; ring

theorem Lg_pos_iff (a : WithZero (Multiplicative ℤ)) : 0 < Lg a ↔ a < 1 := by
  unfold Lg
  by_cases ha : a = 0
  · simp [ha]
  rw [if_neg ha]
  have : WithZero.log a < 0 ↔ a < 1 := by
    rw [← WithZero.log_one, WithZero.log_lt_log ha one_ne_zero]
  rw [← this]
  constructor
  · intro h; have : (0 : ℤ) < -WithZero.log a := by exact_mod_cast h
    omega
  · intro h; exact_mod_cast (by omega : (0 : ℤ) < -WithZero.log a)

theorem Lg_exp (k : ℤ) : Lg (WithZero.exp k) = ((-k : ℤ) : WithTop ℤ) := by
  unfold Lg
  rw [if_neg WithZero.exp_ne_zero, WithZero.log_exp]

noncomputable def toAdd {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) :
    AddValuation E (WithTop ℤ) :=
  AddValuation.of (fun x => Lg (v x)) (by simp [Lg]) (by simp [Lg])
    (fun x y => by
      have h := v.map_add x y
      rcases le_total (v x) (v y) with hxy | hxy
      · rw [max_eq_right hxy] at h
        exact le_trans (min_le_right _ _) (Lg_anti h)
      · rw [max_eq_left hxy] at h
        exact le_trans (min_le_left _ _) (Lg_anti h))
    (fun x y => by simp only [map_mul]; exact Lg_mul _ _)

theorem toAdd_apply {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) (x : E) :
    toAdd v x = Lg (v x) := rfl

theorem good_of_hos {C : Type} [CommRing C] [IsDomain C] [IsDedekindDomain C] {E : Type} [Field E]
    [Algebra C E] [IsFractionRing C E] (w : IsDedekindDomain.HeightOneSpectrum C) :
    Good w.asIdeal (toAdd (w.valuation E)) := by
  refine ⟨fun c => ?_, fun c => ?_, fun k => ?_⟩
  · rw [toAdd_apply]
    have := Lg_anti (w.valuation_le_one (K := E) c)
    simpa [Lg] using this
  · rw [toAdd_apply, Lg_pos_iff, w.valuation_lt_one_iff_mem]
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    have hπv : toAdd (w.valuation E) π = 1 := by
      rw [toAdd_apply, hπ, Lg_exp]; rfl
    have hπ0 : π ≠ 0 := by intro h; rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
    rcases le_or_gt 0 k with hk | hk
    · refine ⟨π ^ k.toNat, ?_⟩
      rw [AddValuation.map_pow, hπv]
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      rw [← this]; norm_cast; simp
    · refine ⟨π⁻¹ ^ (-k).toNat, ?_⟩
      rw [AddValuation.map_pow, AddValuation.map_inv, hπv]
      have : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have e : (-(1 : WithTop ℤ)) = ((-1 : ℤ) : WithTop ℤ) := rfl
      rw [e]
      calc ((-k).toNat • ((-1 : ℤ) : WithTop ℤ)) = ((((-k).toNat : ℕ) • (-1 : ℤ) : ℤ) : WithTop ℤ) := by
            norm_cast
        _ = (k : WithTop ℤ) := by rw [nsmul_eq_mul, this]; simp

theorem centre {C : Type} [CommRing C] [IsDomain C] {E : Type} [Field E] [Algebra C E]
    (nu : AddValuation E (WithTop ℤ)) (hn : ∀ c : C, 0 ≤ nu (algebraMap C E c)) :
    ∃ P : Ideal C, P.IsPrime ∧ ∀ c, c ∈ P ↔ 0 < nu (algebraMap C E c) := by
  let P : Ideal C :=
    { carrier := {c : C | 0 < nu (algebraMap C E c)}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
        exact lt_of_lt_of_le (lt_min hx hy) (AddValuation.map_add nu _ _)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hx ⊢
        exact wt_add_pos (hn c) hx }
  refine ⟨P, ⟨?_, ?_⟩, fun c => Iff.rfl⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    show ¬ (0 < nu (algebraMap C E 1))
    rw [map_one, AddValuation.map_one]; exact lt_irrefl _
  · intro x y hxy
    change 0 < nu (algebraMap C E (x * y)) at hxy
    rw [map_mul, AddValuation.map_mul] at hxy
    exact wt_pos_or (hn x) (hn y) hxy

theorem wt_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) : a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      have : (0 : ℤ) ≤ a := by exact_mod_cast ha
      have : (0 : ℤ) ≤ b := by exact_mod_cast hb
      have : a + b = 0 := by exact_mod_cast h
      exact_mod_cast (by omega : a = 0)

open OAI.PiExponent.FormalInterpolation in
theorem deg_pos (E : Type) [Field E] [Algebra ℂ E] (g : E) (hg : Transcendental ℂ g)
    (hfin : FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    ∑ᶠ nu : PolynomialCurvePlace E, max 0 (polynomialCurveOrder nu g : ℝ) =
      (Module.finrank (IntermediateField.adjoin ℂ {g}) E : ℝ) := by
  classical
  let K := IntermediateField.adjoin ℂ {g}
  let g' : K := ⟨g, IntermediateField.mem_adjoin_simple_self ℂ g⟩
  letI : Algebra ℂ[X] K := (aeval g').toRingHom.toAlgebra
  letI : Algebra ℂ[X] E := (aeval g).toRingHom.toAlgebra
  have hKE : ∀ p : ℂ[X], ((aeval g' p : K) : E) = aeval g p := by
    intro p
    exact (aeval_algHom_apply K.val g' p).symm
  haveI : IsScalarTower ℂ[X] K E := IsScalarTower.of_algebraMap_eq fun p => (hKE p).symm
  have hinj : Function.Injective (algebraMap ℂ[X] K) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply hg
    refine ⟨p, hp0, ?_⟩
    rw [← hKE]
    have : aeval g' p = 0 := hp
    rw [this]; rfl
  haveI : FaithfulSMul ℂ[X] K := (faithfulSMul_iff_algebraMap_injective ℂ[X] K).mpr hinj
  haveI : IsFractionRing ℂ[X] K := by
    apply IsFractionRing.of_field
    intro z
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ (z : E)).mp z.2
    refine ⟨r, s, ?_⟩
    apply Subtype.ext
    rw [hz, IntermediateField.coe_div]
    show _ = ((aeval g' r : K) : E) / ((aeval g' s : K) : E)
    rw [hKE, hKE]
  haveI : FiniteDimensional K E := hfin
  have hAE : Function.Injective (algebraMap ℂ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℂ[X] K E]
    exact (algebraMap K E).injective.comp hinj
  haveI : Module.IsTorsionFree ℂ[X] E := Module.isTorsionFree_iff_algebraMap_injective.mpr hAE
  let C := integralClosure ℂ[X] E
  haveI : IsDedekindDomain C := integralClosure.isDedekindDomain ℂ[X] K E
  haveI : IsFractionRing C E := IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] K E C
  haveI : Module.Finite ℂ[X] C := IsIntegralClosure.finite ℂ[X] K E C
  let p : Ideal ℂ[X] := Ideal.span {X}
  haveI hpm : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible irreducible_X
  letI : Field (ℂ[X] ⧸ p) := Ideal.Quotient.field p
  have hp0 : p ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero
  have hsum := Ideal.sum_ramification_inertia C K E hp0
  set T := IsDedekindDomain.primesOverFinset p C with hT
  have hTmem : ∀ P, P ∈ T ↔ P.IsPrime ∧ P.LiesOver p := fun P => by
    rw [hT, IsDedekindDomain.mem_primesOverFinset_iff hp0]; rfl
  -- inertia degrees are one
  have hpe : Ideal.span {X - Polynomial.C (0 : ℂ)} = p := by simp [p]
  haveI : IsAlgClosed (ℂ[X] ⧸ p) := IsAlgClosed.of_ringEquiv ℂ (ℂ[X] ⧸ p)
    ((quotientSpanXSubCAlgEquiv (0 : ℂ)).toRingEquiv.symm.trans (Ideal.quotEquivOfEq hpe))
  have hinert : ∀ P ∈ T, p.inertiaDeg' P = 1 := by
    intro P hP
    obtain ⟨hPp, hlo⟩ := (hTmem P).mp hP
    haveI := hPp; haveI := hlo
    rw [Ideal.inertiaDeg'_algebraMap]
    haveI : Algebra.IsIntegral (ℂ[X] ⧸ p) (C ⧸ P) := Algebra.IsIntegral.of_finite _ _
    have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ[X] ⧸ p) (K := C ⧸ P)
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap (ℂ[X] ⧸ p) (C ⧸ P)) hb).finrank_eq,
      Module.finrank_self]
  -- places from primes
  have hconstC : ∀ b : ℂ, algebraMap C E (algebraMap ℂ[X] C (Polynomial.C b)) = algebraMap ℂ E b := by
    intro b
    rw [← IsScalarTower.algebraMap_apply]
    show aeval g (Polynomial.C b) = _
    rw [aeval_C]
  have htriv : ∀ nu : AddValuation E (WithTop ℤ), (∀ c : C, 0 ≤ nu (algebraMap C E c)) →
      ∀ b : ℂ, b ≠ 0 → nu (algebraMap ℂ E b) = 0 := by
    intro nu hn b hb
    have h1 := hn (algebraMap ℂ[X] C (Polynomial.C b))
    have h2 := hn (algebraMap ℂ[X] C (Polynomial.C b⁻¹))
    rw [hconstC] at h1 h2
    refine wt_eq_zero h1 h2 ?_
    rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hb, map_one, AddValuation.map_one]
  let Φ : IsDedekindDomain.HeightOneSpectrum C → PolynomialCurvePlace E := fun w =>
    ⟨toAdd (w.valuation E), htriv _ (good_of_hos w).1, (good_of_hos w).2.2⟩
  have hTprime : ∀ P : T, P.1.IsPrime := fun P => ((hTmem P.1).mp P.2).1
  have hTne : ∀ P : T, P.1 ≠ ⊥ := by
    intro P h
    obtain ⟨-, hlo⟩ := (hTmem P.1).mp P.2
    apply hp0
    rw [hlo.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℂ[X] C)
  let W : T → IsDedekindDomain.HeightOneSpectrum C := fun P => ⟨P.1, hTprime P, hTne P⟩
  let v : IsDedekindDomain.HeightOneSpectrum ℂ[X] := ⟨p, hpm.isPrime, hp0⟩
  have hval : ∀ P : T, polynomialCurveOrder (Φ (W P)) g = p.ramificationIdx' P.1 := by
    intro P
    haveI : (W P).asIdeal.LiesOver v.asIdeal := ((hTmem P.1).mp P.2).2
    have e := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (K := K) E v (W P)
      (algebraMap ℂ[X] K X)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton v X_ne_zero rfl] at e
    have hg' : algebraMap K E (algebraMap ℂ[X] K X) = g := by
      show ((aeval g' X : K) : E) = g
      rw [hKE, aeval_X]
    rw [hg', ← WithZero.exp_nsmul] at e
    show (toAdd ((W P).valuation E) g).untop₀ = _
    rw [toAdd_apply, ← e, Lg_exp]
    simp
    rfl
  have hnnC : ∀ nu : PolynomialCurvePlace E, 0 < nu.1 g → ∀ c : C, 0 ≤ nu.1 (algebraMap C E c) := by
    intro nu hnu c
    obtain ⟨q, hmon, hq⟩ := c.2
    refine nonneg_of_root (algebraMap ℂ[X] E) nu.1 q _ hq
      (by rw [hmon.leadingCoeff, map_one, AddValuation.map_one]) (fun j => ?_)
    show 0 ≤ nu.1 (aeval g (q.coeff j))
    rw [aeval_eq_sum_range]
    apply AddValuation.map_le_sum
    intro i _
    rw [Algebra.smul_def, AddValuation.map_mul, AddValuation.map_pow]
    have h1 : 0 ≤ nu.1 (algebraMap ℂ E ((q.coeff j).coeff i)) := by
      by_cases hb : (q.coeff j).coeff i = 0
      · rw [hb, map_zero, AddValuation.map_zero]; exact le_top
      · rw [nu.2.1 _ hb]
    have h2 : 0 ≤ i • nu.1 g := nsmul_nonneg (le_of_lt hnu) i
    exact le_trans h2 (le_add_of_nonneg_left h1)
  let F : PolynomialCurvePlace E → ℝ := fun nu => max 0 (polynomialCurveOrder nu g : ℝ)
  let Sfin : Finset (PolynomialCurvePlace E) := Finset.univ.image (fun P : T => Φ (W P))
  have hsupp : Function.support F ⊆ Sfin := by
    intro nu hnu
    rw [Function.mem_support] at hnu
    have hord : 0 < polynomialCurveOrder nu g := by
      by_contra h
      push_neg at h
      apply hnu
      simp only [F]
      exact max_eq_left (by exact_mod_cast h)
    have hpos : 0 < nu.1 g := by
      unfold polynomialCurveOrder at hord
      induction h : nu.1 g using WithTop.recTopCoe with
      | top => rw [h] at hord; simp at hord
      | coe k => rw [h] at hord; simp at hord; exact_mod_cast hord
    obtain ⟨P0, hP0, hiff⟩ := centre nu.1 (hnnC nu hpos)
    have hX : algebraMap ℂ[X] C X ∈ P0 := by
      rw [hiff, ← IsScalarTower.algebraMap_apply]
      show 0 < nu.1 (aeval g X)
      rw [aeval_X]; exact hpos
    have hlies : P0.LiesOver p := by
      refine ⟨hpm.eq_of_le (Ideal.IsPrime.under ℂ[X] P0).ne_top ?_⟩
      rw [Ideal.span_singleton_le_iff_mem]
      exact hX
    have hmem : P0 ∈ T := (hTmem P0).mpr ⟨hP0, hlies⟩
    rw [Finset.coe_image]
    refine ⟨⟨P0, hmem⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    apply Subtype.ext
    exact good_eq P0 (hTne ⟨P0, hmem⟩) _ _ (good_of_hos (W ⟨P0, hmem⟩))
      ⟨hnnC nu hpos, fun c => (hiff c).symm, nu.2.2⟩
  rw [finsum_eq_sum_of_support_subset F hsupp, Finset.sum_image]
  · have hF : ∀ P : T, F (Φ (W P)) = (p.ramificationIdx' P.1 : ℝ) := by
      intro P
      simp only [F]
      rw [hval P]
      simp
    rw [Finset.sum_congr rfl (fun P _ => hF P)]
    rw [Finset.sum_coe_sort T (fun P => (p.ramificationIdx' P : ℝ)), ← hsum]
    push_cast
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hinert P hP]; simp
  · intro P _ Q _ hPQ
    have hc : ∀ c : C, c ∈ P.1 ↔ c ∈ Q.1 := by
      intro c
      have h1 := (good_of_hos (E := E) (W P)).2.1 c
      have h2 := (good_of_hos (E := E) (W Q)).2.1 c
      have e : toAdd ((W P).valuation E) = toAdd ((W Q).valuation E) := congrArg Subtype.val hPQ
      rw [e] at h1
      exact h1.symm.trans h2
    exact Subtype.ext (Ideal.ext hc)

theorem exch (E : Type) [Field E] [Algebra ℂ E] (t f : E) (ht : Transcendental ℂ t)
    (hfin : FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) (hf : Transcendental ℂ f) :
    FiniteDimensional (IntermediateField.adjoin ℂ {f}) E := by
  have h1 : IsAlgebraic (IntermediateField.adjoin ℂ {t}) f :=
    (IsIntegral.of_finite (IntermediateField.adjoin ℂ {t}) f).isAlgebraic
  have h2 : IsAlgebraic (Algebra.adjoin ℂ {t}) f := IntermediateField.isAlgebraic_adjoin_iff.mp h1
  have h3 : IsAlgebraic (Algebra.adjoin ℂ {f}) (algebraMap E E t) :=
    IsAlgebraic.adjoin_singleton ht hf h2
  have h4 : IsAlgebraic (IntermediateField.adjoin ℂ {f}) t :=
    IntermediateField.isAlgebraic_adjoin_iff.mpr (by simpa using h3)
  let L := IntermediateField.adjoin (IntermediateField.adjoin ℂ {f}) {t}
  haveI : FiniteDimensional (IntermediateField.adjoin ℂ {f}) L :=
    IntermediateField.adjoin.finiteDimensional h4.isIntegral
  have hle : IntermediateField.adjoin ℂ {t} ≤ L.restrictScalars ℂ := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.mem_adjoin_simple_self _ t
  letI : Algebra (IntermediateField.adjoin ℂ {t}) (L.restrictScalars ℂ) :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin ℂ {t}) (L.restrictScalars ℂ) E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional (L.restrictScalars ℂ) E :=
    Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin ℂ {t}) _ E
  haveI : FiniteDimensional L E := this
  exact Module.Finite.trans L E

open OAI.PiExponent.FormalInterpolation in
theorem ord_const (E : Type) [Field E] [Algebra ℂ E] (f : E) (hf : ¬ Transcendental ℂ f)
    (nu : PolynomialCurvePlace E) : polynomialCurveOrder nu f = 0 := by
  have halg : IsAlgebraic ℂ f := not_not.mp hf
  haveI : Algebra.IsAlgebraic ℂ (IntermediateField.adjoin ℂ {f}) :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have hbot := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (IntermediateField.adjoin ℂ {f})
  have hmem := IntermediateField.mem_adjoin_simple_self ℂ f
  rw [hbot, IntermediateField.mem_bot] at hmem
  obtain ⟨c, rfl⟩ := hmem
  by_cases hc : c = 0
  · rw [hc, map_zero, polynomialCurveOrder, AddValuation.map_zero]; rfl
  · rw [polynomialCurveOrder, nu.2.1 c hc]; rfl

theorem adjoin_inv_eq (E : Type) [Field E] [Algebra ℂ E] (t : E) :
    IntermediateField.adjoin ℂ {t⁻¹} = IntermediateField.adjoin ℂ {t} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self ℂ t⁻¹)

open OAI.PiExponent.FormalInterpolation in
theorem ord_inv {E : Type} [Field E] [Algebra ℂ E] (nu : PolynomialCurvePlace E) (f : E) :
    polynomialCurveOrder nu f⁻¹ = -polynomialCurveOrder nu f := by
  unfold polynomialCurveOrder
  rw [AddValuation.map_inv]
  induction nu.1 f using WithTop.recTopCoe with
  | top => rfl
  | coe k => rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]; rfl

open OAI.PiExponent.FormalInterpolation in
theorem balance_of_trans (E : Type) [Field E] [Algebra ℂ E] (f : E) (hf : Transcendental ℂ f)
    (hF : FiniteDimensional (IntermediateField.adjoin ℂ {f}) E) :
    (∑ᶠ nu : PolynomialCurvePlace E, max 0 (polynomialCurveOrder nu f : ℝ)) =
    (∑ᶠ nu : PolynomialCurvePlace E, max 0 (-(polynomialCurveOrder nu f : ℝ))) := by
  have hinvt : Transcendental ℂ f⁻¹ := fun h => hf (IsAlgebraic.inv_iff.mp h)
  have hF' : FiniteDimensional (IntermediateField.adjoin ℂ {f⁻¹}) E := by
    rw [adjoin_inv_eq]; exact hF
  have e1 := deg_pos E f hf hF
  have e2 := deg_pos E f⁻¹ hinvt hF'
  have e3 : (∑ᶠ nu : PolynomialCurvePlace E, max 0 (-(polynomialCurveOrder nu f : ℝ))) =
      ∑ᶠ nu : PolynomialCurvePlace E, max 0 (polynomialCurveOrder nu f⁻¹ : ℝ) := by
    refine finsum_congr fun nu => ?_
    rw [ord_inv]; push_cast; rfl
  rw [e1, e3, e2, adjoin_inv_eq]

open OAI.PiExponent.FormalInterpolation in
theorem balance (E : Type) [Field E] [Algebra ℂ E] (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
    (ht : Transcendental ℂ t) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E, max 0 (polynomialCurveOrder nu f : ℝ)) =
    (∑ᶠ nu : PolynomialCurvePlace E, max 0 (-(polynomialCurveOrder nu f : ℝ))) := by
  by_cases hf : Transcendental ℂ f
  · exact balance_of_trans E f hf (exch E t f ht hfinite hf)
  · simp [ord_const E f hf]

open OAI.PiExponent.FormalInterpolation in
theorem sum_zero (E : Type) [Field E] [Algebra ℂ E] (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
    (ht : Transcendental ℂ t) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E, (polynomialCurveOrder nu f : ℝ)) = 0 := by
  have hfin := main E t hfinite ht f
  have hs1 : (Function.support fun nu : PolynomialCurvePlace E =>
      max 0 (polynomialCurveOrder nu f : ℝ)).Finite := by
    refine hfin.subset fun nu hnu => ?_
    simp only [Function.mem_support] at hnu
    simp only [Set.mem_ofPred_eq]
    intro h; apply hnu; rw [h]; simp
  have hs2 : (Function.support fun nu : PolynomialCurvePlace E =>
      max 0 (-(polynomialCurveOrder nu f : ℝ))).Finite := by
    refine hfin.subset fun nu hnu => ?_
    simp only [Function.mem_support] at hnu
    simp only [Set.mem_ofPred_eq]
    intro h; apply hnu; rw [h]; simp
  have e : ∀ nu : PolynomialCurvePlace E, (polynomialCurveOrder nu f : ℝ) =
      max 0 (polynomialCurveOrder nu f : ℝ) - max 0 (-(polynomialCurveOrder nu f : ℝ)) := by
    intro nu
    rcases le_total 0 (polynomialCurveOrder nu f : ℝ) with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  rw [finsum_congr e, finsum_sub_distrib hs1 hs2, balance E t hfinite ht f, sub_self]

end S39FS

open OAI.PiExponent.FormalInterpolation

theorem solution
    (E : Type) [Field E] [Algebra Complex E]
    (t : E)
    (hfinite : FiniteDimensional (IntermediateField.adjoin Complex {t}) E)
    (ht : Transcendental Complex t) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (polynomialCurveOrder nu f : Real)) =
    (∑ᶠ nu : PolynomialCurvePlace E,
      max 0 (-(polynomialCurveOrder nu f : Real))) :=
  S39FS.balance E t hfinite ht f
