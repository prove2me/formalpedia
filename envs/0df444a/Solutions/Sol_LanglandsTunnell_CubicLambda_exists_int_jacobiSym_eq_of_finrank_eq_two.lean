-- Prove2me | solution 1 for LanglandsTunnell.CubicLambda.exists_int_jacobiSym_eq_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/14d5fd3b-30b0-58bb-b81f-48ff1c6e226a

import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace QuadraticSplitting

private theorem exists_sqrt_generator_of_finrank_eq_two (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) :
    ∃ (α : 𝓞 L) (d : ℤ), d ≠ 0 ∧ (α : L) ∉ Set.range (algebraMap ℚ L) ∧ α ^ 2 = (d : 𝓞 L) := by
  obtain ⟨x, hx⟩ : ∃ x : L, x ∉ Set.range (algebraMap ℚ L) := by
    by_contra hall
    have hall' : ∀ w : L, ∃ c : ℚ, c • (1 : L) = w := fun w => by
      by_cases hw : w ∈ Set.range (algebraMap ℚ L)
      · obtain ⟨c, hc⟩ := hw
        exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm.trans hc⟩
      · exact (hall ⟨w, hw⟩).elim
    have h1 : Module.finrank ℚ L ≤ 1 := finrank_le_one (1 : L) hall'
    omega
  have hint : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  have hne : IntermediateField.adjoin ℚ {x} ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : IntermediateField ℚ L) :=
      hbot.le (IntermediateField.mem_adjoin_simple_self ℚ x)
    exact hx (IntermediateField.mem_bot.mp hxbot)
  have hdvd : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ∣ 2 :=
    ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) L, by rw [Module.finrank_mul_finrank, hL]⟩
  have h2 : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (IntermediateField.finrank_eq_one_iff.mp h1) hne
    · exact h1
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.finrank_top', hL]
    exact h2
  have hnat : (minpoly ℚ x).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top']
    exact hL
  have hc2 : (minpoly ℚ x).coeff 2 = 1 := by
    have h := (minpoly.monic hint).coeff_natDegree
    rwa [hnat] at h
  have hq : ((minpoly ℚ x).coeff 0 : L) + ((minpoly ℚ x).coeff 1 : L) * x + x ^ 2 = 0 := by
    have h := minpoly.aeval ℚ x
    rw [Polynomial.aeval_eq_sum_range, hnat] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, hc2,
      Algebra.smul_def, eq_ratCast, mul_one, Rat.cast_one, one_mul] at h
    linear_combination h
  obtain ⟨c₀, c₁, hq⟩ : ∃ c₀ c₁ : ℚ, (c₀ : L) + (c₁ : L) * x + x ^ 2 = 0 := ⟨_, _, hq⟩
  obtain ⟨D, hD⟩ : ∃ D : ℚ, D = c₁ ^ 2 - 4 * c₀ := ⟨_, rfl⟩
  have hy2 : (2 * x + (c₁ : L)) ^ 2 = (D : L) := by
    rw [hD]
    push_cast
    linear_combination 4 * hq
  have hy : 2 * x + (c₁ : L) ∉ Set.range (algebraMap ℚ L) := by
    rintro ⟨r, hr⟩
    apply hx
    refine ⟨(r - c₁) / 2, ?_⟩
    rw [eq_ratCast] at hr ⊢
    push_cast
    linear_combination hr / 2
  have hD0 : D ≠ 0 := by
    intro h0
    apply hy
    refine ⟨0, ?_⟩
    rw [map_zero]
    have hsq : (2 * x + (c₁ : L)) * (2 * x + (c₁ : L)) = 0 := by
      rw [← sq, hy2, h0, Rat.cast_zero]
    exact (mul_self_eq_zero.mp hsq).symm
  have hden : (D.den : L) ≠ 0 := Nat.cast_ne_zero.mpr D.den_nz
  have h1q : D * (D.den : ℚ) = (D.num : ℚ) := Rat.mul_den_eq_num D
  have h1 : (D : L) * (D.den : L) = (D.num : L) := by exact_mod_cast h1q
  have hz2 : ((D.den : L) * (2 * x + (c₁ : L))) ^ 2 = ((D.num * D.den : ℤ) : L) := by
    push_cast
    linear_combination (D.den : L) ^ 2 * hy2 + (D.den : L) * h1
  have hz : (D.den : L) * (2 * x + (c₁ : L)) ∉ Set.range (algebraMap ℚ L) := by
    rintro ⟨r, hr⟩
    apply hy
    refine ⟨r / D.den, ?_⟩
    rw [map_div₀, hr, map_natCast, div_eq_iff hden]
    ring
  have hzint : IsIntegral ℤ ((D.den : L) * (2 * x + (c₁ : L))) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hz2, ← eq_intCast (algebraMap ℤ L)]
    exact isIntegral_algebraMap
  refine ⟨⟨(D.den : L) * (2 * x + (c₁ : L)), hzint⟩, D.num * D.den, ?_, hz, ?_⟩
  · exact mul_ne_zero (Rat.num_ne_zero.mpr hD0) (by exact_mod_cast D.den_nz)
  · apply RingOfIntegers.ext
    simp only [map_pow, map_intCast, RingOfIntegers.map_mk]
    exact hz2

private theorem adjoin_singleton_eq_top_of_not_mem_range (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) (x : L) (hx : x ∉ Set.range (algebraMap ℚ L)) :
    Algebra.adjoin ℚ {x} = ⊤ := by
  have halg : IsAlgebraic ℚ x := (IsIntegral.of_finite ℚ x).isAlgebraic
  have hne : IntermediateField.adjoin ℚ {x} ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (⊥ : IntermediateField ℚ L) :=
      hbot.le (IntermediateField.mem_adjoin_simple_self ℚ x)
    exact hx (IntermediateField.mem_bot.mp hxbot)
  have hdvd : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ∣ 2 :=
    ⟨Module.finrank (IntermediateField.adjoin ℚ {x}) L, by rw [Module.finrank_mul_finrank, hL]⟩
  have h2 : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (IntermediateField.finrank_eq_one_iff.mp h1) hne
    · exact h1
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [IntermediateField.finrank_top', hL]
    exact h2
  exact (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg).symm.trans
    ((congrArg IntermediateField.toSubalgebra htop).trans IntermediateField.top_toSubalgebra)

private theorem minpoly_int_eq_X_sq_sub_C_of_sq_eq_intCast (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ) (hα : (α : L) ∉ Set.range (algebraMap ℚ L))
    (hsq : α ^ 2 = (d : 𝓞 L)) :
    minpoly ℤ α = Polynomial.X ^ 2 - Polynomial.C d := by
  have _ := hL
  have hint : IsIntegral ℤ α := IsIntegral.of_finite ℤ α
  have hdvd : minpoly ℤ α ∣ Polynomial.X ^ 2 - Polynomial.C d :=
    minpoly.isIntegrallyClosed_dvd hint (by simp [hsq])
  have hne1 : (minpoly ℤ α).natDegree ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.natDegree_eq_one_iff.mp h1)
    apply hα
    refine ⟨(c : ℚ), ?_⟩
    rw [← hc, RingOfIntegers.coe_eq_algebraMap]
    simp
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℤ).natDegree ≤
      (minpoly ℤ α).natDegree := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    have hpos := minpoly.natDegree_pos hint
    omega
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (Polynomial.monic_X_pow_sub_C d two_ne_zero) hdvd hdeg).symm

private theorem intCast_mem_asIdeal_iff_dvd_of_under_eq (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal) (𝔮 : HeightOneSpectrum (𝓞 L))
    (h𝔮 : 𝔮.under (𝓞 ℚ) = p) (n : ℤ) :
    (n : 𝓞 L) ∈ 𝔮.asIdeal ↔ (ℓ : ℤ) ∣ n := by
  have hm : ∀ z : 𝓞 ℚ, algebraMap (𝓞 ℚ) (𝓞 L) z ∈ 𝔮.asIdeal ↔ z ∈ p.asIdeal := by
    intro z
    have h : p.asIdeal = Ideal.under (𝓞 ℚ) 𝔮.asIdeal :=
      (congrArg HeightOneSpectrum.asIdeal h𝔮).symm.trans (HeightOneSpectrum.under_asIdeal (𝓞 ℚ) 𝔮)
    rw [h]
    exact Ideal.mem_comap.symm
  have key : (n : 𝓞 L) ∈ 𝔮.asIdeal ↔ (n : 𝓞 ℚ) ∈ p.asIdeal := by
    have h := hm (n : 𝓞 ℚ)
    rwa [map_intCast] at h
  rw [key]
  constructor
  · intro hn
    by_contra hndvd
    have hcop : IsCoprime (ℓ : ℤ) n :=
      (Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd.mpr hndvd
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : ((1 : ℤ) : 𝓞 ℚ) ∈ p.asIdeal := by
      rw [← hab]
      push_cast
      exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hp) (p.asIdeal.mul_mem_left _ hn)
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by exact_mod_cast h1))
  · rintro ⟨k, rfl⟩
    push_cast
    exact p.asIdeal.mul_mem_right _ hp

private theorem ramificationIdx_under_int_eq_one_of_sq_eq_intCast (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ)
    (hα : (α : L) ∉ Set.range (algebraMap ℚ L)) (hsq : α ^ 2 = (d : 𝓞 L)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h2d : ¬ (ℓ : ℤ) ∣ 2 * d) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : 𝔮.under (𝓞 ℚ) = p) :
    Ideal.ramificationIdx' (𝔮.asIdeal.under ℤ) 𝔮.asIdeal = 1 := by
  have hm := intCast_mem_asIdeal_iff_dvd_of_under_eq L ℓ hℓ p hp 𝔮 h𝔮
  have htop : Algebra.adjoin ℚ {(α : L)} = ⊤ :=
    adjoin_singleton_eq_top_of_not_mem_range L hL (α : L) hα
  have hmp : minpoly ℤ α = Polynomial.X ^ 2 - Polynomial.C d :=
    minpoly_int_eq_X_sq_sub_C_of_sq_eq_intCast L hL α d hα hsq
  have hder : Polynomial.aeval α (Polynomial.derivative (minpoly ℤ α)) = 2 * α := by
    rw [hmp]
    simp [map_ofNat]
  have hdiff : 2 * α ∈ differentIdeal ℤ (𝓞 L) := by
    have h := aeval_derivative_mem_differentIdeal ℤ ℚ L α htop
    rwa [hder] at h
  have hnot : 2 * α ∉ 𝔮.asIdeal := by
    intro hmem
    have heq : 2 * α * (2 * α) = ((4 * d : ℤ) : 𝓞 L) := by
      push_cast
      rw [← hsq]
      ring
    have h4 : ((4 * d : ℤ) : 𝓞 L) ∈ 𝔮.asIdeal := by
      rw [← heq]
      exact 𝔮.asIdeal.mul_mem_left _ hmem
    have h4' : (ℓ : ℤ) ∣ 2 * (2 * d) := by
      have h := (hm (4 * d)).mp h4
      rwa [show (4 : ℤ) * d = 2 * (2 * d) by ring] at h
    rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h4' with h2 | h2
    · exact h2d (h2.mul_right d)
    · exact h2d h2
  have hndvd : ¬ 𝔮.asIdeal ∣ differentIdeal ℤ (𝓞 L) := fun h => hnot (Ideal.dvd_iff_le.mp h hdiff)
  haveI : Algebra.IsUnramifiedAt ℤ 𝔮.asIdeal := not_dvd_differentIdeal_iff.mp hndvd
  haveI : 𝔮.asIdeal.LiesOver (𝔮.asIdeal.under ℤ) := ⟨rfl⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (fun h => 𝔮.ne_bot (Ideal.eq_bot_of_comap_eq_bot h))]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (p := 𝔮.asIdeal)

private theorem ramificationIdx_eq_ramificationIdx_under_int (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal) (𝔮 : HeightOneSpectrum (𝓞 L))
    (h𝔮 : 𝔮.under (𝓞 ℚ) = p) :
    p.asIdeal.ramificationIdx' 𝔮.asIdeal = Ideal.ramificationIdx' (𝔮.asIdeal.under ℤ) 𝔮.asIdeal := by
  have hm := intCast_mem_asIdeal_iff_dvd_of_under_eq L ℓ hℓ p hp 𝔮 h𝔮
  have hcomap : p.asIdeal = Ideal.under (𝓞 ℚ) 𝔮.asIdeal :=
    (congrArg HeightOneSpectrum.asIdeal h𝔮).symm.trans (HeightOneSpectrum.under_asIdeal (𝓞 ℚ) 𝔮)
  have hpk : ∀ k : ℤ, (k : 𝓞 ℚ) ∈ p.asIdeal ↔ (ℓ : ℤ) ∣ k := by
    intro k
    rw [← hm k, hcomap]
    exact Ideal.mem_comap.trans (by rw [map_intCast])
  have hu : Ideal.under ℤ 𝔮.asIdeal = Ideal.span {(ℓ : ℤ)} := by
    ext k
    rw [Ideal.mem_span_singleton, ← hm k]
    exact Ideal.mem_comap.trans (by rw [eq_intCast])
  have hp0 : p.asIdeal = Ideal.span {((ℓ : ℤ) : 𝓞 ℚ)} := by
    ext z
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : 𝓞 ℚ) = z :=
      ⟨Rat.ringOfIntegersEquiv z, (eq_intCast Rat.ringOfIntegersEquiv.symm _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply z)⟩
    rw [Ideal.mem_span_singleton, hpk k]
    constructor
    · intro h
      simpa using map_dvd (Int.castRingHom (𝓞 ℚ)) h
    · intro h
      simpa using map_dvd Rat.ringOfIntegersEquiv h
  have h1 : Ideal.map (algebraMap (𝓞 ℚ) (𝓞 L)) p.asIdeal = Ideal.span {((ℓ : ℤ) : 𝓞 L)} := by
    rw [hp0, Ideal.map_span]
    simp
  have h2 : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.under ℤ 𝔮.asIdeal) =
      Ideal.span {((ℓ : ℤ) : 𝓞 L)} := by
    rw [hu, Ideal.map_span]
    simp
  simp only [Ideal.ramificationIdx', h1, h2]

private theorem two_mul_mul_mem_adjoin_of_sq_eq_intCast (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ) (hα : (α : L) ∉ Set.range (algebraMap ℚ L))
    (hsq : α ^ 2 = (d : 𝓞 L)) (β : 𝓞 L) :
    2 * α * β ∈ Algebra.adjoin ℤ {α} := by
  have htop : Algebra.adjoin ℚ {(α : L)} = ⊤ :=
    adjoin_singleton_eq_top_of_not_mem_range L hL (α : L) hα
  have hmp : minpoly ℤ α = Polynomial.X ^ 2 - Polynomial.C d :=
    minpoly_int_eq_X_sq_sub_C_of_sq_eq_intCast L hL α d hα hsq
  have hder : Polynomial.aeval α (Polynomial.derivative (minpoly ℤ α)) = 2 * α := by
    rw [hmp]
    simp [map_ofNat]
  have hprod := conductor_mul_differentIdeal ℤ ℚ L α htop
  rw [hder] at hprod
  have hmem : 2 * α ∈ conductor ℤ α * differentIdeal ℤ (𝓞 L) := by
    rw [hprod]
    exact Ideal.mem_span_singleton_self (2 * α)
  exact (mem_conductor_iff.mp (Ideal.mul_le_left hmem)) β

private theorem inertiaDeg_criterion_of_sq_eq_intCast (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ)
    (hα : (α : L) ∉ Set.range (algebraMap ℚ L)) (hsq : α ^ 2 = (d : 𝓞 L)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h2d : ¬ (ℓ : ℤ) ∣ 2 * d) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : 𝔮.under (𝓞 ℚ) = p) :
    (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → ∃ n : ℤ, α - (n : 𝓞 L) ∈ 𝔮.asIdeal) ∧
      ((∃ n : ℤ, α - (n : 𝓞 L) ∈ 𝔮.asIdeal) → p.asIdeal.inertiaDeg' 𝔮.asIdeal ≤ 1) := by
  have hm := intCast_mem_asIdeal_iff_dvd_of_under_eq L ℓ hℓ p hp 𝔮 h𝔮
  have hcomap : p.asIdeal = Ideal.under (𝓞 ℚ) 𝔮.asIdeal :=
    (congrArg HeightOneSpectrum.asIdeal h𝔮).symm.trans (HeightOneSpectrum.under_asIdeal (𝓞 ℚ) 𝔮)
  haveI : 𝔮.asIdeal.LiesOver p.asIdeal := ⟨hcomap⟩
  letI := Ideal.Quotient.field p.asIdeal
  letI := Ideal.Quotient.field 𝔮.asIdeal
  rw [Ideal.inertiaDeg_algebraMap]
  constructor
  ·
    intro hf
    obtain ⟨c, hc1⟩ := (finrank_eq_one_iff_of_nonzero' (1 : 𝓞 L ⧸ 𝔮.asIdeal) one_ne_zero).mp hf
      (Ideal.Quotient.mk 𝔮.asIdeal α)
    obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨n, rfl⟩ : ∃ k : ℤ, (k : 𝓞 ℚ) = c₀ :=
      ⟨Rat.ringOfIntegersEquiv c₀, (eq_intCast Rat.ringOfIntegersEquiv.symm _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply c₀)⟩
    refine ⟨n, Ideal.Quotient.eq.mp ?_⟩
    rw [← hc1]
    simp only [Algebra.smul_def, mul_one, map_intCast]
  ·

    rintro ⟨n, hn⟩
    have hℓn : ¬ (ℓ : ℤ) ∣ 2 * n := by
      intro h
      rcases (Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd h with h2 | hn'
      · exact h2d (Dvd.dvd.mul_right h2 d)
      · apply h2d
        refine Dvd.dvd.mul_left ((hm d).mp ?_) 2
        have hαmem : α ∈ 𝔮.asIdeal := by
          have h' := 𝔮.asIdeal.add_mem hn ((hm n).mpr hn')
          rwa [sub_add_cancel] at h'
        have h' := 𝔮.asIdeal.mul_mem_left α hαmem
        rwa [← sq, hsq] at h'
    have hcop : IsCoprime (ℓ : ℤ) (2 * n) :=
      (Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd.mpr hℓn
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : (a : 𝓞 L) * (ℓ : 𝓞 L) + (b : 𝓞 L) * (2 * (n : 𝓞 L)) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 L) hab
    have hℓmem : (ℓ : 𝓞 L) ∈ 𝔮.asIdeal := by
      have h' := (hm ℓ).mpr dvd_rfl
      exact_mod_cast h'
    have hcong : ∀ β : 𝓞 L, ∃ j : ℤ, β - (j : 𝓞 L) ∈ 𝔮.asIdeal := by
      intro β
      have hβ := two_mul_mul_mem_adjoin_of_sq_eq_intCast L hL α d hα hsq β
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hβ
      obtain ⟨q, hq⟩ := (AlgHom.mem_range _).mp hβ
      have hq' : (q.map (Int.castRingHom (𝓞 L))).eval α = 2 * α * β := by
        rw [← hq, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq]
      obtain ⟨M, hM⟩ : ∃ M : ℤ, (q.map (Int.castRingHom (𝓞 L))).eval (n : 𝓞 L) = (M : 𝓞 L) :=
        ⟨_, by rw [Polynomial.eval_intCast_map, eq_intCast]⟩
      have hX : 2 * α * β - (M : 𝓞 L) ∈ 𝔮.asIdeal := by
        rw [← hM, ← hq']
        obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub α (n : 𝓞 L) (q.map (Int.castRingHom (𝓞 L)))
        rw [ht]
        exact 𝔮.asIdeal.mul_mem_right t hn
      refine ⟨b * M, ?_⟩
      have hkey : β - ((b * M : ℤ) : 𝓞 L) =
          (b : 𝓞 L) * ((2 * α * β - (M : 𝓞 L)) - 2 * β * (α - (n : 𝓞 L))) + (a : 𝓞 L) * (ℓ : 𝓞 L) * β := by
        push_cast
        linear_combination (-β) * h1
      rw [hkey]
      exact 𝔮.asIdeal.add_mem
        (𝔮.asIdeal.mul_mem_left _ (𝔮.asIdeal.sub_mem hX (𝔮.asIdeal.mul_mem_left _ hn)))
        (𝔮.asIdeal.mul_mem_right _ (𝔮.asIdeal.mul_mem_left _ hℓmem))
    refine finrank_le_one (1 : 𝓞 L ⧸ 𝔮.asIdeal) fun w => ?_
    obtain ⟨β, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, hj⟩ := hcong β
    refine ⟨(j : 𝓞 ℚ ⧸ p.asIdeal), ?_⟩
    rw [Algebra.smul_def, mul_one, map_intCast]
    exact ((Ideal.Quotient.eq.mpr hj).trans (map_intCast (Ideal.Quotient.mk 𝔮.asIdeal) j)).symm

private theorem jacobiSym_eq_one_of_inertiaDeg_eq_one (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ)
    (hα : (α : L) ∉ Set.range (algebraMap ℚ L)) (hsq : α ^ 2 = (d : 𝓞 L)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h2d : ¬ (ℓ : ℤ) ∣ 2 * d) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : 𝔮.under (𝓞 ℚ) = p) :
    p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → jacobiSym d ℓ = 1 := by
  intro hf
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hm := intCast_mem_asIdeal_iff_dvd_of_under_eq L ℓ hℓ p hp 𝔮 h𝔮
  obtain ⟨n, hn⟩ := (inertiaDeg_criterion_of_sq_eq_intCast L hL α d hα hsq ℓ hℓ h2d p hp 𝔮 h𝔮).1 hf

  have hdvd : (ℓ : ℤ) ∣ d - n ^ 2 := by
    refine (hm (d - n ^ 2)).mp ?_
    have h' := 𝔮.asIdeal.mul_mem_right (α + (n : 𝓞 L)) hn
    have heq : (α - (n : 𝓞 L)) * (α + (n : 𝓞 L)) = ((d - n ^ 2 : ℤ) : 𝓞 L) := by
      push_cast
      linear_combination hsq
    rwa [heq] at h'
  have hd0 : (d : ZMod ℓ) ≠ 0 := fun h =>
    h2d (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd d ℓ).mp h) 2)
  have hsqr : IsSquare (d : ZMod ℓ) := by
    refine ⟨(n : ZMod ℓ), ?_⟩
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (d - n ^ 2) ℓ).mpr hdvd
    push_cast at h'
    linear_combination h'
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact (legendreSym.eq_one_iff ℓ hd0).mpr hsqr

private theorem jacobiSym_eq_neg_one_of_inertiaDeg_eq_two (L : Type) [Field L] [NumberField L]
    [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)] (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ)
    (hα : (α : L) ∉ Set.range (algebraMap ℚ L)) (hsq : α ^ 2 = (d : 𝓞 L)) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (h2d : ¬ (ℓ : ℤ) ∣ 2 * d) (p : HeightOneSpectrum (𝓞 ℚ)) (hp : (ℓ : 𝓞 ℚ) ∈ p.asIdeal)
    (𝔮 : HeightOneSpectrum (𝓞 L)) (h𝔮 : 𝔮.under (𝓞 ℚ) = p) :
    p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 → jacobiSym d ℓ = -1 := by
  intro hf
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hm := intCast_mem_asIdeal_iff_dvd_of_under_eq L ℓ hℓ p hp 𝔮 h𝔮
  have hcrit := (inertiaDeg_criterion_of_sq_eq_intCast L hL α d hα hsq ℓ hℓ h2d p hp 𝔮 h𝔮).2
  have hd0 : (d : ZMod ℓ) ≠ 0 := fun h =>
    h2d (Dvd.dvd.mul_left ((ZMod.intCast_zmod_eq_zero_iff_dvd d ℓ).mp h) 2)
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  refine (legendreSym.eq_one_or_neg_one ℓ hd0).resolve_left fun h1 => ?_

  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff ℓ hd0).mp h1
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (c : ZMod ℓ) = r := ⟨ZMod.cast r, ZMod.intCast_zmod_cast r⟩
  have hdvd : (ℓ : ℤ) ∣ d - c ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hr - ((c : ZMod ℓ) + r) * hc
  have hmem : (α - (c : 𝓞 L)) * (α + (c : 𝓞 L)) ∈ 𝔮.asIdeal := by
    have heq : (α - (c : 𝓞 L)) * (α + (c : 𝓞 L)) = ((d - c ^ 2 : ℤ) : 𝓞 L) := by
      push_cast
      linear_combination hsq
    rw [heq]
    exact (hm _).mpr hdvd
  have hle : p.asIdeal.inertiaDeg' 𝔮.asIdeal ≤ 1 := by
    refine hcrit ?_
    rcases 𝔮.isPrime.mem_or_mem hmem with h | h
    · exact ⟨c, h⟩
    · refine ⟨-c, ?_⟩
      rw [Int.cast_neg, sub_neg_eq_add]
      exact h
  omega

private theorem neg_iff_nrComplexPlaces_ne_zero_of_sq_eq_intCast (L : Type) [Field L] [NumberField L]
    (hL : Module.finrank ℚ L = 2) (α : 𝓞 L) (d : ℤ) (hd : d ≠ 0) (hα : (α : L) ∉ Set.range (algebraMap ℚ L))
    (hsq : α ^ 2 = (d : 𝓞 L)) :
    d < 0 ↔ InfinitePlace.nrComplexPlaces L ≠ 0 := by
  have hx2 : (α : L) ^ 2 = (d : L) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_pow, hsq, map_intCast]
  constructor
  · intro hneg h0
    haveI := NumberField.nrComplexPlaces_eq_zero_iff.mp h0
    obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace L) := inferInstance
    have hψ : (NumberField.InfinitePlace.embedding_of_isReal (NumberField.IsTotallyReal.isReal w) (α : L)) ^ 2 =
        (d : ℝ) := by
      rw [← map_pow, hx2, map_intCast]
    have h0d : (0 : ℝ) ≤ d := by
      rw [← hψ]
      exact sq_nonneg _
    have h0d' : (0 : ℤ) ≤ d := by exact_mod_cast h0d
    omega
  · intro hc
    by_contra hneg
    have hpos : 0 < d := by omega
    have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast hpos.le
    have hgen : Algebra.adjoin ℚ {(α : L)} = ⊤ := adjoin_singleton_eq_top_of_not_mem_range L hL (α : L) hα
    have key : ∀ (φ : L →+* ℂ) (y : L), starRingEnd ℂ (φ y) = φ y := by
      intro φ y
      have hφ2 : (φ (α : L)) ^ 2 = ((Real.sqrt d : ℝ) : ℂ) ^ 2 := by
        rw [← map_pow, hx2, map_intCast, ← Complex.ofReal_pow, Real.sq_sqrt hd0, Complex.ofReal_intCast]
      have hreal : starRingEnd ℂ (φ (α : L)) = φ (α : L) := by
        rcases eq_or_eq_neg_of_sq_eq_sq _ _ hφ2 with h | h
        · rw [h, Complex.conj_ofReal]
        · rw [h, map_neg, Complex.conj_ofReal]
      have hy : y ∈ Algebra.adjoin ℚ {(α : L)} := by
        rw [hgen]
        exact Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).mp hy
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.hom_eval₂, hreal,
        RingHom.ext_rat ((starRingEnd ℂ).comp (φ.comp (algebraMap ℚ L))) (φ.comp (algebraMap ℚ L))]
    have htr : NumberField.IsTotallyReal L := ⟨fun w =>
      NumberField.InfinitePlace.isReal_iff.mpr (NumberField.ComplexEmbedding.isReal_iff.mpr
        (RingHom.ext fun y => by
          rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
          exact key _ y))⟩
    exact hc (NumberField.nrComplexPlaces_eq_zero_iff.mpr htr)

end QuadraticSplitting

open QuadraticSplitting in

theorem solution
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (hL : Module.finrank ℚ L = 2) :
    ∃ d : ℤ, d ≠ 0 ∧ (d < 0 ↔ InfinitePlace.nrComplexPlaces L ≠ 0) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ (ℓ : ℤ) ∣ 2 * d →
        ∀ (p : HeightOneSpectrum (𝓞 ℚ)), (ℓ : 𝓞 ℚ) ∈ p.asIdeal →
          ∀ (𝔮 : HeightOneSpectrum (𝓞 L)), 𝔮.under (𝓞 ℚ) = p →
            p.asIdeal.ramificationIdx' 𝔮.asIdeal = 1 ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 1 → jacobiSym d ℓ = 1) ∧
              (p.asIdeal.inertiaDeg' 𝔮.asIdeal = 2 → jacobiSym d ℓ = -1) := by
  obtain ⟨α, d, hd, hα, hsq⟩ := exists_sqrt_generator_of_finrank_eq_two L hL
  refine ⟨d, hd, neg_iff_nrComplexPlaces_ne_zero_of_sq_eq_intCast L hL α d hd hα hsq, ?_⟩
  intro ℓ hℓ h2d p hp 𝔮 h𝔮
  exact ⟨(ramificationIdx_eq_ramificationIdx_under_int L ℓ hℓ p hp 𝔮 h𝔮).trans
      (ramificationIdx_under_int_eq_one_of_sq_eq_intCast L hL α d hα hsq ℓ hℓ h2d p hp 𝔮 h𝔮),
    jacobiSym_eq_one_of_inertiaDeg_eq_one L hL α d hα hsq ℓ hℓ h2d p hp 𝔮 h𝔮,
    jacobiSym_eq_neg_one_of_inertiaDeg_eq_two L hL α d hα hsq ℓ hℓ h2d p hp 𝔮 h𝔮⟩

end S_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_CubicLambda_exists_int_jacobiSym_eq_of_finrank_eq_two (solution)
