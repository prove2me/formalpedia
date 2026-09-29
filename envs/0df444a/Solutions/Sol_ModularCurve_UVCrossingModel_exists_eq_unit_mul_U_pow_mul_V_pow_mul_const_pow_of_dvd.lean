-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e935de39-5cc0-5c42-b18a-65d64f87de4c

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd

set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial in

noncomputable abbrev CLQ {D : Type*} [CommRing D] (c : D) : Polynomial (PowerSeries D) :=
  X ^ 2 - C (PowerSeries.X : PowerSeries D) * X + C (PowerSeries.C c)

namespace CLQ

variable {D : Type*} [CommRing D]

open Polynomial in
theorem natDegree_eq [Nontrivial D] (c : D) : (CLQ c).natDegree = 2 := by
  unfold CLQ; compute_degree!

open Polynomial in
theorem monic [Nontrivial D] (c : D) : (CLQ c).Monic := by
  unfold CLQ; monicity!

noncomputable abbrev A (c : D) := AdjoinRoot (CLQ c)
noncomputable abbrev α (c : D) : A c := AdjoinRoot.root (CLQ c)
noncomputable abbrev ι (c : D) : PowerSeries D →+* A c := AdjoinRoot.of (CLQ c)

theorem aeval_CLQ (c : D) {S : Type*} [CommRing S] [Algebra (PowerSeries D) S] (x : S) :
    Polynomial.aeval x (CLQ c) = x ^ 2 - algebraMap (PowerSeries D) S PowerSeries.X * x +
      algebraMap (PowerSeries D) S (PowerSeries.C c) := by
  simp [CLQ, map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]

theorem α_rel (c : D) : α c ^ 2 - ι c PowerSeries.X * α c + ι c (PowerSeries.C c) = 0 := by
  have h := AdjoinRoot.aeval_eq (f := CLQ c) (CLQ c)
  rw [AdjoinRoot.mk_self, aeval_CLQ, AdjoinRoot.algebraMap_eq] at h
  exact h

theorem α_sq (c : D) : α c ^ 2 = ι c PowerSeries.X * α c - ι c (PowerSeries.C c) := by
  have := α_rel c; linear_combination this

theorem α_mul_conj (c : D) : α c * (ι c PowerSeries.X - α c) = ι c (PowerSeries.C c) := by
  have := α_rel c; linear_combination -this

theorem eval₂_CLQ (c : D) {S : Type*} [CommRing S] (i : PowerSeries D →+* S) (x : S) :
    Polynomial.eval₂ i x (CLQ c) = x ^ 2 - i PowerSeries.X * x + i (PowerSeries.C c) := by
  simp [CLQ, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]

noncomputable def σ (c : D) : A c →+* A c :=
  AdjoinRoot.lift (ι c) (ι c PowerSeries.X - α c) (by
    rw [eval₂_CLQ]
    have := α_rel c
    linear_combination this)

theorem σ_α (c : D) : σ c (α c) = ι c PowerSeries.X - α c := by
  unfold σ; exact AdjoinRoot.lift_root _

theorem σ_ι (c : D) (b : PowerSeries D) : σ c (ι c b) = ι c b := by
  unfold σ; exact AdjoinRoot.lift_of _

theorem σ_conj (c : D) : σ c (ι c PowerSeries.X - α c) = α c := by
  rw [map_sub, σ_ι, σ_α]; ring

theorem exists_coords [Nontrivial D] (c : D) (r : A c) :
    ∃ p q : PowerSeries D, r = ι c p + ι c q * α c := by
  induction r using AdjoinRoot.induction_on with
  | ih g =>
    have hm := monic c
    set g' := g %ₘ CLQ c with hg'
    have hdeg : g'.natDegree ≤ 1 := by
      have := Polynomial.natDegree_modByMonic_lt g hm (by
        intro h1; have := congrArg Polynomial.natDegree h1; rw [natDegree_eq] at this; simp at this)
      rw [natDegree_eq] at this; rw [hg']; omega
    have hgg : AdjoinRoot.mk (CLQ c) g = AdjoinRoot.mk (CLQ c) g' := by
      rw [AdjoinRoot.mk_eq_mk, hg']
      refine ⟨g /ₘ CLQ c, ?_⟩
      have := Polynomial.modByMonic_add_div g (CLQ c)
      linear_combination -this
    refine ⟨g'.coeff 0, g'.coeff 1, ?_⟩
    rw [hgg]
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    ring

noncomputable def nf (c : D) (p q : PowerSeries D) : PowerSeries D :=
  p ^ 2 + PowerSeries.X * p * q + PowerSeries.C c * q ^ 2

theorem mul_σ (c : D) (p q : PowerSeries D) :
    (ι c p + ι c q * α c) * σ c (ι c p + ι c q * α c) = ι c (nf c p q) := by
  rw [map_add, map_mul, σ_ι, σ_ι, σ_α, nf, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_pow]
  have h := α_mul_conj c
  linear_combination (ι c q) ^ 2 * h

theorem isUnit_of_nf (c : D) (p q : PowerSeries D) (h : IsUnit (nf c p q)) :
    IsUnit (ι c p + ι c q * α c) :=
  isUnit_of_mul_isUnit_left (by rw [mul_σ]; exact h.map _)

end CLQ

namespace CLQ

variable {D : Type*} [CommRing D]

noncomputable abbrev bar (ϖ : D) : PowerSeries D →+* PowerSeries (D ⧸ Ideal.span {ϖ}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))

theorem bar_C (ϖ : D) : bar ϖ (PowerSeries.C ϖ) = 0 := by
  rw [PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]

theorem bar_C_pow (ϖ : D) {e : ℕ} (he : 1 ≤ e) : bar ϖ (PowerSeries.C (ϖ ^ e)) = 0 := by
  rw [map_pow, map_pow, bar_C, zero_pow (by omega)]

theorem bar_X (ϖ : D) : bar ϖ PowerSeries.X = PowerSeries.X := PowerSeries.map_X _

theorem bar_eq_zero_iff (ϖ : D) (p : PowerSeries D) : bar ϖ p = 0 ↔ PowerSeries.C ϖ ∣ p := by
  constructor
  · intro h
    have hc : ∀ n, ∃ d, PowerSeries.coeff n p = ϖ * d := fun n => by
      have := congrArg (PowerSeries.coeff n) h
      rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
      exact this
    choose d hd using hc
    refine ⟨PowerSeries.mk d, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hd]
  · rintro ⟨t, rfl⟩
    rw [map_mul, bar_C, zero_mul]

theorem prime_C [IsDomain D] {ϖ : D} (hϖ : Prime ϖ) : Prime (PowerSeries.C ϖ : PowerSeries D) := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  haveI : IsDomain (D ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hϖ.ne_zero (by simpa using congrArg PowerSeries.constantCoeff h)
  · intro h
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at h
    exact hϖ.not_unit h
  · intro a b hab
    rw [← bar_eq_zero_iff, ← bar_eq_zero_iff]
    rw [← bar_eq_zero_iff, map_mul, mul_eq_zero] at hab
    exact hab

theorem dvd_cancel_pow {B : Type*} [CommRing B] [IsDomain B] {π : B} (hπ : Prime π)
    {k M : ℕ} {x : B} (h : π ^ k * x ∣ π ^ M) : k ≤ M ∧ x ∣ π ^ (M - k) := by
  induction k generalizing M with
  | zero => simpa using h
  | succ k ih =>
    cases M with
    | zero =>
      exfalso
      rw [pow_zero] at h
      exact hπ.not_unit (isUnit_of_dvd_one (dvd_trans (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) x) h))
    | succ M =>
      rw [pow_succ, pow_succ, mul_assoc, mul_comm π x, ← mul_assoc] at h
      have h' := (mul_dvd_mul_iff_right hπ.ne_zero).mp h
      obtain ⟨h1, h2⟩ := ih h'
      refine ⟨by omega, ?_⟩
      rwa [Nat.succ_sub_succ]

end CLQ

namespace CLQ

variable {D : Type*} [CommRing D] [IsDomain D] {ϖ : D}

theorem heart (hϖ : Prime ϖ) {e : ℕ} (he : 1 ≤ e) {p q : PowerSeries D} {i : ℕ}
    (hq : bar ϖ q ≠ 0) (hp : bar ϖ p = 0)
    (h1 : nf (ϖ ^ e) p q ∣ PowerSeries.C ϖ ^ i) (h2 : PowerSeries.C ϖ ^ i ∣ nf (ϖ ^ e) p q) :
    PowerSeries.C ϖ ^ e ∣ p := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  haveI : IsDomain (D ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  have hP := prime_C hϖ
  suffices H : ∀ j, j ≤ e → PowerSeries.C ϖ ^ j ∣ p from H e le_rfl
  intro j
  induction j with
  | zero => intro; exact ⟨p, by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨pj, hpj⟩ := ih (by omega)
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      rw [zero_add, pow_one, ← bar_eq_zero_iff]
      exact hp
    · set M := PowerSeries.C ϖ ^ j * pj ^ 2 + PowerSeries.X * pj * q +
        PowerSeries.C ϖ ^ (e - j) * q ^ 2 with hM
      have hnf : nf (ϖ ^ e) p q = PowerSeries.C ϖ ^ j * M := by
        rw [nf, hpj, hM, map_pow]
        have : (PowerSeries.C ϖ) ^ e = PowerSeries.C ϖ ^ j * PowerSeries.C ϖ ^ (e - j) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
      have hbarM : bar ϖ M = PowerSeries.X * bar ϖ pj * bar ϖ q := by
        rw [hM, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, bar_C,
          bar_X, zero_pow (by omega), zero_pow (by omega), zero_mul, zero_mul, zero_add, add_zero]
      by_cases hij : i ≤ j
      · exfalso
        rw [hnf] at h1
        obtain ⟨-, hM1⟩ := dvd_cancel_pow hP h1
        rw [show i - j = 0 by omega, pow_zero] at hM1
        have hu : IsUnit (bar ϖ M) := (isUnit_of_dvd_one hM1).map _
        rw [PowerSeries.isUnit_iff_constantCoeff, hbarM] at hu
        simp at hu
      · rw [hnf] at h2
        have : PowerSeries.C ϖ ^ j * PowerSeries.C ϖ ^ (i - j) ∣ PowerSeries.C ϖ ^ j * M := by
          rwa [← pow_add, show j + (i - j) = i by omega]
        have hM2 := (mul_dvd_mul_iff_left (pow_ne_zero j hP.ne_zero)).mp this
        have hM3 : PowerSeries.C ϖ ∣ M := dvd_trans (dvd_pow_self _ (by omega)) hM2
        rw [← bar_eq_zero_iff, hbarM] at hM3
        rcases mul_eq_zero.mp hM3 with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' PowerSeries.X_ne_zero
          · rw [bar_eq_zero_iff] at h'
            obtain ⟨p', hp'⟩ := h'
            exact ⟨p', by rw [hpj, hp', pow_succ]; ring⟩
        · exact absurd h hq

theorem main (hϖ : Prime ϖ) {e : ℕ} (he : 1 ≤ e) :
    ∀ (M : ℕ) (p q : PowerSeries D), nf (ϖ ^ e) p q ∣ PowerSeries.C ϖ ^ M →
      ∃ (w : (A (ϖ ^ e))ˣ) (a b n : ℕ), ι (ϖ ^ e) p + ι (ϖ ^ e) q * α (ϖ ^ e) =
        w * α (ϖ ^ e) ^ a * (ι (ϖ ^ e) PowerSeries.X - α (ϖ ^ e)) ^ b *
          ι (ϖ ^ e) (PowerSeries.C ϖ) ^ n := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  haveI : IsDomain (D ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  have hPprime := prime_C hϖ
  set c := ϖ ^ e with hc
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
  intro p q hM
  by_cases hunit : IsUnit (nf c p q)
  · exact ⟨(isUnit_of_nf c p q hunit).unit, 0, 0, 0, by simp⟩

  have stepU : ∀ p q : PowerSeries D, bar ϖ q ≠ 0 → bar ϖ p = 0 →
      nf c p q ∣ PowerSeries.C ϖ ^ M → ¬IsUnit (nf c p q) →
      ∃ (w : (A c)ˣ) (a b n : ℕ), ι c p + ι c q * α c =
        w * α c ^ a * (ι c PowerSeries.X - α c) ^ b * ι c (PowerSeries.C ϖ) ^ n := by
    intro p q hq hp hdvd hnu
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime M).mp hdvd
    obtain ⟨p₁, hp₁⟩ := heart hϖ he hq hp hassoc.dvd hassoc.symm.dvd
    have hfac : ι c p + ι c q * α c =
        α c * (ι c (PowerSeries.X * p₁ + q) + ι c (-p₁) * α c) := by
      have key := α_mul_conj c
      rw [hp₁, ← map_pow, ← hc, map_mul, map_add, map_mul, map_neg]
      linear_combination (-(ι c p₁)) * key
    have hnf' : nf c p q = PowerSeries.C ϖ ^ e * nf c (PowerSeries.X * p₁ + q) (-p₁) := by
      simp only [nf, hp₁, hc, map_pow]; ring
    rw [hnf'] at hdvd
    obtain ⟨heM, hd'⟩ := dvd_cancel_pow hPprime hdvd
    obtain ⟨w, a, b, n, hw⟩ := IH (M - e) (by omega) _ _ hd'
    exact ⟨w, a + 1, b, n, by rw [hfac, hw]; ring⟩
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime M).mp hM
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hassoc
    exact hunit (associated_one_iff_isUnit.mp hassoc)
  have hdvdnf : PowerSeries.C ϖ ∣ nf c p q := dvd_trans (dvd_pow_self _ hi0) hassoc.symm.dvd
  have hbar : bar ϖ p * (bar ϖ p + PowerSeries.X * bar ϖ q) = 0 := by
    rw [← bar_eq_zero_iff] at hdvdnf
    have hexp : bar ϖ (nf c p q) = bar ϖ p * (bar ϖ p + PowerSeries.X * bar ϖ q) := by
      rw [nf, hc]
      simp only [map_add, map_mul, map_pow, bar_C, bar_X, zero_pow (Nat.one_le_iff_ne_zero.mp he),
        zero_mul, add_zero]
      ring
    rw [← hexp]; exact hdvdnf
  by_cases hq : bar ϖ q = 0
  · by_cases hp : bar ϖ p = 0
    · rw [bar_eq_zero_iff] at hp hq
      obtain ⟨p₁, rfl⟩ := hp
      obtain ⟨q₁, rfl⟩ := hq
      have hnf2 : nf c (PowerSeries.C ϖ * p₁) (PowerSeries.C ϖ * q₁) =
          PowerSeries.C ϖ ^ 2 * nf c p₁ q₁ := by
        simp only [nf]; ring
      rw [hnf2] at hM
      obtain ⟨h2M, hd'⟩ := dvd_cancel_pow hPprime hM
      obtain ⟨w, a, b, n, hw⟩ := IH (M - 2) (by omega) p₁ q₁ hd'
      refine ⟨w, a, b, n + 1, ?_⟩
      rw [map_mul, map_mul, show ι c (PowerSeries.C ϖ) * ι c p₁ + ι c (PowerSeries.C ϖ) * ι c q₁ * α c =
        ι c (PowerSeries.C ϖ) * (ι c p₁ + ι c q₁ * α c) by ring, hw]
      ring
    · exfalso
      rw [hq, mul_zero, add_zero] at hbar
      exact hp (mul_self_eq_zero.mp hbar)
  · rcases mul_eq_zero.mp hbar with hp | hp
    · exact stepU p q hq hp hM hunit
    · set p' := p + PowerSeries.X * q with hp'
      set q' := -q with hq'
      have hq'0 : bar ϖ q' ≠ 0 := by rw [hq', map_neg, neg_ne_zero]; exact hq
      have hp'0 : bar ϖ p' = 0 := by rw [hp', map_add, map_mul, bar_X]; exact hp
      have hnfeq : nf c p' q' = nf c p q := by simp only [nf, hp', hq']; ring
      have hnu' : ¬IsUnit (nf c p' q') := by rwa [hnfeq]
      have hM' : nf c p' q' ∣ PowerSeries.C ϖ ^ M := by rwa [hnfeq]
      obtain ⟨w, a, b, n, hw⟩ := stepU p' q' hq'0 hp'0 hM' hnu'
      have hr : ι c p + ι c q * α c = σ c (ι c p' + ι c q' * α c) := by
        rw [map_add, map_mul, σ_ι, σ_ι, σ_α, hp', hq', map_add, map_mul, map_neg]; ring
      refine ⟨Units.map (σ c).toMonoidHom w, b, a, n, ?_⟩
      rw [hr, hw, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, σ_α, σ_conj, σ_ι]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      ring

theorem final (hϖ : Prime ϖ) {e : ℕ} (he : 1 ≤ e) {r : A (ϖ ^ e)} {m : ℕ}
    (hr : r ∣ ι (ϖ ^ e) (PowerSeries.C ϖ) ^ m) :
    ∃ (w : (A (ϖ ^ e))ˣ) (a b n : ℕ),
      r = w * α (ϖ ^ e) ^ a * (ι (ϖ ^ e) PowerSeries.X - α (ϖ ^ e)) ^ b *
        ι (ϖ ^ e) (PowerSeries.C ϖ) ^ n := by
  obtain ⟨t, ht⟩ := hr
  obtain ⟨p, q, hpq⟩ := exists_coords (ϖ ^ e) r
  obtain ⟨p', q', hpq'⟩ := exists_coords (ϖ ^ e) t
  have key : ι (ϖ ^ e) (nf (ϖ ^ e) p q * nf (ϖ ^ e) p' q') =
      ι (ϖ ^ e) (PowerSeries.C ϖ ^ (2 * m)) := by
    calc ι (ϖ ^ e) (nf (ϖ ^ e) p q * nf (ϖ ^ e) p' q')
        = (r * σ (ϖ ^ e) r) * (t * σ (ϖ ^ e) t) := by rw [map_mul, hpq, hpq', mul_σ, mul_σ]
      _ = (r * t) * σ (ϖ ^ e) (r * t) := by rw [map_mul]; ring
      _ = ι (ϖ ^ e) (PowerSeries.C ϖ) ^ m * σ (ϖ ^ e) (ι (ϖ ^ e) (PowerSeries.C ϖ) ^ m) := by rw [← ht]
      _ = ι (ϖ ^ e) (PowerSeries.C ϖ ^ (2 * m)) := by rw [map_pow, σ_ι, map_pow, ← pow_add, two_mul]
  have hinj : Function.Injective (ι (ϖ ^ e)) := by
    refine AdjoinRoot.of.injective_of_degree_ne_zero ?_
    rw [Polynomial.degree_eq_natDegree (monic (ϖ ^ e)).ne_zero, natDegree_eq]
    norm_num
  rw [hpq]
  exact main hϖ he (2 * m) p q ⟨_, (hinj key).symm⟩

end CLQ

namespace PowerSeries p2m_export "PowerSeries" "constantCoeff_C subst monomial coeff_mk mk aeval eval₂_X eval₂ map_X constantCoeff coeff_C_mul eval₂_C coeff_map isUnit_iff_constantCoeff ext map_C map C coeff X X_ne_zero algebraMap_eq quotient_span_X_sub_C_pow_of_irreducible" end PowerSeries
p2m_open_scoped "PowerSeries" in
theorem PowerSeries.exists_eq_unit_mul_root_pow_of_dvd_C_pow_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
    {D : Type*} [CommRing D] [IsDomain D] {ϖ : D} (hϖ : Prime ϖ) {e : ℕ} (he : 1 ≤ e)
    {f : Polynomial (PowerSeries D)}
    (hf : f = Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)))
    {r : AdjoinRoot f} {m : ℕ} (hr : r ∣ AdjoinRoot.of f (PowerSeries.C ϖ) ^ m) :
    ∃ (w : (AdjoinRoot f)ˣ) (a b n : ℕ),
      r = w * AdjoinRoot.root f ^ a * (AdjoinRoot.of f PowerSeries.X - AdjoinRoot.root f) ^ b *
        AdjoinRoot.of f (PowerSeries.C ϖ) ^ n := by
  subst hf
  exact CLQ.final hϖ he hr

namespace CLQ

theorem normalise {M : Type*} [CommRing M] {U V P : M} {e : ℕ} (hUV : U * V = P ^ e) (a b n : ℕ) :
    ∃ a' b' n' : ℕ, (a' = 0 ∨ b' = 0) ∧ U ^ a * V ^ b * P ^ n = U ^ a' * V ^ b' * P ^ n' := by
  rcases le_total a b with hab | hab
  · refine ⟨0, b - a, n + e * a, Or.inl rfl, ?_⟩
    have hb : V ^ b = V ^ a * V ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
    rw [hb, pow_zero, one_mul, pow_add, pow_mul, ← hUV, mul_pow]; ring
  · refine ⟨a - b, 0, n + e * b, Or.inr rfl, ?_⟩
    have ha : U ^ a = U ^ b * U ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hab]
    rw [ha, pow_zero, mul_one, pow_add, pow_mul, ← hUV, mul_pow]; ring

theorem transport {R A : Type*} [CommRing R] [CommRing A] (eqv : R ≃+* A)
    (U S V P : R) (root sX ofP : A) (hSUV : S = U + V)
    (hU : eqv U = root) (hS : eqv S = sX) (hP : eqv P = ofP) {e : ℕ} (hUV : U * V = P ^ e)
    (core : ∀ (x : A) (m : ℕ), x ∣ ofP ^ m →
      ∃ (w : Aˣ) (a b n : ℕ), x = w * root ^ a * (sX - root) ^ b * ofP ^ n)
    {r : R} {m : ℕ} (hr : r ∣ P ^ m) :
    ∃ (w : Rˣ) (a b n : ℕ), (a = 0 ∨ b = 0) ∧ r = w * U ^ a * V ^ b * P ^ n := by
  have hV : eqv V = sX - root := by
    rw [← hS, ← hU, ← map_sub, hSUV, add_sub_cancel_left]
  have hr' : eqv r ∣ ofP ^ m := by
    have := map_dvd eqv hr
    rwa [map_pow, hP] at this
  obtain ⟨w, a, b, n, hw⟩ := core (eqv r) m hr'
  have hw' : eqv ((Units.map eqv.symm.toRingHom.toMonoidHom w : Rˣ) : R) = w := by simp
  have hr2 : r = (Units.map eqv.symm.toRingHom.toMonoidHom w : Rˣ) * U ^ a * V ^ b * P ^ n := by
    apply eqv.injective
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hU, hV, hP, hw']
    exact hw
  obtain ⟨a', b', n', hab, heq⟩ := normalise hUV a b n
  refine ⟨Units.map eqv.symm.toRingHom.toMonoidHom w, a', b', n', hab, ?_⟩
  rw [hr2, mul_assoc, mul_assoc, ← mul_assoc (U ^ a), heq]
  ring

end CLQ

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    {r : UVCrossingModel W (ϖ ^ e)} {m : ℕ} (hr : r ∣ const (ϖ ^ e) ϖ ^ m) :
    ∃ (w : (UVCrossingModel W (ϖ ^ e))ˣ) (a b n : ℕ), (a = 0 ∨ b = 0) ∧
      r = w * U (ϖ ^ e) ^ a * V (ϖ ^ e) ^ b * const (ϖ ^ e) ϖ ^ n := by
  obtain ⟨hIprime, hPID, -, hirr⟩ := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ e he
  haveI := hIprime
  haveI : IsDomain (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) := Ideal.Quotient.isDomain _
  haveI := hPID
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hcc : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)})
      (PowerSeries.C (ϖ ^ e)) = (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) (PowerSeries.C ϖ)) ^ e := by
    rw [map_pow, map_pow]
  obtain ⟨eqv, hU, hS, hconst⟩ := exists_ringEquiv_adjoinRoot (ϖ ^ e)
  have hUV : U (ϖ ^ e) * V (ϖ ^ e) = const (ϖ ^ e) ϖ ^ e := by
    show mk (ϖ ^ e) _ * mk (ϖ ^ e) _ = mk (ϖ ^ e) _ ^ e
    rw [← map_mul, ← map_pow, ← map_pow]
    refine (Ideal.Quotient.eq).2 (Ideal.subset_span ?_)
    simp
  exact CLQ.transport eqv (U (ϖ ^ e)) (S (ϖ ^ e)) (V (ϖ ^ e)) (const (ϖ ^ e) ϖ) _ _ _ (S_def _)
    hU hS (hconst ϖ) hUV
    (fun x m hx =>
      PowerSeries.exists_eq_unit_mul_root_pow_of_dvd_C_pow_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
        hprime he (by rw [hcc]) hx)
    hr

end S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_eq_unit_mul_U_pow_mul_V_pow_mul_const_pow_of_dvd (solution)
