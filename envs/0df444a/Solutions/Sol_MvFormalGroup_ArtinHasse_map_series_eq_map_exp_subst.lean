-- Prove2me | solution 1 for MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6ea41e82-832f-581b-8298-4d1673a0db14

import Mathlib
import Definitions.Def_MvFormalGroup_ArtinHasse
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

open PowerSeries ArithmeticFunction MvFormalGroup.ArtinHasse
open scoped Classical

namespace ArtinHasseIntegralSol

variable (p : ℕ) [hp : Fact p.Prime]

def IsPPow (k : ℕ) : Prop := 0 < k ∧ ∀ q ∈ k.factorization.support, q = p

scoped instance (k : ℕ) : Decidable (IsPPow p k) := by unfold IsPPow; infer_instance

theorem isPPow_iff_exists {k : ℕ} : IsPPow p k ↔ ∃ m, k = p ^ m := by
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨k.factorization p, ?_⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk.ne']
    rw [Finsupp.prod]
    have hsub : k.factorization.support ⊆ {p} := fun q hq => Finset.mem_singleton.mpr (h q hq)
    rcases Finset.subset_singleton_iff.mp hsub with h' | h'
    · rw [h', Finset.prod_empty, Finsupp.notMem_support_iff.mp (h' ▸ Finset.notMem_empty p),
        pow_zero]
    · rw [h', Finset.prod_singleton]
  · rintro ⟨m, rfl⟩
    refine ⟨pow_pos hp.out.pos m, fun q hq => ?_⟩
    have h2 : p.factorization.support = {p} := by
      rw [hp.out.factorization]; simp
    simp only [Nat.factorization_pow] at hq
    have hq' := Finset.mem_of_subset Finsupp.support_smul hq
    rw [h2] at hq'; exact Finset.mem_singleton.mp hq'

theorem isPPow_iff_ordCompl_eq_one {k : ℕ} (hk : 0 < k) :
    IsPPow p k ↔ k / p ^ (k.factorization p) = 1 := by
  rw [isPPow_iff_exists]
  constructor
  · rintro ⟨m, rfl⟩
    exact Nat.ordCompl_self_pow hp.out
  · intro h
    exact ⟨k.factorization p, by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self k p, h, mul_one]⟩

noncomputable def artinHasseArg : ℚ⟦X⟧ :=
  PowerSeries.mk fun k => if IsPPow p k then (k : ℚ)⁻¹ else 0

theorem constantCoeff_artinHasseArg : constantCoeff (artinHasseArg p) = 0 := by
  simp only [artinHasseArg, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, IsPPow,
    lt_irrefl, false_and, if_false]

noncomputable def artinHasseExpSeries : ℚ⟦X⟧ :=
  (PowerSeries.exp ℚ).subst (artinHasseArg p)

theorem hasSubst_artinHasseArg : HasSubst (artinHasseArg p) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_artinHasseArg p)

theorem hasSubst_negXpow {R : Type*} [CommRing R] {n : ℕ} (hn : n ≠ 0) :
    HasSubst (-(X : R⟦X⟧) ^ n) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])

theorem constantCoeff_subst_self' {R : Type*} [CommRing R] {g : R⟦X⟧}
    (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst g) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [show coeff 0 (g ^ n) = 0 from by
          rw [coeff_zero_eq_constantCoeff, map_pow, hg, zero_pow hn],
      smul_zero]

section Glue

variable {A : Type*} [CommRing A] [Algebra ℚ A]

scoped instance instIsAddTorsionFreeOfAlgebraRat : IsAddTorsionFree A :=
  IsAddTorsionFree.of_module_rat A

theorem constantCoeff_subst_self {g : A⟦X⟧} (hg : constantCoeff g = 0)
    (f : A⟦X⟧) : constantCoeff (f.subst g) = constantCoeff f :=
  constantCoeff_subst_self' hg f

theorem one_add_X_mul_deriv_log : (1 + X : A⟦X⟧) * d⁄dX A (log A) = 1 := by
  rw [deriv_log]
  ext n
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff]
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one,
      if_neg (Nat.succ_ne_zero _), ← RingHom.map_add,
      show ((-1 : ℚ) ^ (n + 1) + (-1) ^ n : ℚ) = 0 from by ring]
    exact RingHom.map_zero _

theorem mul_derivative_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX A (logOf f) = d⁄dX A f := by
  have hsub : HasSubst (f - 1 : A⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [logOf_eq, derivative_subst hsub, ← mul_assoc,
    show d⁄dX A (f - 1) = d⁄dX A f from by rw [map_sub]; simp]
  nth_rw 2 [← one_mul (d⁄dX A f)]
  congr 1
  have sub1 : subst (f - 1) (1 : A⟦X⟧) = 1 := by
    rw [← coe_substAlgHom hsub]; exact map_one _
  have step : subst (f - 1) ((1 + X : A⟦X⟧) * d⁄dX A (log A))
      = subst (f - 1) (1 + X : A⟦X⟧) * subst (f - 1) (d⁄dX A (log A)) :=
    subst_mul hsub (1 + X : A⟦X⟧) (d⁄dX A (log A))
  rw [one_add_X_mul_deriv_log, sub1, subst_add hsub, subst_X hsub, sub1,
    show (1 : A⟦X⟧) + (f - 1) = f from by ring] at step
  exact step.symm

theorem logOf_one : logOf (1 : A⟦X⟧) = 0 := by
  refine derivative.ext ?_ (by simp [constantCoeff_logOf (f := (1 : A⟦X⟧)) (by simp)])
  have h := mul_derivative_logOf (A := A) (f := 1) (by simp)
  simpa using h

theorem isUnit_of_constantCoeff_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, hf]; exact isUnit_one

theorem cancel_unit_left {u a b : A⟦X⟧} (hu : IsUnit u) (h : u * a = u * b) :
    a = b := by
  obtain ⟨v, rfl⟩ := hu
  have := congr_arg (fun x => (↑v⁻¹ : A⟦X⟧) * x) h
  simpa [← mul_assoc] using this

theorem logOf_mul_of_constantCoeff_one {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one hfg) ?_
    have leib : d⁄dX A (f * g) = f * d⁄dX A g + g * d⁄dX A f := by
      have := (d⁄dX A).leibniz f g
      simp only [smul_eq_mul] at this; exact this
    rw [mul_derivative_logOf hfg, map_add, mul_add,
      show f * g * d⁄dX A (logOf f) = g * (f * d⁄dX A (logOf f)) from by ring,
      show f * g * d⁄dX A (logOf g) = f * (g * d⁄dX A (logOf g)) from by ring,
      mul_derivative_logOf hf, mul_derivative_logOf hg, leib]
    ring
  · rw [map_add, constantCoeff_logOf hfg, constantCoeff_logOf hf, constantCoeff_logOf hg,
      add_zero]

theorem logOf_prod_of_constantCoeff_one {ι : Type*} (s : Finset ι) (f : ι → A⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    logOf (∏ i ∈ s, f i) = ∑ i ∈ s, logOf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      logOf_mul_of_constantCoeff_one (hf a (Finset.mem_insert_self a s))
        (by rw [map_prod]; exact Finset.prod_eq_one fun i hi =>
              hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem logOf_subst {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 0) :
    logOf (f.subst g) = (logOf f).subst g := by
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hfg : constantCoeff (f.subst g) = 1 := by
    rw [constantCoeff_subst_self hg, hf]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one hfg) ?_
    rw [mul_derivative_logOf hfg, derivative_subst hgs, derivative_subst hgs,
      ← mul_assoc, ← subst_mul hgs, mul_derivative_logOf hf]
  · rw [constantCoeff_logOf hfg, constantCoeff_subst_self hg, constantCoeff_logOf hf]

theorem logOf_exp_subst {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    logOf ((exp A).subst g) = g := by
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have heg : constantCoeff ((exp A).subst g) = 1 := by
    rw [constantCoeff_subst_self hg, constantCoeff_exp]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one heg) ?_
    rw [mul_derivative_logOf heg, derivative_subst hgs, derivative_exp]
  · rw [constantCoeff_logOf heg, hg]

variable [BinomialRing A]

theorem succ_nsmul_choose (r : A) (n : ℕ) :
    (n + 1) • Ring.choose r (n + 1) = (r - n) * Ring.choose r n := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n), ← mul_nsmul', Nat.mul_comm,
    ← Nat.factorial_succ, ← Ring.descPochhammer_eq_factorial_smul_choose,
    descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
    Polynomial.smeval_X, Polynomial.smeval_natCast, npow_one, nsmul_eq_mul,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  ring

theorem logOf_binomialSeries (r : A) :
    logOf (binomialSeries A r) = C r * PowerSeries.log A := by
  have hc : constantCoeff (binomialSeries A r) = 1 := binomialSeries_constantCoeff r
  refine derivative.ext ?_ ?_
  swap
  · rw [constantCoeff_logOf hc, ← coeff_zero_eq_constantCoeff_apply, coeff_C_mul,
      coeff_zero_eq_constantCoeff, constantCoeff_log, mul_zero]
  refine cancel_unit_left (isUnit_of_constantCoeff_one hc) ?_
  rw [mul_derivative_logOf hc]

  refine cancel_unit_left
    (isUnit_of_constantCoeff_one (f := (1 + X : A⟦X⟧)) (by simp)) ?_
  rw [show (1 + X) * (binomialSeries A r * d⁄dX A (C r * log A)) =
          binomialSeries A r * (C r * ((1 + X) * d⁄dX A (log A))) from by
        have : d⁄dX A (C r * log A) = C r * d⁄dX A (log A) := by
          have h := (d⁄dX A).leibniz (C r) (log A)
          simp only [derivative_C, smul_eq_mul, smul_zero, mul_zero, add_zero] at h
          exact h
        rw [this]; ring,
    one_add_X_mul_deriv_log, mul_one]

  ext n
  rw [show binomialSeries A r * C r = C r * binomialSeries A r from mul_comm _ _,
    coeff_C_mul]
  rcases n with _ | n
  · simp only [coeff_zero_eq_constantCoeff, map_mul, map_add, map_one, constantCoeff_X,
      add_zero, one_mul, binomialSeries_coeff, Ring.choose_zero_right, smul_eq_mul, mul_one]
    have := succ_nsmul_choose r 0
    simp only [Nat.cast_zero, sub_zero, zero_add, one_smul, Ring.choose_zero_right,
      mul_one] at this
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative, binomialSeries_coeff,
      smul_eq_mul, mul_one, this]
    ring
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_derivative, coeff_derivative]
    simp only [binomialSeries_coeff, smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    have h := succ_nsmul_choose r (n + 1)
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
    linear_combination h

theorem coeff_eq_of_forall_coeff_logOf_eq {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (k : ℕ)
    (h : ∀ j ≤ k, coeff j (logOf f) = coeff j (logOf g)) :
    coeff k f = coeff k g := by

  suffices H : ∀ j ≤ k, coeff j f = coeff j g from H k le_rfl
  induction k with
  | zero =>
    intro j hj
    interval_cases j
    simp [coeff_zero_eq_constantCoeff, hf, hg]
  | succ n ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj' | rfl
    · exact ih (fun m hm => h m (hm.trans (Nat.le_succ _))) j (Nat.lt_succ_iff.mp hj')

    have Hf := congr_arg (coeff n) (mul_derivative_logOf hf)
    have Hg := congr_arg (coeff n) (mul_derivative_logOf hg)
    rw [coeff_derivative, coeff_mul] at Hf Hg
    have sums_eq : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 f * coeff ij.2 (d⁄dX A (logOf f))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 g * coeff ij.2 (d⁄dX A (logOf g)) := by
      refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hi : i ≤ n := by omega
      have hj1 : j + 1 ≤ n + 1 := by omega
      rw [ih (fun m hm => h m (hm.trans (Nat.le_succ _))) i hi,
        coeff_derivative, coeff_derivative, h (j + 1) hj1]
    have key : coeff (n + 1) f * (↑n + 1) = coeff (n + 1) g * (↑n + 1) :=
      Hf.symm.trans (sums_eq.trans Hg)
    rw [show ((n : A) + 1) = ((n + 1 : ℕ) : A) from by push_cast; ring,
      mul_comm, mul_comm (coeff (n + 1) g), ← nsmul_eq_mul, ← nsmul_eq_mul] at key
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp key

theorem coeff_negXpow_pow {n : ℕ} (_hn : n ≠ 0) (d k : ℕ) :
    coeff k ((-(X : A⟦X⟧) ^ n) ^ d) = if k = n * d then (-1 : A) ^ d else 0 := by
  have h : (-(X : A⟦X⟧) ^ n) ^ d = (-1 : A) ^ d • (X : A⟦X⟧) ^ (n * d) := by
    rw [show (-(X : A⟦X⟧) ^ n) = (-1 : A) • (X : A⟦X⟧) ^ n from by
          rw [neg_one_smul], smul_pow, ← pow_mul]
  rw [h, map_smul, coeff_X_pow]
  split_ifs <;> simp

theorem coeff_log_subst_negXpow {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    coeff k ((log A).subst (-(X : A⟦X⟧) ^ n))
      = if n ∣ k ∧ 0 < k then algebraMap ℚ A (-((k / n : ℕ) : ℚ)⁻¹) else 0 := by
  rw [coeff_subst' (hasSubst_negXpow hn)]
  simp only [coeff_negXpow_pow hn, smul_eq_mul]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_neg (by simp), finsum_eq_zero_of_forall_eq_zero]
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [if_neg (Nat.mul_pos (Nat.pos_of_ne_zero hn) hd).ne, mul_zero]
  by_cases hdvd : n ∣ k
  · rw [if_pos ⟨hdvd, hk⟩, finsum_eq_single _ (k / n)]
    · have hkn : k / n ≠ 0 := fun h => by
        rw [Nat.div_eq_zero_iff] at h
        exact absurd (h.resolve_left hn) (not_lt.mpr (Nat.le_of_dvd hk hdvd))
      rw [if_pos (Nat.mul_div_cancel' hdvd).symm, coeff_log, if_neg hkn]
      set m := k / n
      rw [show ((-1 : A) ^ m) = algebraMap ℚ A ((-1 : ℚ) ^ m) from
            (by rw [map_pow, map_neg, map_one]),
        ← RingHom.map_mul]
      congr 1
      have hm1 : (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ m = -1 := by
        rw [← pow_add, show m + 1 + m = 2 * m + 1 from by ring, pow_succ, pow_mul,
          neg_one_sq, one_pow, one_mul]
      rw [div_mul_eq_mul_div, hm1, neg_div, one_div]
    · intro d hd
      refine (mul_eq_zero_of_right _ (if_neg fun hnd => hd ?_))
      rw [hnd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
  · rw [if_neg (by simp [hdvd]), finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg (fun hnd => hdvd ⟨d, hnd⟩), mul_zero]

end Glue

theorem constantCoeff_artinHasseExpSeries : constantCoeff (artinHasseExpSeries p) = 1 := by
  unfold artinHasseExpSeries
  rw [constantCoeff_subst_self' (constantCoeff_artinHasseArg p), constantCoeff_exp]

theorem map_binomialSeries (r : ℤ_[p]) :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (PowerSeries.binomialSeries ℤ_[p] r)
      = PowerSeries.binomialSeries ℚ_[p] (algebraMap ℤ_[p] ℚ_[p] r) := by
  ext k
  simp only [coeff_map, binomialSeries_coeff, smul_eq_mul, mul_one]
  exact Ring.map_choose (algebraMap ℤ_[p] ℚ_[p]) r k

theorem sum_moebius_coprime_divisors (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ N.divisors with ¬ p ∣ n, (moebius n : ℤ)
      = if IsPPow p N then 1 else 0 := by
  have hN0 : N ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
  set M := N / p ^ (N.factorization p) with hM
  have hMpos : 0 < M := Nat.ordCompl_pos p hN0
  have hMdvd : M ∣ N := Nat.ordCompl_dvd N p
  have hpM : ¬ p ∣ M := Nat.not_dvd_ordCompl hp.out hN0
  have hset : (N.divisors.filter fun n => ¬ p ∣ n) = M.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨fun ⟨⟨hdN, _⟩, hpd⟩ => ⟨Nat.dvd_ordCompl_of_dvd_not_dvd hdN hpd, hMpos.ne'⟩,
      fun ⟨hdM, _⟩ => ⟨⟨hdM.trans hMdvd, hN0⟩, fun hpd => hpM (hpd.trans hdM)⟩⟩
  rw [hset]
  have key : ∑ d ∈ M.divisors, (moebius d : ℤ) = if M = 1 then 1 else 0 := by
    have hid : (↑(moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℤ) = moebius := by
      ext n; simp [intCoe_apply]
    have h := congr_fun (congr_arg DFunLike.coe (coe_moebius_mul_coe_zeta (R := ℤ))) M
    rw [hid, coe_mul_zeta_apply, one_apply] at h
    exact h
  rw [key]
  simp only [isPPow_iff_ordCompl_eq_one p hN, ← hM]

theorem trunc_moebFactor_eq_one {k m : ℕ} (hm : k < m) :
    trunc (k + 1) (moebFactor p m) = 1 := by
  have hm0 : m ≠ 0 := by omega
  have hord : ((k : ℕ∞) + 1) ≤ (moebFactor p m - 1).order := by
    unfold moebFactor; rw [if_neg hm0]
    have hsub1 : (1 : ℤ_[p]⟦X⟧) = subst (-(X : ℤ_[p]⟦X⟧) ^ m) (1 : ℤ_[p]⟦X⟧) := by
      rw [← coe_substAlgHom (hasSubst_negXpow hm0)]; exact (map_one _).symm
    rw [hsub1, ← subst_sub (hasSubst_negXpow hm0)]
    calc ((k : ℕ∞) + 1) ≤ (m : ℕ∞) := by exact_mod_cast hm
      _ = ((-(X : ℤ_[p]⟦X⟧) ^ m)).order := by rw [order_neg, order_X_pow]
      _ ≤ _ := le_order_subst_right' (by simp [hm0]) (by simp)
  ext j
  rw [coeff_trunc, Polynomial.coeff_one]
  rcases lt_or_ge j (k + 1) with hjk | hjk
  · rw [if_pos hjk]
    have hj : (j : ℕ∞) < (moebFactor p m - 1).order :=
      lt_of_lt_of_le (by exact_mod_cast hjk) hord
    have := coeff_of_lt_order j hj
    rw [map_sub, sub_eq_zero] at this
    rw [this, coeff_one]
  · rw [if_neg (not_lt.mpr hjk), eq_comm, if_neg (by omega)]

theorem trunc_prod_eq_one {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (k : ℕ) (hf : ∀ i ∈ s, trunc (k + 1) (f i) = 1) :
    trunc (k + 1) (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← trunc_trunc_mul, hf a (Finset.mem_insert_self _ _),
      Polynomial.coe_one, one_mul, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem coeff_moebProd_stable (k N : ℕ) (hN : k ≤ N) :
    coeff k (moebProd p N) = coeff k (moebProd p k) := by
  classical
  unfold moebProd
  have hsplit : (Finset.Ioc 0 N).filter (¬ p ∣ ·) =
      (Finset.Ioc 0 k).filter (¬ p ∣ ·) ∪ (Finset.Ioc k N).filter (¬ p ∣ ·) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le k) hN]
  rw [hsplit, Finset.prod_union
    ((Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)) )]
  have htr : trunc (k + 1) (∏ n ∈ (Finset.Ioc k N).filter (¬ p ∣ ·), moebFactor p n) = 1 :=
    trunc_prod_eq_one _ _ k fun m hm =>
      trunc_moebFactor_eq_one p (Finset.mem_Ioc.mp (Finset.mem_filter.mp hm).1).1
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self k), ← trunc_mul_trunc, htr,
    Polynomial.coe_one, mul_one, coeff_coe_trunc_of_lt (Nat.lt_succ_self k)]

private noncomputable abbrev ι := algebraMap ℤ_[p] ℚ_[p]

theorem ps_map_subst {R S : Type*} [CommRing R] [CommRing S] {a : R⟦X⟧}
    (ha : HasSubst a) (h : R →+* S) (f : R⟦X⟧) :
    PowerSeries.map h (f.subst a) = (PowerSeries.map h f).subst (PowerSeries.map h a) :=
  map_subst ha f

theorem constantCoeff_map_moebFactor (n : ℕ) :
    constantCoeff (PowerSeries.map (ι p) (moebFactor p n)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
    constantCoeff_moebFactor, map_one]

theorem logOf_map_moebFactor {n : ℕ} (hn : 0 < n) (_hpn : ¬ p ∣ n) :
    logOf (PowerSeries.map (ι p) (moebFactor p n))
      = (ι p (moebExponent p n)) • (log ℚ_[p]).subst (-(X : ℚ_[p]⟦X⟧) ^ n) := by
  unfold moebFactor; rw [if_neg hn.ne']
  rw [ps_map_subst (hasSubst_negXpow hn.ne') (ι p),
    show PowerSeries.map (ι p) (-(X : ℤ_[p]⟦X⟧) ^ n) = -(X : ℚ_[p]⟦X⟧) ^ n from by
      rw [map_neg, map_pow, map_X],
    map_binomialSeries,
    logOf_subst (binomialSeries_constantCoeff _) (by simp [hn.ne']),
    logOf_binomialSeries, ← smul_eq_C_mul,
    subst_smul (hasSubst_negXpow hn.ne')]

theorem coeff_logOf_map_moebProd (N k : ℕ) (hk : k ≤ N) :
    coeff k (logOf (PowerSeries.map (ι p) (moebProd p N)))
      = if IsPPow p k then (k : ℚ_[p])⁻¹ else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [coeff_zero_eq_constantCoeff, constantCoeff_logOf
        (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
              constantCoeff_moebProd, map_one]),
      if_neg (fun ⟨h, _⟩ => absurd h (lt_irrefl 0))]

  unfold moebProd
  rw [show PowerSeries.map (ι p) (∏ n ∈ (Finset.Ioc 0 N).filter (¬ p ∣ ·), moebFactor p n)
        = ∏ n ∈ (Finset.Ioc 0 N).filter (¬ p ∣ ·), PowerSeries.map (ι p) (moebFactor p n)
      from map_prod _ _ _,
    logOf_prod_of_constantCoeff_one _ _ (fun n _ => constantCoeff_map_moebFactor p n),
    map_sum]

  have hsum : ∀ n ∈ (Finset.Ioc 0 N).filter (¬ p ∣ ·),
      coeff k (logOf (PowerSeries.map (ι p) (moebFactor p n)))
        = if n ∣ k then (moebius n : ℚ_[p]) * (k : ℚ_[p])⁻¹ else 0 := by
    intro n hn
    obtain ⟨hn_mem, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn_mem
    rw [logOf_map_moebFactor p hn0 hpn, coeff_smul,
      coeff_log_subst_negXpow hn0.ne' k]
    by_cases hdvd : n ∣ k
    · rw [if_pos hdvd, if_pos ⟨hdvd, hk0⟩, moebExponent, if_neg hpn]
      have hnu : IsUnit (n : ℤ_[p]) :=
        PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr
          ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn))
      have hinv : (ι p) (Ring.inverse (n : ℤ_[p])) = (n : ℚ_[p])⁻¹ := by
        have h1 : (ι p) (n : ℤ_[p]) = (n : ℚ_[p]) := by push_cast; ring
        have h2 := congr_arg (ι p) (Ring.inverse_mul_cancel _ hnu)
        rw [map_mul, map_one, h1] at h2
        exact eq_inv_of_mul_eq_one_left h2
      rw [show (ι p) (-(↑(moebius n) : ℤ_[p]) * Ring.inverse (n : ℤ_[p]))
            = -(moebius n : ℚ_[p]) * (n : ℚ_[p])⁻¹ from by
          rw [map_mul, map_neg, map_intCast, hinv],
        smul_eq_mul,
        show algebraMap ℚ ℚ_[p] (-((k / n : ℕ) : ℚ)⁻¹) = -((k / n : ℕ) : ℚ_[p])⁻¹ from by
          simp [map_neg, map_inv₀, map_natCast]]
      have hkn : (k : ℚ_[p]) = (n : ℚ_[p]) * ((k / n : ℕ) : ℚ_[p]) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      have hknne : ((k / n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr
        (fun h => absurd (Nat.div_eq_zero_iff.mp h |>.resolve_left hn0.ne')
          (not_lt.mpr (Nat.le_of_dvd hk0 hdvd)))
      have hnne : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
      rw [hkn, mul_inv]
      ring
    · rw [if_neg (by simp [hdvd]), smul_zero, if_neg hdvd]
  rw [Finset.sum_congr rfl hsum]

  rw [← Finset.sum_filter, Finset.filter_filter]
  have hrange : ((Finset.Ioc 0 N).filter fun n => ¬ p ∣ n ∧ n ∣ k)
      = k.divisors.filter fun n => ¬ p ∣ n := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors, hk0.ne', ne_eq,
      not_false_eq_true, and_true]
    constructor
    · rintro ⟨⟨hn0, _⟩, hpn, hnk⟩; exact ⟨hnk, hpn⟩
    · rintro ⟨hnk, hpn⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hnk hk0, (Nat.le_of_dvd hk0 hnk).trans hk⟩, hpn, hnk⟩
  rw [hrange, ← Finset.sum_mul]
  have hcast := congr_arg (fun x : ℤ => (x : ℚ_[p])) (sum_moebius_coprime_divisors p k hk0)
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero] at hcast
  rw [hcast]
  split_ifs with hpp
  · simp
  · simp

theorem map_artinHasseExpSeriesZp :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (series p)
      = PowerSeries.map (algebraMap ℚ ℚ_[p]) (artinHasseExpSeries p) := by
  ext k

  rw [coeff_map, MvFormalGroup.ArtinHasse.series, coeff_mk, ← coeff_map (f := ι p)]

  have hRHS : PowerSeries.map (algebraMap ℚ ℚ_[p]) (artinHasseExpSeries p)
      = (exp ℚ_[p]).subst (PowerSeries.map (algebraMap ℚ ℚ_[p]) (artinHasseArg p)) := by
    unfold artinHasseExpSeries
    rw [ps_map_subst (hasSubst_artinHasseArg p), map_exp]
  rw [hRHS]

  set ga := PowerSeries.map (algebraMap ℚ ℚ_[p]) (artinHasseArg p)
  have hga : constantCoeff ga = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
      constantCoeff_artinHasseArg, RingHom.map_zero]
  refine coeff_eq_of_forall_coeff_logOf_eq
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff,
          constantCoeff_moebProd, map_one])
    (by rw [constantCoeff_subst_self hga, constantCoeff_exp])
    k (fun j hj => ?_)
  rw [coeff_logOf_map_moebProd p k j hj, logOf_exp_subst hga, coeff_map, artinHasseArg,
    coeff_mk]
  split_ifs with hpp
  · rw [map_inv₀, map_natCast]
  · exact (RingHom.map_zero _).symm

end ArtinHasseIntegralSol
p2m_reactivate "P2MW.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst.ArtinHasseIntegralSol"

theorem ArtinHasseIntegralSol.mk_eq_artinHasseArg (p : ℕ) [Fact p.Prime] :
    (PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0) =
      ArtinHasseIntegralSol.artinHasseArg p := by
  ext k
  simp only [ArtinHasseIntegralSol.artinHasseArg, PowerSeries.coeff_mk,
    ArtinHasseIntegralSol.isPPow_iff_exists]

open Classical in

theorem solution (p : ℕ) [Fact p.Prime] :
    PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (MvFormalGroup.ArtinHasse.series p) =
      PowerSeries.map (algebraMap ℚ ℚ_[p])
        ((PowerSeries.exp ℚ).subst
          (PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0)) := by
  rw [ArtinHasseIntegralSol.mk_eq_artinHasseArg]
  exact ArtinHasseIntegralSol.map_artinHasseExpSeriesZp p

end
p2m_reactivate "P2MW.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst.ArtinHasseIntegralSol"

end S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst
end P2MW
export P2MW.S_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst (solution)
