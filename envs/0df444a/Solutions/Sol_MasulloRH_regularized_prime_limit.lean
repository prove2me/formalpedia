-- Prove2me | solution 1 for MasulloRH.regularized_prime_limit
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:09:32.841077+00:00
-- url     : https://prove2.me/submissions/8ff8aa0c-61ae-4e8b-aed9-a93e103d9e20

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false
open MasulloRH ArithmeticFunction Filter
open scoped Topology

private def primePower (i : Nat.Primes × ℕ) : ℕ := Nat.Primes.prodNatEquiv i

private noncomputable def primeTerm (s : ℂ) (i : Nat.Primes × ℕ) : ℂ :=
  LSeries.term (fun m => (vonMangoldt m : ℂ)) s (primePower i)

private theorem prime_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (primeTerm s) (-zetaLogDeriv s) := by
  have hi : Function.Injective primePower :=
    Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  apply (hi.hasSum_iff (f := LSeries.term (fun m => (vonMangoldt m : ℂ)) s) ?_).mpr
  · have h := (LSeriesSummable_vonMangoldt hs).hasSum
    change HasSum _ (LSeries _ s) at h
    simpa only [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, zetaLogDeriv] using h
  · intro m hm
    have hm' : ¬IsPrimePow m := fun h => hm ⟨Nat.Primes.prodNatEquiv.symm ⟨m,h⟩,
      congrArg Subtype.val (Nat.Primes.prodNatEquiv.apply_symm_apply _)⟩
    simp [LSeries.term, vonMangoldt_eq_zero_iff.mpr hm']

private theorem cutoff_eventually {x : ℝ} (hx : 1 < x) :
    ∀ᶠ n : ℕ in atTop, traceLogCutoff n x = 1 := by
  have hl := Real.log_pos hx
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 / Real.log x) (Real.log x))
  filter_upwards [eventually_ge_atTop k] with n hn
  have hnk : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have h₁ : 2 / Real.log x ≤ n + 1 := by
    linarith [(le_max_left (2 / Real.log x) (Real.log x)).trans hk.le]
  have h₂ : Real.log x ≤ n + 1 := by
    linarith [(le_max_right (2 / Real.log x) (Real.log x)).trans hk.le]
  simp [traceLogCutoff, hx, Real.smoothTransition.one_of_one_le
    (show 1 ≤ (n + 1) * Real.log x - 1 by linarith [(div_le_iff₀ hl).mp h₁]),
    Real.smoothTransition.zero_of_nonpos (show Real.log x / (n + 1) - 1 ≤ 0 by
      linarith [(div_le_one hN).mpr h₂])]

private theorem cutoff_norm (n : ℕ) {x : ℝ} (hx : 1 < x) :
    ‖(traceLogCutoff n x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, traceLogCutoff, if_pos hx]
  have ha := Real.smoothTransition.nonneg ((n + 1) * Real.log x - 1)
  have hb := Real.smoothTransition.le_one (Real.log x / (n + 1) - 1)
  rw [abs_of_nonneg (mul_nonneg ha (sub_nonneg.mpr hb))]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (sub_nonneg.mpr hb)
    (sub_le_self _ (Real.smoothTransition.nonneg _))

private theorem cutoff_term (s : ℂ) (n : ℕ) (i : Nat.Primes × ℕ) :
    primePowerTraceTerm (regularizedTraceTest n s) i =
    (traceLogCutoff n (primePower i) : ℂ) * (primeTerm s i - primeTerm (5/2) i) := by
  obtain ⟨p,k⟩ := i
  let m : ℕ := (p : ℕ) ^ (k+1)
  let x : ℝ := m
  have hm : 1 < m := one_lt_pow₀ p.prop.one_lt (Nat.succ_ne_zero _)
  have hx : 1 < x := by dsimp only [x]; exact_mod_cast hm
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hd : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hx0).ne'
  have hbase : (↑(p : ℕ) : ℝ) ^ (k+1) = x := by simp [x,m]
  have he (z : ℂ) : (x : ℂ) ^ (1/2-z) = (Real.sqrt x : ℂ) * (x : ℂ) ^ (-z) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hxc, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow hx0.le]; norm_num
  have hterm (z : ℂ) : primeTerm z (p,k) = (Real.log (p : ℝ) : ℂ) * (x : ℂ) ^ (-z) := by
    change LSeries.term _ _ m = _
    rw [LSeries.term_of_ne_zero (by omega)]
    simp only [m, vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime p.prop]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    norm_cast
  simp only [primePowerTraceTerm, hbase, regularizedTraceTest, if_pos hx,
    if_neg (not_lt.mpr (inv_le_one_of_one_le₀ hx.le)), add_zero, hterm]
  change ((Real.log (p : ℝ) / Real.sqrt x : ℝ) : ℂ) *
    ((traceLogCutoff n x : ℂ) * ((x : ℂ) ^ (1 / 2 - s) - (x : ℂ) ^ (-2 : ℂ))) = _
  rw [he, show (-2 : ℂ) = 1/2-5/2 by norm_num, he, Complex.ofReal_div]
  change _ = (traceLogCutoff n x : ℂ) * _
  field_simp

theorem solution (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffPrime n s) atTop
      (𝓝 (-zetaLogDeriv s + zetaLogDeriv (5 / 2))) := by
  have h := (prime_hasSum (s := s) (by linarith)).sub
    (prime_hasSum (s := 5/2) (by norm_num))
  rw [sub_neg_eq_add] at h
  rw [← h.tsum_eq]
  apply tendsto_tsum_of_dominated_convergence h.summable.norm
  · intro i
    have hx : (1 : ℝ) < primePower i := by
      exact_mod_cast one_lt_pow₀ i.1.prop.one_lt (Nat.succ_ne_zero i.2)
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_eventually hx] with n hn
    simp [cutoff_term, hn]
  · exact Filter.Eventually.of_forall fun n i => by
      have hx : (1 : ℝ) < primePower i := by
        exact_mod_cast one_lt_pow₀ i.1.prop.one_lt (Nat.succ_ne_zero i.2)
      rw [cutoff_term, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_norm n hx)
