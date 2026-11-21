-- Prove2me | solution 1 for MasulloRH.omitted_zero_cancellation_iff_RH
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:24:46.16419+00:00
-- url     : https://prove2.me/submissions/9d28a618-c6ed-4f21-943e-3dab66836915

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_archTerm_log_test_eq_neg_real_place
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_regularized_prime_limit
import Theorems.Thm_MasulloRH_regularized_arch_limit
import Theorems.Thm_MasulloRH_regularized_spectral_limit
import Theorems.Thm_MasulloRH_regularized_rhs_analytic
import Theorems.Thm_MasulloRH_derivative_identity_continuation
import Theorems.Thm_MasulloRH_logDeriv_analytic_of_local_ode
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit false
/- Conditional analytic continuation and reflection adapt Prove2Me reductions submitted by
   davidloeffler in the Masullo RH mission, passing the trace law as an explicit hypothesis. -/
open MeasureTheory Set Filter
open scoped Topology

namespace MasulloRH

/-- The positive-width trace identity, with its three convergence assertions. -/
private def RationalTraceFormula : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ

private theorem initial_of_trace (htrace : RationalTraceFormula) (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    regularizedTraceRHS α s = zetaLogDeriv s := by
  have hplus := regularized_mellin_limit s (1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hminus := regularized_mellin_limit s (-1 / 2)
    (by norm_num; linarith) (by norm_num)
  have hpolar : Tendsto (fun n : ℕ => cutoffPolar n s) atTop
      (𝓝 (regularizedPolar s)) := by
    convert hplus.add hminus using 1
    all_goals simp only [cutoffPolar, regularizedPolar]
    all_goals congr 2
    all_goals ring
  have hleft := (regularized_arch_limit s hs).add (regularized_prime_limit s hs)
  have hright := hpolar.sub (regularized_spectral_limit α hα hαsmall s hs)
  have heq : (fun n : ℕ => cutoffArch n s + cutoffPrime n s) =
      (fun n : ℕ => cutoffPolar n s - cutoffSpectral α n s) := by
    funext n
    exact (htrace α hα (regularizedTraceTest n s)
      (regularized_test_admissible n s)).2.2.2
  rw [heq] at hleft
  have hlimit := tendsto_nhds_unique hleft hright
  unfold regularizedTraceRHS
  linear_combination hlimit

private theorem analytic_on_strip_of_trace (htrace : RationalTraceFormula) (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s := by
  have hhol := regularized_rhs_analytic α hα hαsmall
  have hinit := initial_of_trace htrace α hα hαsmall
  apply logDeriv_analytic_of_local_ode s hs.2 (regularizedTraceRHS α) (hhol s hs)
  have hopen : IsOpen {z : ℂ | InTraceContinuationDomain α z} := by
    change IsOpen ({z : ℂ | 1 / 2 + α < z.re} ∩ {z : ℂ | z ≠ 1})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      isOpen_compl_singleton
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact derivative_identity_continuation α hα hαsmall hhol hinit z hz

private theorem analytic_right_of_trace (htrace : RationalTraceFormula) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by
  let α : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4)
  have hα : 0 < α := by
    dsimp [α]
    exact lt_min (by linarith) (by norm_num)
  have hsmall : α < 1 / 2 := by
    have hle : α ≤ 1 / 4 := min_le_right _ _
    linarith
  have hdomain : InTraceContinuationDomain α s := by
    refine ⟨?_, hs_one⟩
    have hle : α ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  exact analytic_on_strip_of_trace htrace α hα hsmall s hdomain

private theorem zero_free_of_trace (htrace : RationalTraceFormula) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs_one
  have hpos : 0 < meromorphicOrderAt riemannZeta s := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
    simpa only [hz] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
    have hd := (isClosed_and_discrete_iff.mp
      ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩) s
    change riemannZetaZerosᶜ ∈ 𝓝[≠] s
    exact Filter.disjoint_principal_right.mp hd
  have hfinite : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
    intro htop
    obtain ⟨z, hne, heq⟩ := (hnear.and (meromorphicOrderAt_eq_top_iff.mp htop)).exists
    exact hne heq
  have hpole := meromorphicOrderAt_logDeriv_eq_neg_one ha.meromorphicAt
    (ne_of_gt hpos) hfinite
  have hnonneg := (analytic_right_of_trace htrace s hs hs_one).meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (logDeriv riemannZeta) s at hnonneg
  rw [hpole] at hnonneg
  change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hnonneg
  have hbad : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hnonneg
  norm_num at hbad

open Complex in
/-- The same implication in Mathlib’s formulation excluding exactly the trivial zeros. -/
private theorem riemannHypothesis_of_trace (htrace : RationalTraceFormula) :
    RiemannHypothesis := by
  intro s hz htriv hs1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hr
  · have hs0 : s ≠ 0 := by
      rintro rfl
      simp [riemannZeta_zero] at hz
    let w : ℂ := 1 - s
    have hw : (1/2 : ℝ) < w.re := by dsimp [w]; simp; linarith
    have hw1 : w ≠ 1 := by simpa [w] using hs0
    have hwN (n : ℕ) : w ≠ -(n : ℂ) := by
      intro he
      have h := congrArg Complex.re he
      simp only [Complex.neg_re, Complex.natCast_re] at h
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hf := riemannZeta_one_sub hwN hw1
    rw [show 1-w = s by dsimp [w]; ring, hz] at hf
    have hbase : (2 * (Real.pi:ℂ)) ≠ 0 := by exact_mod_cast (by positivity : 2 * Real.pi ≠ 0)
    have hfactor : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Gamma w ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)))
        (Complex.Gamma_ne_zero_of_re_pos (by linarith))
    have hcos := (mul_eq_zero.mp (mul_eq_zero.mp hf.symm |>.resolve_right (zero_free_of_trace htrace w hw hw1))).resolve_left hfactor
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have he : w = 2 * (k : ℂ) + 1 := by
      apply mul_left_cancel₀ hpi
      linear_combination 2 * hk
    have hs : s = -2*(k:ℂ) := by dsimp [w] at he; linear_combination -he
    have hkpos : 0 < k := by
      have hkre := congrArg Complex.re he
      norm_num at hkre
      by_contra! hnp
      rcases eq_or_lt_of_le hnp with hk | hk
      · exact hs0 (by simpa [hk] using hs)
      · have hneg : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hkpos.le
    cases n with
    | zero => omega
    | succ n =>
      apply htriv
      refine ⟨n, ?_⟩
      simpa [hn, Nat.cast_succ] using hs
  · exact zero_free_of_trace htrace s hr hs1 hz

end MasulloRH

open MasulloRH MeasureTheory Set
/-- Narrow-window cancellation is equivalent to RH for critical-strip zeros. -/
theorem solution :
    (∀ (α : ℝ), 0 < α → α < 1/2 → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
      (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0) ↔
    RiemannHypothesis := by
  constructor
  · intro hcancel
    apply riemannHypothesis_of_trace
    intro α hα φ hφ
    let outside := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    have hout : (∑' r : outside, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by
      by_cases hn : α < 1/2
      · exact hcancel α hα hn φ hφ
      · have : IsEmpty outside := ⟨fun r => by
          have hh := r.val.prop
          have hr : α ≤ |r.val.val.re - 1/2| := r.prop
          exact (not_lt_of_ge hr) ((abs_lt.mpr ⟨by linarith [hh.2.1], by linarith [hh.2.2]⟩).trans_le (le_of_not_gt hn))⟩
        exact tsum_empty
    obtain ⟨hi, hp, hs, _, hbalance⟩ := trace_window_comparison α φ hφ
    refine ⟨hi, hp, hs, ?_⟩
    rw [archTerm_log_test_eq_neg_real_place φ hφ] at hbalance
    change _ + _ + (∑' r : outside, _) = _ at hbalance
    rw [hout, add_zero] at hbalance
    linear_combination hbalance
  · intro hRH α hα _ φ _
    let outside := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    have : IsEmpty outside := ⟨fun r => by
      have hr := hRH r.val.val r.val.prop.1 (by
        rintro ⟨n, hn⟩
        have hre := congrArg Complex.re hn
        norm_num at hre
        linarith [r.val.prop.2.1, Nat.cast_nonneg (α := ℝ) n]) (by
        intro he
        have hre := congrArg Complex.re he
        simp only [Complex.one_re] at hre
        linarith [r.val.prop.2.2])
      have ho : α ≤ |r.val.val.re - 1/2| := r.prop
      rw [hr, sub_self, abs_zero] at ho
      exact (not_le_of_gt hα) ho⟩
    change (∑' r : outside, _) = 0
    exact tsum_empty
