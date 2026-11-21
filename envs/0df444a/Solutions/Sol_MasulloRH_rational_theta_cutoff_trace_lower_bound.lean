-- Prove2me | solution 1 for MasulloRH.rational_theta_cutoff_trace_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:52:59.06479+00:00
-- url     : https://prove2.me/submissions/82787804-0a8b-4254-95b5-6c50a9884e65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_trace_error_le_finite_resolvent_defect
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_critical_line_mass_dominates_finite_prime_sums
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloRH_rational_theta_cutoff_trace_defect
import Theorems.Thm_MasulloRH_rational_theta_annihilator_jet_trace
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Mathlib

open MasulloRH Filter Topology

private theorem line_kernel (z : ZetaZerosInTraceStrip (1/2)) (hz : z.val.re = 1/2) :
    (zeroResolventTerm (1/2) 3 z).re = (analyticOrderNatAt riemannZeta z.val:ℝ) *
      ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  unfold zeroResolventTerm
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
  congr 1
  simp only [one_div,Complex.sub_re,Complex.inv_re,Complex.normSq_apply,Complex.sub_im]
  norm_num [hz,pow_two,Complex.div_ofNat_re,Complex.div_ofNat_im]
  field_simp
  ring

private theorem finite_mass_implies_trace (α : ℝ) (hα : 0 < α) (_hαsmall : α < 1 / 2)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    regularizedTraceRHS α s = zetaLogDeriv s := by
  classical
  let C := Real.log 2 / 2 + Real.pi / 4 - 37 / 30
  let f (n : ℕ) := ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
    ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ)
  let A := (zetaLogDeriv 3).re -
    (zetaLogDeriv (5/2) + regularizedArch 3 - regularizedPolar 3).re
  let B := 16*(2*(2*‖s‖+3)*(‖s‖+5/2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum : HasSum f (A-C) := by
    convert regularized_reference_mass_prime_series using 1
    dsimp [A,C]
    ring
  have he (N : ℕ) : ‖zetaLogDeriv s - regularizedTraceRHS α s‖ ≤
      B*(A-(C+ ∑ n ∈ Finset.range N, f n)) := by
    obtain ⟨F,hF,hlow⟩ := critical_line_mass_dominates_finite_prime_sums N
    have hw (z) (hz : z ∈ F) : |z.val.re-1/2| < α := by simpa [hF z hz] using hα
    have hmass := regularized_trace_error_le_finite_resolvent_defect α ‖s‖ s le_rfl hs F hw
    apply hmass.trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply sub_le_sub_left
    calc _ ≤ _ := hlow
         _ = _ := Finset.sum_congr rfl fun z hz => (line_kernel z (hF z hz)).symm
  have hlim := (hsum.tendsto_sum_nat.const_add C).const_sub A
  have hlim' := hlim.const_mul B
  have hn := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim' he
  have hdiff : zetaLogDeriv s - regularizedTraceRHS α s = 0 := by
    apply norm_le_zero_iff.mp
    simpa [show A-(C+(A-C)) = 0 by ring] using hn
  exact (sub_eq_zero.mp hdiff).symm

open MasulloGRH MeasureTheory
open scoped Topology InnerProductSpace

private theorem finite_mass_implies_RH : RiemannHypothesis := by
  apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
  intro s hs hzero hone
  by_contra hline
  let α : ℝ := |s.re - 1/2|
  have hα : 0 < α := abs_pos.mpr (sub_ne_zero.mpr hline)
  have hαsmall : α < 1/2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  let ρ : ZetaZerosInTraceStrip (1/2) := ⟨s, hs, hzero, hone, hαsmall⟩
  have heq := finite_mass_implies_trace α hα hαsmall 3 (by norm_num)
  have hhalf := MasulloRH.regularized_initial_identity_full_strip 3 (by norm_num)
  have hbound : (regularizedTraceRHS (1/2) 3).re ≤ (regularizedTraceRHS α 3).re := by
    rw [heq, hhalf]
  have h := (single_resolvent_test α).mp hbound ρ
  exact (lt_irrefl α) h

private theorem theta_convolution_unique (p : ℝ) (φ : ℝ → ℂ)
    {T U : rationalThetaAnnihilator p →L[ℂ] rationalThetaAnnihilator p}
    (hT : IsRationalThetaConvolution p φ T)
    (hU : IsRationalThetaConvolution p φ U) : T = U := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply ext_inner_left ℂ
  exact fun g => (hT u g).trans (hU u g).symm

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ] rationalThetaAnnihilator ((n:ℝ)+1),
        IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T →
          (cutoffPolar n 3 - (cutoffArch n 3 + cutoffPrime n 3)).re ≤
            (operatorTrace T).re + ε := by
  classical
  have hex (n : ℕ) : ∃ T : rationalThetaAnnihilator ((n:ℝ)+1) →L[ℂ]
      rationalThetaAnnihilator ((n:ℝ)+1),
      IsRationalThetaConvolution ((n:ℝ)+1) (regularizedTraceTest n 3) T := by
    obtain ⟨T, hT, _⟩ := (rational_theta_annihilator_jet_trace ((n:ℝ)+1)
      (by linarith [Nat.cast_nonneg (α := ℝ) n])).2 _ (regularized_test_admissible n 3)
    exact ⟨T, hT.1⟩
  choose T hT using hex
  have hdef := rational_theta_cutoff_trace_defect T hT
  dsimp only at hdef
  have hz := hdef.2.2.mpr finite_mass_implies_RH
  rw [hz] at hdef
  intro ε hε N
  have hev := hdef.1.eventually (gt_mem_nhds hε)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨max N M, le_max_left _ _, ?_⟩
  intro U hU
  have hu := theta_convolution_unique _ _ hU (hT (max N M))
  rw [hu]
  have h := hM (max N M) (le_max_right _ _)
  linarith
