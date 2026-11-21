-- Prove2me | solution 3 for MasulloRH.regularized_initial_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:50:46.533274+00:00
-- url     : https://prove2.me/submissions/86962382-2748-4766-b099-e5a2486e1ce9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_trace_error_le_finite_resolvent_defect
import Theorems.Thm_MasulloRH_regularized_reference_mass_prime_series
import Theorems.Thm_MasulloRH_critical_line_mass_dominates_finite_prime_sums
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

theorem solution (α : ℝ) (hα : 0 < α) (_hαsmall : α < 1 / 2)
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
