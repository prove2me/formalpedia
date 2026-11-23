-- Prove2me | solution 2 for MasulloRH.fourth_power_prime_ramp_upper_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:33:56.108799+00:00
-- url     : https://prove2.me/submissions/807ea994-e1e4-44c1-8b7d-9f656912923e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation

-- Step 1: `mathlib_riemannHypothesis` implies `MasulloRH.right_zero_finite_sum_lower_windows` (accepted reduction of `MasulloRH.right_zero_finite_sum_lower_windows`).
section

set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH
end MasulloRH
open MasulloRH
theorem MasulloRH.right_zero_finite_sum_lower_windows :
    ∀ θ : ℝ, 1/2 < θ → θ < 0.8749570698 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ m : ℕ, 2 ≤ m → ∃ J : ℕ, m ≤ J ∧
        ∀ k : ℕ, J ≤ k → (k:ℝ) ≤ (J:ℝ)^(1+δ)+1 →
          ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
            (∀ z : ZetaZerosInTraceStrip (1/2), z ∈ F ↔ θ < z.val.re ∧
              100000  <  |z.val.im| ∧ |z.val.im| ≤ 5/2+2*((k^2:ℕ):ℝ)) ∧
            let x := (k:ℝ)^4;
            -(C*x^θ)  ≤  (∑ z ∈ F,(x:ℂ)*((analyticOrderNatAt riemannZeta z.val : ℂ)*
              (x:ℂ)^(z.val-1)/(z.val*(z.val-1)))).re :=
  by
    intro θ hθ _
    have hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    refine ⟨1, 0, one_pos, le_refl 0, fun m _ => ⟨m, le_refl m, fun k _ _ => ⟨∅, ?_, ?_⟩⟩⟩
    · intro z
      obtain ⟨hzero, hpos, hlt, -⟩ := z.property
      refine ⟨fun h => absurd h (Finset.notMem_empty z), fun h => ?_⟩
      exact absurd (lt_of_lt_of_eq h.1 (hstrip z.val hzero hpos hlt)) (not_lt.mpr hθ.le)
    · intro x
      simp only [Finset.sum_empty, Complex.zero_re, zero_mul, neg_zero, le_refl]

end

-- Step 2: `MasulloRH.right_zero_finite_sum_lower_windows` implies `MasulloRH.fourth_power_prime_ramp_upper_windows` (accepted reduction of `MasulloRH.fourth_power_prime_ramp_upper_windows`).
section

open MasulloRH Finset ArithmeticFunction

theorem solution :
    ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ m : ℕ, 1 ≤ m → ∃ J : ℕ, m ≤ J ∧ ∀ k : ℕ, J ≤ k → (k:ℝ) ≤ (J:ℝ)^(1+δ)+1 →
        let v := (k:ℝ)^4
        (∑ n ∈ range (⌊v⌋₊+1),vonMangoldt n*max (v/(n:ℝ)-1) 0) -
          v*(Real.log v-1-Real.eulerMascheroniConstant) ≤ C*v^θ := by
  classical
  let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
    x*(Real.log x-1-Real.eulerMascheroniConstant)
  intro θ hθ hθ1
  by_cases hb : θ<0.8749570698
  · obtain ⟨δ,C,hδ,hC,hwin⟩ := right_zero_finite_sum_lower_windows θ hθ hb
    refine ⟨δ,C+19,hδ,by linarith,?_⟩
    intro m hm
    obtain ⟨J,hJ,hw⟩ := hwin (max m 2) (le_max_right ..)
    refine ⟨J,(le_max_left ..).trans hJ,?_⟩
    intro k hJk hk
    have hk2 : 2≤k := (le_max_right ..).trans (hJ.trans hJk)
    obtain ⟨F,hF,hlo⟩ := hw k hJk hk
    obtain ⟨E,hE,he⟩ := finite_ordinate_prime_ramp_approximation.1 k hk2 θ hθ.le
    have hFE : E=F := Finset.ext fun z => (hE z).trans (hF z).symm
    rw [hFE] at he
    let x := (k:ℝ)^4
    let Q : ℝ := (∑ z ∈ F,(x:ℂ)*((analyticOrderNatAt riemannZeta z.val : ℂ)*
              (x:ℂ)^(z.val-1)/(z.val*(z.val-1)))).re
    change |G x+Q|≤19*x^θ at he
    change -(C*x^θ) ≤ Q at hlo
    change G x≤(C+19)*x^θ
    linarith [(abs_le.mp he).2]
  · refine ⟨1,9,by norm_num,by norm_num,?_⟩
    intro m hm
    refine ⟨max m 2,le_max_left ..,?_⟩
    intro k hJk _
    have hk : (2:ℝ)≤k := by exact_mod_cast (le_max_right m 2).trans hJk
    let x := (k:ℝ)^4
    have hx : 2≤x := (le_trans (by norm_num : (2:ℝ)≤2^4) (pow_le_pow_left₀ (by norm_num) hk 4))
    have h := finite_ordinate_prime_ramp_approximation.2.2.2 x hx
    change |G x|≤9*x^(0.8749570698:ℝ) at h
    change G x≤9*x^θ
    exact ((le_abs_self _).trans h).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (le_of_not_gt hb)) (by norm_num))

end
