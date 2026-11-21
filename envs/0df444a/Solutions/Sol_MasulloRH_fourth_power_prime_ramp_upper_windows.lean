-- Prove2me | solution 1 for MasulloRH.fourth_power_prime_ramp_upper_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:15:53.7073+00:00
-- url     : https://prove2.me/submissions/e07e1252-b9d2-475c-95ec-dabbefc35d5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_finite_ordinate_prime_ramp_approximation
import Theorems.Thm_MasulloRH_right_zero_finite_sum_lower_windows
import Mathlib

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
