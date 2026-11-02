-- Prove2me | solution 1 for OAI.Laughlin.deltaTerm_tendsto_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:42:46.479211+00:00
-- url     : https://prove2.me/submissions/6d970014-cb63-4929-aa8f-aec9a2aaa398

import Mathlib
import Definitions.Def_OAIQ050L008

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1/2 : ℝ)^z)) := by
  have hp : Tendsto (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) atTop
        (𝓝 (∏ _i ∈ Finset.range z, (1/2 : ℝ))) := by
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_add_mul_div_add_mul_atTop_nhds (-(i : ℝ)) (-(2+(i : ℝ))) 1 (by norm_num)
  have he : (fun Q : ℕ => ∏ i ∈ Finset.range z,
      ((-(i : ℝ) + 1*(Q : ℝ))/(-(2+(i : ℝ))+2*(Q : ℝ)))) =ᶠ[atTop]
        (fun Q : ℕ => fallingRatio Q z) := by
    filter_upwards [eventually_ge_atTop (max z 4)] with Q hQ
    have hzQ : z ≤ Q := le_trans (le_max_left _ _) hQ
    have h4 : 4 ≤ Q := le_trans (le_max_right _ _) hQ
    unfold fallingRatio
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
    simp only [Nat.cast_prod, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hiQ : i ≤ Q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hzQ
    rw [Nat.cast_sub hiQ, Nat.cast_sub (by omega : i ≤ 2*Q-2),
      Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    congr 1 <;> ring
  have hh := hp.congr' he
  simpa [div_pow] using hh

theorem gramEigenvalueFormula_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => gramEigenvalueFormula Q z) atTop
      (𝓝 ((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)) := by
  have hb : Tendsto (fun Q : ℕ =>
      (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ))) atTop (𝓝 (3*(z : ℝ)-1)) := by
    have hh := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((z : ℝ)*((z : ℝ)+1))
    simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hh
  have hh := ((fallingRatio_tendsto z).const_mul ((-1 : ℝ)^z)).mul hb
  have he : (-1 : ℝ)^z * (1/2 : ℝ)^z * (3*(z : ℝ)-1) =
      (3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
    rw [← mul_pow]
    ring
  simpa only [gramEigenvalueFormula, he] using hh

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter
noncomputable section

theorem tailWeight_tendsto (z : ℕ) (hz : 16 ≤ z) :
    Tendsto (fun Q : ℕ => tailWeight Q z) atTop
      (𝓝 ((3/2 : ℝ)*(3*(z : ℝ)-1)*(1/2 : ℝ)^z*((z : ℝ)+1))) := by
  have hd := tendsto_add_mul_div_add_mul_atTop_nhds
    (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  have hh := (hd.mul (gramEigenvalueFormula_tendsto z).abs).mul_const ((z : ℝ)+1)
  have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz
  have he : (3/2 : ℝ)*|(3*(z : ℝ)-1)*(-1/2 : ℝ)^z| *((z : ℝ)+1) =
      (3/2 : ℝ)*(3*(z : ℝ)-1)*(1/2 : ℝ)^z*((z : ℝ)+1) := by
    rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : 0 ≤ 3*(z : ℝ)-1)]
    norm_num only [abs_div, abs_neg, abs_one]
    ring
  rw [he] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext Q
  unfold tailWeight
  congr 2
  ring

theorem deltaTerm_tendsto_s50_oai (m : ℕ) :
    Tendsto (fun Q : ℕ => deltaTerm Q m) atTop
      (𝓝 ((3/2 : ℝ)*(3*(17+2*(m : ℝ))-1)*(18+2*(m : ℝ))*
        (1/2 : ℝ)^(17+2*m))) := by
  have hh := tailWeight_tendsto (17+2*m) (by omega)
  have he : (fun Q => tailWeight Q (17+2*m)) =ᶠ[atTop]
      (fun Q => deltaTerm Q m) := by
    filter_upwards [eventually_ge_atTop (17+2*m)] with Q hQ
    simp [deltaTerm, hQ]
  have ht := hh.congr' he
  have hval : (3/2 : ℝ)*(3*((17+2*m : ℕ) : ℝ)-1)*(1/2 : ℝ)^(17+2*m)*
      (((17+2*m : ℕ) : ℝ)+1) =
      (3/2 : ℝ)*(3*(17+2*(m : ℝ))-1)*(18+2*(m : ℝ))*(1/2 : ℝ)^(17+2*m) := by
    push_cast
    ring
  simpa only [hval] using ht

end
end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.deltaTerm_tendsto_s50_oai := @OAI.Laughlin.deltaTerm_tendsto_s50_oai
