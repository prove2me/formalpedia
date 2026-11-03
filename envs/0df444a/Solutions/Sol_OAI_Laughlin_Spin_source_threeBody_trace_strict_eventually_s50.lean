-- Prove2me | solution 1 for OAI.Laughlin.Spin.source_threeBody_trace_strict_eventually_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T18:42:37.333953+00:00
-- url     : https://prove2.me/submissions/8457d4c2-ae02-44d6-b471-5ab7a624f079

import Mathlib
import Definitions.Def_OAIQ050L019
import Theorems.Thm_OAI_Laughlin_Spin_source_physical_threeBody_trace_formula_tendsto_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem threeBody_2 : e 2 < limitBound 2 := by decide +kernel

theorem threeBody_4 : e 4 < limitBound 4 := by decide +kernel

theorem threeBody_5 : e 5 < limitBound 5 := by decide +kernel

theorem threeBody_6 : e 6 < limitBound 6 := by decide +kernel

theorem threeBody_7 : e 7 < limitBound 7 := by decide +kernel

theorem threeBody_8 : e 8 < limitBound 8 := by decide +kernel

theorem threeBody_9 : e 9 < limitBound 9 := by decide +kernel

theorem threeBody_10 : e 10 < limitBound 10 := by decide +kernel

theorem threeBody_11 : e 11 < limitBound 11 := by decide +kernel

theorem threeBody_12 : e 12 < limitBound 12 := by decide +kernel

theorem threeBody_13 : e 13 < limitBound 13 := by decide +kernel

theorem threeBody_14 : e 14 < limitBound 14 := by decide +kernel

theorem threeBody_15 : e 15 < limitBound 15 := by decide +kernel

theorem threeBody_certificate (z : ℕ)
    (hz : z ∈ [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]) : e z < limitBound z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact threeBody_2
  · exact threeBody_4
  · exact threeBody_5
  · exact threeBody_6
  · exact threeBody_7
  · exact threeBody_8
  · exact threeBody_9
  · exact threeBody_10
  · exact threeBody_11
  · exact threeBody_12
  · exact threeBody_13
  · exact threeBody_14
  · exact threeBody_15

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_ScalarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Topology
open Filter

theorem three_body_real (z : ℕ) (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    (Certificate.e z : ℝ) <
      (3/2 : ℝ)*(3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
  have hh : (Certificate.e z : ℝ) < (Certificate.limitBound z : ℝ) :=
    Rat.cast_lt.mpr (Certificate.threeBody_certificate z hz)
  simpa [Certificate.limitBound] using hh

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q => threeBodyDimensionRatio Q z) atTop (𝓝 (3/2 : ℝ)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext Q
  unfold threeBodyDimensionRatio
  congr 1 <;> ring

theorem source_threeBody_trace_strict_eventually_s50_oai (z : ℕ)
    (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    ∀ᶠ Q : ℕ in atTop, physicalThreeBodyTraceFormula Q z <
      threeBodyDimensionRatio Q z * gramEigenvalueFormula Q z := by
  have h := ((threeBodyDimensionRatio_tendsto z).mul (gramEigenvalueFormula_tendsto z)).sub
    (source_physical_threeBody_trace_formula_tendsto_s50 z)
  have hl : 0 < (3/2 : ℝ)*((3*(z : ℝ)-1)*(-1/2 : ℝ)^z)-(Certificate.e z : ℝ) := by
    have hh := three_body_real z hz
    nlinarith only [hh]
  exact ((tendsto_order.mp h).1 0 hl).mono (fun Q hQ => by linarith)

end Laughlin.Spin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Spin.source_threeBody_trace_strict_eventually_s50_oai := @OAI.Laughlin.Spin.source_threeBody_trace_strict_eventually_s50_oai
