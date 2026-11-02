-- Prove2me | solution 1 for OAI.Laughlin.sharp_scalar_budget_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T12:43:35.893022+00:00
-- url     : https://prove2.me/submissions/8f0536e0-4a1f-4e15-930d-da900b2f4239

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L008
import Theorems.Thm_OAI_Laughlin_deltaTerm_tendsto_s50

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem tail_series_value :
    HasSum (fun m : ℕ =>
      (3/2 : ℝ) * (3 * (17 + 2*(m : ℝ)) - 1) * (18 + 2*(m : ℝ)) *
        (1/2 : ℝ)^(17+2*m)) (61/4096 : ℝ) := by
  have hr : ‖(1/4 : ℝ)‖ < 1 := by norm_num
  have h₂ := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h₁ := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h₀ := hasSum_geometric_of_norm_lt_one hr
  have hs := (((h₂.mul_left (24 : ℝ)).add (h₁.mul_left 172)).add
    (h₀.mul_left 876)).mul_left (3/262144 : ℝ)
  convert! hs using 1
  · ext m
    have hc : (Nat.choose (m+2) 2 : ℝ) * 2 = ((m : ℝ)+2)*((m : ℝ)+1) := by
      have hx : (Nat.choose (m+2) 2 : ℝ) * 2 = ((m : ℝ)+2)*((m : ℝ)+1) := by
        induction m with
        | zero => norm_num
        | succ m ih =>
          rw [Nat.choose_succ_succ', Nat.choose_one_right]
          push_cast
          nlinarith
      exact hx
    have hp : (1/2 : ℝ)^(17+2*m) = (1/2 : ℝ)^17 * (1/4 : ℝ)^m := by
      rw [pow_add, pow_mul]
      norm_num
    rw [hp]
    linear_combination -(9/65536 : ℝ) * (1/4 : ℝ)^m * hc
  · norm_num

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
noncomputable section
open scoped BigOperators

theorem fallingRatio_le_geometric {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2/3 : ℝ)^z := by
  have hr (i : ℕ) (hi : i ∈ Finset.range z) :
      ((Q-i : ℕ) : ℝ) / ((2*Q-2-i : ℕ) : ℝ) ≤ (2/3 : ℝ) := by
    have hiQ : i ≤ Q := (Nat.le_of_lt (Finset.mem_range.mp hi)).trans hz
    have hid : i ≤ 2*Q-2 := by omega
    have h2 : 2 ≤ 2*Q := by omega
    rw [Nat.cast_sub hiQ, Nat.cast_sub hid, Nat.cast_sub h2]
    push_cast
    have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hir : (i : ℝ) ≤ Q := by exact_mod_cast hiQ
    have hden : 0 < 2*(Q : ℝ)-2-i := by linarith
    apply (div_le_iff₀ hden).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  calc
    fallingRatio Q z = ∏ i ∈ Finset.range z,
        (((Q-i : ℕ) : ℝ) / ((2*Q-2-i : ℕ) : ℝ)) := by
      simp [fallingRatio, Nat.descFactorial_eq_prod_range, Nat.cast_prod,
        Finset.prod_div_distrib]
    _ ≤ ∏ _i ∈ Finset.range z, (2/3 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · exact hr
    _ = _ := by simp [div_pow]

theorem tail_bracket_bounds {Q z : ℕ} (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    0 ≤ 3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ∧
      3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ 3*(z : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hzr : (16 : ℝ) ≤ z := by exact_mod_cast hz₀
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hd : (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) ≤ (z : ℝ)+1 := by
    apply (div_le_iff₀ hQr).mpr
    nlinarith
  have hn : 0 ≤ (z : ℝ)*((z : ℝ)+1)/(Q : ℝ) := by positivity
  constructor <;> linarith

theorem gramEigenvalueFormula_abs_le {Q z : ℕ}
    (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    |gramEigenvalueFormula Q z| ≤ (2/3 : ℝ)^z * (3*(z : ℝ)) := by
  have hratio : 0 ≤ fallingRatio Q z := by unfold fallingRatio; positivity
  have hb := tail_bracket_bounds hQ hz₀ hz
  unfold gramEigenvalueFormula
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hratio, abs_of_nonneg hb.1]
  exact mul_le_mul (fallingRatio_le_geometric hQ hz) hb.2 hb.1 (by positivity)

theorem tailWeight_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz₀ : 16 ≤ z) (hz : z ≤ Q) :
    tailWeight Q z ≤ 6*(z : ℝ)*((z : ℝ)+1)*(2/3 : ℝ)^z := by
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdim : (3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2*(Q : ℝ)-1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) z]
  unfold tailWeight
  calc
    _ ≤ (2*((2/3 : ℝ)^z * (3*(z : ℝ)))) * ((z : ℝ)+1) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hdim (gramEigenvalueFormula_abs_le hQ hz₀ hz) (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end
end Laughlin

end OAI
end

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

theorem tail_majorant_summable :
    Summable (fun z : ℕ => 6*(z : ℝ)*((z : ℝ)+1)*(2/3 : ℝ)^z) := by
  have hr : ‖(2/3 : ℝ)‖ < 1 := by norm_num
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one 2 hr).add
    (summable_pow_mul_geometric_of_norm_lt_one 1 hr)).mul_left (6 : ℝ)
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  ring

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

theorem tailWeight_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    0 ≤ tailWeight Q z := by
  have hQr : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hz
  unfold tailWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact div_nonneg (by linarith) (by linarith)
    · exact abs_nonneg _
  · positivity

theorem deltaFormula_tendsto :
    Tendsto deltaFormula atTop (𝓝 (61/4096 : ℝ)) := by
  let bound : ℕ → ℝ := fun m =>
    6*((17+2*m : ℕ) : ℝ)*(((17+2*m : ℕ) : ℝ)+1)*(2/3 : ℝ)^(17+2*m)
  have hinj : Function.Injective (fun m : ℕ => 17+2*m) := by
    intro a b hab
    change 17+2*a = 17+2*b at hab
    omega
  have hb : Summable bound := tail_majorant_summable.comp_injective hinj
  have hbound : ∀ Q m, ‖deltaTerm Q m‖ ≤ bound m := by
    intro Q m
    unfold deltaTerm
    split_ifs with hQ
    · rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg (by omega) hQ)]
      exact tailWeight_le (by omega) (by omega) hQ
    · simp only [norm_zero]
      dsimp [bound]
      positivity
  have hh := tendsto_tsum_of_dominated_convergence hb deltaTerm_tendsto_s50
    (Eventually.of_forall hbound)
  rw [tail_series_value.tsum_eq] at hh
  exact hh

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Fock_SharpGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open Filter
open scoped Topology BigOperators

theorem gammaStar_budget :
    1 - (93527408868499 / 10^14 : ℝ) - 61/4096 - 1222*(3/10^6) = gammaStar := by
  norm_num [gammaStar]

theorem sharp_scalar_budget_s50_oai (error : ℕ → ℝ)
    (he : Tendsto error atTop (𝓝 0)) (γ : ℝ) (hγ : γ < gammaStar) :
    ∀ᶠ Q : ℕ in atTop, γ ≤
      1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-error Q := by
  have ht : Tendsto (fun Q : ℕ =>
      1-93527408868499/10^14-deltaFormula Q-1222*(3/10^6)-error Q) atTop
      (𝓝 ((1-93527408868499/10^14)-61/4096-1222*(3/10^6)-(0 : ℝ))) :=
    ((tendsto_const_nhds.sub deltaFormula_tendsto).sub tendsto_const_nhds).sub he
  have hlim : γ < (1-93527408868499/10^14)-61/4096-1222*(3/10^6)-(0 : ℝ) := by
    simpa only [sub_zero, gammaStar_budget] using hγ
  exact ((tendsto_order.mp ht).1 _ hlim).mono fun _ hQ => le_of_lt hQ

end Laughlin

end OAI
end

theorem solution : type_of% @OAI.Laughlin.sharp_scalar_budget_s50_oai := @OAI.Laughlin.sharp_scalar_budget_s50_oai
