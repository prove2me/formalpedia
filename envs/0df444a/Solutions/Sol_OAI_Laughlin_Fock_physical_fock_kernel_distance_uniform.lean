-- Prove2me | solution 1 for OAI.Laughlin.Fock.physical_fock_kernel_distance_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:33:43.588995+00:00
-- url     : https://prove2.me/submissions/f8541518-90f5-4f62-b718-e8bc1b5f44fb

import Mathlib
import Definitions.Def_Laughlin
import Definitions.Def_OAIQ047L003
import Definitions.Def_OAIQ047L004
import Theorems.Thm_OAI_Laughlin_Fock_averagedFourTransferError_tendsto
import Theorems.Thm_OAI_Laughlin_Fock_physical_threeBody_budget_eventually
import Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_retained_bound
import Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square
import Theorems.Thm_OAI_Laughlin_Fock_sourceKForm_decomposition

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Basic
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
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Bound
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
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Limit
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
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_Convergence
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

theorem deltaTerm_tendsto (m : ℕ) :
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
  have hh := tendsto_tsum_of_dominated_convergence hb deltaTerm_tendsto
    (Eventually.of_forall hbound)
  rw [tail_series_value.tsum_eq] at hh
  exact hh

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Asymptotics_ScalarBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped Topology
open Filter

theorem eventual_scalar_budget (error : ℕ → ℝ)
    (he : Tendsto error atTop (𝓝 0)) :
    ∀ᶠ Q : ℕ in atTop, (1/100 : ℝ) ≤
      1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-error Q := by
  have ht : Tendsto (fun Q : ℕ =>
      1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-error Q) atTop
        (𝓝 ((1-93527408868499/10^14)-61/4096-10946*(3/10^6)-(0 : ℝ))) :=
    (((tendsto_const_nhds.sub deltaFormula_tendsto).sub tendsto_const_nhds).sub he)
  have hlim : (1/100 : ℝ) <
      (1-93527408868499/10^14)-61/4096-10946*(3/10^6)-0 := by norm_num
  exact (tendsto_order.mp ht).1 _ hlim |>.mono (fun Q hQ => le_of_lt hQ)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q)) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j : Module.Dual ℂ (Orbital Q))
      (CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  refine LinearMap.ext fun x => ?_
  change CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q))
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i : Module.Dual ℂ (Orbital Q)) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_Scaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem contraction_map {Q : ℕ} (f : Orbital Q →ₗ[ℂ] Orbital Q)
    (d : Module.Dual ℂ (Orbital Q)) (x : Space Q) :
    CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    change CliffordAlgebra.contractLeft d (ExteriorAlgebra.map f (ExteriorAlgebra.ι ℂ m*x)) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (d.comp f) (ExteriorAlgebra.ι ℂ m*x))
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

theorem projection_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    (LinearMap.proj i).comp (orbitalScaling Q d) = d i • LinearMap.proj i := by
  ext v
  rfl

theorem annihilate_scaling (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) (x : Space Q) :
    annihilate i (exteriorScaling Q d x) = d i • exteriorScaling Q d (annihilate i x) := by
  unfold annihilate exteriorScaling
  rw [contraction_map, projection_scaling, map_smul, LinearMap.smul_apply, map_smul]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_ScalingWedge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

theorem orbitalScaling_mode (Q : ℕ) (d : Fin (Q+1) → ℂ) (i : Fin (Q+1)) :
    orbitalScaling Q d (mode i) = d i • mode i := by
  funext j
  by_cases h : j = i
  · subst j
    simp [orbitalScaling,mode]
  · simp [orbitalScaling,mode,h]

theorem exteriorScaling_wedge (Q n : ℕ) (d : Fin (Q+1) → ℂ) (w : Fin n → Fin (Q+1)) :
    exteriorScaling Q d (ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a))) =
      (∏ a, d (w a)) • ExteriorAlgebra.ιMulti ℂ n (fun a => mode (w a)) := by
  unfold exteriorScaling
  rw [ExteriorAlgebra.map_apply_ιMulti]
  change ExteriorAlgebra.ιMulti ℂ n (fun a => orbitalScaling Q d (mode (w a))) = _
  simp_rw [orbitalScaling_mode]
  exact (ExteriorAlgebra.ιMulti ℂ n).map_smul_univ (fun a => d (w a)) (fun a => mode (w a))

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupation_product (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    (∏ a : Fin n, d (Set.powersetCard.ofFinEmbEquiv.symm A a)) = ∏ i ∈ A.val, d i := by
  apply Finset.prod_bij (fun a _ => Set.powersetCard.ofFinEmbEquiv.symm A a)
  · intro a ha
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A _).mp ⟨a,rfl⟩
  · intro a ha b hb hab
    exact (Set.powersetCard.ofFinEmbEquiv.symm A).injective hab
  · intro b hb
    obtain ⟨a,ha⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem A b).mpr hb
    exact ⟨a, Finset.mem_univ a, ha⟩
  · intro a ha
    rfl

theorem exteriorScaling_occupation_sector (Q n : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Set.powersetCard (Fin (Q+1)) n) :
    exteriorScaling Q d (occupationBasis Q A.val) =
      (∏ i ∈ A.val, d i) • occupationBasis Q A.val := by
  have h := exteriorScaling_wedge Q n d (Set.powersetCard.ofFinEmbEquiv.symm A)
  rw [occupation_product Q n d A] at h
  simpa only [occupationBasis, ExteriorAlgebra.basis_apply_powersetCard,
    ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem exteriorScaling_occupation (Q : ℕ) (d : Fin (Q+1) → ℂ)
    (A : Finset (Fin (Q+1))) :
    exteriorScaling Q d (occupationBasis Q A) = (∏ i ∈ A, d i) • occupationBasis Q A := by
  exact exteriorScaling_occupation_sector Q A.card d ⟨A,rfl⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Exterior_OccupationMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology

theorem occupationNormSq_nonneg (Q : ℕ) (x : Space Q) : 0 ≤ occupationNormSq Q x := by
  unfold occupationNormSq
  positivity

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Creation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) : annihilate i (occupationBasis Q A) = 0 := by
  let d : Fin (Q+1) → ℂ := fun j => if j = i then 0 else 1
  have hd : (∏ j ∈ A, d j) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp [d, show j ≠ i by intro h; subst j; exact hi hj]
  have h := annihilate_scaling Q d i (occupationBasis Q A)
  rw [exteriorScaling_occupation,hd,one_smul] at h
  simpa [d] using h

theorem create_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) : create i (occupationBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q+1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint
    (Pi.basisFun ℂ (Fin (Q+1)))
    (⟨{i},Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q+1)) 1)
    (⟨A,rfl⟩ : Set.powersetCard (Fin (Q+1)) A.card) hd
  change occupationBasis Q {i} * occupationBasis Q A = 0 at h
  rw [occupation_singleton] at h
  exact h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Annihilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock

theorem insertionSign_spec (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A = 1 ∨ insertionSign Q i A = -1 := by
  by_cases h : i ∉ A
  · simpa [insertionSign,h] using (create_unoccupied_sign Q i A h).choose_spec.1
  · simp [insertionSign,h]

theorem insertionSign_sq (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    insertionSign Q i A * insertionSign Q i A = 1 := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_unoccupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    create i (occupationBasis Q A) = insertionSign Q i A • occupationBasis Q (insert i A) := by
  simpa [insertionSign,hi] using (create_unoccupied_sign Q i A hi).choose_spec.2

theorem annihilate_insert (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∉ A) :
    annihilate i (occupationBasis Q (insert i A)) = insertionSign Q i A • occupationBasis Q A := by
  have h := LinearMap.congr_fun (mixed_car i i) (occupationBasis Q A)
  change annihilate i (create i (occupationBasis Q A)) +
    create i (annihilate i (occupationBasis Q A)) = (if i = i then (1 : ℂ) else 0) • occupationBasis Q A at h
  rw [create_unoccupied Q i A hi, map_smul, annihilate_unoccupied Q i A hi, map_zero] at h
  simp only [add_zero, ite_true, one_smul] at h
  have he := congrArg (fun x => insertionSign Q i A • x) h
  simpa only [smul_smul, insertionSign_sq, one_smul] using he

theorem annihilate_occupied (Q : ℕ) (i : Fin (Q+1))
    (A : Finset (Fin (Q+1))) (hi : i ∈ A) :
    annihilate i (occupationBasis Q A) =
      insertionSign Q i (A.erase i) • occupationBasis Q (A.erase i) := by
  simpa only [Finset.insert_erase hi] using
    annihilate_insert Q i (A.erase i) (Finset.notMem_erase i A)

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (annihilate i x) A =
      if i ∈ A then 0 else insertionSign Q i A * (occupationBasis Q).repr x (insert i A) := by
  let e : ℂ := if i ∈ A then 0 else insertionSign Q i A
  have h : ((occupationBasis Q).coord A).comp (annihilate i) =
      e • (occupationBasis Q).coord (insert i A) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (annihilate i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (insert i A)
    by_cases hiB : i ∈ B
    · rw [annihilate_occupied Q i B hiB, map_smul, Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · have hBA : B.erase i ≠ A := by intro h; rw [← h] at hiA; exact Finset.notMem_erase i B hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hBA]
      · by_cases hBA : B = insert i A
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have herase : B.erase i ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.insert_erase hiB]
          simp [e,hiA,Module.Basis.repr_self,herase,hBA]
    · rw [annihilate_unoccupied Q i B hiB]
      have hBA : B ≠ insert i A := by intro h; subst B; simp at hiB
      simp [e,Module.Basis.repr_self,hBA]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

theorem create_coordinate (Q : ℕ) (i : Fin (Q+1)) (x : Space Q)
    (A : Finset (Fin (Q+1))) :
    (occupationBasis Q).repr (create i x) A =
      if i ∈ A then insertionSign Q i (A.erase i) * (occupationBasis Q).repr x (A.erase i) else 0 := by
  let e : ℂ := if i ∈ A then insertionSign Q i (A.erase i) else 0
  have h : ((occupationBasis Q).coord A).comp (create i) =
      e • (occupationBasis Q).coord (A.erase i) := by
    apply (occupationBasis Q).ext
    intro B
    change (occupationBasis Q).repr (create i (occupationBasis Q B)) A =
      e * (occupationBasis Q).repr (occupationBasis Q B) (A.erase i)
    by_cases hiB : i ∈ B
    · rw [create_occupied Q i B hiB]
      have hBA : B ≠ A.erase i := by intro h; rw [h] at hiB; exact Finset.notMem_erase i A hiB
      simp [e,Module.Basis.repr_self,hBA]
    · rw [create_unoccupied Q i B hiB,map_smul,Finsupp.smul_apply]
      by_cases hiA : i ∈ A
      · by_cases hBA : B = A.erase i
        · subst B
          simp [e,hiA,Module.Basis.repr_self]
        · have hins : insert i B ≠ A := by
            intro h
            apply hBA
            rw [← h,Finset.erase_insert hiB]
          simp [e,hiA,Module.Basis.repr_self,hBA,hins]
      · have hins : insert i B ≠ A := by intro h; rw [← h] at hiA; simp at hiA
        simp [e,hiA,Module.Basis.repr_self,Finsupp.single_apply,hins]
  have hx := LinearMap.congr_fun h x
  by_cases hi : i ∈ A <;> simpa [e,hi] using hx

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_ContractionBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_unoccupied_insert {Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i : Fin (Q+1)) (f : Finset (Fin (Q+1)) → R) :
    (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∉ A), f (insert i A)) =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
  classical
  apply Finset.sum_bij (fun A _ => insert i A)
  · intro A hA
    simp
  · intro A hA B hB h
    have ha := (Finset.mem_filter.mp hA).2
    have hb := (Finset.mem_filter.mp hB).2
    have he := congrArg (fun C => C.erase i) h
    simpa [Finset.erase_insert,ha,hb] using he
  · intro B hB
    have hb := (Finset.mem_filter.mp hB).2
    exact ⟨B.erase i,by simp,Finset.insert_erase hb⟩
  · intro A hA
    rfl

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Adjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem insertionSign_star (Q : ℕ) (i : Fin (Q+1)) (A : Finset (Fin (Q+1))) :
    star (insertionSign Q i A) = insertionSign Q i A := by
  rcases insertionSign_spec Q i A with h | h <;> simp [h]

theorem create_annihilate_adjoint (Q : ℕ) (i : Fin (Q+1)) (x y : Space Q) :
    occupationInner Q (create i x) y = occupationInner Q x (annihilate i y) := by
  let f : Finset (Fin (Q+1)) → ℂ := fun A =>
    insertionSign Q i (A.erase i) *
      (star ((occupationBasis Q).repr x (A.erase i)) * (occupationBasis Q).repr y A)
  have hl : occupationInner Q (create i x) y =
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin (Q+1)) => i ∈ A), f A := by
    rw [Finset.sum_filter]
    unfold occupationInner
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hi : i ∈ A <;>
      simp only [f, create_coordinate, hi, ite_true, ite_false, star_mul,
        insertionSign_star, star_zero, zero_mul, mul_comm, mul_left_comm]
  rw [hl, ← sum_unoccupied_insert i f, Finset.sum_filter]
  unfold occupationInner
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hi : i ∈ A <;>
    simp only [f, hi, annihilate_coordinate, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, Finset.erase_insert, zero_mul, mul_assoc, mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Inner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_smul_left (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q (c • x) y = star c * occupationInner Q x y := by
  simp [occupationInner,star_mul,Finset.mul_sum,mul_comm,mul_left_comm]

theorem occupationInner_smul_right (Q : ℕ) (c : ℂ) (x y : Space Q) :
    occupationInner Q x (c • y) = c * occupationInner Q x y := by
  simp [occupationInner,Finset.mul_sum,mul_left_comm]

theorem occupationInner_sum_left {I : Type*} (Q : ℕ) (s : Finset I)
    (x : I → Space Q) (y : Space Q) :
    occupationInner Q (∑ a ∈ s, x a) y = ∑ a ∈ s, occupationInner Q (x a) y := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,star_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem occupationInner_sum_right {I : Type*} (Q : ℕ) (s : Finset I)
    (x : Space Q) (y : I → Space Q) :
    occupationInner Q x (∑ a ∈ s, y a) = ∑ a ∈ s, occupationInner Q x (y a) := by
  simp only [occupationInner,map_sum,Finsupp.finsetSum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem occupationInner_self (Q : ℕ) (x : Space Q) :
    occupationInner Q x x = (occupationNormSq Q x : ℂ) := by
  unfold occupationInner occupationNormSq
  simp only [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
  rfl

theorem occupationNormSq_eq_zero (Q : ℕ) (x : Space Q) :
    occupationNormSq Q x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hc : ∀ A, (occupationBasis Q).repr x A = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun A (_ : A ∈ Finset.univ) => sq_nonneg ‖(occupationBasis Q).repr x A‖)).mp h
      intro A
      have ha := hs A (Finset.mem_univ A)
      simpa using ha
    apply (occupationBasis Q).repr.injective
    ext A
    simp [hc]
  · intro h
    simp [h,occupationNormSq]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_Hamiltonian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem pairCreate_pair_adjoint (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (x y : Space Q) :
    occupationInner Q (pairCreateEnd Q c x) y = occupationInner Q x (pairEnd Q c y) := by
  simp only [pairCreateEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,star_star,create_annihilate_adjoint]

theorem sourceFockHamiltonian_quadratic (Q : ℕ) (x : Space Q) :
    occupationInner Q (sourceFockHamiltonian Q x) x = (sourceFockEnergy Q x : ℂ) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,sourcePairCreateEnd,sourcePairEnd,pairCreate_pair_adjoint,
    occupationInner_self,sourceFockEnergy,Complex.ofReal_sum]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PositiveFockLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators ComplexOrder
open Matrix

theorem occupationInner_star (Q : ℕ) (x y : Space Q) :
    star (occupationInner Q x y) = occupationInner Q y x := by
  simp [occupationInner,star_mul,mul_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_Orthonormality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_LoweringAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem choose_lowering (Q i : ℕ) (hi : 0 < i) (hiQ : i ≤ Q+1) :
    ((Q : ℝ)-(i : ℝ)+1) * (Q.choose (i-1) : ℝ) =
      (i : ℝ) * (Q.choose i : ℝ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hk : k ≤ Q := by omega
  have h := Nat.choose_succ_right_eq Q k
  have hc := congrArg (fun x : ℕ => (x : ℝ)) h
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at hc
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  nlinarith only [hc]

theorem pairPolynomialCoefficient_lowering (Q i j : ℕ)
    (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) +
    (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      ((i : ℝ)+(j : ℝ)-1)*pairPolynomialCoefficient Q i j := by
  have left : (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*pairPolynomialCoefficient Q (i-1) j else 0) =
      (i : ℝ)*((i : ℝ)-1-(j : ℝ))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hi : 0 < i
    · rw [ite_eq_left hi]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
      calc
        _ = ((i : ℝ)-1-(j : ℝ))*(Q.choose j : ℝ)*
          (((Q : ℝ)-(i : ℝ)+1)*(Q.choose (i-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q i hi (by omega)]; ring
    · have hz : i = 0 := by omega
      simp [hz]
  have right : (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*pairPolynomialCoefficient Q i (j-1) else 0) =
      (j : ℝ)*((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*(Q.choose j : ℝ) := by
    by_cases hj : 0 < j
    · rw [ite_eq_left hj]
      unfold pairPolynomialCoefficient
      rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      calc
        _ = ((i : ℝ)-((j : ℝ)-1))*(Q.choose i : ℝ)*
          (((Q : ℝ)-(j : ℝ)+1)*(Q.choose (j-1) : ℝ)) := by ring
        _ = _ := by rw [choose_lowering Q j hj (by omega)]; ring
    · have hz : j = 0 := by omega
      simp [hz]
  rw [left, right]
  unfold pairPolynomialCoefficient
  ring

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairCoefficient_choose (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairCoefficient Q p x y = if x.val+y.val = p+1 then
      ((x.val : ℝ)-(y.val : ℝ)) *
        Real.sqrt ((Q.choose x.val : ℝ)*(Q.choose y.val : ℝ) /
          (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))) else 0 := by
  have hx : (x.val.factorial : ℝ) ≠ 0 := by positivity
  have hy : (y.val.factorial : ℝ) ≠ 0 := by positivity
  have hpf : (p.factorial : ℝ) ≠ 0 := by positivity
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hQ)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  unfold pairCoefficient
  split_ifs
  · have hr : (((Q.descFactorial x.val : ℝ)*(Q.descFactorial y.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(x.val.factorial : ℝ)*(y.val.factorial : ℝ))) / 2 =
      (Q.choose x.val : ℝ)*(Q.choose y.val : ℝ)/(2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
        simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
        field_simp
    have hs := congrArg Real.sqrt hr
    rw [Real.sqrt_div (by positivity) (2 : ℝ)] at hs
    rw [← hs]
    ring
  · rfl

theorem pairCoefficient_polynomial_weight (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    pairCoefficient Q p x y * Real.sqrt (Q.choose x.val : ℝ) *
      Real.sqrt (Q.choose y.val : ℝ) * Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) =
        if x.val+y.val = p+1 then pairPolynomialCoefficient Q x.val y.val else 0 := by
  have hd : Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
    positivity
  rw [pairCoefficient_choose Q p hQ hp]
  split_ifs
  · rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    unfold pairPolynomialCoefficient
    have hx := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose x.val by positivity)
    have hy := Real.sq_sqrt (show (0 : ℝ) ≤ Q.choose y.val by positivity)
    field_simp
    calc
      _ = ((x.val : ℝ)-(y.val : ℝ)) * (Real.sqrt (Q.choose x.val : ℝ))^2 *
        (Real.sqrt (Q.choose y.val : ℝ))^2 := by ring
      _ = _ := by rw [hx,hy]
  · simp

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_PolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem rawPairState_lowering (Q p i j : ℕ) (hiQ : i ≤ Q) (hjQ : j ≤ Q) :
    lowerPair Q (rawPairState Q p) i j = (p+1 : ℕ)*rawPairState Q (p+1) i j := by
  by_cases h : i+j = p+2
  · have hx : 0 < i → i-1+j = p+1 := by omega
    have hy : 0 < j → i+(j-1) = p+1 := by omega
    have hr : ((i : ℝ)+(j : ℝ)-1) = (p+1 : ℕ) := by
      have hc := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at hc ⊢
      linarith
    have ha := pairPolynomialCoefficient_lowering Q i j hiQ hjQ
    rw [hr] at ha
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simpa [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc] using ha
    · simpa [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc] using ha
  · have hx : 0 < i → i-1+j ≠ p+1 := by omega
    have hy : 0 < j → i+(j-1) ≠ p+1 := by omega
    by_cases hi : 0 < i <;> by_cases hj : 0 < j
    · simp [lowerPair, rawPairState, h, hx hi, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hx hi, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hy hj, hi, hj, Nat.add_assoc]
    · simp [lowerPair, rawPairState, h, hi, hj, Nat.add_assoc]

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_NormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

theorem pairNormalization_pos (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2) :
    0 < pairNormalization Q p := by
  unfold pairNormalization
  apply Real.sqrt_pos.mpr
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hc : (0 : ℝ) < (2*Q-2).choose p := by exact_mod_cast Nat.choose_pos hp
  positivity

theorem pairNormalization_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    ((p : ℝ)+1) / pairNormalization Q p =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ)) / pairNormalization Q (p+1) := by
  have hdn := pairNormalization_pos Q (p+1) hQ (by omega)
  have hd := pairNormalization_pos Q p hQ (by omega)
  apply (div_eq_div_iff (ne_of_gt hd) (ne_of_gt hdn)).mpr
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq (2*Q-2) p)
  push_cast at hc
  have he : (((p : ℝ)+1)*pairNormalization Q (p+1))^2 =
      (Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p)^2 := by
    unfold pairNormalization
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    linear_combination (2*(Q : ℝ)*((p : ℝ)+1))*hc
  have hn₁ : 0 ≤ ((p : ℝ)+1)*pairNormalization Q (p+1) := by positivity
  have hn₂ : 0 ≤ Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*pairNormalization Q p := by positivity
  nlinarith only [he,hn₁,hn₂]

theorem lowerPair_div (Q : ℕ) (f : ℕ → ℕ → ℝ) (d : ℝ) (i j : ℕ) :
    lowerPair Q (fun i j => f i j / d) i j = lowerPair Q f i j / d := by
  unfold lowerPair
  split_ifs <;> ring

theorem normalizedPairState_lowering (Q p i j : ℕ) (hQ : 0 < Q)
    (hp : p < 2*Q-2) (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q p) i j =
      Real.sqrt (((p : ℝ)+1)*((2*Q-2-p : ℕ) : ℝ))*normalizedPairState Q (p+1) i j := by
  unfold normalizedPairState
  rw [lowerPair_div, rawPairState_lowering Q p i j hi hj]
  push_cast
  calc
    _ = (((p : ℝ)+1)/pairNormalization Q p)*rawPairState Q (p+1) i j := by ring
    _ = _ := by rw [pairNormalization_ratio Q p hQ hp]; ring

theorem normalizedPairState_eq_coefficients (Q p : ℕ) (hQ : 0 < Q)
    (hp : p ≤ 2*Q-2) (x y : Fin (Q+1)) :
    normalizedPairState Q p x.val y.val = pairCoefficient Q p x y *
      Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) := by
  unfold normalizedPairState rawPairState
  apply (div_eq_iff (ne_of_gt (pairNormalization_pos Q p hQ hp))).mpr
  exact (pairCoefficient_polynomial_weight Q p hQ hp x y).symm

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem sqrt_choose_step (A p : ℕ) (hp : p < A) :
    ladder A p * Real.sqrt (A.choose (p+1) : ℝ) =
      (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose (p+1) : ℝ))^2 =
      ((A-p : ℕ)*Real.sqrt (A.choose p : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have h₁ : 0 ≤ ladder A p * Real.sqrt (A.choose (p+1) : ℝ) := by
    exact mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have h₂ : 0 ≤ (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by positivity
  nlinarith

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_TensorLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

theorem ladder_weight_previous (Q : ℕ) (x : Fin (Q+1)) (hx : 0 < x.val) :
    ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ) =
      ((Q : ℝ)-x.val+1)*Real.sqrt (Q.choose (x.val-1) : ℝ) := by
  have h := sqrt_choose_step Q (x.val-1) (by omega)
  rw [show x.val-1+1=x.val by omega] at h
  have hc : ((Q-(x.val-1) : ℕ) : ℝ) = (Q : ℝ)-x.val+1 := by
    rw [Nat.cast_sub (by omega : x.val-1 ≤ Q),Nat.cast_sub (by omega : 1 ≤ x.val)]
    push_cast; ring
  rwa [hc] at h

theorem pairTensorLower_weight (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y * Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      lowerPair Q (normalizedPairState Q p) x.val y.val := by
  have hl :
      (if h : 0 < x.val then ladder Q (x.val-1)*pairCoefficient Q p ⟨x.val-1,by omega⟩ y else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < x.val then ((Q : ℝ)-x.val+1)*normalizedPairState Q p (x.val-1) y.val else 0) := by
    by_cases hx : 0 < x.val
    · rw [dite_eq_left hx,ite_eq_left hx,normalizedPairState_eq_coefficients Q p hQ hp ⟨x.val-1,by omega⟩ y]
      calc
        _ = pairCoefficient Q p ⟨x.val-1,by omega⟩ y * Real.sqrt (Q.choose y.val : ℝ)*
          (ladder Q (x.val-1)*Real.sqrt (Q.choose x.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q x hx]; ring
    · simp only [dite_eq_right hx,ite_eq_right hx,zero_mul]
  have hr :
      (if h : 0 < y.val then ladder Q (y.val-1)*pairCoefficient Q p x ⟨y.val-1,by omega⟩ else 0) *
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) =
      (if 0 < y.val then ((Q : ℝ)-y.val+1)*normalizedPairState Q p x.val (y.val-1) else 0) := by
    by_cases hy : 0 < y.val
    · rw [dite_eq_left hy,ite_eq_left hy,normalizedPairState_eq_coefficients Q p hQ hp x ⟨y.val-1,by omega⟩]
      calc
        _ = pairCoefficient Q p x ⟨y.val-1,by omega⟩ * Real.sqrt (Q.choose x.val : ℝ)*
          (ladder Q (y.val-1)*Real.sqrt (Q.choose y.val : ℝ)) := by ring
        _ = _ := by rw [ladder_weight_previous Q y hy]; ring
    · simp only [dite_eq_right hy,ite_eq_right hy,zero_mul]
  unfold pairTensorLower lowerPair
  rw [add_mul,add_mul,hl,hr]

theorem pairCoefficient_tensor_lowering (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (x y : Fin (Q+1)) :
    pairTensorLower Q p x y = ladder (2*Q-2) p * pairCoefficient Q (p+1) x y := by
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  apply (mul_right_cancel₀ hy)
  apply (mul_right_cancel₀ hx)
  have he := pairTensorLower_weight Q p hQ (by omega) x y
  rw [normalizedPairState_lowering Q p x.val y.val hQ hp (by omega) (by omega),
    normalizedPairState_eq_coefficients Q (p+1) hQ (by omega) x y] at he
  unfold ladder
  linear_combination he

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_HighestSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem highestRaw_zero (A B z : ℕ) :
    highestRaw A B z 0 = 1 / Real.sqrt (B.choose z : ℝ) := by
  simp [highestRaw]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_MatrixQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix

theorem occupation_matrix_quadratic_positive {I : Type*} [Fintype I]
    (Q : ℕ) (M : Matrix I I ℂ) (hM : M.PosSemidef) (v : I → Space Q) :
    0 ≤ (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)).re := by
  have he : (∑ i, ∑ j, M i j * occupationInner Q (v i) (v j)) =
      ∑ A : Finset (Fin (Q+1)), star (fun i => (occupationBasis Q).repr (v i) A) ⬝ᵥ
        (M*ᵥ (fun i => (occupationBasis Q).repr (v i) A)) := by
    simp only [occupationInner,dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j hj
    apply Finset.sum_congr rfl; intro A hA
    ring
  rw [he,Complex.re_sum]
  exact Finset.sum_nonneg (fun A hA => (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg _)).1)

theorem occupation_matrix_quadratic_factor {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (W : Matrix J I ℂ) (C : Matrix I I ℂ) (v : J → Space Q) :
    (∑ i, ∑ j, C i j * occupationInner Q
      (∑ a, star (W a i) • v a) (∑ b, star (W b j) • v b)) =
      ∑ a, ∑ b, (W*C*Wᴴ) a b * occupationInner Q (v a) (v b) := by
  simp_rw [occupationInner_sum_left,occupationInner_smul_left,star_star,
    occupationInner_sum_right,occupationInner_smul_right]
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.mul_sum,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a ha
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b hb
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  ring

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_FockHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem contractionForm_sum {I J : Type*} [Fintype I] [Fintype J] (Q : ℕ)
    (minus : I → Module.End ℂ (Space Q)) (M : J → Matrix I I ℂ) (x : Space Q) :
    contractionForm Q minus (∑ j, M j) x = ∑ j, contractionForm Q minus (M j) x := by
  simp only [contractionForm,Matrix.sum_apply,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourBodyCopy_coordinate (Q r D n : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q) :
    fourBodyCopy Q r D hr hA hB n (p,i) =
      ∑ b : Fin (genericCoupledWeight Q Q r+1), pairCoupledWedge Q r hr b.val i *
        ((-1 : ℝ)^(D-r) * genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
          (D-r) hA hB n (p,b)) := by
  simp only [fourBodyCopy,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensorPairInclusion,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,ite_mul,
    one_mul,zero_mul,pairCoupledInclusion,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_EnergyReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationNormSq_smul (Q : ℕ) (c : ℂ) (x : Space Q) :
    occupationNormSq Q (c • x) = ‖c‖^2 * occupationNormSq Q x := by
  simp [occupationNormSq,mul_pow,Finset.mul_sum]

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Spin_Basis2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericCoupledIndex_card (A B : ℕ) :
    Fintype.card (GenericCoupledIndex A B) = Fintype.card (SpinIndex A B) := by
  have hr : (Fintype.card (GenericCoupledIndex A B) : ℝ) =
      (Fintype.card (SpinIndex A B) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (min A B+1)) :
        ((genericCoupledWeight A B z.val+1 : ℕ) : ℝ) = A+B+1-2*(z.val : ℝ) := by
      have hz := z.isLt
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*z.val ≤ A+B)]
      push_cast
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rcases le_total A B with h | h
    · rw [Nat.min_eq_left h]; ring
    · rw [Nat.min_eq_right h]; ring
  exact_mod_cast hr

theorem genericCoupledBasis_isometry (A B : ℕ) :
    (genericCoupledBasis A B)ᵀ * genericCoupledBasis A B = 1 := by
  ext s t
  simp only [Matrix.mul_apply,Matrix.transpose_apply,genericCoupledBasis,Matrix.one_apply]
  by_cases h : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      genericUnitDescendant_norm A B s.1.val s.2.val _ _ (by have := s.2.isLt; omega)
  · rw [ite_eq_right h]
    apply genericUnitDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      exact h (by have he : n=m := Fin.ext hnm; subst m; rfl)
    · left
      intro he
      exact hzw (Fin.ext he)

theorem genericCoupledBasis_complete (A B : ℕ) :
    genericCoupledBasis A B * (genericCoupledBasis A B)ᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (m := GenericCoupledIndex A B) (n := SpinIndex A B) (R := ℝ) (genericCoupledIndex_card A B)).mp
    (genericCoupledBasis_isometry A B)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

theorem fourWedgeInclusion_factor (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    fourWedgeInclusion Q r D hr hA hB =
      ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
        (pairCoupledInclusion Q r hr).map Complex.ofReal) *
        physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB := by
  ext i n
  rw [fourWedgeInclusion,fourBodyCopy_coordinate]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_one,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kroneckerMap,
    Matrix.of_apply,Matrix.one_apply,ite_mul,one_mul,zero_mul,physicalCoupledInclusion,
    Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,genericCoupledInclusion,pairCoupledInclusion]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FockCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin
open scoped BigOperators Matrix Kronecker

theorem antisymmetric_exterior_sum (Q : ℕ) (f : SpinIndex Q Q → Space Q)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (a : SpinIndex Q Q → ℂ) :
    (∑ i, a i • f i) = ∑ i : WedgePairIndex Q, (a i.val-a i.val.swap) • f i.val := by
  apply (occupationBasis Q).repr.injective
  ext A
  have h := antisymmetric_ordered_sum Q
    (fun i => (occupationBasis Q).repr (f i) A) a (by
      intro i j; rw [hf,map_neg]; rfl)
  simpa only [map_sum,map_smul,Finset.sum_apply',Finsupp.smul_apply,smul_eq_mul,mul_comm] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_GenericPhysicalResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem physicalCoupledInclusion_complete (A B : ℕ) :
    (∑ z : Fin (min A B+1),
      physicalCoupledInclusion A B z.val (by omega) (by omega) *
        (physicalCoupledInclusion A B z.val (by omega) (by omega))ᴴ) = 1 := by
  have hc : (genericCoupledBasis A B).map Complex.ofReal *
      ((genericCoupledBasis A B).map Complex.ofReal)ᴴ = 1 := by
    ext i j
    have h := congrArg Complex.ofReal (congrFun (congrFun (genericCoupledBasis_complete A B) i) j)
    simpa only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
      Complex.star_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul,Matrix.one_apply,
      apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using h
  rw [← hc]
  ext i j
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.map_apply,
    Fintype.sum_sigma,physicalCoupledInclusion,Matrix.smul_apply,smul_eq_mul,
    genericCoupledInclusion,genericCoupledBasis]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro n hn
  have hp : ((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)=1 := by
    simp only [star_pow,star_neg,star_one,← mul_pow]
    norm_num
  simp only [star_mul]
  calc
    _ = (((-1 : ℂ)^z.val)*star ((-1 : ℂ)^z.val)) *
      ((genericUnitDescendant A B z.val (by omega) (by omega) n.val i : ℂ)*
        star (genericUnitDescendant A B z.val (by omega) (by omega) n.val j : ℂ)) := by ring
    _ = _ := by rw [hp,one_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TargetResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem fourPairEmbedding_resolution (Q r : ℕ) (hr : r ≤ Q) :
    fourPairEmbedding Q r hr*(fourPairEmbedding Q r hr)ᴴ =
      ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
        fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega) *
          (fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega))ᴴ := by
  let F : Matrix (FourWedgeIndex Q) (SpinIndex (2*Q-2) (genericCoupledWeight Q Q r)) ℂ :=
    fourPairEmbedding Q r hr
  have hA (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ 2*Q-2 :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_left _ _)
  have hB (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ genericCoupledWeight Q Q r :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_right _ _)
  have hp (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) :
      fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z) *
        (fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z))ᴴ =
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
    rw [fourWedgeInclusion_factor]
    let v : {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r} →
        Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := fun k =>
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2)ᴴ
    exact congrArg v (show (⟨r+z.val-r,by constructor <;> omega⟩ :
      {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r}) = ⟨z.val,by constructor <;> omega⟩
      from Subtype.ext (Nat.add_sub_cancel_left r z.val))
  change F*Fᴴ = _
  calc
    _ = F*(∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z) *
        (physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ)*Fᴴ := by
      rw [physicalCoupledInclusion_complete,Matrix.mul_one]
    _ = ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := Finset.sum_congr rfl (fun z hz => (hp z).symm)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_TargetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix ComplexOrder

theorem castSpinColumns_mul_adjoint {I : Type*} (m n : ℕ) (h : m=n)
    (W : Matrix I (Fin (m+1)) ℂ) :
    castSpinColumns m n h W * (castSpinColumns m n h W)ᴴ = W*Wᴴ := by
  subst n
  rfl

theorem fourWedgeProjector_congr (Q r D E : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hA' : E-r ≤ 2*Q-2) (hB' : E-r ≤ genericCoupledWeight Q Q r) (h : D=E) :
    fourWedgeInclusion Q r D hr hA hB*(fourWedgeInclusion Q r D hr hA hB)ᴴ =
      fourWedgeInclusion Q r E hr hA' hB'*(fourWedgeInclusion Q r E hr hA' hB')ᴴ := by
  subst E
  rfl

theorem retainedFirst_projector (Q D : ℕ) (hQ : D+2 ≤ Q) (hD : 1 ≤ D) :
    retainedFourInclusion Q D hQ (firstOddPairLabel D hD) *
      (retainedFourInclusion Q D hQ (firstOddPairLabel D hD))ᴴ =
    fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega) *
      (fourWedgeInclusion Q 1 D (by omega) (by omega) (by unfold genericCoupledWeight; omega))ᴴ := by
  unfold retainedFourInclusion
  rw [castSpinColumns_mul_adjoint]
  rfl

theorem contractionForm_projector_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    0 ≤ (contractionForm Q L (W*Wᴴ) x).re :=
  occupation_matrix_quadratic_positive Q _ (Matrix.posSemidef_self_mul_conjTranspose W) _

theorem sum_fin_castLE_le (m n : ℕ) (hmn : m ≤ n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∑ i : Fin m, f (Fin.castLE hmn i)) ≤ ∑ i : Fin n, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image (Fin.castLE hmn), f i := by
      rw [Finset.sum_image]
      intro i hi j hj he
      exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i hi hnot => hf i)

theorem retainedFourTarget_le_full (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    retainedFourTarget Q hQ x ≤
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
  let f (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q 1)+1)) : ℝ :=
    (contractionForm Q (sourceFourFamilyEnd Q)
      (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega) *
        (fourWedgeInclusion Q 1 (1+z.val) (by omega) (by omega) (by omega))ᴴ) x).re
  have hn : 23 ≤ min (2*Q-2) (genericCoupledWeight Q Q 1)+1 := by
    unfold genericCoupledWeight
    omega
  have hs := sum_fin_castLE_le 23 _ hn f (fun z => contractionForm_projector_nonneg Q _ _ x)
  have hl : (∑ d : Fin 23, f (Fin.castLE hn d)) = retainedFourTarget Q hQ x := by
    unfold retainedFourTarget
    apply Finset.sum_congr rfl
    intro d hd
    rw [retainedFirst_projector]
    dsimp only [f,Fin.val_castLE]
    exact congrArg (fun M => (contractionForm Q (sourceFourFamilyEnd Q) M x).re)
      (fourWedgeProjector_congr Q 1 (1+d.val) (d.val+1) (by omega)
        (by omega) (by unfold genericCoupledWeight; omega)
        (by omega) (by unfold genericCoupledWeight; omega) (Nat.add_comm 1 d.val))
  have hr : (∑ z, f z) =
      (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q (by omega)) x).re := by
    rw [fourPairTargetMatrix,fourPairEmbedding_resolution,contractionForm_sum,Complex.re_sum]
  rwa [hl,hr] at hs

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Pair_CoupledOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem highestUnit_one_zero (Q : ℕ) (hQ : 1 ≤ Q) :
    highestUnit Q Q 1 0 = 1 / Real.sqrt 2 := by
  have hn := highestUnit_norm Q Q 1 hQ hQ
  have hr := highestUnit_reverse Q 1 0 (by omega)
  norm_num at hr
  simp only [show 1+1=2 by omega,Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at hn
  rw [hr] at hn
  have hp : 0 < highestUnit Q Q 1 0 := by
    rw [highestUnit,highestRaw_zero]
    have hqr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    simp only [Nat.choose_one_right]
    exact div_pos (by positivity) (highestNorm_pos Q Q 1 hQ hQ)
  have ht : 0 < (1 : ℝ)/Real.sqrt 2 := by positivity
  have hs : ((1 : ℝ)/Real.sqrt 2)^2 = 1/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith only [hn,hp,ht,hs]

theorem pairCoupledTensor_one_zero (Q : ℕ) (hQ : 1 ≤ Q) (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ 0 i = pairCoefficient Q 0 i.1 i.2 := by
  rw [pairCoupledTensor,genericUnitDescendant_zero]
  simp only [pow_one,Pi.smul_apply,smul_eq_mul,neg_one_mul]
  by_cases hi : i.1.val+i.2.val=1
  · let p : Fin 2 := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex Q Q 1 hQ hQ p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    have hv : genericHighest Q Q 1 hQ hQ i = highestUnit Q Q 1 i.1.val := by
      change extendWeightSlice Q Q 1 hQ hQ _ i = _
      rw [he,extendWeightSlice_at]; rfl
    rw [hv]
    have hqr : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    rcases (show i.1.val=0 ∨ i.1.val=1 by omega) with h0 | h1
    · have hj : i.2.val=1 := by omega
      simp [pairCoefficient,h0,hj,highestUnit_one_zero Q hQ,hqr,div_eq_mul_inv]
    · have hj : i.2.val=0 := by omega
      have hr := highestUnit_reverse Q 1 0 (by omega)
      norm_num at hr
      rw [h1,hr,highestUnit_one_zero Q hQ]
      simp [pairCoefficient,h1,hj,hqr]
  · have hv : genericHighest Q Q 1 hQ hQ i = 0 :=
      extendWeightSlice_off Q Q 1 hQ hQ _ i hi
    simp [hv,pairCoefficient,hi]

theorem pairCoupledTensor_lowering (Q r n : ℕ) (hr : r ≤ Q)
    (hn : n < genericCoupledWeight Q Q r) :
    (totalRaise Q Q)ᵀ *ᵥ pairCoupledTensor Q r hr n =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q r : ℝ)-n)) •
        pairCoupledTensor Q r hr (n+1) := by
  rw [pairCoupledTensor,Matrix.mulVec_smul,genericUnitDescendant_lowering Q Q r n hr hr hn]
  exact smul_comm _ _ _

theorem pairCoupledTensor_one (Q n : ℕ) (hQ : 1 ≤ Q) (hn : n ≤ 2*Q-2)
    (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ n i = pairCoefficient Q n i.1 i.2 := by
  induction n generalizing i with
  | zero => exact pairCoupledTensor_one_zero Q hQ i
  | succ n ih =>
    have hcw : genericCoupledWeight Q Q 1 = 2*Q-2 := by unfold genericCoupledWeight; omega
    have hlt : n < genericCoupledWeight Q Q 1 := by rw [hcw]; omega
    have hreal : (n : ℝ) < genericCoupledWeight Q Q 1 := by exact_mod_cast hlt
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (pairCoupledTensor_lowering Q 1 n hQ hlt) i
    have hf : pairCoupledTensor Q 1 hQ n = fun j => pairCoefficient Q n j.1 j.2 := by
      funext j; exact ih (by omega) j
    rw [hf] at he
    change (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n))*
        pairCoupledTensor Q 1 hQ (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have hc := pairCoefficient_tensor_lowering Q n (by omega) (by omega) i.1 i.2
    have hl : pairTensorLower Q n i.1 i.2 =
        (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) := by
      rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      unfold pairTensorLower; split_ifs <;> ring
    rw [hcw] at he hd
    have hw : ladder (2*Q-2) n = Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n)) := by
      unfold ladder
      rw [Nat.cast_sub (by omega : n ≤ 2*Q-2)]
    rw [hw] at hc
    have he' : pairTensorLower Q n i.1 i.2 =
      Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n))*pairCoupledTensor Q 1 hQ (n+1) i := by
      rw [hl,totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      exact he
    exact (mul_left_cancel₀ hd) (he'.symm.trans hc)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_PairTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix Kronecker

theorem pairCoupledOne_contract (Q : ℕ) (hQ : 1 ≤ Q)
    (n : Fin (genericCoupledWeight Q Q 1+1)) (x : Space Q) :
    (∑ i : WedgePairIndex Q, (pairCoupledInclusion Q 1 hQ i n : ℂ) •
      annihilate i.val.2 (annihilate i.val.1 x)) = sourcePairEnd Q n.val x := by
  have hf (i j : Fin (Q+1)) : annihilate i (annihilate j x) =
      -annihilate j (annihilate i x) := by
    have h := LinearMap.congr_fun (annihilate_anticommute i j) x
    exact eq_neg_of_add_eq_zero_left h
  have he := antisymmetric_exterior_sum Q
    (fun i => annihilate i.2 (annihilate i.1 x)) hf
    (fun i => ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ))
  have hn : n.val ≤ 2*Q-2 := by have := n.isLt; unfold genericCoupledWeight at this; omega
  have hc (i : WedgePairIndex Q) :
      ((pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 : ℝ) : ℂ) -
        ((pairCoefficient Q n.val i.val.2 i.val.1 / Real.sqrt 2 : ℝ) : ℂ) =
      (pairCoupledInclusion Q 1 hQ i n : ℂ) := by
    rw [pairCoefficient_swap Q n.val i.val.1 i.val.2]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hreal : pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 -
        -pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 =
      Real.sqrt 2*pairCoefficient Q n.val i.val.1 i.val.2 := by
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [← Complex.ofReal_sub,hreal]
    simp only [pairCoupledInclusion,pairCoupledWedge,tensorToWedgePair,pairCoupledTensor_one Q n.val hQ hn]
  have he' := he.trans (Finset.sum_congr rfl (fun i hi =>
    congrArg (fun c : ℂ => c • annihilate i.val.2 (annihilate i.val.1 x)) (hc i)))
  calc
    _ = ∑ i : SpinIndex Q Q, ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ) •
        annihilate i.2 (annihilate i.1 x) := he'.symm
    _ = _ := by
      simp only [sourcePairEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,
        Module.End.mul_apply,Fintype.sum_prod_type]

theorem fourPairEmbedding_contract (Q : ℕ) (hQ : 1 ≤ Q)
    (j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1)) (x : Space Q) :
    (∑ i : FourWedgeIndex Q, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x) =
      sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x) := by
  simp only [fourPairEmbedding,Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,
    Matrix.map_apply,apply_ite,star_zero,Complex.star_def,Complex.conj_ofReal,
    ite_mul,one_mul,zero_mul,ite_smul,zero_smul,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact pairCoupledOne_contract Q hQ j.2 (sourcePairEnd Q j.1.val x)

theorem contractionForm_factor_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    contractionForm Q L (W*Wᴴ) x =
      (∑ j, (occupationNormSq Q (∑ i, star (W i j) • L i x) : ℂ)) := by
  have h := occupation_matrix_quadratic_factor Q W (1 : Matrix J J ℂ) (fun i => L i x)
  rw [Matrix.mul_one] at h
  change (∑ a, ∑ b, (W*Wᴴ) a b * occupationInner Q (L a x) (L b x)) = _
  rw [← h]
  simp [Matrix.one_apply,occupationInner_self]

theorem fourPairTargetMatrix_Fock (Q : ℕ) (hQ : 1 ≤ Q) (x : Space Q) :
    (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q hQ) x).re =
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  rw [fourPairTargetMatrix,contractionForm_factor_one]
  simp only [Complex.re_sum,Complex.ofReal_re]
  have he : (∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
      occupationNormSq Q (∑ i, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x)) =
      ∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
        occupationNormSq Q (sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x)) :=
    Finset.sum_congr rfl (fun j hj => congrArg (occupationNormSq Q) (fourPairEmbedding_contract Q hQ j x))
  rw [he,Fintype.sum_prod_type]
  have hw : genericCoupledWeight Q Q 1=2*Q-2 := by unfold genericCoupledWeight; omega
  apply Finset.sum_congr rfl
  intro p hp
  exact Fintype.sum_equiv (finCongr (congrArg (fun m => m+1) hw)) _ _ (fun q => rfl)

theorem sourceA4Form_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤
      (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
      (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := retainedFourTarget_le_full Q hQ x
  rw [fourPairTargetMatrix_Fock] at ht
  have hb := sourceA4Form_retained_bound Q hQ x
  linarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_NormalSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem pair_annihilate_create_inner (Q p : ℕ) (x y : Space Q) :
    occupationInner Q x (sourcePairCreateEnd Q p y) =
      occupationInner Q (sourcePairEnd Q p x) y := by
  have h := congrArg star (pairCreate_pair_adjoint Q
    (fun i j => ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ)) y x)
  simpa only [occupationInner_star,sourcePairCreateEnd,sourcePairEnd] using h

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_SevenSquareAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Rotation Spin MeasureTheory
open scoped BigOperators Matrix

theorem sourceKForm_nonneg (Q : ℕ) (hQ : 15 ≤ Q) (x : Space Q) : 0 ≤ sourceKForm Q hQ x := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro g
  apply List.sum_nonneg
  intro a ha
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp ha
  exact occupationNormSq_nonneg Q _

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_PhysicalFockGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators Topology

theorem physical_fock_budget_eventually :
    ∀ᶠ Q : ℕ in atTop, ∃ hQ : 25 ≤ Q, ∀ x : Space Q,
      sourceKForm Q (by omega) x +
        (1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-averagedFourTransferError Q) *
          sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_threeBody_budget_eventually,eventually_ge_atTop 25] with Q h3 h25
  obtain ⟨h15,h3⟩ := h3
  refine ⟨h25,fun x => ?_⟩
  have h3x := h3 x
  change sourceA3Form Q x-deltaFormula Q*sourceFockEnergy Q x ≤ _ at h3x
  have h4 := sourceA4Form_bound Q h25 x
  have hs := sourceFockHamiltonian_normal_square Q (by omega) x
  rw [sourceKForm_decomposition Q h25]
  nlinarith

theorem physical_fock_square_eventually :
    ∀ᶠ Q : ℕ in atTop, ∀ x : Space Q,
      (1/100 : ℝ)*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  filter_upwards [physical_fock_budget_eventually,
    eventual_scalar_budget averagedFourTransferError averagedFourTransferError_tendsto] with Q h hs
  obtain ⟨hQ,h⟩ := h
  intro x
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  have hm := mul_le_mul_of_nonneg_right hs hE
  have hk := sourceKForm_nonneg Q (by omega) x
  have hx := h x
  linarith

theorem physical_fock_square_uniform :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      (1/100 : ℝ)*sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x) := by
  obtain ⟨q,hq⟩ := eventually_atTop.mp physical_fock_square_eventually
  exact ⟨max 25 q,le_max_left _ _,fun Q hQ => hq Q (le_trans (le_max_right _ _) hQ)⟩

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_EigenvalueGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Filter
open scoped BigOperators

theorem sourceFockHamiltonian_symmetric (Q : ℕ) (x y : Space Q) :
    occupationInner Q (sourceFockHamiltonian Q x) y =
      occupationInner Q x (sourceFockHamiltonian Q y) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply,
    occupationInner_sum_left,occupationInner_sum_right,pair_annihilate_create_inner]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairCreate_pair_adjoint Q _ _ _

theorem sourceFock_eigen_energy (Q : ℕ) (x : Space Q) (a : ℝ)
    (he : sourceFockHamiltonian Q x=(a : ℂ) • x) :
    sourceFockEnergy Q x=a*occupationNormSq Q x := by
  have h := sourceFockHamiltonian_quadratic Q x
  rw [he,occupationInner_smul_left,occupationInner_self] at h
  simp only [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h.symm

theorem sourceFock_eigen_nonneg (Q : ℕ) (x : Space Q) (hx : x≠0) (a : ℝ)
    (he : sourceFockHamiltonian Q x=(a : ℂ) • x) : 0 ≤ a := by
  have hn : 0 < occupationNormSq Q x :=
    lt_of_le_of_ne (occupationNormSq_nonneg Q x) (Ne.symm (mt (occupationNormSq_eq_zero Q x).mp hx))
  have hE : 0 ≤ sourceFockEnergy Q x := Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)
  rw [sourceFock_eigen_energy Q x a he] at hE
  exact nonneg_of_mul_nonneg_left hE hn

theorem physical_fock_eigenvalue_gap_uniform :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q, x≠0 → ∀ a : ℝ,
      sourceFockHamiltonian Q x=(a : ℂ) • x → a=0 ∨ (1/100 : ℝ) ≤ a := by
  obtain ⟨Q₀,h25,h⟩ := physical_fock_square_uniform
  refine ⟨Q₀,h25,fun Q hQ x hx a he => ?_⟩
  have hn : 0 < occupationNormSq Q x :=
    lt_of_le_of_ne (occupationNormSq_nonneg Q x) (Ne.symm (mt (occupationNormSq_eq_zero Q x).mp hx))
  have ha := sourceFock_eigen_nonneg Q x hx a he
  have hs := h Q hQ x
  rw [sourceFock_eigen_energy Q x a he,he,occupationNormSq_smul] at hs
  have hnorm : ‖(a : ℂ)‖^2=a^2 := by simp
  rw [hnorm] at hs
  have hs' : (1/100 : ℝ)*a ≤ a^2 := by nlinarith
  by_cases hz : a=0
  · exact Or.inl hz
  · right
    have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    nlinarith

end Laughlin.Fock

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_SpectralKernelDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators InnerProductSpace

theorem spectral_kernel_distance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : Module.End ℂ E) (hT : T.IsSymmetric) (c : ℝ) (hc : 0 ≤ c)
    (hgap : ∀ v : E, v≠0 → ∀ a : ℝ, T v=(a : ℂ) • v → a=0 ∨ c≤a)
    (x : E) : ∃ y : E, T y=0 ∧ c*‖x-y‖^2 ≤ (inner ℂ (T x) x).re := by
  classical
  let d := Module.finrank ℂ E
  let b := hT.eigenvectorBasis (n := d) rfl
  let a := hT.eigenvalues (n := d) rfl
  let z : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun i => if a i=0 then b.repr x i else 0)
  let y := b.repr.symm z
  have hyrepr (i : Fin d) : b.repr y i = if a i=0 then b.repr x i else 0 := by
    simp [y,z]
  have hdiag (v : E) (i : Fin d) : b.repr (T v) i = (a i : ℂ)*b.repr v i :=
    hT.eigenvectorBasis_apply_self_apply rfl v i
  have hy : T y=0 := by
    apply b.repr.injective
    ext i
    rw [hdiag,hyrepr]
    by_cases hi : a i=0 <;> simp [hi]
  have hnorm : ‖x-y‖^2 = ∑ i : Fin d, if a i=0 then 0 else ‖b.repr x i‖^2 := by
    rw [← b.repr.norm_map,EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [map_sub,PiLp.sub_apply,hyrepr]
    by_cases ha : a i=0 <;> simp [ha]
  have he : (inner ℂ (T x) x).re = ∑ i : Fin d, a i*‖b.repr x i‖^2 := by
    rw [← b.repr.inner_map_map,PiLp.inner_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiag]
    simp only [RCLike.inner_apply,map_mul,Complex.conj_ofReal]
    have hn : (star (b.repr x i)*b.repr x i).re = ‖b.repr x i‖^2 := by
      change (((starRingEnd ℂ) (b.repr x i))*b.repr x i).re = _
      rw [← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.ofReal_re,Complex.normSq_eq_norm_sq]
    have hh : b.repr x i * ((a i : ℂ) * star (b.repr x i)) =
        (a i : ℂ)*(star (b.repr x i)*b.repr x i) := by ring
    change (b.repr x i * ((a i : ℂ) * star (b.repr x i))).re = _
    rw [hh,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hn]
  refine ⟨y,hy,?_⟩
  rw [hnorm,he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb : b i ≠ 0 := b.orthonormal.ne_zero i
  have hgi := hgap (b i) hb (a i) (hT.apply_eigenvectorBasis rfl i)
  by_cases ha : a i=0
  · simp [ha]
  · rw [ite_eq_right ha]
    exact mul_le_mul (hgi.resolve_left ha) le_rfl (sq_nonneg _)
      (hc.trans (hgi.resolve_left ha))

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Fock_SpectralDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

theorem occupationEuclidean_inner (Q : ℕ) (x y : Space Q) :
    inner ℂ (occupationEuclidean Q x) (occupationEuclidean Q y) = occupationInner Q x y := by
  simp only [occupationEuclidean,LinearEquiv.trans_apply,PiLp.inner_apply,
    Module.Basis.equivFun_apply,occupationInner]
  apply Finset.sum_congr rfl
  intro A hA
  change (occupationBasis Q).repr y A * star ((occupationBasis Q).repr x A) = _
  ring

theorem occupationEuclidean_norm (Q : ℕ) (x : Space Q) :
    ‖occupationEuclidean Q x‖^2 = occupationNormSq Q x := by
  have h := occupationEuclidean_inner Q x x
  rw [inner_self_eq_norm_sq_to_K,occupationInner_self] at h
  change (‖occupationEuclidean Q x‖ : ℂ)^2 = (occupationNormSq Q x : ℂ) at h
  exact_mod_cast h

theorem euclideanFockHamiltonian_apply (Q : ℕ) (x : Space Q) :
    euclideanFockHamiltonian Q (occupationEuclidean Q x) =
      occupationEuclidean Q (sourceFockHamiltonian Q x) := by
  simp [euclideanFockHamiltonian]

theorem euclideanFockHamiltonian_symmetric (Q : ℕ) :
    (euclideanFockHamiltonian Q).IsSymmetric := by
  intro x y
  obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective x
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective y
  simp only [euclideanFockHamiltonian_apply,occupationEuclidean_inner]
  exact sourceFockHamiltonian_symmetric Q u v

theorem physical_fock_kernel_distance_uniform_oai :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      ∃ y : Space Q, sourceFockHamiltonian Q y=0 ∧
        (1/100 : ℝ)*occupationNormSq Q (x-y) ≤ sourceFockEnergy Q x := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_eigenvalue_gap_uniform
  refine ⟨Q₀,h25,fun Q hQ x => ?_⟩
  have hg : ∀ v : EuclideanSpace ℂ (Finset (Fin (Q+1))), v≠0 → ∀ a : ℝ,
      euclideanFockHamiltonian Q v=(a : ℂ) • v → a=0 ∨ (1/100 : ℝ)≤a := by
    intro v hv a he
    obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective v
    apply hgap Q hQ u (by intro hu; simp [hu] at hv) a
    apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_smul] using he
  obtain ⟨z,hz,hb⟩ := spectral_kernel_distance (euclideanFockHamiltonian Q)
    (euclideanFockHamiltonian_symmetric Q) (1/100) (by norm_num) hg (occupationEuclidean Q x)
  obtain ⟨y,rfl⟩ := (occupationEuclidean Q).surjective z
  refine ⟨y,?_,?_⟩
  · apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_zero] using hz
  · rw [← map_sub,occupationEuclidean_norm,euclideanFockHamiltonian_apply,
      occupationEuclidean_inner,sourceFockHamiltonian_quadratic,Complex.ofReal_re] at hb
    exact hb

end Laughlin.Fock

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Fock.physical_fock_kernel_distance_uniform_oai := @OAI.Laughlin.Fock.physical_fock_kernel_distance_uniform_oai
