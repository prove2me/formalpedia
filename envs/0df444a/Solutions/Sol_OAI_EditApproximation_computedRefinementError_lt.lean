-- Prove2me | solution 1 for OAI.EditApproximation.computedRefinementError_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:23:52.860109+00:00
-- url     : https://prove2.me/submissions/63ee84e1-51ba-4749-b971-129305138df0

import Mathlib
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_OAIQ361V3Ea001

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

/-- The fourth-root scale has ample polynomial slack. -/
theorem fourth_root_polynomial_slack {ell H quarterRoot : ℝ}
    (hell : 1 ≤ ell) (hH : ell ^ 20000 ≤ H)
    (hroot : 0 ≤ quarterRoot) (hrootPower : quarterRoot ^ 4 = H) :
    ell ^ 5000 ≤ quarterRoot := by
  apply (pow_le_pow_iff_left₀ (pow_nonneg (zero_le_one.trans hell) 5000)
    hroot (by decide : 4 ≠ 0)).mp
  rw [← pow_mul, hrootPower]
  exact hH

/-- The five explicit terms in Section 8 are collectively below `1/ell`.
Here `quarterRoot = H^(1/4)` and `q = p_*+21`. The hypotheses are small
consequences of the manuscript's large-input cutoff, not asymptotic
notation or a presumed error bound. -/
theorem refinement_error_envelope {ell H quarterRoot q : ℝ}
    (hell : 64000000000000 ≤ ell) (hH : ell ^ 2 ≤ H)
    (hroot : ell ^ 4 ≤ quarterRoot) (hq : 0 ≤ q) (hqSquare : q ^ 2 ≤ ell) :
    52000 / H ^ 18 + 8040000 * ell ^ 4 / quarterRoot ^ 2 +
        200 * ell / quarterRoot + 1000000 * q / ell ^ 2 + 13200 / H ^ 2 < 1 / ell := by
  have hellpos : 0 < ell := by linarith
  have hellone : 1 ≤ ell := by linarith
  have hHone : 1 ≤ H := (one_le_pow₀ hellone).trans hH
  have hHpos : 0 < H := by linarith
  have hrootpos : 0 < quarterRoot := (pow_pos hellpos 4).trans_le hroot
  have hell2 : ell ≤ ell ^ 2 := by nlinarith
  have hHell : ell ≤ H := hell2.trans hH
  have hH18 : H ≤ H ^ 18 := by
    simpa only [pow_one] using pow_le_pow_right₀ hHone (by decide : 1 ≤ 18)
  have ht1 : 52000 / H ^ 18 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hHpos 18) (by positivity : 0 < 8 * ell)).2
    have hsize : 416000 * ell ≤ ell ^ 2 := by nlinarith
    nlinarith
  have hrootSquare : ell ^ 8 ≤ quarterRoot ^ 2 := by
    have hsq := pow_le_pow_left₀ (pow_nonneg hellpos.le 4) hroot 2
    simpa only [← pow_mul] using hsq
  have hell5 : ell ^ 5 ≤ ell ^ 7 := pow_le_pow_right₀ hellone (by decide : 5 ≤ 7)
  have hsecondPower : 64320000 * ell ^ 5 ≤ ell ^ 8 := by
    have hcoef : 64320000 ≤ ell := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hellpos.le 7)
    have hfirst := mul_le_mul_of_nonneg_left hell5 (by norm_num : (0 : ℝ) ≤ 64320000)
    nlinarith [show ell * ell ^ 7 = ell ^ 8 by ring]
  have ht2 : 8040000 * ell ^ 4 / quarterRoot ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hrootpos 2) (by positivity : 0 < 8 * ell)).2
    have hid : (8040000 * ell ^ 4) * (8 * ell) = 64320000 * ell ^ 5 := by ring
    rw [hid, one_mul]
    exact hsecondPower.trans hrootSquare
  have hsmallPower : 1600 * ell ^ 2 ≤ ell ^ 4 := by
    have hcoef : (1600 : ℝ) ≤ ell ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ell)
    nlinarith [show ell ^ 2 * ell ^ 2 = ell ^ 4 by ring]
  have ht3 : 200 * ell / quarterRoot ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ hrootpos (by positivity : 0 < 8 * ell)).2
    nlinarith [hsmallPower.trans hroot]
  have hqScale : 8000000 * q ≤ ell := by
    have hsq : (8000000 * q) ^ 2 ≤ ell ^ 2 := by
      have ha := mul_le_mul_of_nonneg_left hqSquare (by norm_num : (0 : ℝ) ≤ 8000000 ^ 2)
      have hb := mul_le_mul_of_nonneg_right hell hellpos.le
      nlinarith
    exact (sq_le_sq₀ (by positivity : 0 ≤ 8000000 * q) hellpos.le).mp hsq
  have ht4 : 1000000 * q / ell ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hellpos 2) (by positivity : 0 < 8 * ell)).2
    have hmul := mul_le_mul_of_nonneg_right hqScale hellpos.le
    nlinarith
  have ht5 : 13200 / H ^ 2 ≤ 1 / (8 * ell) := by
    apply (div_le_div_iff₀ (pow_pos hHpos 2) (by positivity : 0 < 8 * ell)).2
    have hsq := pow_le_pow_left₀ hellpos.le hHell 2
    have hsize : 105600 * ell ≤ ell ^ 2 := by nlinarith
    nlinarith
  have hstrict : 5 * (1 / (8 * ell)) < 1 / ell := by
    rw [mul_one_div]
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * ell) hellpos).2
    nlinarith
  linarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

theorem coarseExponent_shift_square (ell : ℕ) (hell : 1764 ≤ ell) :
    ((coarseExponent ell : ℝ) + 21) ^ 2 ≤ ell := by
  have hp : (coarseExponent ell : ℝ) ^ 4 ≤ ell := by
    exact_mod_cast (coarseExponent_fourth_power ell).trans (Nat.log_le_self 2 ell)
  have hellR : (1764 : ℝ) ≤ ell := by exact_mod_cast hell
  have hscaled : (4 * (coarseExponent ell : ℝ) ^ 2) ^ 2 ≤ (ell : ℝ) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 16)
    have hb : 16 * (ell : ℝ) ≤ (ell : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hquarter : 4 * (coarseExponent ell : ℝ) ^ 2 ≤ ell :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg ell)).mp hscaled
  nlinarith [sq_nonneg ((coarseExponent ell : ℝ) - 21)]

theorem heightQuarterRoot_fourth_power (N : ℕ) :
    heightQuarterRoot N ^ 4 = inputHeight N := by
  unfold heightQuarterRoot
  rw [show (Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 4 =
    ((Real.sqrt (Real.sqrt (inputHeight N : ℝ))) ^ 2) ^ 2 by ring]
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_positive_counts (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    0 < (integerParameters N).T ∧ 0 < (integerParameters N).S := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpow := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans (inputHeight_polynomial_slack N hN hell)
  have hpowN : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpow
  have hellpos : 0 < inputSmallLog N := Nat.two_pow_pos _
  exact ⟨Nat.two_pow_pos _, Nat.div_pos hpowN (pow_pos hellpos 2)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact divisibility and power bounds for the computed time counts. -/

namespace EditApproximation

theorem computed_refinement_count_exact (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (integerParameters N).S * inputSmallLog N ^ 2 = inputHeight N := by
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (Nat.one_le_two_pow (n := smallLogExponent N))
  have hpowR := (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans
    (inputHeight_polynomial_slack N hN hell)
  have hpow : inputSmallLog N ^ 2 ≤ inputHeight N := by exact_mod_cast hpowR
  have hexponent : smallLogExponent N * 2 ≤ heightExponent N := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using hpow
  have hdiv : inputSmallLog N ^ 2 ∣ inputHeight N := by
    simpa only [inputSmallLog, inputHeight, ← pow_mul] using Nat.pow_dvd_pow 2 hexponent
  exact Nat.div_mul_cancel hdiv

theorem computed_warmup_count_power (N : ℕ) :
    inputHeight N ^ 3 ≤ (integerParameters N).T ^ 4 ∧
      (integerParameters N).T ^ 4 ≤ 16 * inputHeight N ^ 3 := by
  let k := heightExponent N
  have hlow : 3 * k ≤ ((3 * k + 3) / 4) * 4 := by omega
  have hhigh : ((3 * k + 3) / 4) * 4 ≤ 3 * k + 4 := by omega
  constructor
  · simpa only [integerParameters, inputHeight, ← pow_mul, k, mul_comm] using
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlow
  · have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hhigh
    simpa only [integerParameters, inputHeight, ← pow_mul, pow_add, k,
      show (2 : ℕ) ^ 4 = 16 by norm_num, mul_comm] using h

theorem computed_warmup_count_root (N : ℕ) :
    heightQuarterRoot N ^ 3 ≤ ((integerParameters N).T : ℝ) ∧
      ((integerParameters N).T : ℝ) ≤ 2 * heightQuarterRoot N ^ 3 := by
  have hroot : 0 ≤ heightQuarterRoot N := Real.sqrt_nonneg _
  have hT : (0 : ℝ) ≤ (integerParameters N).T := Nat.cast_nonneg _
  have hpower := computed_warmup_count_power N
  have hlow : (inputHeight N : ℝ) ^ 3 ≤ ((integerParameters N).T : ℝ) ^ 4 := by exact_mod_cast hpower.1
  have hhigh : ((integerParameters N).T : ℝ) ^ 4 ≤ 16 * (inputHeight N : ℝ) ^ 3 := by exact_mod_cast hpower.2
  have hrootPower := heightQuarterRoot_fourth_power N
  constructor
  · apply (pow_le_pow_iff_left₀ (pow_nonneg hroot 3) hT (by decide : 4 ≠ 0)).1
    calc
      (heightQuarterRoot N ^ 3) ^ 4 = (inputHeight N : ℝ) ^ 3 := by
        rw [← pow_mul, Nat.mul_comm 3 4, pow_mul, hrootPower]
      _ ≤ _ := hlow
  · apply (pow_le_pow_iff_left₀ hT (mul_nonneg (by norm_num) (pow_nonneg hroot 3)) (by decide : 4 ≠ 0)).1
    calc
      _ ≤ 16 * (inputHeight N : ℝ) ^ 3 := hhigh
      _ = (2 * heightQuarterRoot N ^ 3) ^ 4 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm 3 4, pow_mul, hrootPower]
        norm_num

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementErrorTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit estimates for the actual four parts of the refinement error. -/

namespace EditApproximation

theorem refinement_grid_error {ell H M J P : ℝ}
    (hell : 1 ≤ ell) (hH : ell ≤ H) (hM : M ≤ H)
    (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H) (hP : H ^ 20 ≤ P) :
    (8 * M + 512 * ell) * J / P ≤ 52000 / H ^ 18 := by
  have hHone : 1 ≤ H := hell.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hHone
  have hJbound : J ≤ 100 * H := by
    have hm := mul_le_mul_of_nonneg_left hell hJ
    nlinarith only [hm, hdepth]
  have hcoef : 8 * M + 512 * ell ≤ 520 * H := by linarith only [hM, hH]
  have hnum := mul_le_mul hcoef hJbound hJ (by positivity : (0 : ℝ) ≤ 520 * H)
  have hPpos : 0 < P := (pow_pos hHpos 20).trans_le hP
  calc
    _ ≤ 52000 * H ^ 2 / P := div_le_div_of_nonneg_right (by nlinarith only [hnum]) hPpos.le
    _ ≤ 52000 * H ^ 2 / H ^ 20 := div_le_div_of_nonneg_left (by positivity) (pow_pos hHpos 20) hP
    _ = _ := by field_simp

theorem refinement_excluded_error {ell root H J P T S : ℝ}
    (hell : 1 ≤ ell) (hroot : 1 ≤ root) (hrootPower : root ^ 4 = H)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H)
    (hJP : J / P ≤ 1) (hJT : J / T ≤ 100 * root / ell) :
    40000 * ell ^ 2 * root * (1 + J / P + J / T) / S ≤
      8040000 * ell ^ 4 / root ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hrootpos : 0 < root := lt_of_lt_of_le zero_lt_one hroot
  have hSrepr : S = root ^ 4 / ell ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hellpos.ne')).2
    exact hcount.trans hrootPower.symm
  have hbracket : 1 + J / P + J / T ≤ 2 + 100 * root / ell := by linarith only [hJP, hJT]
  have hfirst : 80000 * ell ^ 4 / root ^ 3 ≤ 80000 * ell ^ 4 / root ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hrootpos 2)
    have hm := mul_le_mul_of_nonneg_right hroot (pow_nonneg hrootpos.le 2)
    nlinarith only [hm, show root * root ^ 2 = root ^ 3 by ring]
  have hellPower : ell ^ 3 ≤ ell ^ 4 := pow_le_pow_right₀ hell (by decide : 3 ≤ 4)
  have hsecond : 4000000 * ell ^ 3 / root ^ 2 ≤ 4000000 * ell ^ 4 / root ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hellPower (by norm_num)) (pow_nonneg hrootpos.le 2)
  calc
    _ ≤ 40000 * ell ^ 2 * root * (2 + 100 * root / ell) / S :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbracket (by positivity)) hS.le
    _ = 80000 * ell ^ 4 / root ^ 3 + 4000000 * ell ^ 3 / root ^ 2 := by
      rw [hSrepr]
      field_simp
      ring
    _ ≤ 80000 * ell ^ 4 / root ^ 2 + 4000000 * ell ^ 4 / root ^ 2 := add_le_add hfirst hsecond
    _ = 4080000 * ell ^ 4 / root ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by norm_num : (4080000 : ℝ) ≤ 8040000) (pow_nonneg hellpos.le 4)) (pow_nonneg hrootpos.le 2)

theorem refinement_depth_ratios {ell H root J P T S : ℝ}
    (hell : 1 ≤ ell) (hH : 100 ≤ H) (hroot : 0 < root) (hrootPower : root ^ 4 = H)
    (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H)
    (hP : H ^ 20 ≤ P) (hT : root ^ 3 ≤ T)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H) :
    J / P ≤ 1 ∧ J / T ≤ 100 * root / ell ∧ J / S ≤ 100 * ell := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hHone : 1 ≤ H := by linarith only [hH]
  have hHpos : 0 < H := by linarith only [hH]
  have hJbound : J ≤ 100 * H := by
    have hm := mul_le_mul_of_nonneg_left hell hJ
    nlinarith only [hm, hdepth]
  have hPbound : 100 * H ≤ P := by
    calc
      100 * H ≤ H ^ 2 := by nlinarith only [hH, sq_nonneg H]
      _ ≤ H ^ 20 := pow_le_pow_right₀ hHone (by decide : 2 ≤ 20)
      _ ≤ P := hP
  have hPpos : 0 < P := (pow_pos hHpos 20).trans_le hP
  have hTpos : 0 < T := (pow_pos hroot 3).trans_le hT
  refine ⟨(div_le_one₀ hPpos).2 (hJbound.trans hPbound), ?_, ?_⟩
  · apply (div_le_div_iff₀ hTpos hellpos).2
    have hm := mul_le_mul_of_nonneg_left hT (show 0 ≤ 100 * root by positivity)
    have hid : (100 * root) * root ^ 3 = 100 * H := by rw [← hrootPower]; ring
    rw [hid] at hm
    exact hdepth.trans hm
  · apply (div_le_iff₀ hS).2
    apply le_of_mul_le_mul_right _ hellpos
    calc
      J * ell ≤ 100 * H := hdepth
      _ = (100 * ell * S) * ell := by rw [← hcount]; ring

theorem refinement_ordinary_error {ell root q J S : ℝ}
    (hell : 1 ≤ ell) (hroot : 0 < root) (hq : 1 ≤ q)
    (hJS : J / S ≤ 100 * ell) :
    2 * J / S * (1 / root + 4 * (1 / ell ^ 4) * ell +
        64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)) ≤
      200 * ell / root + 1000000 * q / ell ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let bracket := 1 / root + 4 * (1 / ell ^ 4) * ell +
    64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)
  have hbracket : 0 ≤ bracket := by dsimp only [bracket] <;> positivity
  have htwo : 2 * J / S ≤ 200 * ell := by
    calc
      2 * J / S = 2 * (J / S) := by ring
      _ ≤ 2 * (100 * ell) := mul_le_mul_of_nonneg_left hJS (by norm_num)
      _ = _ := by ring
  have hpower : ell ^ 2 ≤ ell ^ 9 := pow_le_pow_right₀ hell (by decide : 2 ≤ 9)
  have hsmall : 400 / ell ^ 9 ≤ 400 / ell ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hellpos 2) hpower
  have hcoeff : 26400 + 51200 * q + 400 ≤ 1000000 * q := by linarith only [hq]
  calc
    _ ≤ 200 * ell * bracket := mul_le_mul_of_nonneg_right htwo hbracket
    _ = 200 * ell / root + (26400 + 51200 * q) / ell ^ 2 + 400 / ell ^ 9 := by
      dsimp only [bracket]
      field_simp
      ring
    _ ≤ 200 * ell / root + (26400 + 51200 * q + 400) / ell ^ 2 := by
      have h := add_le_add_right hsmall (200 * ell / root + (26400 + 51200 * q) / ell ^ 2)
      simpa only [add_div, add_assoc] using h
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right hcoeff (pow_nonneg hellpos.le 2)) _

theorem refinement_numerical_error {ell H J S : ℝ}
    (hell : 0 ≤ ell) (hH : 1 ≤ H) (hJ : 0 ≤ J) (hS : 0 < S)
    (hdepth : J * ell ≤ 100 * H) :
    2 * J / S * (64 * ell * (S / H ^ 3) + 2 * S * (1 / H ^ 4) * ell) ≤ 13200 / H ^ 2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hsmall : 4 * ell * J / H ^ 4 ≤ 4 * ell * J / H ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hHpos 3)
      (pow_le_pow_right₀ hH (by decide : 3 ≤ 4))
  calc
    _ = 128 * ell * J / H ^ 3 + 4 * ell * J / H ^ 4 := by field_simp <;> ring
    _ ≤ 128 * ell * J / H ^ 3 + 4 * ell * J / H ^ 3 := add_le_add_right hsmall _
    _ = 132 * (J * ell) / H ^ 3 := by ring
    _ ≤ 132 * (100 * H) / H ^ 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdepth (by norm_num)) (pow_nonneg hHpos.le 3)
    _ = _ := by field_simp <;> ring

theorem refinement_error_from_stage_bounds {ell H root q M J P T S : ℝ}
    (hell : 64000000000000 ≤ ell) (hH : ell ^ 2 ≤ H)
    (hroot : ell ^ 4 ≤ root) (hrootPower : root ^ 4 = H)
    (hq : 1 ≤ q) (hqSquare : q ^ 2 ≤ ell)
    (hM : M ≤ H) (hJ : 0 ≤ J) (hdepth : J * ell ≤ 100 * H)
    (hP : H ^ 20 ≤ P) (hT : root ^ 3 ≤ T)
    (hS : 0 < S) (hcount : S * ell ^ 2 = H) :
    (8 * M + 512 * ell) * J / P +
      (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
          (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
            2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S < 1 / ell := by
  have hellone : 1 ≤ ell := by linarith only [hell]
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hellone
  have hHell : ell ≤ H := (by nlinarith only [hellone] : ell ≤ ell ^ 2).trans hH
  have hHlarge : 100 ≤ H := by linarith only [hell, hHell]
  have hrootone : 1 ≤ root := (one_le_pow₀ hellone).trans hroot
  have hrootpos : 0 < root := lt_of_lt_of_le zero_lt_one hrootone
  have hratios := refinement_depth_ratios hellone hHlarge hrootpos hrootPower hJ hdepth hP hT hS hcount
  have hgrid := refinement_grid_error hellone hHell hM hJ hdepth hP
  have hbad := refinement_excluded_error hellone hrootone hrootPower hS hcount hratios.1 hratios.2.1
  have hordinary := refinement_ordinary_error hellone hrootpos hq hratios.2.2
  have hnumeric := refinement_numerical_error (zero_le_one.trans hellone) (by linarith only [hHlarge]) hJ hS hdepth
  have hsplit : (8 * M + 512 * ell) * J / P +
      (40000 * root * ell ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / root + 4 * (1 / ell ^ 4) * ell +
          (64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4) + S / H ^ 3) +
            2 * (1 / ell ^ 10) + 2 * S * (1 / H ^ 4) * ell))) / S =
      (8 * M + 512 * ell) * J / P +
        40000 * ell ^ 2 * root * (1 + J / P + J / T) / S +
        2 * J / S * (1 / root + 4 * (1 / ell ^ 4) * ell +
          64 * ell * (4 * q * ell / ell ^ 5 + 2 * (1 / ell ^ 4)) + 2 * (1 / ell ^ 10)) +
        2 * J / S * (64 * ell * (S / H ^ 3) + 2 * S * (1 / H ^ 4) * ell) := by ring
  rw [hsplit]
  apply lt_of_le_of_lt _ (refinement_error_envelope hell hH hroot (zero_le_one.trans hq) hqSquare)
  linarith only [hgrid, hbad, hordinary, hnumeric]

theorem computedRefinementError_lt_oai (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedRefinementError N nx < 1 / (inputSmallLog N : ℝ) := by
  have hcut : 64000000000000 ≤ inputSmallLog N := by
    have hsmall : 64000000000000 ≤ (2 : ℕ) ^ 46 := by norm_num
    exact hsmall.trans ((pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (by decide : 46 ≤ 1000)).trans hell)
  have hlarge : (64000000000000 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hcut
  have hellone : (1 : ℝ) ≤ inputSmallLog N := by linarith only [hlarge]
  have hpoly := inputHeight_polynomial_slack N hN hell
  have hroot := fourth_root_polynomial_slack hellone hpoly
    (Real.sqrt_nonneg _) (heightQuarterRoot_fourth_power N)
  have hHone : 1 ≤ inputHeight N := Nat.one_le_two_pow
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : inputHeight N ^ 20 ≤ (integerParameters N).P :=
    pow_le_pow_right₀ hHone (by omega : 20 ≤ coarseExponent (inputSmallLog N) + 20)
  have hdepth := computed_tree_depth_bound N nx hN hnx ((by decide : 200 ≤ 64000000000000).trans hcut)
  have hcount := computed_refinement_count_exact N hN hell
  unfold computedRefinementError
  apply refinement_error_from_stage_bounds hlarge
  · exact (pow_le_pow_right₀ hellone (by decide : 2 ≤ 20000)).trans hpoly
  · exact (pow_le_pow_right₀ hellone (by decide : 4 ≤ 5000)).trans hroot
  · exact heightQuarterRoot_fourth_power N
  · have hp : (0 : ℝ) ≤ coarseExponent (inputSmallLog N) := Nat.cast_nonneg _
    linarith only [hp]
  · exact coarseExponent_shift_square _ ((by decide : 1764 ≤ 64000000000000).trans hcut)
  · exact_mod_cast hM
  · exact Nat.cast_nonneg _
  · exact_mod_cast hdepth
  · exact_mod_cast hP
  · exact (computed_warmup_count_root N).1
  · exact_mod_cast (computed_stage_positive_counts N hN hell).2
  · exact_mod_cast hcount

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedRefinementError_lt_oai := @OAI.EditApproximation.computedRefinementError_lt_oai
