-- Prove2me | solution 1 for OAI.EditApproximation.physicalProgram_expected_state_excess
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:46:29.029111+00:00
-- url     : https://prove2.me/submissions/227ec63b-e89c-40f8-9644-f00e8c80cbca

import Mathlib
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedRefinementError_lt
import Theorems.Thm_OAI_EditApproximation_physicalProgram_subtree_node_regret
import Theorems.Thm_OAI_EditApproximation_subtree_expected_excess_of_good_nodes

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GroupSmallConstants
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed small parameters satisfy the group and online error inequalities. -/

namespace EditApproximation

theorem group_online_range_small {ell : ℚ} (hell : 8 ≤ ell) :
    8 * (128 * ell) * (1 / ell ^ 40) ≤ 1 / ell ^ 10 := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef : (1024 : ℚ) ≤ ell ^ 29 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 4
    norm_num at h
    exact (by norm_num : (1024 : ℚ) ≤ 4096) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 4 ≤ 29)))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos he0 40) (pow_pos he0 10)).2
  have h := mul_le_mul_of_nonneg_right hcoef (pow_nonneg he0.le 11)
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem group_online_eta_range {ell : ℚ} (hell : 3 ≤ ell) :
    ell ^ 5 * (3 * (1 / ell ^ 10)) ≤ 1 / ell ^ 4 := by
  have he0 : 0 < ell := by linarith only [hell]
  have h := mul_le_mul_of_nonneg_right hell (pow_nonneg he0.le 9)
  have hmul : ell ^ 5 * (3 * (1 / ell ^ 10)) = 3 * ell ^ 5 / ell ^ 10 := by ring
  rw [hmul]
  apply (div_le_div_iff₀ (pow_pos he0 10) (pow_pos he0 4)).2
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

theorem group_rounded_error_small {ell : ℚ} (hell : 8 ≤ ell) :
    2 * (1 / ell ^ 20) + 512 * (128 * ell) * ell * (1 / ell ^ 40) ≤
      (1 / ell ^ 4) * (1 / ell ^ 10) := by
  have he : 1 ≤ ell := by linarith only [hell]
  have he0 : 0 < ell := by linarith only [hell]
  have hcoef1 : (4 : ℚ) ≤ ell ^ 6 := by
    exact (by norm_num : (4 : ℚ) ≤ 8).trans
      (hell.trans (by simpa only [pow_one] using pow_le_pow_right₀ he (by decide : 1 ≤ 6)))
  have hcoef2 : (131072 : ℚ) ≤ ell ^ 24 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 8) hell 6
    norm_num at h
    exact (by norm_num : (131072 : ℚ) ≤ 262144) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 6 ≤ 24)))
  have hfirst : 2 / ell ^ 20 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 20) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef1 (pow_nonneg he0.le 14)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have hsecond : 65536 * ell ^ 2 / ell ^ 40 ≤ 1 / (2 * ell ^ 14) := by
    apply (div_le_div_iff₀ (pow_pos he0 40) (by positivity : 0 < 2 * ell ^ 14)).2
    have h := mul_le_mul_of_nonneg_right hcoef2 (pow_nonneg he0.le 16)
    first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))
  have hid : (1 / ell ^ 4) * (1 / ell ^ 10) = 2 * (1 / (2 * ell ^ 14)) := by
    field_simp
  rw [hid]
  have hid2 : 512 * (128 * ell) * ell * (1 / ell ^ 40) = 65536 * ell ^ 2 / ell ^ 40 := by ring
  rw [hid2]
  have hid1 : 2 * (1 / ell ^ 20) = 2 / ell ^ 20 := by ring
  rw [hid1]
  simpa only [two_mul] using add_le_add hfirst hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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



theorem intervalTreeDepth_capacity (M nx : ℕ) (hM : 2 ≤ M) :
    nx ≤ M ^ intervalTreeDepth M nx :=
  (le_max_right 1 nx).trans (Nat.le_pow_clog hM (max 1 nx))

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedBandSpacing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The input-computed dyadic parameters discharge all spacing and basic rounding premises. -/

namespace EditApproximation

theorem computed_theta_dyadic (N : ℕ) :
    (rationalParameters (inputSmallLog N)).theta =
      (2 : ℚ) ^ (-((40 * smallLogExponent N : ℕ) : ℤ)) := by
  change 1 / (((2 ^ smallLogExponent N : ℕ) : ℚ) ^ 40) = _
  rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [zpow_neg, zpow_natCast]
  rw [Nat.mul_comm (smallLogExponent N) 40, one_div]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_StageParameterBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.rationalParametersWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters for the actual local energy and online inequalities. -/

namespace EditApproximation

theorem refinementFactor_le {A : ℚ} {F : ℕ} (hA : 1 ≤ A) (hF : 1 ≤ F) :
    refinementFactor A F ≤ A := by
  apply max_le hA
  have hFQ : (1 : ℚ) ≤ F := by exact_mod_cast hF
  apply (div_le_iff₀ (by linarith only [hFQ] : (0 : ℚ) < F)).2
  have h := mul_le_mul_of_nonneg_left hFQ (by linarith only [hA] : 0 ≤ A)
  simpa only [mul_one] using h

theorem computed_initialFactor_twice_le_P (N : ℕ) (hN : 0 < N) :
    2 * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  have hH : 2 ≤ H := by
    have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (heightExponent_pos N hN)
    simpa only [H, inputHeight, pow_one] using h
  have hHone : 1 ≤ H := by omega
  have hpow : 2 ≤ H ^ 16 := hH.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hHone (by decide : 1 ≤ 16))
  change 2 * H ^ (p + 4) ≤ H ^ (p + 20)
  calc
    2 * H ^ (p + 4) ≤ H ^ (p + 4) * H ^ 16 := by
      simpa only [mul_comm] using Nat.mul_le_mul_left (H ^ (p + 4)) hpow
    _ = H ^ (p + 20) := by
      rw [← pow_add]

theorem computed_refinementFactor_spacing (N : ℕ) (hN : 0 < N) (A : ℚ)
    (hA : 1 ≤ A) (hupper : A ≤ (integerParameters N).initialFactor) :
    2 * (refinementFactor A (inputSmallLog N) : ℝ) ≤ (integerParameters N).P := by
  have hfactor := refinementFactor_le hA (show 1 ≤ inputSmallLog N from Nat.one_le_two_pow)
  have hnum : (2 : ℚ) * (integerParameters N).initialFactor ≤ (integerParameters N).P := by
    exact_mod_cast computed_initialFactor_twice_le_P N hN
  have hQ : (2 : ℚ) * refinementFactor A (inputSmallLog N) ≤ (integerParameters N).P := by
    linarith only [hfactor, hupper, hnum]
  exact_mod_cast hQ

theorem computed_online_range (ell : ℕ) (hell : 8 ≤ ell) :
    0 < (rationalParameters ell).eta ∧ 0 ≤ (rationalParameters ell).kappa ∧
      (rationalParameters ell).kappa ≤ 1 / 2 ∧
      ((rationalParameters ell).eta : ℝ) *
        (2 * ((rationalParameters ell).delta : ℝ) +
          8 * (128 * (ell : ℝ)) * ((rationalParameters ell).theta : ℝ)) ≤
        ((rationalParameters ell).kappa : ℝ) := by
  have hellQ : (8 : ℚ) ≤ ell := by exact_mod_cast hell
  have he0 : (0 : ℚ) < ell := by linarith only [hellQ]
  have hpow : (2 : ℚ) ≤ (ell : ℚ) ^ 4 := by
    exact (by linarith only [hellQ] : (2 : ℚ) ≤ ell).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [hellQ] : (1 : ℚ) ≤ ell)
        (by decide : 1 ≤ 4))
  have hhalf : (1 : ℚ) / (ell : ℚ) ^ 4 ≤ 1 / 2 := by
    exact (div_le_div_iff₀ (pow_pos he0 4) (by norm_num : (0 : ℚ) < 2)).2 (by simpa using hpow)
  have hrange := group_online_range_small hellQ
  have heta := group_online_eta_range (by linarith only [hellQ] : (3 : ℚ) ≤ ell)
  have h := mul_le_mul_of_nonneg_left hrange (pow_nonneg he0.le 5)
  have hQ : (ell : ℚ) ^ 5 * (2 * (1 / (ell : ℚ) ^ 10) +
      8 * (128 * ell) * (1 / (ell : ℚ) ^ 40)) ≤ 1 / (ell : ℚ) ^ 4 := by
    linarith only [h, heta]
  refine ⟨pow_pos he0 5, (by positivity : (0 : ℚ) ≤ 1 / (ell : ℚ) ^ 4), hhalf, ?_⟩
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  simpa only [rationalParameters, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow,
    Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] using hR

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedStageParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical premises for the computed physical refinement stage. -/

namespace EditApproximation

 theorem computed_stage_tree_small (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    (intervalTreeDepth (integerParameters N).M nx : ℝ) *
      (4 * ((integerParameters N).M : ℝ) / (integerParameters N).P) ≤ 1 / 2 := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let J := intervalTreeDepth M nx
  have hdepth := computed_tree_depth_bound N nx hN hnx hell
  have hellone : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hJ : J ≤ 100 * H := by
    calc
      J = J * 1 := (Nat.mul_one J).symm
      _ ≤ J * inputSmallLog N := Nat.mul_le_mul_left J hellone
      _ ≤ 100 * H := hdepth
  have hJR : (J : ℝ) ≤ 100 * H := by exact_mod_cast hJ
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (Nat.div_le_self _ _)
  have hMR : (M : ℝ) ≤ H := by exact_mod_cast hM
  have hP800 := (computed_stage_grid_bounds N hN).2.1
  have hPr : (0 : ℝ) < P := by exact_mod_cast (show 0 < P from lt_of_lt_of_le (by decide) (computed_stage_grid_bounds N hN).1)
  have hproduct := mul_le_mul hJR hMR (Nat.cast_nonneg M) (by positivity : (0 : ℝ) ≤ 100 * H)
  change (J : ℝ) * (4 * (M : ℝ) / P) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hPr).2
  nlinarith only [hproduct, hP800]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected root-excess accuracy of the finite selection program under finite Bernstein bounds. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem physicalProgramNodeCoefficient_nonneg (N F S H : ℕ) (eta kappa delta : ℚ)
    (heta : (0 : ℝ) ≤ eta) (hkappa : (0 : ℝ) ≤ kappa) (hdelta : (0 : ℝ) ≤ delta) :
    0 ≤ physicalProgramNodeCoefficient N F eta kappa delta S H := by
  unfold physicalProgramNodeCoefficient
  positivity

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalProgramStateAccuracy
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalMedianUpdateTable_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expected excess at every original physical table entry, under the same
query-filtered global stream law. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem rooted_refinement_budget_mono {M F P T S ratio velocityTolerance coefficient K J : ℝ}
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hP : 0 ≤ P) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hratio : 0 ≤ ratio) (htau : 0 ≤ velocityTolerance) (hcoef : 0 ≤ coefficient)
    (hKJ : K ≤ J) :
    (8 * M + 512 * F) * K / P +
      (40000 * ratio * F ^ 2 * (1 + K / P + K / T) +
        2 * K * (1 / ratio + 4 * velocityTolerance * F + coefficient)) / S ≤
    (8 * M + 512 * F) * J / P +
      (40000 * ratio * F ^ 2 * (1 + J / P + J / T) +
        2 * J * (1 / ratio + 4 * velocityTolerance * F + coefficient)) / S := by
  gcongr

section Accuracy

variable {α : Type*} [DecidableEq α] {M J R H : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N : ℕ) (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N)
  (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
  (U : PhysicalEntry M J target.length → ℕ) (P : ℕ) (hPeq : P = (integerParameters N).P)
  (A : ℚ) (hA : 1 ≤ A) (hAupper : A ≤ (integerParameters N).initialFactor)
  (hsize : source.length + target.length ≤ N)
  (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
    (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
  (T S : ℕ) (hTeq : T = (integerParameters N).T) (hSeq : S = (integerParameters N).S)
  (hHeq : H = inputHeight N)
  (bernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b (inputSmallLog N)).length,
    FiniteBernsteinInput (Measure.pi fun _ : Fin
      (groupSampleCount M (inputSmallLog N ^ 80) b (groupDyadicScaleAt M b (inputSmallLog N) h)) =>
      (PMF.uniformOfFintype (Fin M)).toMeasure))
  (root : PhysicalNode M J) (rootQ : TargetInterval target.length)

local notation "ell" => inputSmallLog N
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "Draw" => PhysicalProgramDraw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau
local notation "choices" => physicalProgramDrawSelections source target U N P ell A T thetaExponent H (ell ^ 80) tau eta kappa
local notation "globalLaw" => physicalProgramDrawLaw (R := R) source target U N P ell A T thetaExponent H (ell ^ 80) tau

include hN hell hMeq hJeq hPeq hA hAupper hsize hseed hTeq hSeq hHeq bernstein

/-- A pass of the actual rational recurrence has expected positive root
error at most the actual edit cost divided by the computed small logarithm. -/
theorem physicalProgram_expected_state_excess_oai :
    (∫ draw : Draw, max ((physicalRefinement source target U N P ell A T delta (choices draw)
      root S rootQ : ℝ) -
        stateEditCost (physicalSource source root) target rootQ) 0 ∂globalLaw) ≤
      (1 / (ell : ℝ)) * stateEditCost (physicalSource source root) target rootQ := by
  classical
  have hell1764 : 1764 ≤ ell := by
    have hlarge : 4096 ≤ (2 : ℕ) ^ 1000 := by
      have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 12 ≤ 1000)
      norm_num only [show (2 : ℕ) ^ 12 = 4096 by norm_num] at h
      exact h
    omega
  have hell200 : 200 ≤ ell := by omega
  have hF : 1 ≤ ell := Nat.one_le_two_pow
  have hEllQ : (8 : ℚ) ≤ ell := by exact_mod_cast (show 8 ≤ ell by omega)
  have hEllPos : (0 : ℚ) < ell := Nat.cast_pos.2 (Nat.two_pow_pos _)
  have hbranch : 2 ≤ M := by
    rw [hMeq]
    exact (computed_branching_bounds N hN hell200).1
  have hM : 0 < M := by omega
  have hP := computed_program_grid_lower N P hN hPeq
  have hcounts := computed_stage_positive_counts N hN hell
  have hT : 0 < T := by rw [hTeq]; exact hcounts.1
  have hS : 0 < S := by rw [hSeq]; exact hcounts.2
  have hpoly : ell ^ 20000 ≤ inputHeight N := by exact_mod_cast inputHeight_polynomial_slack N hN hell
  have hEllHeight : ell ≤ inputHeight N := by
    have hpow : ell ≤ ell ^ 20000 := by
      simpa only [pow_one] using pow_le_pow_right₀ hF (by decide : 1 ≤ 20000)
    exact hpow.trans hpoly
  have hH : 4 ≤ H := by rw [hHeq]; omega
  have hrange := computed_online_range ell (by omega : 8 ≤ ell)
  have hdelta : 0 < delta := div_pos zero_lt_one (pow_pos hEllPos 10)
  have htau : 0 ≤ tau := (div_pos zero_lt_one (pow_pos hEllPos 4)).le
  have hηrange : (eta : ℝ) * (2 * (delta : ℝ) + 8 * ((128 * ell : ℚ) : ℝ) *
      (((2 : ℚ) ^ (-(thetaExponent : ℤ))) : ℝ)) ≤ (kappa : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, computed_theta_dyadic,
      Rat.cast_zpow] using hrange.2.2.2
  have herror : 2 * (rationalParameters ell).gamma + 512 * (128 * ell : ℚ) * ell *
      (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ kappa * delta := by
    simpa only [← computed_theta_dyadic, rationalParameters] using group_rounded_error_small hEllQ
  have hscale : 2 * (refinementFactor A ell : ℝ) ≤ P := by
    rw [hPeq]
    exact computed_refinementFactor_spacing N hN A hA hAupper
  have hMP : 4 * (M : ℝ) / P ≤ 1 := by
    rw [hMeq, hPeq]
    exact (computed_stage_grid_bounds N hN).2.2
  have hcapacity : source.length ≤ M ^ J := by
    rw [hJeq]
    exact intervalTreeDepth_capacity M source.length hbranch
  have hsmall : (J : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 := by
    rw [hJeq, hMeq, hPeq]
    exact computed_stage_tree_small N source.length hN (by omega) hell200
  have hratio : 0 < heightQuarterRoot N := by
    unfold heightQuarterRoot
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.two_pow_pos _)))
  have hηR : (0 : ℝ) < eta := (Rat.cast_pos (K := ℝ)).mpr hrange.1
  have hκR : (0 : ℝ) ≤ kappa := (Rat.cast_nonneg (K := ℝ)).mpr hrange.2.1
  have hdeltaR : (0 : ℝ) < delta := (Rat.cast_pos (K := ℝ)).mpr hdelta
  have hcoef := physicalProgramNodeCoefficient_nonneg N ell S H eta kappa delta hηR.le hκR hdeltaR.le
  let K := J - root.1.val
  have hK : K ≤ J := Nat.sub_le _ _
  have hheight : root.1.val + K = J := by dsimp only [K]; omega
  have hsmallK : (K : ℝ) * (4 * (M : ℝ) / P) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK)
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))).trans hsmall
  have hgood := fun (d : Fin K) (path : TreeLayer M d.val) =>
    physicalProgram_subtree_node_regret (R := R) source target N hN hell hM hMeq U P hPeq A hA hAupper
      hsize hseed T hT hHeq hH delta eta kappa hdelta hrange.1 hrange.2.1 hrange.2.2.1
      hηrange herror bernstein root K hheight rootQ S d path
  have hbound := subtree_expected_excess_of_good_nodes source target hM U N P ell A
    hsize hP hF hA hseed T hT delta choices root K hheight rootQ globalLaw (heightQuarterRoot N) hratio tau htau
    hscale hMP hcapacity hsmallK S hS (physicalProgramNodeCoefficient N ell eta kappa delta S H) hcoef hgood
  have hbudget : ((8 * (M : ℝ) + 512 * ell) * J / P +
      (40000 * heightQuarterRoot N * (ell : ℝ) ^ 2 * (1 + (J : ℝ) / P + (J : ℝ) / T) +
        2 * J * (1 / heightQuarterRoot N + 4 * (tau : ℝ) * ell +
          physicalProgramNodeCoefficient N ell eta kappa delta S H)) / S) =
        computedRefinementError N source.length := by
    dsimp only [physicalProgramNodeCoefficient, computedRefinementError]
    rw [hJeq, hMeq, hPeq, hTeq, hSeq, hHeq]
    simp only [rationalParameters, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_ofNat]
  have hbudget_le := rooted_refinement_budget_mono (M := (M : ℝ)) (F := (ell : ℝ))
    (P := (P : ℝ)) (T := (T : ℝ)) (S := (S : ℝ)) (ratio := heightQuarterRoot N)
    (velocityTolerance := (tau : ℝ)) (coefficient := physicalProgramNodeCoefficient N ell eta kappa delta S H)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hratio.le ((Rat.cast_nonneg (K := ℝ)).mpr htau) hcoef
    (Nat.cast_le.mpr hK)
  rw [hbudget] at hbudget_le
  exact (hbound.trans (mul_le_mul_of_nonneg_right hbudget_le (Nat.cast_nonneg _))).trans (mul_le_mul_of_nonneg_right
    (computedRefinementError_lt N source.length hN (by omega) hell).le (Nat.cast_nonneg _))

end Accuracy

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalProgram_expected_state_excess_oai.{u_1} := @OAI.EditApproximation.physicalProgram_expected_state_excess_oai.{u_1}
