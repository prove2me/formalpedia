-- Prove2me | solution 1 for MIPStarRE.QPBT.delta_extract_le_delta_qld_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:28:35.297054+00:00
-- url     : https://prove2.me/submissions/eafb772f-dea7-49e0-ac5c-32df3659ef1e

-- Generated proof for MIPStarRE.QPBT.delta_extract_le_delta_qld_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Extraction by the swap unitaries

The concrete swap operators below yield the Pauli extraction conclusion. The
local maps are constructed from the global polynomial
measurements, and all operators retain the heterogeneous Alice and Bob
placements. The generalized Pauli projectors use the field and basis fixed by
`P.model`.

## References

The extraction witness records the conclusion of blueprint `lem:qld-unitary`,
from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1860`.
The error-form comparison formalizes `lem:qld-extraction-error-form` and
supports `rem:pauli-robustness-form` in the blueprint; its paper source is
lines 1855-1858 and 1868-1876.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

theorem solution (C a b : ℝ) (hC : 1 ≤ C) (ha : 1 < a)
    (hb : 0 < b) (hb1 : b < 1) :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon → epsilon ≤ 1 →
      _root_.MIPStarRE.QPBT.deltaExtract C
          (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
            (_root_.MIPStarRE.QPBT.deltaQld a b epsilon P.m P.d P.q) P.m P.d P.q)
          P.m P.d P.q ≤
        _root_.MIPStarRE.QPBT.deltaQld (4 * C ^ 2 * a) (b / 8) epsilon P.m P.d P.q := by
  have hC0 : 0 ≤ C := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hconstant : a ≤ 4 * C ^ 2 * a := by
    have hCsq : 1 ≤ C ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hCsq ha0]
  intro params epsilon hepsilon0 hepsilon1
  let degree : ℝ := ((params.m * params.d : ℕ) : ℝ)
  have hdegree1 : 1 ≤ degree :=
    Nat.one_le_cast.mpr (Nat.mul_pos params.one_le_m params.hd)
  have hdegree0 : 0 ≤ degree := by linarith
  have hfield1 : (1 : ℝ) ≤ (params.q : ℝ) := by
    obtain ⟨size, -, hsize⟩ := params.hq
    rw [hsize]
    exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hfield0 : (0 : ℝ) ≤ (params.q : ℝ) := by positivity
  let amplitude : ℝ := a * degree ^ a
  let rate : ℝ := epsilon ^ (b / 8) + (params.q : ℝ) ^ (-(b / 8)) +
    (2 : ℝ) ^ (-((b / 8) * degree))
  have hamplitude1 : 1 ≤ amplitude :=
    one_le_mul_of_one_le_of_one_le ha.le (Real.one_le_rpow hdegree1 ha0)
  have hamplitude0 : 0 ≤ amplitude := by linarith
  have hdegree_amplitude : degree ≤ amplitude :=
    (Real.self_le_rpow_of_one_le hdegree1 ha.le).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hdegree0 a) ha.le)
  have hrate0 : 0 ≤ rate := by dsimp [rate]; positivity
  have hepsilon_rate : epsilon ^ (b / 8) ≤ rate := by
    dsimp [rate]
    linarith [Real.rpow_nonneg hfield0 (-(b / 8)),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * degree))]
  have hfield_rate : (params.q : ℝ) ^ (-(b / 8)) ≤ rate := by
    dsimp [rate]
    linarith [Real.rpow_nonneg hepsilon0 (b / 8),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((b / 8) * degree))]
  have hroot_sum {first second third : ℝ}
      (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) (hthird : 0 ≤ third) :
      (first + second + third) ^ (1 / 4 : ℝ) ≤
        first ^ (1 / 4 : ℝ) + second ^ (1 / 4 : ℝ) + third ^ (1 / 4 : ℝ) :=
    (Real.rpow_add_le_add_rpow (p := (1 / 4 : ℝ)) (add_nonneg hfirst hsecond) hthird
      (by norm_num) (by norm_num)).trans
      (add_le_add (Real.rpow_add_le_add_rpow (p := (1 / 4 : ℝ)) hfirst hsecond
        (by norm_num) (by norm_num)) le_rfl)
  have hrate_root :
      (epsilon ^ b + (params.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree))) ^
        (1 / 4 : ℝ) ≤ rate := by
    refine (hroot_sum (by positivity) (by positivity) (by positivity)).trans ?_
    rw [← Real.rpow_mul hepsilon0, ← Real.rpow_mul hfield0,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact Real.rpow_le_rpow_of_exponent_ge' hepsilon0 hepsilon1
        (by positivity) (by linarith)
    · exact Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_nonneg hb.le hdegree0]
  have hglobal0 : 0 ≤ _root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q := by
    simp only [_root_.MIPStarRE.QPBT.deltaQld, Real.rpow_eq_pow]
    positivity
  have hglobal_root :
      (_root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q) ^ (1 / 4 : ℝ) ≤
        amplitude * rate := by
    change (amplitude *
      (epsilon ^ b + (params.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * degree)))) ^
        (1 / 4 : ℝ) ≤ amplitude * rate
    rw [Real.mul_rpow hamplitude0 (by positivity)]
    exact mul_le_mul (Real.rpow_le_self_of_one_le hamplitude1 (by norm_num))
      hrate_root (by positivity) hamplitude0
  have hsqrt_root : (Real.sqrt epsilon) ^ (1 / 4 : ℝ) ≤ amplitude * rate := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hepsilon0]
    exact ((Real.rpow_le_rpow_of_exponent_ge' hepsilon0 hepsilon1
      (by positivity) (by linarith)).trans hepsilon_rate).trans
      (le_mul_of_one_le_left hrate0 hamplitude1)
  have hratio_root : (degree / (params.q : ℝ)) ^ (1 / 4 : ℝ) ≤ amplitude * rate := by
    rw [Real.div_rpow hdegree0 hfield0, div_eq_mul_inv, ← Real.rpow_neg hfield0]
    exact mul_le_mul
      ((Real.rpow_le_self_of_one_le hdegree1 (by norm_num)).trans hdegree_amplitude)
      ((Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)).trans hfield_rate)
      (by positivity) hamplitude0
  have hratio : degree / (params.q : ℝ) ≤ amplitude * rate := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul hdegree_amplitude
      ((Real.rpow_le_rpow_of_exponent_le hfield1 (by linarith)).trans hfield_rate)
      (by positivity) hamplitude0
  have hconstruct_root :
      (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
        (_root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q) params.m params.d params.q) ^
          (1 / 4 : ℝ) ≤ 3 * C * amplitude * rate := by
    unfold _root_.MIPStarRE.QPBT.deltaConstructPaulis
    rw [Real.mul_rpow hC0 (by positivity)]
    calc
      C ^ (1 / 4 : ℝ) *
          (_root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q + Real.sqrt epsilon +
            degree / (params.q : ℝ)) ^ (1 / 4 : ℝ) ≤
          C * ((_root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q) ^ (1 / 4 : ℝ) +
            (Real.sqrt epsilon) ^ (1 / 4 : ℝ) +
            (degree / (params.q : ℝ)) ^ (1 / 4 : ℝ)) :=
        mul_le_mul (Real.rpow_le_self_of_one_le hC (by norm_num))
          (hroot_sum hglobal0 (by positivity) (by positivity))
          (by positivity) hC0
      _ ≤ C * (amplitude * rate + amplitude * rate + amplitude * rate) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hglobal_root hsqrt_root) hratio_root) hC0
      _ = 3 * C * amplitude * rate := by ring
  calc
    _root_.MIPStarRE.QPBT.deltaExtract C
        (_root_.MIPStarRE.QPBT.deltaConstructPaulis C epsilon
          (_root_.MIPStarRE.QPBT.deltaQld a b epsilon params.m params.d params.q) params.m params.d params.q)
        params.m params.d params.q ≤
        C * (3 * C * amplitude * rate + amplitude * rate) :=
      mul_le_mul_of_nonneg_left (add_le_add hconstruct_root hratio) hC0
    _ = (C * (3 * C + 1)) * (amplitude * rate) := by ring
    _ ≤ 4 * C ^ 2 * (amplitude * rate) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hamplitude0 hrate0)
    _ = (4 * C ^ 2 * a) * degree ^ a * rate := by dsimp [amplitude]; ring
    _ ≤ _root_.MIPStarRE.QPBT.deltaQld (4 * C ^ 2 * a) (b / 8) epsilon params.m params.d params.q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hdegree1 hconstant) (by positivity)) hrate0
