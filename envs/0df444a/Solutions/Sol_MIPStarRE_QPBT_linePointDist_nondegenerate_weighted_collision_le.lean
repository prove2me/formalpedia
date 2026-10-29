-- Prove2me | solution 1 for MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.470596+00:00
-- url     : https://prove2.me/submissions/5b1c34bb-c930-4ce1-a1ae-f97fc96e3841

-- Generated proof for MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_avgOver_aLinePointDist_resample_parameter
import Theorems.Thm_MIPStarRE_QPBT_avgOver_dLinePointDist_resample_parameter
import Theorems.Thm_MIPStarRE_QPBT_evalCoefficient_collision_card_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Combining/Lines/MixedResampling.lean. -/
/-!
# Mixed line-point parameter resampling

This module combines the axis and diagonal resampling identities for the equal
mixture defining the line-point distribution.

## References

The resampling supports the Schwartz-Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`. The
mixed line-point law is `def:line-point-dist` in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-- Resampling a uniform affine parameter on a sampled line preserves the
unconditional mixed line-point law, including zero-direction diagonal fibers.
This formalization-only identity combines the axis and diagonal cases of the
conditional sampling used at paper line 955. It is recorded in blueprint
`cor:line-point-parameter-resampling`. -/
theorem avgOver_linePointDist_resample_parameter (L : _root_.MIPStarRE.QPBT.LdParams)
    (value : (_root_.MIPStarRE.QPBT.LineDesc L × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) value =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)) (fun param =>
          value (sample.1, sample.1.base + param • sample.1.direction))) := by
  rw [_root_.MIPStarRE.QPBT.linePointDist, _root_.MIPStarRE.QPBT.avgOver_mix, _root_.MIPStarRE.QPBT.avgOver_mix]
  rw [_root_.MIPStarRE.QPBT.avgOver_aLinePointDist_resample_parameter L value,
    _root_.MIPStarRE.QPBT.avgOver_dLinePointDist_resample_parameter L value]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/LowDegree.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.instDecidableRel_qPBT
attribute [local instance] _root_.MIPStarRE.QPBT.WinImplications.linePointFintypeCanonical
/-!
# Low-degree winning implications

This module proves the exact line-point and Pauli-basis consistency bounds.

## References

The line-point and Pauli-basis consistency theorems prove items 2 and 3
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications





































/-- A uniquely determined line evaluation is returned by `evalOpt`. -/
theorem evalOpt_eq_some_of_evaluatesTo {L : _root_.MIPStarRE.QPBT.LdParams} {c : ℕ}
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (f : _root_.MIPStarRE.QPBT.DegPoly L c) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (a : _root_.MIPStarRE.QPBT.ScalarQ L) (h : _root_.MIPStarRE.QPBT.EvaluatesTo line f u a) :
    _root_.MIPStarRE.QPBT.evalOpt line u f = some a := by
  unfold _root_.MIPStarRE.QPBT.evalOpt
  rw [dif_pos ⟨a, h⟩]
  apply congrArg some
  obtain ⟨t, ht⟩ := h.1
  exact ((Classical.choose_spec ⟨a, h⟩).2 t ht).symm.trans (h.2 t ht)
























































end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/AffineEvaluation.lean. -/
/-!
# Evaluation on a nondegenerate affine line

This module identifies completed line-polynomial evaluation with evaluation at
the unique affine parameter of a point on a line with nonzero direction.

## References

The result is the geometric step in the collision argument at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-- On a nonzero direction, completed evaluation agrees with polynomial
evaluation at the unique affine parameter. -/
theorem evalOpt_affine_parameter_of_direction_ne_zero {L : _root_.MIPStarRE.QPBT.LdParams}
    {bound : ℕ} (line : _root_.MIPStarRE.QPBT.LineDesc L) (hdir : line.direction ≠ 0)
    (poly : _root_.MIPStarRE.QPBT.DegPoly L bound) (param : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalOpt line (line.base + param • line.direction) poly =
      some (_root_.MIPStarRE.QPBT.evalCoefficient poly param) := by
  apply _root_.MIPStarRE.QPBT.WinImplications.evalOpt_eq_some_of_evaluatesTo
  refine ⟨⟨param, rfl⟩, ?_⟩
  intro other heq
  have hsmul : param • line.direction = other • line.direction :=
    add_left_cancel heq
  have hsub : (param - other) • line.direction = 0 := by
    rw [sub_smul, hsmul, sub_self]
  have hparam : param = other :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hdir)
  rw [hparam]

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/UniformAffineCollision.lean. -/
/-!
# Uniform collision bounds on nondegenerate affine lines

This module combines uniqueness of affine evaluation with the univariate
root-count bound to control collisions under a uniform line parameter.

## References

The result is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section

/-- On a nondegenerate line, completed evaluations of distinct degree-bounded
polynomials collide with probability at most the degree bound divided by the
field size under a uniform affine parameter. -/
theorem evalOpt_uniform_parameter_collision_le {L : _root_.MIPStarRE.QPBT.LdParams} {bound : ℕ}
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (hdir : line.direction ≠ 0)
    (first second : _root_.MIPStarRE.QPBT.DegPoly L bound) (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)) (fun param =>
      if _root_.MIPStarRE.QPBT.evalOpt line (line.base + param • line.direction) first =
        _root_.MIPStarRE.QPBT.evalOpt line (line.base + param • line.direction) second then 1 else 0) ≤
      (bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) := by
  classical
  simp_rw [_root_.MIPStarRE.QPBT.evalOpt_affine_parameter_of_direction_ne_zero line hdir,
    Option.some.injEq]
  have hcard := _root_.MIPStarRE.QPBT.evalCoefficient_collision_card_le first second hne
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver
  simp only [_root_.LIDT.MIPStarRE.LDT.uniformDistribution_support, _root_.MIPStarRE.QPBT.uniformDistribution_weight_apply,
    mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end

end MIPStarRE.QPBT

/-!
# Weighted collision bounds for sampled lines

This module lifts the uniform affine-parameter collision estimate to the mixed
line-point distribution with an arbitrary nonnegative weight depending only on
the sampled line.

## References

The estimate is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution {L : _root_.MIPStarRE.QPBT.LdParams}
    {bound : ℕ} (weight : _root_.MIPStarRE.QPBT.LineDesc L → ℝ)
    (hweight : ∀ line, 0 ≤ weight line) (first second : _root_.MIPStarRE.QPBT.DegPoly L bound)
    (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
      if sample.1.direction ≠ 0 then weight sample.1 *
        (if _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 first = _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
          if sample.1.direction ≠ 0 then weight sample.1 else 0) := by
  classical
  rw [_root_.MIPStarRE.QPBT.avgOver_linePointDist_resample_parameter]
  rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
  intro sample
  by_cases hdir : sample.1.direction ≠ 0
  · simp only [if_pos hdir]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    exact (mul_le_mul_of_nonneg_left
      (_root_.MIPStarRE.QPBT.evalOpt_uniform_parameter_collision_le sample.1 hdir first second hne)
      (hweight sample.1)).trans_eq
      (mul_comm _ _)
  · simp [hdir, _root_.LIDT.MIPStarRE.LDT.avgOver]
