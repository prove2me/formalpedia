-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.avgOver_mix
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:08:33.175369+00:00
-- url     : https://prove2.me/submissions/b16899b9-c1ee-43af-a00e-8d4dfad94a11

-- Generated proof for MIPStarRE.QPBT.WinImplications.avgOver_mix.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Observables/WinImplications/Averages.lean. -/
/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
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





/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
a finite distribution average may be extended to the full finite type. -/
theorem avgOver_eq_sum_univ {X : Type*} [Fintype X]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (f : X → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver μ f = ∑ x : X, μ.weight x * f x := by
  classical
  exact (_root_.LIDT.MIPStarRE.LDT.Distribution.sum_univ_eq_sum_support μ (fun x => μ.weight x * f x)
    (fun x hx => by rw [μ.outsideSupport x hx, zero_mul])).symm
























end WinImplications

end

end MIPStarRE.QPBT

/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

theorem solution {X : Type*} [Finite X] [DecidableEq X]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution X) (f : X → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.mix t ht0 ht1 μ ν) f =
      t * _root_.LIDT.MIPStarRE.LDT.avgOver μ f + (1 - t) * _root_.LIDT.MIPStarRE.LDT.avgOver ν f := by
  letI := Fintype.ofFinite X
  rw [_root_.MIPStarRE.QPBT.WinImplications.avgOver_eq_sum_univ, _root_.MIPStarRE.QPBT.WinImplications.avgOver_eq_sum_univ, _root_.MIPStarRE.QPBT.WinImplications.avgOver_eq_sum_univ]
  simp only [_root_.MIPStarRE.QPBT.Distribution.mix]
  calc
    (∑ x, (t * μ.weight x + (1 - t) * ν.weight x) * f x) =
        (∑ x, (t * (μ.weight x * f x) + (1 - t) * (ν.weight x * f x))) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = t * (∑ x, μ.weight x * f x) +
        (1 - t) * (∑ x, ν.weight x * f x) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
