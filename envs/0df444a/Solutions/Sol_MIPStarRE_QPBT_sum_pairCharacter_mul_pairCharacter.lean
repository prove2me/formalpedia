-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_pairCharacter_mul_pairCharacter
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.319627+00:00
-- url     : https://prove2.me/submissions/bb9950d2-4246-4cc5-a7c0-404840aa0870

-- Generated proof for MIPStarRE.QPBT.sum_pairCharacter_mul_pairCharacter.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_sum_fixedCharacter_mul_fixedCharacter

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Approximate commutation of the field-valued expanded point measurements

The approximate commutation of `lem:qld-comm-cons` is stated for the binary
refinements `M^{(Point,W),u,r}_b` of the expanded point measurements.  The
combined point measurements of `lem:qld-4-10` are built here directly from the
`F_q`-valued measurements `M^{(Point,W),u}_a`, so the commutation estimate is
transferred to them.  The transfer is exact: since
`M^{(Point,X),x}_a = E_r (-1)^{tr(ar)} X^r(x)` and
`M^{(Point,Z),z}_b = E_s (-1)^{tr(bs)} Z^s(z)`, the commutator of the two
measurement effects is the Fourier transform, in the outcome pair `(a, b)`,
of the commutators of the expanded observables, and Parseval's identity for
the additive characters of `F_q` turns the sum over `(a, b)` of the squared
norms into the average over `(r, s)` of the squared norms of the observable
commutators.  No factor depending on `q` is lost.

## Main results

* `sum_norm_sum_smul_sq_of_orthogonal`: Parseval's identity for an orthogonal
  system of coefficients.
* `sum_fixedCharacter_mul`: Fourier cancellation for the fixed trace character.
* `expPoint_comm`: the field-valued expanded point measurements approximately
  commute on every register placement, with the error of
  `lem:qld-comm-cons`.

## References

The commutation estimate for the binary refinements is item 2 of
`lem:qld-comm-cons`, blueprint
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1210`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`; the
Fourier form of the point effects is `def:expanded-point-measurement`, paper
lines 384--418.  The role of the transfer in the proof of `lem:qld-4-10` is
explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries





/-! ## Parseval's identity for an orthogonal system of coefficients -/



/-! ## The fixed trace character -/



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}

theorem solution
    (rs rs' : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        (starRingEnd ℂ) (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.1 * rs.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.2 * rs.2))) *
          (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.1 * rs'.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (ab.2 * rs'.2))) =
      if rs = rs' then
        (((Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
  have hstar : ∀ t : ZMod 2, (starRingEnd ℂ) (_root_.MIPStarRE.QPBT.phaseSign t) = _root_.MIPStarRE.QPBT.phaseSign t := by
    intro t
    rw [← Complex.star_def]
    exact _root_.MIPStarRE.QPBT.star_phaseSign t
  simp_rw [map_mul, hstar]
  rw [Fintype.sum_prod_type]
  calc ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * rs.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (b * rs.2)) *
          (_root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * rs'.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (b * rs'.2)))
      = (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * rs.1)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (a * rs'.1))) *
          ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (b * rs.2)) *
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (b * rs'.2)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring
    _ = _ := by
        rw [_root_.MIPStarRE.QPBT.sum_fixedCharacter_mul_fixedCharacter,
          _root_.MIPStarRE.QPBT.sum_fixedCharacter_mul_fixedCharacter]
        by_cases h1 : rs.1 = rs'.1 <;> by_cases h2 : rs.2 = rs'.2
        · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]
          push_cast
          ring
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (congrArg Prod.snd h))]
          simp
        · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 (congrArg Prod.fst h))]
          simp
        · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 (congrArg Prod.fst h))]
          simp
