-- Prove2me | solution 1 for MIPStarRE.QPBT.polynomialAgreement_avg_eq_agreementProbability
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:23.954487+00:00
-- url     : https://prove2.me/submissions/c90df54d-508b-4f18-93e4-44bb4c179083

-- Generated proof for MIPStarRE.QPBT.polynomialAgreement_avg_eq_agreementProbability.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The linear form in the combining variables and its collision estimate

At a fixed point `u` of the original space, the combined polynomial of a tuple
`g` restricts, as a function of the combining variables `α`, to the linear form
`α ↦ ∑_{r < k} g_r(u) α_r`.  The recovery step of the reduction compares two
such linear forms: if the tuple of values `(g_0(u), …, g_{k-1}(u))` differs from
a tuple `b` of answers, then the two linear forms are distinct polynomials of
total degree at most one, so by the Schwartz--Zippel lemma they agree at a
uniformly sampled `α` with probability at most `1/q`.

This module proves that estimate.  It is the quantitative content of the last
paragraph of the source proof, where the same bound is obtained for the
combining map of the surface game.

## Main statements

* `combiningLinearForm_injective` — a linear form determines its coefficients.
* `combiningLinearForm_agreementProbability_le` — the Schwartz--Zippel bound.
* `directCombiningCollision_avg_le` — the bound in the averaged form used by the
  consistency calculus of the directly indexed game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1484-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## The linear form of a tuple of scalars -/













/-! ## The averaged form -/

theorem solution {m : ℕ} {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] (g h : MvPolynomial (Fin m) K) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun u => if MvPolynomial.eval u g = MvPolynomial.eval u h then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) =
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability m K g h : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun u => if MvPolynomial.eval u g = MvPolynomial.eval u h then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
      = ∑ u : Fin m → K,
          if MvPolynomial.eval u g = MvPolynomial.eval u h then
            (Fintype.card K ^ m : _root_.LIDT.MIPStarRE.LDT.Error)⁻¹ else 0 := by
        simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution]
    _ = ∑ u ∈ Finset.univ.filter (fun u : Fin m → K =>
          MvPolynomial.eval u g = MvPolynomial.eval u h),
          (Fintype.card K ^ m : _root_.LIDT.MIPStarRE.LDT.Error)⁻¹ := by
        rw [← Finset.sum_filter]
    _ = (((Finset.univ.filter fun u : Fin m → K =>
          MvPolynomial.eval u g = MvPolynomial.eval u h).card : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) *
          (Fintype.card K ^ m : _root_.LIDT.MIPStarRE.LDT.Error)⁻¹ := by
        simp
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability m K g h : _root_.LIDT.MIPStarRE.LDT.Error) := by
        simp [_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability, div_eq_mul_inv]
