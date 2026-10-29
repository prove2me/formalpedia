-- Prove2me | solution 1 for MIPStarRE.QPBT.PolynomialImageBounds.exists_common_exceptional_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:08:28.549309+00:00
-- url     : https://prove2.me/submissions/71720a47-f8c5-4fd8-9b90-00a003b16c13

-- Generated proof for MIPStarRE.QPBT.PolynomialImageBounds.exists_common_exceptional_coefficient.
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
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Distribution.IsProbability
end LIDT.MIPStarRE.LDT.Distribution.IsProbability
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace LIDT.MIPStarRE.Quantum.Measurement
end LIDT.MIPStarRE.Quantum.Measurement
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/- Source helpers from QPBT/Combining/PolynomialFiberBounds.lean. -/
/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem exists_nonconstant_coeff {R : Type*} [CommSemiring R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (hp : ¬ ∃ r, p = MvPolynomial.C r) :
    ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 := by
  classical
  by_contra! h
  apply hp
  refine ⟨p.coeff 0, ?_⟩
  ext e
  by_cases he : e = 0
  · simp [he]
  · simp [MvPolynomial.coeff_C, Ne.symm he, h e he]





variable {ι : Type*} [Fintype ι] [DecidableEq ι]







end

end MIPStarRE.QPBT.PolynomialImageBounds

/- Source helpers from QPBT/Upstream.lean. -/
/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `f382c801026f53a9efc260fdee707cb35e0adb15`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder



namespace LIDT
namespace MIPStarRE.LDT



/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  unfold _root_.LIDT.MIPStarRE.LDT.avgOver _root_.LIDT.MIPStarRE.LDT.uniformDistribution _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, one_div, Finset.mul_sum]


end MIPStarRE.LDT
end LIDT

/- Source helpers from QPBT/Combining/PolynomialImageBounds.lean. -/
/-!
# Indicator-weighted ordered products

This module proves the local norm calculation in `eq:qld-g-prime`. The state
vector is not assumed normalized: its squared norm controls the exceptional
coefficient, so the estimate can be summed over all polynomial outcomes.
The measurements act on an arbitrary finite space, which includes either
player's placed expanded measurements.

The coefficient-polynomial argument also bounds mass outside the scalar-linear
image, with its actual ordered-correlation error displayed in the conclusion.
These are auxiliary estimates, not the global polynomial-pair construction.
The remaining block-separation and construction obligations are recorded in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#513.

Only the dependency chain needed for these estimates is exposed; supporting
lemmas remain private.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1289-1326`,
  especially `eq:qld-g-42`, `eq:qld-g-43`, and `eq:qld-g-prime`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace PolynomialImageBounds

variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

































/-- Schwartz--Zippel in the uniform-average notation used by the coefficient
and fiber calculations in `eq:qld-g-prime-bound` and `eq:qld-g-2`. -/
theorem avg_eval_eq_le {n D : ℕ} (p r : MvPolynomial (Fin n) F)
    (hne : p ≠ r) (hp : p.totalDegree ≤ D) (hr : r.totalDegree ≤ D) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
      (fun u => if MvPolynomial.eval u p = MvPolynomial.eval u r then 1 else 0) ≤
      (D : ℝ) / Fintype.card F := by
  have hsz := _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree hne hp hr
  calc
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability n F p r : ℝ) := by
      simp [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum,
        _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability, div_eq_mul_inv, mul_comm]
    _ ≤ (((D : ℚ≥0) / Fintype.card F : ℚ≥0) : ℝ) := by exact_mod_cast hsz
    _ = _ := by simp













end PolynomialImageBounds

end

end MIPStarRE.QPBT

/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem solution {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D) :
    ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 ∧
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F))
        (fun z => if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) ≤
          (C : ℝ) / Fintype.card F ∧
      ∀ z : Fin k → F, MvPolynomial.eval z (p.coeff e) ≠ 0 → ∀ b : F,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
          (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
            then 1 else 0) ≤ (D : ℝ) / Fintype.card F := by
  obtain ⟨e, he, hc⟩ := exists_nonconstant_coeff p hp
  refine ⟨e, he, hc, ?_, ?_⟩
  · simpa using _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_eval_eq_le (p.coeff e) 0 hc (hcoeff e) (by simp)
  · intro z hz b
    have hne : MvPolynomial.map (MvPolynomial.eval z) p ≠ MvPolynomial.C b := by
      intro h
      apply hz
      have h' := congrArg (fun polynomial => polynomial.coeff e) h
      simpa [MvPolynomial.coeff_map, MvPolynomial.coeff_C, Ne.symm he] using h'
    have hd : (MvPolynomial.map (MvPolynomial.eval z) p).totalDegree ≤ D :=
      (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdegree
    simpa using _root_.MIPStarRE.QPBT.PolynomialImageBounds.avg_eval_eq_le _ (MvPolynomial.C b) hne hd (by simp)
