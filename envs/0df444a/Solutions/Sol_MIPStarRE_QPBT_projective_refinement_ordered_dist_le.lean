-- Prove2me | solution 1 for MIPStarRE.QPBT.projective_refinement_ordered_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:18:24.512984+00:00
-- url     : https://prove2.me/submissions/eccfbbb5-e76a-4504-8b61-250e4cb058da

-- Generated proof for MIPStarRE.QPBT.projective_refinement_ordered_dist_le.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_postprocess_effect_mul_effect
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_sum_norm_mul_funIndexed_apply_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_two_mul_consistencyDefect

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.CombinedPointsWitness
end MIPStarRE.QPBT.CombinedPointsWitness
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective









































/-- Formalization-only auxiliary lemma for the agreement facts (Facts 4.13 and
4.14): every effect of a complete measurement is bounded by the identity. -/
theorem measurement_effect_le_one {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (a : α) :
    M.effect a ≤ 1 := by
  calc
    M.effect a ≤ ∑ b : α, M.effect b :=
      Finset.single_le_sum (fun b _ => M.pos b) (Finset.mem_univ a)
    _ = 1 := M.sum_eq_one

















































end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Support.lean. -/
/-! # Quantitative support for sandwiched measurements

This module develops the consistency and operator-distance estimates used
in the quantitative sandwich argument.

## References

Blueprint `lem:ld-sandwich` and `lem:ld-sandwich-measurement`; paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus

namespace SandwichProduct



























/-- A projective joint effect selects its matching postprocessing fiber when
multiplied on the right. This is the formalization-only identity
`lem:sandwich-postprocess-effect-right` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem effect_mul_postprocess_effect {α β ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (b : β) (a : α) :
    M.effect a * (M.postprocess f).effect b =
      if f a = b then M.effect a else 0 := by
  have h := congrArg Matrix.conjTranspose
    (_root_.MIPStarRE.QPBT.DistanceCalculus.postprocess_effect_mul_effect M hM f b a)
  rw [Matrix.conjTranspose_mul,
    _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a,
    _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian (M.postprocess f) b] at h
  by_cases hab : f a = b
  · simpa [hab, _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M a] using h
  · simpa [hab] using h





end SandwichProduct

end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems.lean. -/
/-! # State-dependent distance calculus

This module records the consistency and state-dependent distance estimates used
throughout the quantum Pauli basis test. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

The operator-level inequalities they rest on live in
`MIPStarRE.QPBT.Games.DistanceTheorems.Calculus`.

## References

The source results run from blueprint `fact:agreement` through
`lem:close-strategies-have-close-values`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461` and
`:531-540`. The observable conversion lemmas come from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:95-131`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus











/-- The squared effects of a POVM sum to at most the identity. This is the
formalization-only estimate `lem:sandwich-povm-square-sum` used in the
contractions underlying `lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_sum_adjoint_mul_le_one
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq I]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α I) :
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ 1 := by
  calc
    ∑ a : α, (M.effect a)ᴴ * M.effect a ≤ ∑ a : α, M.effect a := by
      apply Finset.sum_le_sum
      intro a _
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian]
      exact _root_.LIDT.MIPStarRE.Quantum.sq_le_self (M.pos a) (_root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_le_one M a)
    _ = 1 := M.sum_eq_one























end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/BipartiteTransport.lean. -/
/-!
# Bipartite estimates and transport for the expanded line measurements

This module collects the generic distance estimates used by items 2 and 3 of
the expanded-line consistency lemma, and the identities that transport the
placed families of the six-register expanded state to the two opposite-
placement bipartitions. The generic estimates are: the distance between two
oppositely placed complete measurements is at most twice the complement of
their diagonal overlap (`fact:agreement`), and a projective family compared
with itself followed by an effect selected through a coarse-graining is at
most as far as the coarse-grained families are from each other
(`fact:add-a-proj2` for a projective refinement). The transport identities
are formalization-only auxiliaries: they carry a relation between placed
operators on the six-register expanded state to the product shape in which the
generic estimates are stated, a step the source leaves implicit.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`, and
the generic estimates `fact:agreement` and `fact:add-a-proj2` of
`blueprint/src/chapter/ch12_qpbt_games.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Generic bipartite estimates -/

namespace DistanceCalculus

/-- A projective effect is absorbed by the postprocessed effect of the fiber
containing its own outcome. Formalization-only auxiliary for the projective
refinement of `fact:add-a-proj2` used by `eq:qld-comm-line-pt-cons`. -/
theorem effect_mul_postprocess_effect_self {α β ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement α ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M) (g : α → β) (a : α) :
    M.effect a * (M.postprocess g).effect (g a) = M.effect a := by
  simpa using _root_.MIPStarRE.QPBT.SandwichProduct.effect_mul_postprocess_effect M hM g (g a) a







end DistanceCalculus



end

end MIPStarRE.QPBT

/-!
# Ordered products selected by a global projective measurement

The point comparison of a projective measurement can be refined to its original
outcomes and composed with the two combined-point ordered-product estimates.
All bounds are on the actual expanded state and retain the complete outcome sum.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1283-1300`.
These are auxiliary estimates for issue Dengnifer/MIPStarRE-QPBT-bak#513, not the global-pair
constructor.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution {X Γ α ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype Γ] [DecidableEq Γ]
    [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (R : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ι) (hR : _root_.MIPStarRE.QPBT.Measurement.IsProjective R)
    (ev : X → Γ → α) (A B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement α ι) (T : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) (eta deltaSelf deltaOrder : ℝ)
    (hpoint : _root_.MIPStarRE.QPBT.consistencyDefect μ
      (fun x a => (R.postprocess (ev x)).effect a) (fun x a => (B x).effect a) ψ ≤ eta)
    (hself : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (B x).effect a)
      (fun x a => (A x).effect a) ψ ≤ deltaSelf)
    (horder : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x a => (A x).effect a) T ψ ≤ deltaOrder) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * T x (ev x g)) ψ ≤
        4 * eta + 4 * deltaSelf + 4 * deltaOrder := by
  have hlift (U V : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x g => R.effect g * U x (ev x g))
        (fun x g => R.effect g * V x (ev x g)) ψ ≤ _root_.MIPStarRE.QPBT.opFamilyDistSq μ U V ψ := by
    unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
    apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
    intro x
    simpa only [mul_sub] using _root_.MIPStarRE.QPBT.DistanceCalculus.sum_norm_mul_funIndexed_apply_le (ev x) R.effect
      (fun a => U x a - V x a) ψ (_root_.MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one R)
  have hinsert : _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun _ g => R.effect g)
      (fun x g => R.effect g * (B x).effect (ev x g)) ψ ≤ 2 * eta := by
    have h := hlift (fun x a => (R.postprocess (ev x)).effect a)
      (fun x a => (B x).effect a)
    simp only [_root_.MIPStarRE.QPBT.DistanceCalculus.effect_mul_postprocess_effect_self R hR] at h
    exact h.trans ((_root_.MIPStarRE.QPBT.opFamilyDistSq_le_two_mul_consistencyDefect μ
      (fun x => R.postprocess (ev x)) B ψ).trans (mul_le_mul_of_nonneg_left hpoint
        (by norm_num)))
  have htail := (hlift (fun x a => (B x).effect a) T).trans
    (_root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ (fun x a => (B x).effect a)
      (fun x a => (A x).effect a) T ψ deltaSelf deltaOrder hself horder)
  have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ (fun _ g => R.effect g)
    (fun x g => R.effect g * (B x).effect (ev x g))
    (fun x g => R.effect g * T x (ev x g)) ψ (2 * eta)
    (2 * deltaSelf + 2 * deltaOrder) hinsert htail
  convert h using 1
  ring
