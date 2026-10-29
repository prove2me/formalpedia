-- Prove2me | solution 1 for MIPStarRE.QPBT.ldStrategyToDirect_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:32:45.784445+00:00
-- url     : https://prove2.me/submissions/c00eaf1a-311a-49e0-9855-87ab071c4278

-- Generated proof for MIPStarRE.QPBT.ldStrategyToDirect_value_eq.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiber
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_SeedFiberValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ldCL_ldSpaceOfDirectResidue_directLdMap
import Theorems.Thm_MIPStarRE_QPBT_parseLdQuestion_ldCL_ofDirectResidue

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Correspondence.lean. -/
/-!
# Question correspondence for the directly indexed low-degree game

The finite-field coordinates, polynomial answers, and question law of the
directly indexed game are equivalent to their seed-indexed and low individual
degree counterparts.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:98-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Parameters and finite-field coordinates -/













/-! ## Bounded coefficient vectors -/

















/-! ## Parameters and answers of the two QPBT game presentations -/







/-! ## Parsing seed-indexed questions -/















/-- The seed-indexed and direct predicates agree after parsing questions and
transporting answers. -/
theorem ldWinPredicate_parse (L : _root_.MIPStarRE.QPBT.LdParams)
    (x y : _root_.MIPStarRE.QPBT.LdQuestion L) (a b : _root_.MIPStarRE.QPBT.LdAnswer L) :
    _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
        (_root_.MIPStarRE.QPBT.parseLdQuestion L x) (_root_.MIPStarRE.QPBT.parseLdQuestion L y)
        (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L a) (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L b) =
      _root_.MIPStarRE.QPBT.ldWinPredicate L x y a b := by
  rcases x with ⟨tx, x⟩
  rcases y with ⟨ty, y⟩
  cases tx <;> cases ty <;> cases a <;> cases b <;> rfl

/-! ## Exact question-law transport -/











end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/SeedFiber.lean. -/
/-!
# Seed-fiber dilation for the directly indexed low-degree game

This module dilates a seed-indexed low-degree strategy by a maximally
correlated residue register.  Block-diagonal projective measurements retain
arbitrary dependence on the seed within each `chiIndex` fiber.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Projective block measurements -/













/-! ## The correlated residue state -/









/-! ## From the seed-indexed game to the direct game -/













/-- Coordinate formula for the correlated residue lift. -/
theorem seedFiberLiftedState_apply
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    (i : S.ιA) (j : S.ιB)
    (r s : Fin (L.q / L.m)) :
    _root_.MIPStarRE.QPBT.seedFiberLiftedState S L ((i, r), (j, s)) =
      if r = s then
        S.ψ (i, j) * (Real.sqrt (Fintype.card (Fin (L.q / L.m)) : ℝ) : ℂ)⁻¹
      else 0 := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  simp [_root_.MIPStarRE.QPBT.seedFiberLiftedState, _root_.MIPStarRE.QPBT.reindexState, _root_.MIPStarRE.QPBT.vecTensor, _root_.MIPStarRE.QPBT.seedResidueAncilla,
    _root_.MIPStarRE.QPBT.eprState, _root_.MIPStarRE.QPBT.prodShuffle]

end

end MIPStarRE.QPBT

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Strategy.lean. -/
/-!
# Strategy transport for the directly indexed low-degree game

This module reads one coordinate of a projective directly indexed strategy as
a two-space low individual degree test strategy.  The question and answer
transport of `Transport.Questions` supplies the canonical direct question of
every LDT line, with the reversed coordinate order and the leading index of
the decoded diagonal direction, together with answer readouts that are
covariant under line rebasing; this establishes all four covariance
conditions of `ProjStrat`.  The module also records exact Born-weight
formulas for both directions of strategy transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:49-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## From a direct strategy to an LDT strategy -/















































/-- Correlated residue registers turn two block-diagonal effects into the
uniform average of their matching source-block Born weights. -/
private theorem seedFiberBlockBornAmplitude
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    (A : Fin (L.q / L.m) → _root_.LIDT.MIPStarRE.Quantum.Op S.ιA)
    (B : Fin (L.q / L.m) → _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    vectorBornAmplitude (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℂ)⁻¹ *
        ∑ residue, vectorBornAmplitude S.ψ (A residue) (B residue) := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  unfold vectorBornAmplitude _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    dotProduct, Matrix.mulVec]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [_root_.MIPStarRE.QPBT.seedFiberLiftedState_apply, Matrix.blockDiagonal_apply,
    mul_assoc, mul_comm]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring_nf
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← mul_assoc]
  congr 1
  exact _root_.MIPStarRE.QPBT.inv_sqrt_natCast_mul_self (L.q / L.m)

/-- Correlated residue registers give the uniform average of the source-block
Born weights. -/
private theorem seedFiberBlockBornWeight
    {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) (L : _root_.MIPStarRE.QPBT.LdParams)
    (A : Fin (L.q / L.m) → _root_.LIDT.MIPStarRE.Quantum.Op S.ιA)
    (B : Fin (L.q / L.m) → _root_.LIDT.MIPStarRE.Quantum.Op S.ιB) :
    vectorBornWeight (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L)
        (Matrix.blockDiagonal A) (Matrix.blockDiagonal B) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue, vectorBornWeight S.ψ (A residue) (B residue) := by
  unfold vectorBornWeight
  rw [seedFiberBlockBornAmplitude]
  simp [Complex.mul_re, Complex.inv_re, Complex.inv_im]

/-- The Born weight of the direct strategy obtained by dilating a seed-indexed
strategy with a correlated residue register is the uniform average of the
original seed-dependent Born weights over that residue. -/
theorem ldStrategyToDirect_bornWeight
    (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L))
    (x y : _root_.MIPStarRE.QPBT.DirectLdQuestion L.toDirectLdParams)
    (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams) :
    _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S) x y a b =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
        ∑ residue,
          _root_.MIPStarRE.QPBT.outcomeWeight S
            (_root_.MIPStarRE.QPBT.seededLdQuestion L x residue)
            (_root_.MIPStarRE.QPBT.seededLdQuestion L y residue)
            ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a)
            ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b) := by
  change vectorBornWeight (_root_.MIPStarRE.QPBT.seedFiberLiftedState S L)
      (Matrix.blockDiagonal fun residue =>
        (S.A (_root_.MIPStarRE.QPBT.seededLdQuestion L x residue)).effect
          ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a))
      (Matrix.blockDiagonal fun residue =>
        (S.B (_root_.MIPStarRE.QPBT.seededLdQuestion L y residue)).effect
          ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b)) = _
  exact seedFiberBlockBornWeight S L _ _









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/SeedFiberValue.lean. -/
/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section







/-- At the canonical direct questions of a common direct sample, the accepted
mass of the dilation is the uniform residue average of the accepted mass of
the original strategy at the seeded canonical questions. -/
private theorem directAcceptedMass_ldStrategyToDirect (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L)) (tA tB : _root_.MIPStarRE.QPBT.LdType)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace L.toDirectLdParams) :
    directAcceptedMass L.toDirectLdParams (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S)
        (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
        (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) =
      (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ * ∑ residue : Fin (L.q / L.m),
        ldAcceptedMass L S
          (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
          (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue)) := by
  classical
  have hwin : ∀ (residue : Fin (L.q / L.m)) (a b : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams),
      _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
          (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
          (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a b =
        _root_.MIPStarRE.QPBT.ldWinPredicate L
          (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
          (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
          ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a) ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b) := by
    intro residue a b
    rw [← _root_.MIPStarRE.QPBT.ldWinPredicate_parse, _root_.MIPStarRE.QPBT.parseLdQuestion_ldCL_ofDirectResidue,
      _root_.MIPStarRE.QPBT.parseLdQuestion_ldCL_ofDirectResidue, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  have hseeded : ∀ (t : _root_.MIPStarRE.QPBT.LdType) (residue : Fin (L.q / L.m)),
      _root_.MIPStarRE.QPBT.seededLdQuestion L (t, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams t sample) residue =
        (t, _root_.MIPStarRE.QPBT.ldCL L t (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue)) := by
    intro t residue
    exact congrArg (fun z => (t, z))
      (_root_.MIPStarRE.QPBT.ldCL_ldSpaceOfDirectResidue_directLdMap L t sample residue)
  have hmass : ∀ residue : Fin (L.q / L.m),
      ldAcceptedMass L S
          (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
          (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue)) =
        ∑ a' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
          ∑ b' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
            if _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
                (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
                (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' then
              _root_.MIPStarRE.QPBT.outcomeWeight S
                (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a') ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b')
            else 0 := by
    intro residue
    unfold ldAcceptedMass
    rw [← Equiv.sum_comp (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Equiv.sum_comp (_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hwin residue a' b']
  unfold directAcceptedMass
  simp only [hmass]
  calc
    ∑ a' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
        ∑ b' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
          (if _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
              (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
              (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' then
            _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S)
              (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
              (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b'
          else 0) =
        ∑ a' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
          ∑ b' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
            ∑ residue : Fin (L.q / L.m),
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
                    (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
                    (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' then
                  _root_.MIPStarRE.QPBT.outcomeWeight S
                    (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a') ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b')
                else 0) := by
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
      by_cases hc : _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
          (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
          (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' = true
      · simp only [hc, if_true]
        rw [← Finset.mul_sum, _root_.MIPStarRE.QPBT.ldStrategyToDirect_bornWeight]
        simp only [hseeded]
      · simp [hc]
    _ = ∑ a' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
          ∑ residue : Fin (L.q / L.m),
            ∑ b' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
                    (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
                    (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' then
                  _root_.MIPStarRE.QPBT.outcomeWeight S
                    (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a') ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b')
                else 0) :=
      Finset.sum_congr rfl fun a' _ => Finset.sum_comm
    _ = ∑ residue : Fin (L.q / L.m),
          ∑ a' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
            ∑ b' : _root_.MIPStarRE.QPBT.DirectLdAnswer L.toDirectLdParams,
              (Fintype.card (Fin (L.q / L.m)) : ℝ)⁻¹ *
                (if _root_.MIPStarRE.QPBT.directLdWinPredicate L.toDirectLdParams
                    (tA, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tA sample)
                    (tB, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams tB sample) a' b' then
                  _root_.MIPStarRE.QPBT.outcomeWeight S
                    (tA, _root_.MIPStarRE.QPBT.ldCL L tA (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    (tB, _root_.MIPStarRE.QPBT.ldCL L tB (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue))
                    ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm a') ((_root_.MIPStarRE.QPBT.ldDirectAnswerEquiv L).symm b')
                else 0) :=
      Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun residue _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [Finset.mul_sum]



end

end MIPStarRE.QPBT

/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.ldGame L)) :
    (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S).value = S.value := by
  classical
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  have hsymm : ∀ b : ((_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) × _root_.MIPStarRE.QPBT.DirectLdSpace L.toDirectLdParams) ×
      Fin (L.q / L.m),
      (_root_.MIPStarRE.QPBT.ldQuestionSeedFiberEquiv L).symm b =
        (b.1.1, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L b.1.2 b.2) :=
    fun b => rfl
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.directLdQuestionDistribution L.toDirectLdParams)
      (fun xy => directAcceptedMass L.toDirectLdParams (_root_.MIPStarRE.QPBT.ldStrategyToDirect L S) xy.1 xy.2) =
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.ldQuestionDistribution L) (fun xy => ldAcceptedMass L S xy.1 xy.2)
  unfold _root_.MIPStarRE.QPBT.directLdQuestionDistribution _root_.MIPStarRE.QPBT.ldQuestionDistribution
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map,
    _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.MIPStarRE.QPBT.ldQuestionSeedFiberEquiv L)]
  simp only [hsymm]
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod (fun (src : (_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) × _root_.MIPStarRE.QPBT.DirectLdSpace L.toDirectLdParams)
      (residue : Fin (L.q / L.m)) =>
      ldAcceptedMass L S
        (src.1.1, _root_.MIPStarRE.QPBT.ldCL L src.1.1 (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L src.2 residue))
        (src.1.2, _root_.MIPStarRE.QPBT.ldCL L src.1.2 (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L src.2 residue)))]
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro src
  rw [directAcceptedMass_ldStrategyToDirect, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_eq_inv_card_mul_sum]
