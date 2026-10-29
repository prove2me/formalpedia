-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_restrictedLinePointDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:11:48.666031+00:00
-- url     : https://prove2.me/submissions/b562c3b5-6243-494b-97f5-0d024e17fb0a

-- Generated proof for MIPStarRE.QPBT.avgOver_restrictedLinePointDist_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_aLinePointDist_eq_bind_restricted
import Theorems.Thm_MIPStarRE_QPBT_avgOver_bind
import Theorems.Thm_MIPStarRE_QPBT_dLinePointDist_eq_bind_restricted

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistributionAux.lean. -/
/-! # Operations on finite distributions

Finite distributions support products, convex mixtures, dependent binds,
normalized restrictions, and push-forwards.  Uniform laws are preserved by
bijections and balanced maps, their product projections are uniform, and
dependent uniform sampling agrees with push-forward from a product.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

















/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/





















/-! ## Elementary rewriting of finite distributions -/







/-! ## Reindexing a dependent mixture -/







/-! ## Associativity of dependent mixtures -/



/-! ## Products with an independent factor -/



/-! ## The equal two-term mixture as a uniform dependent mixture -/



/-! ## Averages of the distribution operations -/





/-- Formalization-only auxiliary: one component of a uniform mixture carries at
most the whole nonnegative average, scaled by its mixture weight.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_bind_uniform_component_le {ι β : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [DecidableEq β]
    (ν : ι → _root_.LIDT.MIPStarRE.LDT.Distribution β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (i : ι) :
    1 / (Fintype.card ι : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (ν i) f ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι) ν) f := by
  classical
  rw [_root_.MIPStarRE.QPBT.avgOver_bind]
  have hterm : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι).weight j * _root_.LIDT.MIPStarRE.LDT.avgOver (ν j) f := fun j _ =>
    mul_nonneg ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι).nonnegative j) (_root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ hf)
  have hsingle := Finset.single_le_sum
    (f := fun j => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ι).weight j * _root_.LIDT.MIPStarRE.LDT.avgOver (ν j) f)
    hterm (Finset.mem_univ i)
  rw [_root_.MIPStarRE.QPBT.uniformDistribution_weight_apply] at hsingle
  exact hsingle

end MIPStarRE.QPBT

/-!
# Error inflation of restricted line-point averages

This module records how a nonnegative average over the line-point distribution
transfers to one restricted component.  The line-point law places weight
`1 / 2` on each of its two kinds and, inside each kind, weight `1 / m` on each
coordinate index, so every restricted component carries mixture weight
`1 / (2 m)` and a nonnegative average inflates by at most `2 m`.

## References

The estimates are items 1 and 2 of blueprint
`lem:restricted-line-mixture-bounds`, formalizing the unlabelled estimates at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement



/-! ## Inflation of a restricted line-point average -/

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (f : (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kind : _root_.MIPStarRE.QPBT.LineKind) (i : Fin P.m) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f := by
  classical
  haveI : Nonempty (Fin P.m) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.one_le_m)
  have hm : (0 : ℝ) < (P.m : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_m
  have hAnonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist P.toLdParams) f :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ hf
  have hDnonneg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist P.toLdParams) f :=
    _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg _ _ hf
  have hmixture : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f =
      1 / 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist P.toLdParams) f +
        (1 - 1 / 2) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist P.toLdParams) f :=
    _root_.MIPStarRE.QPBT.avgOver_mix _ _ _ _ _ f
  -- Each kind is bounded by twice the full line-point average.
  have hsum : 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist P.toLdParams) f +
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist P.toLdParams) f := by
    rw [hmixture]
    ring
  have hAle : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.aLinePointDist P.toLdParams) f ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f := by
    rw [hsum]
    exact le_add_of_nonneg_right hDnonneg
  have hDle : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.dLinePointDist P.toLdParams) f ≤
      2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f := by
    rw [hsum]
    exact le_add_of_nonneg_left hAnonneg
  -- The coordinate index contributes a further factor `m`.
  have hcomponent : ∀ (ν : Fin P.m → _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams ×
      (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) (μ : _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.LineDesc P.toLdParams ×
      (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))),
      μ = _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m)) ν →
      _root_.LIDT.MIPStarRE.LDT.avgOver μ f ≤ 2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f →
      _root_.LIDT.MIPStarRE.LDT.avgOver (ν i) f ≤ 2 * (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f := by
    intro ν μ hbind hle
    have hcomp := _root_.MIPStarRE.QPBT.avgOver_bind_uniform_component_le ν f hf i
    rw [Fintype.card_fin, ← hbind] at hcomp
    have hstep : _root_.LIDT.MIPStarRE.LDT.avgOver (ν i) f ≤ (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver μ f := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm] at hcomp
      rw [mul_comm]
      exact hcomp
    calc _root_.LIDT.MIPStarRE.LDT.avgOver (ν i) f ≤ (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver μ f := hstep
      _ ≤ (P.m : ℝ) * (2 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f) := by
          exact mul_le_mul_of_nonneg_left hle (le_of_lt hm)
      _ = 2 * (P.m : ℝ) * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist P.toLdParams) f := by ring
  cases kind with
  | axis =>
      exact hcomponent (_root_.MIPStarRE.QPBT.restrictedALineDist P.toLdParams) _
        (_root_.MIPStarRE.QPBT.aLinePointDist_eq_bind_restricted P.toLdParams) hAle
  | diagonal =>
      exact hcomponent (_root_.MIPStarRE.QPBT.restrictedDLineDist P.toLdParams) _
        (_root_.MIPStarRE.QPBT.dLinePointDist_eq_bind_restricted P.toLdParams) hDle
