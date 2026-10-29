-- Prove2me | solution 1 for MIPStarRE.QPBT.uniformDistribution_map_directLine_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:09.161335+00:00
-- url     : https://prove2.me/submissions/7b4a0645-6921-403a-8a84-5d604adcb838

-- Generated proof for MIPStarRE.QPBT.uniformDistribution_map_directLine_add_smul.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_Distribution_bind_const
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_map_lineRepMap_add_smul

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section









instance instNonemptyFinM_1 (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Nonempty (Fin D.m) := ⟨D.firstIndex⟩



















/-! ## Finite direct-line carrier -/

















































end

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



















/-- Formalization-only lemma: binding a uniform distribution to a family of
uniformly seeded push-forwards is the push-forward of the uniform distribution
on the product.  This is `lem:uniform-bind-map` in blueprint chapter 13. -/
theorem bind_uniformDistribution_map {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α → β → γ) :
    _root_.MIPStarRE.QPBT.Distribution.bind (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (fun a => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).map (g a)) =
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).map fun p => g p.1 p.2 :=
  _root_.MIPStarRE.QPBT.bind_uniformOnFinset_map (Finset.univ : Finset α) id Function.injective_id
    Finset.image_id g

/-! ## Elementary rewriting of finite distributions -/







/-! ## Reindexing a dependent mixture -/







/-! ## Associativity of dependent mixtures -/



/-! ## Products with an independent factor -/



/-! ## The equal two-term mixture as a uniform dependent mixture -/



/-! ## Averages of the distribution operations -/







end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/UniformLinePoint.lean. -/
/-!
# A uniform point of the extended space from the sub-line law

The first scalar estimate in the combining argument samples an extended line
from the directly indexed sub-line witness and then a uniform affine parameter.
This module records that the resulting extended point is uniform and hence
that its two source coordinate blocks are independent uniform points.
This is an auxiliary law. Transport to the source's seed-indexed extended
distribution remains open, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

These statements support `lem:claim-17-1` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  The paper uses this sampling
fact at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1159-1166`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-- If every slice of a map of a pair carries the second uniform law to one
fixed law, then the map carries the uniform law of the pair to that law. -/
theorem uniformDistribution_map_uncurry {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α × β → γ) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution γ)
    (hg : ∀ a, (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).map (fun b => g (a, b)) = ν) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)).map g = ν := by
  rw [← _root_.MIPStarRE.QPBT.bind_uniformDistribution_map (fun a b => g (a, b)),
    show (fun a => (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β).map (fun b => g (a, b))) =
      fun _ => ν from funext hg]
  exact _root_.MIPStarRE.QPBT.Distribution.bind_const _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability α) ν









end



end MIPStarRE.QPBT

/-!
# A uniform point of the extended space from the sub-line law

The first scalar estimate in the combining argument samples an extended line
from the directly indexed sub-line witness and then a uniform affine parameter.
This module records that the resulting extended point is uniform and hence
that its two source coordinate blocks are independent uniform points.
This is an auxiliary law. Transport to the source's seed-indexed extended
distribution remains open, as recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## References

These statements support `lem:claim-17-1` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.  The paper uses this sampling
fact at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1159-1166`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (V : Fin D.m × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) → (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D × _root_.MIPStarRE.QPBT.DirectScalarQ D)).map
        (fun p => _root_.MIPStarRE.QPBT.lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
          p.2 • V (p.1.index, p.1.direction)) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) := by
  classical
  let e : _root_.MIPStarRE.QPBT.DirectLdSpace D × _root_.MIPStarRE.QPBT.DirectScalarQ D ≃
      (Fin D.m × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) ×
        ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × _root_.MIPStarRE.QPBT.DirectScalarQ D) :=
    { toFun := fun p => ((p.1.index, p.1.direction), (p.1.point, p.2))
      invFun := fun w => (⟨w.2.1, w.1.1, w.1.2⟩, w.2.2)
      left_inv := by rintro ⟨⟨pt, i, dir⟩, t⟩; rfl
      right_inv := by rintro ⟨⟨i, dir⟩, pt, t⟩; rfl }
  have hequiv :
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D × _root_.MIPStarRE.QPBT.DirectScalarQ D)).map e =
        _root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin D.m × (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)) ×
          ((Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) × _root_.MIPStarRE.QPBT.DirectScalarQ D)) :=
    _root_.MIPStarRE.QPBT.uniformDistribution_map_equiv e
  have hmap :
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D × _root_.MIPStarRE.QPBT.DirectScalarQ D)).map
          (fun p => _root_.MIPStarRE.QPBT.lineRepMap (V (p.1.index, p.1.direction)) p.1.point +
            p.2 • V (p.1.index, p.1.direction)) =
        ((_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectLdSpace D × _root_.MIPStarRE.QPBT.DirectScalarQ D)).map e).map
          (fun w => _root_.MIPStarRE.QPBT.lineRepMap (V w.1) w.2.1 + w.2.2 • V w.1) := by
    rw [_root_.MIPStarRE.QPBT.Distribution.map_map]
    rfl
  rw [hmap, hequiv]
  refine _root_.MIPStarRE.QPBT.uniformDistribution_map_uncurry _ _ fun a => ?_
  exact _root_.MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul (V a)
