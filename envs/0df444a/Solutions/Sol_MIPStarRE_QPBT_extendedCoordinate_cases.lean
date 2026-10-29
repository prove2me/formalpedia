-- Prove2me | solution 1 for MIPStarRE.QPBT.extendedCoordinate_cases
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:51:53.493142+00:00
-- url     : https://prove2.me/submissions/703ef9c7-7827-4b0d-8cab-9b01befd85fe

-- Generated proof for MIPStarRE.QPBT.extendedCoordinate_cases.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineUniform.lean. -/
/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/



/-! ## Uniform points of a line -/



/-! ## Resampling a uniform point along its canonical line -/



/-! ## Injectivity of the two block embeddings -/





/-! ## The blocks of an elementary coordinate direction -/

















/-! ## The coordinates occupied by the two blocks -/

/-- The `i`-th `X`-block coordinate of the extended space is its `i`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embX_val (m : ℕ) (i : Fin m) : (_root_.MIPStarRE.QPBT.embX m i).val = i.val := rfl

/-- The `i`-th `Z`-block coordinate of the extended space is its `(m + i)`-th
coordinate.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem embZ_val (m : ℕ) (i : Fin m) : (_root_.MIPStarRE.QPBT.embZ m i).val = m + i.val := rfl

/-- The extended coordinate carrying the first scalar is the coordinate
`2 m`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem alphaVar_val (m : ℕ) : (_root_.MIPStarRE.QPBT.alphaVar m).val = 2 * m := by
  simp [_root_.MIPStarRE.QPBT.alphaVar, _root_.MIPStarRE.QPBT.finCombineEquiv]

/-- The extended coordinate carrying the second scalar is the coordinate
`2 m + 1`.  Blueprint `def:combine-map`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`. -/
theorem betaVar_val (m : ℕ) : (_root_.MIPStarRE.QPBT.betaVar m).val = 2 * m + 1 := by
  simp [_root_.MIPStarRE.QPBT.betaVar, _root_.MIPStarRE.QPBT.finCombineEquiv]

/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/







end

end MIPStarRE.QPBT

/-!
# The branch data of the sub-line sampling procedure

The sampling procedure of the sub-line lemma draws a line kind, a stored
extended coordinate, and an unrestricted extended direction, and forms from
them the direction of the extended line: the elementary direction at the
stored coordinate in the axis branch, and the extended direction with the
coordinates preceding the stored coordinate replaced by zero in the diagonal
branch.  The two source lines are then read off the two coordinate blocks.
This module fixes the coordinate index that each source line must carry: the
stored coordinate itself when it belongs to that block, the first coordinate
otherwise.  With that choice the source block of the extended direction always
lies in the line spanned by the corresponding source direction, which is the
incidence hypothesis of the two projection lemmas.  The module also records
that moving an extended point to its canonical representative does not change
the canonical representative of either of its source blocks.

## References

The statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate blocks are those of `def:combine-map`, blueprint lines
445--480, paper lines 970--989; the prefix truncation is that of
blueprint `def:ld-question-distribution`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The three ranges of extended coordinates -/

theorem solution (m : ℕ) (k : Fin (2 * m + 2)) :
    (∃ i : Fin m, k = _root_.MIPStarRE.QPBT.embX m i) ∨ (∃ j : Fin m, k = _root_.MIPStarRE.QPBT.embZ m j) ∨
      k = _root_.MIPStarRE.QPBT.alphaVar m ∨ k = _root_.MIPStarRE.QPBT.betaVar m := by
  rcases lt_or_ge k.val m with hk | hk
  · exact Or.inl ⟨⟨k.val, hk⟩, Fin.ext (_root_.MIPStarRE.QPBT.embX_val m ⟨k.val, hk⟩).symm⟩
  · rcases lt_or_ge k.val (2 * m) with hk2 | hk2
    · refine Or.inr (Or.inl ⟨⟨k.val - m, by omega⟩, Fin.ext ?_⟩)
      rw [_root_.MIPStarRE.QPBT.embZ_val]
      change k.val = m + (k.val - m)
      omega
    · have hk3 : k.val < 2 * m + 2 := k.isLt
      rcases Nat.lt_or_ge k.val (2 * m + 1) with hk4 | hk4
      · refine Or.inr (Or.inr (Or.inl (Fin.ext ?_)))
        rw [_root_.MIPStarRE.QPBT.alphaVar_val]
        omega
      · refine Or.inr (Or.inr (Or.inr (Fin.ext ?_)))
        rw [_root_.MIPStarRE.QPBT.betaVar_val]
        omega
