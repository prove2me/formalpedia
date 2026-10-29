-- Prove2me | solution 1 for MIPStarRE.QPBT.avgOver_rpow_quarter_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:03:55.796821+00:00
-- url     : https://prove2.me/submissions/380e8c98-3e56-49c9-8cf3-35739be68ff6

-- Generated proof for MIPStarRE.QPBT.avgOver_rpow_quarter_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Points/Orthonormalization.lean. -/
/-!
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Jensen's inequality for the fourth root -/

/-- The fourth root of a nonnegative real is the iterated square root. -/
theorem rpow_quarter_eq_sqrt_sqrt {t : ℝ} (ht : 0 ≤ t) :
    Real.rpow t (1 / 4 : ℝ) = Real.sqrt (Real.sqrt t) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  norm_num



/-! ## The bipartition with Bob's registers first -/





end

end MIPStarRE.QPBT

/-!
# Orthonormalization of the sandwich POVM

For each fixed point pair `(x, z)`, the sandwich POVM `R^{x,z}` on one
register placement is consistent with the sandwich POVM on the opposite
placement, with the consistency defect bounded by
`ProjectiveSetting.sandwichDefectBound`.  The orthonormalization lemma
`lem:ortho`, in its explicit-constant form
`projective_rounding_with_explicit_constant`, therefore produces a projective
measurement `Q^{x,z}` on the original local space, within `220 · c^{1/4}` of
`R^{x,z}` on the expanded state, where `c` is that bound.  Choosing such a
measurement for every pair and averaging, the concavity of `t ↦ t^{1/4}`
turns the average of the fiberwise errors into the same function of the
average defect.

The orthonormalization lemma is stated for a bipartite state whose first
tensor factor carries the POVM to be rounded.  The two bipartitions used are
`AA' | BA''(B'B'')`, for Alice's measurements, and `BA'' | AA'(B'B'')`, for
Bob's; the second is introduced here.

## Main results

* `baAaBipartition` with its two placement lemmas.
* `avgOver_rpow_quarter_le`: Jensen's inequality for the fourth root.
* `ProjectiveSetting.exists_projective_close_sandwich`: the fiberwise
  orthonormalization, for any bipartition exhibiting the two placements as
  the two tensor factors.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:786-790`
(the application of the orthonormalization lemma), blueprint
`blueprint/src/chapter/ch15_qpbt_combining.tex:870-878` (`lem:qld-4-10`), and
`blueprint/src/chapter/ch14_qpbt_observables.tex:395-464` (`lem:ortho`); the
route is explained in `docs/paper-gaps/qpbt_combined-points-field-valued.tex`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Jensen's inequality for the fourth root -/

theorem solution {X : Type*} (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (h𝒟 : ∑ x ∈ 𝒟.support, 𝒟.weight x ≤ 1) (b : X → ℝ) (hb : ∀ x, 0 ≤ b x) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun x => Real.rpow (b x) (1 / 4 : ℝ)) ≤
      Real.rpow (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 b) (1 / 4 : ℝ) := by
  have h1 : |avgOver 𝒟 (fun x => Real.sqrt (Real.sqrt (b x)))| ≤
      Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun x => Real.sqrt (b x))) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun x => by rw [abs_of_nonneg (Real.sqrt_nonneg _)])
      (fun x => Real.sqrt_nonneg _) h𝒟
  have h2 : |avgOver 𝒟 (fun x => Real.sqrt (b x))| ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 b) :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise 𝒟 _ _
      (fun x => by rw [abs_of_nonneg (Real.sqrt_nonneg _)]) hb h𝒟
  have havg : 0 ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 b := _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg 𝒟 b hb
  rw [_root_.MIPStarRE.QPBT.rpow_quarter_eq_sqrt_sqrt havg]
  calc _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun x => Real.rpow (b x) (1 / 4 : ℝ))
      = _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun x => Real.sqrt (Real.sqrt (b x))) :=
        _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun x => _root_.MIPStarRE.QPBT.rpow_quarter_eq_sqrt_sqrt (hb x)
    _ ≤ |avgOver 𝒟 (fun x => Real.sqrt (Real.sqrt (b x)))| := le_abs_self _
    _ ≤ Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun x => Real.sqrt (b x))) := h1
    _ ≤ Real.sqrt (Real.sqrt (_root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 b)) :=
        Real.sqrt_le_sqrt (le_trans (le_abs_self _) h2)
