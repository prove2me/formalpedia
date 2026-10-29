-- Prove2me | solution 1 for MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_restricted_le_at
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:23:39.055891+00:00
-- url     : https://prove2.me/submissions/dd11d990-6e97-49af-918d-b25a8b58d628

-- Generated proof for MIPStarRE.QPBT.CombinedLinesWitness.one_sub_Z_overlap_restricted_le_at.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineBlocks
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineConstruct
import Definitions.Def_QPBT_QPBT_Combining_Lines_SubLineSeed
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Combining_ZEvalDeficit
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Expanded
import Definitions.Def_QPBT_QPBT_Observables_PointConsistency
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map
import Theorems.Thm_MIPStarRE_QPBT_CombinedLinesWitness_one_sub_Z_overlap_le_at
import Theorems.Thm_MIPStarRE_QPBT_CombinedPointsWitness_orderedZX_dist_le
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_isProbability
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_fst
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_left
import Theorems.Thm_MIPStarRE_QPBT_Distribution_prod_map_right
import Theorems.Thm_MIPStarRE_QPBT_Distribution_restrict_isProbability
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_sum_norm_place_completedPair_sub_sq
import Theorems.Thm_MIPStarRE_QPBT_avgOver_prod_restrictedLinePointDist_le
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_integrand_nonneg
import Theorems.Thm_MIPStarRE_QPBT_restrict_uniform_prod_fst
import Theorems.Thm_MIPStarRE_QPBT_restrictedALineDist_eq_map_prod
import Theorems.Thm_MIPStarRE_QPBT_restrictedDLineDist_eq_map_prod
import Theorems.Thm_MIPStarRE_QPBT_uniformDistribution_prod

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Combining/Defs.lean. -/
/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

























































/-- Every restricted axis-line law has total mass one. -/
theorem restrictedALineDist_isProbability (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    (_root_.MIPStarRE.QPBT.restrictedALineDist L i).IsProbability := by
  unfold _root_.MIPStarRE.QPBT.restrictedALineDist _root_.MIPStarRE.QPBT.restrictedALinePreDist
  exact (_root_.MIPStarRE.QPBT.Distribution.restrict_isProbability
    (_root_.MIPStarRE.QPBT.clDistribution (_root_.MIPStarRE.QPBT.ldALineCL L) (_root_.MIPStarRE.QPBT.ldPointCL L))
    (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i) (_root_.MIPStarRE.QPBT.restrictedALineSeedEvent_positive L i)).map _

/-- Every restricted diagonal-line law has total mass one. -/
theorem restrictedDLineDist_isProbability (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    (_root_.MIPStarRE.QPBT.restrictedDLineDist L i).IsProbability := by
  unfold _root_.MIPStarRE.QPBT.restrictedDLineDist _root_.MIPStarRE.QPBT.restrictedDLinePreDist
  exact (_root_.MIPStarRE.QPBT.Distribution.restrict_isProbability
    (_root_.MIPStarRE.QPBT.clDistribution (_root_.MIPStarRE.QPBT.ldDLineCL L) (_root_.MIPStarRE.QPBT.ldPointCL L))
    (_root_.MIPStarRE.QPBT.restrictedLineSeedEvent L i) (_root_.MIPStarRE.QPBT.restrictedDLineSeedEvent_positive L i)).map _

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineConstruct.lean. -/
/-!
# The sampling procedure of the sub-line lemma

This module carries out the sampling procedure of `lem:qld-sublines`.  A line
kind is drawn from the two kinds, an extended coordinate and an extended point
and direction are drawn uniformly, and two scalar seeds are drawn
independently in the coordinate-index fibers of the two coordinates that the
two source lines must carry.  The sampled triple consists of the axis or
diagonal line of the extended sample together with the two source lines
decoded from the two coordinate blocks of the extended point and direction and
from the two seeds.

The module records the elementary evaluations of that triple, the description
of the support of the resulting law, the three pointwise properties of a
sampled triple -- incidence of the two source blocks, compatibility of the
affine data, and closure of the axis branch -- and the identification of its
extended-line marginal.

## References

The construction is the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The auxiliary randomness of one branch -/







/-- Every seed law of a source line has total mass one. -/
theorem subLineSeedDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (i : Fin P.m) :
    (_root_.MIPStarRE.QPBT.subLineSeedDist P i).IsProbability := by
  rw [_root_.MIPStarRE.QPBT.subLineSeedDist]
  exact _root_.MIPStarRE.QPBT.Distribution.restrict_isProbability _ _
    (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive P.toLdParams i)





/-! ## The sampled triple -/













/-! ## Elementary evaluations of the sampled triple -/













/-! ## The support of the sub-line law -/



/-! ## Pointwise properties of a sampled triple -/



















/-! ## Total mass and extended marginal -/









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSeed.lean. -/
/-!
# The two independent blocks of a fresh diagonal direction pair

This module splits the fresh diagonal direction pair of the sub-line sampling
procedure into its two independent blocks.  The coordinate-index event
constrains only the scalar seed of the pair, so conditioning on it leaves the
direction block uniform and independent of the conditioned seed.  The
direction block of a fresh pair is therefore available as an unconstrained
uniform vector, which is what allows the sampling procedure to read it off the
corresponding block of the direction of the sampled extended line.

## References

The block decomposition supports `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The coordinate-index event is that of `def:ith-restricted-line`, blueprint
lines 1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The coordinate-index event on a scalar seed -/







/-! ## The blocks of a fresh diagonal direction pair -/

/-- A fresh diagonal direction pair at coordinate index `i` is a scalar seed
conditioned on the coordinate-index fiber of `i` together with an independent
uniform direction block.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem freshDiagonalPairDist_eq_prod (L : _root_.MIPStarRE.QPBT.LdParams) (i : Fin L.m) :
    _root_.MIPStarRE.QPBT.freshDiagonalPairDist L i =
      _root_.MIPStarRE.QPBT.Distribution.prod
        (_root_.MIPStarRE.QPBT.Distribution.restrict (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L))
          (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i) (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive L i))
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)) := by
  classical
  unfold _root_.MIPStarRE.QPBT.freshDiagonalPairDist
  exact _root_.MIPStarRE.QPBT.restrict_uniform_prod_fst (_root_.MIPStarRE.QPBT.ldSeedIndexEvent L i)
    (_root_.MIPStarRE.QPBT.ldSeedIndexEvent_positive L i) (_root_.MIPStarRE.QPBT.ldSeedDirEvent_positive L i)



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/LinePointOverlap.lean. -/
/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}





















/-! ## Effects of the completed measurement families -/





/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (b : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExpOption
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)







/-! ## Factorization of opposite placements with distinct Pauli factors -/













end ProjectiveSetting

/-! ## The overlap identity -/







end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineSource.lean. -/
/-!
# The projected marginals of the sub-line law

This module identifies the two projected point marginals of the sub-line law
of `lem:qld-sublines` as mixtures of the restricted product laws.  The two
source lines of a sampled triple depend on the drawn extended point only
through the canonical representatives of its two source blocks, and those
representatives are unchanged when the drawn point is replaced by any point of
the extended line; a uniform point of the extended line through a uniform
point is a uniform point, so the drawn point may be replaced throughout by the
point that is finally retained.  The six generating blocks of the resulting
law -- the two source point blocks, the two scalar seeds and the two source
direction blocks -- are then regrouped into the two restricted product laws
carried by the two indices of the branch.

## References

The identification is the last step of the proof of `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The restricted laws are `def:ith-restricted-line`, blueprint lines
1209--1228, paper lines 1038--1048.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## Source lines depend on the point block only through its representative -/







/-! ## Generating form of the restricted product components -/

/-- The restricted line-point law of a kind at an index is the law of the
source line of that kind decoded from a uniform point block, a scalar seed in
the coordinate-index fiber of the index and a uniform direction block,
together with that same point block.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrictedLinePointDist_eq_map_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i : Fin P.m) :
    _root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i =
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.subLineSeedDist P i)
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))).map
        (fun w => (_root_.MIPStarRE.QPBT.subLineSourceLine P kind w.1 w.2.1 w.2.2, w.1)) := by
  cases kind
  · show _root_.MIPStarRE.QPBT.restrictedALineDist P.toLdParams i = _
    rw [_root_.MIPStarRE.QPBT.restrictedALineDist_eq_map_prod, _root_.MIPStarRE.QPBT.freshDiagonalPairDist_eq_prod]
    rfl
  · show _root_.MIPStarRE.QPBT.restrictedDLineDist P.toLdParams i = _
    rw [_root_.MIPStarRE.QPBT.restrictedDLineDist_eq_map_prod, _root_.MIPStarRE.QPBT.freshDiagonalPairDist_eq_prod]
    rfl





/-! ## The joint projected marginal of one branch at one extended coordinate -/



/-! ## The two one-point projected marginals of one branch -/





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/ZEvalDeficit.lean. -/
/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Completed point pairs -/









namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}







/-- The completed `Z`-then-`X` point product vanishes on both `none` classes
and restricts to the ordered product on evaluated pairs. -/
theorem completedPair_norm_sq_sum_ZX (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) {δ : ℝ}
    (points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δ) (p : _root_.MIPStarRE.QPBT.Placement)
    (x z : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place p (((points.Q p.side x z).postprocess (fun ab =>
              (some ab.1, some ab.2))).effect o) -
            S.place p
              ((S.pointMeasExpOption p.side .Z z).effect o.2 *
                (S.pointMeasExpOption p.side .X x).effect o.1))
          S.psiHat‖ ^ 2) =
      ∑ ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P,
        ‖_root_.MIPStarRE.QPBT.applyOperatorToState
          (S.place p ((points.Q p.side x z).effect ab) -
            S.place p
              ((S.pointMeasExp p.side .Z z).effect ab.2 *
                (S.pointMeasExp p.side .X x).effect ab.1))
          S.psiHat‖ ^ 2 := by
  refine S.sum_norm_place_completedPair_sub_sq p (points.Q p.side x z) _ _ ?_ ?_ ?_
  · intro ab
    rw [S.pointMeasExpOption_effect_some, S.pointMeasExpOption_effect_some]
  · intro o2
    rw [S.pointMeasExpOption_effect_none, mul_zero]
  · intro o1
    rw [S.pointMeasExpOption_effect_none, zero_mul]


end ProjectiveSetting

/-! ## The abstract one-point deficit -/



/-! ## The two placed deficits -/





/-! ## The two deficits over a product of restricted line-point laws -/

/-- Every restricted line-point law has total mass one. -/
theorem restrictedLinePointDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kind : _root_.MIPStarRE.QPBT.LineKind) (i : Fin P.m) :
    (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i).IsProbability := by
  cases kind
  · change (_root_.MIPStarRE.QPBT.restrictedALineDist P.toLdParams i).IsProbability
    exact _root_.MIPStarRE.QPBT.restrictedALineDist_isProbability P.toLdParams i
  · change (_root_.MIPStarRE.QPBT.restrictedDLineDist P.toLdParams i).IsProbability
    exact _root_.MIPStarRE.QPBT.restrictedDLineDist_isProbability P.toLdParams i

/-- The point marginal of a restricted line-point law is uniform. -/
theorem restrictedLinePointDist_map_snd (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kind : _root_.MIPStarRE.QPBT.LineKind)
    (i : Fin P.m) :
    (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kind i).map Prod.snd =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) := by
  rw [_root_.MIPStarRE.QPBT.restrictedLinePointDist_eq_map_prod, _root_.MIPStarRE.QPBT.Distribution.map_map]
  exact _root_.MIPStarRE.QPBT.Distribution.prod_map_fst _ _ (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _
    (_root_.MIPStarRE.QPBT.subLineSeedDist_isProbability P i) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _))

/-- The pair of points of a product of two restricted line-point laws is a
uniform pair. -/
theorem prod_restrictedLinePointDist_map_points (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (kindX kindZ : _root_.MIPStarRE.QPBT.LineKind) (i j : Fin P.m) :
    (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j)).map (fun s => (s.1.2, s.2.2)) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
  have h : _root_.MIPStarRE.QPBT.Distribution.prod ((_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i).map Prod.snd)
      ((_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j).map Prod.snd) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution
        ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) := by
    rw [_root_.MIPStarRE.QPBT.restrictedLinePointDist_map_snd, _root_.MIPStarRE.QPBT.restrictedLinePointDist_map_snd,
      _root_.MIPStarRE.QPBT.uniformDistribution_prod]
  rw [← h, _root_.MIPStarRE.QPBT.Distribution.prod_map_left, _root_.MIPStarRE.QPBT.Distribution.prod_map_right,
    _root_.MIPStarRE.QPBT.Distribution.map_map]

/-- A state-dependent distance between two families depending on the pair of
points only, averaged over a product of two restricted line-point laws, is the
distance averaged over a uniform pair of points. -/
theorem opFamilyDistSq_prod_restricted_points {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (kindX kindZ : _root_.MIPStarRE.QPBT.LineKind)
    (i j : Fin P.m)
    (F G : (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq
        (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
          (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j))
        (fun s a => F (s.1.2, s.2.2) a) (fun s a => G (s.1.2, s.2.2) a) ψ =
      _root_.MIPStarRE.QPBT.opFamilyDistSq
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
          ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))) F G ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  rw [← _root_.MIPStarRE.QPBT.prod_restrictedLinePointDist_map_points P kindX kindZ i j,
    _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map]



end

end MIPStarRE.QPBT

/-!
# Z-point deficits of the evaluated pair-line measurement

This module bounds the deficit of the overlap between the evaluated paired-line
measurement and the expanded Z-point measurement. The proof inserts the completed
joint point measurement, replaces it by the X-then-Z ordered product, and sums
the X effects. It uses evaluated consistency and the distance from the joint
point measurement to that ordered product. The bound holds first over any
probability law on pairs of line-point pairs and then over a product of restricted
line-point laws, whose point marginal is the uniform pair.

The estimates hold for arbitrary opposite placements, with first-player
specializations; register commutation requires no symmetry of the state.
The completed-outcome and real-overlap lemmas are also available for other
calculations. The concrete X-deficit argument is separate, in
`MIPStarRE.QPBT.Combining.Lines.ConcreteXDeficit`.

## References

The Z deficit supports blueprint `lem:claim-17-3-re-direct`, alongside the
source `lem:claim-17-3`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1204-1239`; the
consistency input is `lem:qld-xz-lines` and the ordered products are those of
`lem:qld-4-10`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



/-! ## Completed point pairs -/









open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}












/-! ## The abstract one-point deficit -/



/-! ## The two placed deficits -/





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}








/-! ## The two deficits over a product of restricted line-point laws -/











variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε δQ δP : ℝ} {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε}
  {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness S δQ}

theorem solution
    (lines : _root_.MIPStarRE.QPBT.CombinedLinesWitness S points δP)
    (first second : _root_.MIPStarRE.QPBT.Placement) (hopposite : first.IsOpposite second) (kindX kindZ : _root_.MIPStarRE.QPBT.LineKind)
    (i j : Fin P.m) :
    1 - _root_.LIDT.MIPStarRE.LDT.avgOver
      (_root_.MIPStarRE.QPBT.Distribution.prod (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindX i)
        (_root_.MIPStarRE.QPBT.restrictedLinePointDist P kindZ j))
      (fun s => ∑ o : Option (_root_.MIPStarRE.QPBT.PauliScalar P) × Option (_root_.MIPStarRE.QPBT.PauliScalar P),
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
          (S.place first
            (((lines.T first.side s.1.1 s.2.1).postprocess fun fs =>
              (_root_.MIPStarRE.QPBT.evalOpt s.1.1 s.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt s.2.1 s.2.2 fs.2)).effect o) *
            S.place second ((S.pointMeasExpOption second.side .Z s.2.2).effect o.2))) ≤
      2 * Real.sqrt (4 * (P.m : ℝ) ^ 2 * δP) + 2 * Real.sqrt (4 * δQ) := by
  refine lines.one_sub_Z_overlap_le_at first second hopposite _
    (_root_.MIPStarRE.QPBT.Distribution.prod_isProbability _ _
      (_root_.MIPStarRE.QPBT.restrictedLinePointDist_isProbability P kindX i)
      (_root_.MIPStarRE.QPBT.restrictedLinePointDist_isProbability P kindZ j)) _ _ ?_ ?_
  · unfold _root_.MIPStarRE.QPBT.consistencyDefect at ⊢
    refine le_trans
      (_root_.MIPStarRE.QPBT.avgOver_prod_restrictedLinePointDist_le _ ?_ kindX kindZ i j) ?_
    · intro sample
      exact _root_.MIPStarRE.QPBT.consistencyDefect_integrand_nonneg S first second hopposite
        ((lines.T first.side sample.1.1 sample.2.1).postprocess fun fs =>
          (_root_.MIPStarRE.QPBT.evalOpt sample.1.1 sample.1.2 fs.1, _root_.MIPStarRE.QPBT.evalOpt sample.2.1 sample.2.2 fs.2))
        ((points.Q second.side sample.1.2 sample.2.2).postprocess fun ab =>
          (some ab.1, some ab.2))
    · exact mul_le_mul_of_nonneg_left (lines.consistent first second hopposite) (by positivity)
  · calc
      _ = _root_.MIPStarRE.QPBT.opFamilyDistSq
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
            (fun xz o => S.place second
              (((points.Q second.side xz.1 xz.2).postprocess fun ab =>
                (some ab.1, some ab.2)).effect o))
            (fun xz o => S.place second
              ((S.pointMeasExpOption second.side .Z xz.2).effect o.2 *
                (S.pointMeasExpOption second.side .X xz.1).effect o.1))
            S.psiHat :=
        _root_.MIPStarRE.QPBT.opFamilyDistSq_prod_restricted_points P kindX kindZ i j _ _ _
      _ = _root_.MIPStarRE.QPBT.opFamilyDistSq
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
              ((Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) × (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)))
            (fun xz ab => S.place second ((points.Q second.side xz.1 xz.2).effect ab))
            (fun xz ab => S.place second
              ((S.pointMeasExp second.side .Z xz.2).effect ab.2 *
                (S.pointMeasExp second.side .X xz.1).effect ab.1))
            S.psiHat := by
        unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
        exact _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun xz =>
          S.completedPair_norm_sq_sum_ZX points second xz.1 xz.2
      _ ≤ 4 * δQ := points.orderedZX_dist_le second
