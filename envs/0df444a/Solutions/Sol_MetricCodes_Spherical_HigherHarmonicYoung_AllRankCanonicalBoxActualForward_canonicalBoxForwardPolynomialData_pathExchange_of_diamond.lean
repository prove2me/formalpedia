-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward.canonicalBoxForwardPolynomialData_pathExchange_of_diamond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/5d8e540b-812e-4dae-b465-c39654c775fd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankInterlacingAdjacentPathExchange_reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 80000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentFibrePhase
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinAdjacentProjectedCoefficient
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSuffixClosure
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonHighest
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching
open SpherePacking.HarmonicCoordinateOperators
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
theorem _root_.solution
    {r m n : ℕ}
    (hdiamond : DominantSameAxisDiamond (r + 1) (n + 1))
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (p : HarmonicYoungSpace (n := n)
      (Weyl.flooredWeight b (n + 1))) :
    arbitraryRowAxialRaise (boxSignature (m := m) a (n + 1) low)
        row (Fin.last n)
        (reverseInterlacingPolynomialSeed
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1)) p) -
      reverseInterlacingPolynomialSeed
        (boxSignature (m := m) a (n + 1) high)
        (Weyl.flooredWeight b (n + 1)) p ∈
      youngGramRadialIdeal (r + 1) (n + 1) := by
  rw [hrow,
    reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
      hdiamond (boxSignature_interlaces a b hstable low) row p,
    sub_self]
  exact (youngGramRadialIdeal (r + 1) (n + 1)).zero_mem
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
