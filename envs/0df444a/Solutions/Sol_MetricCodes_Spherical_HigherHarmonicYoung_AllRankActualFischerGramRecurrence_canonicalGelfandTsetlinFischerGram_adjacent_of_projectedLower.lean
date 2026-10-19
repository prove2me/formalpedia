-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/5dce75fd-e210-4b82-8350-c09969e981ac

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalForwardAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowUnconditionalBranch
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 2))
    (hlow : Interlaces low mu)
    (hhigh : Interlaces (raiseWeight low row) mu)
    (hdom : Antitone low)
    (hlowGram : PositiveGelfandTsetlinFischerGram (n := n) low mu hlow)
    (hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight low row) mu hhigh)
    (hexchange : ∀ p : HarmonicYoungSpace (n := n) mu,
      arbitraryRowAxialRaise low row (Fin.last n)
          (reverseInterlacingPolynomialSeed low mu p) -
        reverseInterlacingPolynomialSeed (raiseWeight low row) mu p ∈
          youngGramRadialIdeal (r + 1) (n + 1))
    (hcartan : ∀ p : HarmonicYoungSpace (n := n) mu,
      projectedCoordinateLower low (raiseWeight low row)
          (sum_raiseWeight low row) row
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
          (arbitraryRowSameAxisHarmonicRaise low hdom row (Fin.last n)
            (reverseInterlacingHarmonicBranch low mu hlow p)) =
        (arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) •
          reverseInterlacingHarmonicBranch low mu hlow p)
    (p : HarmonicYoungSpace (n := n) mu) (hp : p ≠ 0) :
    canonicalGelfandTsetlinFischerGram
        (raiseWeight low row) mu hhigh hhighGram =
      arbitraryRowAxialLowerScalar low row ^ 2 *
        internalRowLowerGramScalar (raiseWeight low row) row *
        canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
        plusProbability (n + 1) low mu row := by
  have hraise := arbitraryRowSameAxisHarmonicRaise_reverseBranch_eq_of_pathExchange
    low mu row hlow hhigh hdom 1 (by simpa using hexchange) p
  simp only [one_smul] at hraise
  have hforward :=
    projectedCoordinateRaise_reverseInterlacingHarmonicBranch_eq_of_pathExchange
      low mu row hlow hhigh hdom 1 (by simpa using hexchange) p
  simp only [mul_one] at hforward
  have hlower := hcartan p
  rw [hraise] at hlower
  have hactual := projectedCoordinateRaise_inner
    (raiseWeight low row) low (sum_raiseWeight low row) row
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
  rw [hforward, hlower] at hactual
  have hleft := real_inner_smul_left
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
    (reverseInterlacingHarmonicBranch
      (raiseWeight low row) mu hhigh p)
    (arbitraryRowAxialLowerScalar low row)⁻¹
  have hright := real_inner_smul_right
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (reverseInterlacingHarmonicBranch low mu hlow p)
    (arbitraryRowAxialLowerScalar low row *
      internalRowLowerGramScalar (raiseWeight low row) row *
      plusProbability (n + 1) low mu row)
  have hpairHigh := canonicalGelfandTsetlinFischerGram_inner
    (raiseWeight low row) mu hhigh hhighGram p p
  have hpairLow := canonicalGelfandTsetlinFischerGram_inner
    low mu hlow hlowGram p p
  have hscalar :
      (arbitraryRowAxialLowerScalar low row)⁻¹ *
          (canonicalGelfandTsetlinFischerGram
            (raiseWeight low row) mu hhigh hhighGram * ⟪p, p⟫_ℝ) =
        (arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) *
          (canonicalGelfandTsetlinFischerGram low mu hlow hlowGram *
            ⟪p, p⟫_ℝ) := by
    calc
      _ = (arbitraryRowAxialLowerScalar low row)⁻¹ *
          ⟪reverseInterlacingHarmonicBranch
              (raiseWeight low row) mu hhigh p,
            reverseInterlacingHarmonicBranch
              (raiseWeight low row) mu hhigh p⟫_ℝ :=
        congrArg ((arbitraryRowAxialLowerScalar low row)⁻¹ * ·)
          hpairHigh.symm
      _ = (arbitraryRowAxialLowerScalar low row *
            internalRowLowerGramScalar (raiseWeight low row) row *
            plusProbability (n + 1) low mu row) *
          ⟪reverseInterlacingHarmonicBranch low mu hlow p,
            reverseInterlacingHarmonicBranch low mu hlow p⟫_ℝ :=
        hleft.symm.trans (hactual.trans hright)
      _ = _ := congrArg
        ((arbitraryRowAxialLowerScalar low row *
          internalRowLowerGramScalar (raiseWeight low row) row *
          plusProbability (n + 1) low mu row) * ·) hpairLow
  have hpositive : 0 < ⟪p, p⟫_ℝ := real_inner_self_pos.mpr hp
  have hgap : arbitraryRowAxialLowerScalar low row ≠ 0 :=
    (arbitraryRowAxialLowerScalar_pos low row).ne'
  field_simp [hgap] at hscalar
  simpa [mul_assoc, mul_left_comm, mul_comm] using hscalar
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankActualFischerGramRecurrence
