-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange.iteratedArbitraryRowAxialRaise_move_last_of_rowDiamond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/6bd126aa-6b04-43ed-8d3e-2f600d40f0b6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamond_raiseWeight_raiseWeight_comm

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankReverseInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamond
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankAdjacentInterlacingSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (rows : List (Fin (r + 1))) (row : Fin (r + 1))
    (hdiamond : DominantSameAxisRowDiamond n row)
    (hrows : ∀ i ∈ rows, i < row)
    (hdom : ∀ (front : List (Fin (r + 1))),
      (∀ i, front.count i ≤ rows.count i) →
        Antitone (arbitraryRowPathWeight lam front))
    (k : Fin n) (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise (arbitraryRowPathWeight lam rows) row k
        (iteratedArbitraryRowAxialRaise lam k rows p) =
      iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
        (arbitraryRowAxialRaise lam row k p) := by
  classical
  induction rows generalizing lam p with
  | nil => rfl
  | cons i rest ih =>
      have hi : i < row := hrows i (by simp)
      have hrest : ∀ j ∈ rest, j < row := by
        intro j hj
        exact hrows j (by simp [hj])
      have hdom0 : Antitone lam := by
        simpa [arbitraryRowPathWeight] using
          hdom [] (by simp)
      have hdomrest : ∀ (front : List (Fin (r + 1))),
          (∀ j, front.count j ≤ rest.count j) →
            Antitone
              (arbitraryRowPathWeight (raiseWeight lam i) front) := by
        intro front hfront
        have hfull : ∀ j,
            (i :: front).count j ≤ (i :: rest).count j := by
          intro j
          by_cases hij : i = j
          · subst j
            simpa using Nat.add_le_add_left (hfront i) 1
          · simp [hij, hfront j]
        simpa [arbitraryRowPathWeight] using hdom (i :: front) hfull
      change
        arbitraryRowAxialRaise
            (arbitraryRowPathWeight (raiseWeight lam i) rest) row k
          (iteratedArbitraryRowAxialRaise (raiseWeight lam i) k rest
            (arbitraryRowAxialRaise lam i k p)) =
        iteratedArbitraryRowAxialRaise
          (raiseWeight (raiseWeight lam row) i) k rest
          (arbitraryRowAxialRaise (raiseWeight lam row) i k
            (arbitraryRowAxialRaise lam row k p))
      rw [ih (lam := raiseWeight lam i)
        (p := arbitraryRowAxialRaise lam i k p) hrest hdomrest]
      rw [hdiamond lam hdom0 i hi k p]
      rw [raiseWeight_raiseWeight_comm lam i row (ne_of_lt hi)]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingAdjacentPathExchange
