-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT.spectralPathOperator_rtt_and_same_target_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/12144a2d-6592-4dd5-8c14-3e12d8b496ae

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRTTStep_spectralPathOperator_succ_rtt_of
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep_spectralPathOperator_succ_same_target_commute_of
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRTT_spectralPathOperator_zero_pivot_rtt
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRTT_spectralPathOperator_zero_pivot_same_target_commute

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
set_option maxHeartbeats 4000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (pivot : Fin (r + 1)) :
    (∀ (s t : Fin (r + 1)), pivot ≤ s → pivot ≤ t →
      ∀ (k : Fin n) (u v : ℝ),
        (u - v) •
            ((spectralPathOperator lam pivot s k u).comp
                (spectralPathOperator lam pivot t k v) -
              (spectralPathOperator lam pivot t k v).comp
                (spectralPathOperator lam pivot s k u)) =
          (spectralPathOperator lam pivot t k u).comp
              (spectralPathOperator lam pivot s k v) -
            (spectralPathOperator lam pivot t k v).comp
              (spectralPathOperator lam pivot s k u)) ∧
    (∀ (target : Fin (r + 1)), pivot ≤ target →
      ∀ (k : Fin n) (u v : ℝ),
        (spectralPathOperator lam pivot target k u).comp
            (spectralPathOperator lam pivot target k v) =
          (spectralPathOperator lam pivot target k v).comp
            (spectralPathOperator lam pivot target k u)) := by
  induction pivot using Fin.induction with
  | zero =>
      constructor
      · intro s t _ _ k u v
        exact spectralPathOperator_zero_pivot_rtt lam s t k u v
      · intro target _ k u v
        exact spectralPathOperator_zero_pivot_same_target_commute
          lam target k u v
  | succ a ih =>
      rcases ih with ⟨ihrtt, ihcomm⟩
      constructor
      · intro s t hs ht k u v
        exact spectralPathOperator_succ_rtt_of lam hdom a s t hs ht k u v
          (fun w z => ihcomm a.castSucc le_rfl k w z)
          (fun i j hi hj w z => ihrtt i j hi hj k w z)
      · intro target ht k u v
        exact spectralPathOperator_succ_same_target_commute_of
          lam hdom a target ht k u v
          (fun i hi w z => ihcomm i hi k w z)
          (fun i j hi hj w z => ihrtt i j hi hj k w z)
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTT
