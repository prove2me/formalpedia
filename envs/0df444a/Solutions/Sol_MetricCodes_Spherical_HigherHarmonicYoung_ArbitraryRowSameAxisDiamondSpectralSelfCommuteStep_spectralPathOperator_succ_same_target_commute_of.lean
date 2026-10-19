-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep.spectralPathOperator_succ_same_target_commute_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/c8f64444-70b9-4398-b321-fd3632db8cef

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathOperator_succ
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_polarization_comp_spectralPathOperator_later_target_commute
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_polarization_comp_spectralPathOperator_self_sub
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute_spectralStep_same_target_commute

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (target : Fin (r + 1))
    (htarget : a.succ ≤ target)
    (k : Fin n) (u v : ℝ)
    (hcomm : ∀ (i : Fin (r + 1)), a.castSucc ≤ i → ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc i k w).comp
          (spectralPathOperator lam a.castSucc i k z) =
        (spectralPathOperator lam a.castSucc i k z).comp
          (spectralPathOperator lam a.castSucc i k w))
    (hrtt : ∀ (i j : Fin (r + 1)),
      a.castSucc ≤ i → a.castSucc ≤ j → ∀ w z : ℝ,
        (w - z) •
            ((spectralPathOperator lam a.castSucc i k w).comp
                (spectralPathOperator lam a.castSucc j k z) -
              (spectralPathOperator lam a.castSucc j k z).comp
                (spectralPathOperator lam a.castSucc i k w)) =
          (spectralPathOperator lam a.castSucc j k w).comp
              (spectralPathOperator lam a.castSucc i k z) -
            (spectralPathOperator lam a.castSucc j k z).comp
              (spectralPathOperator lam a.castSucc i k w)) :
    (spectralPathOperator lam a.succ target k u).comp
        (spectralPathOperator lam a.succ target k v) =
      (spectralPathOperator lam a.succ target k v).comp
        (spectralPathOperator lam a.succ target k u) := by
  let g : ℝ := shiftedRowGap lam a.succ a.castSucc
  let x : ℝ := g + u
  let y : ℝ := g + v
  let w : ℝ := u + g + 1
  let z : ℝ := v + g + 1
  let A := spectralPathOperator lam a.castSucc a.castSucc k w
  let B := spectralPathOperator lam a.castSucc a.castSucc k z
  let C := spectralPathOperator lam a.castSucc target k w
  let D := spectralPathOperator lam a.castSucc target k z
  let R := polarization r n target a.castSucc
  have hpos : a.castSucc < target :=
    Fin.castSucc_lt_iff_succ_le.mpr htarget
  have hdelta : x - y = w - z := by
    dsimp [x, y, w, z]
    ring
  have hAB : A * B = B * A := hcomm a.castSucc le_rfl w z
  have hCD : C * D = D * C := hcomm target hpos.le w z
  have hRA : R * A - A * R = C :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc target hpos k w
  have hRB : R * B - B * R = D :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc target hpos k z
  have hRC : R * C = C * R :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc target target hpos hpos k w
  have hRD : R * D = D * R :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc target target hpos hpos k z
  have hcross : (x - y) • (C * B - B * C) = A * D - B * C := by
    rw [hdelta]
    exact hrtt target a.castSucc hpos.le le_rfl w z
  have hstep := spectralStep_same_target_commute A B C D R x y
    hAB hCD hRA hRB hRC hRD hcross
  rw [spectralPathOperator_succ lam hdom a target k u,
    spectralPathOperator_succ lam hdom a target k v]
  change
    (x • C - A.comp R).comp (y • D - B.comp R) =
      (y • D - B.comp R).comp (x • C - A.comp R)
  exact hstep
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralSelfCommuteStep
