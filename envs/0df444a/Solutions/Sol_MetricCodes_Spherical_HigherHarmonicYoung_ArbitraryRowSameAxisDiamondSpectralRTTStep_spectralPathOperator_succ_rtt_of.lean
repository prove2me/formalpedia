-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep.spectralPathOperator_succ_rtt_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/2ccb6b62-478b-4bff-91d5-2bbec075977c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_spectralPathOperator_succ
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_polarization_comp_spectralPathOperator_later_target_commute
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralRootTransport_polarization_comp_spectralPathOperator_self_sub
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralAbstractRTT_spectralStep_rtt

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (s t : Fin (r + 1))
    (hs : a.succ ≤ s) (ht : a.succ ≤ t)
    (k : Fin n) (u v : ℝ)
    (hself : ∀ w z : ℝ,
      (spectralPathOperator lam a.castSucc a.castSucc k w).comp
          (spectralPathOperator lam a.castSucc a.castSucc k z) =
        (spectralPathOperator lam a.castSucc a.castSucc k z).comp
          (spectralPathOperator lam a.castSucc a.castSucc k w))
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
    (u - v) •
        ((spectralPathOperator lam a.succ s k u).comp
            (spectralPathOperator lam a.succ t k v) -
          (spectralPathOperator lam a.succ t k v).comp
            (spectralPathOperator lam a.succ s k u)) =
      (spectralPathOperator lam a.succ t k u).comp
          (spectralPathOperator lam a.succ s k v) -
        (spectralPathOperator lam a.succ t k v).comp
          (spectralPathOperator lam a.succ s k u) := by
  let g : ℝ := shiftedRowGap lam a.succ a.castSucc
  let x : ℝ := g + u
  let y : ℝ := g + v
  let w : ℝ := u + g + 1
  let z : ℝ := v + g + 1
  let A := spectralPathOperator lam a.castSucc a.castSucc k w
  let B := spectralPathOperator lam a.castSucc a.castSucc k z
  let C := spectralPathOperator lam a.castSucc s k w
  let D := spectralPathOperator lam a.castSucc s k z
  let E := spectralPathOperator lam a.castSucc t k w
  let F := spectralPathOperator lam a.castSucc t k z
  let S := polarization r n s a.castSucc
  let T := polarization r n t a.castSucc
  have has : a.castSucc < s := Fin.castSucc_lt_iff_succ_le.mpr hs
  have hat : a.castSucc < t := Fin.castSucc_lt_iff_succ_le.mpr ht
  have hdelta : x - y = w - z := by
    dsimp [x, y, w, z]
    ring
  have hdelta' : x - y = u - v := by
    dsimp [x, y]
    ring
  have hAB : A * B = B * A := hself w z
  have hSB : S * B - B * S = D :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc s has k z
  have hTA : T * A - A * T = E :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc t hat k w
  have hTB : T * B - B * T = F :=
    polarization_comp_spectralPathOperator_self_sub
      lam a.castSucc t hat k z
  have hSF : S * F = F * S :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc s t has hat k z
  have hTC : T * C = C * T :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc t s hat has k w
  have hTD : T * D = D * T :=
    polarization_comp_spectralPathOperator_later_target_commute
      lam a.castSucc t s hat has k z
  have hST : S * T = T * S := by
    apply LinearMap.ext
    intro p
    change polarization r n s a.castSucc
        (polarization r n t a.castSucc p) =
      polarization r n t a.castSucc
        (polarization r n s a.castSucc p)
    rw [polarization_polarization_commutator]
    simp [ne_of_lt hat, ne_of_lt has]
  have hcross : (x - y) • (C * F - F * C) = E * D - F * C := by
    rw [hdelta]
    exact hrtt s t has.le hat.le w z
  have hCB : (x - y) • (C * B - B * C) = A * D - B * C := by
    rw [hdelta]
    exact hrtt s a.castSucc has.le le_rfl w z
  have hAF : (x - y) • (A * F - F * A) = E * B - F * A := by
    rw [hdelta]
    exact hrtt a.castSucc t le_rfl hat.le w z
  have hEB : (x - y) • (E * B - B * E) = A * F - B * E := by
    rw [hdelta]
    exact hrtt t a.castSucc hat.le le_rfl w z
  have hstep := spectralStep_rtt A B C D E F S T x y
    hAB hSB hTA hTB hSF hTC hTD hST hcross hCB hAF hEB
  rw [hdelta'] at hstep
  rw [spectralPathOperator_succ lam hdom a s k u,
    spectralPathOperator_succ lam hdom a t k v,
    spectralPathOperator_succ lam hdom a t k u,
    spectralPathOperator_succ lam hdom a s k v]
  change
    (u - v) •
        ((x • C - A.comp S).comp (y • F - B.comp T) -
          (y • F - B.comp T).comp (x • C - A.comp S)) =
      (x • E - A.comp T).comp (y • D - B.comp S) -
        (y • F - B.comp T).comp (x • C - A.comp S)
  exact hstep
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRTTStep
