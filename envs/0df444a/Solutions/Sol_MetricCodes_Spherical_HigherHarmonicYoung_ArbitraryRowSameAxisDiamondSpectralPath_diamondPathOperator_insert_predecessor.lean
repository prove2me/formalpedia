-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath.diamondPathOperator_insert_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/f44befc3-cb97-4980-8a3d-46612a1ef14a

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonLastRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
theorem _root_.solution {r n : ℕ}
    (a : Fin r) (target : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    diamondPathOperator target k (insert a.castSucc S) =
      (diamondPathOperator a.castSucc k S).comp
        (polarization r n target a.castSucc) := by
  classical
  have hstart :
      polarizationPathStart target (insert a.castSucc S) =
        polarizationPathStart a.castSucc S := by
    by_cases hnon : S.Nonempty
    · rw [polarizationPathStart,
        dif_pos (S.insert_nonempty a.castSucc),
        polarizationPathStart, dif_pos hnon,
        Finset.min'_insert a.castSucc S hnon]
      apply min_eq_right
      exact le_of_lt ((mem_precedingRows (S.min' hnon) a.castSucc).mp
        (hS (Finset.min'_mem S hnon)))
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
      simp [hempty, polarizationPathStart]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, diamondPathOperator_apply]
  rw [sort_insert_last_of_preceding a S hS, hstart]
  simp only [List.append_assoc, List.singleton_append]
  rw [lowerPolarizationPath_append_cons_apply
    (S.sort (· ≤ ·)) a.castSucc [target] p]
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
