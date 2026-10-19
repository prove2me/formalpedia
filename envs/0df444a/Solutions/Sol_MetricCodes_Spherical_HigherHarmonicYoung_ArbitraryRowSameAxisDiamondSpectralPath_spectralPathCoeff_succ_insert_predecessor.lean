-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath.spectralPathCoeff_succ_insert_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/b44c6815-2948-4670-9980-4ac7e2ce8dc2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralPath_shiftedRowGap_succ_eq_add_predecessor

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
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (a : Fin r) (t : ℝ) (S : Finset (Fin (r + 1)))
    (hS : S ⊆ precedingRows a.castSucc) :
    spectralPathCoeff lam a.succ t (insert a.castSucc S) =
      -spectralPathCoeff lam a.castSucc
        (t + shiftedRowGap lam a.succ a.castSucc + 1) S := by
  classical
  have hnot : a.castSucc ∉ S := by
    intro ha
    exact (lt_irrefl a.castSucc)
      ((mem_precedingRows a.castSucc a.castSucc).mp (hS ha))
  have hdiff :
      precedingRows a.succ \ insert a.castSucc S =
        precedingRows a.castSucc \ S := by
    rw [precedingRows_succ a]
    ext b
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨hb | hb, hnotb⟩
      · exact False.elim (hnotb (Or.inl hb))
      · exact ⟨hb, fun h => hnotb (Or.inr h)⟩
    · rintro ⟨hb, hbS⟩
      exact ⟨Or.inr hb, by
        rintro (rfl | hb')
        · exact (lt_irrefl a.castSucc)
            ((mem_precedingRows a.castSucc a.castSucc).mp hb)
        · exact hbS hb'⟩
  have hprod :
      (∏ b ∈ precedingRows a.castSucc \ S,
        (shiftedRowGap lam a.succ b + t)) =
      ∏ b ∈ precedingRows a.castSucc \ S,
        (shiftedRowGap lam a.castSucc b +
          (t + shiftedRowGap lam a.succ a.castSucc + 1)) := by
    apply Finset.prod_congr rfl
    intro b hb
    rw [shiftedRowGap_succ_eq_add_predecessor
      lam hdom a b
        ((mem_precedingRows b a.castSucc).mp
          (Finset.mem_sdiff.mp hb).1)]
    ring
  unfold spectralPathCoeff
  rw [Finset.card_insert_of_notMem hnot, hdiff, hprod, pow_succ]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
