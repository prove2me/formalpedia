-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_isConvLine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:50.2225+00:00
-- url     : https://prove2.me/submissions/3fe195e8-abca-4c09-aaa5-12fc209ec3d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_size_nonneg
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_le_mul_size
import Theorems.Thm_GlobalTheory_AnArc_norm_apply_le_size
import Theorems.Thm_GlobalTheory_AnArc_exists_size_sq_le
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_H_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution : ∃ T₀, A.IsConvLine T₀ := by
  obtain ⟨C, hC, h⟩ := A.exists_size_sq_le
  obtain ⟨CH, hCH, hH⟩ := A.exists_norm_H_le
  obtain ⟨Cc, hCc, hc⟩ := A.exists_norm_le_mul_size A.ct
  obtain ⟨CT, hCT, hT⟩ := A.exists_norm_le_mul_size A.T
  refine ⟨(CH * Cc ^ 2 / 2 + CT) * C, fun μ => ?_⟩
  have hs := A.size_nonneg μ
  have h1 : (A.H (A.ct μ) (A.ct μ)).re ≤ CH * Cc ^ 2 * A.size μ ^ 2 :=
    calc _ ≤ CH * ‖A.ct μ‖ * ‖A.ct μ‖ := (Complex.re_le_norm _).trans (hH _ _)
      _ ≤ CH * (Cc * A.size μ) * (Cc * A.size μ) := by gcongr <;> exact hc μ
      _ = _ := by ring
  have h2 : -(A.T μ μ).im ≤ CT * A.size μ ^ 2 :=
    calc _ ≤ ‖A.T μ‖ * A.size μ :=
          (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (A.norm_apply_le_size _ μ))
      _ ≤ CT * A.size μ * A.size μ := by gcongr; exact hT μ
      _ = _ := by ring
  have h3 : (CH * Cc ^ 2 / 2 + CT) * A.size μ ^ 2 ≤ (CH * Cc ^ 2 / 2 + CT) * (C * A.be μ μ) :=
    mul_le_mul_of_nonneg_left (h μ) (by positivity)
  linarith
end GlobalTheory.AnArc
