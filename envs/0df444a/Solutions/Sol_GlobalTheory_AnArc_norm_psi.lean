-- Prove2me | solution 1 for GlobalTheory.AnArc.norm_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:27:48.547829+00:00
-- url     : https://prove2.me/submissions/cc9167e1-3ee8-4edf-a045-124c6dc46e3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_norm_e
import Theorems.Thm_GlobalTheory_AnArc_psi_sq

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
theorem _root_.solution (μ : A.X) : ‖(A.psi μ : ℂ)‖ = Real.exp (-(Real.pi * (A.T μ μ).im)) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le, ← norm_pow, psi_sq, norm_e, sq, ← Real.exp_add]
  congr 1; ring
end GlobalTheory.AnArc
