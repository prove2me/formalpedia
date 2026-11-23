-- Prove2me | solution 1 for GlobalTheory.AnArc.IsConvLine.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:37.365547+00:00
-- url     : https://prove2.me/submissions/2f136ee2-8851-402d-ae65-1c6e019a9ae7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

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
variable {A}
namespace GlobalTheory.AnArc
namespace IsConvLine
theorem _root_.solution {T₀ T₁ : ℝ} (h : A.IsConvLine T₀) (hT : T₀ ≤ T₁) : A.IsConvLine T₁ := fun μ =>
  (h μ).trans (mul_le_mul_of_nonneg_right hT (by exact_mod_cast A.be_self_nonneg μ))
end IsConvLine
end GlobalTheory.AnArc
