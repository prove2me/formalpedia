-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiableOn_Sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:03.64122+00:00
-- url     : https://prove2.me/submissions/d7848495-912e-4c60-b062-d0716f05c829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_hasSumLocallyUniformlyOn_term
import Theorems.Thm_GlobalTheory_AnArc_isOpen_above
import Theorems.Thm_GlobalTheory_AnArc_differentiable_term_mul
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_of_hasSumLocallyUniformlyOn


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
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) :
    DifferentiableOn ℂ (fun p : ℂ × A.V => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} :=
  SCV.differentiableOn_of_hasSumLocallyUniformlyOn (isOpen_above T₀) (hasSumLocallyUniformlyOn_term hT hj h)
    fun μ => (differentiable_term_mul h.1 μ).differentiableOn
end GlobalTheory.AnArc
