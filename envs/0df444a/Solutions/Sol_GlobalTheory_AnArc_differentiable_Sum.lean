-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiable_Sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:41.360839+00:00
-- url     : https://prove2.me/submissions/70ec0aa4-a066-4c9a-a926-85ae69cef984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_isOpen_above
import Theorems.Thm_GlobalTheory_AnArc_differentiableOn_Sum

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
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) :
    Differentiable ℂ (A.Sum j α th w) := fun v =>
  ((differentiableOn_Sum hT hj h).differentiableAt ((isOpen_above T₀).mem_nhds (x := (w, v)) hw)).comp v
    (f := fun v => (w, v)) (by fun_prop)
end GlobalTheory.AnArc
