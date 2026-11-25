-- Prove2me | solution 1 for GlobalTheory.AnArc.summable_norm_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:14.791043+00:00
-- url     : https://prove2.me/submissions/3ab3fcf6-7a6b-4719-8753-fe857de0b176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_locally_normal

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
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    Summable fun μ => ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ := by
  obtain ⟨t, ht, u, hu, hb⟩ := locally_normal hT hj h (w, v) hw
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun μ => hb μ (w, v) (mem_of_mem_nhds ht)) hu
end GlobalTheory.AnArc
