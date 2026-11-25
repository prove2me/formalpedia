-- Prove2me | solution 1 for GlobalTheory.AnArc.locally_normal_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:56:29.373025+00:00
-- url     : https://prove2.me/submissions/9cf7c157-c731-4405-a075-94f80cb78c82

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
    ∃ t ∈ 𝓝 v, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ v' ∈ t,
      ‖A.term j α th μ v' * eTwoPi (w * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨t, ht, u, hu, hb⟩ := locally_normal hT hj h (w, v) hw
  exact ⟨_, (Continuous.prodMk_right w).continuousAt ht, u, hu, fun μ v' hv' => hb μ (w, v') hv'⟩
end GlobalTheory.AnArc
