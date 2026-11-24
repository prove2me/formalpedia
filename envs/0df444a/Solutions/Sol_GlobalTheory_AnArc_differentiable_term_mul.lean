-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiable_term_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:41.846412+00:00
-- url     : https://prove2.me/submissions/fd712e85-8b88-4222-bed5-171b7da253e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_differentiable_term


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
omit hT
namespace GlobalTheory.AnArc
theorem _root_.solution (h : Differentiable ℂ th) (μ : A.X) :
    Differentiable ℂ fun p : ℂ × A.V => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ) := by
  have := A.differentiable_term j α h μ
  unfold eTwoPi
  fun_prop
end GlobalTheory.AnArc
