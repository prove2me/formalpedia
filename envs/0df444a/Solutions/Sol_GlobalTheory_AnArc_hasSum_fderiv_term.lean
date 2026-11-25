-- Prove2me | solution 1 for GlobalTheory.AnArc.hasSum_fderiv_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:15.6294+00:00
-- url     : https://prove2.me/submissions/9a4ce0ac-5bb9-4535-a14e-4256e18c8d2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_locally_normal_right
import Theorems.Thm_GlobalTheory_AnArc_differentiable_term
import Theorems.Thm_GlobalTheory_SCV_hasSum_fderiv_of_locally_normal


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
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v v₀ : A.V) :
    HasSum (fun μ => fderiv ℂ (A.term j α th μ) v v₀ * eTwoPi (w * A.exponent j α μ))
      (fderiv ℂ (A.Sum j α th w) v v₀) := by
  have h1 := SCV.hasSum_fderiv_of_locally_normal isOpen_univ
    (F := fun μ v => A.term j α th μ v * eTwoPi (w * A.exponent j α μ))
    (fun μ => ((A.differentiable_term j α h.1 μ).mul_const _).differentiableOn)
    (fun v _ => locally_normal_right hT hj h hw v) (Set.mem_univ v)
  refine ((ContinuousLinearMap.apply ℂ ℂ v₀).hasSum h1).congr_fun fun μ => ?_
  rw [fderiv_mul_const (A.differentiable_term j α h.1 μ v)]
  simp [mul_comm]
end GlobalTheory.AnArc
