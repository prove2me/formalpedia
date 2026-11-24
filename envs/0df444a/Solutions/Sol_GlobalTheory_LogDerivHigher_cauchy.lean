-- Prove2me | solution 1 for GlobalTheory.LogDerivHigher.cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:26.964252+00:00
-- url     : https://prove2.me/submissions/951e72a7-14a8-44e9-a380-2cdfb75ef5d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Theorems.Thm_GlobalTheory_LogDerivHigher_extend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher
namespace GlobalTheory.LogDerivHigher
theorem _root_.solution (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) (g : ℂ → ℂ)
    (h1 : DifferentiableOn ℂ g (U \ Z)) (h2 : ∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K)
    (s : ℂ) (R : ℝ) (hR : 0 < R) (hs : s ∉ Z) (hsub : Metric.closedBall s R ⊆ U) (k : ℕ) :
    ‖iteratedDeriv k g s‖ ≤ k.factorial * K / R ^ k := by
  obtain ⟨G, g1, g2, g3⟩ := extend K U hU Z g h1 h2
  have hev : g =ᶠ[𝓝 s] G := by
    filter_upwards [Z.finite_toSet.isClosed.isOpen_compl.mem_nhds hs] with z hz
    exact (g2 z hz).symm
  rw [hev.iteratedDeriv_eq]
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR ?_
    fun z hz => g3 z (hsub (Metric.sphere_subset_closedBall hz))
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball s hR.ne']
  exact g1.mono hsub
end GlobalTheory.LogDerivHigher
