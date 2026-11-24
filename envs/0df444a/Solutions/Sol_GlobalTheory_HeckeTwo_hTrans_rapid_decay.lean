-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.hTrans_rapid_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:10:21.236752+00:00
-- url     : https://prove2.me/submissions/d9a5f293-256c-4d93-9a6f-7d595ec78abe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_fourier_decay_of_iteratedDeriv
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_iteratedDeriv_mem
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_contDiff_wF
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wSpan_integrable
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hTrans_eq_fourier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  intro σ hσ y hy N
  obtain ⟨C, hC⟩ := HDecay.fourier_decay_of_iteratedDeriv (HDecay.contDiff_wF hy)
    (fun n => HDecay.wSpan_integrable hy hσ (HDecay.iteratedDeriv_mem hy n)) N
  exact ⟨C, fun ν => by rw [HDecay.hTrans_eq_fourier hy ν]; exact hC ν⟩
end GlobalTheory.HeckeTwo
