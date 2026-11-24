-- Prove2me | solution 1 for GlobalTheory.cauchyRiemann_iff_differentiableOn_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:06.240004+00:00
-- url     : https://prove2.me/submissions/0c2ca2b3-1b68-450c-ac8a-f0a9209fe01c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Theorems.Thm_GlobalTheory_map_I_smul_of_cauchyRiemann
import Theorems.Thm_GlobalTheory_SCV_contDiffOn_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (U : Set (Fin g → ℂ)) (f : (Fin g → ℂ) → ℂ), IsOpen U → (DifferentiableOn ℝ f U → ((∀ a, ∀ z ∈ U, (fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))) = 0) ↔ DifferentiableOn ℂ f U)) ∧ (DifferentiableOn ℂ f U → ContDiffOn ℝ ∞ f U ∧ ∀ v, DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U) := by
  intro g U f hU
  refine ⟨fun hR => ⟨fun hCR => ?_, fun hC => ?_⟩, fun hC => ?_⟩
  ·
    intro z hz
    have hzR : DifferentiableAt ℝ f z := hR.differentiableAt (hU.mem_nhds hz)
    set L := fderiv ℝ f z with hL
    have hlin : ∀ (c : ℂ) (v : Fin g → ℂ), L (c • v) = c • L v :=
      map_I_smul_of_cauchyRiemann L (fun a => hCR a z hz)
    let L' : (Fin g → ℂ) →L[ℂ] ℂ :=
      { toFun := L
        map_add' := L.map_add
        map_smul' := hlin
        cont := L.continuous }
    have hres : L'.restrictScalars ℝ = L := by
      ext v; rfl
    exact (hasFDerivAt_of_restrictScalars ℝ hzR.hasFDerivAt hres).differentiableAt.differentiableWithinAt
  · intro a z hz
    have hzC : DifferentiableAt ℂ f z := hC.differentiableAt (hU.mem_nhds hz)
    rw [hzC.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    rw [← mul_assoc, I_mul_I]
    ring
  · refine ⟨?_, fun v => SCV.differentiableOn_fderiv_apply hU hC v⟩
    exact (SCV.contDiffOn_of_differentiableOn hU hC ∞).restrict_scalars ℝ
end GlobalTheory
