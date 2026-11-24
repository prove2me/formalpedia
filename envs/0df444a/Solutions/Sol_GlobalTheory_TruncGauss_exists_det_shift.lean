-- Prove2me | solution 1 for GlobalTheory.TruncGauss.exists_det_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:59.983081+00:00
-- url     : https://prove2.me/submissions/165bb082-8ad7-4037-a7b7-8daa2018e766

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDefStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TruncatedGaussianIntegralUniformPosSemidef
import Theorems.Thm_GlobalTheory_TruncGauss_isCompact_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.TruncGauss
namespace GlobalTheory.TruncGauss
theorem _root_.solution (n : ℕ) (C r : ℝ) (hr : 0 < r) : ∃ η : ℝ, 0 < η ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) →
      ‖(H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ H ∈ {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C},
      ‖(H + (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
    refine (isCompact_bdd n C).eventually_forall_of_forall_eventually fun H _ => ?_
    have hc : Continuous fun z : ℝ × Matrix (Fin n) (Fin n) ℂ =>
        ‖(z.2 + (z.1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - z.2.det‖ := by
      fun_prop
    have h0 : ‖(H + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ = 0 := by simp
    have := hc.continuousAt (x := ((0 : ℝ), H))
    exact this.eventually (gt_mem_nhds (by simpa [h0] using hr))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨t, htpos, fun H hH => ht H hH⟩
end GlobalTheory.TruncGauss
