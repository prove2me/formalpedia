-- Prove2me | solution 1 for GlobalTheory.LineThrough.exists_common_nonroot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:49:09.883251+00:00
-- url     : https://prove2.me/submissions/c068b0b4-7ef8-47d7-af3e-c27f4037eaf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough
namespace GlobalTheory.LineThrough
theorem _root_.solution (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Countable)
    (h0 : (0 : MvPolynomial (Fin d) ℂ) ∉ S) :
    ∃ c : Fin d → ℂ, ∀ f ∈ S, MvPolynomial.eval c f ≠ 0 := by
  have hd : Dense (⋂ f ∈ S, {c : Fin d → ℂ | MvPolynomial.eval c f ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun f _ => ?_) hS (fun f hf => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval f) continuous_const
    · rw [Metric.dense_iff]
      intro x r hr
      by_contra hne
      apply h0
      have : f = 0 := by
        refine MvPolynomial.funext_set (fun i => Metric.ball (x i) r)
          (fun i => (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) |> infinite_of_mem_nhds (x i)) ?_
        intro y hy
        by_contra hy0
        apply hne
        refine ⟨y, ?_, by simpa using hy0⟩
        rw [ball_pi _ hr]
        exact hy
      exact this ▸ hf
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun f hf => by simpa using Set.mem_iInter₂.1 hc f hf⟩
end GlobalTheory.LineThrough
