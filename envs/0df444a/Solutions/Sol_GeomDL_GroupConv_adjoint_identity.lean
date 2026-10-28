-- Prove2me | solution 1 for GeomDL.GroupConv.adjoint_identity
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:38:00.910886+00:00
-- url     : https://prove2.me/submissions/0faa305b-ce56-4997-b022-fa07b670b7d5

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

open GeomDL.GroupConv

universe u v
theorem solution {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSMul G Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.SMulInvariantMeasure G Ω μ]
    (htrans : ∀ a b : Ω, ∃ k : G, k • a = b)
    (g : G) (x θ : Ω → ℝ) :
    signalPairing μ x (signalAction g θ) =
      signalPairing μ (signalAction g⁻¹ x) θ := by
  unfold signalPairing signalAction
  rw [← MeasureTheory.integral_smul_eq_self (μ := μ) (fun u => x u * θ (g⁻¹ • u)) (g := g)]
  simp [inv_inv, smul_smul]
