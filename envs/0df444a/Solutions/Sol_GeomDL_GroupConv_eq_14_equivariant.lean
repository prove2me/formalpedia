-- Prove2me | solution 1 for GeomDL.GroupConv.eq_14_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T15:56:46.66118+00:00
-- url     : https://prove2.me/submissions/1c9681d6-de2c-4b24-8d30-7a9ef9c47007

import Mathlib
import Definitions.Def_GeomDL_GroupConv_Model

open GeomDL.GroupConv

universe u v

theorem solution {G : Type u} {Ω : Type v} [Group G] [MulAction G Ω]
    [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSMul G Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.SMulInvariantMeasure G Ω μ]
    (htrans : ∀ a b : Ω, ∃ k : G, k • a = b)
    (h : G) (x θ : Ω → ℝ) (g : G) :
    groupConvolution μ (signalAction h x) θ g =
      regularAction h (groupConvolution μ x θ) g := by
  simp only [groupConvolution, signalPairing, signalAction, regularAction]
  rw [← MeasureTheory.integral_smul_eq_self (μ := μ)
    (fun u => x u * θ ((h⁻¹ * g)⁻¹ • u)) (g := h⁻¹)]
  congr 1
  funext u
  simp only [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
