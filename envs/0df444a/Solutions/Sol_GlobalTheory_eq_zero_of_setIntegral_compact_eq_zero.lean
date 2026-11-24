-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_setIntegral_compact_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:41.356558+00:00
-- url     : https://prove2.me/submissions/bd2b0d30-a213-4892-9efa-c891ebe27f4a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContDensityOnEqFibreMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [MetricSpace K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] {B : Set K} (hB : IsOpen B) {h : K → ℂ} (hc : ContinuousOn h B)
    (hz : ∀ S : Set K, IsCompact S → S ⊆ B → ∫ b in S, h b ∂ν = 0) {t : K} (ht : t ∈ B) :
    h t = 0 := by
  by_contra hne
  have hpos : 0 < ‖h t‖ := norm_pos_iff.2 hne
  have hca : ContinuousAt h t := hc.continuousAt (hB.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hca (‖h t‖ / 2) (half_pos hpos)
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hB t ht
  have hρ0 : 0 < min (ε / 2) (δ / 2) := lt_min (half_pos hε) (half_pos hδ)
  have hmemS : ∀ b ∈ Metric.closedBall t (min (ε / 2) (δ / 2)), dist b t < ε ∧ dist b t < δ := by
    intro b hb
    have hb' := Metric.mem_closedBall.1 hb
    constructor
    · linarith [min_le_left (ε / 2) (δ / 2)]
    · linarith [min_le_right (ε / 2) (δ / 2)]
  have hSc := isCompact_closedBall t (min (ε / 2) (δ / 2))
  have hSB : Metric.closedBall t (min (ε / 2) (δ / 2)) ⊆ B := fun b hb =>
    hδB (Metric.mem_ball.2 (hmemS b hb).2)
  have hνS : 0 < ν (Metric.closedBall t (min (ε / 2) (δ / 2))) :=
    Metric.measure_closedBall_pos ν t hρ0
  have hνSf : ν (Metric.closedBall t (min (ε / 2) (δ / 2))) < ⊤ := hSc.measure_lt_top
  have hIh : IntegrableOn h (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    (hc.mono hSB).integrableOn_compact hSc
  have hIc : IntegrableOn (fun _ => h t) (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    integrableOn_const hνSf.ne
  have key := integral_sub hIh hIc
  rw [hz _ hSc hSB, setIntegral_const, zero_sub] at key
  have hbound := norm_setIntegral_le_of_norm_le_const hνSf (f := fun b => h b - h t)
    (C := ‖h t‖ / 2) (fun b hb => by rw [← dist_eq_norm]; exact (hball (hmemS b hb).1).le)
  rw [key, norm_neg, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hbound
  have hreal : 0 < ν.real (Metric.closedBall t (min (ε / 2) (δ / 2))) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hνS.ne' hνSf.ne
  nlinarith [mul_pos hreal hpos]
end GlobalTheory
