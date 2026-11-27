-- Prove2me | solution 1 for Kyprianou.Ch04.compactUniformSequenceEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:14:02.201314+00:00
-- url     : https://prove2.me/submissions/c4d1a845-25fe-4c61-ace6-a59d16401e11

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rightContinuousCompactEnvelopeV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Pairwise dyadic envelopes control the limit without requiring its measurability
or right continuity as an additional assumption. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → NNReal → Ω → ℝ) (X : NNReal → Ω → ℝ) (T : NNReal)
    (hM : ∀ n t, AEMeasurable (Y n t) P)
    (hR : ∀ n, ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y n s w) (Ici t) t)
    (hU : ∀ᵐ w ∂P, ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T,
      |Y n t w - X t w| < d) :
    ∃ S : ℕ → Ω → ℝ≥0∞, (∀ n, Measurable (S n)) ∧ ∀ᵐ w ∂P,
      (∀ n t, t ≤ T → ENNReal.ofReal |Y n t w - X t w| ≤ S n w) ∧
      (∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n ≥ N, S n w ≤ ENNReal.ofReal d) := by
  have hr (m l : ℕ) : ∀ᵐ w ∂P, ∀ t,
      ContinuousWithinAt (fun s => Y m s w - Y l s w) (Ici t) t := by
    filter_upwards [hR m,hR l] with w hm hl
    exact fun t => (hm t).sub (hl t)
  choose Q hQm hQ using fun m l => Kyprianou.Ch04.rightContinuousCompactEnvelopeV1
    P (fun t w => Y m t w - Y l t w) T (fun t => (hM m t).sub (hM l t)) (hr m l)
  let S (m : ℕ) (w : Ω) := ⨆ l : ℕ, Q m (m+l) w
  refine ⟨S,fun m => Measurable.iSup (fun l => hQm m (m+l)),?_⟩
  filter_upwards [hU,ae_all_iff.mpr (fun m => ae_all_iff.mpr (hQ m))] with w hw hq
  constructor
  · intro m t ht
    by_cases hf : S m w = ⊤
    · rw [hf]; exact le_top
    have hb (l : ℕ) : |Y m t w - Y (m+l) t w| ≤ (S m w).toReal := by
      have hh := ENNReal.toReal_mono hf
        (((hq m (m+l)).1 t ht).trans (le_iSup (fun l => Q m (m+l) w) l))
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using hh
    rw [← ENNReal.ofReal_toReal hf]
    apply ENNReal.ofReal_le_ofReal
    by_contra! hbad
    obtain ⟨N,hN⟩ := hw ((|Y m t w-X t w|-(S m w).toReal)/2) (by linarith)
    have hsmall := hN (m+N) (by omega) t ht
    have htri := abs_add_le (Y m t w - Y (m+N) t w) (Y (m+N) t w - X t w)
    have he : (Y m t w - Y (m+N) t w) + (Y (m+N) t w - X t w) =
        Y m t w - X t w := by ring
    rw [he] at htri
    linarith [hb N]
  · intro d hd
    obtain ⟨N,hN⟩ := hw (d/2) (by positivity)
    refine ⟨N,fun m hm => iSup_le fun l => (hq m (m+l)).2 d ?_⟩
    intro t ht
    have h := abs_sub (Y m t w-X t w) (Y (m+l) t w-X t w)
    have he : (Y m t w-X t w)-(Y (m+l) t w-X t w) =
        Y m t w-Y (m+l) t w := by ring
    rw [he] at h
    linarith [hN m hm t ht,hN (m+l) (by omega) t ht]
