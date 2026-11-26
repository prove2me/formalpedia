-- Prove2me | solution 1 for Kyprianou.Ch04.orderedSupSquareTailCauchyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:32.968837+00:00
-- url     : https://prove2.me/submissions/54d3b30b-063f-4774-8814-83adbee5cb89

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An ordered-cutoff maximal bound with a vanishing tail yields the full Cauchy estimate. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U : ℝ → NNReal → Ω → ℝ) (T : NNReal) (q : ℝ → ℝ)
    (hq : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hb : ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      Integrable (fun w => sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T)) P ∧
      (∫ w, sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T) ∂P) ≤ q b) :
    ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
      ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
        Integrable (fun w => sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T)) P ∧
        (∫ w, sSup ((fun t : NNReal => |U a t w - U b t w|^2) '' Iic T) ∂P) < δ := by
  intro δ hδ
  obtain ⟨r,hr,hsmall⟩ := Metric.tendsto_nhdsWithin_nhds.mp hq δ hδ
  let e0 := min r 1 / 2
  have he0 : 0 < e0 := by dsimp [e0]; positivity
  have he01 : e0 < 1 := by dsimp [e0]; linarith [min_le_right r (1:ℝ)]
  have he0r : e0 < r := by dsimp [e0]; linarith [min_le_left r (1:ℝ)]
  have hq' (a : ℝ) (ha : 0 < a) (ha0 : a < e0) : q a < δ := by
    have h := hsmall (x := a) ha (by simpa [Real.dist_eq,abs_of_pos ha] using ha0.trans he0r)
    rw [Real.dist_eq,sub_zero] at h
    exact (le_abs_self _).trans_lt h
  refine ⟨e0,he0,he01,?_⟩
  intro a b ha ha0 hb' hb0
  rcases lt_trichotomy a b with hab | hab | hba
  · have h := hb a b ha hab (hb0.trans he01)
    exact ⟨h.1,h.2.trans_lt (hq' b hb' hb0)⟩
  · subst b
    have hz : (fun w => sSup ((fun t : NNReal => |U a t w - U a t w|^2) '' Iic T)) =
        fun _ => (0 : ℝ) := by
      funext w
      simp only [sub_self,abs_zero,zero_pow (by decide : 2 ≠ 0)]
      rw [(show (Iic T).Nonempty from ⟨T,by simp⟩).image_const,csSup_singleton]
    rw [hz]
    simp [hδ]
  · have h := hb b a hb' hba (ha0.trans he01)
    simpa only [abs_sub_comm (U b _ _) (U a _ _)] using
      (show Integrable (fun w => sSup ((fun t : NNReal => |U b t w - U a t w|^2) '' Iic T)) P ∧
        (∫ w, sSup ((fun t : NNReal => |U b t w - U a t w|^2) '' Iic T) ∂P) < δ from
        ⟨h.1,h.2.trans_lt (hq' a ha ha0)⟩)
