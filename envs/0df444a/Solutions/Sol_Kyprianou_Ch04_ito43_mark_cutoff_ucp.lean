-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_mark_cutoff_ucp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:28:10.748984+00:00
-- url     : https://prove2.me/submissions/875f9463-5aae-4b22-96ee-8e0fc2d3a1b1

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_integral_series
import Theorems.Thm_Kyprianou_Ch04_ito43_mark_cutoff_error_sections
import Theorems.Thm_Kyprianou_Ch04_ito43_cadlag_stopped_cutoff_kernel_uniform
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_generic_right_continuous_bounded
import Theorems.Thm_Kyprianou_Ch04_ito43_ae_right_continuous_sup
import Theorems.Thm_Kyprianou_Ch04_ito43_uniform_sup_bound_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (hr : Continuous r) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ z, |z| ≤ δ → r z = 0) (T : NNReal) :
    let E : ℕ → NNReal → Ω → ℝ := fun n t w =>
      let u : ℕ → NNReal := fun k => T*(k:NNReal)/(n:NNReal)
      let v : ℕ → NNReal := fun k => min t (u k)
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) -
        ∑ k ∈ Finset.range n, r (X (v (k+1)) w-X (v k) w)
    ∀ e : ℝ, 0 < e → Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by
  intro E e he
  have hgood : ∀ᵐ w ∂P,
      (∀ n, (∀ t, ContinuousWithinAt (fun s => |E n s w|) (Ici t) t) ∧
        BddAbove (range (fun t : Iic T => |E n t w|))) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ≤ T, |E n t w| < ε) := by
    filter_upwards [hX.cadlag_ae,hL] with w hc hl
    let K : NNReal → ℝ → ℝ → ℝ := fun _ _ z => r z
    have hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2) :=
      hr.comp (continuous_snd.comp continuous_snd)
    have hz : ∀ s x z, |z| ≤ δ → K s x z = 0 := fun _ _ z h => hzero z h
    have h0 := hzero 0 (by simpa using hδ.le)
    have heq : (fun n t => E n t w) = fun n t =>
        (∑' s : Ioc (0:NNReal) t, K s.1 (L s.1 w) (X s.1 w-L s.1 w)) -
        ∑ k ∈ Finset.range n, K (T*(k:NNReal)/(n:NNReal)) (X (T*(k:NNReal)/(n:NNReal)) w)
          (X (min t (T*((k+1:ℕ):NNReal)/(n:NNReal))) w-X (min t (T*(k:NNReal)/(n:NNReal))) w) := by
      funext n t
      dsimp [E,K]
      rw [Kyprianou.Ch04.ito43_mark_integral_series X L w hc hl r h0 t]
    refine ⟨?_,?_⟩
    · apply Eq.mpr (congrArg (fun F : ℕ → NNReal → ℝ =>
          ∀ n, (∀ t, ContinuousWithinAt (fun s => |F n s|) (Ici t) t) ∧
            BddAbove (range (fun t : Iic T => |F n t|))) heq)
      exact Kyprianou.Ch04.ito43_cutoff_generic_right_continuous_bounded
        (fun t => X t w) (fun t => L t w) hc hl K hK δ hδ hz T
    · intro ε hε
      have h := Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform
        (fun t => X t w) (fun t => L t w) hc hl K hK δ hδ hz T ε hε
      filter_upwards [h] with n hn
      intro t ht
      rw [congrFun (congrFun heq n) t,abs_sub_comm]
      exact hn t ht
  let B : ℕ → Ω → ℝ := fun n w => sSup (range (fun t : Iic T => |E n t w|))
  have hm (n : ℕ) : AEStronglyMeasurable (B n) P :=
    Kyprianou.Ch04.ito43_ae_right_continuous_sup P (E n) T
      (Kyprianou.Ch04.ito43_mark_cutoff_error_sections P X L hX hL r hr δ hδ hzero T n)
      (hgood.mono fun w hw => hw.1 n)
  have hb : ∀ᵐ w ∂P, Tendsto (fun n => B n w) atTop (nhds 0) ∧
      ∀ n t, t ≤ T → |E n t w| ≤ |B n w| := by
    filter_upwards [hgood] with w hw
    exact Kyprianou.Ch04.ito43_uniform_sup_bound_limit (fun n t => E n t w) T
      (fun n => (hw.1 n).2) hw.2
  exact Kyprianou.Ch04.ito43_ucp_countable_envelope P E B T hm
    (hb.mono fun w hw => hw.1) (hb.mono fun w hw => hw.2) e he
