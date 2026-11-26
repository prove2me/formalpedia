-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_kernel_measurable_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:08.066262+00:00
-- url     : https://prove2.me/submissions/6bc36f5c-4973-480e-a524-f5e104f43843

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Countable clipped dyadic evaluations give a finite measurable compact bound. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : Measurable (fun z : NNReal × Omega => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w))
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ))) (T : NNReal) :
    ∃ M : Omega → ℝ, Measurable M ∧ (∀ w, 0 ≤ M w) ∧
      ∀ w s, s ∈ Icc (0 : ℝ) (T : ℝ) → ∀ r : NNReal, r ≤ T → |g (s,X r w)| ≤ M w := by
  let d : ℕ × ℕ → NNReal := fun k => min T ((k.1 : NNReal) / 2 ^ k.2)
  let a : NNReal → ℕ → ℕ × ℕ := fun t n => (Nat.ceil ((t : ℝ)*2^n),n)
  let K : (ℕ × ℕ) × (ℕ × ℕ) → Omega → ℝ := fun k w =>
    |g ((d k.1 : ℝ), X (d k.2) w)|
  let M : Omega → ℝ := fun w => ⨆ k, K k w
  have hd (k : ℕ × ℕ) : d k ≤ T := min_le_left _ _
  have hg0 : Continuous (fun z : ℝ × ℝ => g (max 0 z.1,z.2)) :=
    hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max 0 z.1 from le_max_left _ _,mem_univ _⟩)
  have hKm (k : (ℕ × ℕ) × (ℕ × ℕ)) : Measurable (K k) := by
    have hx : Measurable (X (d k.2)) := hX.comp (measurable_const.prodMk measurable_id)
    have h := (hg0.measurable.comp
      (measurable_const.prodMk hx : Measurable (fun w => ((d k.1 : ℝ),X (d k.2) w)))).abs
    simpa only [K,Function.comp_apply,Prod.fst,Prod.snd,max_eq_right (d k.1).coe_nonneg] using h
  have hbdd (w : Omega) : BddAbove (range (fun k => K k w)) := by
    obtain ⟨C,_,hC⟩ := Kyprianou.Ch04.ito43_compact_kernel_bound (fun t => X t w) (hCad w) g hg T
    refine ⟨C,?_⟩
    rintro y ⟨k,rfl⟩
    exact hC _ ⟨by positivity,by exact_mod_cast hd k.1⟩ _ (hd k.2)
  have hle (w : Omega) (k : (ℕ × ℕ) × (ℕ × ℕ)) : K k w ≤ M w := le_ciSup (hbdd w) k
  have hdt (t : NNReal) (ht : t ≤ T) :
      Tendsto (fun n => d (a t n)) atTop (nhds t) := by
    simpa only [d,a,min_eq_right ht] using
      (tendsto_const_nhds (x := T)).min (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto t)
  have hdr (t : NNReal) (ht : t ≤ T) (n : ℕ) : t ≤ d (a t n) :=
    le_min ht (AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal t n)
  refine ⟨M,Measurable.iSup hKm, ?_, ?_⟩
  · intro w
    exact (abs_nonneg _).trans (hle w ((0,0),(0,0)))
  · intro w s hs r hr
    let s' := Real.toNNReal s
    have hs' : s' ≤ T := (Real.toNNReal_le_iff_le_coe).mpr hs.2
    have hsval : (s' : ℝ) = s := Real.coe_toNNReal s hs.1
    have hrt : Tendsto (fun n => d (a r n)) atTop (nhdsWithin r (Ici r)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hdt r hr,Eventually.of_forall (hdr r hr)⟩
    have hXt := (hCad w r).1.tendsto.comp hrt
    have hst : Tendsto (fun n => (d (a s' n) : ℝ)) atTop (nhds s) := by
      rw [← hsval]
      exact (NNReal.continuous_coe.tendsto s').comp (hdt s' hs')
    have hpair := hst.prodMk_nhds hXt
    have hlim : Tendsto (fun n => K (a s' n,a r n) w) atTop (nhds |g (s,X r w)|) := by
      have h := (hg0.tendsto (s,X r w)).comp hpair
      simpa only [K,Function.comp_apply,Prod.fst,Prod.snd,max_eq_right hs.1,max_eq_right (NNReal.coe_nonneg _)] using h.abs
    exact le_of_tendsto hlim (Eventually.of_forall fun n => hle w (a s' n,a r n))
