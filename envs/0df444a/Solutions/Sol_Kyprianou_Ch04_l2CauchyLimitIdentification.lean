-- Prove2me | solution 1 for Kyprianou.Ch04.l2CauchyLimitIdentification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:25:59.240388+00:00
-- url     : https://prove2.me/submissions/7629daaa-ae64-4913-bc62-0d437596a5c8

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u

/-- Identify the complete L2 limit of a Cauchy sequence with its limit in measure. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hC : CauchySeq (fun n => (hX n).toLp (X n)))
    (hY : TendstoInMeasure P X atTop Y) :
    ∃ h : MemLp Y 2 P,
      Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (h.toLp Y)) := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hC
  have hm := tendstoInMeasure_of_tendsto_Lp hz
  have hm' : TendstoInMeasure P X atTop (z : Ω → ℝ) :=
    TendstoInMeasure.congr_left (fun n => (hX n).coeFn_toLp) hm
  have heq : (z : Ω → ℝ) =ᵐ[P] Y := tendstoInMeasure_ae_unique hm' hY
  have h : MemLp Y 2 P := (memLp_congr_ae heq).mp (Lp.memLp z)
  refine ⟨h, ?_⟩
  have he : z = h.toLp Y := by
    apply Lp.ext
    exact heq.trans h.coeFn_toLp.symm
  simpa only [he] using hz
