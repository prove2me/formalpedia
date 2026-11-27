-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_qv_unweighted_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:32:18.809634+00:00
-- url     : https://prove2.me/submissions/54f36b10-de39-4f03-9b65-ad72e2de316f

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Theorems.Thm_Kyprianou_Ch04_ito43_path_jump_kernel_energy_bound
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Bound the time mass by the horizon and the actual squared-jump integral by the summable jump energy. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hJ : ({s : NNReal | 0 < s ∧ X s w ≠ L s w}).Countable)
    (H T t : NNReal) (ht : t ≤ T) (hT : T ≤ H)
    (hE : Summable (fun s : Ioc (0:NNReal) H => (X s w-L s w)^2))
    (σ : ℝ) (hσ : 0 ≤ σ) :
    σ*(∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) +
      (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        z.2^2/2 ∂(Kyprianou.Ch04.pathJumpMeasure X L w)) ≤
      σ*(T:ℝ) + (1/2)*(∑' s : Ioc (0:NNReal) H, (X s w-L s w)^2) := by
  have htime : (∫ s in Icc (0:ℝ) (t:ℝ), (1:ℝ) ∂volume) = (t:ℝ) := by
    rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
      ENNReal.toReal_ofReal t.coe_nonneg]
    simp
  have hjump :=
    (Kyprianou.Ch04.ito43_path_jump_kernel_energy_bound X L w hJ H t (ht.trans hT)
      (1/2) (by norm_num) hE (fun z => z.2^2/2) (by
        intro s _ _
        rw [abs_of_nonneg (by positivity : 0 ≤ (X s w-L s w)^2/2)]
        ring_nf <;> exact le_rfl)).2
  rw [htime]
  exact add_le_add (mul_le_mul_of_nonneg_left (show (t:ℝ) ≤ (T:ℝ) from ht) hσ)
    (abs_le.mp hjump).2
