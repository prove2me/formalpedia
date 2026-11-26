-- Prove2me | solution 1 for Kyprianou.Ch04.continuousWeightOnLeftLimitPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:14.44543+00:00
-- url     : https://prove2.me/submissions/d6838358-1065-45b7-98b0-a34c6aa008f9

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A continuous time-space function evaluated on supplied positive-time left limits is strict-left continuous. -/
theorem solution (Y L : NNReal → ℝ) (f : ℝ → ℝ → ℝ)
    (hL : ∀ t, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (L t)))
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    ∀ r, 0 < r → Tendsto (fun t : NNReal => f (t : ℝ) (L t))
      (𝓝[<] r) (𝓝 (f (r : ℝ) (L r))) := by
  have hEq (t : NNReal) (ht : 0 < t) : Y.leftLim t = L t := by
    haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0,ht⟩
    exact leftLim_eq_of_tendsto (hL t ht)
  intro r hr
  have hY : Tendsto Y (𝓝[<] r) (𝓝 (Y.leftLim r)) := by
    rw [hEq r hr]
    exact hL r hr
  have hYleft := (continuousWithinAt_leftLim_Iic hY).tendsto.mono_left
    (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hLleft : Tendsto L (𝓝[<] r) (𝓝 (L r)) := by
    rw [← hEq r hr]
    apply hYleft.congr'
    filter_upwards [Ioo_mem_nhdsLT hr] with t ht
    exact hEq t ht.1
  have hpair : Tendsto (fun t : NNReal => ((t : ℝ),L t)) (𝓝[<] r)
      (𝓝 ((r : ℝ),L r)) :=
    (NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hLleft
  have hp : Tendsto (fun t : NNReal => ((t : ℝ),L t)) (𝓝[<] r)
      (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set ℝ)] ((r : ℝ),L r)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpair,Eventually.of_forall fun t => ⟨t.coe_nonneg,mem_univ _⟩⟩
  exact (hf ((r : ℝ),L r) ⟨r.coe_nonneg,mem_univ _⟩).tendsto.comp hp
