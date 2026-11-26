-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_time_slice_ftc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:16:47.557799+00:00
-- url     : https://prove2.me/submissions/1a780fe9-c113-4f33-91fb-96916779a94b

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

/-- Time increments at a fixed position are integrals of the continuous within-half-plane derivative. -/
theorem solution (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Icc a b, fderivWithin ℝ f
      (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)) (s,x) (1,0)) =
      f (b,x) - f (a,x) := by
  let S := Ici (0 : ℝ) ×ˢ (univ : Set ℝ)
  let g := fun s : ℝ => fderivWithin ℝ f S (s,x) (1,0)
  let k := fun s : ℝ => (s,x)
  have hmaps : MapsTo k (Icc a b) S := fun s hs => ⟨ha.trans hs.1,mem_univ _⟩
  have hk : Continuous k := continuous_id.prodMk continuous_const
  have hu : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici _).prod uniqueDiffOn_univ
  have hg : ContinuousOn g (Icc a b) :=
    ((hf.continuousOn_fderivWithin hu (by norm_num)).clm_apply continuousOn_const).comp
      hk.continuousOn hmaps
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hf.continuousOn.comp hk.continuousOn hmaps) _ (hg.intervalIntegrable_of_Icc hab)
  intro s hs
  have hs0 : 0 < s := ha.trans_lt hs.1
  have hmem : S ∈ nhds (s,x) := by
    apply Filter.mem_of_superset ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (s,x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) from ⟨hs0,mem_univ _⟩))
    exact prod_mono Ioi_subset_Ici_self Subset.rfl
  have hd := ((hf.differentiableOn (by norm_num) (s,x)
    (show (s,x) ∈ S from ⟨hs0.le,mem_univ _⟩)).differentiableAt hmem).hasFDerivAt
  have hdk : HasDerivAt k (1,0) s := (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h := hd.comp_hasDerivAt s hdk
  simpa only [g, fderivWithin_of_mem_nhds hmem] using h
