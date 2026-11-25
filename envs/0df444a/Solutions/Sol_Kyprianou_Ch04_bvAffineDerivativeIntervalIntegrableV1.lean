-- Prove2me | solution 1 for Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:10:03.807618+00:00
-- url     : https://prove2.me/submissions/4f093c6d-95dd-4f96-8003-ee9789c1f040

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (a d l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (v : ℝ × ℝ) :
    IntervalIntegrable (fun u => fderiv ℝ f (u, a + d * u) v) volume l r := by
  let H : Set (ℝ × ℝ) := Set.prod (Set.Ici (0 : ℝ)) Set.univ
  let q : ℝ → ℝ × ℝ := fun u => (u, a + d * u)
  have hq : Continuous q := by fun_prop
  have hm : MapsTo q (Icc l r) H := fun u hu => ⟨hl.trans hu.1, mem_univ _⟩
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hc : ContinuousOn (fun u => fderivWithin ℝ f H (q u) v) (Icc l r) :=
    ((hf.continuousOn_fderivWithin hUnique le_rfl).comp hq.continuousOn hm).clm_apply
      continuousOn_const
  apply (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hlr hc).congr_uIoo
  rw [uIoo_of_le hlr]
  intro u hu
  have hmem : H ∈ 𝓝 (q u) := by
    have hpos : 0 < u := hl.trans_lt hu.1
    refine Filter.mem_of_superset
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show q u ∈ Set.prod (Ioi (0 : ℝ)) Set.univ from ⟨hpos, mem_univ _⟩)) ?_
    intro z hz
    exact ⟨show z.1 ∈ Ici (0 : ℝ) from le_of_lt (show 0 < z.1 from hz.1), hz.2⟩
  have hDiff := hf.differentiableOn_one (q u) (hm ⟨hu.1.le, hu.2.le⟩)
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v)
    (fderivWithin_eq_fderiv (hUnique (q u) (hm ⟨hu.1.le, hu.2.le⟩))
      (hDiff.differentiableAt hmem))
