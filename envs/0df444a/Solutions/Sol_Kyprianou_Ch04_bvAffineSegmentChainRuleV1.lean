-- Prove2me | solution 1 for Kyprianou.Ch04.bvAffineSegmentChainRuleV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:10:05.909652+00:00
-- url     : https://prove2.me/submissions/97aa8d3f-4d90-4e93-bfdc-ec7cf86bf46b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvAffineDerivativeIntervalIntegrableV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (a d l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) :
    f (r, a + d * r) - f (l, a + d * l) =
      ∫ u in l..r, fderiv ℝ f (u, a + d * u) (1, d) := by
  let H : Set (ℝ × ℝ) := Set.prod (Set.Ici (0 : ℝ)) Set.univ
  let q : ℝ → ℝ × ℝ := fun u => (u, a + d * u)
  have hq : Continuous q := by fun_prop
  have hm : MapsTo q (Icc l r) H := fun u hu => ⟨hl.trans hu.1, mem_univ _⟩
  have hc : ContinuousOn (f ∘ q) (Icc l r) := hf.continuousOn.comp hq.continuousOn hm
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hc
  · intro u hu
    have hmem : H ∈ 𝓝 (q u) := by
      have hpos : 0 < u := hl.trans_lt hu.1
      refine Filter.mem_of_superset
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds
          (show q u ∈ Set.prod (Ioi (0 : ℝ)) Set.univ from ⟨hpos, mem_univ _⟩)) ?_
      intro z hz
      exact ⟨show z.1 ∈ Ici (0 : ℝ) from le_of_lt (show 0 < z.1 from hz.1), hz.2⟩
    have hDiff := (hf.differentiableOn_one (q u) (hm ⟨hu.1.le, hu.2.le⟩)).differentiableAt hmem
    have hq' : HasDerivAt q (1, d) u := by
      simpa [q, id] using (hasDerivAt_id u).prodMk
        (((hasDerivAt_id u).const_mul d).const_add a)
    exact hDiff.hasFDerivAt.comp_hasDerivAt u hq'
  · exact Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1 f hf a d l r hl hlr (1, d)
