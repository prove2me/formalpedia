-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46DenseRightCrossingWitnessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:39:47.420663+00:00
-- url     : https://prove2.me/submissions/9a35cd8e-ec38-4d20-84c5-e089d52c399a

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (D : Set NNReal) (hD : Dense D) (f : NNReal → Real)
    (s t : NNReal) (hst : s < t)
    (hR : ContinuousWithinAt f (Ici s) s)
    (H : Real) (hH : H < f s) :
    ∃ r ∈ D, s < r ∧ r < t ∧ H < f r := by
  have he : {r : NNReal | H < f r} ∈ nhdsWithin s (Ici s) :=
    hR.eventually (Ioi_mem_nhds hH)
  obtain ⟨V,hV,hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
  obtain ⟨b,hb,hbV⟩ := exists_Ico_subset_of_mem_nhds hV ⟨t,hst⟩
  obtain ⟨r,hr,hrs,hrt⟩ := hD.exists_between (lt_min hb hst)
  exact ⟨r,hr,hrs,hrt.trans_le (min_le_right _ _),
    hsub ⟨hbV ⟨hrs.le,hrt.trans_le (min_le_left _ _)⟩,hrs.le⟩⟩
