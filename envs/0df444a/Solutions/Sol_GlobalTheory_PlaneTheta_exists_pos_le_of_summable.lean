-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.exists_pos_le_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:11.775746+00:00
-- url     : https://prove2.me/submissions/5eab8a67-d3f4-4199-9534-d0acd85b8415

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
namespace GlobalTheory.PlaneTheta
theorem _root_.solution {ι : Type*} {q : ι → ℝ}
    (h : Summable fun i => Real.exp (-q i)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < q i → δ ≤ q i := by
  have h1 := h.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  rw [Filter.eventually_cofinite] at h1
  have h2 : {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}.Finite := h1.subset fun i hi => hi.1
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i ∈ {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}, δ < q i :=
    (Filter.eventually_all_finite h2).2 fun i hi => nhdsWithin_le_nhds (gt_mem_nhds hi.2)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  obtain ⟨δ, ⟨h5, h6⟩, h7⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
  refine ⟨δ, h7, fun i hi => ?_⟩
  by_cases hc : Real.exp (-q i) < Real.exp (-1)
  · rw [Real.exp_lt_exp] at hc
    linarith
  · exact (h5 i ⟨hc, hi⟩).le
end GlobalTheory.PlaneTheta
