-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.heckeAct_normInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:29.687806+00:00
-- url     : https://prove2.me/submissions/1c83c4a3-ef51-4711-aaa0-4a8bfc76cab6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    {v : V} (hv : v ∈ fixedVectors ρ K) : heckeAct μ ρ (normInd μ K) v = v := by
  have hvs : v ∈ smoothVectors ρ := mem_smoothVectors_of_mem_fixedVectors hKo hv
  have hK0 : μ.real (K : Set G) ≠ 0 := by
    rw [measureReal_ne_zero_iff hKc.measure_lt_top.ne]
    exact (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ (normInd_mem μ hKc hKo) hvs]
  have hpt : ∀ g, normInd μ K g * φ (ρ g v) =
      (K : Set G).indicator (fun _ => ((μ.real (K : Set G))⁻¹ : ℂ) * φ v) g := by
    intro g
    by_cases hg : g ∈ (K : Set G)
    · rw [normInd, Set.indicator_of_mem hg, Set.indicator_of_mem hg, mem_fixedVectors.1 hv g hg]
    · rw [normInd, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hK0, Complex.ofReal_one, one_mul]
end GroundTheory.Automorphic.Whittaker
