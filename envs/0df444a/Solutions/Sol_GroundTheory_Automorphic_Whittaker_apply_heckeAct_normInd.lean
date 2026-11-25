-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.apply_heckeAct_normInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:57.10412+00:00
-- url     : https://prove2.me/submissions/02f61c80-a9c7-41b4-83d5-9d7bd4968455

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

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
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [μ.IsMulRightInvariant]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {ξ : smoothVectors (Representation.dual ρ)}
    (hξ : ξ ∈ fixedVectors (contragredient ρ) K) (v : V) :
    (ξ : Module.Dual ℂ V) (heckeAct μ ρ (normInd μ K) v) = (ξ : Module.Dual ℂ V) v := by
  have hK0 : μ.real (K : Set G) ≠ 0 := by
    rw [measureReal_ne_zero_iff hKc.measure_lt_top.ne]
    exact (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  rw [dual_heckeAct μ (normInd_mem μ hKc hKo) (hρ v)]
  have hpt : ∀ g, normInd μ K g * (ξ : Module.Dual ℂ V) (ρ g v) =
      (K : Set G).indicator
        (fun _ => ((μ.real (K : Set G))⁻¹ : ℂ) * (ξ : Module.Dual ℂ V) v) g := by
    intro g
    by_cases hg : g ∈ (K : Set G)
    · rw [normInd, Set.indicator_of_mem hg, Set.indicator_of_mem hg,
        mem_fixedVectors_contragredient.1 hξ g hg v]
    · rw [normInd, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ hK0, Complex.ofReal_one, one_mul]
end GroundTheory.Automorphic.Whittaker
