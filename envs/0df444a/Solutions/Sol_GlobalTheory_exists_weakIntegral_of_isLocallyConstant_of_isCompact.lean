-- Prove2me | solution 1 for GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:13.844149+00:00
-- url     : https://prove2.me/submissions/b8b7056f-52a2-4bad-b300-70b84d7aee45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory
open MeasureTheory ValuativeRel Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (U : Type) [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [OpensMeasurableSpace U] (m : Measure U) [IsFiniteMeasureOnCompacts m] (V : Type) [AddCommGroup V] [Module ℂ V] (T : U → V) (_ : IsLocallyConstant T) (K : Set U) (_ : IsCompact K) (_ : ∀ u, u ∉ K → T u = 0), ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ u, l (T u) ∂m := by
  intro U _ _ _ _ m _ V _ _ T hT K hK hzero
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun v : V => T ⁻¹' {v})
    (fun v => hT.isOpen_fiber v) (fun u _ => Set.mem_iUnion.2 ⟨T u, rfl⟩)
  have hS : ∀ u, T u ∈ insert 0 t := by
    intro u
    by_cases hu : u ∈ K
    · have h := ht hu
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff] at h
      obtain ⟨v, hv, huv⟩ := h
      rw [huv]
      exact Finset.mem_insert_of_mem hv
    · rw [hzero u hu]
      exact Finset.mem_insert_self 0 t
  have hmeas : ∀ v, MeasurableSet (T ⁻¹' {v}) := fun v => (hT.isOpen_fiber v).measurableSet
  refine ⟨∑ v ∈ insert 0 t, ((m.real (T ⁻¹' {v}) : ℂ)) • v, fun l => ?_⟩
  have hpt : ∀ u, l (T u) = ∑ v ∈ insert 0 t, (T ⁻¹' {v}).indicator (fun _ => l v) u := by
    intro u
    rw [Finset.sum_eq_single_of_mem (T u) (hS u)]
    · simp
    · intro v _ hv
      exact Set.indicator_of_notMem
        (show u ∉ T ⁻¹' {v} from fun h => hv (Set.mem_singleton_iff.1 h).symm) (fun _ => l v)
  have hint : ∀ v ∈ insert 0 t, Integrable ((T ⁻¹' {v}).indicator fun _ => l v) m := by
    intro v _
    by_cases hv : v = 0
    · subst hv
      simp
    · have hsub : T ⁻¹' {v} ⊆ K := by
        intro u hu
        by_contra hK'
        exact hv (by rw [← Set.mem_singleton_iff.1 hu, hzero u hK'])
      have hfin : m (T ⁻¹' {v}) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
      exact (integrable_indicator_iff (hmeas v)).2 (integrableOn_const (C := l v) hfin)
  rw [integral_congr_ae (ae_of_all _ hpt), integral_finset_sum _ hint, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hmeas v), map_smul, smul_eq_mul, Complex.real_smul]
end _root_.GlobalTheory
end GlobalTheory
