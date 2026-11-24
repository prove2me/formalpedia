-- Prove2me | solution 1 for GlobalTheory.PowerSeriesFlat.flat_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:30.338313+00:00
-- url     : https://prove2.me/submissions/fe2b55bd-267c-4e76-a237-a6b5369d8586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatMvPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.PowerSeriesFlat
namespace GlobalTheory.PowerSeriesFlat
theorem _root_.solution (T : Type*) [CommRing T] [IsNoetherianRing T] (ι : Type*) :
    Module.Flat T (ι → T) := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x h
  let φ : (Fin l → T) →ₗ[T] T := Fintype.linearCombination T f
  have hφ : ∀ v : Fin l → T, φ v = ∑ i, f i * v i := by
    intro v
    simp [φ, Fintype.linearCombination_apply, mul_comm]
  have hfg : (LinearMap.ker φ).FG := IsNoetherian.noetherian _
  obtain ⟨k, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hx : ∀ t : ι, ∃ c : Fin k → T, ∑ j, c j • s j = fun i => x i t := by
    intro t
    have hm : (fun i => x i t) ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, hφ]
      have := congrFun h t
      simpa [Finset.sum_apply] using this
    rw [← hs] at hm
    exact (Submodule.mem_span_range_iff_exists_fun T).1 hm
  choose c hc using hx
  refine ⟨k, fun i j => s j i, fun j t => c t j, ?_, ?_⟩
  · intro i
    funext t
    have := congrFun (hc t) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j
    have hm : s j ∈ LinearMap.ker φ := by
      rw [← hs]
      exact Submodule.subset_span ⟨j, rfl⟩
    rwa [LinearMap.mem_ker, hφ] at hm
end GlobalTheory.PowerSeriesFlat
