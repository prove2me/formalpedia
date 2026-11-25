-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_units_neg_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:44.865211+00:00
-- url     : https://prove2.me/submissions/fd876dd1-fa97-4dab-8e97-f055318c7d1a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalClassFormation_ExtensionEmbeddingOfIsRealAlgebraMap
import Theorems.Thm_GroundTheory_ProfCoh_apply_eq_abs_embedding_of_isReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.ProfCoh
theorem _root_.solution (S : Set {v : InfinitePlace K // v.IsReal}) :
    ∃ a : Kˣ, ∀ v : {v : InfinitePlace K // v.IsReal},
      (embedding_of_isReal v.2 (a : K) < 0 ↔ v ∈ S) ∧ (0 < embedding_of_isReal v.2 (a : K) ↔ v ∉ S) := by
  classical

  set c : InfinitePlace K → K := fun v => if h : v.IsReal then
    (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1) else 1 with hcdef
  let t : (v : InfinitePlace K) → WithAbs v.1 := fun v => WithAbs.toAbs v.1 (c v)
  let U : Set ((v : InfinitePlace K) → WithAbs v.1) := Set.pi Set.univ fun v => Metric.ball (t v) 1
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have htU : t ∈ U := fun v _ => Metric.mem_ball_self one_pos
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open hU ⟨t, htU⟩

  have hclose : ∀ v : InfinitePlace K, v (x - c v) < 1 := by
    intro v
    have h := hx v (Set.mem_univ v)
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hc : ∀ v : InfinitePlace K, v (c v) = 1 := by
    intro v
    rw [hcdef]
    show v.1 (if h : v.IsReal then (if (⟨v, h⟩ : {v : InfinitePlace K // v.IsReal}) ∈ S then -1 else 1)
      else 1) = 1
    split_ifs <;> simp only [AbsoluteValue.map_neg, AbsoluteValue.map_one]
  have hx0 : x ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
    have := hclose v
    rw [zero_sub, show v (-c v) = v (c v) from v.1.map_neg _, hc] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 x hx0, fun v => ?_⟩
  have h := hclose v.1
  rw [apply_eq_abs_embedding_of_isReal v.2, map_sub] at h
  have hcv : c v.1 = if v ∈ S then -1 else 1 := by rw [hcdef]; exact dif_pos v.2
  rw [hcv] at h
  rw [Units.val_mk0]
  by_cases hv : v ∈ S
  · rw [if_pos hv, map_neg, map_one, sub_neg_eq_add, abs_lt] at h
    exact ⟨⟨fun _ => hv, fun _ => by linarith [h.2]⟩, ⟨fun h' => by linarith [h.2], fun h' => absurd hv h'⟩⟩
  · rw [if_neg hv, map_one, abs_lt] at h
    exact ⟨⟨fun h' => by linarith [h.1], fun h' => absurd h' hv⟩, ⟨fun _ => hv, fun _ => by linarith [h.1]⟩⟩
end GroundTheory.ProfCoh
