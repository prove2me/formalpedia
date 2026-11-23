-- Prove2me | solution 1 for GlobalTheory.CubeFace.span_triples
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:54.105226+00:00
-- url     : https://prove2.me/submissions/a9a0c3df-679c-4016-b25e-4650ad932a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℝ V] (Λ : Submodule ℤ V)
    (h : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Submodule.span ℝ {l : Fin 3 → V | ∀ a, l a ∈ Λ} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h1 : x a ∈ Submodule.span ℝ (Λ : Set V) := by rw [h]; trivial
  have h2 := Submodule.mem_map_of_mem (f := LinearMap.single ℝ (fun _ : Fin 3 => V) a) h1
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩ b
  by_cases hb : b = a
  · subst hb; simpa using hv
  · simp [Pi.single_eq_of_ne hb]
end GlobalTheory.CubeFace
