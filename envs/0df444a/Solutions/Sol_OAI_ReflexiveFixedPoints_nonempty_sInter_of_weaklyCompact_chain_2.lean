-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.nonempty_sInter_of_weaklyCompact_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:00:39.541374+00:00
-- url     : https://prove2.me/submissions/dc69433e-f58a-4e20-931d-13a1be762702

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/MinimalInvariant.lean:L26-L49
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.nonempty_sInter_of_weaklyCompact_chain. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness

-- ---- from OAI.Analysis.Nonexpansive.MinimalInvariant ----
namespace OAI

/-!
# A genuine minimal invariant set

The order is reverse inclusion among the nonempty norm-closed convex
invariant subsets of a separable invariant set.  Intersections of chains
are nonempty in the actual weak topology.  No weak continuity of the
nonexpansive map is used: invariance passes to intersections pointwise.
-/

noncomputable section

open Set TopologicalSpace

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The weak compactness argument used for the lower bound of a chain. -/
theorem nonempty_sInter_of_weaklyCompact_chain
    {c : Set (Set X)} (hne : c.Nonempty) (hc : IsChain (· ⊆ ·) c)
    (hcompact : ∀ s ∈ c, WeaklyCompact s)
    (hclosed : ∀ s ∈ c, WeaklyClosed s)
    (hnonempty : ∀ s ∈ c, s.Nonempty) : (⋂₀ c).Nonempty := by
  classical
  let : Nonempty c := hne.to_subtype
  let w : c → Set (WeakSpace ℝ X) := fun s => (toWeakSpace ℝ X) '' (s : Set X)
  have hdir : Directed (· ⊇ ·) w := by
    intro s t
    rcases hc.total s.property t.property with hst | hts
    · exact ⟨s, Subset.rfl, Set.image_mono hst⟩
    · exact ⟨t, Set.image_mono hts, Subset.rfl⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    w hdir (fun s => (hnonempty s s.property).image _)
    (fun s => hcompact s s.property) (fun s => hclosed s s.property)
  refine ⟨(toWeakSpace ℝ X).symm z, Set.mem_sInter.mpr ?_⟩
  intro s hs
  obtain ⟨x, hx, hzx⟩ := Set.mem_iInter.mp hz ⟨s, hs⟩
  have heq : (toWeakSpace ℝ X).symm z = x := by
    rw [← hzx]
    exact (toWeakSpace ℝ X).symm_apply_apply x
  simpa only [heq] using hx

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.nonempty_sInter_of_weaklyCompact_chain.{u} := @_root_.OAI.ReflexiveFixedPoints.nonempty_sInter_of_weaklyCompact_chain.{u}
