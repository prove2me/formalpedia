-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.nonempty_sInter_of_weaklyCompact_chain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:57:27.199329+00:00
-- url     : https://prove2.me/submissions/ba8d01b0-b673-4737-a277-bea5bb6c1fd5

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness

open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem solution
    {c : Set (Set X)} (hne : c.Nonempty) (hc : IsChain (· ⊆ ·) c)
    (hcompact : ∀ s ∈ c, WeaklyCompact s)
    (hclosed : ∀ s ∈ c, WeaklyClosed s)
    (hnonempty : ∀ s ∈ c, s.Nonempty) : (⋂₀ c).Nonempty := by
  haveI : Nonempty c := hne.to_subtype
  let e := toWeakSpace ℝ X
  let t : c → Set (WeakSpace ℝ X) := fun s => e '' (s : Set X)
  have htd : Directed (· ⊇ ·) t := by
    intro s1 s2
    rcases eq_or_ne (s1 : Set X) s2 with h | h
    · exact ⟨s1, le_rfl, by simp only [t, h]; exact le_rfl⟩
    · rcases hc s1.2 s2.2 h with h12 | h21
      · exact ⟨s1, le_rfl, Set.image_mono h12⟩
      · exact ⟨s2, Set.image_mono h21, le_rfl⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd
    (fun s => (hnonempty s s.2).image _) (fun s => hcompact s s.2) (fun s => hclosed s s.2)
  refine ⟨e.symm y, ?_⟩
  rw [Set.mem_sInter]
  intro s hs
  have := Set.mem_iInter.mp hy ⟨s, hs⟩
  obtain ⟨x, hx, rfl⟩ := this
  simpa using hx
