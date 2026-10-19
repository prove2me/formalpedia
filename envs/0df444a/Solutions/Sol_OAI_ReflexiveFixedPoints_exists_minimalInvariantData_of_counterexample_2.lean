-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:04:20.96068+00:00
-- url     : https://prove2.me/submissions/0661674f-1c5f-453b-9af7-835027d63e3c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/MinimalInvariant.lean:L51-L123
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Theorems.Thm_OAI_ReflexiveFixedPoints_exists_separable_invariant_subset
import Theorems.Thm_OAI_ReflexiveFixedPoints_nonempty_sInter_of_weaklyCompact_chain

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

/-- Restricting an actual fixed-point-free nonexpansive selfmap gives
minimal invariant data in the same ambient space and the same norm. -/
theorem exists_minimalInvariantData_of_counterexample
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    ∃ D : MinimalInvariantData (X := X), D.K ⊆ C := by
  classical
  obtain ⟨S, hSC, hSne, hSclosed, hSbounded, hSconvex, hSsep, hSinv⟩ :=
    exists_separable_invariant_subset hne hclosed hbounded hconvex F hF
  let family : Set (Set X) := {s | s ⊆ S ∧ s.Nonempty ∧ IsClosed s ∧
    Convex ℝ s ∧ InvariantSubset C F s}
  have hSmem : S ∈ family :=
    ⟨Subset.rfl, hSne, hSclosed, hSconvex, hSinv⟩
  have lower : ∀ c ⊆ family, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ family, ∀ s ∈ c, lb ⊆ s := by
    intro c hcf hc hcn
    obtain ⟨s₀, hs₀⟩ := hcn
    have hinterS : ⋂₀ c ⊆ S :=
      (Set.sInter_subset_of_mem hs₀).trans (hcf hs₀).1
    have hinterne : (⋂₀ c).Nonempty := by
      apply nonempty_sInter_of_weaklyCompact_chain ⟨s₀, hs₀⟩ hc
      · intro s hs
        exact weaklyCompact_of_closed_bounded_convex hX (hcf hs).2.2.1
          (hSbounded.subset (hcf hs).1) (hcf hs).2.2.2.1
      · intro s hs
        exact weaklyClosed_of_closed_convex (hcf hs).2.2.1 (hcf hs).2.2.2.1
      · intro s hs
        exact (hcf hs).2.1
    refine ⟨⋂₀ c, ⟨hinterS, hinterne, ?_, ?_, ?_⟩,
      fun s hs => Set.sInter_subset_of_mem hs⟩
    · exact isClosed_sInter fun s hs => (hcf hs).2.2.1
    · exact convex_sInter fun s hs => (hcf hs).2.2.2.1
    · intro x hx
      apply Set.mem_sInter.mpr
      intro s hs
      exact (hcf hs).2.2.2.2 x (Set.mem_sInter.mp hx s hs)
  obtain ⟨K, hKS, hKmin⟩ := zorn_superset_nonempty family lower S hSmem
  have hK := hKmin.prop
  have hKC : K ⊆ C := hKS.trans hSC
  let T : K → K := fun x =>
    ⟨F ⟨x, hKC x.property⟩, hK.2.2.2.2 ⟨x, hKC x.property⟩ x.property⟩
  have hT : LipschitzWith 1 T := by
    intro x y
    exact hF ⟨x, hKC x.property⟩ ⟨y, hKC y.property⟩
  have hTno : ∀ x : K, T x ≠ x := by
    intro x hx
    apply hno ⟨x, hKC x.property⟩
    apply Subtype.ext
    exact congrArg (fun y : K => (y : X)) hx
  have hTmin : MinimalInvariant K T := by
    intro s hsK hsne hsclosed hsconvex hsinv
    apply hKmin.eq_of_subset
    · refine ⟨hsK.trans hKS, hsne, hsclosed, hsconvex, ?_⟩
      intro x hx
      have hxK : (x : X) ∈ K := hsK hx
      exact hsinv ⟨x, hxK⟩ hx
    · exact hsK
  refine ⟨{
    K := K
    nonempty := hK.2.1
    closed := hK.2.2.1
    bounded := hSbounded.subset hKS
    convex := hK.2.2.2.1
    separable := hSsep.mono hKS
    weak_compact := weaklyCompact_of_closed_bounded_convex hX hK.2.2.1
      (hSbounded.subset hKS) hK.2.2.2.1
    T := T
    nonexpansive := hT
    no_fixed := hTno
    minimal := hTmin
  }, hKC⟩

end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints
open Set TopologicalSpace


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample.{u} := @_root_.OAI.ReflexiveFixedPoints.exists_minimalInvariantData_of_counterexample.{u}
