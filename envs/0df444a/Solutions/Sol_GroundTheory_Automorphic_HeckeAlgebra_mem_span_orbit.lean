-- Prove2me | solution 1 for GroundTheory.Automorphic.HeckeAlgebra.mem_span_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:47:21.021881+00:00
-- url     : https://prove2.me/submissions/e5fa893e-2ab3-4eb0-aa3e-e4276c540398

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
open GroundTheory.Automorphic.HeckeAlgebra
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic.HeckeAlgebra
theorem _root_.solution [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (w : V) :
    w ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  set S := Submodule.span ℂ (range fun g => ρ g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this
end GroundTheory.Automorphic.HeckeAlgebra
