-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isIrreducible_restrict_of_isMinimal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:26.892242+00:00
-- url     : https://prove2.me/submissions/58773d3f-c724-4b12-9332-4ab5ce283668

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
omit [MeasurableSpace G] [OpensMeasurableSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {V : Submodule ℂ H} [CompleteSpace V]
    (hV : π.IsInvariant V) (h : π.IsMinimal V) : (π.restrict V hV).IsIrreducible := by
  obtain ⟨hcl, -, hne, hmin⟩ := h
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun W hW hWinv => ?_⟩
  set U : Submodule ℂ H := W.map V.subtype with hU
  have hUcl : IsClosed (U : Set H) := by
    rw [hU, Submodule.map_coe]
    exact hcl.isClosedMap_subtype_val _ hW
  have hUinv : π.IsInvariant U := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨π.restrict V hV g w, hWinv g w hw, rfl⟩
  have hUV : U ≤ V := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  rcases hmin U hUcl hUinv hUV with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have : (w : H) ∈ U := ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro w _
    have : (w : H) ∈ U := by rw [h]; exact w.2
    obtain ⟨w', hw', hww'⟩ := this
    have : w' = w := Subtype.ext hww'
    rwa [← this]
end GroundTheory.Automorphic.UnitaryRep
