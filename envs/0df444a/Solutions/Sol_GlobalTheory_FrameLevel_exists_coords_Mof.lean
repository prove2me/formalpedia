-- Prove2me | solution 1 for GlobalTheory.FrameLevel.exists_coords_Mof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:05:06.048024+00:00
-- url     : https://prove2.me/submissions/b14206ea-b54d-4514-aac1-4a7e29491bf3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameLevel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameLevel
theorem _root_.solution {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    {y : S.V} (hy : y ∈ S.Mof g g') :
    ∃ β γ : Fin (r + 1) → L.O, y = ∑ i, (β i : E) • g i +
      ∑ i, (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
  unfold Frames.Mof at hy
  rw [Submodule.span_union, Submodule.mem_sup] at hy
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu
  obtain ⟨γ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu'
  exact ⟨β, γ, rfl⟩
end GlobalTheory.FrameLevel
