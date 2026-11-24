-- Prove2me | solution 1 for GlobalTheory.HL.CoordMass.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:46.035825+00:00
-- url     : https://prove2.me/submissions/04c7ebef-6c1a-4e7d-af0d-dc370f16e3a6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportUnitaryMass
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordMass
open GlobalTheory.HL.Eichler GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.CoordMass
theorem _root_.solution (g : S.GLV) : g ∈ S.H0 ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
    ∀ b, g (S.f b) = S.f b ∧ g (S.f' b) = S.f' b := by
  constructor
  · rintro ⟨h1, -, h2⟩
    refine ⟨h1, fun b => ⟨?_, ?_⟩⟩
    · exact sub_eq_zero.1 (h2 _ (Submodule.mem_sup_left (FrameOnto.mem_spanTo S _ b.2)))
    · exact sub_eq_zero.1 (h2 _ (Submodule.mem_sup_right (FrameOnto.mem_spanTo S _ b.2)))
  · rintro ⟨h1, h2⟩
    have h3 : ∀ v ∈ S.ME, g v = v := by
      have : S.ME ≤ LinearMap.eqLocus (g : S.V →ₗ[E] S.V) LinearMap.id := by
        refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
        · rintro _ ⟨i, -, rfl⟩; exact (h2 i).1
        · rintro _ ⟨i, -, rfl⟩; exact (h2 i).2
      exact fun v hv => this hv
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
    · rwa [← g.injective (h3 _ hv)]
    · rwa [h3 v hv]
    · rw [h3 v hv, sub_self]; exact zero_mem _
end GlobalTheory.HL.CoordMass
