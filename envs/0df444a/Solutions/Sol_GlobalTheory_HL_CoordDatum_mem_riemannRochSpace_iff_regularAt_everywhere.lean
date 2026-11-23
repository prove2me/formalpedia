-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:05.276818+00:00
-- url     : https://prove2.me/submissions/85567573-b879-496e-81ae-b817bd666c0f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_fix_span

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordDatum
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordDatum
theorem _root_.solution (g : S.GLV) : g ∈ S.H0 ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
    ∀ b, g (S.f b) = S.f b ∧ g (S.f' b) = S.f' b := by
  unfold Frames.H0
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, -, h2⟩
    refine ⟨h1, fun b => ⟨?_, ?_⟩⟩
    · have := h2 (S.f b) (Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩))
      exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
    · have := h2 (S.f' b) (Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩))
      exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have hfix : ∀ v ∈ S.ME, g v = v := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add, fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).1) a ha,
        fix_span g _ (by rintro _ ⟨i, -, rfl⟩; exact (h2 i).2) b hb]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rwa [hfix v hv]⟩, fun v hv => ?_⟩
    · rwa [← g.injective (hfix _ hv)]
    · rw [hfix v hv, sub_self]; exact Submodule.zero_mem _
end GlobalTheory.HL.CoordDatum
