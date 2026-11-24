-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:20:02.236265+00:00
-- url     : https://prove2.me/submissions/13b28f6e-8805-4874-8dc7-a6b9eedf497a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_NSet
import Theorems.Thm_GlobalTheory_HL_CoordUnip_grp_apply

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V) (hf : ∀ a, f a = c.e (Fr.f a))
    (g : V ≃ₗ[E] V) : g ∈ Fr.N ↔ c.grp g ∈ S.Nof f := by
  have hset : Fr.NSet = {g | c.grp g ∈ S.Nof f} := by
    ext g
    exact mem_NSet S c.e Fr f c.h_eq hf g (c.grp g) (grp_apply c g)
  have hsub : Fr.N = (S.Nof f).comap c.grp.toMonoidHom := by
    rw [LocNG.FrameD.N, hset]
    exact Subgroup.closure_eq ((S.Nof f).comap c.grp.toMonoidHom)
  rw [hsub]
  rfl
end GlobalTheory.HL.CoordUnip
