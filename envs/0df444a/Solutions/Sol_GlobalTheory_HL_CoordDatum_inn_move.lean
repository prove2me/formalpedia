-- Prove2me | solution 1 for GlobalTheory.HL.CoordDatum.inn_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:07.785224+00:00
-- url     : https://prove2.me/submissions/2fe20b98-b5f3-4424-8107-67b0b8832c55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramePairCoordinatesTransportInnerData
import Theorems.Thm_GlobalTheory_HL_CoordDatum_grp_apply
import Theorems.Thm_GlobalTheory_HL_CoordDatum_mem_inn
import Theorems.Thm_P2M_GlobalTheory_HL_CoordDatum_mem_inn__53c3259fe203
import Theorems.Thm_GlobalTheory_HL_CoordDatum_smul_sub_iff

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
theorem _root_.solution (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V)
    (hp : ∀ v, g v ∈ H.perp (H.X f) ↔ v ∈ H.perp (H.X f)) (L L' : Submodule M.L.O (H.Wb f)) :
    (∀ x y : ↥(H.perp (H.X f)), (y : V) = g x → (H.mkW f x ∈ L ↔ H.mkW f y ∈ L')) ↔
      c.grp g • c.inn f L = c.inn f L' := by
  rw [smul_sub_iff]
  constructor
  · intro h v
    obtain ⟨v, rfl⟩ := c.e.surjective v
    rw [grp_apply, mem_inn, mem_inn]
    exact ⟨fun ⟨hv, h1⟩ => ⟨(hp v).2 hv, (h ⟨v, hv⟩ ⟨_, (hp v).2 hv⟩ rfl).1 h1⟩,
      fun ⟨hv, h1⟩ => ⟨(hp v).1 hv, (h ⟨v, (hp v).1 hv⟩ ⟨_, hv⟩ rfl).2 h1⟩⟩
  · intro h x y hxy
    rw [← mem_inn' c, ← mem_inn' c, h, grp_apply, hxy]
end GlobalTheory.HL.CoordDatum
