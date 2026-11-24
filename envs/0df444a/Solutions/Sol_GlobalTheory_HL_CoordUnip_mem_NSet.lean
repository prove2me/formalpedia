-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.mem_NSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:59:49.726903+00:00
-- url     : https://prove2.me/submissions/6c491be7-c59f-4cd2-8c86-0b3092559d20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_spanTo_zero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_Nof
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_Fj
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_X
import Theorems.Thm_GlobalTheory_HL_CoordUnip_mem_perp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordUnip
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (Fr : LocNG.FrameD H r) (f : Fin (r + 1) → S.V)
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution (he : ∀ x y, S.h (e x) (e y) = H.h x y) (hf : ∀ a, f a = e (Fr.f a))
    (g : V ≃ₗ[E] V) (g' : S.GLV) (hg : ∀ v, g' (e v) = e (g v)) :
    g ∈ Fr.NSet ↔ g' ∈ S.Nof f := by
  rw [mem_Nof]
  simp only [LocNG.FrameD.NSet, Set.mem_ofPred_eq, LocNG.IsUnitary]
  have hgS : ∀ v w, S.h (g' (e v)) (g' (e w)) = H.h (g v) (g w) := fun v w => by rw [hg, hg, he]
  have hsub : ∀ v, g' (e v) - e v = e (g v - v) := fun v => by rw [hg, map_sub]
  constructor
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      obtain ⟨v, rfl⟩ := e.surjective x
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [hgS, he]
      exact hu v w
    · intro j hj x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_Fj S e Fr f hf j (by omega)]
      have := hfl (j + 1) (by omega) v ((mem_Fj S e Fr f hf (j + 1) (by omega) v).2 hx)
      simpa using this
    · intro x hx
      obtain ⟨v, rfl⟩ := e.surjective x
      rw [hsub, ← mem_X S e Fr f hf]
      exact hp v ((mem_perp S e Fr f he hf v).2 hx)
  · rintro ⟨hu, hfl, hp⟩
    refine ⟨fun v w => ?_, ?_, ?_⟩
    · rw [← hgS, ← he]
      exact hu _ _
    · intro j hj v hv
      cases j with
      | zero =>
        have h0 := (mem_Fj S e Fr f hf 0 (Nat.zero_le _) v).1 hv
        rw [spanTo_zero, Submodule.mem_bot] at h0
        have hv0 : v = 0 := e.injective (by rw [h0, map_zero])
        subst hv0
        simp
      | succ i =>
        rw [Nat.add_sub_cancel, mem_Fj S e Fr f hf i (by omega), ← hsub]
        exact hfl i (by omega) (e v) ((mem_Fj S e Fr f hf (i + 1) hj v).1 hv)
    · intro v hv
      rw [mem_X S e Fr f hf, ← hsub]
      exact hp (e v) ((mem_perp S e Fr f he hf v).1 hv)
end GlobalTheory.HL.CoordUnip
