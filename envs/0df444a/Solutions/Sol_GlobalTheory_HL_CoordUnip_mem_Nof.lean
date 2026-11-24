-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.mem_Nof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:27.597125+00:00
-- url     : https://prove2.me/submissions/ee0fdd09-1a63-4da0-af22-c759e9096aa6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_flag_iff
import Theorems.Thm_GlobalTheory_HL_CoordUnip_spanTo_zero
import Theorems.Thm_GlobalTheory_HL_CoordUnip_spanTo_mono
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
namespace GlobalTheory.HL.CoordUnip
theorem _root_.solution (S : Frames M.L r k) (f : Fin (r + 1) → S.V) (g : S.GLV) :
    g ∈ S.Nof f ↔ (∀ x y, S.h (g x) (g y) = S.h x y) ∧
      (∀ j, j < r → ∀ v ∈ S.spanTo f (j + 1), g v - v ∈ S.spanTo f j) ∧
      ∀ v ∈ perp M.L S.Hm (S.spanTo f r), g v - v ∈ S.spanTo f r := by
  have mu : ∀ (A B : Submodule E S.V) (g : S.GLV),
      g ∈ unipOn A B ↔ (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B := fun _ _ _ => Iff.rfl
  have mi : g ∈ isomG M.L S.Hm ↔ ∀ x y, S.h (g x) (g y) = S.h x y := Iff.rfl
  have mp : ∀ (Y : Submodule E S.V) (v : S.V), v ∈ perp M.L S.Hm Y ↔ ∀ y ∈ Y, S.h v y = 0 :=
    fun _ _ => Iff.rfl
  simp only [Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, mu, mi]
  constructor
  · rintro ⟨⟨hiso, hu⟩, hp⟩
    exact ⟨hiso, fun j hj v hv => (hu ⟨j, hj⟩).2 v hv, hp.2⟩
  · rintro ⟨hiso, hu, hp⟩
    have hfl := flag_iff (S.spanTo f) (spanTo_zero S f) (spanTo_mono S f) r g hu
    refine ⟨⟨hiso, fun j => ⟨hfl (j + 1) j.isLt, hu j j.isLt⟩⟩, ?_, hp⟩
    have hX := hfl r le_rfl
    intro v
    rw [mp, mp]
    constructor
    · intro hv y hy
      rw [← hiso v y]
      exact hv (g y) ((hX y).2 hy)
    · intro hv y hy
      have hy' : g.symm y ∈ S.spanTo f r := (hX _).1 (by simpa using hy)
      have := hv (g.symm y) hy'
      rw [← hiso v (g.symm y), LinearEquiv.apply_symm_apply] at this
      exact this
end GlobalTheory.HL.CoordUnip
