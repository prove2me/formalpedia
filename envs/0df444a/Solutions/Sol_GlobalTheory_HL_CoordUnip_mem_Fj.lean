-- Prove2me | solution 1 for GlobalTheory.HL.CoordUnip.mem_Fj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:49.754667+00:00
-- url     : https://prove2.me/submissions/9dfb8c07-513d-42a7-902a-4d86fb7c9cb9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
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
theorem _root_.solution (hf : ∀ a, f a = e (Fr.f a)) (j : ℕ) (hj : j ≤ r) (x : V) :
    x ∈ Fr.Fj j ↔ e x ∈ S.spanTo f j := by
  have hs : S.spanTo f j = (Fr.Fj j).map (e : V →ₗ[E] S.V) := by
    unfold Frames.spanTo LocNG.FrameD.Fj
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Fr.e ⟨i, by omega⟩, ⟨⟨i, by omega⟩, hi, rfl⟩, ?_⟩
      rw [hf]
      rfl
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a.castSucc, by simpa using ha, by rw [hf]; rfl⟩
  rw [hs, Submodule.mem_map_equiv]
  simp
end GlobalTheory.HL.CoordUnip
