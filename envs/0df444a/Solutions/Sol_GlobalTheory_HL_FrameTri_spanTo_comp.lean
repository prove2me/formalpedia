-- Prove2me | solution 1 for GlobalTheory.HL.FrameTri.spanTo_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:36.940116+00:00
-- url     : https://prove2.me/submissions/096a03fb-bffa-4fef-9d45-304a2af9ceae

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameTri_map_mem
import Theorems.Thm_GlobalTheory_HL_FrameTri_map_mem_iff
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTri
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include hg
namespace GlobalTheory.HL.FrameTri
theorem _root_.solution {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) :
    S.spanTo (fun b => n (g b)) j = S.spanTo g j := by
  have h : S.spanTo (fun b => n (g b)) j = (S.spanTo g j).map (n : S.V →ₗ[E] S.V) := by
    unfold Frames.spanTo
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [h]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem S g t hg hn j hx
  · intro hv
    refine ⟨n.symm v, ?_, by simp⟩
    apply (map_mem_iff S g t hg hn j _).1
    simpa using hv
end GlobalTheory.HL.FrameTri
