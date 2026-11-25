-- Prove2me | solution 1 for GlobalTheory.HL.ContModel.mem_hermLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:44.762976+00:00
-- url     : https://prove2.me/submissions/43eaad1e-3997-4e19-87f3-2f3c270f99b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.ContModel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.ContModel
theorem _root_.solution (L : LocE F E) (m : ℕ) (X : Matrix (Fin m) (Fin m) E) :
    X ∈ hermLat L m ↔ IsHerm L X ∧ IsIntM L X := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure h⟩
  induction h using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨by ext i j; simp [cT], fun i j => L.O.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i j => L.O.add_mem (hx.2 i j) (hy.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    have h2 := congrFun (congrFun hy.1 i) j
    simp only [cT] at h1 h2
    simp [cT, h1, h2]
  | neg x _ hx =>
    refine ⟨?_, fun i j => L.O.neg_mem (hx.2 i j)⟩
    ext i j
    have h1 := congrFun (congrFun hx.1 i) j
    simp only [cT] at h1
    simp [cT, h1]
end GlobalTheory.HL.ContModel
