-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.gram_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:52.419527+00:00
-- url     : https://prove2.me/submissions/a3f107da-ffd1-4a22-b06f-6eaa76d1e640

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_mem_perp_span
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
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HermOrthBasis
theorem _root_.solution {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det)
    (w : Fin n → E) (hw : w ∈ perp L Hm (Submodule.span E (Set.range x)))
    (hu : IsUnit (hf L Hm w w)) :
    IsUnit (gramT L Hm (Fin.cons w x : Fin (m + 1) → Fin n → E)).det := by
  have h := (mem_perp_span L Hm x w).1 hw
  rw [det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => by simp [gramT, h]),
    add_zero]
  have : (gramT L Hm (Fin.cons w x : Fin (m + 1) → Fin n → E)).submatrix
      (Fin.succAbove 0) Fin.succ = gramT L Hm x := by
    ext a b; simp [gramT]
  rw [this]
  simpa [gramT] using ⟨hu, hx⟩
end GlobalTheory.HermOrthBasis
