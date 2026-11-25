-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.symm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:18.181772+00:00
-- url     : https://prove2.me/submissions/d3401cf8-1920-4f2b-9a96-8d1e80c6b826

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Theorems.Thm_GlobalTheory_HL_FrameClass_exists_inv
import Theorems.Thm_GlobalTheory_HL_FrameClass_sum_comp
import Theorems.Thm_GlobalTheory_HL_FrameClass_intM_mul
import Theorems.Thm_GlobalTheory_HL_FrameClass_cong_iff
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    (g, g') ∈ S.frameCls p.1 p.2 := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨B, hB, bt, bd, hAB, hBA⟩ := exists_inv L.O A hA (fun i j h => (ht i j h).1) (fun i => (hd i).1)
  obtain ⟨B', hB', bt', bd', hAB', hBA'⟩ :=
    exists_inv L.O A' hA' (fun i j h => (ht i j h).2) (fun i => (hd i).2)
  refine ⟨B, B', hB, hB', fun i j h => ⟨bt i j h, bt' i j h⟩, fun i => ⟨bd i, bd' i⟩, ?_, fun j => ?_,
    fun j => ?_⟩
  · refine (cong_iff _ _ _).2 ⟨-(B' * C * B), fun i j => ?_, ?_⟩
    · exact neg_mem (intM_mul (intM_mul hB' hC) hB i j)
    · rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, mul_sub, sub_mul, hBA', mul_assoc, hAB]
      simp
  · have := sum_comp A B g p.1 (fun j => ∑ i, B i j • p.1 i) h1 (fun _ => rfl) j
    rw [this, hAB]; simp [Matrix.one_apply]
  · have := sum_comp A' B' g' p.2 (fun j => ∑ i, B' i j • p.2 i) h2 (fun _ => rfl) j
    rw [this, hAB']; simp [Matrix.one_apply]
end GlobalTheory.HL.FrameClass
