-- Prove2me | solution 1 for GlobalTheory.HL.FrameClass.trans_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:42.871703+00:00
-- url     : https://prove2.me/submissions/9cd7d776-90fe-46b4-812c-aa95128e1dda

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Theorems.Thm_GlobalTheory_HL_FrameClass_sum_comp
import Theorems.Thm_GlobalTheory_HL_FrameClass_intM_mul
import Theorems.Thm_GlobalTheory_HL_FrameClass_cong_iff
import Theorems.Thm_GlobalTheory_HL_FrameClass_tri_mul
import Theorems.Thm_GlobalTheory_HL_FrameClass_diag_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameClass
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.FrameClass
theorem _root_.solution {g g' : Fin (r + 1) → S.V} {p q : S.FrP} (hp : p ∈ S.frameCls g g')
    (hq : q ∈ S.frameCls p.1 p.2) : q ∈ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨B, B', hB, hB', kt, kd, kc, k1, k2⟩ := hq
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨D, hD, kc⟩ := (cong_iff _ _ _).1 kc
  refine ⟨A * B, A' * B', intM_mul hA hB, intM_mul hA' hB', fun i j h => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_,
    sum_comp A B g p.1 q.1 h1 k1, sum_comp A' B' g' p.2 q.2 h2 k2⟩
  · exact tri_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1) i j h
  · exact tri_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2) i j h
  · rw [diag_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1), (hd i).1, (kd i).1, one_mul]
  · rw [diag_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2), (hd i).2, (kd i).2, one_mul]
  · refine (cong_iff _ _ _).2 ⟨C * B' + A * D, fun i j => ?_, ?_⟩
    · exact add_mem (intM_mul hC hB' i j) (intM_mul hA hD i j)
    · rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, ← kc, sub_mul, mul_sub]; abel
end GlobalTheory.HL.FrameClass
