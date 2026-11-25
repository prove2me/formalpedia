-- Prove2me | solution 1 for GlobalTheory.HL.FrameTri.coeff_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:41:27.090615+00:00
-- url     : https://prove2.me/submissions/5fdc544e-2164-473b-90bc-23917e79528a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
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
namespace GlobalTheory.HL.FrameTri
theorem _root_.solution (g : Fin (r + 1) → S.V) {j : ℕ} {v : S.V} (hv : v ∈ S.spanTo g j) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), j ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun a ha => ?_, ?_⟩
    · have hi' : (i : ℕ) < j := hi
      have : a ≠ i := by rintro rfl; omega
      simp [this]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨a • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩
end GlobalTheory.HL.FrameTri
