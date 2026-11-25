-- Prove2me | solution 1 for GlobalTheory.FramePsi.hf_span_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:32.540466+00:00
-- url     : https://prove2.me/submissions/f6488e2f-3980-4740-9664-4ab9561f4363

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
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
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FramePsi
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (s : Set (Fin n → E)) (hs : ∀ y ∈ s, hf L Hm x y = 0) :
    ∀ y ∈ Submodule.span E s, hf L Hm x y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => exact hs y h
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    have : hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
      simp [hf, mul_add, Finset.sum_add_distrib]
    rw [this, ha, hb, add_zero]
  | smul c a _ ha =>
    have : hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
      simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha, mul_zero]
end GlobalTheory.FramePsi
