-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.mem_perp_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:32.674746+00:00
-- url     : https://prove2.me/submissions/60334fd6-2c07-49b6-8f9d-a94547b4f62e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_hf_add_right
import Theorems.Thm_GlobalTheory_HL_Model_hf_smul_right
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (s : Set (Fin n → E))
    (x : Fin n → E) : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ s, hf L H x y = 0 := by
  have hmem : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ Submodule.span E s, hf L H x y = 0 := Iff.rfl
  rw [hmem]
  constructor
  · intro hx y hy
    exact hx y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => simp [hf]
    | add u v _ _ hu hv => rw [hf_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_right, hu, mul_zero]
end GlobalTheory.HL.Inhab
