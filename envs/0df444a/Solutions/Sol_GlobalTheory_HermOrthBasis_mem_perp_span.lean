-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.mem_perp_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:29:10.555722+00:00
-- url     : https://prove2.me/submissions/2fcbf0d9-83d5-4e2d-8730-ccfb0f82dfd1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_right
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
theorem _root_.solution {m : ℕ} (x : Fin m → Fin n → E) (v : Fin n → E) :
    v ∈ perp L Hm (Submodule.span E (Set.range x)) ↔ ∀ a, hf L Hm v (x a) = 0 := by
  refine ⟨fun h a => h _ (Submodule.subset_span ⟨a, rfl⟩), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact h a
  | zero => simp [hf]
  | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
  | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
end GlobalTheory.HermOrthBasis
