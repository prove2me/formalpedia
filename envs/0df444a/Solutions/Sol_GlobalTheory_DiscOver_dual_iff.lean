-- Prove2me | solution 1 for GlobalTheory.DiscOver.dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:20.085167+00:00
-- url     : https://prove2.me/submissions/05c1bce8-4a35-4c4b-af3c-529595b35f37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
import Theorems.Thm_GlobalTheory_DiscOver_sum_comb
import Theorems.Thm_GlobalTheory_DiscOver_hf_gram
import Theorems.Thm_GlobalTheory_DiscOver_mem_spanO

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
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.DiscOver
theorem _root_.solution (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (w : Fin m → Fin n → E) (hu : IsUnit (gram L Hm w).det) (x : Fin n → E) :
    (x ∈ Submodule.span E (Set.range w) ∧ ∀ a, hf L Hm x (w a) ∈ L.O) ↔
      x ∈ Submodule.span L.O (Set.range (comb w (gram L Hm w)⁻¹)) := by
  rw [mem_spanO, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨⟨t, rfl⟩, h⟩
    refine ⟨(gram L Hm w).mulVec t, fun a => ?_, ?_⟩
    · rw [← hf_gram]; exact h a
    · rw [sum_comb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · rintro ⟨s, hs, rfl⟩
    rw [sum_comb]
    refine ⟨⟨_, rfl⟩, fun a => ?_⟩
    rw [hf_gram, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    exact hs a
end GlobalTheory.DiscOver
