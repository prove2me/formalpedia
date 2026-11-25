-- Prove2me | solution 1 for GlobalTheory.HermOrthBasis.isCompl_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:10:13.180041+00:00
-- url     : https://prove2.me/submissions/7b91e0d8-8bbd-4e65-95d0-81a540b5a028

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_sub_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_mem_perp_span
import Theorems.Thm_GlobalTheory_HermOrthBasis_gram_mulVec
import Theorems.Thm_GlobalTheory_HermOrthBasis_coeff_eq_zero
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
theorem _root_.solution {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) :
    IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) := by
  refine ⟨Submodule.disjoint_def.2 fun v hv hv' => ?_, codisjoint_iff.2 (eq_top_iff.2 fun v _ => ?_)⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
    rw [coeff_eq_zero L Hm x hx c ((mem_perp_span L Hm x _).1 hv')]
    simp
  · let c := (gramT L Hm x)⁻¹ *ᵥ fun a => hf L Hm v (x a)
    refine Submodule.mem_sup.2 ⟨∑ b, c b • x b,
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩, v - ∑ b, c b • x b,
      (mem_perp_span L Hm x _).2 fun a => ?_, by abel⟩
    rw [hf_sub_left, ← gram_mulVec, mulVec_mulVec, mul_nonsing_inv _ hx, one_mulVec, sub_self]
end GlobalTheory.HermOrthBasis
