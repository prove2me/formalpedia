-- Prove2me | solution 1 for GlobalTheory.FlagEich.pairR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:04.358354+00:00
-- url     : https://prove2.me/submissions/7c411ccd-8254-4bbb-bb6f-e5691a04be8a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_mem_gen
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_add_r
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_smul_r
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V} {j : ℕ} (hj : j ≤ r) (x : S.V)
    (h : ∀ c : Fin r, (c : ℕ) < j → hf L S.Hm x (g c.castSucc) = 0) :
    ∀ y ∈ S.spanTo g j, hf L S.Hm x y = 0 := by
  intro y hy
  unfold Frames.spanTo at hy
  induction hy using Submodule.span_induction with
  | mem z hz => obtain ⟨c, hc, rfl⟩ := mem_gen S hj hz; exact h c hc
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [hf_add_r, ha, hb, add_zero]
  | smul c a _ ha => rw [hf_smul_r, ha, mul_zero]
end GlobalTheory.FlagEich
