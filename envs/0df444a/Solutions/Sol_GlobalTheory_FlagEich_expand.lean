-- Prove2me | solution 1 for GlobalTheory.FlagEich.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:21.696961+00:00
-- url     : https://prove2.me/submissions/138cee75-5d01-43d5-8531-d264146cd606

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
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : x = ∑ a : Fin r, hf L S.Hm x (gs a) • g a.castSucc := by
  unfold Frames.spanTo at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, rfl⟩ := mem_gen S le_rfl hz
    simp [H1, Fin.castSucc_inj, ite_smul]
  | zero => simp [hf]
  | add a b _ _ ha hb =>
    rw [Finset.sum_congr rfl (fun i _ => by rw [hf_add_l, add_smul]), Finset.sum_add_distrib, ← ha, ← hb]
  | smul c a _ ha =>
    rw [Finset.sum_congr rfl (fun i _ => by rw [hf_smul_l, mul_smul]), ← Finset.smul_sum, ← ha]
end GlobalTheory.FlagEich
