-- Prove2me | solution 1 for GlobalTheory.FlagEich.prod_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:39:45.933104+00:00
-- url     : https://prove2.me/submissions/7948fad9-391b-45ef-b39e-f0aab49d227e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
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
namespace GlobalTheory.FlagEich
theorem _root_.solution {G : Type*} [Group G] : ∀ {r : ℕ} (f : Fin r → G) (M : Fin r) (x : G),
    (∀ i, i ≤ M → f i = 1) → (List.ofFn (Function.update f M x)).prod = x * (List.ofFn f).prod := by
  intro r
  induction r with
  | zero => intro f M; exact M.elim0
  | succ r ih =>
    intro f M x hf
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hf0 : f 0 = 1 := hf 0 (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
    cases M using Fin.cases with
    | zero =>
      have : (fun i : Fin r => Function.update f 0 x i.succ) = fun i => f i.succ := by
        funext i; rw [Function.update_apply, if_neg (Fin.succ_ne_zero i)]
      rw [this, hf0]; simp
    | succ M' =>
      have : (fun i : Fin r => Function.update f M'.succ x i.succ) =
          Function.update (fun i => f i.succ) M' x := by
        funext i; simp only [Function.update_apply, Fin.succ_inj]
      rw [this, ih (fun i => f i.succ) M' x (fun i hi => hf _ (Fin.succ_le_succ_iff.mpr hi))]
      have h0 : Function.update f M'.succ x 0 = 1 := by
        rw [Function.update_apply, if_neg (Fin.succ_ne_zero M').symm]; exact hf0
      rw [h0, hf0]; simp
end GlobalTheory.FlagEich
