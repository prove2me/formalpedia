-- Prove2me | solution 1 for GlobalTheory.exists_continuousMultilinearMap_of_inner_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:02.522812+00:00
-- url     : https://prove2.me/submissions/c53c7772-61e4-497d-9659-3b6e3d4abe63

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsContinuousMultilinearMapOfInnerProd
import Theorems.Thm_GlobalTheory_eq_of_inner_eq_on_dense_span
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (t : (∀ v, H v) → E)
    (hin : ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range t) : Set E)) :
    ∃ m : ContinuousMultilinearMap ℂ H E, (∀ x, m x = t x) ∧ ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
  have hn : ∀ x, ‖t x‖ = ∏ v, ‖x v‖ := by
    intro x
    have h := hin x x
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖t x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
      rw [← Finset.prod_pow]
      exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _)
      two_ne_zero).1 h'
  have hu : ∀ [DecidableEq ι] (y x : ∀ v, H v) (i : ι) (a : H i),
      ⟪t y, t (Function.update x i a)⟫_ℂ =
        ⟪y i, a⟫_ℂ * ∏ j ∈ Finset.univ.erase i, ⟪y j, x j⟫_ℂ := by
    intro _ y x i a
    rw [hin, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  let m : MultilinearMap ℂ H E :=
    { toFun := t
      map_update_add' := by
        intro _ x i a b
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_add_right, hu, hu, hu, inner_add_right, add_mul]
      map_update_smul' := by
        intro _ x i c a
        refine eq_of_inner_eq_on_dense_span hd ?_
        rintro _ ⟨y, rfl⟩
        rw [inner_smul_right, hu, hu, inner_smul_right, mul_assoc] }
  refine ⟨m.mkContinuous 1 fun x => ?_, fun x => rfl, hn⟩
  rw [one_mul]
  exact (hn x).le
end GlobalTheory
