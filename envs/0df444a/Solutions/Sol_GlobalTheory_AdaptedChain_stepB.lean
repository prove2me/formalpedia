-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.stepB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:17.032634+00:00
-- url     : https://prove2.me/submissions/416f0af8-ef99-4579-bd75-9b4bb0c81a15

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_elim_frob
import Theorems.Thm_GlobalTheory_AdaptedChain_tan_pure
import Theorems.Thm_GlobalTheory_AdaptedChain_change
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_spec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_pure
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_inv_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution [IsAlgClosed C] (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (hG : ∀ c ∈ Q, ∀ k, S.cur c 1 (Sum.inl k) = 0) (E : Finset I) :
    ∃ (S' : Sys X) (Q' : Finset I), Q' ⊆ Q ∧ Q.card ≤ Q'.card + E.card ∧
      (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      (∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      ∀ c ∈ Q', ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, g e ≠ 0 → X.ty (Sum.inl e) = b + 2 ∧ e ∉ E) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  set w : I → I → C := fun x e => if x ∈ Q then S.co (fun n => (V.l : C) * S.cur x 2 n) e else 0 with hw
  have hwi : ∀ x e, V.Ge 0 (w x e) := by
    intro x e
    simp only [hw]
    split_ifs with hx
    · refine S.co_int (fun n => ?_) e
      have hg : X.Good _ _ (S.cur x) := ⟨S.curve x, hG x hx⟩
      simpa using (hg.bound 0 n).l_mul
    · exact VF.Ge.zero 0
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim_frob (V := V) Q w hwi E 2
  obtain ⟨S1, a1, a2, a3⟩ := change S b Q hQ L hL hQL P hP
  refine ⟨S1, Q', h1, h2, a1, a2, fun c hc k => ?_, fun c hc => ?_⟩
  · rw [a3]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x ∈ Q
    · rw [hG x hx, mul_zero]
    · rw [hP.2.2.2 c hc x hx, zero_pow (lpos 1), zero_mul]
  set W : I → C := fun e => ∑ x, P c x ^ V.l ^ 2 * w x e with hW
  have hWi : ∀ e, V.Ge 0 (W e) := fun e => VF.Ge.sum fun x _ => ((hP.1 _ _).pow _).mul_int (hwi _ _)
  have hmain : ∀ k, (V.l : C) * S1.cur c 2 (Sum.inl k) = ∑ e, W e * S.tan e k := by
    intro k
    rw [a3, Finset.mul_sum]
    simp only [hW, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ Q
    · have := S.co_spec (fun n => (V.l : C) * S.cur x 2 n) k
      simp only [mul_assoc, ← Finset.mul_sum, hw, if_pos hx]
      rw [show ∑ e, S.co (fun n => (V.l : C) * S.cur x 2 n) e * S.tan e k =
        (V.l : C) * S.cur x 2 (Sum.inl k) from this]
      ring
    · simp [hP.2.2.2 c (h1 hc) x hx, zero_pow (lpos 2)]
  refine ⟨fun e => if X.ty (Sum.inl e) = b + 2 ∧ e ∉ E then W e else 0,
    fun k => if X.ty (Sum.inl k) = b + 2 then (V.l : C)⁻¹ * ∑ e ∈ E, W e * S.tan e k else 0,
    fun e => ?_, fun k => ?_, fun e he => ?_, fun k => ?_⟩
  · dsimp only; split_ifs
    · exact hWi e
    · exact VF.Ge.zero 0
  · dsimp only; split_ifs
    · have : V.Ge 1 (∑ e ∈ E, W e * S.tan e k) := VF.Ge.sum fun e he => by
        rw [mul_comm]; exact (S.U_int e k).mul_int (h3 c hc e he)
      simpa using this.l_inv_mul
    · exact VF.Ge.zero 0
  · by_contra hh; exact he (if_neg hh)
  · dsimp only
    by_cases hk : X.ty (Sum.inl k) = b + 2
    · rw [if_pos hk, mul_inv_cancel_left₀ VF.l_ne_zero, hmain, ← Finset.sum_ite_mem_eq E,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : e ∈ E
      · simp [he]
      · by_cases he' : X.ty (Sum.inl e) = b + 2
        · simp [he, he']
        · simp [he, he', tan_pure S (c := e) (k := k) (by rw [hk]; exact Ne.symm he')]
    · rw [if_neg hk, S1.pure c 2 _ (by rw [hQ c (h1 hc)]; simpa using hk), mul_zero, add_zero]
      symm
      refine Finset.sum_eq_zero fun e _ => ?_
      split_ifs with he
      · rw [tan_pure S (by rw [he.1]; exact hk), mul_zero]
      · rw [zero_mul]
end GlobalTheory.AdaptedChain
