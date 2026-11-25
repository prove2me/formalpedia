-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.stepA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:15.159641+00:00
-- url     : https://prove2.me/submissions/3b130ae0-994a-441e-9e1d-de007c52ffe4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_elim_frob
import Theorems.Thm_GlobalTheory_AdaptedChain_change
import Theorems.Thm_GlobalTheory_AdaptedChain_modify
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_bound0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_pure
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L) :
    ∃ (S' : Sys X) (Q' : Finset I), Q' ⊆ Q ∧
      Q.card ≤ Q'.card + (Finset.univ.filter fun k => X.ty (Sum.inl k) = b + 1).card ∧
      (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      ∀ c ∈ Q', ∀ k, S'.cur c 1 (Sum.inl k) = 0 := by
  obtain ⟨P, Q', hP, h1, h2, h3⟩ := elim_frob (V := V) Q (fun x k => (V.l : C) * S.cur x 1 (Sum.inl k))
    (fun x k => by simpa using (X.bound0 1 _ (S.mem x) (Sum.inl k)).l_mul)
    (Finset.univ.filter fun k => X.ty (Sum.inl k) = b + 1) 1
  obtain ⟨S1, a1, a2, a3⟩ := change S b Q hQ L hL hQL P hP
  obtain ⟨S2, b1, b2, b3⟩ := modify S1 Q' (by
    intro c hc k
    by_cases hk : X.ty (Sum.inl k) = b + 1
    · have := h3 c hc k (by simpa using hk)
      have e : ∑ x, P c x ^ V.l ^ 1 * ((V.l : C) * S.cur x 1 (Sum.inl k)) =
          (V.l : C) * S1.cur c 1 (Sum.inl k) := by
        rw [a3, Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [e] at this
      simpa using this.of_l_mul
    · rw [S1.pure c 1 _ (by rw [hQ c (h1 hc)]; simpa using hk)]
      exact VF.Ge.zero 0)
  refine ⟨S2, Q', h1, h2, fun c hc => ?_, fun c hc => ?_, b3⟩
  · rw [b1 c (fun hh => hc (h1 hh)), a1 c hc]
  · rw [b2]; exact a2 c hc
end GlobalTheory.AdaptedChain
