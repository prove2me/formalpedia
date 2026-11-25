-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:38.881131+00:00
-- url     : https://prove2.me/submissions/308cf3b6-aaf8-484d-8528-25816e7fe348

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_be_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_pure


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
theorem _root_.solution (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (P : Matrix I I C) (hP : admitted V Q P) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      ∀ c i n, S'.cur c i n = ∑ x, P c x ^ (V.l ^ i) * S.cur x i n := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hty : ∀ c x, X.ty (Sum.inl x) ≠ X.ty (Sum.inl c) → P c x = 0 := by
    intro c x h
    by_cases hc : c ∈ Q
    · exact hP.2.2.2 c hc x (fun hx => h (by rw [hQ c hc, hQ x hx]))
    · rw [hP.2.2.1 c hc x, if_neg (fun hh : x = c => h (by rw [hh]))]
  have hval : ∀ c i n, (∑ x, teich V.l (P c x) (S.cur x)) i n = ∑ x, P c x ^ (V.l ^ i) * S.cur x i n := by
    intro c i n; simp [Finset.sum_apply, teich]
  refine ⟨⟨fun c k => (P * S.U) c k, fun c => ∑ x, teich V.l (P c x) (S.cur x), fun c => ⟨?_, ?_, ?_⟩, ?_⟩,
    fun c hc => ?_, fun c hc => ?_, hval⟩
  · exact X.Ty.sum_mem fun x _ => X.teich_mem _ (hP.1 _ _) _ (S.mem x)
  · funext n
    rw [hval]
    cases n with
    | inl k => simp [S.cur_zero_inl, Matrix.mul_apply, Sys.U]
    | inr j => simp [S.be_zero]
  · intro i n hn
    rw [hval]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : X.ty (Sum.inl x) = X.ty (Sum.inl c)
    · rw [S.pure x i n (by rw [hx]; exact hn), mul_zero]
    · rw [hty c x hx, zero_pow (lpos i), zero_mul]
  · show V.v (P * S.U).det = 0
    rw [Matrix.det_mul, V.v.map_mul, hP.2.1, zero_add]
    exact S.unimod
  · funext i n
    show (∑ x, teich V.l (P c x) (S.cur x)) i n = _
    rw [hval]
    simp [hP.2.2.1 c hc, zero_pow (lpos i)]
  · have : (fun k => (P * S.U) c k) = ∑ x, P c x • S.tan x := by
      funext k; simp [Matrix.mul_apply, Sys.U, Finset.sum_apply]
    show (fun k => (P * S.U) c k) ∈ L
    rw [this]
    refine L.sum_mem fun x _ => ?_
    by_cases hx : x ∈ Q
    · exact hL _ (hP.1 _ _) _ (hQL x hx)
    · rw [hP.2.2.2 c hc x hx, zero_smul]; exact L.zero_mem
end GlobalTheory.AdaptedChain
