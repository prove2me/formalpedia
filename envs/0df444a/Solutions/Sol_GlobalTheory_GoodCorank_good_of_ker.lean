-- Prove2me | solution 1 for GlobalTheory.GoodCorank.good_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:12.287166+00:00
-- url     : https://prove2.me/submissions/7db05a6d-7953-4508-9f57-d18122930038

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
import Theorems.Thm_GlobalTheory_GoodCorank_good_of_int
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_bound0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_std_spec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_GlobalTheory_AdaptedChain_frob_sum
import Theorems.Thm_GlobalTheory_AdaptedChain_int_of_pow


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
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]
namespace GlobalTheory.GoodCorank
theorem _root_.solution (G : Cart V d I J) {a : ZMod d} (r : I → I → C)
    (hr : ∀ b c, r b c ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b)) {u : I → C} (hu : ∀ c, V.Ge 0 (u c))
    (hp : ∀ c, G.ty (Sum.inl c) ≠ a → u c = 0)
    (hk : ∀ b, G.ty (Sum.inl b) = a + 1 → ∑ c, u c * r b c = 0) : ∃ x, G.Good a u x := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hy : G.IsCurve a u (∑ c, teich V.l (u c) (G.std c)) := by
    refine ⟨G.Ty.sum_mem fun c _ => G.teich_mem _ (hu c) _ (G.std_spec c).1, ?_, fun i n hn => ?_⟩
    · funext n
      have : ∀ b, G.std b 0 n = Sum.elim (Pi.single b 1) 0 n := fun b => by rw [(G.std_spec b).2.1]
      simp only [Finset.sum_apply, teich, this, pow_zero, pow_one]
      cases n with
      | inl c => simp [Pi.single_apply]
      | inr j => simp
    · simp only [Finset.sum_apply, teich]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : G.ty (Sum.inl c) = a
      · rw [(G.std_spec c).2.2 i n (by rwa [hc]), mul_zero]
      · rw [hp c hc, zero_pow (lpos i), zero_mul]
  refine good_of_int G hy fun b => ?_
  by_cases hb : G.ty (Sum.inl b) = a + 1
  · have hrint : ∀ c, V.Ge 0 (r b c) := fun c => by
      refine GlobalTheory.AdaptedChain.int_of_pow V.l_prime.ne_zero ?_
      rw [hr]
      simpa using (G.bound0 1 _ (G.std_spec c).1 (Sum.inl b)).l_mul
    have hf := (GlobalTheory.AdaptedChain.frob_sum Finset.univ (fun c => u c * r b c)
      (fun c => (hu c).mul_int (hrint c)) 1).neg
    rw [hk b hb, zero_pow (lpos 1), zero_sub, neg_neg] at hf
    have e : ∑ c, (u c * r b c) ^ V.l ^ 1 =
        (V.l : C) * (∑ c, teich V.l (u c) (G.std c)) 1 (Sum.inl b) := by
      simp only [Finset.sum_apply, teich, pow_one, mul_pow, hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at hf
    simpa using hf.of_l_mul
  · rw [hy.2.2 1 _ (by simpa using hb)]
    exact VF.Ge.zero 0
end GlobalTheory.GoodCorank
