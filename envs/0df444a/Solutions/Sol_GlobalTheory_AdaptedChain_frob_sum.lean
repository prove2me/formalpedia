-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.frob_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:25.385344+00:00
-- url     : https://prove2.me/submissions/ad38e53e-5818-4f6e-830c-d016c49ab6ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
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
namespace GlobalTheory.AdaptedChain
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i, V.Ge 0 (f i)) (k : ℕ) :
    V.Ge 1 ((∑ i ∈ s, f i) ^ (V.l ^ k) - ∑ i ∈ s, f i ^ (V.l ^ k)) := by
  induction s using Finset.induction_on with
  | empty => simpa [zero_pow (pow_pos V.l_prime.pos k).ne'] using VF.Ge.zero 1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : V.Ge 0 (∑ i ∈ s, f i) := VF.Ge.sum fun i _ => hf i
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨f a, hf a⟩ : intRing V) ⟨_, hs⟩ k
    have hr' := congrArg Subtype.val hr
    simp only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow, Subring.coe_natCast] at hr'
    have h1 : V.Ge 1 ((V.l : C) * (f a * (∑ i ∈ s, f i) * (r : C))) := by
      simpa using (((hf a).mul_int hs).mul_int r.2).l_mul
    have := h1.add ih
    convert this using 1
    rw [hr']; ring
end GlobalTheory.AdaptedChain
