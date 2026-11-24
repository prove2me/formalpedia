-- Prove2me | solution 1 for GlobalTheory.CharInvForm.kills_linear_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:03.342346+00:00
-- url     : https://prove2.me/submissions/ecff4d36-7c0a-49a1-a416-52fcdbfcf989

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslationInvariantFunctionalLinearZero
import Theorems.Thm_GlobalTheory_CharInvForm_temperate_exp_I
import Theorems.Thm_GlobalTheory_T_identity_as_sum_exp_minus_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CharInvForm
namespace GlobalTheory.CharInvForm
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  intro V _ _ _ T hT L h g hg
  obtain ⟨n, a, A, hA, hdiv⟩ := GlobalTheory.T.identity_as_sum_exp_minus_one
  have hAL : ∀ j, Function.HasTemperateGrowth (fun x : V => A j (L x)) := fun j =>
    (hA j).comp L.hasTemperateGrowth
  have hE : ∀ j, Function.HasTemperateGrowth
      (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) := fun j =>
    temperate_exp_I.comp (a j • L).hasTemperateGrowth
  let k : Fin n → SchwartzMap V ℂ := fun j => SchwartzMap.smulLeftCLM ℂ (fun x : V => A j (L x)) h
  let f' : Fin n → SchwartzMap V ℂ := fun j =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) (k j)
  have hk : ∀ j x, k j x = A j (L x) * h x := fun j x => by
    simp only [k]
    rw [SchwartzMap.smulLeftCLM_apply_apply (hAL j), smul_eq_mul]
  have hf : ∀ j x, f' j x = Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ)) * k j x := fun j x => by
    simp only [f']
    rw [SchwartzMap.smulLeftCLM_apply_apply (hE j), smul_eq_mul]
  have hsum : g = ∑ j, (f' j - k j) := by
    ext x
    rw [SchwartzMap.sum_apply, hg x]
    conv_lhs => rw [hdiv (L x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.sub_apply, hf, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sub, hT (a j • L) (k j) (f' j) (hf j), sub_self]
end GlobalTheory.CharInvForm
