-- Prove2me | solution 1 for GlobalTheory.PDivGroup.toSpanSingleton_constGen_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:09.006347+00:00
-- url     : https://prove2.me/submissions/48bc6983-db5d-430d-9adb-439d81adc0eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
import Theorems.Thm_GlobalTheory_PDivGroup_exists_algHom_pi_eq_eval
import Theorems.Thm_GlobalTheory_PDivGroup_constHom_constGen
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_PDivGroup_constFun_mulP
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDivGroup_smul_constGen_pt
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


attribute [local simp] GlobalTheory.PDivGroup.constHom_constGen

set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]
variable [Nontrivial O]
namespace GlobalTheory.PDivGroup
theorem _root_.solution
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := fun t => by
  have h1 : ∀ n, ∃ k : ℕ, ∀ φ, t.pt n φ = constFun p O n φ k := fun n => by
    obtain ⟨k, hk⟩ := exists_algHom_pi_eq_eval hO
      ((t.pt n).comp ((constFun p O n).symm : (ZMod (p ^ n) → O) →ₐ[O] (const p O).A n))
    refine ⟨k.val, fun φ => ?_⟩
    rw [ZMod.natCast_zmod_val, ← hk (constFun p O n φ)]
    exact congrArg (t.pt n) ((constFun p O n).symm_apply_apply φ).symm
  choose k hk using h1
  have h2 : ∀ n, ((k (n + 1) : ℕ) : ZMod (p ^ n)) = k n := fun n => by
    have h := t.pt_mulP n ((constFun p O n).symm (Pi.single (k n : ZMod (p ^ n)) 1))
    rw [hk, hk, constFun_mulP, AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h
    exact zero_ne_one h
  have h3 : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, h2, sub_self]
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3),
    TateOver.ext (funext fun n => AlgHom.ext fun φ => ?_)⟩
  rw [LinearMap.toSpanSingleton_apply, smul_constGen_pt,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3 n, Int.cast_natCast, hk]
end GlobalTheory.PDivGroup
