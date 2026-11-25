-- Prove2me | solution 1 for GlobalTheory.PDivGroup.exists_algHom_pi_eq_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:45:32.660097+00:00
-- url     : https://prove2.me/submissions/456cd702-8d8b-4c52-8e48-ceae61f45a32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
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



set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
namespace GlobalTheory.PDivGroup
theorem _root_.solution {O ι : Type*} [CommRing O] [Nontrivial O] [Finite ι]
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (ι → O) →ₐ[O] O) :
    ∃ k, ∀ g, f g = g k := by
  classical
  have := Fintype.ofFinite ι
  have h1 : ∃ k, f (Pi.single k 1) ≠ 0 := by
    by_contra h
    have h' : ∀ k, f (Pi.single k 1) = 0 := fun k => by_contra fun hk => h ⟨k, hk⟩
    have h2 : f (∑ k, Pi.single k 1) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => h' k
    have h3 : (∑ k, Pi.single k 1 : ι → O) = 1 := Finset.univ_sum_single (1 : ι → O)
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨k, hk⟩ := h1
  have hi : IsIdempotentElem (Pi.single k 1 : ι → O) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have h4 : f (Pi.single k 1) = 1 := (hO _ (hi.map f)).resolve_left hk
  refine ⟨k, fun g => ?_⟩
  have h5 : g * Pi.single k 1 = g k • (Pi.single k 1 : ι → O) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  have h6 := congrArg f h5
  rwa [map_mul, map_smul, h4, mul_one, smul_eq_mul, mul_one] at h6
end GlobalTheory.PDivGroup
