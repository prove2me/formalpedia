-- Prove2me | solution 1 for GlobalTheory.QFam.isFam_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:32.088636+00:00
-- url     : https://prove2.me/submissions/8f58b28f-483f-4d20-9af0-abe2b804b0e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
import Theorems.Thm_GlobalTheory_QFam_IsFam_const_mul_fun
import Theorems.Thm_GlobalTheory_QFam_IsFam_mul_fun
import Theorems.Thm_GlobalTheory_QFam_IsFam_pow_fun
import Theorems.Thm_GlobalTheory_QFam_IsFam_sum_fun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
namespace GlobalTheory.QFam
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
private lemma isFam_apply_smul_mul_denom_zpow {w : ℤ} {f : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ ^ (-w) = f (act i γ) τ := by
  rw [← SL_slash_apply, hf i γ]
end GlobalTheory.QFam
end

set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ModularForm
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
namespace GlobalTheory.QFam
namespace _root_.GlobalTheory.QFam
theorem _root_.solution : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι),
    (∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c) ∧
    (∀ w f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w g →
      (_root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ + g i τ) ∧
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ - g i τ) ∧
    (∀ w (c : ℂ) f, _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ) ∧
    (∀ w w' f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w' g →
      _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ) ∧
    (∀ w f (k : ℕ), _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k) ∧
    (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) →
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act (w k) (f k)) →
        _root_.GlobalTheory.QFam.IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f,
      (∀ k γ, φ (act' k γ) = act (φ k) γ) → _root_.GlobalTheory.QFam.IsFam act w f →
        _root_.GlobalTheory.QFam.IsFam act' w fun k => f (φ k)) := by
  intro ι act
  have hconst : ∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c := by
    intro c i γ
    funext τ
    simp [SL_slash_apply]
  refine ⟨hconst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f g hf hg
    constructor
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
  · intro w c f hf
    exact hf.const_mul_fun c
  · intro w w' f g hf hg
    exact hf.mul_fun hg
  · intro w f k hf
    exact hf.pow_fun k
  · intro κ t w f hf
    exact _root_.GlobalTheory.QFam.IsFam.sum_fun t hf
  · intro κ t w f hf
    classical
    induction t using Finset.induction_on with
    | empty => simpa using hconst 1
    | insert a s ha ih =>
      have hmul := (hf a (Finset.mem_insert_self a s)).mul_fun
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert ha, Finset.prod_insert ha] using hmul
  · intro κ act' φ w f hφ hf k γ
    show f (φ k) ∣[w] γ = f (φ (act' k γ))
    rw [hf (φ k) γ, hφ k γ]
end _root_.GlobalTheory.QFam
end GlobalTheory.QFam
