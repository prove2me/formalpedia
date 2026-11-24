-- Prove2me | solution 1 for GlobalTheory.QFam.IsFam.sum_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:30.743931+00:00
-- url     : https://prove2.me/submissions/12940a3e-865c-40db-96e6-be615bce6085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
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
namespace _root_.GlobalTheory.QFam.IsFam
theorem _root_.solution {κ : Type} (t : Finset κ) {w : ℤ}
    {f : κ → ι → ℍ → ℂ} (hf : ∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => isFam_apply_smul_mul_denom_zpow (hf k hk) i γ τ
end _root_.GlobalTheory.QFam.IsFam
end GlobalTheory.QFam
