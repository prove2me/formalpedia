-- Prove2me | solution 1 for GlobalTheory.QFam.IsFam.const_mul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:28.008682+00:00
-- url     : https://prove2.me/submissions/8d97d92c-03d3-4408-bc45-8b7e71570654

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
theorem _root_.solution {w : ℤ} {f : ι → ℍ → ℂ} (c : ℂ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ]
  ring
end _root_.GlobalTheory.QFam.IsFam
end GlobalTheory.QFam
