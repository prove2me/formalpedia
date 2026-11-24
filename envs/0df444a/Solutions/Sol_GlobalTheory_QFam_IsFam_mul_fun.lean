-- Prove2me | solution 1 for GlobalTheory.QFam.IsFam.mul_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:29.485142+00:00
-- url     : https://prove2.me/submissions/28145469-d73a-44ea-baf4-72428372edf9

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
theorem _root_.solution {w w' : ℤ} {f g : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (hg : _root_.GlobalTheory.QFam.IsFam act w' g) :
    _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ, neg_add,
    zpow_add₀ (UpperHalfPlane.denom_ne_zero _ _)]
  ring
end _root_.GlobalTheory.QFam.IsFam
end GlobalTheory.QFam
