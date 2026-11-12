-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Probs_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:53:24.463085+00:00
-- url     : https://prove2.me/submissions/0442015c-1667-431b-8287-c2e264e053d2

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_mul_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_Z0_1_7Den_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

namespace Ball

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem inv_sound {a : Ball} {x : ℝ} (hx : a.Encloses x)
    (hpos : 0 < a.lower) : (inv a).Encloses x⁻¹ := by
  have hlo : (0 : ℝ) < a.lower := by exact_mod_cast hpos
  obtain ⟨hl, hu⟩ := bounds hx
  have hxp : 0 < x := lt_of_lt_of_le hlo hl
  apply ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hxp hu
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_inv, one_div] using
      one_div_le_one_div_of_le hlo hl

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma forall_fin6 {P : Fin 6 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) : ∀ i, P i := by
  intro i
  fin_cases i <;> assumption

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_Zero0_1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma w195_sound : w195.Encloses (weight 0 : ℝ) := by
  have he : weight 0 = 1 := by decide +kernel
  rw [he, Rat.cast_one]
  simpa only [w195, Rat.cast_one] using Ball.exact_sound 1

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma Z0_1_7Raw_sound_0 (j : Fin 6) :
    (Z0_1_7Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_1 (j : Fin 6) :
    (Z0_1_7Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_2 (j : Fin 6) :
    (Z0_1_7Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_3 (j : Fin 6) :
    (Z0_1_7Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_4 (j : Fin 6) :
    (Z0_1_7Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound_5 (j : Fin 6) :
    (Z0_1_7Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_1_7Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_1_7Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 1 7) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 1 7) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_1_7Raw_sound (ij : PairSlot) :
    (Z0_1_7Raw ij).Encloses (weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_1_7Raw_sound_0 j) (Z0_1_7Raw_sound_1 j) (Z0_1_7Raw_sound_2 j) (Z0_1_7Raw_sound_3 j) (Z0_1_7Raw_sound_4 j) (Z0_1_7Raw_sound_5 j)
lemma Z0_1_7Den_pos : 0 < Z0_1_7Den.lower := by decide +kernel
lemma Z0_1_7Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 1 7) →
    contains (.mul (Z0_1_7Raw (i,j)) (.inv Z0_1_7Den)) (Z0_1_7Probs (i,j)) = true := by
  decide +kernel
lemma Z0_1_7Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 1 7) → Z0_1_7Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_1_7Probs_sound_oai (ij : PairSlot) :
    (Z0_1_7Probs ij).Encloses (zeroPairLaw (shape 0 1 7) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 1 7)
  · have hb := contains_sound (Ball.mul_sound (Z0_1_7Raw_sound ij)
      (Ball.inv_sound Z0_1_7Den_sound Z0_1_7Den_pos)) (Z0_1_7Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, if_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_1_7Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false, if_false] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Probs_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Probs_sound_oai
