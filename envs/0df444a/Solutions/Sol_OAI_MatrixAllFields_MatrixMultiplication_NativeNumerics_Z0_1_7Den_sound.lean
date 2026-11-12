-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Den_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T09:20:07.700297+00:00
-- url     : https://prove2.me/submissions/3e1e8333-b9ff-412c-a907-eb317941c4e0

import Mathlib
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Ball_exact_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound

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

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

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

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma listSumBall_sound {α : Type*} (xs : List α) (b : α → Ball) (v : α → ℝ)
    (h : ∀ x ∈ xs, (b x).Encloses (v x)) :
    (listSumBall xs b).Encloses ((xs.map v).sum) := by
  induction xs with
  | nil => simpa [listSumBall] using Ball.exact_sound 0
  | cons x xs ih =>
    simpa only [listSumBall, List.foldr_cons, List.map_cons, List.sum_cons] using
      Ball.add_sound (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators

lemma list_cast_enclosed {A : Type*} (xs : List A) (b : A → Ball) (v : A → ℚ)
    (h : ∀ a ∈ xs, (b a).Encloses (v a : ℝ)) :
    (listSumBall xs b).Encloses ((xs.map v).sum : ℝ) := by
  simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def] using
    listSumBall_sound xs b (fun a => (v a : ℝ)) h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

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
lemma Z0_1_7Den_sound_oai : Z0_1_7Den.Encloses
    (((orderedPairs (shape 0 1 7)).map (fun ij => weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 1 7)) Z0_1_7Raw
    (fun ij => weight (orderedPairInteger (shape 0 1 7) ij.1 ij.2))
    (fun ij _ => Z0_1_7Raw_sound ij)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Den_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.Z0_1_7Den_sound_oai
