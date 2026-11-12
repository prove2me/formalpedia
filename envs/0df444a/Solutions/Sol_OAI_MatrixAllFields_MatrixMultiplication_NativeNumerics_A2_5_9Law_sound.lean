-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:58:17.881319+00:00
-- url     : https://prove2.me/submissions/90b9fd0b-d4d9-406a-a530-29e182c415c0

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_5_9Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
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

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

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

theorem exact_sound (q : ℚ) : (exact q).Encloses (q : ℝ) := by
  simp [Encloses, exact]

theorem add_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (add a b).Encloses (x + y) := by
  unfold Encloses add
  simp only [Rat.cast_add]
  calc
    _ = |(x - (a.center : ℝ)) + (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |y - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ _ := add_le_add hx hy

theorem mul_sound {a b : Ball} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (mul a b).Encloses (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := by exact_mod_cast nonnegative_radius hx
  have hb : (0 : ℝ) ≤ b.radius := by exact_mod_cast nonnegative_radius hy
  unfold Encloses mul
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs]
  calc
    _ = |(a.center : ℝ) * (y - (b.center : ℝ)) +
          (b.center : ℝ) * (x - (a.center : ℝ)) +
          (x - (a.center : ℝ)) * (y - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - (b.center : ℝ))| +
          |(b.center : ℝ) * (x - (a.center : ℝ))| +
          |(x - (a.center : ℝ)) * (y - (b.center : ℝ))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |(a.center : ℝ)| * |y - (b.center : ℝ)| +
          |(b.center : ℝ)| * |x - (a.center : ℝ)| +
          |x - (a.center : ℝ)| * |y - (b.center : ℝ)| := by simp only [abs_mul]
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _)))
      (mul_le_mul hx hy (abs_nonneg _) ha)

theorem widen_sound {a b : Ball} {x : ℝ} (hx : a.Encloses x)
    (h : |a.center - b.center| + a.radius ≤ b.radius) : b.Encloses x := by
  have hc : |(a.center : ℝ) - (b.center : ℝ)| + (a.radius : ℝ) ≤ (b.radius : ℝ) := by
    exact_mod_cast h
  unfold Encloses
  calc
    _ = |(x - (a.center : ℝ)) + ((a.center : ℝ) - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + |(a.center : ℝ) - (b.center : ℝ)| := add_le_add hx (le_refl _)
    _ ≤ _ := by linarith

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

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

theorem contains_sound {a b : Ball} {x : ℝ}
    (ha : a.Encloses x) (hab : contains a b = true) : b.Encloses x :=
  Ball.widen_sound ha (of_decide_eq_true hab)

end MatrixMultiplication.AllFieldCertificates.Replay

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

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_5_9
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
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A2_5_9_below : below (shape 2 5 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1)] := by decide +kernel
lemma A2_5_9Den_sound : A2_5_9Den.Encloses (((below (shape 2 5 9)).map (splitWeight positiveInitial tableP (shape 2 5 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 5 9)) A2_5_9Raw (splitWeight positiveInitial tableP (shape 2 5 9)) A2_5_9Raw_sound) (by decide +kernel)
lemma A2_5_9Den_positive : 0 < A2_5_9Den.lower := by decide +kernel
lemma A2_5_9Law_check_0_0_8 : contains (.mul (A2_5_9Raw (shape 0 0 8)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_5_9Law_check_0_1_7 : contains (.mul (A2_5_9Raw (shape 0 1 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_5_9Law_check_0_2_6 : contains (.mul (A2_5_9Raw (shape 0 2 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_5_9Law_check_0_3_5 : contains (.mul (A2_5_9Raw (shape 0 3 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_5_9Law_check_0_4_4 : contains (.mul (A2_5_9Raw (shape 0 4 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_5_9Law_check_0_5_3 : contains (.mul (A2_5_9Raw (shape 0 5 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 5 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_0_7 : contains (.mul (A2_5_9Raw (shape 1 0 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_5_9Law_check_1_1_6 : contains (.mul (A2_5_9Raw (shape 1 1 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_5_9Law_check_1_2_5 : contains (.mul (A2_5_9Raw (shape 1 2 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_5_9Law_check_1_3_4 : contains (.mul (A2_5_9Raw (shape 1 3 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_5_9Law_check_1_4_3 : contains (.mul (A2_5_9Raw (shape 1 4 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_5_2 : contains (.mul (A2_5_9Raw (shape 1 5 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 5 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_0_6 : contains (.mul (A2_5_9Raw (shape 2 0 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_5_9Law_check_2_1_5 : contains (.mul (A2_5_9Raw (shape 2 1 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_5_9Law_check_2_2_4 : contains (.mul (A2_5_9Raw (shape 2 2 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_5_9Law_check_2_3_3 : contains (.mul (A2_5_9Raw (shape 2 3 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_5_9Law_check_2_4_2 : contains (.mul (A2_5_9Raw (shape 2 4 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_5_1 : contains (.mul (A2_5_9Raw (shape 2 5 1)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 5 1)) = true := by decide +kernel
lemma A2_5_9Law_check (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
    contains (.mul (A2_5_9Raw u) (.inv A2_5_9Den)) (A2_5_9Table u) = true := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_5_9Law_check_0_0_8
  · exact A2_5_9Law_check_0_1_7
  · exact A2_5_9Law_check_0_2_6
  · exact A2_5_9Law_check_0_3_5
  · exact A2_5_9Law_check_0_4_4
  · exact A2_5_9Law_check_0_5_3
  · exact A2_5_9Law_check_1_0_7
  · exact A2_5_9Law_check_1_1_6
  · exact A2_5_9Law_check_1_2_5
  · exact A2_5_9Law_check_1_3_4
  · exact A2_5_9Law_check_1_4_3
  · exact A2_5_9Law_check_1_5_2
  · exact A2_5_9Law_check_2_0_6
  · exact A2_5_9Law_check_2_1_5
  · exact A2_5_9Law_check_2_2_4
  · exact A2_5_9Law_check_2_3_3
  · exact A2_5_9Law_check_2_4_2
  · exact A2_5_9Law_check_2_5_1
lemma A2_5_9Law_sound_oai (u : Shape) :
    (A2_5_9Law u).Encloses (stageALaw (shape 2 5 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 5 9)
  · have h := contains_sound (Ball.mul_sound (A2_5_9Raw_sound u hu)
      (Ball.inv_sound A2_5_9Den_sound A2_5_9Den_positive)) (A2_5_9Law_check u hu)
    simpa only [A2_5_9Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_5_9Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_5_9Law_sound_oai
