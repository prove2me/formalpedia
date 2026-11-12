-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Law_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:57:49.837419+00:00
-- url     : https://prove2.me/submissions/df3a969e-6f4e-4946-9ea7-12e9038d1671

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_2_12Den_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_A2_2_12Raw_sound

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
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SplitA2_2_12
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
lemma A2_2_12_below : below (shape 2 2 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4)] := by decide +kernel
lemma A2_2_12Den_positive : 0 < A2_2_12Den.lower := by decide +kernel
lemma A2_2_12Law_check_0_0_8 : contains (.mul (A2_2_12Raw (shape 0 0 8)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_2_12Law_check_0_1_7 : contains (.mul (A2_2_12Raw (shape 0 1 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_2_12Law_check_0_2_6 : contains (.mul (A2_2_12Raw (shape 0 2 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_0_7 : contains (.mul (A2_2_12Raw (shape 1 0 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_2_12Law_check_1_1_6 : contains (.mul (A2_2_12Raw (shape 1 1 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_2_5 : contains (.mul (A2_2_12Raw (shape 1 2 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_0_6 : contains (.mul (A2_2_12Raw (shape 2 0 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_2_12Law_check_2_1_5 : contains (.mul (A2_2_12Raw (shape 2 1 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_2_4 : contains (.mul (A2_2_12Raw (shape 2 2 4)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_2_12Law_check (u : Shape) (hu : u ∈ below (shape 2 2 12)) :
    contains (.mul (A2_2_12Raw u) (.inv A2_2_12Den)) (A2_2_12Table u) = true := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_2_12Law_check_0_0_8
  · exact A2_2_12Law_check_0_1_7
  · exact A2_2_12Law_check_0_2_6
  · exact A2_2_12Law_check_1_0_7
  · exact A2_2_12Law_check_1_1_6
  · exact A2_2_12Law_check_1_2_5
  · exact A2_2_12Law_check_2_0_6
  · exact A2_2_12Law_check_2_1_5
  · exact A2_2_12Law_check_2_2_4
lemma A2_2_12Law_sound_oai (u : Shape) :
    (A2_2_12Law u).Encloses (stageALaw (shape 2 2 12) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 2 12)
  · have h := contains_sound (Ball.mul_sound (A2_2_12Raw_sound u hu)
      (Ball.inv_sound A2_2_12Den_sound A2_2_12Den_positive)) (A2_2_12Law_check u hu)
    simpa only [A2_2_12Law, hu, ite_true, if_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_2_12Law, hu, ite_false, if_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Law_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.A2_2_12Law_sound_oai
