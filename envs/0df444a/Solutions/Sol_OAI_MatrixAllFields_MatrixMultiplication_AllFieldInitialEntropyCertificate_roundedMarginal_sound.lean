-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:55.910193+00:00
-- url     : https://prove2.me/submissions/440f8d25-0bfc-4a0e-a443-5f26919c883c

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_initialDenominatorBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_initialRawBall_sound

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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

lemma finSumBall_sound (n : ℕ) (b : Fin n → Ball) (v : Fin n → ℝ)
    (h : ∀ i, (b i).Encloses (v i)) :
    (finSumBall n b).Encloses (∑ i, v i) := by
  induction n with
  | zero => simpa [finSumBall] using Ball.exact_sound 0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    exact Ball.add_sound (h 0) (ih _ _ (fun i => h i.succ))

lemma initialDenominatorBall_positive : 0 < initialDenominatorBall.lower := by
  decide +kernel

lemma initialLawBall_sound (s : Shape) (hs : s ∈ sortedInitial) :
    (initialLawBall s).Encloses (initialLaw s : ℝ) := by
  have h := Ball.mul_sound (initialRawBall_sound s hs)
    (Ball.inv_sound initialDenominatorBall_sound initialDenominatorBall_positive)
  simpa only [initialLawBall, initialLaw, hs, ite_true, if_true, Rat.cast_div,
    div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv] using h

lemma initialMarginalBall_sound (k : Fin 17) :
    (initialMarginalBall k).Encloses (AllFieldInitialEntropy.nativeInitialMarginal k) := by
  apply finSumBall_sound
  intro g
  have h := Ball.mul_sound (initialLawBall_sound (sortedInitial.get g) (List.get_mem _ _))
    (Ball.exact_sound ((∑ w : Fin 3, if sortedInitial.get g w = k.val then (1 : ℚ) else 0) / 3))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Rat.cast_div, Rat.cast_sum, apply_ite, Rat.cast_one,
    Rat.cast_zero, Rat.cast_ofNat, mul_div_assoc]

lemma marginal_containment_0 : contains (initialMarginalBall 0) (roundedMarginal 0) = true := by
  decide +kernel

lemma marginal_containment_1 : contains (initialMarginalBall 1) (roundedMarginal 1) = true := by
  decide +kernel

lemma marginal_containment_2 : contains (initialMarginalBall 2) (roundedMarginal 2) = true := by
  decide +kernel

lemma marginal_containment_3 : contains (initialMarginalBall 3) (roundedMarginal 3) = true := by
  decide +kernel

lemma marginal_containment_4 : contains (initialMarginalBall 4) (roundedMarginal 4) = true := by
  decide +kernel

lemma marginal_containment_5 : contains (initialMarginalBall 5) (roundedMarginal 5) = true := by
  decide +kernel

lemma marginal_containment_6 : contains (initialMarginalBall 6) (roundedMarginal 6) = true := by
  decide +kernel

lemma marginal_containment_7 : contains (initialMarginalBall 7) (roundedMarginal 7) = true := by
  decide +kernel

lemma marginal_containment_8 : contains (initialMarginalBall 8) (roundedMarginal 8) = true := by
  decide +kernel

lemma marginal_containment_9 : contains (initialMarginalBall 9) (roundedMarginal 9) = true := by
  decide +kernel

lemma marginal_containment_10 : contains (initialMarginalBall 10) (roundedMarginal 10) = true := by
  decide +kernel

lemma marginal_containment_11 : contains (initialMarginalBall 11) (roundedMarginal 11) = true := by
  decide +kernel

lemma marginal_containment_12 : contains (initialMarginalBall 12) (roundedMarginal 12) = true := by
  decide +kernel

lemma marginal_containment_13 : contains (initialMarginalBall 13) (roundedMarginal 13) = true := by
  decide +kernel

lemma marginal_containment_14 : contains (initialMarginalBall 14) (roundedMarginal 14) = true := by
  decide +kernel

lemma marginal_containment_15 : contains (initialMarginalBall 15) (roundedMarginal 15) = true := by
  decide +kernel

lemma marginal_containment_16 : contains (initialMarginalBall 16) (roundedMarginal 16) = true := by
  decide +kernel

lemma roundedMarginal_sound_oai (k : Fin 17) :
    (roundedMarginal k).Encloses (AllFieldInitialEntropy.nativeInitialMarginal k) := by
  apply contains_sound (initialMarginalBall_sound k)
  fin_cases k
  · exact marginal_containment_0
  · exact marginal_containment_1
  · exact marginal_containment_2
  · exact marginal_containment_3
  · exact marginal_containment_4
  · exact marginal_containment_5
  · exact marginal_containment_6
  · exact marginal_containment_7
  · exact marginal_containment_8
  · exact marginal_containment_9
  · exact marginal_containment_10
  · exact marginal_containment_11
  · exact marginal_containment_12
  · exact marginal_containment_13
  · exact marginal_containment_14
  · exact marginal_containment_15
  · exact marginal_containment_16

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.roundedMarginal_sound_oai
