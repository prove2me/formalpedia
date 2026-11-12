-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:53:56.874696+00:00
-- url     : https://prove2.me/submissions/7a0d38ca-4846-42c4-8320-eb1976d370fb

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_log_center_lipschitz
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_normalized_sound

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

theorem pad_sound {b : Ball} {x y : ℝ} {error : ℚ}
    (hx : b.Encloses x) (hxy : |y - x| ≤ (error : ℝ)) :
    (pad b error).Encloses y := by
  unfold Ball.Encloses pad at *
  simp only [Rat.cast_add]
  calc
    _ = |(y - x) + (x - (b.center : ℝ))| := by congr 1; ring
    _ ≤ |y - x| + |x - (b.center : ℝ)| := abs_add_le _ _
    _ ≤ (error : ℝ) + (b.radius : ℝ) := add_le_add hxy hx
    _ = _ := by ring

end MatrixMultiplication.AllFieldCertificates.Replay

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

lemma checkLog_sound_oai {two a b : Ball} {w : LogData} {x : ℝ}
    (htwo : two.Encloses (Real.log 2)) (hx : a.Encloses x)
    (h : checkLog two a b w = true) : b.Encloses (Real.log x) := by
  simp only [checkLog, Bool.and_eq_true] at h
  obtain ⟨hpos, hd, hlo, hhi, heq⟩ := of_decide_eq_true h.1
  have hm : (0 : ℝ) < (w.numerator : ℝ) / w.denominator := by
    have hn : 0 < w.numerator := lt_of_lt_of_le hd hlo
    exact div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hd)
  have heq' : (a.center : ℝ) = ((w.numerator : ℝ) / w.denominator) * (2 : ℝ) ^ w.exponent := by
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) heq
  have hlog : Real.log (a.center : ℝ) =
      Real.log ((w.numerator : ℝ) / w.denominator) + (w.exponent : ℝ) * Real.log 2 := by
    rw [heq', Real.log_mul (ne_of_gt hm) (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hcenter : (Ball.add (normalized w.numerator w.denominator)
      (Ball.mul (.exact w.exponent) two)).Encloses (Real.log (a.center : ℝ)) := by
    rw [hlog]
    exact Ball.add_sound (normalized_sound hd hlo hhi)
      (by simpa using Ball.mul_sound (Ball.exact_sound (w.exponent : ℚ)) htwo)
  exact contains_sound (pad_sound hcenter (log_center_lipschitz hx hpos)) h.2

end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.checkLog_sound_oai
