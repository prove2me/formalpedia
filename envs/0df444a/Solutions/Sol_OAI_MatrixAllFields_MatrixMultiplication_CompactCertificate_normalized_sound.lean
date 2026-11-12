-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.normalized_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:13:09.246544+00:00
-- url     : https://prove2.me/submissions/0d64bc7c-031f-430c-ae2a-dd3297e9370c

import Mathlib
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_normalized_log_error_48
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_pad_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_logApprox_sound

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

theorem ofBounds_sound {lo hi : ℚ} {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (ofBounds lo hi).Encloses x := by
  simp only [Encloses, ofBounds, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ball

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section

namespace MatrixMultiplication.CompactCertificate
open AllFieldCertificates AllFieldCertificates.Replay
open Foundation.RationalLogCertificate

lemma NInterval.ball_sound {a : NInterval} {x : ℝ} (h : a.Encloses scale x) :
    a.ball.Encloses x := by
  apply Ball.ofBounds_sound
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.1
  · simpa only [Rat.cast_div, Rat.cast_natCast] using h.2

lemma normalized_sound_oai {n d : ℕ} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2 * d) :
    (normalized n d).Encloses (Real.log ((n : ℝ) / d)) := by
  apply pad_sound (NInterval.ball_sound (logApprox_sound hd hlo))
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hl : 1 ≤ (n : ℝ) / d := (le_div_iff₀ hd').2 (by simpa only [one_mul] using (Nat.cast_le.mpr hlo : (d : ℝ) ≤ n))
  have hh : (n : ℝ) / d ≤ 2 := (div_le_iff₀ hd').2 (by exact_mod_cast hhi)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
    (normalized_log_error_48 ((n : ℝ) / d) hl hh).le

end MatrixMultiplication.CompactCertificate

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.normalized_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.CompactCertificate.normalized_sound_oai
