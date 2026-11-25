-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_lt_one_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:54.780793+00:00
-- url     : https://prove2.me/submissions/69897959-253d-49e5-a528-e3dc7a44692a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
namespace GroundTheory.PAdicHodge
theorem _root_.solution {q : ℝ} (hq : q < 1) (d : ℕ) :
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ q ≤ μ ^ d := by
  set q' := max q 0
  have hq' : q' < 1 := max_lt hq one_pos
  have hq0 : 0 ≤ q' := le_max_right _ _
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exact ⟨1 / 2, by norm_num, by norm_num, by rw [hd, pow_zero]; exact hq.le⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := -((1 - q') / (2 * d))
  have ha1 : (1 - q') / (2 * d) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have ha0 : 0 < (1 - q') / (2 * d) := by
    apply div_pos <;> linarith
  refine ⟨1 + a, by simp only [a]; linarith, by simp only [a]; linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := a) (by simp only [a]; linarith) d
  have : (d : ℝ) * a = -((1 - q') / 2) := by
    simp only [a]; field_simp
  rw [this] at hb
  calc q ≤ q' := le_max_left _ _
    _ ≤ 1 + -((1 - q') / 2) := by linarith
    _ ≤ _ := hb
end GroundTheory.PAdicHodge
