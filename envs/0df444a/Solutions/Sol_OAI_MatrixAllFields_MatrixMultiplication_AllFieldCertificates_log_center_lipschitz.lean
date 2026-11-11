-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:55.469388+00:00
-- url     : https://prove2.me/submissions/5a875576-6712-434f-93b9-9aa802f681a5

import Mathlib
import Definitions.Def_OAIQ254M000

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

namespace Ball

theorem nonnegative_radius {b : Ball} {x : ℝ} (h : b.Encloses x) : 0 ≤ b.radius := by
  have : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans h
  exact_mod_cast this

theorem bounds {b : Ball} {x : ℝ} (h : b.Encloses x) :
    (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp only [lower, upper, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

end Ball

theorem log_center_lipschitz_oai {b : Ball} {x : ℝ} (hx : b.Encloses x)
    (hpos : 0 < b.lower) :
    |Real.log x - Real.log (b.center : ℝ)| ≤ (b.radius / b.lower : ℚ) := by
  have hr : (0 : ℝ) ≤ b.radius := by exact_mod_cast Ball.nonnegative_radius hx
  have hl : (0 : ℝ) < b.lower := by exact_mod_cast hpos
  have hcl : (b.lower : ℝ) ≤ b.center := by
    simp only [Ball.lower, Rat.cast_sub]
    linarith
  have hc : (0 : ℝ) < b.center := hl.trans_le hcl
  obtain ⟨hxl, _⟩ := Ball.bounds hx
  have hxp : 0 < x := hl.trans_le hxl
  have logs (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
      Real.log a - Real.log c ≤ (a - c) / c := by
    rw [← Real.log_div ha.ne' hc.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos ha hc)
    have he : a / c - 1 = (a - c) / c := by field_simp
    rwa [he] at h
  have hup : Real.log x - Real.log (b.center : ℝ) ≤ (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ (x - (b.center : ℝ)) / (b.center : ℝ) := logs _ _ hxp hc
      _ ≤ (b.radius : ℝ) / (b.center : ℝ) :=
        div_le_div_of_nonneg_right (abs_le.mp hx).2 hc.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hcl
  have hdown : Real.log (b.center : ℝ) - Real.log x ≤
      (b.radius : ℝ) / (b.lower : ℝ) := by
    calc
      _ ≤ ((b.center : ℝ) - x) / x := logs _ _ hc hxp
      _ ≤ (b.radius : ℝ) / x :=
        div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1]) hxp.le
      _ ≤ _ := div_le_div_of_nonneg_left hr hl hxl
  rw [Rat.cast_div]
  exact abs_le.mpr ⟨by linarith, hup⟩

end MatrixMultiplication.AllFieldCertificates

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.log_center_lipschitz_oai
