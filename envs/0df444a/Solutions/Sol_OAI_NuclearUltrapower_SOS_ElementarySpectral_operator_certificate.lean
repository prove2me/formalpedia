-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:00:22.46821+00:00
-- url     : https://prove2.me/submissions/f7e4fde0-eccd-4946-90c7-a5bad7534d2a

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem operator_certificate_oai (D Q R : H →L[ℂ] H)
    (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
    (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R := by
  rw [h]
  ext x
  simp only [add_apply, sub_apply, smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
    ← Int.cast_smul_eq_zsmul ℝ]
  norm_num only [Int.cast_ofNat]
  abel

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate_oai.{u_1}
