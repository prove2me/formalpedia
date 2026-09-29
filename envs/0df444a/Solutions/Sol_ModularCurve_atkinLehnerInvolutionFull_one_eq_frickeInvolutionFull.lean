-- Prove2me | solution 1 for ModularCurve.atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8791eaaf-a229-53f6-a0fb-72a323c39807

import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_IsFrickeAutFull_eq_frickeInvolutionFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve

private theorem isFrickeAutFull_of_isAtkinLehnerAutFull_one (q : ℕ) [Fact q.Prime]
    (σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q))
    (h : IsAtkinLehnerAutFull 1 q σ) : IsFrickeAutFull (1 * q) σ := by
  have hq : q.Prime := Fact.out
  obtain ⟨h1, h2⟩ := h 1 ⟨Nat.one_ne_zero⟩ dvd_rfl
  have eSub : ∀ (m1 : qExpand ℚ (1 * q) jq ∈ modularFunctionFieldFull (1 * q))
      (m2 : qExpand ℚ q jq ∈ modularFunctionFieldFull (1 * q)),
      (⟨qExpand ℚ (1 * q) jq, m1⟩ : modularFunctionFieldFull (1 * q))
        = ⟨qExpand ℚ q jq, m2⟩ :=
    fun m1 m2 => Subtype.ext (by
      show qExpand ℚ (1 * q) jq = qExpand ℚ q jq
      simp only [one_mul])
  intro a b hab _ _
  have hab' : a * b = q := by rwa [one_mul] at hab
  rcases hq.eq_one_or_self_of_dvd a (Dvd.intro b hab') with rfl | rfl
  · obtain rfl : b = q := by rwa [one_mul] at hab'
    exact h1.trans (eSub _ _)
  · obtain rfl : b = 1 := Nat.eq_of_mul_eq_mul_left hq.pos (by rw [mul_one]; exact hab')
    exact (congrArg σ (eSub _ _).symm).trans h2

theorem solution (q : ℕ) [Fact q.Prime] :
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by
  have hAL : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
      IsAtkinLehnerAutFull 1 q σ :=
    exists_isAtkinLehnerAutFull_of_prime_of_not_dvd 1 q Fact.out
      (fun hdvd => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp hdvd))
  exact (isFrickeAutFull_of_isAtkinLehnerAutFull_one q _
    (isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 q hAL)).eq_frickeInvolutionFull

#print axioms solution

end S_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull
end P2MW
export P2MW.S_ModularCurve_atkinLehnerInvolutionFull_one_eq_frickeInvolutionFull (solution)
