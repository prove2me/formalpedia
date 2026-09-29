-- Prove2me | solution 1 for IntermediateField.finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1f117fe6-1183-5826-b628-c066a51556cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : (n : F) ≠ 0) (a : E) (b : F) (hb : b ≠ 0) (hab : a ^ n = algebraMap F E b)
    (hgen : IntermediateField.adjoin F ({a} : Set E) = ⊤) :
    FiniteDimensional F E ∧ Module.finrank F E ≤ n ∧ Algebra.IsSeparable F E := by
  classical
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  set P : Polynomial F := Polynomial.X ^ n - Polynomial.C b with hP
  have hPsep : P.Separable := Polynomial.separable_X_pow_sub_C b hn hb
  have hmonic : P.Monic := Polynomial.monic_X_pow_sub_C b hn0
  have hPne : P ≠ 0 := hmonic.ne_zero
  have haP : Polynomial.aeval a P = 0 := by
    simp [hP, hab]
  have hint : IsIntegral F a := ⟨P, hmonic, by rw [← Polynomial.aeval_def]; exact haP⟩
  have hdvd : minpoly F a ∣ P := minpoly.dvd F a haP
  have hsepa : IsSeparable F a := hPsep.of_dvd hdvd
  have hdeg : (minpoly F a).natDegree ≤ n := by
    calc (minpoly F a).natDegree ≤ P.natDegree := Polynomial.natDegree_le_of_dvd hdvd hPne
      _ = n := by rw [hP, Polynomial.natDegree_X_pow_sub_C]

  have hfdA : FiniteDimensional F ↥(IntermediateField.adjoin F ({a} : Set E)) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hrkA : Module.finrank F ↥(IntermediateField.adjoin F ({a} : Set E)) = (minpoly F a).natDegree :=
    IntermediateField.adjoin.finrank hint
  have hsepA : Algebra.IsSeparable F ↥(IntermediateField.adjoin F ({a} : Set E)) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).mpr hsepa
  rw [hgen] at hfdA hrkA hsepA
  have e : (⊤ : IntermediateField F E) ≃ₐ[F] E := IntermediateField.topEquiv
  haveI := hfdA
  haveI := hsepA
  refine ⟨e.toLinearEquiv.finiteDimensional, ?_, AlgEquiv.Algebra.isSeparable e⟩
  rw [← e.toLinearEquiv.finrank_eq, hrkA]
  exact hdeg

end S_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top
end P2MW
export P2MW.S_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top (solution)
