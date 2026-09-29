-- Prove2me | solution 1 for ModPForms.modPMod_le_modPMod_add_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/63b5e874-d2f5-5609-a42b-7b13d5e0f783

import Definitions.Def_CuspForm_ModPForms
import Theorems.Thm_ModularForm_exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_modPMod_le_modPMod_add_sub_one
set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open ModularForm CongruenceSubgroup ModPForms
open scoped MatrixGroups

namespace E34S

section Furniture

variable {N' : ℕ} {k : ℤ}

private lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  simp [Gamma0_mem, ModularGroup.coe_T]

private lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

private lemma analyticAt_mf (f : ModularForm (Gamma0 N') k) : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 N')

private lemma qCoeff_eq (f : ℍ → ℂ) (n : ℕ) : ModularFormClass.qCoeff f n = (qExpansion 1 f).coeff n := rfl

end Furniture
end E34S

open E34S in
theorem solution (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (k : ℤ)
    (F : Type) [Field F] [CharP F p] :
    modPMod N' k F ≤ modPMod N' (k + ((p : ℤ) - 1)) F := by
  obtain ⟨A, b, hb, hb0, hbn⟩ := ModularForm.exists_gamma0_qCoeff_intCast_and_dvd_sub_one_of_five_le p hp hp5 N'
  have hb0F : ((b 0 : ℤ) : F) = 1 := by
    have h : (((b 0 - 1 : ℤ)) : F) = 0 := (CharP.intCast_eq_zero_iff F p _).mpr hb0
    rwa [Int.cast_sub, Int.cast_one, sub_eq_zero] at h
  have hbF : ∀ n, 0 < n → ((b n : ℤ) : F) = 0 := fun n hn => (CharP.intCast_eq_zero_iff F p _).mpr (hbn n hn)
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨f, a, ha, rfl⟩

  have ha' : ∀ i, (qExpansion 1 ⇑f).coeff i = (a i : ℂ) := ha
  have hb' : ∀ i, (qExpansion 1 ⇑A).coeff i = (b i : ℂ) := hb
  have hconv : ∀ n, ModularFormClass.qCoeff (f.mul A) n =
      ((∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * b x.2 : ℤ) : ℂ) := by
    intro n
    rw [qCoeff_eq, ModularForm.coe_mul, qExpansion_mul (analyticAt_mf f) (analyticAt_mf A), PowerSeries.coeff_mul]
    simp only [ha', hb', Int.cast_sum, Int.cast_mul]
  have hred : (PowerSeries.mk fun n => ((a n : ℤ) : F)) =
      PowerSeries.mk fun n => (((∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * b x.2 : ℤ)) : F) := by
    ext n
    simp only [PowerSeries.coeff_mk]
    push_cast
    rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
    · simp only [hb0F, mul_one]
    · intro x hx hne
      have hx2 : 0 < x.2 := by
        rcases Nat.eq_zero_or_pos x.2 with h | h
        · exfalso
          apply hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          ext
          · show x.1 = n
            omega
          · exact h
        · exact h
      rw [hbF x.2 hx2, mul_zero]
  rw [hred]
  exact Submodule.subset_span ⟨f.mul A, fun n => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, a x.1 * b x.2, hconv, rfl⟩

end S_ModPForms_modPMod_le_modPMod_add_sub_one
end P2MW
export P2MW.S_ModPForms_modPMod_le_modPMod_add_sub_one (solution)
