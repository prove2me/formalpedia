-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.orth_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:42:51.130273+00:00
-- url     : https://prove2.me/submissions/491cb0e1-d218-4909-b916-8bcb07ee4ec3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatIntegralEqSumResidueRepresentativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCosetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitarySiegelThetaTransformationLawStandar
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_eq_one_iff
import Theorems.Thm_GlobalTheory_SW_FourierJ_ech_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ
noncomputable section
namespace GlobalTheory.SW.FourierJ
theorem _root_.solution {R : ℕ} (hR : 0 < R) (a b : Fin (R * R)) :
    ∑ n : Fin (R * R), ech ((((a : ℕ) : ℚ) / R - ((b : ℕ) : ℚ) / R) * (((n : ℕ) : ℚ) / R)) =
      if a = b then (R : ℂ) ^ 2 else 0 := by
  have hR0 : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  split_ifs with h
  · simp [h, ech_zero, sq]
  · set t : ℚ := (((a : ℕ) : ℚ) - (b : ℕ)) / (R * R) with ht
    have hpow : ∀ n : ℕ, ech (t * n) = ech t ^ n := by
      intro n; simp only [ech, ← Complex.exp_nat_mul]; push_cast; ring_nf
    have h1 : ∀ n : Fin (R * R), ech ((((a : ℕ) : ℚ) / R - ((b : ℕ) : ℚ) / R) *
        (((n : ℕ) : ℚ) / R)) = ech t ^ (n : ℕ) := by
      intro n; rw [← hpow, ht]; congr 1; field_simp
    have hne : ech t ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := (ech_eq_one_iff _).1 h1
      rw [ht, div_eq_iff (mul_ne_zero hR0 hR0)] at hm
      have hm' : ((a : ℕ) : ℤ) - (b : ℕ) = m * ((R * R : ℕ) : ℤ) := by exact_mod_cast hm
      have ha := a.2
      have hb := b.2
      have : ((a : ℕ) : ℤ) - (b : ℕ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd (m := ((R * R : ℕ) : ℤ)) ⟨m, by rw [hm', mul_comm]⟩
          (by rw [abs_lt]; omega)
      exact h (Fin.ext (by omega))
    have hN : ech t ^ (R * R) = 1 := by
      rw [← hpow]
      exact (ech_eq_one_iff _).2 ⟨((a : ℕ) : ℤ) - (b : ℕ), by rw [ht]; push_cast; field_simp⟩
    simp only [h1]
    rw [Fin.sum_univ_eq_sum_range (fun n => ech t ^ n), geom_sum_eq hne, hN]; simp
end GlobalTheory.SW.FourierJ
