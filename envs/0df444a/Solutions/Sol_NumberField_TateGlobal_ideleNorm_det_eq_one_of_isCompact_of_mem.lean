-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d05827bb-8632-5e2e-bb94-9efc0c7d6e45

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.TateGlobal

theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by

  have hcont : Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hmul : ∀ a b : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det (a * b)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det a) * ideleNorm F (Matrix.GeneralLinearGroup.det b) := by
    intro a b; rw [map_mul, ideleNorm_mul]
  have hpow : ∀ (n : ℕ), ideleNorm F (Matrix.GeneralLinearGroup.det (u ^ n)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u n, hmul, ih, ← pow_succ]

  obtain ⟨M, hM⟩ := (hU.image hcont).isBounded.bddAbove
  have hbd : ∀ g ∈ U, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M := fun g hg => hM ⟨g, hg, rfl⟩
  set x := ideleNorm F (Matrix.GeneralLinearGroup.det u) with hx
  have hxpos : 0 < x := ideleNorm_pos _

  have hup : ∀ n : ℕ, x ^ n ≤ M := fun n => by rw [← hpow]; exact hbd _ (U.pow_mem hu n)
  have hinv : ideleNorm F (Matrix.GeneralLinearGroup.det u⁻¹) = x⁻¹ := by
    have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (u * u⁻¹)) = 1 := by
      rw [mul_inv_cancel]; simp [NumberField.TateGlobal.ideleNorm]
    rw [hmul] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hpow' : ∀ n : ℕ, ideleNorm F (Matrix.GeneralLinearGroup.det (u⁻¹ ^ n)) = x⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u⁻¹ n, hmul, ih, hinv, ← pow_succ]
  have hdown : ∀ n : ℕ, x⁻¹ ^ n ≤ M := fun n => by
    rw [← hpow']; exact hbd _ (U.pow_mem (U.inv_mem hu) n)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have h1 : 1 < x⁻¹ := (one_lt_inv₀ hxpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    exact absurd (hdown n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hup n) (not_le.mpr hn)

end S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem (solution)
