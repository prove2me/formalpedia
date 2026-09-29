-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_coeffEmb_modularUnitSeries_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2c36c4bf-5d4b-5810-9123-8f171eba7d77

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve IsLocalRing

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h', y, hy, hres⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst R
  have hq : ((1 * q : ℕ) : ℤ) = (q : ℤ) := by rw [one_mul]

  have hcoeff : ∀ n : ℤ, ((y.coeff n : A) : AlgebraicClosure ℚ)
      = algebraMap ℚ (AlgebraicClosure ℚ) ((modularUnitSeries (1 * q)).coeff n) := fun n => by
    have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff n) hy
    simp only [coeffMap_coeff, coeffEmb_coeff] at this
    exact this
  have hc : (modularUnitSeries (1 * q)).coeff (1 - (q : ℤ)) = 1 := by
    have := coeff_modularUnitSeries_self (1 * q)
    rwa [hq] at this
  have hy1 : y.coeff (1 - (q : ℤ)) = 1 := by
    apply Subtype.ext
    rw [OneMemClass.coe_one, hcoeff, hc, map_one]
  have hy0 : ∀ k : ℤ, k < 1 - (q : ℤ) → y.coeff k = 0 := fun k hk => by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, hcoeff, coeff_modularUnitSeries_of_lt (1 * q) (by rw [hq]; exact hk),
      map_zero]

  have hres' : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := hres
  have hc1 : (coeffMap (IsLocalRing.residue A) y).coeff (1 - (q : ℤ)) = 1 := by
    rw [coeffMap_coeff, hy1, map_one]
  intro h0
  have : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) = 0 := by rw [h0]; rfl
  rw [hres'] at this
  have h2 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (1 - (q : ℤ))) this
  simp only [HahnSeries.coeff_zero] at h2
  rw [hc1] at h2
  exact one_ne_zero h2

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero (solution)
