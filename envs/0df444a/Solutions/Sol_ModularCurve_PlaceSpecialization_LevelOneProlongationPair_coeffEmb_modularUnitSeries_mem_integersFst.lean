-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6fbe419a-0072-5166-b46b-cfc10e03ae01

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace Ws14Port

section MapRingHom
variable {R S : Type*} [Semiring R] [Semiring S]

def mapRingHom (φ : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map φ
  map_zero' := by ext n; simp
  map_one' := by ext n; simp
  map_add' x y := by ext n; simp
  map_mul' x y := HahnSeries.map_mul (f := (φ : R →ₙ+* S))

@[scoped simp]
theorem coeff_mapRingHom (φ : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (mapRingHom φ x).coeff n = φ (x.coeff n) := rfl

theorem mapRingHom_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (mapRingHom φ) := by
  intro x y h
  ext n
  exact hφ (congrArg (fun z => z.coeff n) h)
end MapRingHom

def intLaurentEmb : LaurentSeries ℤ →+* LaurentSeries ℚ := mapRingHom (Int.castRingHom ℚ)

theorem intLaurentEmb_injective : Function.Injective intLaurentEmb :=
  mapRingHom_injective Int.cast_injective

@[scoped simp]
theorem coeff_intLaurentEmb (f : LaurentSeries ℤ) (n : ℤ) :
    (intLaurentEmb f).coeff n = (f.coeff n : ℚ) := rfl

noncomputable def deltaSeriesZ : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

theorem intLaurentEmb_deltaSeriesZ : intLaurentEmb deltaSeriesZ = deltaSeries := by
  ext n
  simp only [coeff_intLaurentEmb, deltaSeriesZ, deltaSeries, HahnSeries.coeff_single_mul, one_mul]
  rcases lt_or_ge (n - (1 : ℤ)) 0 with hn | hn
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, Int.cast_zero]
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    rw [show n - (1 : ℤ) = (k : ℤ) by omega,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      dedekindEtaUnitQ, PowerSeries.coeff_map]
    rfl

theorem intLaurentEmb_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries ℤ) :
    intLaurentEmb (qExpand ℤ N f) = qExpand ℚ N (intLaurentEmb f) := by
  ext n
  simp only [coeff_intLaurentEmb]
  by_cases hdvd : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_intLaurentEmb]
  · rw [qExpand_coeff_of_not_dvd N _ hdvd, qExpand_coeff_of_not_dvd N _ hdvd, Int.cast_zero]

noncomputable def deltaSeriesZInv : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem deltaSeriesZ_mul_inv : deltaSeriesZ * deltaSeriesZInv = 1 := by
  have hη : HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit *
      HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv]; exact map_one _
  have hs : (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1 : LaurentSeries ℤ)
      = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul]; rfl
  unfold deltaSeriesZ deltaSeriesZInv
  rw [mul_mul_mul_comm, hs, hη, one_mul]

noncomputable def modularUnitSeriesZ (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  deltaSeriesZ * qExpand ℤ p deltaSeriesZInv

theorem intLaurentEmb_modularUnitSeriesZ (p : ℕ) [NeZero p] :
    intLaurentEmb (modularUnitSeriesZ p) = modularUnitSeries p := by
  have h1 : intLaurentEmb (qExpand ℤ p deltaSeriesZ) = deltaSeriesN p := by
    rw [intLaurentEmb_qExpand, intLaurentEmb_deltaSeriesZ]; rfl
  have hinv : intLaurentEmb (qExpand ℤ p deltaSeriesZInv) * deltaSeriesN p = 1 := by
    rw [← h1, ← map_mul, ← map_mul, mul_comm, deltaSeriesZ_mul_inv, map_one, map_one]
  rw [modularUnitSeriesZ, map_mul, intLaurentEmb_deltaSeriesZ, modularUnitSeries,
    ← one_mul (deltaSeriesN p)⁻¹, ← hinv, mul_assoc,
    mul_inv_cancel₀ (deltaSeriesN_ne_zero p), mul_one, mul_comm]

theorem modularUnitSeriesZ_ne_zero (p : ℕ) [NeZero p] : modularUnitSeriesZ p ≠ 0 := fun h0 => by
  have h := coeff_modularUnitSeries_self p
  rw [← intLaurentEmb_modularUnitSeriesZ, h0, map_zero, HahnSeries.coeff_zero] at h
  exact zero_ne_one h

theorem coeff_modularUnitSeriesZ_self (p : ℕ) [NeZero p] :
    (modularUnitSeriesZ p).coeff (1 - (p : ℤ)) = 1 := by
  have h := coeff_modularUnitSeries_self p
  rw [← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb] at h
  exact_mod_cast h

theorem coeff_modularUnitSeriesZ_of_lt (p : ℕ) [NeZero p] {k : ℤ} (hk : k < 1 - (p : ℤ)) :
    (modularUnitSeriesZ p).coeff k = 0 := by
  have h := coeff_modularUnitSeries_of_lt p hk
  rw [← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb] at h
  exact_mod_cast h

theorem coeff_map_modularUnitSeriesZ_self {S : Type*} [Semiring S] (φ : ℤ →+* S) (p : ℕ) [NeZero p] :
    (mapRingHom φ (modularUnitSeriesZ p)).coeff (1 - (p : ℤ)) = 1 := by
  rw [coeff_mapRingHom, coeff_modularUnitSeriesZ_self, map_one]

theorem coeff_map_modularUnitSeriesZ_of_lt {S : Type*} [Semiring S] (φ : ℤ →+* S) (p : ℕ) [NeZero p]
    {k : ℤ} (hk : k < 1 - (p : ℤ)) : (mapRingHom φ (modularUnitSeriesZ p)).coeff k = 0 := by
  rw [coeff_mapRingHom, coeff_modularUnitSeriesZ_of_lt p hk, map_zero]

theorem modularUnitSeriesZ_mul_qExpand_deltaSeriesZ (p : ℕ) [NeZero p] :
    modularUnitSeriesZ p * qExpand ℤ p deltaSeriesZ = deltaSeriesZ := by
  have hinv : qExpand ℤ p deltaSeriesZInv * qExpand ℤ p deltaSeriesZ = 1 := by
    rw [← map_mul, mul_comm, deltaSeriesZ_mul_inv, map_one]
  rw [modularUnitSeriesZ, mul_assoc, hinv, mul_one]

def modularUnitSeriesA (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] : LaurentSeries A :=
  mapRingHom (Int.castRingHom A) (modularUnitSeriesZ p)

theorem coeffMap_subtype_modularUnitSeriesA (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] :
    coeffMap A.subtype (modularUnitSeriesA A p) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) := by
  ext n
  rw [coeffMap_coeff, coeffEmb_coeff, ← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb,
    modularUnitSeriesA, coeff_mapRingHom, map_intCast]
  simp

theorem coeff_modularUnitSeriesA_self (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] :
    (modularUnitSeriesA A p).coeff (1 - (p : ℤ)) = 1 :=
  coeff_map_modularUnitSeriesZ_self _ p

theorem coeff_modularUnitSeriesA_of_lt (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p]
    {k : ℤ} (hk : k < 1 - (p : ℤ)) : (modularUnitSeriesA A p).coeff k = 0 :=
  coeff_map_modularUnitSeriesZ_of_lt _ p hk

end Ws14Port
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst.Ws14Port"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst.Ws14Port"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers,
      ∃ y : LaurentSeries A, coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)) ∧
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
  have hmem := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
    (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))
  have hy : coeffMap A.subtype (Ws14Port.modularUnitSeriesA A (1 * q)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [Ws14Port.coeffMap_subtype_modularUnitSeriesA]; exact hmem
  obtain ⟨h, hh⟩ := R.residue₁_coeffMap (Ws14Port.modularUnitSeriesA A (1 * q)) hy
  have e : (⟨coeffMap A.subtype (Ws14Port.modularUnitSeriesA A (1 * q)), hy⟩ : ↥(modularFunctionFieldBar (1 * q)))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)), hmem⟩ :=
    Subtype.ext (Ws14Port.coeffMap_subtype_modularUnitSeriesA A (1 * q))
  have h' : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)), hmem⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := e ▸ h
  refine ⟨h', Ws14Port.modularUnitSeriesA A (1 * q), Ws14Port.coeffMap_subtype_modularUnitSeriesA A (1 * q), ?_⟩
  have e' : (⟨⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)), hmem⟩, h'⟩ : R.R₁.integers)
      = ⟨⟨coeffMap A.subtype (Ws14Port.modularUnitSeriesA A (1 * q)), hy⟩, h⟩ := Subtype.ext e.symm
  rw [e']
  exact hh

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst (solution)
