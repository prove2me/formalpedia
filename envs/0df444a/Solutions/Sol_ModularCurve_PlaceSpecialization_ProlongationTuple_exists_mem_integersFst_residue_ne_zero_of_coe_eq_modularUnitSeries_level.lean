-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3fe8dc4b-fa39-5a52-bd51-8e4a6578d1c8

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularUnitIntegralModel

section MapRingHom
variable {R S : Type*} [Semiring R] [Semiring S]

private def mapRingHom (φ : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map φ
  map_zero' := by ext n; simp
  map_one' := by ext n; simp
  map_add' x y := by ext n; simp
  map_mul' x y := HahnSeries.map_mul (f := (φ : R →ₙ+* S))

@[scoped simp]
private theorem coeff_mapRingHom (φ : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (mapRingHom φ x).coeff n = φ (x.coeff n) := rfl

private theorem mapRingHom_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (mapRingHom φ) := by
  intro x y h
  ext n
  exact hφ (congrArg (fun z => z.coeff n) h)
end MapRingHom

private def intLaurentEmb : LaurentSeries ℤ →+* LaurentSeries ℚ := mapRingHom (Int.castRingHom ℚ)

private theorem intLaurentEmb_injective : Function.Injective intLaurentEmb :=
  mapRingHom_injective Int.cast_injective

@[scoped simp]
private theorem coeff_intLaurentEmb (f : LaurentSeries ℤ) (n : ℤ) :
    (intLaurentEmb f).coeff n = (f.coeff n : ℚ) := rfl

private noncomputable def deltaSeriesZ : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

private theorem intLaurentEmb_deltaSeriesZ : intLaurentEmb deltaSeriesZ = deltaSeries := by
  ext n
  simp only [coeff_intLaurentEmb, deltaSeriesZ, deltaSeries, HahnSeries.coeff_single_mul, one_mul]
  rcases lt_or_ge (n - (1 : ℤ)) 0 with hn | hn
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, Int.cast_zero]
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    rw [show n - (1 : ℤ) = (k : ℤ) by omega,
      HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      dedekindEtaUnitQ, PowerSeries.coeff_map]
    rfl

private theorem intLaurentEmb_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries ℤ) :
    intLaurentEmb (qExpand ℤ N f) = qExpand ℚ N (intLaurentEmb f) := by
  ext n
  simp only [coeff_intLaurentEmb]
  by_cases hdvd : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_intLaurentEmb]
  · rw [qExpand_coeff_of_not_dvd N _ hdvd, qExpand_coeff_of_not_dvd N _ hdvd, Int.cast_zero]

private noncomputable def deltaSeriesZInv : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

private theorem deltaSeriesZ_mul_inv : deltaSeriesZ * deltaSeriesZInv = 1 := by
  have hη : HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit *
      HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv]; exact map_one _
  have hs : (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1 : LaurentSeries ℤ)
      = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul]; rfl
  unfold deltaSeriesZ deltaSeriesZInv
  rw [mul_mul_mul_comm, hs, hη, one_mul]

private noncomputable def modularUnitSeriesZ (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  deltaSeriesZ * qExpand ℤ p deltaSeriesZInv

private theorem intLaurentEmb_modularUnitSeriesZ (p : ℕ) [NeZero p] :
    intLaurentEmb (modularUnitSeriesZ p) = modularUnitSeries p := by
  have h1 : intLaurentEmb (qExpand ℤ p deltaSeriesZ) = deltaSeriesN p := by
    rw [intLaurentEmb_qExpand, intLaurentEmb_deltaSeriesZ]; rfl
  have hinv : intLaurentEmb (qExpand ℤ p deltaSeriesZInv) * deltaSeriesN p = 1 := by
    rw [← h1, ← map_mul, ← map_mul, mul_comm, deltaSeriesZ_mul_inv, map_one, map_one]
  rw [modularUnitSeriesZ, map_mul, intLaurentEmb_deltaSeriesZ, modularUnitSeries,
    ← one_mul (deltaSeriesN p)⁻¹, ← hinv, mul_assoc,
    mul_inv_cancel₀ (deltaSeriesN_ne_zero p), mul_one, mul_comm]

private theorem modularUnitSeriesZ_ne_zero (p : ℕ) [NeZero p] : modularUnitSeriesZ p ≠ 0 := fun h0 => by
  have h := coeff_modularUnitSeries_self p
  rw [← intLaurentEmb_modularUnitSeriesZ, h0, map_zero, HahnSeries.coeff_zero] at h
  exact zero_ne_one h

private theorem coeff_modularUnitSeriesZ_self (p : ℕ) [NeZero p] :
    (modularUnitSeriesZ p).coeff (1 - (p : ℤ)) = 1 := by
  have h := coeff_modularUnitSeries_self p
  rw [← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb] at h
  exact_mod_cast h

private theorem coeff_modularUnitSeriesZ_of_lt (p : ℕ) [NeZero p] {k : ℤ} (hk : k < 1 - (p : ℤ)) :
    (modularUnitSeriesZ p).coeff k = 0 := by
  have h := coeff_modularUnitSeries_of_lt p hk
  rw [← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb] at h
  exact_mod_cast h

private theorem coeff_map_modularUnitSeriesZ_self {S : Type*} [Semiring S] (φ : ℤ →+* S) (p : ℕ) [NeZero p] :
    (mapRingHom φ (modularUnitSeriesZ p)).coeff (1 - (p : ℤ)) = 1 := by
  rw [coeff_mapRingHom, coeff_modularUnitSeriesZ_self, map_one]

private theorem coeff_map_modularUnitSeriesZ_of_lt {S : Type*} [Semiring S] (φ : ℤ →+* S) (p : ℕ) [NeZero p]
    {k : ℤ} (hk : k < 1 - (p : ℤ)) : (mapRingHom φ (modularUnitSeriesZ p)).coeff k = 0 := by
  rw [coeff_mapRingHom, coeff_modularUnitSeriesZ_of_lt p hk, map_zero]

private theorem modularUnitSeriesZ_mul_qExpand_deltaSeriesZ (p : ℕ) [NeZero p] :
    modularUnitSeriesZ p * qExpand ℤ p deltaSeriesZ = deltaSeriesZ := by
  have hinv : qExpand ℤ p deltaSeriesZInv * qExpand ℤ p deltaSeriesZ = 1 := by
    rw [← map_mul, mul_comm, deltaSeriesZ_mul_inv, map_one]
  rw [modularUnitSeriesZ, mul_assoc, hinv, mul_one]

private def modularUnitSeriesA (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] : LaurentSeries A :=
  mapRingHom (Int.castRingHom A) (modularUnitSeriesZ p)

private theorem coeffMap_subtype_modularUnitSeriesA (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] :
    coeffMap A.subtype (modularUnitSeriesA A p) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p) := by
  ext n
  rw [coeffMap_coeff, coeffEmb_coeff, ← intLaurentEmb_modularUnitSeriesZ, coeff_intLaurentEmb,
    modularUnitSeriesA, coeff_mapRingHom, map_intCast]
  simp

private theorem coeff_modularUnitSeriesA_self (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p] :
    (modularUnitSeriesA A p).coeff (1 - (p : ℤ)) = 1 :=
  coeff_map_modularUnitSeriesZ_self _ p

private theorem coeff_modularUnitSeriesA_of_lt (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [NeZero p]
    {k : ℤ} (hk : k < 1 - (p : ℤ)) : (modularUnitSeriesA A p).coeff k = 0 :=
  coeff_map_modularUnitSeriesZ_of_lt _ p hk

end ModularUnitIntegralModel
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level.ModularUnitIntegralModel"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level.ModularUnitIntegralModel"

open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple AlgebraicCurve IsLocalRing in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    ∃ h₁ : u ∈ R.R₁.integers,
      R.R₁.residue ⟨u, h₁⟩ ≠ 0 ∧
      ∃ y : LaurentSeries A, coeffMap A.subtype y = (u : LaurentSeries (AlgebraicClosure ℚ)) ∧
        ((R.R₁.residue ⟨u, h₁⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y ∧
        ((R.R₁.residue ⟨u, h₁⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := by

  set y : LaurentSeries A := ModularUnitIntegralModel.modularUnitSeriesA A q with hy_def
  have hyu : coeffMap A.subtype y = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hy_def, ModularUnitIntegralModel.coeffMap_subtype_modularUnitSeriesA, hu]
  have hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [hyu]; exact u.2
  obtain ⟨h, hh⟩ := R.residue₁_coeffMap y hy
  have e : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar (N * q))) = u :=
    Subtype.ext hyu
  have h₁ : u ∈ R.R₁.integers := e ▸ h
  have e' : (⟨u, h₁⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hy⟩, h⟩ := Subtype.ext e.symm
  have hres : ((R.R₁.residue ⟨u, h₁⟩ : modularFunctionFieldFullC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
    rw [e']; exact hh

  have hy1 : y.coeff (1 - (q : ℤ)) = 1 := ModularUnitIntegralModel.coeff_modularUnitSeriesA_self A q
  have hy0 : ∀ m : ℤ, m < 1 - (q : ℤ) → y.coeff m = 0 := fun m hm =>
    ModularUnitIntegralModel.coeff_modularUnitSeriesA_of_lt A q hm
  have hc1 : (coeffMap (IsLocalRing.residue A) y).coeff (1 - (q : ℤ)) = 1 := by
    rw [coeffMap_coeff, hy1, map_one]
  have hne : coeffMap (IsLocalRing.residue A) y ≠ 0 := fun h0 => by
    have := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (1 - (q : ℤ))) h0
    simp only [HahnSeries.coeff_zero] at this
    rw [hc1] at this
    exact one_ne_zero this
  refine ⟨h₁, ?_, y, hyu, hres, ?_⟩
  · intro h0
    apply hne
    rw [← hres, h0]
    rfl
  · rw [hres]
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [hc1]; exact one_ne_zero)) ?_
    by_contra hlt
    rw [not_le] at hlt
    have hz : (coeffMap (IsLocalRing.residue A) y).coeff
        (coeffMap (IsLocalRing.residue A) y).order = 0 := by
      rw [coeffMap_coeff, hy0 _ hlt, map_zero]
    exact hne (HahnSeries.coeff_order_eq_zero.mp hz)

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level (solution)
