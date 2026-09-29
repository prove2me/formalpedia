-- Prove2me | solution 1 for ModularCurve.residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/eb1b8052-3e1e-5324-8fc1-731de9c2e3e5

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField AlgebraicCurve

namespace LigozatUnitEngine

def deltaInt : LaurentSeries ℤ :=
  HahnSeries.ofPowerSeries ℤ ℤ (PowerSeries.X * dedekindEtaUnit)

def deltaInvInt : LaurentSeries ℤ :=
  HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem deltaInt_eq : deltaInt = HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit := by
  rw [deltaInt, map_mul, HahnSeries.ofPowerSeries_X]

theorem deltaInt_mul_deltaInvInt : deltaInt * deltaInvInt = 1 := by
  rw [deltaInt_eq, deltaInvInt, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul,
    dedekindEtaUnit_mul_inv, map_one, mul_one]
  simp

variable (p : ℕ) [Fact p.Prime]

def unitInt : LaurentSeries ℤ := deltaInt * qExpand ℤ p deltaInvInt

def unitInvInt : LaurentSeries ℤ := deltaInvInt * qExpand ℤ p deltaInt

theorem unitInt_mul_unitInvInt : unitInt p * unitInvInt p = 1 := by
  rw [unitInt, unitInvInt, mul_mul_mul_comm, deltaInt_mul_deltaInvInt, ← map_mul,
    mul_comm deltaInvInt, deltaInt_mul_deltaInvInt, map_one, mul_one]

section CoeffMap

variable {K : Type*} [CommRing K]

theorem coeffMap_deltaInt (f : ℤ →+* K) :
    coeffMap f deltaInt =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) := by
  rw [deltaInt, coeffMap_ofPowerSeries]

theorem coeffMap_deltaInt_mul_deltaInvInt (f : ℤ →+* K) :
    coeffMap f deltaInt * coeffMap f deltaInvInt = 1 := by
  rw [← map_mul, deltaInt_mul_deltaInvInt, map_one]

theorem coeffMap_unitInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) = coeffMap f deltaInt * qExpand K p (coeffMap f deltaInvInt) := by
  rw [unitInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInvInt p) = coeffMap f deltaInvInt * qExpand K p (coeffMap f deltaInt) := by
  rw [unitInvInt, map_mul, ModularCurve.coeffMap_qExpand]

theorem coeffMap_unitInt_mul_unitInvInt (f : ℤ →+* K) :
    coeffMap f (unitInt p) * coeffMap f (unitInvInt p) = 1 := by
  rw [← map_mul, unitInt_mul_unitInvInt, map_one]

theorem isUnit_coeffMap_unitInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInt p)) :=
  IsUnit.of_mul_eq_one _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem isUnit_coeffMap_unitInvInt (f : ℤ →+* K) : IsUnit (coeffMap f (unitInvInt p)) :=
  IsUnit.of_mul_eq_one_right _ (coeffMap_unitInt_mul_unitInvInt p f)

theorem coeffMap_unitInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInt p f).ne_zero

theorem coeffMap_unitInvInt_ne_zero [Nontrivial K] (f : ℤ →+* K) : coeffMap f (unitInvInt p) ≠ 0 :=
  (isUnit_coeffMap_unitInvInt p f).ne_zero

end CoeffMap

theorem coeffMap_rat_deltaInt : coeffMap (Int.castRingHom ℚ) deltaInt = deltaSeries := by
  rw [deltaInt_eq, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  rfl

theorem coeffMap_rat_deltaInvInt : coeffMap (Int.castRingHom ℚ) deltaInvInt = deltaSeries⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_deltaInt, coeffMap_deltaInt_mul_deltaInvInt]

theorem coeffMap_rat_unitInt : coeffMap (Int.castRingHom ℚ) (unitInt p) = modularUnitSeries p := by
  rw [coeffMap_unitInt, coeffMap_rat_deltaInt, coeffMap_rat_deltaInvInt, map_inv₀]
  rfl

theorem coeffMap_rat_unitInvInt :
    coeffMap (Int.castRingHom ℚ) (unitInvInt p) = (modularUnitSeries p)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← coeffMap_rat_unitInt, coeffMap_unitInt_mul_unitInvInt]

section CharP

variable {K : Type*} [CommRing K] [CharP K p]

theorem qExpand_coeffMap_eq_pow (f : ℤ →+* K) (x : LaurentSeries ℤ) :
    qExpand K p (coeffMap f x) = coeffMap f x ^ p := by
  rw [ModularCurve.pow_char_eq_map_frobenius_qExpand p (coeffMap f x)]
  change _ = coeffMap (frobenius K p) (qExpand K p (coeffMap f x))
  rw [ModularCurve.coeffMap_qExpand, coeffMap_coeffMap,
    coeffMap_congr (((frobenius K p).comp f).ext_int f)]

theorem coeffMap_unitInt_charP (f : ℤ →+* K) :
    coeffMap f (unitInt p) = coeffMap f deltaInt * coeffMap f deltaInvInt ^ p := by
  rw [coeffMap_unitInt, qExpand_coeffMap_eq_pow]

theorem coeffMap_unitInt_mul_pow_charP (f : ℤ →+* K) :
    coeffMap f (unitInt p) * coeffMap f deltaInt ^ (p - 1) = 1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h1 : coeffMap f deltaInt ^ (p - 1) * coeffMap f deltaInt = coeffMap f deltaInt ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  calc coeffMap f (unitInt p) * coeffMap f deltaInt ^ (p - 1)
      = coeffMap f deltaInvInt ^ p * (coeffMap f deltaInt ^ (p - 1) * coeffMap f deltaInt) := by
        rw [coeffMap_unitInt_charP]; ring
    _ = 1 := by
        rw [h1, ← mul_pow, mul_comm, coeffMap_deltaInt_mul_deltaInvInt, one_pow]

theorem coeffMap_unitInvInt_charP (f : ℤ →+* K) :
    coeffMap f (unitInvInt p) = coeffMap f deltaInt ^ (p - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h1 : coeffMap f deltaInt ^ p = coeffMap f deltaInt * coeffMap f deltaInt ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp]
  rw [coeffMap_unitInvInt, qExpand_coeffMap_eq_pow, h1, ← mul_assoc, mul_comm (coeffMap f deltaInvInt),
    coeffMap_deltaInt_mul_deltaInvInt, one_mul]

theorem coeffMap_unitInvInt_eq_pow (f : ℤ →+* K) :
    coeffMap f (unitInvInt p) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) ^ (p - 1) := by
  rw [coeffMap_unitInvInt_charP, coeffMap_deltaInt]

theorem coeffMap_unitInt_eq_inv {k : Type*} [Field k] [CharP k p] (f : ℤ →+* k) :
    coeffMap f (unitInt p) =
      (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) ^ (p - 1))⁻¹ := by
  rw [← coeffMap_deltaInt]
  exact (inv_eq_of_mul_eq_one_left (coeffMap_unitInt_mul_pow_charP p f)).symm

end CharP

end LigozatUnitEngine

namespace LigozatUnitBar

open LigozatUnitEngine

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk" => IsLocalRing.ResidueField A

abbrev ιA : LaurentSeries A →+* LaurentSeries ℚ̄ := coeffMap A.subtype

abbrev uA : LaurentSeries A := coeffMap (Int.castRingHom A) (unitInt p)

abbrev uInvA : LaurentSeries A := coeffMap (Int.castRingHom A) (unitInvInt p)

theorem coeffEmb_coeffMap_int (x : LaurentSeries ℤ) :
    coeffEmb ℚ̄ (coeffMap (Int.castRingHom ℚ) x) = ιA A (coeffMap (Int.castRingHom A) x) := by
  rw [coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) x

theorem coeffEmb_unit : coeffEmb ℚ̄ (modularUnitSeries p) = ιA A (uA p A) := by
  rw [← coeffMap_rat_unitInt, coeffEmb_coeffMap_int]

theorem coeffEmb_unit_inv : (coeffEmb ℚ̄ (modularUnitSeries p))⁻¹ = ιA A (uInvA p A) := by
  rw [← map_inv₀, ← coeffMap_rat_unitInvInt, coeffEmb_coeffMap_int]

theorem coeffEmb_C_mul (c : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb ℚ̄ (HahnSeries.C c * x) = HahnSeries.C (algebraMap ℚ ℚ̄ c) * coeffEmb ℚ̄ x := by
  rw [map_mul, HahnSeries.C_apply, HahnSeries.C_apply, coeffEmb, coeffMap_single]

theorem residue_comp_int : (IsLocalRing.residue A).comp (Int.castRingHom A) = Int.castRingHom kk :=
  RingHom.ext_int _ _

theorem charP_of_liesOverPrime (hA : A.LiesOverPrime p) : CharP kk p := by
  have hp : ((p : A) : ℚ̄) ∈ A.nonunits := by
    have : ((p : A) : ℚ̄) = (p : ℚ̄) := map_natCast A.subtype p
    rw [this]; exact hA
  have hmax : (p : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hp
  have h0 : (p : kk) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

end LigozatUnitBar

namespace LigozatUnitSS

open LigozatUnitEngine LigozatUnitBar

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * p))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldFullC (IsLocalRing.ResidueField A) N

set_option synthInstance.maxHeartbeats 1600000 in
theorem main (hp : 5 ≤ p) (hA : A.LiesOverPrime p)
    (hmem : modularUnitSeries p ∈ modularFunctionFieldFull (N * p))
    (R₀ : RegularProlongation A FF Fb)
    (h₀ : ∀ (y : LaurentSeries A) (hy : ιA A y ∈ FF),
        ∃ hint : (⟨ιA A y, hy⟩ : FF) ∈ R₀.integers,
          ((R₀.residue ⟨_, hint⟩ : Fb) : LaurentSeries kk) = coeffMap (IsLocalRing.residue A) y)
    [DecidableEq kk] (S₀ : Finset kk) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p kk) :
    ∃ hu₀ : (⟨coeffEmb ℚ̄ (modularUnitSeries p), coeffEmb_mem_laurentBaseChange ℚ̄ hmem⟩ : FF)
        ∈ R₀.integers,
      (⟨coeffEmb ℚ̄ (modularUnitSeries p), coeffEmb_mem_laurentBaseChange ℚ̄ hmem⟩ : FF)⁻¹
        ∈ R₀.integers ∧
      ((R₀.residue ⟨_, hu₀⟩ : Fb) : LaurentSeries kk) =
        ∏ a ∈ S₀, (jqModC kk - HahnSeries.C a) ^ (12 / jWidth a) := by
  haveI : CharP kk p := charP_of_liesOverPrime p A hA
  haveI : IsAlgClosed kk := ValuationSubring.isAlgClosed_residueField A
  set ub : FF := ⟨coeffEmb ℚ̄ (modularUnitSeries p), coeffEmb_mem_laurentBaseChange ℚ̄ hmem⟩ with hub_def
  have hy : ιA A (uA p A) ∈ FF := by rw [← coeffEmb_unit]; exact ub.2
  have hy' : ιA A (uInvA p A) ∈ FF := by rw [← coeffEmb_unit_inv]; exact inv_mem ub.2
  obtain ⟨hint, hres⟩ := h₀ (uA p A) hy
  obtain ⟨hint', -⟩ := h₀ (uInvA p A) hy'
  have hub_eq : ub = ⟨ιA A (uA p A), hy⟩ := Subtype.ext (coeffEmb_unit p A)
  have hubinv_eq : ub⁻¹ = ⟨ιA A (uInvA p A), hy'⟩ :=
    Subtype.ext (by rw [IntermediateField.coe_inv]; exact coeffEmb_unit_inv p A)
  have hu₀ : ub ∈ R₀.integers := by rw [hub_eq]; exact hint
  have hu₀inv : ub⁻¹ ∈ R₀.integers := by rw [hubinv_eq]; exact hint'
  refine ⟨hu₀, hu₀inv, ?_⟩
  have : (⟨ub, hu₀⟩ : R₀.integers) = ⟨_, hint⟩ := Subtype.ext hub_eq
  rw [this, hres, coeffMap_coeffMap, residue_comp_int, coeffMap_unitInt_eq_inv]
  exact inv_eq_of_mul_eq_one_right
    (ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one p hp kk S₀ hS₀)

end LigozatUnitSS

end

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hp : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (R₀ : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
      (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))

    (h₀ : ∀ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
        (((R₀.residue ⟨_, hint⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.coeffMap (IsLocalRing.residue A) y)
    [DecidableEq (IsLocalRing.ResidueField A)] (S₀ : Finset (IsLocalRing.ResidueField A))
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ModularCurve.ssJSet p (IsLocalRing.ResidueField A)) :
    ∃ hu₀ : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p))⁻¹ ∈ R₀.integers ∧
      (((R₀.residue ⟨_, hu₀⟩ :
          ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        ∏ a ∈ S₀, (ModularCurve.jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^
          (12 / ModularCurve.jWidth a) :=
  LigozatUnitSS.main N p A hp hA hmem R₀ h₀ S₀ hS₀

end S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
end P2MW
export P2MW.S_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation (solution)
