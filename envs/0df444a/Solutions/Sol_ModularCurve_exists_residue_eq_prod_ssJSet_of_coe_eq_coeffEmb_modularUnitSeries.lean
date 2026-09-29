-- Prove2me | solution 1 for ModularCurve.exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/acc661a6-a9c7-58e3-ad0b-20ad0c6bc9f9

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField AlgebraicCurve

namespace ResidueHalfSol

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

variable {K S : Type*} [CommRing K] [CommRing S]

theorem coeffMap_ofPowerSeries (f : K →+* S) (x : PowerSeries K) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ K x) = HahnSeries.ofPowerSeries ℤ S (x.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_deltaInt (f : ℤ →+* K) :
    coeffMap f deltaInt = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) := by
  rw [deltaInt, coeffMap_ofPowerSeries]

theorem coeffMap_deltaInt_eq (f : ℤ →+* K) :
    coeffMap f deltaInt = HahnSeries.single 1 1 * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f dedekindEtaUnit) := by
  rw [deltaInt_eq, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]

theorem coeffMap_deltaInvInt_eq (f : ℤ →+* K) :
    coeffMap f deltaInvInt =
      HahnSeries.single (-1) 1 * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map f dedekindEtaUnitInv) := by
  rw [deltaInvInt, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]

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

theorem coeffMap_unitInt_eq_deltaInv_pow (f : ℤ →+* K) :
    coeffMap f (unitInt p) = coeffMap f deltaInvInt ^ (p - 1) := by
  have h := coeffMap_unitInt_mul_pow_charP p f
  calc coeffMap f (unitInt p)
      = coeffMap f (unitInt p) * (coeffMap f deltaInt ^ (p - 1) * coeffMap f deltaInvInt ^ (p - 1)) := by
        rw [← mul_pow, coeffMap_deltaInt_mul_deltaInvInt, one_pow, mul_one]
    _ = coeffMap f deltaInvInt ^ (p - 1) := by rw [← mul_assoc, h, one_mul]

theorem coeffMap_unitInt_eq_inv {k : Type*} [Field k] [CharP k p] (f : ℤ →+* k) :
    coeffMap f (unitInt p) =
      (HahnSeries.ofPowerSeries ℤ k (PowerSeries.map f (PowerSeries.X * dedekindEtaUnit)) ^ (p - 1))⁻¹ := by
  rw [← coeffMap_deltaInt]
  exact (inv_eq_of_mul_eq_one_left (coeffMap_unitInt_mul_pow_charP p f)).symm

end CharP

section Orders

variable {k : Type*} [Field k]

theorem order_eq_of_coeff (x : LaurentSeries k) (m : ℤ) (h1 : x.coeff m ≠ 0) (h2 : ∀ j < m, x.coeff j = 0) :
    x.order = m := by
  have hne : x ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  rw [not_le] at hlt
  exact hne (HahnSeries.coeff_order_eq_zero.mp (h2 _ hlt))

theorem coeff_ofPowerSeries_zero (U : PowerSeries k) :
    (HahnSeries.ofPowerSeries ℤ k U).coeff 0 = PowerSeries.constantCoeff U := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff]

theorem order_ofPowerSeries_of_constantCoeff_ne_zero (U : PowerSeries k) (hU : PowerSeries.constantCoeff U ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ k U).order = 0 := by
  refine order_eq_of_coeff _ 0 ?_ fun j hj => ModularCurve.ofPowerSeries_coeff_of_neg U hj
  rwa [coeff_ofPowerSeries_zero]

theorem ofPowerSeries_ne_zero_of_constantCoeff_ne_zero (U : PowerSeries k) (hU : PowerSeries.constantCoeff U ≠ 0) :
    HahnSeries.ofPowerSeries ℤ k U ≠ 0 := by
  intro h
  apply hU
  rw [← coeff_ofPowerSeries_zero, h, HahnSeries.coeff_zero]

theorem constantCoeff_map_dedekindEtaUnit (f : ℤ →+* k) :
    PowerSeries.constantCoeff (PowerSeries.map f dedekindEtaUnit) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_dedekindEtaUnit, map_one]

theorem order_coeffMap_deltaInt (f : ℤ →+* k) : (coeffMap f deltaInt).order = 1 := by
  have hU : PowerSeries.constantCoeff (PowerSeries.map f dedekindEtaUnit) ≠ 0 := by
    rw [constantCoeff_map_dedekindEtaUnit]; exact one_ne_zero
  rw [coeffMap_deltaInt_eq, HahnSeries.order_mul (by simp) (ofPowerSeries_ne_zero_of_constantCoeff_ne_zero _ hU),
    HahnSeries.order_single one_ne_zero, order_ofPowerSeries_of_constantCoeff_ne_zero _ hU, add_zero]

theorem coeffMap_deltaInt_ne_zero {K : Type*} [CommRing K] [Nontrivial K] (f : ℤ →+* K) : coeffMap f deltaInt ≠ 0 :=
  (IsUnit.of_mul_eq_one _ (coeffMap_deltaInt_mul_deltaInvInt f)).ne_zero

theorem coeff_jqModC_neg_one' : (jqModC k).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, show (-1 : ℤ) - -1 = 0 from by ring, coeff_ofPowerSeries_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem coeff_jqModC_of_lt {i : ℤ} (hi : i < -1) : (jqModC k).coeff i = 0 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul]
  exact ModularCurve.ofPowerSeries_coeff_of_neg _ (by omega)

theorem order_jqModC_sub_C (a : k) : (jqModC k - HahnSeries.C a).order = -1 := by
  refine order_eq_of_coeff _ _ ?_ fun j hj => ?_
  · rw [HahnSeries.coeff_sub, coeff_jqModC_neg_one', HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num), sub_zero]
    exact one_ne_zero
  · rw [HahnSeries.coeff_sub, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega), sub_zero]
    exact coeff_jqModC_of_lt hj

theorem jqModC_sub_C_ne_zero (a : k) : jqModC k - HahnSeries.C a ≠ 0 := by
  intro h
  have := order_jqModC_sub_C a
  rw [h, HahnSeries.order_zero] at this
  norm_num at this

theorem order_prod {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries k) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).order = ∑ i ∈ s, (f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      HahnSeries.order_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem sum_eq_of_pow_mul_prod_eq_one (f : ℤ →+* k) (S₀ : Finset k) (n : k → ℕ)
    (h : coeffMap f deltaInt ^ (p - 1) * ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ n a = 1) :
    ∑ a ∈ S₀, n a = p - 1 := by
  have hP0 : ∀ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ n a ≠ 0 := fun a _ => pow_ne_zero _ (jqModC_sub_C_ne_zero a)
  have hord := congrArg HahnSeries.order h
  rw [HahnSeries.order_one, HahnSeries.order_mul (pow_ne_zero _ (coeffMap_deltaInt_ne_zero f)) (Finset.prod_ne_zero_iff.mpr hP0),
    HahnSeries.order_pow, order_coeffMap_deltaInt, order_prod _ _ hP0] at hord
  have hsum : ∑ i ∈ S₀, ((jqModC k - HahnSeries.C i) ^ n i).order = -(∑ i ∈ S₀, (n i : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [HahnSeries.order_pow, order_jqModC_sub_C, nsmul_eq_mul, mul_neg_one]
  rw [hsum, nsmul_eq_mul, mul_one] at hord
  have h1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have : ((∑ i ∈ S₀, n i : ℕ) : ℤ) = ((p - 1 : ℕ) : ℤ) := by push_cast [h1] at hord ⊢; linarith
  exact_mod_cast this

end Orders

section Residue

variable {k : Type*} [Field k] [CharP k p]

theorem coeffMap_unitInt_eq_prod_of_five_le [IsAlgClosed k] [DecidableEq k] (hp : 5 ≤ p) (S₀ : Finset k)
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p k) :
    coeffMap (Int.castRingHom k) (unitInt p) = ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ (12 / jWidth a) ∧
      ∑ a ∈ S₀, 12 / jWidth a = p - 1 := by
  have hD := ModularCurve.delta_pow_mul_prod_jqModC_sub_pow_eq_one p hp k S₀ hS₀
  refine ⟨?_, sum_eq_of_pow_mul_prod_eq_one p (Int.castRingHom k) S₀ (fun a => 12 / jWidth a) ?_⟩
  · rw [coeffMap_unitInt_eq_inv]
    exact inv_eq_of_mul_eq_one_right hD
  · rw [coeffMap_deltaInt]; exact hD

theorem cast_240_eq_zero_of_lt_five (hp : p < 5) : ((240 : ℤ) : k) = 0 := by
  have hprime : p.Prime := Fact.out
  have hdvd : p ∣ 240 := by
    have h2 := hprime.two_le
    interval_cases p
    · norm_num
    · norm_num
    · exact absurd hprime (by decide)
  obtain ⟨c, hc⟩ := hdvd
  have : ((240 : ℕ) : k) = 0 := by rw [hc, Nat.cast_mul, CharP.cast_eq_zero k p, zero_mul]
  exact_mod_cast this

theorem jqModC_eq_coeffMap_deltaInvInt_of_lt_five (hp : p < 5) :
    jqModC k = coeffMap (Int.castRingHom k) deltaInvInt := by
  set f := Int.castRingHom k with hf
  have hE4 : PowerSeries.map f eisenstein4 = 1 := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_one, eisenstein4, PowerSeries.coeff_mk]
    split_ifs with hn
    · rw [map_one]
    · rw [map_mul, show f 240 = ((240 : ℤ) : k) from rfl, cast_240_eq_zero_of_lt_five p hp, zero_mul]
  have h1 : PowerSeries.map f jNum = PowerSeries.map f dedekindEtaUnitInv := by
    rw [jNum, map_mul, map_pow, hE4, one_pow, one_mul]
  rw [jqModC, ← hf, h1, coeffMap_deltaInvInt_eq]

theorem coeffMap_unitInt_eq_pow_of_lt_five (hp : p < 5) :
    coeffMap (Int.castRingHom k) (unitInt p) = ∏ a ∈ ({0} : Finset k), (jqModC k - HahnSeries.C a) ^ (p - 1) := by
  rw [Finset.prod_singleton, map_zero, sub_zero, jqModC_eq_coeffMap_deltaInvInt_of_lt_five p hp,
    coeffMap_unitInt_eq_deltaInv_pow]

theorem mem_singleton_zero_iff_mem_ssJSet_of_lt_five [IsAlgClosed k] [DecidableEq k] (hp : p < 5) (a : k) :
    a ∈ ({0} : Finset k) ↔ a ∈ ssJSet p k := by
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ModularCurve.zero_mem_ssJSet_of_lt_five hp
  · intro ha
    have hprime : p.Prime := Fact.out
    have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p ha
    have h2 := hprime.two_le
    interval_cases p
    · exact ModularCurve.eq_zero_of_mem_ssJSet_two a ha hpow
    · exact ModularCurve.eq_zero_of_mem_ssJSet_three a ha hpow
    · exact absurd hprime (by decide)

theorem exists_coeffMap_unitInt_eq_prod [IsAlgClosed k] [DecidableEq k] :
    ∃ (S₀ : Finset k) (n : k → ℕ), (∀ a, a ∈ S₀ ↔ a ∈ ssJSet p k) ∧ (∀ a ∈ S₀, 0 < n a) ∧
      (∑ a ∈ S₀, n a = p - 1) ∧
      coeffMap (Int.castRingHom k) (unitInt p) = ∏ a ∈ S₀, (jqModC k - HahnSeries.C a) ^ n a := by
  rcases le_or_gt 5 p with hp | hp
  · set S₀ := (ModularCurve.ssJSet_finite p k).toFinset with hS₀def
    have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet p k := fun a => Set.Finite.mem_toFinset _
    obtain ⟨hprod, hsum⟩ := coeffMap_unitInt_eq_prod_of_five_le p hp S₀ hS₀
    exact ⟨S₀, fun a => 12 / jWidth a, hS₀, fun a _ => Nat.div_pos (Nat.le_of_dvd (by norm_num) (
      (jWidth_dvd_six a).trans (by norm_num))) (jWidth_pos a), hsum, hprod⟩
  · have hprime : p.Prime := Fact.out
    refine ⟨{0}, fun _ => p - 1, mem_singleton_zero_iff_mem_ssJSet_of_lt_five p hp, fun a _ => ?_, ?_,
      coeffMap_unitInt_eq_pow_of_lt_five p hp⟩
    · exact Nat.sub_pos_of_lt hprime.one_lt
    · rw [Finset.sum_singleton]

end Residue

section AForms

variable (A : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem coeffEmb_coeffMap_int (x : LaurentSeries ℤ) :
    coeffEmb ℚ̄ (coeffMap (Int.castRingHom ℚ) x) = coeffMap A.subtype (coeffMap (Int.castRingHom A) x) := by
  rw [coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) x

theorem coeffEmb_modularUnitSeries :
    coeffEmb ℚ̄ (modularUnitSeries p) = coeffMap A.subtype (coeffMap (Int.castRingHom A) (unitInt p)) := by
  rw [← coeffMap_rat_unitInt, coeffEmb_coeffMap_int]

theorem coeffEmb_modularUnitSeries_inv :
    (coeffEmb ℚ̄ (modularUnitSeries p))⁻¹ = coeffMap A.subtype (coeffMap (Int.castRingHom A) (unitInvInt p)) := by
  rw [← map_inv₀, ← coeffMap_rat_unitInvInt, coeffEmb_coeffMap_int]

theorem residue_comp_int :
    (IsLocalRing.residue A).comp (Int.castRingHom A) = Int.castRingHom (IsLocalRing.ResidueField A) :=
  RingHom.ext_int _ _

end AForms

section Main

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem coe_algebraMap_intermediateField {κ : Type*} [Field κ] (Fb : IntermediateField κ (LaurentSeries κ)) (a : κ) :
    ((algebraMap κ ↥Fb a : ↥Fb) : LaurentSeries κ) = HahnSeries.C a := by
  change algebraMap κ (LaurentSeries κ) a = HahnSeries.C a
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem main
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring ℚ̄) [CharP (IsLocalRing.ResidueField ↥A) p]
    (F : IntermediateField ℚ̄ (LaurentSeries ℚ̄))
    (Fb : IntermediateField (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)))
    (R : RegularProlongation A ↥F ↥Fb)
    (hR : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ F),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥F) ∈ R.integers,
        ((R.residue ⟨_, h⟩ : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (G : ↥F) (hG : ((G : ↥F) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (modularUnitSeries p)) :
    ∃ (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (n : IsLocalRing.ResidueField ↥A → ℕ) (hG₁ : G ∈ R.integers),
      G⁻¹ ∈ R.integers ∧
      (∀ a, a ∈ S₀ ↔ a ∈ @ssJSet p (IsLocalRing.ResidueField ↥A) _ (Classical.decEq _)) ∧ (∀ a ∈ S₀, 0 < n a) ∧
      (∑ a ∈ S₀, n a = p - 1) ∧
      ((R.residue ⟨G, hG₁⟩ : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        ∏ a ∈ S₀, (jqModC (IsLocalRing.ResidueField ↥A) - HahnSeries.C a) ^ n a ∧
      ∀ xb : ↥Fb, ((xb : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A) →
        R.residue ⟨G, hG₁⟩ = ∏ a ∈ S₀, (xb - algebraMap (IsLocalRing.ResidueField ↥A) ↥Fb a) ^ n a := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  set uA : LaurentSeries ↥A := coeffMap (Int.castRingHom A) (unitInt p) with huA
  set uInvA : LaurentSeries ↥A := coeffMap (Int.castRingHom A) (unitInvInt p) with huInvA
  have hy : coeffMap A.subtype uA ∈ F := by
    rw [huA, ← coeffEmb_modularUnitSeries, ← hG]; exact G.2
  have hy' : coeffMap A.subtype uInvA ∈ F := by
    rw [huInvA, ← coeffEmb_modularUnitSeries_inv, ← hG, ← IntermediateField.coe_inv]; exact (G⁻¹).2
  obtain ⟨hint, hres⟩ := hR uA hy
  obtain ⟨hint', -⟩ := hR uInvA hy'
  have hG_eq : G = ⟨coeffMap A.subtype uA, hy⟩ :=
    Subtype.ext (by change (G : LaurentSeries ℚ̄) = coeffMap A.subtype uA; rw [hG, huA, coeffEmb_modularUnitSeries])
  have hGinv_eq : G⁻¹ = ⟨coeffMap A.subtype uInvA, hy'⟩ :=
    Subtype.ext (by
      change ((G⁻¹ : ↥F) : LaurentSeries ℚ̄) = coeffMap A.subtype uInvA
      rw [IntermediateField.coe_inv, hG, huInvA, coeffEmb_modularUnitSeries_inv])
  have hG₁ : G ∈ R.integers := by rw [hG_eq]; exact hint
  have hG₁inv : G⁻¹ ∈ R.integers := by rw [hGinv_eq]; exact hint'

  obtain ⟨S₀, n, hS₀, hpos, hsum, hprod⟩ :=
    @exists_coeffMap_unitInt_eq_prod p _ (IsLocalRing.ResidueField ↥A) _ _ _ (Classical.decEq _)
  have hresG : ((R.residue ⟨G, hG₁⟩ : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      ∏ a ∈ S₀, (jqModC (IsLocalRing.ResidueField ↥A) - HahnSeries.C a) ^ n a := by
    have : (⟨G, hG₁⟩ : R.integers) = ⟨_, hint⟩ := Subtype.ext hG_eq
    rw [this, hres, huA, coeffMap_coeffMap, residue_comp_int, hprod]
  refine ⟨S₀, n, hG₁, hG₁inv, hS₀, hpos, hsum, hresG, fun xb hxb => ?_⟩

  apply Subtype.ext
  rw [hresG]
  simp only [SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, hxb,
    coe_algebraMap_intermediateField]

end Main

end ResidueHalfSol

end

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField ↥A) p]
    (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (Fb : IntermediateField (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)))
    (R : AlgebraicCurve.RegularProlongation A ↥F ↥Fb)

    (hR : ∀ (y : LaurentSeries ↥A) (hy : ModularCurve.coeffMap A.subtype y ∈ F),
      ∃ h : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ↥F) ∈ R.integers,
        ((R.residue ⟨_, h⟩ : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥A) y)
    (G : ↥F)
    (hG : ((G : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p)) :
    ∃ (S₀ : Finset (IsLocalRing.ResidueField ↥A)) (n : IsLocalRing.ResidueField ↥A → ℕ) (hG₁ : G ∈ R.integers),
      G⁻¹ ∈ R.integers ∧
      (∀ a, a ∈ S₀ ↔ a ∈ @ModularCurve.ssJSet p (IsLocalRing.ResidueField ↥A) _ (Classical.decEq _)) ∧
      (∀ a ∈ S₀, 0 < n a) ∧ (∑ a ∈ S₀, n a = p - 1) ∧
      ((R.residue ⟨G, hG₁⟩ : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        ∏ a ∈ S₀, (ModularCurve.jqModC (IsLocalRing.ResidueField ↥A) - HahnSeries.C a) ^ n a ∧
      ∀ xb : ↥Fb, ((xb : ↥Fb) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField ↥A) →
        R.residue ⟨G, hG₁⟩ = ∏ a ∈ S₀, (xb - algebraMap (IsLocalRing.ResidueField ↥A) ↥Fb a) ^ n a :=
  ResidueHalfSol.main p A F Fb R hR G hG

end S_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries
end P2MW
export P2MW.S_ModularCurve_exists_residue_eq_prod_ssJSet_of_coe_eq_coeffEmb_modularUnitSeries (solution)
