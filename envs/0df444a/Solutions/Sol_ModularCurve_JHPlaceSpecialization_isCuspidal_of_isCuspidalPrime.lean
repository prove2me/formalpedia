-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isCuspidal_of_isCuspidalPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2481fcfd-3602-5085-90d3-9b4443e932b0

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open scoped MatrixGroups

noncomputable section

namespace Ws49
namespace CuspPrime

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_and_mem_maximalIdeal_of_ord_pos {g : F} (hg0 : g ≠ 0) (h : 0 < v.ord g) :
    ∃ hg : g ∈ v.toValuationSubring, (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
  ⟨v.mem_toValuationSubring_of_ord_nonneg_alt hg0 h.le, (v.mem_maximalIdeal_iff_ord_pos hg0 _).mpr h⟩

theorem hasValue_of_ord_sub_pos {g : F} {a : K} (h0 : g - algebraMap K F a ≠ 0) (h : 0 < v.ord (g - algebraMap K F a)) :
    v.HasValue g a := by
  obtain ⟨hmem, hmax⟩ := mem_and_mem_maximalIdeal_of_ord_pos v h0 h
  have hc : algebraMap K F a ∈ v.toValuationSubring := (algebraMap K v.toValuationSubring a).2
  have hg : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F a) + algebraMap K F a := by ring
    rw [this]; exact add_mem hmem hc
  refine ⟨hg, ?_⟩
  have hdiff : (⟨g, hg⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring a = ⟨g - algebraMap K F a, hmem⟩ :=
    Subtype.ext rfl
  have hz : residue v.toValuationSubring (⟨g, hg⟩ - algebraMap K v.toValuationSubring a) = 0 := by
    rw [hdiff]; exact (residue_eq_zero_iff _).mpr hmax
  rw [map_sub, sub_eq_zero] at hz
  rw [hz]
  exact v.residue_algebraMap a

theorem ord_sub_pos_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (h0 : g - algebraMap K F a ≠ 0) :
    0 < v.ord (g - algebraMap K F a) := by
  have hc : algebraMap K F a ∈ v.toValuationSubring := (algebraMap K v.toValuationSubring a).2
  have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem h.mem hc
  refine (v.mem_maximalIdeal_iff_ord_pos h0 hmem).mp ?_
  rw [← residue_eq_zero_iff]
  have hdiff : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring a :=
    Subtype.ext rfl
  rw [hdiff, map_sub, h.residue_eq, v.residue_algebraMap, sub_self]

end PlaceFacts

section Poly

theorem ringHom_int_poly_ext {S : Type*} [CommRing S] (f g : ℤ[X] →+* S) (h : f X = g X) : f = g :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) h

theorem map_eval₂_aeval {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (Φ : Polynomial ℤ[X]) (x y : S) :
    φ (Φ.eval₂ (aeval (R := ℤ) x).toRingHom y) = Φ.eval₂ (aeval (R := ℤ) (φ x)).toRingHom (φ y) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply ringHom_int_poly_ext
  simp

theorem isIntegral_of_eval₂_aeval_eq_zero {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (Φ : Polynomial ℤ[X]) (hΦ : Φ.Monic)
    (r : R) (y : S) (h : Φ.eval₂ (aeval (R := ℤ) (algebraMap R S r)).toRingHom y = 0) : IsIntegral R y := by
  refine ⟨Φ.map (aeval (R := ℤ) r).toRingHom, hΦ.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap R S).comp (aeval (R := ℤ) r).toRingHom = (aeval (R := ℤ) (algebraMap R S r)).toRingHom := by
    apply ringHom_int_poly_ext
    simp
  rw [this]
  exact h

end Poly

section Inputs

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

theorem neZero_p : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] neZero_p

omit [NeZero M] in
theorem qExpand_congr {R : Type*} [CommRing R] {n m : ℕ} (h : n = m) [NeZero n] [NeZero m] (f : LaurentSeries R) :
    qExpand R n f = qExpand R m f := by subst h; rfl

include hpM in

theorem gammaH_le_inf : CohCarrier.GammaH M H ≤ CohCarrier.GammaH 1 ⊤ ⊓ CongruenceSubgroup.Gamma0 (1 * p) := by
  refine le_inf ?_ ?_
  · intro γ _
    rw [CohCarrier.GammaH_top, CongruenceSubgroup.Gamma0_mem]
    exact Subsingleton.elim _ _
  · intro γ hγ
    have h0 : γ ∈ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H hγ
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [one_mul]
    have hdvd : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ((Int.natCast_dvd_natCast.mpr hpM).trans hdvd)

include hpM in

theorem exists_coe_eq_qExpand_jqModC :
    ∃ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
  have hp : p.Prime := Fact.out
  have h1 : qExpand ℚ p (jqModC ℚ) ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH 1 ⊤ ⊓ CongruenceSubgroup.Gamma0 (1 * p)) :=
    ModularCurve.qExpand_jqModC_mem_qExpFunctionFieldC_gammaH_inf_gamma0_mul ℚ 1 p
      (by rw [one_mul]; exact_mod_cast hp.ne_zero) (fun h => hp.ne_one (Nat.dvd_one.mp h)) ⊤
  have h2 : qExpand ℚ p (jqModC ℚ) ∈ xHFunctionField M H := qExpFunctionFieldC_mono ℚ (gammaH_le_inf p M H hpM) h1
  refine ⟨⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (jqModC ℚ)), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h2⟩, ?_⟩
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (jqModC ℚ)) = _
  rw [coeffEmb, coeffMap_qExpand, coeffMap_jqModC]

theorem modular_relation (data : ModularPolynomialData p) (x x' : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) :
    data.Φ.eval₂ (aeval (R := ℤ) x).toRingHom x' = 0 := by
  have h := data.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) 1
  rw [jqNModC_one] at h
  have hp : jqNModC (AlgebraicClosure ℚ) (1 * p) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := qExpand_congr (one_mul p) _
  rw [hp, ← hx', ← hx] at h
  let ι : ↥(xHFunctionFieldBar M H) →+* LaurentSeries (AlgebraicClosure ℚ) := (xHFunctionFieldBar M H).val.toRingHom
  have hι : ∀ y : ↥(xHFunctionFieldBar M H), ι y = (y : LaurentSeries (AlgebraicClosure ℚ)) := fun _ => rfl
  have key := map_eval₂_aeval ι data.Φ x x'
  simp only [hι] at key
  have e : ((data.Φ.eval₂ (aeval (R := ℤ) x).toRingHom x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    refine key.trans ?_
    convert h using 2 <;> first | rfl | with_reducible_and_instances rfl | exact ringHom_int_poly_ext _ _ (by simp)
  exact Subtype.ext (by simpa using e)

omit [Fact p.Prime] in

theorem surjective_algebraMap_residueField (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : Module.Finite (AlgebraicClosure ℚ) W.ResidueField := IsCurveOver.finiteResidue W
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) W.ResidueField := Algebra.IsIntegral.of_finite _ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := W.ResidueField)).2

omit [Fact p.Prime] in

theorem coe_algebraMap (a : (AlgebraicClosure ℚ)) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C a := by
  rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a from
    (IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ)) a).symm, HahnSeries.algebraMap_apply', ← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

end Inputs

end Ws49.CuspPrime

open Ws49.CuspPrime in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) W) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  intro x hx a
  by_contra hle
  push Not at hle

  have hxc0 : x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h
    have h' := congrArg (fun y : ↥(xHFunctionFieldBar M H) => ((y : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) (sub_eq_zero.mp h)
    simp only [hx, coe_algebraMap, coeff_jqModC_neg_one] at h'
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by norm_num)] at h'
    exact one_ne_zero h'
  have hval : W.HasValue x (a : (AlgebraicClosure ℚ)) := hasValue_of_ord_sub_pos W hxc0 hle

  obtain ⟨x', hx'⟩ := exists_coe_eq_qExpand_jqModC p M H hpM
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have hrel := modular_relation p M H data x x' hx hx'

  let O := W.toValuationSubring
  let xO : ↥O := ⟨x, hval.mem⟩
  have hcoeff : ∀ i, (data.Φ.map (aeval (R := ℤ) x).toRingHom).coeff i ∈ O := by
    intro i
    rw [Polynomial.coeff_map]
    show aeval (R := ℤ) x (data.Φ.coeff i) ∈ O
    have : aeval (R := ℤ) x (data.Φ.coeff i) = ((aeval (R := ℤ) xO (data.Φ.coeff i) : ↥O) : ↥(xHFunctionFieldBar M H)) := by
      rw [show x = O.subtype.toIntAlgHom xO from rfl, Polynomial.aeval_algHom_apply]
      rfl
    rw [this]
    exact SetLike.coe_mem _
  have hx'O : x' ∈ O := W.mem_of_eval_monic_eq_zero (data.monic.map _) hcoeff (by rw [Polynomial.eval_map]; exact hrel)
  let x'O : ↥O := ⟨x', hx'O⟩

  obtain ⟨b, hb, -⟩ := W.exists_hasValue_of_surjective (surjective_algebraMap_residueField M H W) hx'O

  have hrelO : data.Φ.eval₂ (aeval (R := ℤ) xO).toRingHom x'O = 0 := by
    have h1 := map_eval₂_aeval O.subtype data.Φ xO x'O
    have h2 : O.subtype (data.Φ.eval₂ (aeval (R := ℤ) xO).toRingHom x'O) = 0 := h1.trans hrel
    exact Subtype.ext (by simpa using h2)
  have hrelκ := congrArg (residue ↥O) hrelO
  rw [map_eval₂_aeval (residue ↥O) data.Φ xO x'O, map_zero, show residue ↥O xO = algebraMap _ _ (a : (AlgebraicClosure ℚ)) from hval.residue_eq,
    show residue ↥O x'O = algebraMap _ _ b from hb.residue_eq, ← map_eval₂_aeval (algebraMap (AlgebraicClosure ℚ) W.ResidueField) data.Φ,
    map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) W.ResidueField).injective] at hrelκ

  have hint : IsIntegral ↥A b := isIntegral_of_eval₂_aeval_eq_zero data.Φ data.monic a b hrelκ
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := (AlgebraicClosure ℚ))).mp hint

  have hx'c0 : x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (y : (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : ↥(xHFunctionFieldBar M H) => ((z : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff ((p : ℤ) * (-1))) (sub_eq_zero.mp h)
    simp only [hx', coe_algebraMap, qExpand_coeff_mul, coeff_jqModC_neg_one] at h'
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)] at h'
    exact one_ne_zero h'
  have hyb : W.HasValue x' (y : (AlgebraicClosure ℚ)) := by rw [show ((y : (AlgebraicClosure ℚ))) = b from hy]; exact hb
  exact absurd (hW x' hx' y) (not_le.mpr (ord_sub_pos_of_hasValue W hyb hx'c0))

end

end S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime (solution)
