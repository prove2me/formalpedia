-- Prove2me | solution 1 for ModularCurve.finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b9e748bf-4eaf-5884-9ae0-1b2066d68a91

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

open WithZero

namespace FixFrobPen12

variable (p : ℕ) [Fact p.Prime]

noncomputable abbrev Zp : ValuationSubring ℚ := (Rat.padicValuation p).valuationSubring

theorem natCast_mem_maximalIdeal :
    ((p : ↥(Zp p)) : ↥(Zp p)) ∈ IsLocalRing.maximalIdeal ↥(Zp p) := by
  rw [Valuation.mem_maximalIdeal_iff]
  show Rat.padicValuation p ((p : ↥(Zp p)) : ℚ) < 1
  rw [show ((p : ↥(Zp p)) : ℚ) = (p : ℚ) from by simp, Rat.padicValuation_self, ← exp_zero]
  exact exp_lt_exp.mpr (by norm_num)

scoped instance charP_residueField : CharP (IsLocalRing.ResidueField ↥(Zp p)) p := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime), ← map_natCast (IsLocalRing.residue ↥(Zp p)),
    IsLocalRing.residue_eq_zero_iff]
  exact natCast_mem_maximalIdeal p

noncomputable def ψ : ZMod p →+* IsLocalRing.ResidueField ↥(Zp p) :=
  ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField ↥(Zp p))

theorem exists_int_sub_mem (x : ↥(Zp p)) :
    ∃ n : ℤ, x - (n : ↥(Zp p)) ∈ IsLocalRing.maximalIdeal ↥(Zp p) := by
  have hp : p.Prime := Fact.out
  have hx : ¬ p ∣ (x : ℚ).den := Rat.padicValuation_le_one_iff.mp x.2
  set d : ℕ := (x : ℚ).den with hd
  set a : ℤ := (x : ℚ).num with ha
  have hd0 : (d : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  set c : ZMod p := (a : ZMod p) * (d : ZMod p)⁻¹ with hc
  refine ⟨(c.val : ℤ), ?_⟩
  rw [Valuation.mem_maximalIdeal_iff]
  show Rat.padicValuation p ((x - ((c.val : ℤ) : ↥(Zp p)) : ↥(Zp p)) : ℚ) < 1
  have hcoe : (((x - ((c.val : ℤ) : ↥(Zp p)) : ↥(Zp p)) : ℚ)) = (x : ℚ) - ((c.val : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [hcoe]

  have hdq : ((d : ℤ) : ℚ) ≠ 0 := by
    have := (x : ℚ).den_pos
    exact_mod_cast this.ne'
  have hxeq : (x : ℚ) - ((c.val : ℤ) : ℚ) = (((a - (c.val : ℤ) * d : ℤ)) : ℚ) / ((d : ℤ) : ℚ) := by
    rw [eq_div_iff hdq]
    push_cast
    have : (x : ℚ) * (d : ℚ) = (a : ℚ) := by
      rw [ha, hd]
      exact_mod_cast (x : ℚ).mul_den_eq_num
    linear_combination this
  rw [hxeq, map_div₀, Rat.padicValuation_cast, Rat.padicValuation_cast]

  have hnum : (p : ℤ) ∣ a - (c.val : ℤ) * d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hc, mul_assoc, inv_mul_cancel₀ hd0, mul_one, sub_self]
  have hden : Int.padicValuation p (d : ℤ) = 1 := by
    rw [Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
    exact hx
  rw [hden, div_one]
  exact Int.padicValuation_lt_one_iff.mpr hnum

theorem ψ_surjective : Function.Surjective (ψ p) := by
  intro r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨n, hn⟩ := exists_int_sub_mem p y
  refine ⟨(n : ZMod p), ?_⟩
  rw [map_intCast, ← map_intCast (IsLocalRing.residue ↥(Zp p)) n, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff]
  exact hn

scoped instance finite_residueField : Finite (IsLocalRing.ResidueField ↥(Zp p)) :=
  Finite.of_surjective _ (ψ_surjective p)

theorem natCard_residueField : Nat.card (IsLocalRing.ResidueField ↥(Zp p)) = p := by
  have h := Nat.card_eq_of_bijective _ ⟨(ψ p).injective, ψ_surjective p⟩
  rw [Nat.card_zmod] at h
  exact h.symm

scoped instance perfectField_residueField : PerfectField (IsLocalRing.ResidueField ↥(Zp p)) := PerfectField.ofFinite

theorem pow_card_eq (a : IsLocalRing.ResidueField ↥(Zp p)) : a ^ p = a := by
  haveI := Fintype.ofFinite (IsLocalRing.ResidueField ↥(Zp p))
  have h := FiniteField.pow_card a
  rwa [Fintype.card_eq_nat_card, natCard_residueField] at h

end FixFrobPen12
p2m_reactivate "P2MW.S_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL.FixFrobPen12"

namespace FixFrobPen12

theorem qExpand_coeffMap' (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {K' : Type*} [Field K'] (τ : K →+* K') (s : LaurentSeries K) :
    ModularCurve.qExpand K' p (ModularCurve.coeffMap τ s) = ModularCurve.coeffMap τ (ModularCurve.qExpand K p s) := by
  ext k
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.coeffMap_coeff, ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_mul]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd p _ hk, ModularCurve.coeffMap_coeff, ModularCurve.qExpand_coeff_of_not_dvd p _ hk, map_zero]

end FixFrobPen12
p2m_reactivate "P2MW.S_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL.FixFrobPen12"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p]
    (halg : ∀ a : κ, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a)
    (F : Pic0 κ (Fbar p M H hpM κ) →+ Pic0 κ (Fbar p M H hpM κ))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p z)
    (n : ℕ) (hn : 0 < n) :
    (Function.fixedPoints (⇑F)^[n]).Finite := by
  classical
  have hp : p.Prime := Fact.out

  by_cases hin : ModularCurve.QExpFrobeniusInputsModL κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p
  swap
  · have hF0 : ∀ z, F z = 0 := fun z => by
      rw [hF, ModularCurve.qExpFrobeniusPushforwardModL_of_not hin]; rfl
    have hsub : Function.fixedPoints (⇑F)^[n] ⊆ {0} := by
      intro z hz
      rw [Set.mem_singleton_iff, ← Function.mem_fixedPoints.mp hz]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [Function.iterate_succ_apply', hF0]
    exact Set.Finite.subset (Set.finite_singleton _) hsub
  obtain ⟨hP, hfin, hFI, hN⟩ := hin
  haveI := hP

  haveI : (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hT' : ModularGroup.T ∈ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  obtain ⟨hcurve₀, hfg⟩ :=
    ModularCurve.isCurveOver_and_exists_finset_adjoin_eq_top_qExpFunctionFieldC_residueField ℚ (FixFrobPen12.Zp p) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) hT'
  haveI := hcurve₀
  haveI : IsCurveOver κ (Fbar p M H hpM κ) := ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) hT'

  let ι₀ : (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) →+* κ :=
    (ZMod.castHom (dvd_refl p) κ).comp (RingEquiv.ofBijective (FixFrobPen12.ψ p) ⟨(FixFrobPen12.ψ p).injective, FixFrobPen12.ψ_surjective p⟩).symm.toRingHom
  letI : Algebra (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) κ := ι₀.toAlgebra

  let emb : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) →+* (Fbar p M H hpM κ) :=
    ((ModularCurve.coeffMap ι₀).comp (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).toSubfield.subtype).codRestrict (ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM))
      (fun x => ModularCurve.coeffMap_mem_qExpFunctionFieldC_of_mem ι₀ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) x.2)
  letI : Algebra ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) := emb.toAlgebra
  have hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)), ((algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) x : (Fbar p M H hpM κ)) : LaurentSeries κ) = ModularCurve.coeffMap ι₀ (x : LaurentSeries (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p))) :=
    fun x => rfl

  have himage : ⇑(ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val '' Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ)) =
      ⇑(ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) κ)) '' ((ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) : Set (LaurentSeries (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)))) := by
    ext s
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : LaurentSeries (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p))), x.2, (hι x).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, hι ⟨t, ht⟩⟩
  have hgen : IntermediateField.adjoin κ (Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ))) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    set S : Set (Fbar p M H hpM κ) := Set.range (algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ)) with hSdef
    have h1 : IntermediateField.adjoin κ (⇑(ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val '' S) ≤
        (IntermediateField.adjoin κ S).map (ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      show _ ∈ ((IntermediateField.map (ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val (IntermediateField.adjoin κ S) :
        IntermediateField κ (LaurentSeries κ)) : Set (LaurentSeries κ))
      rw [IntermediateField.coe_map]
      exact ⟨x, IntermediateField.subset_adjoin κ S hx, rfl⟩
    have hy0 : (y : LaurentSeries κ) ∈ IntermediateField.adjoin κ (⇑(ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val '' S) := by
      rw [himage, ← ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)]
      exact y.2
    have hy : (y : LaurentSeries κ) ∈ ((IntermediateField.map (ModularCurve.qExpFunctionFieldC κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)).val (IntermediateField.adjoin κ S) :
        IntermediateField κ (LaurentSeries κ)) : Set (LaurentSeries κ)) := h1 hy0
    rw [IntermediateField.coe_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    rw [← this]; exact hz

  set φ := ModularCurve.qExpFrobeniusModL κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p with hφdef
  have hφ : ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)), φ (algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) x) = algebraMap ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) (x ^ Nat.card (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p))) := by
    intro x
    apply Subtype.ext
    rw [FixFrobPen12.natCard_residueField, ModularCurve.coe_qExpFrobeniusModL, hι, hι, FixFrobPen12.qExpand_coeffMap',
      SubmonoidClass.coe_pow]
    congr 1
    exact ModularCurve.qExpand_eq_pow_of_coeff_fixed (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) p _ (fun k => FixFrobPen12.pow_card_eq p _)
  have hC := AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) κ ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) hfg hgen φ hφ
  have halg' : ∀ a : κ, ∃ m : ℕ, 0 < m ∧ a ^ Nat.card (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) ^ m = a := by
    rw [FixFrobPen12.natCard_residueField]; exact halg

  have hT : ∀ D : Divisor.degZero (K := κ) (F := (Fbar p M H hpM κ)),
      F (Pic0.mk D) = Pic0.mk ⟨Divisor.pushforwardAlong φ (ModularCurve.qExpFrobeniusModL_isIntegral κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p) D,
        Divisor.pushforwardAlong_mem_degZero φ (ModularCurve.qExpFrobeniusModL_isIntegral κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p) D.2⟩ := by
    intro D
    rw [hF, ModularCurve.qExpFrobeniusPushforwardModL_mk hfin hFI hN]
    rfl
  obtain ⟨P, -, -, -, -, hiter⟩ :=
    AlgebraicCurve.Pic0.exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
      (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) κ ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥(FixFrobPen12.Zp p)) (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM)) (Fbar p M H hpM κ) hfg hC hgen halg' φ (ModularCurve.qExpFrobeniusModL_isIntegral κ (ModularCurve.JHNeronObjectAtP.ΓN p M H hpM) p) hφ F hT
  exact (hiter n hn).1

end S_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL
end P2MW
export P2MW.S_ModularCurve_finite_fixedPoints_iterate_qExpFrobeniusPushforwardModL (solution)
