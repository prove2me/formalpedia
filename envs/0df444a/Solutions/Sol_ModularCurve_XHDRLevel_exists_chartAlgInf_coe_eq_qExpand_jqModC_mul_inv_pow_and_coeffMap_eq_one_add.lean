-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c77a42ee-fe54-52e4-9b01-e20127bd36b6

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

open ModularCurve ModularCurve.XHDRLevel AlgebraicCurve
open scoped MatrixGroups

namespace TInfMemPen14

theorem map_mem_chartAlgInf {R : Type} [CommRing R] {K₁ K₂ : Type} [Field K₁] [Field K₂] [Algebra R K₁] [Algebra R K₂]
    (f : K₁ →+* K₂) (hf : ∀ r : R, f (algebraMap R K₁ r) = algebraMap R K₂ r)
    (j₁ : K₁) [Fact (j₁ ≠ 0)] (j₂ : K₂) [Fact (j₂ ≠ 0)] (hj : f j₁ = j₂) {x : K₁}
    (hx : x ∈ TwoChartIntegralModel.chartAlgInf R K₁ j₁) : f x ∈ TwoChartIntegralModel.chartAlgInf R K₂ j₂ := by
  rw [TwoChartIntegralModel.mem_chartAlg_iff] at hx ⊢
  let fa : K₁ →ₐ[R] K₂ := ⟨f, hf⟩
  have hfa : ∀ y, fa y = f y := fun _ => rfl
  have hmap : (Algebra.adjoin R ({j₁⁻¹} : Set K₁)).map fa = Algebra.adjoin R ({j₂⁻¹} : Set K₂) := by
    rw [AlgHom.map_adjoin, Set.image_singleton, hfa, map_inv₀, hj]
  let φ : Algebra.adjoin R ({j₁⁻¹} : Set K₁) →+* Algebra.adjoin R ({j₂⁻¹} : Set K₂) :=
    (fa.toRingHom.comp (Algebra.adjoin R ({j₁⁻¹} : Set K₁)).val.toRingHom).codRestrict _ (fun y => by
      rw [← hmap]
      exact Subalgebra.mem_map.mpr ⟨y, y.2, rfl⟩)
  exact hx.map_of_comp_eq φ f (by ext y; rfl)

def incl {K F : IntermediateField ℚ (LaurentSeries ℚ)} (h : K ≤ F) : ↥K →+* ↥F where
  toFun x := ⟨x.1, h x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_incl {K F : IntermediateField ℚ (LaurentSeries ℚ)} (h : K ≤ F) (x : ↥K) :
    ((incl h x : ↥F) : LaurentSeries ℚ) = (x : LaurentSeries ℚ) := rfl

theorem ringHom_ratLocalizedAt_ext (p : ℕ) {L : Type*} [Ring L] [CharZero L] [IsDomain L]
    (g₁ g₂ : ↥(GaloisRep.ratLocalizedAt p) →+* L) : g₁ = g₂ := by
  ext r
  have hden : (((r : ℚ).den : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (r : ℚ).den_ne_zero

  have hr : r * (((r : ℚ).den : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = (((r : ℚ).num : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) := by
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (r : ℚ)
  have h1 := congrArg g₁ hr
  have h2 := congrArg g₂ hr
  rw [map_mul, map_natCast, map_intCast] at h1 h2
  exact mul_right_cancel₀ hden (h1.trans h2.symm)

scoped instance : CharZero (LaurentSeries ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective

section Level

variable (p : ℕ) [Fact p.Prime]

scoped instance instNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

noncomputable def jK : ↥(modularFunctionFieldFull p) := ⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩

noncomputable def jK' : ↥(modularFunctionFieldFull p) := ⟨qExpand ℚ p jq, jqd_mem_full p dvd_rfl⟩

omit [Fact p.Prime] in
theorem coe_jK [NeZero p] : ((⟨qExpand ℚ 1 jq, jqd_mem_full p (one_dvd p)⟩ : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = jqModC ℚ :=
  qExpand_one_apply jq

theorem coe_jK_eq : ((jK p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = jqModC ℚ := qExpand_one_apply jq

theorem coe_jK' : ((jK' p : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := rfl

scoped instance : Fact (jK p ≠ 0) := ⟨fun h => jq_ne_zero (by
  have := congrArg (fun x : ↥(modularFunctionFieldFull p) => (x : LaurentSeries ℚ)) h
  first | exact this | (simp [coe_jK_eq] at this; exact this) | simpa [coe_jK_eq] using this)⟩

theorem tK_mem (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    jK' p * ((jK p)⁻¹) ^ p ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull p) (jK p) := by

  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isFrickeAutFull_of_neZero p
  have hσj : σ (jK p) = jK' p := hσ 1 p (one_mul p) inferInstance inferInstance
  have hσj' : σ (jK' p) = jK p := hσ p 1 (mul_one p) inferInstance inferInstance

  have hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 p) :=
    ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p
  obtain ⟨W, hWpin, -⟩ := ModularCurve.XHDRLevel.exists_valuationSubring_gauss_qExpFunctionFieldC p (CongruenceSubgroup.Gamma0 p) hj
  let W₀ : ValuationSubring ↥(modularFunctionFieldFull p) := W.comap (incl hle)
  have hW₀ : ∀ f : ↥(modularFunctionFieldFull p), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype) := fun f => by
    rw [ValuationSubring.mem_comap]
    exact hWpin _
  have h := ModularCurve.qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss p (modularFunctionFieldFull p)
    (jK p) (coe_jK_eq p) (jK' p) (coe_jK' p) σ hσj hσj' W₀ hW₀
  exact h.1

theorem exists_chartAlgInf_coe_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ t : ↥(chartAlgInf p (ΓM M H) hj),
      ((t : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) * ((jqModC ℚ)⁻¹) ^ p := by

  have h0 : CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 p := by
    intro A hA
    have hA0 := CohCarrier.GammaH_le_Gamma0 H hA
    rw [CongruenceSubgroup.Gamma0_mem] at hA0 ⊢
    have := congrArg (ZMod.castHom hpM (ZMod p)) hA0
    rwa [map_intCast, map_zero] at this
  have hle : modularFunctionFieldFull p ≤ qExpFunctionFieldC ℚ (ΓM M H) :=
    (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ p).trans (qExpFunctionFieldC_mono ℚ h0)
  let ι : ↥(modularFunctionFieldFull p) →+* ↥(qExpFunctionFieldC ℚ (ΓM M H)) := incl hle

  have hι : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      ι (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull p) r) =
        algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) r := by
    intro r
    apply Subtype.ext
    have := congrArg (fun g => g r) (ringHom_ratLocalizedAt_ext p
      ((algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(modularFunctionFieldFull p)))
      ((algebraMap ↥(qExpFunctionFieldC ℚ (ΓM M H)) (LaurentSeries ℚ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (ΓM M H)))))
    exact this
  have hιj : ι (jK p) = jAt (ΓM M H) hj := Subtype.ext (by rw [coe_incl, coe_jK_eq, coe_jAt])
  have hmem := map_mem_chartAlgInf ι hι (jK p) (jAt (ΓM M H) hj) hιj (tK_mem p hj)
  refine ⟨⟨ι (jK' p * ((jK p)⁻¹) ^ p), hmem⟩, ?_⟩
  show ((ι (jK' p * ((jK p)⁻¹) ^ p) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = _
  rw [coe_incl]
  push_cast
  rw [coe_jK', coe_jK_eq]

end Level

end TInfMemPen14
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add.TInfMemPen14"

namespace TInfCongPen14

theorem coeffMap_ofPowerSeries {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (x : PowerSeries K) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ K x) = HahnSeries.ofPowerSeries ℤ K' (x.map f) := by
  ext i
  rw [coeffMap_coeff]
  change f (((x : PowerSeries K) : LaurentSeries K).coeff i) = ((x.map f : PowerSeries K') : LaurentSeries K').coeff i
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

theorem coeffMap_natCast_smul {K K' : Type*} [CommRing K] [CommRing K'] (f : K →+* K') (n : ℕ) (x : LaurentSeries K) :
    coeffMap f ((n : K) • x) = (n : K') • coeffMap f x := by
  ext i
  simp [coeffMap_coeff]

section Generic

variable (K : Type*) [CommRing K]

noncomputable def Ainv : PowerSeries ℤ := PowerSeries.invOfUnit jNum 1

theorem jNum_mul_Ainv : jNum * Ainv = 1 :=
  PowerSeries.mul_invOfUnit jNum 1 (by rw [Units.val_one, constantCoeff_jNum])

noncomputable def Jinv : LaurentSeries K :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (Ainv.map (Int.castRingHom K))

theorem jqModC_mul_Jinv : jqModC K * Jinv K = 1 := by
  rw [jqModC, Jinv, mul_mul_mul_comm, HahnSeries.single_mul_single, show (-1 : ℤ) + 1 = 0 by norm_num, one_mul]
  have hA : (jNum.map (Int.castRingHom K)) * (Ainv.map (Int.castRingHom K)) = 1 := by
    rw [← map_mul, jNum_mul_Ainv, map_one]
  rw [← map_mul, hA, RingHom.map_one, mul_one]
  rfl

noncomputable def T (p : ℕ) [NeZero p] : LaurentSeries K := qExpand K p (jqModC K) * Jinv K ^ p

variable {K}

theorem coeffMap_Jinv {K' : Type*} [CommRing K'] (f : K →+* K') : coeffMap f (Jinv K) = Jinv K' := by
  rw [Jinv, Jinv, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  congr 2
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, ← RingHom.comp_apply,
    RingHom.eq_intCast' (f.comp (Int.castRingHom K))]

theorem coeffMap_T {K' : Type*} [CommRing K'] (f : K →+* K') (p : ℕ) [NeZero p] : coeffMap f (T K p) = T K' p := by
  rw [T, T, map_mul, map_pow, coeffMap_qExpand, coeffMap_Jinv]
  congr 2
  exact map_jqModC f

end Generic
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add.TInfMemPen14"

theorem T_zmod_eq_one (p : ℕ) [Fact p.Prime] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    T (ZMod p) p = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [T, ModularCurve.qExpand_jqModC_eq_pow_unconditional (ZMod p) (ℓ := p), ← mul_pow, jqModC_mul_Jinv, one_pow]

theorem exists_T_int_eq_one_add_smul (p : ℕ) [Fact p.Prime] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ W : LaurentSeries ℤ, T ℤ p = 1 + (p : ℤ) • W := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set D : LaurentSeries ℤ := T ℤ p - 1 with hD
  have hdvd : ∀ i : ℤ, (p : ℤ) ∣ D.coeff i := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : coeffMap (Int.castRingHom (ZMod p)) D = 0 := by
      rw [hD, map_sub, map_one, coeffMap_T, T_zmod_eq_one, sub_self]
    have := congrArg (fun x : LaurentSeries (ZMod p) => x.coeff i) h1
    simpa [coeffMap_coeff] using this
  choose w hw using hdvd
  let W : LaurentSeries ℤ :=
    { coeff := w
      isPWO_support' := D.isPWO_support.mono (by
        intro i hi
        simp only [Function.mem_support, ne_eq] at hi ⊢
        intro h0
        apply hi
        have h := hw i
        rw [h0] at h
        exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) }
  refine ⟨W, ?_⟩
  have hDW : D = (p : ℤ) • W := by
    ext i
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    exact hw i
  rw [← sub_eq_iff_eq_add', ← hD, hDW]

theorem exists_coeffMap_eq_and_eq_one_add (p : ℕ) [Fact p.Prime] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ y z : LaurentSeries (R p),
      coeffMap (algebraMap (R p) ℚ) y = qExpand ℚ p (jqModC ℚ) * ((jqModC ℚ)⁻¹) ^ p ∧
      y = 1 + ((p : ℕ) : R p) • z := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨W, hW⟩ := exists_T_int_eq_one_add_smul p
  refine ⟨T (R p) p, coeffMap (Int.castRingHom (R p)) W, ?_, ?_⟩
  · rw [coeffMap_T, T]
    congr 2

    exact (inv_eq_of_mul_eq_one_right (jqModC_mul_Jinv ℚ)).symm
  · rw [← coeffMap_T (Int.castRingHom (R p)) p, hW, map_add, map_one]
    congr 1
    have := coeffMap_natCast_smul (Int.castRingHom (R p)) p W
    simpa using this

end TInfCongPen14
p2m_reactivate "P2MW.S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add.TInfMemPen14"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ (t : ↥(chartAlgInf p (ΓM M H) hj)) (y z : LaurentSeries (R p)),
      ((t : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) * ((jqModC ℚ)⁻¹) ^ p ∧
      coeffMap (algebraMap (R p) ℚ) y = ((t : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) ∧
      y = 1 + ((p : ℕ) : R p) • z := by
  obtain ⟨t, ht⟩ := TInfMemPen14.exists_chartAlgInf_coe_eq p M H hpM hj
  obtain ⟨y, z, hy, hz⟩ := TInfCongPen14.exists_coeffMap_eq_and_eq_one_add p
  exact ⟨t, y, z, ht, hy.trans ht.symm, hz⟩

end S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add (solution)
