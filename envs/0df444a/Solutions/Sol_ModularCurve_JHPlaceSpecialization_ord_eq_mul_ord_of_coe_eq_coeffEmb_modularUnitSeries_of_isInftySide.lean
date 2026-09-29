-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/94687e2c-c96a-53d7-868e-f7c05643cabc

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false
set_option quotPrecheck false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

noncomputable section

namespace OrdUnitInfH

section level
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

scoped instance neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

scoped instance gammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange 𝕂 F₀ ≤ laurentBaseChange 𝕂 F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange 𝕂 (h hy)

theorem level_le (hpM : p ∣ M) : modularFunctionFieldBar p ≤ xHFunctionFieldBar M H := by
  apply laurentBaseChange_mono
  calc modularFunctionFieldFull p
      ≤ modularFunctionFieldFull M := full_degeneracy_le hpM
    _ = modularFunctionFieldFullC ℚ M := (modularFunctionFieldFullC_rat M).symm
    _ ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M) := modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M
    _ ≤ xHFunctionField M H := x0_le_xHFunctionFieldC ℚ M H

def ι (hpM : p ∣ M) : ↥(modularFunctionFieldBar p) →ₐ[𝕂] FM := IntermediateField.inclusion (level_le p M H hpM)

theorem coe_ι (hpM : p ∣ M) (f : ↥(modularFunctionFieldBar p)) :
    ((ι p M H hpM f : FM) : LaurentSeries 𝕂) = (f : LaurentSeries 𝕂) :=
  IntermediateField.coe_inclusion _ f

theorem coeffEmb_jq_eq_jqModC : coeffEmb 𝕂 jq = jqModC 𝕂 := by
  ext n
  rw [coeffEmb_coeff, ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ), jqModC_eq_map_intCast (K := 𝕂)]
  simp

theorem coeffEmb_qExpand' (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb 𝕂 (qExpand ℚ n x) = qExpand 𝕂 n (coeffEmb 𝕂 x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

def jN : ↥(modularFunctionFieldBar p) :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (modularFunctionField_le_full p (jq_mem p))⟩

def jpN : ↥(modularFunctionFieldBar p) :=
  ⟨coeffEmb 𝕂 (qExpand ℚ p jq), coeffEmb_mem_laurentBaseChange 𝕂 (jqd_mem_full p (dvd_refl p))⟩

def uN : ↥(modularFunctionFieldBar p) :=
  ⟨coeffEmb 𝕂 (modularUnitSeries p), coeffEmb_mem_laurentBaseChange 𝕂 (modularUnitSeries_mem_modularFunctionFieldFull p)⟩

theorem coe_ι_jN (hpM : p ∣ M) : ((ι p M H hpM (jN p) : FM) : LaurentSeries 𝕂) = jqModC 𝕂 := by
  rw [coe_ι]
  show coeffEmb 𝕂 jq = jqModC 𝕂
  exact coeffEmb_jq_eq_jqModC

theorem coe_ι_jpN (hpM : p ∣ M) : ((ι p M H hpM (jpN p) : FM) : LaurentSeries 𝕂) = qExpand 𝕂 p (jqModC 𝕂) := by
  rw [coe_ι]
  show coeffEmb 𝕂 (qExpand ℚ p jq) = qExpand 𝕂 p (jqModC 𝕂)
  rw [coeffEmb_qExpand', coeffEmb_jq_eq_jqModC]

theorem coe_ι_uN (hpM : p ∣ M) :
    ((ι p M H hpM (uN p) : FM) : LaurentSeries 𝕂) = coeffEmb 𝕂 (modularUnitSeries p) := by
  rw [coe_ι]
  rfl

theorem jN_ne_zero : jN p ≠ 0 := fun h =>
  (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero (congrArg Subtype.val h)

theorem jpN_ne_zero : jpN p ≠ 0 := fun h =>
  (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr ((map_ne_zero (qExpand ℚ p)).mpr jq_ne_zero)
    (congrArg Subtype.val h)

theorem isIntegral_of_finiteDimensional_adjoin_image {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (i : F →ₐ[K] F') (x : F)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin K ({i x} : Set F')) F') :
    i.toRingHom.IsIntegral := by
  classical
  letI : Algebra F F' := i.toRingHom.toAlgebra
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  set Kt : IntermediateField K F' := IntermediateField.adjoin K ({i x} : Set F') with hKt
  have hmap : Kx.map i = Kt := by
    rw [hKx, IntermediateField.adjoin_map, Set.image_singleton]
  let e : ↥Kx ≃ₐ[K] ↥Kt := (Kx.equivMap i).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ y : ↥Kx, ((e y : ↥Kt) : F') = i (y : F) := fun y => rfl
  letI : Algebra ↥Kt F := ((algebraMap ↥Kx F).comp (e.symm : ↥Kt →ₐ[K] ↥Kx).toRingHom).toAlgebra
  haveI : IsScalarTower ↥Kt F F' := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    show (k : F') = i ((e.symm k : ↥Kx) : F)
    rw [← he, AlgEquiv.apply_symm_apply]
  haveI : Module.Finite ↥Kt F' := hfd
  haveI : Module.Finite F F' := Module.Finite.of_restrictScalars_finite ↥Kt F F'
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  intro z
  exact Algebra.IsIntegral.isIntegral z

theorem ι_isIntegral (hpM : p ∣ M) : (ι p M H hpM).toRingHom.IsIntegral := by
  have h := (transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC 𝕂
    (CohCarrier.GammaH M H) (translation_mem_GammaH M H) (ι p M H hpM (jN p))
    (coe_ι_jN p M H hpM)).2
  exact isIntegral_of_finiteDimensional_adjoin_image (ι p M H hpM) (jN p) h

theorem ramificationIndexAlong_pos {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

end level

section engine
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ
local notation "FM" => ↥(xHFunctionFieldBar M H)

theorem coe_ne_zero_of_residue_eq_one (A : ValuationSubring 𝕂) {τ : ↥A}
    (hτ : IsLocalRing.residue ↥A τ = 1) : (τ : 𝕂) ≠ 0 := by
  intro h0
  have hτ0 : τ = 0 := Subtype.ext h0
  rw [hτ0, map_zero] at hτ
  exact zero_ne_one hτ

theorem ord_eq_mul_ord (hpM : p ∣ M) (A : ValuationSubring 𝕂)
    (u : FM) (hu : ((u : FM) : LaurentSeries 𝕂) = coeffEmb 𝕂 (modularUnitSeries p))
    (xM : FM) (hxM : ((xM : FM) : LaurentSeries 𝕂) = jqModC 𝕂)
    (W : Place 𝕂 FM) (hW : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W) :
    W.ord u = ((p : ℤ) - 1) * W.ord xM := by
  classical
  obtain ⟨hcusp, x, x', hx, hx', τ, hτ, hval⟩ := hW

  set φ := ι p M H hpM with hφ_def
  have hι : φ.toRingHom.IsIntegral := ι_isIntegral p M H hpM
  have hxxM : x = xM := Subtype.ext (hx.trans hxM.symm)
  have hxM' : xM = φ (jN p) := Subtype.ext (hxM.trans (coe_ι_jN p M H hpM).symm)
  have hx'' : x' = φ (jpN p) := Subtype.ext (hx'.trans (coe_ι_jpN p M H hpM).symm)
  have hu' : u = φ (uN p) := Subtype.ext (hu.trans (coe_ι_uN p M H hpM).symm)

  set W₁ : Place 𝕂 ↥(modularFunctionFieldBar p) := W.restrictAlong φ hι with hW₁_def
  have hord : ∀ f : ↥(modularFunctionFieldBar p),
      W.ord (φ f) = Place.ramificationIndexAlong φ W * W₁.ord f :=
    fun f => Place.ord_restrictAlong φ hι W f
  have he : (0 : ℤ) < Place.ramificationIndexAlong φ W := by
    exact_mod_cast ramificationIndexAlong_pos φ hι W

  have hle : W.ord xM ≤ 0 := by
    have h := hcusp xM hxM 0
    simpa using h

  have hxM0 : xM ≠ 0 := by
    rw [hxM']; exact (map_ne_zero φ).mpr (jN_ne_zero p)
  have hx'0 : x' ≠ 0 := by
    rw [hx'']; exact (map_ne_zero φ).mpr (jpN_ne_zero p)
  have hchart : W.ord x' = (p : ℤ) * W.ord xM := by
    have h0 : W.ord (x' / x ^ p) = 0 := hval.ord_eq_zero (coe_ne_zero_of_residue_eq_one A hτ)
    rw [hxxM] at h0
    rw [div_eq_mul_inv, W.ord_mul hx'0 (inv_ne_zero (pow_ne_zero p hxM0)), Place.ord_inv, ← zpow_natCast,
      Place.ord_zpow] at h0
    linarith
  rcases lt_or_ge (W.ord xM) 0 with hneg | hnn
  ·
    have hpole : W₁.ord (jN p) < 0 := by
      have e := hord (jN p)
      rw [← hxM'] at e
      by_contra hge
      rw [not_lt] at hge
      have : 0 ≤ W.ord xM := by rw [e]; exact mul_nonneg he.le hge
      exact absurd hneg (not_lt.mpr this)
    have hrow := ord_coeffEmb_modularUnitSeries_eq_sub_of_ord_jqModC_neg p W₁ hpole p (dvd_refl p)
      (modularUnitSeries_mem_modularFunctionFieldFull p)

    have e1 : W.ord u = Place.ramificationIndexAlong φ W * W₁.ord (uN p) := by rw [hu']; exact hord _
    have e2 : W.ord xM = Place.ramificationIndexAlong φ W * W₁.ord (jN p) := by
      conv_lhs => rw [hxM']
      exact hord _
    have e3 : W.ord x' = Place.ramificationIndexAlong φ W * W₁.ord (jpN p) := by rw [hx'']; exact hord _
    have hrow' : W₁.ord (uN p) = W₁.ord (jpN p) - W₁.ord (jN p) := hrow
    rw [e1, hrow', mul_sub, ← e3, ← e2, hchart]
    ring
  ·
    have h0 : W.ord xM = 0 := le_antisymm hle hnn
    have hnn₁ : 0 ≤ W₁.ord (jN p) := by
      have e := hord (jN p)
      rw [← hxM', h0] at e
      rcases lt_or_ge (W₁.ord (jN p)) 0 with hlt | hge
      · exfalso
        have : Place.ramificationIndexAlong φ W * W₁.ord (jN p) < 0 := mul_neg_of_pos_of_neg he hlt
        omega
      · exact hge
    have hnc : ¬ IsCusp (CharPModel.jBar p) W₁ := by
      rw [isCusp_iff_ord_neg, not_lt]
      exact hnn₁
    have hz := ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp p p (dvd_refl p)
      (modularUnitSeries_mem_modularFunctionFieldFull p) W₁ hnc
    have hz' : W₁.ord (uN p) = 0 := hz
    rw [hu', hord, hz', h0]
    ring

end engine

end OrdUnitInfH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide.OrdUnitInfH"

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide.OrdUnitInfH"

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (xM : ↥(xHFunctionFieldBar M H))
    (hxM : ((xM : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W) :
    W.ord u = ((p : ℤ) - 1) * W.ord xM :=
  OrdUnitInfH.ord_eq_mul_ord p M H hpM A u hu xM hxM W hW

end S_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide (solution)
