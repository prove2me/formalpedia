-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_eq_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2b01ccfa-bb81-5920-b637-8133e0258e23

import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme jNum jNumQ constantCoeff_jNumQ jq ofPowerSeries_coeff_of_neg modularFunctionFieldFull"
p2m_open "ModularCurve"

namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull coe_jFull mem_chartAlg_iff chartAlgInf"
p2m_open "ModularCurve.IgusaScheme"

namespace CuspInfty

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

theorem jq_inv_eq : (jq)⁻¹ = HahnSeries.ofPowerSeries ℤ ℚ (PowerSeries.X * jNumQ⁻¹) := by
  have hj : jNumQ * jNumQ⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_jNumQ]; exact one_ne_zero)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [jq, map_mul (HahnSeries.ofPowerSeries ℤ ℚ), HahnSeries.ofPowerSeries_X, mul_mul_mul_comm,
    HahnSeries.single_mul_single, ← map_mul (HahnSeries.ofPowerSeries ℤ ℚ), hj,
    map_one (HahnSeries.ofPowerSeries ℤ ℚ), mul_one, neg_add_cancel, mul_one]
  rfl

def valHom : FN →+* LaurentSeries ℚ where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem valHom_apply (x : FN) : valHom N x = (x : LaurentSeries ℚ) := rfl

theorem adjoin_subset (x : FN) (hx : x ∈ Algebra.adjoin ℤℓ ({(jFull N)⁻¹} : Set FN)) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) ∧
      PowerSeries.constantCoeff y ∈ GaloisRep.ratLocalizedAt ℓ := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨PowerSeries.X * jNumQ⁻¹, ?_, ?_⟩
    · rw [IntermediateField.coe_inv, coe_jFull, jq_inv_eq]
    · rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
      exact zero_mem _
  | algebraMap c =>
    refine ⟨PowerSeries.C (c : ℚ), ?_, ?_⟩
    · rw [HahnSeries.ofPowerSeries_C]
      rfl
    · rw [PowerSeries.constantCoeff_C]
      exact c.2
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0⟩ := hx
    obtain ⟨b, hb, hb0⟩ := hy
    refine ⟨a + b, by rw [map_add, ha, hb]; rfl, ?_⟩
    rw [map_add]
    exact add_mem ha0 hb0
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0⟩ := hx
    obtain ⟨b, hb, hb0⟩ := hy
    refine ⟨a * b, by rw [map_mul, ha, hb]; rfl, ?_⟩
    rw [map_mul]
    exact mul_mem ha0 hb0

scoped instance isNoetherian_base : IsPrincipalIdealRing ℤℓ := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ

theorem exists_powerSeries_of_mem_chartAlgInf (x : FN) (hx : x ∈ chartAlgInf N ℓ) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) ∧
      PowerSeries.constantCoeff y ∈ GaloisRep.ratLocalizedAt ℓ := by
  classical
  set A := Algebra.adjoin ℤℓ ({(jFull N)⁻¹} : Set FN) with hA
  obtain ⟨P, hP, hPx⟩ : IsIntegral A x := (mem_chartAlg_iff N ℓ).mp hx

  choose lift hlift hlift0 using fun a : A => adjoin_subset N ℓ (a : FN) a.2

  have hinj := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℚ)
  let L : A →+* PowerSeries ℚ :=
    { toFun := lift
      map_one' := hinj (by rw [hlift, map_one]; rfl)
      map_mul' := fun a b => hinj (by rw [hlift, map_mul, hlift, hlift]; rfl)
      map_zero' := hinj (by rw [hlift, map_zero]; rfl)
      map_add' := fun a b => hinj (by rw [hlift, map_add, hlift, hlift]; rfl) }
  have hL : ∀ a : A, HahnSeries.ofPowerSeries ℤ ℚ (L a) = ((a : FN) : LaurentSeries ℚ) := hlift

  have hcomp : (algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)).comp L =
      (valHom N).comp (algebraMap A FN) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, valHom_apply]
    exact hL a
  have hint : IsIntegral (PowerSeries ℚ) ((x : FN) : LaurentSeries ℚ) := by
    refine ⟨P.map L, hP.map L, ?_⟩
    rw [eval₂_map, hcomp, ← valHom_apply N x, ← hom_eval₂, hPx, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨y, hy, ?_⟩

  have hrel : eval₂ L y P = 0 := by
    apply hinj
    change algebraMap (PowerSeries ℚ) (LaurentSeries ℚ) (eval₂ L y P) = _
    rw [hom_eval₂, hcomp, hy, ← valHom_apply N x, ← hom_eval₂, hPx, map_zero, map_zero]
  have hrel0 : eval₂ ((PowerSeries.constantCoeff (R := ℚ)).comp L) (PowerSeries.constantCoeff y) P = 0 := by
    rw [← hom_eval₂, hrel, map_zero]

  let L₀ : A →+* ℤℓ :=
    { toFun := fun a => ⟨PowerSeries.constantCoeff (L a), hlift0 a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hL₀ : (algebraMap ℤℓ ℚ).comp L₀ = (PowerSeries.constantCoeff (R := ℚ)).comp L :=
    RingHom.ext fun _ => rfl
  haveI : IsFractionRing ℤℓ ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  have hint0 : IsIntegral ℤℓ (PowerSeries.constantCoeff y) := by
    refine ⟨P.map L₀, hP.map L₀, ?_⟩
    rw [eval₂_map, hL₀]
    exact hrel0
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint0
  rw [← hc]
  exact c.2

theorem coeff_eq_zero_of_neg (x : FN) (hx : x ∈ chartAlgInf N ℓ) {k : ℤ} (hk : k < 0) :
    (x : LaurentSeries ℚ).coeff k = 0 := by
  obtain ⟨y, hy, -⟩ := exists_powerSeries_of_mem_chartAlgInf N ℓ x hx
  rw [← hy]
  exact ofPowerSeries_coeff_of_neg y hk

theorem coeff_zero_mem (x : FN) (hx : x ∈ chartAlgInf N ℓ) :
    (x : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt ℓ := by
  obtain ⟨y, hy, hy0⟩ := exists_powerSeries_of_mem_chartAlgInf N ℓ x hx
  rw [← hy, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hy0

theorem coeff_zero_ofPowerSeries (y : PowerSeries ℚ) :
    (HahnSeries.ofPowerSeries ℤ ℚ y).coeff 0 = PowerSeries.constantCoeff y := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_zero_mul (x y : FN) (hx : x ∈ chartAlgInf N ℓ) (hy : y ∈ chartAlgInf N ℓ) :
    ((x * y : FN) : LaurentSeries ℚ).coeff 0 =
      (x : LaurentSeries ℚ).coeff 0 * (y : LaurentSeries ℚ).coeff 0 := by
  obtain ⟨a, ha, -⟩ := exists_powerSeries_of_mem_chartAlgInf N ℓ x hx
  obtain ⟨b, hb, -⟩ := exists_powerSeries_of_mem_chartAlgInf N ℓ y hy
  rw [MulMemClass.coe_mul, ← ha, ← hb, ← map_mul (HahnSeries.ofPowerSeries ℤ ℚ),
    coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries, map_mul]

def evalInfty : chartAlgInf N ℓ →+* ℤℓ where
  toFun x := ⟨((x : FN) : LaurentSeries ℚ).coeff 0, coeff_zero_mem N ℓ x x.2⟩
  map_one' := by
    apply Subtype.ext
    show (((1 : chartAlgInf N ℓ) : FN) : LaurentSeries ℚ).coeff 0 = ((1 : ℤℓ) : ℚ)
    rw [OneMemClass.coe_one, OneMemClass.coe_one, OneMemClass.coe_one, HahnSeries.coeff_one, if_pos rfl]
  map_zero' := by
    apply Subtype.ext
    show (((0 : chartAlgInf N ℓ) : FN) : LaurentSeries ℚ).coeff 0 = ((0 : ℤℓ) : ℚ)
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  map_add' x y := by
    apply Subtype.ext
    show (((x + y : chartAlgInf N ℓ) : FN) : LaurentSeries ℚ).coeff 0 =
      ((x : FN) : LaurentSeries ℚ).coeff 0 + ((y : FN) : LaurentSeries ℚ).coeff 0
    rw [AddMemClass.coe_add, AddMemClass.coe_add, HahnSeries.coeff_add]
  map_mul' x y := by
    apply Subtype.ext
    show (((x * y : chartAlgInf N ℓ) : FN) : LaurentSeries ℚ).coeff 0 =
      ((x : FN) : LaurentSeries ℚ).coeff 0 * ((y : FN) : LaurentSeries ℚ).coeff 0
    rw [MulMemClass.coe_mul]
    exact coeff_zero_mul N ℓ _ _ x.2 y.2

theorem evalInfty_apply (x : chartAlgInf N ℓ) :
    ((evalInfty N ℓ x : ℤℓ) : ℚ) = ((x : FN) : LaurentSeries ℚ).coeff 0 := rfl

theorem evalInfty_algebraMap (c : ℤℓ) : evalInfty N ℓ (algebraMap ℤℓ (chartAlgInf N ℓ) c) = c := by
  apply Subtype.ext
  rw [evalInfty_apply, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤℓ ℚ FN]
  have h : (((algebraMap ℚ FN (algebraMap ℤℓ ℚ c)) : FN) : LaurentSeries ℚ) =
      HahnSeries.C (algebraMap ℤℓ ℚ c) :=
    congrArg (fun f : ℚ →+* LaurentSeries ℚ => f (algebraMap ℤℓ ℚ c))
      (Subsingleton.elim ((valHom N).comp (algebraMap ℚ FN)) (HahnSeries.C : ℚ →+* LaurentSeries ℚ))
  rw [h, HahnSeries.C_apply, HahnSeries.coeff_single_same]
  rfl

def evalInftyAlgHom : chartAlgInf N ℓ →ₐ[ℤℓ] ℤℓ :=
  { evalInfty N ℓ with commutes' := evalInfty_algebraMap N ℓ }

theorem exists_algHom_chartAlgInf_eq_coeff_zero :
    ∃ φ : ↥(chartAlgInf N ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(GaloisRep.ratLocalizedAt ℓ),
      ∀ x : ↥(chartAlgInf N ℓ),
        ((φ x : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) =
          ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 :=
  ⟨evalInftyAlgHom N ℓ, fun _ => rfl⟩

end CuspInfty
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme.CuspInfty"

end IgusaScheme
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme.CuspInfty P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme.CuspInfty P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme.CuspInfty P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero.ModularCurve.IgusaScheme"

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ φ : ↥(chartAlgInf N ℓ) →ₐ[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(GaloisRep.ratLocalizedAt ℓ),
      ∀ x : ↥(chartAlgInf N ℓ),
        ((φ x : ↥(GaloisRep.ratLocalizedAt ℓ)) : ℚ) =
          ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 :=
  ModularCurve.IgusaScheme.CuspInfty.exists_algHom_chartAlgInf_eq_coeff_zero N ℓ

end S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_eq_coeff_zero (solution)
