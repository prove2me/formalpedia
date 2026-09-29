-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4a355c84-2361-5bd4-bb2a-6b6abd7d220a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve ModularCurve.IgusaScheme AlgebraicCurve.TwoChartIntegralModel"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme jNum jNumQ constantCoeff_jNumQ jq modularFunctionFieldFull"
p2m_open "ModularCurve"

namespace CuspInftyGeneric

variable (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra R ℚ] [IsFractionRing R ℚ]
  (N : ℕ) [NeZero N] [Algebra R ↥(modularFunctionFieldFull N)] [IsScalarTower R ℚ ↥(modularFunctionFieldFull N)]

set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)

section RingLemmas

variable {B S K : Type*} [CommRing B] [CommRing S] [CommRing K]

def liftOfRange (i : S →+* K) (hi : Function.Injective i) (g : B →+* K)
    (h : ∀ b, g b ∈ i.range) : B →+* S :=
  (RingEquiv.ofBijective i.rangeRestrict
      ⟨fun _ _ e => hi (congrArg Subtype.val e), i.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict i.range h)

theorem liftOfRange_spec (i : S →+* K) (hi : Function.Injective i) (g : B →+* K)
    (h : ∀ b, g b ∈ i.range) (b : B) : i (liftOfRange i hi g h b) = g b := by
  set e := RingEquiv.ofBijective i.rangeRestrict
      ⟨fun _ _ e => hi (congrArg Subtype.val e), i.rangeRestrict_surjective⟩
  have : e (e.symm ⟨g b, h b⟩) = ⟨g b, h b⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val this

end RingLemmas

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

theorem coe_algebraMap_rat (q : ℚ) : ((algebraMap ℚ FN q : FN) : LaurentSeries ℚ) = HahnSeries.C q :=
  congrArg (fun f : ℚ →+* LaurentSeries ℚ => f q)
    (Subsingleton.elim ((valHom N).comp (algebraMap ℚ FN)) (HahnSeries.C : ℚ →+* LaurentSeries ℚ))

theorem coe_algebraMap_base (c : R) :
    ((algebraMap R FN c : FN) : LaurentSeries ℚ) = HahnSeries.C (algebraMap R ℚ c) := by
  rw [IsScalarTower.algebraMap_apply R ℚ FN c, coe_algebraMap_rat]

theorem adjoin_subset (x : FN) (hx : x ∈ Algebra.adjoin R ({(jFull N)⁻¹} : Set FN)) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) ∧
      PowerSeries.constantCoeff y ∈ (algebraMap R ℚ).range := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨PowerSeries.X * jNumQ⁻¹, ?_, ?_⟩
    · rw [IntermediateField.coe_inv, coe_jFull, jq_inv_eq]
    · rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]
      exact zero_mem _
  | algebraMap c =>
    refine ⟨PowerSeries.C (algebraMap R ℚ c), ?_, ?_⟩
    · rw [HahnSeries.ofPowerSeries_C, coe_algebraMap_base]
    · rw [PowerSeries.constantCoeff_C]
      exact ⟨c, rfl⟩
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

theorem exists_powerSeries_of_mem_chartAlgInf (x : FN) (hx : x ∈ chartAlgInf R FN (jFull N)) :
    ∃ y : PowerSeries ℚ, HahnSeries.ofPowerSeries ℤ ℚ y = (x : LaurentSeries ℚ) ∧
      PowerSeries.constantCoeff y ∈ (algebraMap R ℚ).range := by
  classical
  set A := Algebra.adjoin R ({(jFull N)⁻¹} : Set FN) with hA
  obtain ⟨P, hP, hPx⟩ : IsIntegral A x := (mem_chartAlg_iff R FN).mp hx

  choose lift hlift hlift0 using fun a : A => adjoin_subset R N (a : FN) a.2
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

  have hRinj : Function.Injective (algebraMap R ℚ) := IsFractionRing.injective R ℚ
  let L₀ : A →+* R := liftOfRange (algebraMap R ℚ) hRinj ((PowerSeries.constantCoeff (R := ℚ)).comp L)
    (fun a => hlift0 a)
  have hL₀ : (algebraMap R ℚ).comp L₀ = (PowerSeries.constantCoeff (R := ℚ)).comp L :=
    RingHom.ext fun a => liftOfRange_spec _ hRinj _ _ a
  have hint0 : IsIntegral R (PowerSeries.constantCoeff y) := by
    refine ⟨P.map L₀, hP.map L₀, ?_⟩
    rw [eval₂_map, hL₀]
    exact hrel0
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint0
  exact ⟨c, hc⟩

theorem coeff_zero_ofPowerSeries (y : PowerSeries ℚ) :
    (HahnSeries.ofPowerSeries ℤ ℚ y).coeff 0 = PowerSeries.constantCoeff y := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_zero_mem (x : FN) (hx : x ∈ chartAlgInf R FN (jFull N)) :
    (x : LaurentSeries ℚ).coeff 0 ∈ (algebraMap R ℚ).range := by
  obtain ⟨y, hy, hy0⟩ := exists_powerSeries_of_mem_chartAlgInf R N x hx
  rw [← hy, coeff_zero_ofPowerSeries]
  exact hy0

theorem coeff_zero_mul (x y : FN) (hx : x ∈ chartAlgInf R FN (jFull N)) (hy : y ∈ chartAlgInf R FN (jFull N)) :
    ((x * y : FN) : LaurentSeries ℚ).coeff 0 =
      (x : LaurentSeries ℚ).coeff 0 * (y : LaurentSeries ℚ).coeff 0 := by
  obtain ⟨a, ha, -⟩ := exists_powerSeries_of_mem_chartAlgInf R N x hx
  obtain ⟨b, hb, -⟩ := exists_powerSeries_of_mem_chartAlgInf R N y hy
  rw [MulMemClass.coe_mul, ← ha, ← hb, ← map_mul (HahnSeries.ofPowerSeries ℤ ℚ),
    coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries, coeff_zero_ofPowerSeries, map_mul]

def evalInftyRat : chartAlgInf R FN (jFull N) →+* ℚ where
  toFun x := ((x : FN) : LaurentSeries ℚ).coeff 0
  map_one' := by
    show (((1 : chartAlgInf R FN (jFull N)) : FN) : LaurentSeries ℚ).coeff 0 = 1
    rw [OneMemClass.coe_one, OneMemClass.coe_one, HahnSeries.coeff_one, if_pos rfl]
  map_zero' := by
    show (((0 : chartAlgInf R FN (jFull N)) : FN) : LaurentSeries ℚ).coeff 0 = 0
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, HahnSeries.coeff_zero]
  map_add' x y := by
    show (((x + y : chartAlgInf R FN (jFull N)) : FN) : LaurentSeries ℚ).coeff 0 =
      ((x : FN) : LaurentSeries ℚ).coeff 0 + ((y : FN) : LaurentSeries ℚ).coeff 0
    rw [AddMemClass.coe_add, AddMemClass.coe_add, HahnSeries.coeff_add]
  map_mul' x y := by
    show (((x * y : chartAlgInf R FN (jFull N)) : FN) : LaurentSeries ℚ).coeff 0 =
      ((x : FN) : LaurentSeries ℚ).coeff 0 * ((y : FN) : LaurentSeries ℚ).coeff 0
    rw [MulMemClass.coe_mul]
    exact coeff_zero_mul R N _ _ x.2 y.2

def evalInfty : chartAlgInf R FN (jFull N) →+* R :=
  liftOfRange (algebraMap R ℚ) (IsFractionRing.injective R ℚ) (evalInftyRat R N)
    (fun x => coeff_zero_mem R N x x.2)

theorem algebraMap_evalInfty (x : chartAlgInf R FN (jFull N)) :
    algebraMap R ℚ (evalInfty R N x) = ((x : FN) : LaurentSeries ℚ).coeff 0 :=
  liftOfRange_spec _ _ _ _ x

theorem evalInfty_algebraMap (c : R) : evalInfty R N (algebraMap R (chartAlgInf R FN (jFull N)) c) = c := by
  apply IsFractionRing.injective R ℚ
  rw [algebraMap_evalInfty, Subalgebra.coe_algebraMap, coe_algebraMap_base, HahnSeries.C_apply,
    HahnSeries.coeff_single_same]

def evalInftyAlgHom : chartAlgInf R FN (jFull N) →ₐ[R] R :=
  { evalInfty R N with commutes' := evalInfty_algebraMap R N }

end CuspInftyGeneric
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve.CuspInftyGeneric"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve.CuspInftyGeneric P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve.CuspInftyGeneric P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero.ModularCurve AlgebraicCurve.TwoChartIntegralModel"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Algebra R ℚ] [IsFractionRing R ℚ]
    (N : ℕ) [NeZero N] [Algebra R ↥(modularFunctionFieldFull N)] [IsScalarTower R ℚ ↥(modularFunctionFieldFull N)] :
    ∃ φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)) →ₐ[R] R,
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R ↥(modularFunctionFieldFull N)
        (ModularCurve.IgusaScheme.jFull N)),
        algebraMap R ℚ (φ x) = ((x : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ).coeff 0 :=
  ⟨ModularCurve.CuspInftyGeneric.evalInftyAlgHom R N, fun x => ModularCurve.CuspInftyGeneric.algebraMap_evalInfty R N x⟩

end S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_algebraMap_eq_coeff_zero (solution)
