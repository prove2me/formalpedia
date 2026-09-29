-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a836ee66-ca78-5200-9f55-78843bdeef85

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_injective constantCoeff_jNum jq jq_mem divisorExpansions modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff coeffMap_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC jqModC_rat map_jqModC modularFunctionFieldC ssPlaces exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar"
p2m_open "ModularCurve"

namespace IgusaGaussRestriction

open HahnSeries IntermediateField AlgebraicCurve IsLocalRing

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem coeffMap_subtype_injective : Function.Injective (coeffMap A.subtype) := by
  intro x y h
  ext k
  have hk := congrArg (fun z : LaurentSeries L => z.coeff k) h
  simp only [coeffMap_coeff] at hk
  exact hk

theorem coeffMap_subtype_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : coeffMap A.subtype x ≠ 0 := by
  intro h
  apply hx
  have hx0 : x = 0 := coeffMap_subtype_injective A (by rw [h, map_zero])
  rw [hx0, map_zero]

theorem ne_zero_of_residue_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hx (map_zero _)

theorem residue_mul_ne_zero {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) :
    coeffMap (IsLocalRing.residue A) (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

theorem coeffMap_subtype_C (a : A) : coeffMap A.subtype (HahnSeries.C a) = HahnSeries.C (a : L) :=
  coeffMap_C _ _

theorem algebraMap_eq_C (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

end Coeff

section ConstantAction

variable (L : Type*) [Field L]

theorem coe_smul_eq_C_mul (F : IntermediateField L (LaurentSeries L)) (c : L) (x : F) :
    ((c • x : F) : LaurentSeries L) = HahnSeries.C c * (x : LaurentSeries L) := by
  rw [@Algebra.smul_def L F _ _ (SubalgebraClass.toAlgebra F), MulMemClass.coe_mul,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem coe_algebraMap_eq_C (F : IntermediateField L (LaurentSeries L)) (c : L) :
    ((algebraMap L F c : F) : LaurentSeries L) = HahnSeries.C c := by
  rw [SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem C_mem (F : IntermediateField L (LaurentSeries L)) (c : L) : HahnSeries.C c ∈ F := by
  rw [← algebraMap_eq_C]
  exact F.algebraMap_mem c

end ConstantAction

section Frac

variable {L : Type*} [Field L] (A : ValuationSubring L) (F₀ : IntermediateField L (LaurentSeries L))

def IsFrac (f : LaurentSeries L) : Prop :=
  ∃ (c : L) (x y : LaurentSeries A),
    coeffMap (IsLocalRing.residue A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
    coeffMap A.subtype x ∈ F₀ ∧ coeffMap A.subtype y ∈ F₀ ∧
    f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x

def Rescales : Prop :=
  ∀ w : LaurentSeries A, coeffMap A.subtype w ∈ F₀ → w ≠ 0 →
    ∃ (c : L) (w₁ : LaurentSeries A), c ≠ 0 ∧ coeffMap (IsLocalRing.residue A) w₁ ≠ 0 ∧
      HahnSeries.C c * coeffMap A.subtype w = coeffMap A.subtype w₁

variable {A F₀}

theorem isFrac_C (c : L) : IsFrac A F₀ (HahnSeries.C c) :=
  ⟨c, 1, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; exact one_ne_zero,
    by rw [map_one]; exact one_mem _, by rw [map_one]; exact one_mem _, rfl⟩

theorem isFrac_zero : IsFrac A F₀ 0 := by
  have h := isFrac_C (A := A) (F₀ := F₀) 0
  rwa [map_zero] at h

theorem isFrac_one : IsFrac A F₀ 1 := by
  have h := isFrac_C (A := A) (F₀ := F₀) 1
  rwa [map_one] at h

theorem IsFrac.eq_zero_of_const_eq_zero {f : LaurentSeries L} {x y : LaurentSeries A}
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : f * coeffMap A.subtype y = HahnSeries.C (0 : L) * coeffMap A.subtype x) : f = 0 := by
  rw [map_zero, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (coeffMap_subtype_ne_zero A hy)

theorem isFrac_mul {f g : LaurentSeries L} (hf : IsFrac A F₀ f) (hg : IsFrac A F₀ g) :
    IsFrac A F₀ (f * g) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  obtain ⟨c', x', y', hx', hy', hxF', hyF', hg⟩ := hg
  refine ⟨c * c', x * x', y * y', residue_mul_ne_zero A hx hx', residue_mul_ne_zero A hy hy', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_mem hxF hxF'
  · rw [map_mul]; exact mul_mem hyF hyF'
  · rw [map_mul, map_mul, map_mul]
    calc f * g * (coeffMap A.subtype y * coeffMap A.subtype y')
        = (f * coeffMap A.subtype y) * (g * coeffMap A.subtype y') := by ring
      _ = (HahnSeries.C c * coeffMap A.subtype x) * (HahnSeries.C c' * coeffMap A.subtype x') := by
          rw [hf, hg]
      _ = HahnSeries.C c * HahnSeries.C c' * (coeffMap A.subtype x * coeffMap A.subtype x') := by ring

theorem isFrac_neg {f : LaurentSeries L} (hf : IsFrac A F₀ f) : IsFrac A F₀ (-f) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  refine ⟨-c, x, y, hx, hy, hxF, hyF, ?_⟩
  rw [neg_mul, hf, map_neg, neg_mul]

theorem isFrac_inv {f : LaurentSeries L} (hf : IsFrac A F₀ f) : IsFrac A F₀ f⁻¹ := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  rcases eq_or_ne c 0 with rfl | hc
  · rw [IsFrac.eq_zero_of_const_eq_zero hy hf, inv_zero]
    exact isFrac_zero
  have hCc : (HahnSeries.C c : LaurentSeries L) ≠ 0 := HahnSeries.C_ne_zero hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hf
    exact mul_ne_zero hCc (coeffMap_subtype_ne_zero A hx) hf.symm
  refine ⟨c⁻¹, y, x, hy, hx, hyF, hxF, ?_⟩
  refine mul_left_cancel₀ (mul_ne_zero hf0 hCc) ?_
  calc f * HahnSeries.C c * (f⁻¹ * coeffMap A.subtype x)
      = f * f⁻¹ * (HahnSeries.C c * coeffMap A.subtype x) := by ring
    _ = f * coeffMap A.subtype y := by rw [mul_inv_cancel₀ hf0, one_mul, hf]
    _ = f * (HahnSeries.C c * HahnSeries.C c⁻¹) * coeffMap A.subtype y := by
        rw [← map_mul, mul_inv_cancel₀ hc, map_one, mul_one]
    _ = f * HahnSeries.C c * (HahnSeries.C c⁻¹ * coeffMap A.subtype y) := by ring

theorem isFrac_add_of_mul (hR : Rescales A F₀) {f g : LaurentSeries L} {c : L} {a : A}
    {x y x' y' : LaurentSeries A}
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) (hy' : coeffMap (IsLocalRing.residue A) y' ≠ 0)
    (hxF : coeffMap A.subtype x ∈ F₀) (hyF : coeffMap A.subtype y ∈ F₀)
    (hxF' : coeffMap A.subtype x' ∈ F₀) (hyF' : coeffMap A.subtype y' ∈ F₀)
    (hf : f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x)
    (hg : g * coeffMap A.subtype y' = HahnSeries.C (c * a) * coeffMap A.subtype x') :
    IsFrac A F₀ (f + g) := by

  set w : LaurentSeries A := x * y' + HahnSeries.C a * x' * y with hw_def
  have hwF : coeffMap A.subtype w ∈ F₀ := by
    rw [hw_def, map_add, map_mul, map_mul, map_mul, coeffMap_subtype_C]
    exact add_mem (mul_mem hxF hyF') (mul_mem (mul_mem (C_mem L F₀ _) hxF') hyF)
  have hsum : (f + g) * coeffMap A.subtype (y * y') = HahnSeries.C c * coeffMap A.subtype w := by
    simp only [hw_def, map_add, map_mul, coeffMap_subtype_C]
    calc (f + g) * (coeffMap A.subtype y * coeffMap A.subtype y')
        = (f * coeffMap A.subtype y) * coeffMap A.subtype y'
            + (g * coeffMap A.subtype y') * coeffMap A.subtype y := by ring
      _ = HahnSeries.C c * coeffMap A.subtype x * coeffMap A.subtype y'
            + HahnSeries.C c * HahnSeries.C (a : L) * coeffMap A.subtype x' * coeffMap A.subtype y := by
          rw [hf, hg, map_mul]
      _ = HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y'
            + HahnSeries.C (a : L) * coeffMap A.subtype x' * coeffMap A.subtype y) := by ring
  rcases eq_or_ne w 0 with hw0 | hw0
  ·
    have hzero : f + g = 0 := by
      rw [hw0, map_zero, mul_zero] at hsum
      exact (mul_eq_zero.mp hsum).resolve_right
        (coeffMap_subtype_ne_zero A (residue_mul_ne_zero A hy hy'))
    rw [hzero]
    exact isFrac_zero
  · obtain ⟨c₁, w₁, hc₁, hw₁, hresc⟩ := hR w hwF hw0
    refine ⟨c / c₁, w₁, y * y', hw₁, residue_mul_ne_zero A hy hy', ?_, ?_, ?_⟩
    · rw [← hresc]
      exact mul_mem (C_mem L F₀ _) hwF
    · rw [map_mul]; exact mul_mem hyF hyF'
    · rw [hsum, ← hresc, ← mul_assoc, ← map_mul, div_mul_cancel₀ c hc₁]

theorem isFrac_add (hR : Rescales A F₀) {f g : LaurentSeries L} (hf : IsFrac A F₀ f)
    (hg : IsFrac A F₀ g) : IsFrac A F₀ (f + g) := by
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ := hf
  obtain ⟨c', x', y', hx', hy', hxF', hyF', hg⟩ := hg
  rcases eq_or_ne c 0 with rfl | hc
  · rw [IsFrac.eq_zero_of_const_eq_zero hy hf, zero_add]
    exact ⟨c', x', y', hx', hy', hxF', hyF', hg⟩
  rcases eq_or_ne c' 0 with rfl | hc'
  · rw [IsFrac.eq_zero_of_const_eq_zero hy' hg, add_zero]
    exact ⟨c, x, y, hx, hy, hxF, hyF, hf⟩

  rcases A.mem_or_inv_mem (c' / c) with hmem | hmem
  · have hc'eq : c' = c * (⟨c' / c, hmem⟩ : A) := by
      show c' = c * (c' / c)
      rw [mul_div_cancel₀ c' hc]
    rw [hc'eq] at hg
    exact isFrac_add_of_mul hR hy hy' hxF hyF hxF' hyF' hf hg
  · have hceq : c = c' * (⟨(c' / c)⁻¹, hmem⟩ : A) := by
      show c = c' * (c' / c)⁻¹
      rw [inv_div, mul_div_cancel₀ c hc']
    rw [hceq] at hf
    rw [add_comm]
    exact isFrac_add_of_mul hR hy' hy hxF' hyF' hxF hyF hg hf

theorem isFrac_of_mem_closure (hR : Rescales A F₀) {S : Set (LaurentSeries L)}
    (hS : ∀ s ∈ S, IsFrac A F₀ s) {f : LaurentSeries L}
    (hf : f ∈ Subfield.closure (Set.range (algebraMap L (LaurentSeries L)) ∪ S)) : IsFrac A F₀ f := by
  induction hf using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hyS
      · rw [algebraMap_eq_C]
        exact isFrac_C a
      · exact hS y hyS
  | one => exact isFrac_one
  | add x y _ _ hx hy => exact isFrac_add hR hx hy
  | neg x _ hx => exact isFrac_neg hx
  | inv x _ hx => exact isFrac_inv hx
  | mul x y _ _ hx hy => exact isFrac_mul hx hy

end Frac

section Read

variable {L : Type*} [Field L] (A : ValuationSubring L) (F₀ : IntermediateField L (LaurentSeries L))

theorem mem_iff_const_mem (V : ValuationSubring F₀)
    (hVconst : ∀ c : L, algebraMap L F₀ c ∈ V ↔ c ∈ A)
    (hVunit : ∀ (x : LaurentSeries A) (hx : coeffMap A.subtype x ∈ F₀),
      coeffMap (IsLocalRing.residue A) x ≠ 0 →
        (⟨coeffMap A.subtype x, hx⟩ : F₀) ∈ V ∧ (⟨coeffMap A.subtype x, hx⟩ : F₀)⁻¹ ∈ V)
    (f : F₀) {c : L} {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hxF : coeffMap A.subtype x ∈ F₀) (hyF : coeffMap A.subtype y ∈ F₀)
    (hf : (f : LaurentSeries L) * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x) :
    f ∈ V ↔ c ∈ A := by
  set X : F₀ := ⟨coeffMap A.subtype x, hxF⟩ with hX
  set Y : F₀ := ⟨coeffMap A.subtype y, hyF⟩ with hY
  have hX0 : X ≠ 0 := fun h => coeffMap_subtype_ne_zero A hx (congrArg Subtype.val h)
  have hY0 : Y ≠ 0 := fun h => coeffMap_subtype_ne_zero A hy (congrArg Subtype.val h)
  have hfXY : f * Y = algebraMap L F₀ c * X := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_algebraMap_eq_C]
    exact hf
  obtain ⟨hXV, hXinv⟩ := hVunit x hxF hx
  obtain ⟨hYV, hYinv⟩ := hVunit y hyF hy
  rw [← hVconst c]
  constructor
  · intro hfV
    have h : algebraMap L F₀ c = f * Y * X⁻¹ := by
      rw [hfXY, mul_inv_cancel_right₀ hX0]
    rw [h]
    exact mul_mem (mul_mem hfV hYV) hXinv
  · intro hcV
    have h : f = algebraMap L F₀ c * X * Y⁻¹ := by
      rw [← hfXY, mul_inv_cancel_right₀ hY0]
    rw [h]
    exact mul_mem (mul_mem hcV hXV) hYinv

theorem gauss_iff_const_mem (f : LaurentSeries L) {c : L} (hc : c ≠ 0) {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (hf : f * coeffMap A.subtype y = HahnSeries.C c * coeffMap A.subtype x) :
    (∃ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 ∧
        f * coeffMap A.subtype y' = coeffMap A.subtype x') ↔ c ∈ A := by
  constructor
  · rintro ⟨x', y', hy', hf'⟩
    by_contra hcA

    have hnu : c⁻¹ ∈ A.nonunits := (ValuationSubring.inv_mem_nonunits_iff A).mpr (Or.inr hcA)
    obtain ⟨hcinv, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnu
    have hres : IsLocalRing.residue A ⟨c⁻¹, hcinv⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax

    have hkey : coeffMap A.subtype (x * y') = coeffMap A.subtype (HahnSeries.C ⟨c⁻¹, hcinv⟩ * x' * y) := by
      rw [map_mul, map_mul, map_mul, coeffMap_subtype_C]
      have h1 : HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y') =
          coeffMap A.subtype x' * coeffMap A.subtype y := by
        calc HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y')
            = (HahnSeries.C c * coeffMap A.subtype x) * coeffMap A.subtype y' := by ring
          _ = f * coeffMap A.subtype y * coeffMap A.subtype y' := by rw [hf]
          _ = (f * coeffMap A.subtype y') * coeffMap A.subtype y := by ring
          _ = coeffMap A.subtype x' * coeffMap A.subtype y := by rw [hf']
      calc coeffMap A.subtype x * coeffMap A.subtype y'
          = HahnSeries.C (c⁻¹ * c) * (coeffMap A.subtype x * coeffMap A.subtype y') := by
            rw [inv_mul_cancel₀ hc, map_one, one_mul]
        _ = HahnSeries.C (c⁻¹ : L) * (HahnSeries.C c * (coeffMap A.subtype x * coeffMap A.subtype y')) := by
            rw [map_mul, mul_assoc]
        _ = HahnSeries.C (c⁻¹ : L) * coeffMap A.subtype x' * coeffMap A.subtype y := by
            rw [h1, mul_assoc]
    have hkey' := congrArg (coeffMap (IsLocalRing.residue A)) (coeffMap_subtype_injective A hkey)
    rw [map_mul, map_mul, map_mul, coeffMap_C, hres, map_zero, zero_mul, zero_mul] at hkey'
    exact mul_ne_zero hx hy' hkey'
  · intro hcA
    refine ⟨HahnSeries.C ⟨c, hcA⟩ * x, y, hy, ?_⟩
    rw [map_mul, coeffMap_subtype_C]
    exact hf

end Read

section Modular

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (M' : ℕ)

theorem coeffEmb_qExpand (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N x) = qExpand (AlgebraicClosure ℚ) N (coeffEmb (AlgebraicClosure ℚ) x) :=
  coeffMap_qExpand _ N x

theorem coeffEmb_jq_eq : coeffEmb (AlgebraicClosure ℚ) jq = coeffMap A.subtype (jqModC A) := by
  show (jq).map (algebraMap ℚ (AlgebraicClosure ℚ)) = (jqModC A).map A.subtype
  rw [← jqModC_rat, map_jqModC, map_jqModC]

theorem coeffMap_residue_jqModC_ne_zero : coeffMap (IsLocalRing.residue A) (jqModC A) ≠ 0 := by
  have h : coeffMap (IsLocalRing.residue A) (jqModC A) = jqModC (ResidueField A) := map_jqModC _
  rw [h]
  intro h0
  have h1 := congrArg (fun z : LaurentSeries (ResidueField A) => z.coeff (0 + (-1))) h0
  simp only [jqModC, HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.coeff_zero] at h1
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one] at h1
  exact one_ne_zero h1

theorem isFrac_coeffEmb_divisorExpansions {s : LaurentSeries ℚ} (hs : s ∈ divisorExpansions M') :
    IsFrac A (modularFunctionFieldBar M') (coeffEmb (AlgebraicClosure ℚ) s) := by
  obtain ⟨d, hd, hdM, rfl⟩ := hs
  refine ⟨1, qExpand A d (jqModC A), 1, ?_, by rw [map_one]; exact one_ne_zero, ?_,
    by rw [map_one]; exact one_mem _, ?_⟩
  · rw [coeffMap_qExpand]
    intro h0
    exact coeffMap_residue_jqModC_ne_zero A
      (qExpand_injective (R := ResidueField A) d (by rw [h0, map_zero]))
  · rw [coeffMap_qExpand, ← coeffEmb_jq_eq, ← coeffEmb_qExpand]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M' hdM)
  · rw [map_one, mul_one, map_one, one_mul, coeffMap_qExpand, ← coeffEmb_jq_eq, ← coeffEmb_qExpand]

theorem isFrac_coeffEmb_of_mem (hR : Rescales A (modularFunctionFieldBar M')) {g : LaurentSeries ℚ}
    (hg : g ∈ modularFunctionFieldFull M') :
    IsFrac A (modularFunctionFieldBar M') (coeffEmb (AlgebraicClosure ℚ) g) := by
  have hg' : g ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M') := by
    rw [← IntermediateField.adjoin_toSubfield]
    exact hg
  clear hg
  induction hg' using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hyS
      · rw [algebraMap_eq_C, coeffEmb, coeffMap_C]
        exact isFrac_C _
      · exact isFrac_coeffEmb_divisorExpansions A M' hyS
  | one => rw [map_one]; exact isFrac_one
  | add x y _ _ hx hy => rw [map_add]; exact isFrac_add hR hx hy
  | neg x _ hx => rw [map_neg]; exact isFrac_neg hx
  | inv x _ hx => rw [map_inv₀]; exact isFrac_inv hx
  | mul x y _ _ hx hy => rw [map_mul]; exact isFrac_mul hx hy

theorem isFrac_of_mem_modularFunctionFieldBar (hR : Rescales A (modularFunctionFieldBar M'))
    {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ modularFunctionFieldBar M') :
    IsFrac A (modularFunctionFieldBar M') f := by
  rw [mem_laurentBaseChange_iff] at hf
  refine isFrac_of_mem_closure hR ?_ hf
  rintro s ⟨g, hg, rfl⟩
  exact isFrac_coeffEmb_of_mem A M' hR hg

theorem rescales_modularFunctionFieldBar [NeZero M'] (q : ℕ) [Fact q.Prime] (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ FullLevel.fieldBar q M') :
    Rescales A (modularFunctionFieldBar M') := by
  intro w hw hw0
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  set g : ↥(FullLevel.fieldBar q M') := ⟨coeffMap A.subtype w, hle hw⟩ with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    apply hw0
    apply coeffMap_subtype_injective A
    rw [map_zero]
    exact congrArg Subtype.val h
  have h₀ : ((((1 : AlgebraicClosure ℚ) • g : ↥(FullLevel.fieldBar q M'))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype w := by
    rw [coe_smul_eq_C_mul, map_one, one_mul]
  obtain ⟨c, hc, y, hy, hyres⟩ :=
    ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
      q (q ^ 2 * M') (FullLevel.levelH q M') A hA g hg0 1 one_ne_zero w h₀
  refine ⟨c, y, hc, hyres, ?_⟩
  rw [← hy, coe_smul_eq_C_mul]

end Modular

end IgusaGaussRestriction

end ModularCurve

end

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s)) :
    ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q) := by
  intro f

  have hResc := ModularCurve.IgusaGaussRestriction.rescales_modularFunctionFieldBar A M' q hA hle
  obtain ⟨c, x, y, hx, hy, hxF, hyF, hf⟩ :=
    ModularCurve.IgusaGaussRestriction.isFrac_of_mem_modularFunctionFieldBar A M' hResc f.2
  rw [hIg_inf, IntermediateField.coe_inclusion]
  rcases eq_or_ne c 0 with rfl | hc
  ·
    have hf0 : f = 0 :=
      Subtype.ext (ModularCurve.IgusaGaussRestriction.IsFrac.eq_zero_of_const_eq_zero hy hf)
    subst hf0
    refine ⟨fun _ => ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩, fun _ => zero_mem _⟩
    rw [ZeroMemClass.coe_zero, zero_mul, map_zero]

  rw [ModularCurve.IgusaGaussRestriction.gauss_iff_const_mem A (f : LaurentSeries (AlgebraicClosure ℚ))
    hc hx hy hf]
  refine ModularCurve.IgusaGaussRestriction.mem_iff_const_mem A (modularFunctionFieldBar M') R₀.integers
    R₀.algebraMap_mem_iff ?_ f hx hy hxF hyF hf

  intro z hz hzred
  obtain ⟨hzV, hzres⟩ := hR₀ z hz
  have hres_ne : R₀.residue ⟨_, hzV⟩ ≠ 0 := by
    intro h0
    apply hzred
    rw [← hzres, h0]
    rfl
  have hunit : IsUnit (⟨_, hzV⟩ : R₀.integers) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← R₀.ker_residue, RingHom.mem_ker]
    exact hres_ne
  have hval : R₀.integers.valuation (⟨coeffMap A.subtype z, hz⟩ : ↥(modularFunctionFieldBar M')) = 1 :=
    (ValuationSubring.valuation_eq_one_iff R₀.integers ⟨_, hzV⟩).mp hunit
  refine ⟨hzV, ValuationSubring.mem_of_valuation_le_one _ _ ?_⟩
  rw [map_inv₀, hval, inv_one]

end S_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_constantReduction_integers_iff_inclusion_mem_igusaGaussRing_of_eq_two_of_dvd (solution)
