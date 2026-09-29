-- Prove2me | solution 1 for ModularCurve.map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/fac416c1-ad20-56c1-85b3-d4c0dee40d43

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

namespace FrobCong

open ModularCurve

open HahnSeries

section Pres

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]

noncomputable abbrev toL (L : Type) [Field L] [Algebra A L] (x : PowerSeries A) : LaurentSeries L :=
  ofPowerSeries ℤ L (x.map (algebraMap A L))

noncomputable abbrev toκ (x : PowerSeries A) : LaurentSeries (IsLocalRing.ResidueField A) :=
  ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A))

variable (L) in

def Pres (f : LaurentSeries L) (x y : PowerSeries A) : Prop :=
  y.map (IsLocalRing.residue A) ≠ 0 ∧ f * toL L y = toL L x

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_mul (x y : PowerSeries A) : toL L (x * y) = toL L x * toL L y := by simp [toL, map_mul]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_sub (x y : PowerSeries A) : toL L (x - y) = toL L x - toL L y := by simp [toL, map_sub]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_one : toL L (1 : PowerSeries A) = 1 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_zero : toL L (0 : PowerSeries A) = 0 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_pow (x : PowerSeries A) (n : ℕ) : toL L (x ^ n) = toL L x ^ n := by simp [toL, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_mul (x y : PowerSeries A) : toκ (x * y) = toκ x * toκ y := by simp [toκ, map_mul]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_sub (x y : PowerSeries A) : toκ (x - y) = toκ x - toκ y := by simp [toκ, map_sub]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_pow (x : PowerSeries A) (n : ℕ) : toκ (x ^ n) = toκ x ^ n := by simp [toκ, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_zero : toκ (0 : PowerSeries A) = 0 := by simp [toκ]
omit [IsFractionRing A L] in
theorem toκ_eq_zero_iff (x : PowerSeries A) : toκ x = 0 ↔ x.map (IsLocalRing.residue A) = 0 := by
  constructor
  · intro e; exact ofPowerSeries_injective (e.trans (map_zero _).symm)
  · intro e; rw [toκ, e, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem toL_injective : Function.Injective (toL (A := A) L) := fun x y h =>
  PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) (ofPowerSeries_injective h)

theorem Pres.mul {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f * g) (x * x') (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

theorem Pres.pow {f : LaurentSeries L} {x y : PowerSeries A} (hf : Pres L f x y) (n : ℕ) :
    Pres L (f ^ n) (x ^ n) (y ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem Pres.sub {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f - g) (x * y' - x' * y) (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_sub, toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

omit [IsFractionRing A L] in
theorem Pres.one : Pres L (1 : LaurentSeries L) (1 : PowerSeries A) 1 :=
  ⟨by simp, by simp⟩

theorem Pres.unique {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    x.map (IsLocalRing.residue A) * y'.map (IsLocalRing.residue A)
      = x'.map (IsLocalRing.residue A) * y.map (IsLocalRing.residue A) := by
  have : toL L (x * y') = toL L (x' * y) := by
    rw [toL_mul, toL_mul, ← h.2, ← h'.2]; ring
  have := toL_injective this
  rw [← map_mul, ← map_mul, this]

theorem Pres.ne_zero {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : f ≠ 0 := by
  rintro rfl
  have h2 := h.2
  rw [zero_mul, eq_comm] at h2
  have : x = 0 := toL_injective (L := L) (h2.trans (toL_zero (L := L)).symm)
  exact hx (by simp [this])

theorem Pres.inv {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : Pres L f⁻¹ y x := by
  refine ⟨hx, ?_⟩
  have hf := h.ne_zero hx
  rw [← h.2, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

theorem Pres.map_ne_zero_of_inv {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (hf : f ≠ 0) (h' : Pres L f⁻¹ x' y') :
    x.map (IsLocalRing.residue A) ≠ 0 := by
  have hp := h.mul h'
  rw [mul_inv_cancel₀ hf] at hp
  have hu := hp.unique Pres.one
  simp only [map_mul, map_one, mul_one, one_mul] at hu
  intro hx0
  rw [hx0, zero_mul] at hu
  exact mul_ne_zero h.1 h'.1 hu.symm

theorem Pres.red_eq {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    toκ x / toκ y = toκ x' / toκ y' := by
  have hy : toκ y ≠ 0 := fun e => h.1 ((toκ_eq_zero_iff y).mp e)
  have hy' : toκ y' ≠ 0 := fun e => h'.1 ((toκ_eq_zero_iff y').mp e)
  have e := congrArg (ofPowerSeries ℤ (IsLocalRing.ResidueField A)) (h.unique h')
  rw [map_mul, map_mul] at e
  rw [div_eq_div_iff hy hy']
  exact e

end Pres

end FrobCong
p2m_reactivate "P2MW.S_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand.FrobCong"

open FrobCong HahnSeries in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) :
    j ∈ W₀ ∧ σ j - j ^ p ∈ W₀.nonunits := by
  classical
  obtain ⟨⟨x₀, y₀, hy₀, hj₀, hr₀⟩, ⟨x₁, y₁, hy₁, hj₁, hr₁⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have Pj : Pres L ((j : ↥K) : LaurentSeries L) x₀ y₀ := ⟨hy₀, by rw [hj]; exact hj₀⟩
  have Pσj : Pres L ((σ j : ↥K) : LaurentSeries L) x₁ y₁ := ⟨hy₁, by rw [hσj]; exact hj₁⟩
  have hy₀κ : toκ y₀ ≠ 0 := fun e => hy₀ ((toκ_eq_zero_iff y₀).mp e)
  have hy₁κ : toκ y₁ ≠ 0 := fun e => hy₁ ((toκ_eq_zero_iff y₁).mp e)
  have hx₀ : toκ x₀ = ModularCurve.jqModC _ * toκ y₀ := by rw [← hr₀, div_mul_cancel₀ _ hy₀κ]
  have hx₁ : toκ x₁ = ModularCurve.jqModC _ ^ p * toκ y₁ := by rw [← hr₁, div_mul_cancel₀ _ hy₁κ]
  refine ⟨(hW₀ j).mpr ⟨x₀, y₀, hy₀, Pj.2⟩, ?_⟩

  have Pg : Pres L (((σ j - j ^ p : ↥K)) : LaurentSeries L) (x₁ * y₀ ^ p - x₀ ^ p * y₁) (y₁ * y₀ ^ p) := by
    push_cast; exact Pσj.sub (Pj.pow p)
  have hX : (x₁ * y₀ ^ p - x₀ ^ p * y₁).map (IsLocalRing.residue A) = 0 := by
    rw [← toκ_eq_zero_iff, toκ_sub, toκ_mul, toκ_mul, toκ_pow, toκ_pow, hx₀, hx₁]; ring
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : σ j - j ^ p = 0
  · exact Or.inl h0
  right
  intro hinv
  obtain ⟨x', y', hy', h'⟩ := (hW₀ _).mp hinv
  have hg0 : (((σ j - j ^ p : ↥K)) : LaurentSeries L) ≠ 0 := by
    intro e; apply h0; exact_mod_cast e
  have P' : Pres L ((((σ j - j ^ p : ↥K)) : LaurentSeries L))⁻¹ x' y' := by
    refine ⟨hy', ?_⟩
    have e := h'
    push_cast at e ⊢
    exact e
  exact Pg.map_ne_zero_of_inv hg0 P' hX

#print axioms solution

end S_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand
end P2MW
export P2MW.S_ModularCurve_map_j_sub_pow_mem_nonunits_gauss_of_coe_map_eq_qExpand (solution)
