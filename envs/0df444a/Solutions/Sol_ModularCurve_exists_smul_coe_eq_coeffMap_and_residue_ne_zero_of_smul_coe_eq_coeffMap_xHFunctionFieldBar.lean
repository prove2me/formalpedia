-- Prove2me | solution 1 for ModularCurve.exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d2fcdaf7-8804-5f67-8e67-5ed1af9ae59a

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionField xHFunctionFieldBar coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange mem_laurentBaseChange_iff coeffMap_mem_laurentBaseChange"
p2m_open "ModularCurve"

namespace PrimitiveRescale

open HahnSeries IntermediateField

section Lift

variable {R S : Type*} [CommRing R] [CommRing S]

def liftSeries (f : R →+* S) (hf : Function.Injective f) (x : LaurentSeries S) (g : ℤ → R)
    (hg : ∀ k, f (g k) = x.coeff k) : LaurentSeries R where
  coeff := g
  isPWO_support' := x.isPWO_support.mono (by
    intro k hk
    rw [Function.mem_support] at hk
    rw [HahnSeries.mem_support]
    intro h0
    apply hk
    apply hf
    rw [hg, h0, map_zero])

@[scoped simp]
theorem liftSeries_coeff (f : R →+* S) (hf : Function.Injective f) (x : LaurentSeries S) (g : ℤ → R)
    (hg : ∀ k, f (g k) = x.coeff k) (k : ℤ) : (liftSeries f hf x g hg).coeff k = g k :=
  rfl

theorem coeffMap_liftSeries (f : R →+* S) (hf : Function.Injective f) (x : LaurentSeries S)
    (g : ℤ → R) (hg : ∀ k, f (g k) = x.coeff k) : coeffMap f (liftSeries f hf x g hg) = x := by
  ext k
  rw [coeffMap_coeff, liftSeries_coeff, hg]

end Lift

section ConstantAction

variable (L : Type*) [Field L]

theorem coe_smul_eq_single_mul (F : IntermediateField L (LaurentSeries L)) (c : L) (x : F) :
    ((c • x : F) : LaurentSeries L) = HahnSeries.single 0 c * (x : LaurentSeries L) := by
  rw [@Algebra.smul_def L F _ _ (SubalgebraClass.toAlgebra F), MulMemClass.coe_mul,
    SubalgebraClass.coe_algebraMap, algebraMap_laurentSeries_eq_single]

theorem coe_smul_coeff (F : IntermediateField L (LaurentSeries L)) (c : L) (x : F) (k : ℤ) :
    ((c • x : F) : LaurentSeries L).coeff k = c * (x : LaurentSeries L).coeff k := by
  rw [coe_smul_eq_single_mul, HahnSeries.coeff_single_zero_mul]

theorem eq_zero_of_smul_eq_zero (F : IntermediateField L (LaurentSeries L)) {c : L} (hc : c ≠ 0)
    {x : F} (h : c • x = 0) : x = 0 := by
  rw [@Algebra.smul_def L F _ _ (SubalgebraClass.toAlgebra F)] at h
  exact (mul_eq_zero.mp h).resolve_left (by simpa using hc)

end ConstantAction

section Descent

variable (L : Type*) [Field L] [Algebra ℚ L]

def CoeffsInNumberField (x : LaurentSeries L) : Prop :=
  ∃ K₀ : IntermediateField ℚ L, FiniteDimensional ℚ K₀ ∧ ∀ k, x.coeff k ∈ K₀

variable {L}

theorem CoeffsInNumberField.add {x y : LaurentSeries L} (hx : CoeffsInNumberField L x)
    (hy : CoeffsInNumberField L y) : CoeffsInNumberField L (x + y) := by
  obtain ⟨K₁, h₁, hx⟩ := hx
  obtain ⟨K₂, h₂, hy⟩ := hy
  haveI := h₁
  haveI := h₂
  refine ⟨K₁ ⊔ K₂, inferInstance, fun k => ?_⟩
  rw [HahnSeries.coeff_add]
  exact add_mem ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) (hx k)) ((le_sup_right : K₂ ≤ K₁ ⊔ K₂) (hy k))

theorem CoeffsInNumberField.neg {x : LaurentSeries L} (hx : CoeffsInNumberField L x) :
    CoeffsInNumberField L (-x) := by
  obtain ⟨K₁, h₁, hx⟩ := hx
  refine ⟨K₁, h₁, fun k => ?_⟩
  rw [HahnSeries.coeff_neg]
  exact neg_mem (hx k)

theorem CoeffsInNumberField.mul {x y : LaurentSeries L} (hx : CoeffsInNumberField L x)
    (hy : CoeffsInNumberField L y) : CoeffsInNumberField L (x * y) := by
  obtain ⟨K₁, h₁, hx⟩ := hx
  obtain ⟨K₂, h₂, hy⟩ := hy
  haveI := h₁
  haveI := h₂
  refine ⟨K₁ ⊔ K₂, inferInstance, fun k => ?_⟩
  rw [HahnSeries.coeff_mul]
  refine sum_mem fun ij _ => mul_mem ?_ ?_
  · exact (le_sup_left : K₁ ≤ K₁ ⊔ K₂) (hx _)
  · exact (le_sup_right : K₂ ≤ K₁ ⊔ K₂) (hy _)

theorem exists_coeffMap_eq_of_forall_coeff_mem (K₀ : IntermediateField ℚ L) {x : LaurentSeries L}
    (hx : ∀ k, x.coeff k ∈ K₀) :
    ∃ x' : LaurentSeries K₀, coeffMap (algebraMap K₀ L) x' = x :=
  ⟨liftSeries (algebraMap K₀ L) (FaithfulSMul.algebraMap_injective K₀ L) x (fun k => ⟨x.coeff k, hx k⟩)
      (fun _ => rfl),
    coeffMap_liftSeries _ _ _ _ _⟩

theorem CoeffsInNumberField.inv {x : LaurentSeries L} (hx : CoeffsInNumberField L x) :
    CoeffsInNumberField L x⁻¹ := by
  obtain ⟨K₁, h₁, hx⟩ := hx
  refine ⟨K₁, h₁, fun k => ?_⟩
  obtain ⟨x', rfl⟩ := exists_coeffMap_eq_of_forall_coeff_mem K₁ hx
  rw [← map_inv₀, coeffMap_coeff]
  exact (x'⁻¹.coeff k).2

theorem CoeffsInNumberField.algebraMap [Algebra.IsAlgebraic ℚ L] (c : L) :
    CoeffsInNumberField L (algebraMap L (LaurentSeries L) c) := by
  refine ⟨ℚ⟮c⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c), fun k => ?_⟩
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
  split_ifs
  · exact mem_adjoin_simple_self ℚ c
  · exact zero_mem _

theorem CoeffsInNumberField.coeffEmb (z : LaurentSeries ℚ) : CoeffsInNumberField L (coeffEmb L z) := by
  refine ⟨⊥, inferInstance, fun k => ?_⟩
  rw [coeffEmb_coeff]
  exact IntermediateField.algebraMap_mem _ _

theorem coeffsInNumberField_of_mem_laurentBaseChange [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) : CoeffsInNumberField L x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, _, rfl⟩
      · exact CoeffsInNumberField.algebraMap a
      · exact CoeffsInNumberField.coeffEmb z
  | one =>
      have h := CoeffsInNumberField.coeffEmb (L := L) 1
      rwa [map_one] at h
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end Descent

section Main

open IsDiscreteValuationRing

theorem main (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (g : ↥(ModularCurve.xHFunctionFieldBar M H)) (hg : g ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : c₀ ≠ 0) (y₀ : LaurentSeries ↥Pl)
    (h₀ : ((c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap Pl.subtype y₀) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ y : LaurentSeries ↥Pl,
      ((c • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

  obtain ⟨K₀, hfd, hK₀⟩ :=
    coeffsInNumberField_of_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (xHFunctionField M H)
      (c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)).2
  have hcoe : ∀ k, ((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ) =
      ((c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff k := by
    intro k
    rw [h₀, coeffMap_coeff]
    rfl
  haveI : FiniteDimensional ℚ K₀ := hfd

  set A : ValuationSubring K₀ := Pl.comap (algebraMap K₀ (AlgebraicClosure ℚ)) with hA_def
  haveI : IsDiscreteValuationRing A :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime K₀ Pl (Fact.out) hPl

  have hmemK : ∀ k, ((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ) ∈ K₀ := fun k => (hcoe k) ▸ hK₀ k
  have hmemA : ∀ k, (⟨((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ), hmemK k⟩ : K₀) ∈ A := by
    intro k
    rw [hA_def, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply]
    exact (y₀.coeff k).2
  let a : ℤ → A := fun k => ⟨⟨((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ), hmemK k⟩, hmemA k⟩
  have ha : ∀ k, (((a k : A) : K₀) : AlgebraicClosure ℚ) = ((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ) :=
    fun _ => rfl
  have ha_zero_iff : ∀ k, a k = 0 ↔ y₀.coeff k = 0 := by
    intro k
    constructor
    · intro h
      have h' : (((a k : A) : K₀) : AlgebraicClosure ℚ) = 0 := by
        rw [h]
        rfl
      rw [ha] at h'
      exact_mod_cast h'
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      rw [ha, h]
      rfl

  have hy₀ : y₀ ≠ 0 := by
    intro hy
    apply hg
    have h1 : (c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) = 0 := by
      rw [← ZeroMemClass.coe_eq_zero, h₀, hy, map_zero]
    exact eq_zero_of_smul_eq_zero (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) hc₀ h1
  obtain ⟨k₁, hk₁⟩ : ∃ k, y₀.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hy₀ (HahnSeries.ext (funext h))
  have ha₁ : a k₁ ≠ 0 := fun h => hk₁ ((ha_zero_iff k₁).mp h)

  let k₀ : ℤ := Function.argmin (fun k => addVal A (a k))
  have hmin : ∀ k, addVal A (a k₀) ≤ addVal A (a k) := fun k =>
    Function.argmin_le (fun k => addVal A (a k)) k
  have ha₀ : a k₀ ≠ 0 := by
    intro h
    have h' := hmin k₁
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at h'
    exact ha₁ h'
  have hdvd : ∀ k, a k₀ ∣ a k := fun k => addVal_le_iff_dvd.mp (hmin k)
  choose d hd using hdvd
  have hd₀ : d k₀ = 1 := by
    have h := hd k₀
    conv_lhs at h => rw [← mul_one (a k₀)]
    exact (mul_left_cancel₀ ha₀ h).symm

  set α : AlgebraicClosure ℚ := ((y₀.coeff k₀ : ↥Pl) : AlgebraicClosure ℚ) with hα_def
  have hα : α ≠ 0 := by
    intro h
    apply ha₀
    rw [ha_zero_iff]
    exact Subtype.ext h

  have hrel : ∀ k, ((y₀.coeff k : ↥Pl) : AlgebraicClosure ℚ) =
      α * (((d k : A) : K₀) : AlgebraicClosure ℚ) := by
    intro k
    have h := congrArg (fun z : A => (((z : A) : K₀) : AlgebraicClosure ℚ)) (hd k)
    simp only [ha] at h
    exact h
  have hdmem : ∀ k, (((d k : A) : K₀) : AlgebraicClosure ℚ) ∈ Pl := fun k =>
    ValuationSubring.mem_comap.mp (d k).2

  have hcoeff : ∀ (c : AlgebraicClosure ℚ) (k : ℤ),
      ((c • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)).coeff k =
        c * (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k := fun c k =>
    coe_smul_coeff (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) c g k
  let y : LaurentSeries ↥Pl :=
    liftSeries Pl.subtype Subtype.val_injective
      (((α⁻¹ * c₀) • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
      (fun k => ⟨(((d k : A) : K₀) : AlgebraicClosure ℚ), hdmem k⟩) (by
        intro k
        rw [hcoeff, mul_assoc, ← hcoeff c₀ k, ← hcoe k, hrel k, ← mul_assoc, inv_mul_cancel₀ hα,
          one_mul]
        rfl)
  refine ⟨α⁻¹ * c₀, mul_ne_zero (inv_ne_zero hα) hc₀, y, (coeffMap_liftSeries _ _ _ _ _).symm, ?_⟩
  ·
    intro h
    have h1 : (ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y).coeff k₀ = 1 := by
      rw [coeffMap_coeff, liftSeries_coeff]
      have : (⟨(((d k₀ : A) : K₀) : AlgebraicClosure ℚ), hdmem k₀⟩ : ↥Pl) = 1 := by
        apply Subtype.ext
        change (((d k₀ : A) : K₀) : AlgebraicClosure ℚ) = 1
        rw [hd₀]
        rfl
      rw [this, map_one]
    rw [h] at h1
    exact zero_ne_one (h1 ▸ (HahnSeries.coeff_zero (a := k₀)).symm)

end Main

end PrimitiveRescale
p2m_reactivate "P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.ModularCurve.PrimitiveRescale"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.ModularCurve.PrimitiveRescale P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.ModularCurve.PrimitiveRescale P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar.ModularCurve"

open scoped MatrixGroups

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (g : ↥(ModularCurve.xHFunctionFieldBar M H)) (hg : g ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (hc₀ : c₀ ≠ 0) (y₀ : LaurentSeries ↥Pl)
    (h₀ : ((c₀ • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y₀) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ ∃ y : LaurentSeries ↥Pl,
      ((c • g : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
      ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 :=
  ModularCurve.PrimitiveRescale.main p M H Pl hPl g hg c₀ hc₀ y₀ h₀

end S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_smul_coe_eq_coeffMap_and_residue_ne_zero_of_smul_coe_eq_coeffMap_xHFunctionFieldBar (solution)
