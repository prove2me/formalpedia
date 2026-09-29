-- Prove2me | solution 1 for ModularCurve.PhiGen.mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3202ff89-7fd6-53cd-b9d9-d64f047d901a

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul
import Theorems.Thm_ModularCurve_multiset_map_cosetReps_smul
import Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
set_option autoImplicit false
noncomputable section
open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffMap coeffMap_coeff coeffMap_single coeffEmb coeffEmb_coeff qTwist qTwist_coeff PhiGen.phiProd hasSum_modularUnitSeries_qParam hasSum_modularUnitSeries_inv_qParam hasSum_qParam_mul_laurent hasSum_qParam_heckeMatrix_smul multiset_map_cosetReps_smul discriminant_div_discriminant_heckeDiagMatrix_smul mem_adjoin_jq_of_hasSum_of_slash_invariant"
p2m_open "ModularCurve"

namespace UnitReal

def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

lemma add (hA : RealL h A F) (hB : RealL h B G) : RealL h (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

lemma neg (hA : RealL h A F) : RealL h (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

lemma sub (hA : RealL h A F) (hB : RealL h B G) : RealL h (A - B) (F - G) := fun τ => by
  simpa [sub_mul] using (hA τ).sub (hB τ)

lemma mul (hh : 0 < h) (hA : RealL h A F) (hB : RealL h B G) : RealL h (A * B) (F * G) := fun τ =>
  hasSum_qParam_mul_laurent h hh A B F G hA hB τ

lemma single (h : ℝ) (a : ℂ) (n : ℤ) :
    RealL h (HahnSeries.single n a) (fun τ => a * 𝕢 h (τ : ℂ) ^ n) := fun τ => by
  refine (hasSum_ite_eq n (a * 𝕢 h (τ : ℂ) ^ n)).congr_fun fun m => ?_
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, hm]

lemma C (h : ℝ) (a : ℂ) : RealL h (HahnSeries.C a) (fun _ => a) := by
  simpa using single h a 0

lemma one (h : ℝ) : RealL h 1 1 := by
  first | simpa using C h 1 | (have h' := C h 1; simp at h'; exact h') | exact C h 1

lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A') (h2 : ∀ τ, F τ = F' τ) :
    RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma prod (hh : 0 < h) {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => first | simpa using one h | exact one h
  | insert a s ha ih =>
    have h1 := (hAF a (Finset.mem_insert_self a s)).mul hh (ih fun i hi => hAF i (Finset.mem_insert_of_mem hi))
    refine h1.congr (Finset.prod_insert ha).symm fun τ => ?_
    simp [Finset.prod_insert ha]

lemma coeff_prod_X_sub_C (hh : 0 < h) {ι : Type} (s : Finset ι) {a : ι → LaurentSeries ℂ}
    {α : ι → ℍ → ℂ} (haα : ∀ i ∈ s, RealL h (a i) (α i)) (k : ℕ) :
    RealL h ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (fun τ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    by_cases hk : k = 0
    · subst hk; first | simpa using one h | exact one h
    · simp only [hk, if_false]
      exact zero h
  | insert b s hb ih =>
    have ih' := fun k => ih (fun i hi => haα i (Finset.mem_insert_of_mem hi)) k
    have hb' := haα b (Finset.mem_insert_self b s)
    have hA : (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (a i))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) * (Polynomial.X - Polynomial.C (a b)) :=
      (Finset.prod_insert hb).trans (mul_comm (G := Polynomial (LaurentSeries ℂ)) _ _)
    have hfun : ∀ τ : ℍ, (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (α i τ))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))) * (Polynomial.X - Polynomial.C (α b τ)) :=
      fun τ => (Finset.prod_insert hb).trans (mul_comm (G := Polynomial ℂ) _ _)
    cases k with
    | zero =>
      refine ((ih' 0).mul hh hb').neg.congr ?_ fun τ => ?_
      · rw [hA, Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub]
        exact (mul_neg (α := LaurentSeries ℂ) _ _).symm
      · simp only [hfun τ, Polynomial.mul_coeff_zero, Pi.neg_apply, Pi.mul_apply, Polynomial.coeff_sub,
          Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    | succ k =>
      refine ((ih' k).sub ((ih' (k + 1)).mul hh hb')).congr ?_ fun τ => ?_
      · rw [hA, Polynomial.coeff_mul_X_sub_C]
      · simp only [hfun τ, Polynomial.coeff_mul_X_sub_C, Pi.sub_apply, Pi.mul_apply]

end RealL

section Sigma

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

def expRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

lemma isPrimitiveRoot_expRoot : IsPrimitiveRoot (expRoot ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ hℓ.out.ne_zero

def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

variable (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

lemma sigma_zeta : sigma ℓ ζ hζ (ζ : CyclotomicField ℓ ℚ) = expRoot ℓ := by
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)
  let r : primitiveRoots ℓ ℂ := ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe hζ ℂ
    (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos) (e.symm r)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit hℓ in
lemma sigma_ratCast' (σ : CyclotomicField ℓ ℚ →+* ℂ) (q : ℚ) : σ (q : CyclotomicField ℓ ℚ) = (q : ℂ) :=
  map_ratCast σ q

end Sigma

theorem coeffMap_qExpand_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (ModularCurve.qExpand R N x) = ModularCurve.qExpand S N (coeffMap f x) := by
  ext m
  by_cases h : (N : ℤ) ∣ m
  · obtain ⟨l, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

section Unit

abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

def UC : LaurentSeries ℂ := coeffMap castC (modularUnitSeries p)

def VC : LaurentSeries ℂ := coeffMap castC (HahnSeries.C ((p : ℚ) ^ 12) * (modularUnitSeries p)⁻¹)

lemma realL_UC : RealL 1 (UC p) (fun τ => ModularForm.discriminant τ /
    ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ)) := fun τ =>
  ModularCurve.hasSum_modularUnitSeries_qParam p τ

lemma realL_VC : RealL 1 (VC p) (fun τ => (p : ℂ) ^ 12 *
    (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ) / ModularForm.discriminant τ)) := by
  have h : RealL 1 (coeffMap castC (modularUnitSeries p)⁻¹) (fun τ =>
      ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ) / ModularForm.discriminant τ) := fun τ =>
    ModularCurve.hasSum_modularUnitSeries_inv_qParam p τ
  refine ((RealL.C 1 ((p : ℂ) ^ 12)).mul one_pos h).congr ?_ fun τ => rfl
  rw [VC, map_mul, HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single, map_pow castC, map_natCast castC]

lemma realL_qExpand_of_realL_one (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL 1 x F) :
    RealL p (qExpand ℂ p x) F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (p : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hp.out.ne_zero)
  rw [← hinj.hasSum_iff]
  · refine (hx τ).congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd p _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL p (qExpand ℂ p x) F) :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (p : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hp.out.ne_zero)
  have h := hx τ
  rw [← hinj.hasSum_iff] at h
  · refine h.congr_fun fun n => ?_
    simp only [Function.comp_apply, qExpand_coeff_mul]
    congr 1
    rw [zpow_mul, zpow_natCast]
    congr 1
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
    rw [← Complex.exp_nat_mul]
    congr 1
    field_simp [(Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd p _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

end Unit

section Translates

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : (CyclotomicField p ℚ)ˣ)
  (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
  (conj : Fin (p + 1) → LaurentSeries (CyclotomicField p ℚ))

def conjC (i : Fin (p + 1)) : LaurentSeries ℂ := coeffMap (sigma p ζ hζ) (conj i)

def anConj (i : Fin (p + 1)) (τ : ℍ) : ℂ :=
  Fin.cases (ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))
    (fun b : Fin p => (p : ℂ) ^ 12 *
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
        ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ))) i

omit hp in
@[scoped simp] lemma anConj_zero (τ : ℍ) : anConj p 0 τ =
    ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ) := by
  simp [anConj]

omit hp in
@[scoped simp] lemma anConj_succ (b : Fin p) (τ : ℍ) : anConj p b.succ τ = (p : ℂ) ^ 12 *
    (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
      ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ)) := by
  simp [anConj]

lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap (sigma p ζ hζ) (coeffEmb (CyclotomicField p ℚ) x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

lemma realL_conjC_zero
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p))) :
    RealL p (conjC p ζ hζ conj 0) (anConj p 0) := by
  have h : conjC p ζ hζ conj 0 = qExpand ℂ p (UC p) := by
    rw [conjC, hconj0, coeffMap_qExpand_apply, coeffMap_sigma_coeffEmb]
    rfl
  rw [h]
  refine (realL_qExpand_of_realL_one p (UC p) _ (realL_UC p)).congr rfl fun τ => ?_
  rw [anConj_zero]

omit hp in
lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot p ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / p) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

lemma coeffMap_sigma_base :
    coeffMap (sigma p ζ hζ) (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p))⁻¹) =
      VC p := by
  rw [VC, map_mul, map_mul, map_inv₀, map_inv₀, coeffMap_sigma_coeffEmb, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffMap_single, coeffMap_single, map_pow (sigma p ζ hζ), map_natCast (sigma p ζ hζ), map_pow castC,
    map_natCast castC]

lemma realL_conjC_succ
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p))⁻¹))
    (b : Fin p) : RealL p (conjC p ζ hζ conj b.succ) (anConj p b.succ) := by
  intro τ
  have h := ModularCurve.hasSum_qParam_heckeMatrix_smul p (b : ℕ) (VC p) _ (realL_VC p) τ
  rw [anConj_succ]
  refine h.congr_fun fun m => ?_
  congr 1
  rw [conjC, hconjS b, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, Units.val_pow_eq_pow_val, map_pow, sigma_zeta, expRoot_pow_zpow, ← coeffMap_coeff,
    coeffMap_sigma_base]

lemma realL_conjC
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p))⁻¹))
    (i : Fin (p + 1)) : RealL p (conjC p ζ hζ conj i) (anConj p i) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · exact realL_conjC_zero p ζ hζ conj hconj0
  · exact realL_conjC_succ p ζ hζ conj hconjS b

lemma map_phiProd : (PhiGen.phiProd p conj).map (coeffMap (sigma p ζ hζ)) =
    ∏ i : Fin (p + 1), (Polynomial.X - Polynomial.C (conjC p ζ hζ conj i)) := by
  rw [PhiGen.phiProd, ← Polynomial.coe_mapRingHom, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conjC]

lemma realL_phiProd_coeff
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (coeffEmb (CyclotomicField p ℚ) (modularUnitSeries p))⁻¹))
    (k : ℕ) :
    RealL p (((PhiGen.phiProd p conj).map (coeffMap (sigma p ζ hζ))).coeff k)
      (fun τ => (∏ i : Fin (p + 1), (Polynomial.X - Polynomial.C (anConj p i τ))).coeff k) := by
  rw [map_phiProd]
  exact RealL.coeff_prod_X_sub_C (by exact_mod_cast hp.out.pos) Finset.univ
    (fun i _ => realL_conjC p ζ hζ conj hconj0 hconjS i) k

end Translates

end UnitReal
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffMap coeffMap_coeff coeffMap_single coeffEmb coeffEmb_coeff qTwist qTwist_coeff PhiGen.phiProd hasSum_modularUnitSeries_qParam hasSum_modularUnitSeries_inv_qParam hasSum_qParam_mul_laurent hasSum_qParam_heckeMatrix_smul multiset_map_cosetReps_smul discriminant_div_discriminant_heckeDiagMatrix_smul mem_adjoin_jq_of_hasSum_of_slash_invariant" namespace PhiGen p2m_export "ModularCurve.PhiGen" "conj phiProd" end ModularCurve.PhiGen
p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve ModularCurve.UnitReal in

theorem ModularCurve.PhiGen.hasSum_coeff_of_qExpand_descent_phiProd_modularUnit
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (conj : Fin (p + 1) → LaurentSeries (CyclotomicField p ℚ))
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p
      (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p))⁻¹))
    (c : ℕ → LaurentSeries ℚ)
    (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k =
      ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.qExpand ℚ p (c k)))
    (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.discriminant τ /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))) *
        ∏ b : Fin p, (Polynomial.X - Polynomial.C ((p : ℂ) ^ 12 *
          (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
            ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ))))).coeff k) := by
  have h1 := realL_phiProd_coeff p ζ hζ conj hconj0 hconjS k
  rw [Polynomial.coeff_map, hc k, coeffMap_sigma_coeffEmb, coeffMap_qExpand_apply] at h1
  have h2 := realL_one_of_realL_qExpand p _ _ h1 τ
  have hprod : (∏ i : Fin (p + 1), (Polynomial.X - Polynomial.C (anConj p i τ))) =
      (Polynomial.X - Polynomial.C (ModularForm.discriminant τ /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))) *
        ∏ b : Fin p, (Polynomial.X - Polynomial.C ((p : ℂ) ^ 12 *
          (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
            ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ)))) := by
    rw [Fin.prod_univ_succ]; simp only [anConj_zero, anConj_succ]
  rw [hprod] at h2
  exact h2

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial ModularForm
open scoped MatrixGroups ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "modularUnitSeries qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffMap coeffMap_coeff coeffMap_single coeffEmb coeffEmb_coeff qTwist qTwist_coeff PhiGen.phiProd hasSum_modularUnitSeries_qParam hasSum_modularUnitSeries_inv_qParam hasSum_qParam_mul_laurent hasSum_qParam_heckeMatrix_smul multiset_map_cosetReps_smul discriminant_div_discriminant_heckeDiagMatrix_smul mem_adjoin_jq_of_hasSum_of_slash_invariant"
p2m_open "ModularCurve"

namespace UnitCoset

def uA (p : ℕ) (τ : ℍ) : ℂ :=
  ModularForm.discriminant τ / ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ)

def rep (p : ℕ) (i : Fin (p + 1)) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (fun b : Fin p => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i

@[scoped simp] theorem rep_zero {p : ℕ} : rep p 0 = 1 := rfl
@[scoped simp] theorem rep_succ {p : ℕ} (b : Fin p) :
    rep p b.succ = ModularGroup.S * ModularGroup.T ^ (b : ℕ) := by
  simp [rep]

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem discriminant_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ)
      = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  first | simpa [CuspForm.coe_discriminant] using this | (have h' := this; simp [CuspForm.coe_discriminant] at h'; exact h') | exact this

theorem denom_mapGL (g : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ g) τ = ((g 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((g 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem coe_ne_zero' (z : ℍ) : (z : ℂ) ≠ 0 := by
  intro h
  have him := z.im_pos
  rw [UpperHalfPlane.im, h] at him
  simp at him

theorem denom_S (τ : ℍ) : denom (mapGL ℝ ModularGroup.S) τ = (τ : ℂ) := by
  rw [denom_mapGL]
  have h10 : ModularGroup.S 1 0 = 1 := by
    have := congrFun (congrFun ModularGroup.coe_S 1) 0; simpa using this
  have h11 : ModularGroup.S 1 1 = 0 := by
    have := congrFun (congrFun ModularGroup.coe_S 1) 1; simpa using this
  rw [h10, h11]
  push_cast
  ring

theorem T_pow_eq_zpow (j : ℕ) :
    (ModularGroup.T ^ j : SL(2, ℤ)) = ModularGroup.T ^ (j : ℤ) := (zpow_natCast _ _).symm

theorem denom_T_pow (j : ℕ) (τ : ℍ) : denom (mapGL ℝ (ModularGroup.T ^ j)) τ = 1 := by
  rw [T_pow_eq_zpow, denom_mapGL]
  have h10 : (ModularGroup.T ^ (j : ℤ)) 1 0 = 0 := by
    have := congrFun (congrFun (ModularGroup.coe_T_zpow (j : ℤ)) 1) 0; simpa using this
  have h11 : (ModularGroup.T ^ (j : ℤ)) 1 1 = 1 := by
    have := congrFun (congrFun (ModularGroup.coe_T_zpow (j : ℤ)) 1) 1; simpa using this
  rw [h10, h11]
  push_cast
  ring

theorem coe_T_pow_smul (j : ℕ) (τ : ℍ) :
    ((ModularGroup.T ^ j • τ : ℍ) : ℂ) = (τ : ℂ) + j := by
  rw [T_pow_eq_zpow, modular_T_zpow_smul, coe_vadd]
  push_cast
  ring

theorem discriminant_T_pow_smul (j : ℕ) (τ : ℍ) :
    ModularForm.discriminant (ModularGroup.T ^ j • τ) = ModularForm.discriminant τ := by
  rw [discriminant_sl_smul, denom_T_pow, one_zpow, one_mul]

theorem heckeDiag_heckeMatrix_smul {p : ℕ} (hp' : p ≠ 0) (j : ℕ) (τ : ℍ) :
    ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p j • τ
      = ModularGroup.T ^ j • τ := by
  have hpne : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp'
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul hp', ModularForm.coe_heckeMatrix_smul hp',
    coe_T_pow_smul]
  field_simp

theorem heckeDiag_st_smul {p : ℕ} (hp' : p ≠ 0) (j : ℕ) (τ : ℍ) :
    ModularForm.heckeDiagMatrix p • (ModularGroup.S * ModularGroup.T ^ j) • τ
      = ModularGroup.S • ModularForm.heckeMatrix p j • τ := by
  have hpne : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp'
  have htj : ((τ : ℂ) + j) ≠ 0 := by
    have h := coe_T_pow_smul j τ
    rw [← h]
    exact coe_ne_zero' _
  have hMne : ((ModularForm.heckeMatrix p j • τ : ℍ) : ℂ) ≠ 0 := coe_ne_zero' _
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul hp', mul_smul]
  simp only [modular_S_smul, UpperHalfPlane.coe_mk]
  simp only [coe_T_pow_smul, ModularForm.coe_heckeMatrix_smul hp']
  field_simp

theorem uA_st_smul {p : ℕ} (hp' : p ≠ 0) (j : ℕ) (τ : ℍ) :
    uA p ((ModularGroup.S * ModularGroup.T ^ j) • τ)
      = (p : ℂ) ^ (12 : ℕ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p j • τ) /
          ModularForm.discriminant (ModularForm.heckeMatrix p j • τ)) := by
  have hpne : ((p : ℂ)) ≠ 0 := by exact_mod_cast hp'
  have htj : ((τ : ℂ) + j) ≠ 0 := by
    have h := coe_T_pow_smul j τ
    rw [← h]
    exact coe_ne_zero' _

  have hnum : ModularForm.discriminant ((ModularGroup.S * ModularGroup.T ^ j) • τ) =
      ((τ : ℂ) + j) ^ (12 : ℤ) * ModularForm.discriminant τ := by
    rw [mul_smul, discriminant_sl_smul ModularGroup.S, denom_S, coe_T_pow_smul,
      discriminant_T_pow_smul]

  have hden : ModularForm.discriminant
      (ModularForm.heckeDiagMatrix p • (ModularGroup.S * ModularGroup.T ^ j) • τ) =
      (((τ : ℂ) + j) / p) ^ (12 : ℤ) *
        ModularForm.discriminant (ModularForm.heckeMatrix p j • τ) := by
    rw [heckeDiag_st_smul hp', discriminant_sl_smul ModularGroup.S, denom_S,
      ModularForm.coe_heckeMatrix_smul hp']

  have htarget : ModularForm.discriminant
      (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p j • τ)
      = ModularForm.discriminant τ := by
    rw [heckeDiag_heckeMatrix_smul hp', discriminant_T_pow_smul]
  have hMne : ModularForm.discriminant (ModularForm.heckeMatrix p j • τ) ≠ 0 :=
    ModularForm.discriminant_ne_zero _
  have h12 : ((p : ℂ)) ^ (12 : ℕ) = ((p : ℂ)) ^ (12 : ℤ) := by
    rw [← zpow_natCast]
    try norm_num
  rw [uA, hnum, hden, htarget, h12]
  rw [div_zpow]
  field_simp

variable {p : ℕ} [hp : Fact p.Prime]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

include hp in

theorem unitCosetPoly_smul' (γ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (ModularForm.discriminant (γ • τ) /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix p • γ • τ))) *
      ∏ b : Fin p, (X - C ((p : ℂ) ^ (12 : ℕ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • γ • τ) /
          ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • γ • τ))))
    = (X - C (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))) *
      ∏ b : Fin p, (X - C ((p : ℂ) ^ (12 : ℕ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
          ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ)))) := by
  have hp' : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have hF : ∀ δ ∈ CongruenceSubgroup.Gamma0 p, ∀ σ : ℍ, uA p (δ • σ) = uA p σ := by
    intro δ hδ σ
    simpa only [uA] using
      ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul p δ hδ σ

  have hmul := ModularCurve.multiset_map_cosetReps_smul p ℂ (uA p) hF γ τ

  have hside : ∀ σ : ℍ,
      (X - C (ModularForm.discriminant σ /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix p • σ))) *
        ∏ b : Fin p, (X - C ((p : ℂ) ^ (12 : ℕ) *
          (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • σ) /
            ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • σ))))
      = ∏ i : Fin (p + 1), (X - C (uA p (rep p i • σ))) := by
    intro σ
    rw [Fin.prod_univ_succ]
    refine congrArg₂ (· * ·) ?_ ?_
    · rw [rep_zero, one_smul]
      simp only [uA]
    · refine Finset.prod_congr rfl fun b _ => ?_
      rw [rep_succ, uA_st_smul hp' (b : ℕ) σ]
  rw [hside (γ • τ), hside τ]

  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have hmap : ∀ σ : ℍ,
      (Finset.univ.val.map fun i : Fin (p + 1) => X - C (uA p (rep p i • σ)))
        = ((Finset.univ.val.map fun i : Fin (p + 1) => uA p (rep p i • σ)).map
            fun z : ℂ => X - C z) := by
    intro σ
    rw [Multiset.map_map]
    rfl
  rw [hmap (γ • τ), hmap τ]
  refine congrArg Multiset.prod (congrArg (Multiset.map fun z : ℂ => X - C z) ?_)
  have hrep : ∀ σ : ℍ, (fun i : Fin (p + 1) => uA p (rep p i • σ))
      = fun i : Fin (p + 1) => uA p
        ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
          (fun b : Fin p => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i :
            Matrix.SpecialLinearGroup (Fin 2) ℤ) • σ) := by
    intro σ
    rfl
  rw [hrep (γ • τ), hrep τ]
  exact hmul

end UnitCoset
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitCoset"

theorem unitCosetPoly_smul (p : ℕ) [hp : Fact (Nat.Prime p)]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (Polynomial.X - Polynomial.C (ModularForm.discriminant (γ • τ) /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix p • γ • τ))) *
      ∏ b : Fin p, (Polynomial.X - Polynomial.C ((p : ℂ) ^ (12 : ℕ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • γ • τ) /
          ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • γ • τ))))
    = (Polynomial.X - Polynomial.C (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))) *
      ∏ b : Fin p, (Polynomial.X - Polynomial.C ((p : ℂ) ^ (12 : ℕ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
          ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ)))) :=
  UnitCoset.unitCosetPoly_smul' γ τ

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitCoset"

end
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitCoset"

noncomputable section

open UpperHalfPlane Polynomial

p2m_open_scoped "ModularCurve ModularCurve.PhiGen" in

private theorem ModularCurve.PhiGen.solution_impl
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
    (conj : Fin (p + 1) → LaurentSeries (CyclotomicField p ℚ))
    (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p
      (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p)))
    (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ))
      (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p))⁻¹))
    (c : ℕ → LaurentSeries ℚ)
    (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k =
      ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.qExpand ℚ p (c k)))
    (k : ℕ) : c k ∈ Algebra.adjoin ℚ {ModularCurve.jq} := by
  classical
  refine ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant (c k)
    (fun τ : UpperHalfPlane => ((Polynomial.X - Polynomial.C (ModularForm.discriminant τ /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix p • τ))) *
        ∏ b : Fin p, (Polynomial.X - Polynomial.C ((p : ℂ) ^ 12 *
          (ModularForm.discriminant (ModularForm.heckeDiagMatrix p • ModularForm.heckeMatrix p (b : ℕ) • τ) /
            ModularForm.discriminant (ModularForm.heckeMatrix p (b : ℕ) • τ))))).coeff k) ?_ ?_
  · exact fun τ =>
      ModularCurve.PhiGen.hasSum_coeff_of_qExpand_descent_phiProd_modularUnit
        p ζ hζ conj hconj0 hconjS c hc k τ
  · exact fun γ τ => congrArg (fun P : Polynomial ℂ => P.coeff k)
      (ModularCurve.unitCosetPoly_smul p γ τ)

end
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitReal P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit.ModularCurve.UnitCoset"

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : (CyclotomicField p ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p) (conj : Fin (p + 1) → LaurentSeries (CyclotomicField p ℚ)) (hconj0 : conj 0 = ModularCurve.qExpand (CyclotomicField p ℚ) p (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p))) (hconjS : ∀ b : Fin p, conj b.succ = ModularCurve.qTwist (ζ ^ (b : ℕ)) (HahnSeries.C ((p : CyclotomicField p ℚ) ^ 12) * (ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.modularUnitSeries p))⁻¹)) (c : ℕ → LaurentSeries ℚ) (hc : ∀ k : ℕ, (ModularCurve.PhiGen.phiProd p conj).coeff k = ModularCurve.coeffEmb (CyclotomicField p ℚ) (ModularCurve.qExpand ℚ p (c k))) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {ModularCurve.jq} :=
  ModularCurve.PhiGen.solution_impl p ζ hζ conj hconj0 hconjS c hc k

end S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit
end P2MW
export P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_qExpand_descent_phiProd_modularUnit (solution)
