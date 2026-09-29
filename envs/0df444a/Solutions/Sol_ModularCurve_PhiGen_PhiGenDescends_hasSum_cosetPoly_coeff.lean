-- Prove2me | solution 1 for ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6906357b-f645-5e50-a6ef-62a6b647d1a1

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_hasSum_qParam_heckeMatrix_smul
import Theorems.Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq qTwist_coeff PhiGen.conj PhiGen.conj_zero PhiGen.conj_succ PhiGen.phiProd PhiGen.PhiGenDescends coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff coeffMap_qExpand hasSum_jq_qParam hasSum_qParam_mul_laurent hasSum_qParam_heckeMatrix_smul hasSum_qParam_heckeDiagMatrix_smul"
p2m_open "ModularCurve"

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
  have h__af := C h 1
  simp at h__af
  exact h__af

lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A') (h2 : ∀ τ, F τ = F' τ) :
    RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma prod (hh : 0 < h) {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => (have h__af := one h; simp at h__af ⊢; exact h__af)
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
    · subst hk; (have h__af := one h; simp at h__af ⊢; exact h__af)
    · have h__af := zero h
      simp [hk] at h__af ⊢
      exact h__af
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

section JT

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

def jqC : LaurentSeries ℂ := coeffMap castC jq

lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

lemma realL_jqC : RealL 1 jqC jt := fun τ => ModularCurve.hasSum_jq_qParam τ

end JT

section Translates

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
  (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)

def conjC (i : Fin (ℓ + 1)) : LaurentSeries ℂ := coeffMap (sigma ℓ ζ hζ) (PhiGen.conj ℓ ζ i)

def rep (i : Fin (ℓ + 1)) : GL (Fin 2) ℝ :=
  Fin.cases (ModularForm.heckeDiagMatrix ℓ) (fun b : Fin ℓ => ModularForm.heckeMatrix ℓ (b : ℕ)) i

omit hℓ in
@[scoped simp] lemma rep_zero : rep ℓ 0 = ModularForm.heckeDiagMatrix ℓ := by simp [rep]
omit hℓ in
@[scoped simp] lemma rep_succ (b : Fin ℓ) : rep ℓ b.succ = ModularForm.heckeMatrix ℓ (b : ℕ) := by simp [rep]

lemma realL_conjC_zero : RealL ℓ (conjC ℓ ζ hζ 0) (fun τ => jt (ModularForm.heckeDiagMatrix ℓ • τ)) := by
  intro τ
  have h := ModularCurve.hasSum_qParam_heckeDiagMatrix_smul ℓ jqC jt realL_jqC τ
  have hconj : conjC ℓ ζ hζ 0 = qExpand ℂ (ℓ * ℓ) jqC := by
    rw [conjC, PhiGen.conj_zero, coeffMap_qExpand]
    congr 1
    ext m
    simp [jqC_coeff, map_ratCast]
  rw [hconj]
  exact h

omit hℓ in
lemma expRoot_pow_zpow (b : ℕ) (m : ℤ) :
    (expRoot ℓ ^ b) ^ m = Complex.exp (2 * Real.pi * Complex.I * b * m / ℓ) := by
  rw [expRoot, ← Complex.exp_nat_mul, ← Complex.exp_int_mul]
  congr 1
  ring

lemma realL_conjC_succ (b : Fin ℓ) :
    RealL ℓ (conjC ℓ ζ hζ b.succ) (fun τ => jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)) := by
  intro τ
  have h := ModularCurve.hasSum_qParam_heckeMatrix_smul ℓ (b : ℕ) jqC jt realL_jqC τ
  refine h.congr_fun fun m => ?_
  congr 1
  rw [conjC, PhiGen.conj_succ, coeffMap_coeff, qTwist_coeff, map_mul, Units.val_zpow_eq_zpow_val,
    map_zpow₀, Units.val_pow_eq_pow_val, map_pow, sigma_zeta, expRoot_pow_zpow]
  congr 1
  simp [jqC_coeff, map_ratCast]

lemma realL_conjC (i : Fin (ℓ + 1)) : RealL ℓ (conjC ℓ ζ hζ i) (fun τ => jt (rep ℓ i • τ)) := by
  refine Fin.cases ?_ (fun b => ?_) i
  · simpa only [rep_zero] using realL_conjC_zero ℓ ζ hζ
  · simpa only [rep_succ] using realL_conjC_succ ℓ ζ hζ b

lemma map_phiProd : (PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ)) =
    ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjC ℓ ζ hζ i)) := by
  rw [PhiGen.phiProd, ← Polynomial.coe_mapRingHom, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [conjC]

lemma realL_phiProd_coeff (k : ℕ) :
    RealL ℓ (((PhiGen.phiProd ℓ (PhiGen.conj ℓ ζ)).map (coeffMap (sigma ℓ ζ hζ))).coeff k)
      (fun τ => (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))).coeff k) := by
  rw [map_phiProd]
  exact RealL.coeff_prod_X_sub_C (by exact_mod_cast hℓ.out.pos) Finset.univ
    (fun i _ => realL_conjC ℓ ζ hζ i) k

lemma realL_one_of_realL_qExpand (x : LaurentSeries ℂ) (F : ℍ → ℂ) (hx : RealL ℓ (qExpand ℂ ℓ x) F) :
    RealL 1 x F := by
  intro τ
  have hinj : Function.Injective (fun n : ℤ => (ℓ : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast hℓ.out.ne_zero)
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
    field_simp [(Nat.cast_ne_zero.mpr hℓ.out.ne_zero : (ℓ : ℂ) ≠ 0)]
  · intro m hm
    rw [qExpand_coeff_of_not_dvd ℓ _ (fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩), zero_mul]

lemma coeffMap_sigma_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap (sigma ℓ ζ hζ) (coeffEmb (CyclotomicField ℓ ℚ) x) = coeffMap castC x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeffMap_coeff, eq_ratCast, map_ratCast]
  rfl

include hζ in

theorem hasSum_coeff_of_phiGenDescends (c : ℕ → LaurentSeries ℚ) (hc : PhiGen.PhiGenDescends ℓ ζ c)
    (k : ℕ) (τ : ℍ) :
    HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m)
      (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) ^ 3 /
          ModularForm.discriminant (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))).coeff k) := by
  have h1 := realL_phiProd_coeff ℓ ζ hζ k
  rw [Polynomial.coeff_map, hc k, coeffMap_sigma_coeffEmb, coeffMap_qExpand] at h1
  have h2 := realL_one_of_realL_qExpand ℓ _ _ h1 τ
  have hprod : (∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (jt (rep ℓ i • τ)))) =
      (Polynomial.X - Polynomial.C (jt (ModularForm.heckeDiagMatrix ℓ • τ))) *
        ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (jt (ModularForm.heckeMatrix ℓ (b : ℕ) • τ))) := by
    rw [Fin.prod_univ_succ]; simp only [rep_zero, rep_succ]
  rw [hprod] at h2
  exact h2

end Translates

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.ModularCurve"

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (((c k).coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (((Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeDiagMatrix ℓ • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (ModularForm.E₄ (ModularForm.heckeMatrix ℓ (b : ℕ) • τ) ^ 3 / ModularForm.discriminant (ModularForm.heckeMatrix ℓ (b : ℕ) • τ)))).coeff k) :=
  ModularCurve.hasSum_coeff_of_phiGenDescends ℓ ζ hζ c hc k τ

end
p2m_reactivate "P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.ModularCurve"

end S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
end P2MW
export P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff (solution)
