-- Prove2me | solution 1 for ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6cd85d0b-d0bb-5e15-b57d-f5d694c67ccd

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Theorems.Thm_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "jq PoleOrderLE coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single hasSum_jq_qParam coeff_eq_zero_of_hasSum_of_slash_invariant hasSum_qParam_mul_laurent E4_cube_div_discriminant_smul exists_aeval_jq_sub_holomorphicAtInfty"
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

section JT

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

def jqC : LaurentSeries ℂ := coeffMap castC jq

lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

lemma realL_jqC : RealL 1 jqC jt := fun τ => ModularCurve.hasSum_jq_qParam τ

end JT

section JOut

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

lemma realL_aeval_jq (P : Polynomial ℚ) :
    RealL 1 (coeffMap castC (Polynomial.aeval jq P)) (fun τ => (P.map castC).eval (jt τ)) := by
  induction P using Polynomial.induction_on with
  | C a =>
    refine (RealL.C 1 (a : ℂ)).congr ?_ fun τ => ?_
    · rw [Polynomial.aeval_C, algebraMap_laurentSeries_eq_single, coeffMap_single]
      rfl
    · simp
  | add P Q hP hQ =>
    refine (hP.add hQ).congr ?_ fun τ => ?_
    · rw [map_add, map_add]
    · simp
  | monomial n a ih =>
    refine (ih.mul one_pos realL_jqC).congr ?_ fun τ => ?_
    · rw [jqC, ← map_mul]
      congr 1
      symm
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    · simp [pow_succ, mul_assoc]

theorem mem_adjoin_jq_of_realL_invariant (f : LaurentSeries ℚ) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) : f ∈ Algebra.adjoin ℚ {jq} := by

  obtain ⟨n, hn⟩ : ∃ n : ℕ, PoleOrderLE f n := by
    by_cases hf0 : f = 0
    · exact ⟨0, fun m _ => by simp [hf0]⟩
    refine ⟨(-f.order).toNat, fun m hm => HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hm ?_)⟩
    have := Int.self_le_toNat (-f.order)
    omega

  obtain ⟨P, -, he⟩ := ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty n f hn
  set e : LaurentSeries ℚ := f - Polynomial.aeval jq P with he_def
  have he0 : ∀ m : ℤ, m < 0 → e.coeff m = 0 := fun m hm => he m (by simpa using hm)
  have hfR : RealL 1 (coeffMap castC f) F := hF
  have hE : RealL 1 (coeffMap castC e) (F - fun τ => (P.map castC).eval (jt τ)) := by
    rw [he_def, map_sub]
    exact hfR.sub (realL_aeval_jq P)
  have hEinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (F - fun τ => (P.map castC).eval (jt τ)) (γ • τ) = (F - fun τ => (P.map castC).eval (jt τ)) τ := by
    intro γ τ
    simp only [Pi.sub_apply, hinv γ τ, jt_smul γ τ]

  have hEN : ∀ τ : ℍ, HasSum (fun n : ℕ => ((e.coeff n : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ n)
      ((F - fun τ => (P.map castC).eval (jt τ)) τ) := by
    intro τ
    have h := hE τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · exact h
    · intro m hm
      have hm' : m < 0 := by
        by_contra hge
        push Not at hge
        exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
      rw [coeffMap_coeff, he0 m hm', map_zero, zero_mul]
  have hvan : ∀ n : ℕ, n ≠ 0 → e.coeff n = 0 := fun n hn => by
    have := coeff_eq_zero_of_hasSum_of_slash_invariant hEN hEinv hn
    exact_mod_cast this

  have heconst : e = HahnSeries.single 0 (e.coeff 0) := by
    ext m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [he0 m hm, HahnSeries.coeff_single_of_ne hm.ne]
    · rw [HahnSeries.coeff_single_same]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
      rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne')]
      exact hvan n (by exact_mod_cast hm.ne')
  have hck : f = algebraMap ℚ (LaurentSeries ℚ) (e.coeff 0) + Polynomial.aeval jq P := by
    rw [algebraMap_laurentSeries_eq_single, ← heconst, he_def, sub_add_cancel]
  rw [hck]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Polynomial.aeval_mem_adjoin_singleton ℚ jq)

end JOut

end ModularCurve

theorem solution (f : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ) (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) : f ∈ Algebra.adjoin ℚ {ModularCurve.jq} :=
  ModularCurve.mem_adjoin_jq_of_realL_invariant f F hF hinv

end

end S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
end P2MW
export P2MW.S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant (solution)
