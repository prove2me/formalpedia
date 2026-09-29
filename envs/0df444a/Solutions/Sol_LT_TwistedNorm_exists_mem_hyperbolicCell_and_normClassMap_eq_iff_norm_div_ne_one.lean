-- Prove2me | solution 1 for LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/12aaf7a6-152c-5007-8aeb-f7c658aa2617

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one

set_option autoImplicit false

namespace R4HypB

open Matrix Polynomial LT.TwistedNorm

section Poly

variable {K : Type*} [Field K]

theorem ne_of_X_sub_C_mul_eq {a b c d : K} (hab : a ≠ b)
    (h : (X - C a) * (X - C b) = (X - C c) * (X - C d)) : c ≠ d := by
  intro hcd
  subst hcd
  have ha := congrArg (Polynomial.eval a) h
  have hb := congrArg (Polynomial.eval b) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  have ha' : a - c = 0 := by
    rcases mul_eq_zero.mp ha.symm with h1 | h1 <;> exact h1
  have hb' : b - c = 0 := by
    rcases mul_eq_zero.mp hb.symm with h1 | h1 <;> exact h1
  exact hab (by rw [sub_eq_zero] at ha' hb'; rw [ha', hb'])

theorem charpoly_of_apply_one_zero_eq_zero (M : Matrix (Fin 2) (Fin 2) K) (h : M 1 0 = 0) :
    M.charpoly = (X - C (M 0 0)) * (X - C (M 1 1)) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, h, mul_zero, sub_zero,
    map_add, map_mul]
  ring

end Poly

section Galois

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

theorem prod_range_iterate_eq_algebraMap_norm (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (a : L) :
    ∏ i ∈ Finset.range (Module.finrank F L), (⇑σ)^[i] a = algebraMap F L (Algebra.norm F a) := by
  rw [Algebra.norm_eq_prod_automorphisms, prod_algEquiv_eq_prod_range_of_generator hgen]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [AlgEquiv.coe_pow]

omit [FiniteDimensional F L] [IsGalois F L] in

theorem iterate_apply_eq_prod_mul {r x : L} (h : σ x = r * x) (k : ℕ) :
    (⇑σ)^[k] x = (∏ i ∈ Finset.range k, (⇑σ)^[i] r) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, h, ← mul_assoc, map_prod,
        Finset.prod_range_succ']
      congr 1
      simp only [Function.iterate_zero, id_eq]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Function.iterate_succ_apply']

theorem eq_zero_of_apply_eq_mul_of_norm_ne_one (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {r x : L} (h : σ x = r * x) (hr : Algebra.norm F r ≠ 1) : x = 0 := by
  have hn := iterate_apply_eq_prod_mul h (Module.finrank F L)
  rw [iterate_finrank_apply_of_generator hgen, prod_range_iterate_eq_algebraMap_norm hgen] at hn

  have h1 : (algebraMap F L (Algebra.norm F r) - 1) * x = 0 := by
    rw [sub_mul, one_mul, ← hn, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exfalso
    apply hr
    have h3 : algebraMap F L (Algebra.norm F r) = algebraMap F L 1 := by
      rw [map_one]; exact sub_eq_zero.mp h2
    exact (algebraMap F L).injective h3
  · exact h2

end Galois

section TriangularNorm

variable {L : Type*} [Field L] (τ : L →+* L)

theorem mul_apply_of_upper (P Q : GL (Fin 2) L)
    (hP : (P : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hQ : (Q : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((P * Q : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((P * Q : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
        (P : Matrix (Fin 2) (Fin 2) L) 0 0 * (Q : Matrix (Fin 2) (Fin 2) L) 0 0 ∧
    ((P * Q : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
        (P : Matrix (Fin 2) (Fin 2) L) 1 1 * (Q : Matrix (Fin 2) (Fin 2) L) 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hP, hQ]

theorem map_apply_entries (δ : GL (Fin 2) L) (i j : Fin 2) (k : ℕ) :
    (((Matrix.GeneralLinearGroup.map (n := Fin 2) τ)^[k] δ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) i j = (⇑τ)^[k] ((δ : Matrix (Fin 2) (Fin 2) L) i j) :=
  iterate_generalLinearGroup_map_apply τ k δ i j

theorem sigmaPartialNorm_upper (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (r : ℕ) :
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map τ) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map τ) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 0 0 = ∏ i ∈ Finset.range r, (⇑τ)^[i] ((δ : Matrix (Fin 2) (Fin 2) L) 0 0) ∧
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map τ) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 1 = ∏ i ∈ Finset.range r, (⇑τ)^[i] ((δ : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  induction r with
  | zero =>
      simp [sigmaPartialNorm_zero]
  | succ r ih =>
      obtain ⟨ih10, ih00, ih11⟩ := ih
      have hQ : (((Matrix.GeneralLinearGroup.map (n := Fin 2) τ)^[r] δ : GL (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
        rw [map_apply_entries, hδ]
        exact Function.iterate_fixed (map_zero _) _
      obtain ⟨h10, h00, h11⟩ := mul_apply_of_upper
        (sigmaPartialNorm (Matrix.GeneralLinearGroup.map τ) δ r)
        ((Matrix.GeneralLinearGroup.map (n := Fin 2) τ)^[r] δ) ih10 hQ
      rw [sigmaPartialNorm_succ]
      refine ⟨h10, ?_, ?_⟩
      · rw [h00, ih00, map_apply_entries, Finset.prod_range_succ]
      · rw [h11, ih11, map_apply_entries, Finset.prod_range_succ]

end TriangularNorm

section NormRep

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

theorem charpoly_normRep_map (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) L) :
    ((normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly.map (algebraMap F L) =
      ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ :
          GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).charpoly := by
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  exact charpoly_map_eq_charpoly_of_conj_eq_map hP

theorem charpoly_normRep_eq_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ((normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly =
      ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  rw [← hc, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact (Matrix.charpoly_units_conj c _).symm

theorem charpoly_sigmaNormPow_of_upper (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ :
          GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).charpoly =
      (X - C (algebraMap F L (Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0)))) *
        (X - C (algebraMap F L (Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 1 1)))) := by
  obtain ⟨h10, h00, h11⟩ := sigmaPartialNorm_upper (σ : L →+* L) δ hδ (Module.finrank F L)
  rw [sigmaNormPow_def, charpoly_of_apply_one_zero_eq_zero _ h10, h00, h11]
  have e : ∀ a : L, ∏ i ∈ Finset.range (Module.finrank F L), (⇑(σ : L →+* L))^[i] a =
      algebraMap F L (Algebra.norm F a) := fun a =>
    prod_range_iterate_eq_algebraMap_norm hgen a
  rw [e, e]

end NormRep

section B

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

theorem entries_ne_zero_of_upper (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet := Matrix.isUnits_det_units δ
  rw [Matrix.det_fin_two, hδ, mul_zero, sub_zero] at hdet
  have hne := hdet.ne_zero
  exact ⟨left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

theorem thmB (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.hyperbolicCell F ∧
        normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 := by
  obtain ⟨ha0, hd0⟩ := entries_ne_zero_of_upper δ hδ
  set na := Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0) with hna
  set nd := Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 1 1) with hnd
  have hnd0 : nd ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd0

  have hrep : ((normRep hgen δ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly =
      (X - C na) * (X - C nd) := by
    apply Polynomial.map_injective (algebraMap F L) (algebraMap F L).injective
    rw [charpoly_normRep_map hgen δ, charpoly_sigmaNormPow_of_upper hgen δ hδ]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hdiv : Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1)
      = na / nd := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, ← div_eq_mul_inv]
  constructor
  · rintro ⟨γ, hγ, hclass⟩
    obtain ⟨a, b, hab, hchar⟩ := hγ
    rw [← charpoly_normRep_eq_of_normClassMap_eq hgen hclass, hrep] at hchar
    have hnn : na ≠ nd := ne_of_X_sub_C_mul_eq hab hchar.symm
    rw [hdiv]
    intro h1
    apply hnn
    rw [div_eq_one_iff_eq hnd0] at h1
    exact h1
  · intro hN
    rw [hdiv] at hN
    have hnn : na ≠ nd := by
      intro h; apply hN; rw [h, div_self hnd0]
    refine ⟨normRep hgen δ, ⟨na, nd, hnn, hrep⟩, normClassMap_mk hgen δ⟩

end B

end R4HypB

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.hyperbolicCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      Algebra.norm F ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 :=
  R4HypB.thmB hgen δ hδ

end S_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
end P2MW
export P2MW.S_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one (solution)
