-- Prove2me | solution 1 for LT.TwistedNorm.apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/abad9fb5-d021-5da9-8952-bde5764e5255

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell

set_option autoImplicit false

namespace R4UniCoset

open Matrix Polynomial LT.TwistedNorm

section Poly

variable {K : Type*} [Field K]

theorem charpoly_of_upper (M : Matrix (Fin 2) (Fin 2) K) (h : M 1 0 = 0) :
    M.charpoly = (X - C (M 0 0)) * (X - C (M 1 1)) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, h, mul_zero, sub_zero,
    map_add, map_mul]
  ring

theorem eq_of_X_sub_C_mul_eq_sq {u v w : K} (h : (X - C u) * (X - C v) = (X - C w) ^ 2) :
    u = w ∧ v = w := by
  have hu := congrArg (Polynomial.eval u) h
  have hv := congrArg (Polynomial.eval v) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero, eval_pow] at hu hv
  exact ⟨sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hu.symm),
    sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv.symm)⟩

end Poly

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
        rw [iterate_generalLinearGroup_map_apply, hδ]
        exact Function.iterate_fixed (map_zero _) _
      obtain ⟨h10, h00, h11⟩ := mul_apply_of_upper
        (sigmaPartialNorm (Matrix.GeneralLinearGroup.map τ) δ r)
        ((Matrix.GeneralLinearGroup.map (n := Fin 2) τ)^[r] δ) ih10 hQ
      rw [sigmaPartialNorm_succ]
      refine ⟨h10, ?_, ?_⟩
      · rw [h00, ih00, iterate_generalLinearGroup_map_apply, Finset.prod_range_succ]
      · rw [h11, ih11, iterate_generalLinearGroup_map_apply, Finset.prod_range_succ]

end TriangularNorm

section Main

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

theorem isNormRep_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) c⁻¹, ?_⟩
  rw [← hc, map_mul, map_mul, map_inv, ← hP]
  group

theorem sigmaNormPow_entries_of_upper_of_unipotent (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (β : GL (Fin 2) L) (hβ : (β : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    {γ : GL (Fin 2) F} (hγ : γ ∈ AutomorphicForm.unipotentCell F)
    (hclass : normClassMap hgen (SigmaConjClasses.mk σ β) = ConjClasses.mk γ) :
    ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 0 0 =
      ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 1 ∧
    ((sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
  set N := sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β with hN
  obtain ⟨h10, -, -⟩ := sigmaPartialNorm_upper (σ : L →+* L) β hβ (Module.finrank F L)
  rw [← sigmaNormPow_def, ← hN] at h10
  obtain ⟨hnc, a, hchar⟩ := hγ
  obtain ⟨P, hP⟩ := isNormRep_of_normClassMap_eq hgen hclass
  rw [← hN] at hP

  have hcharN : ((N : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).charpoly = (X - C (algebraMap F L a)) ^ 2 := by
    rw [← charpoly_map_eq_charpoly_of_conj_eq_map hP, hchar]
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [charpoly_of_upper _ h10] at hcharN
  obtain ⟨h00, h11⟩ := eq_of_X_sub_C_mul_eq_sq hcharN
  refine ⟨h10, h00.trans h11.symm, ?_⟩
  intro h01

  have hscal : ((N : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L a • (1 : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01, h00, h11]
  have hconj : P⁻¹ * N * P = N := GL2.conj_eq_self_of_coe_eq_smul_one N P _ hscal
  rw [hconj] at hP
  apply hnc
  refine ⟨a, ?_⟩
  ext i j
  have hij := congrFun (congrFun (congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hP) i) j
  simp only [hscal, Matrix.GeneralLinearGroup.map_apply] at hij
  apply (algebraMap F L).injective
  rw [← hij]
  fin_cases i <;> fin_cases j <;> simp

theorem main (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (β : GL (Fin 2) L) (hβ : (β : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (hunip : ∃ γ : GL (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
      normClassMap hgen (SigmaConjClasses.mk σ β) = ConjClasses.mk γ)
    (η : GL (Fin 2) L)
    (hη : ((η⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) η : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((η : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  obtain ⟨γ, hγ, hclass⟩ := hunip
  set β' := η⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) η with hβ'
  have hclass' : normClassMap hgen (SigmaConjClasses.mk σ β') = ConjClasses.mk γ := by
    rw [← hclass]
    congr 1
    exact (SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨η, rfl⟩).symm
  obtain ⟨-, hdiag, h01⟩ := sigmaNormPow_entries_of_upper_of_unipotent hgen β hβ hγ hclass
  obtain ⟨h10', hdiag', -⟩ := sigmaNormPow_entries_of_upper_of_unipotent hgen β' hη hγ hclass'
  set N := sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β with hN
  set N' := sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) β' with hN'
  have hσ : ∀ a : L, (⇑(σ : L →+* L))^[Module.finrank F L] a = a :=
    fun a => iterate_finrank_apply_of_generator hgen a

  have hNN : η * N' = N * η := by
    rw [hN', hβ', sigmaNormPow_sigmaConj_generalLinearGroup (n := Fin 2) hσ η β, ← hN]
    group
  have hM := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) hNN
  simp only [Units.val_mul] at hM
  set A : Matrix (Fin 2) (Fin 2) L := ((N : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hA
  set A' : Matrix (Fin 2) (Fin 2) L := ((N' : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hA'
  set E : Matrix (Fin 2) (Fin 2) L := ((η : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) with hE
  have h10A : A 1 0 = 0 := by
    obtain ⟨h, -, -⟩ := sigmaPartialNorm_upper (σ : L →+* L) β hβ (Module.finrank F L)
    rw [← sigmaNormPow_def] at h
    exact h
  have e10 := congrFun (congrFun hM 1) 0
  have e00 := congrFun (congrFun hM 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e10 e00
  change E 1 0 * A' 0 0 + E 1 1 * A' 1 0 = A 1 0 * E 0 0 + A 1 1 * E 1 0 at e10
  change E 0 0 * A' 0 0 + E 0 1 * A' 1 0 = A 0 0 * E 0 0 + A 0 1 * E 1 0 at e00
  change A' 1 0 = 0 at h10'
  change A' 0 0 = A' 1 1 at hdiag'
  change A 0 0 = A 1 1 at hdiag
  change A 0 1 ≠ 0 at h01
  rw [h10', mul_zero, add_zero, h10A, zero_mul, zero_add] at e10
  rw [h10', mul_zero, add_zero] at e00

  by_contra hr
  have hx : A' 0 0 = A 0 0 := by
    rw [hdiag]
    exact mul_left_cancel₀ hr (e10.trans (mul_comm _ _))
  rw [hx] at e00
  have : A 0 1 * E 1 0 = 0 := by linear_combination -e00
  rcases mul_eq_zero.mp this with h | h
  · exact h01 h
  · exact hr h

end Main

end R4UniCoset

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (β : Matrix.GeneralLinearGroup (Fin 2) L) (hβ : (β : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.unipotentCell F)
    (hclass : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ β) = ConjClasses.mk γ)
    (η : Matrix.GeneralLinearGroup (Fin 2) L)
    (hη : ((η⁻¹ * β * Matrix.GeneralLinearGroup.map (σ : L →+* L) η :
        Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((η : Matrix.GeneralLinearGroup (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 :=
  R4UniCoset.main hgen β hβ ⟨γ, hγ, hclass⟩ η hη

end S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell
end P2MW
export P2MW.S_LT_TwistedNorm_apply_one_zero_eq_zero_of_sigmaConj_upper_of_normClassMap_eq_mk_of_mem_unipotentCell (solution)
