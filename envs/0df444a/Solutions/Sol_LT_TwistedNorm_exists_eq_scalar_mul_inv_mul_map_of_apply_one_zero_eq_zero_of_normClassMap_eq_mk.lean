-- Prove2me | solution 1 for LT.TwistedNorm.exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/09c16a3c-e623-5f53-8c53-85f68e2eb477

import Mathlib
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk

set_option autoImplicit false

noncomputable section

namespace R3TriFam

open LT.TwistedNorm LT.TwistedNorm.GL2 Matrix Polynomial

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

abbrev sc : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2)

abbrev σG (σ : L ≃ₐ[F] L) : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

abbrev σU (σ : L ≃ₐ[F] L) : Lˣ →* Lˣ := Units.map ((σ : L →+* L) : L →* L)

theorem sc_comm (u : Lˣ) (g : GL (Fin 2) L) : sc u * g = g * sc u := by
  apply Units.ext
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (u : L) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) L)).eq

theorem σG_sc (σ : L ≃ₐ[F] L) (u : Lˣ) : σG σ (sc u) = sc (σU σ u) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply]
  change σ ((Matrix.scalar (Fin 2) (u : L)) i j) = Matrix.scalar (Fin 2) (σ (u : L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem sigmaPartialNorm_sc_mul (σ : L ≃ₐ[F] L) (u : Lˣ) (δ : GL (Fin 2) L) (r : ℕ) :
    sigmaPartialNorm (σG σ) (sc u * δ) r =
      sc (sigmaPartialNorm (σU σ) u r) * sigmaPartialNorm (σG σ) δ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul, map_mul,
        σG_sc]
      rw [mul_assoc (sc u), ← mul_assoc δ, ← sc_comm _ δ]
      simp only [mul_assoc]

theorem coe_sc_sigmaNormPow [FiniteDimensional F L] [IsGalois F L] {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    ((sc (sigmaNormPow (σU σ) (Module.finrank F L) u) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L (Algebra.norm F (u : L)) • (1 : Matrix (Fin 2) (Fin 2) L) := by
  rw [← coe_sigmaNormPow_units_eq_algebraMap_norm hgen u]
  ext i j
  change Matrix.scalar (Fin 2) _ i j = _
  rw [Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem coe_mul_map_apply (σ : L ≃ₐ[F] L) (δ P : GL (Fin 2) L) (i j : Fin 2) :
    ((δ * σG σ P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (δ : Matrix (Fin 2) (Fin 2) L) i 0 * σ ((P : Matrix (Fin 2) (Fin 2) L) 0 j) +
        (δ : Matrix (Fin 2) (Fin 2) L) i 1 * σ ((P : Matrix (Fin 2) (Fin 2) L) 1 j) := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

theorem sigmaPartialNorm_triangular (σ : L ≃ₐ[F] L) (δ : GL (Fin 2) L)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (a d : Lˣ)
    (ha : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = a) (hd : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = d) (r : ℕ) :
    ((sigmaPartialNorm (σG σ) δ r : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((sigmaPartialNorm (σG σ) δ r : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 =
      ((sigmaPartialNorm (σU σ) a r : Lˣ) : L) ∧
    ((sigmaPartialNorm (σG σ) δ r : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 =
      ((sigmaPartialNorm (σU σ) d r : Lˣ) : L) := by
  induction r with
  | zero =>
      simp only [sigmaPartialNorm_zero, Units.val_one]
      refine ⟨?_, ?_, ?_⟩
      · exact Matrix.one_apply_ne (by decide)
      · exact Matrix.one_apply_eq 0
      · exact Matrix.one_apply_eq 1
  | succ r ih =>
      obtain ⟨h10, h00, h11⟩ := ih
      simp only [sigmaPartialNorm_succ']
      refine ⟨?_, ?_, ?_⟩
      · rw [coe_mul_map_apply, hδ, h10, zero_mul, map_zero, mul_zero, add_zero]
      · rw [coe_mul_map_apply, ha, h00, h10, map_zero, mul_zero, add_zero, Units.val_mul, Units.coe_map,
          MonoidHom.coe_coe]
        rfl
      · rw [coe_mul_map_apply, hδ, hd, h11, zero_mul, zero_add, Units.val_mul, Units.coe_map,
          MonoidHom.coe_coe]
        rfl

variable [FiniteDimensional F L] [IsGalois F L]

theorem isNormRep_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (hN : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hN
  obtain ⟨Q, hQ⟩ := hN
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
  rw [← hQ, map_mul, map_mul, map_inv, ← hP]
  group

theorem main [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : GL (Fin 2) F)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F)
    (hN : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ (h : GL (Fin 2) L) (u : Lˣ), δ = sc u * (h⁻¹ * σG σ h) := by
  classical

  have hdet : (δ : Matrix (Fin 2) (Fin 2) L).det =
      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 * (δ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [Matrix.det_fin_two, hδ, mul_zero, sub_zero]
  have hdet0 : (δ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero
  have ha0 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := fun h => hdet0 (by rw [hdet, h, zero_mul])
  have hd0 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := fun h => hdet0 (by rw [hdet, h, mul_zero])
  set a : Lˣ := Units.mk0 _ ha0 with ha
  set d : Lˣ := Units.mk0 _ hd0 with hd
  have hNtri := sigmaPartialNorm_triangular σ δ hδ a d rfl rfl (Module.finrank F L)
  obtain ⟨hN10, hN00, hN11⟩ := hNtri
  rw [← sigmaNormPow_def] at hN10
  rw [← sigmaNormPow_def, ← sigmaNormPow_def, coe_sigmaNormPow_units_eq_algebraMap_norm hgen] at hN00
  rw [← sigmaNormPow_def, ← sigmaNormPow_def, coe_sigmaNormPow_units_eq_algebraMap_norm hgen] at hN11
  set N := sigmaNormPow (σG σ) (Module.finrank F L) δ with hNdef
  set A : L := algebraMap F L (Algebra.norm F (a : L)) with hA
  set Dd : L := algebraMap F L (Algebra.norm F (d : L)) with hDd

  obtain ⟨P, hP⟩ := isNormRep_of_normClassMap_mk_eq hgen hN

  have hchar : (γ : Matrix (Fin 2) (Fin 2) F).charpoly.map (algebraMap F L) =
      (N : Matrix (Fin 2) (Fin 2) L).charpoly := charpoly_map_eq_charpoly_of_conj_eq_map hP
  have hrootL : ((N : Matrix (Fin 2) (Fin 2) L).charpoly).IsRoot A := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, hN00, hN11, hN10]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero]
    ring
  have hroot : ((γ : Matrix (Fin 2) (Fin 2) F).charpoly).IsRoot (Algebra.norm F (a : L)) := by
    rw [← hchar] at hrootL
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, hA, Polynomial.eval₂_at_apply] at hrootL
    exact (algebraMap F L).injective (by rw [hrootL, map_zero])

  have hγc : γ ∈ AutomorphicForm.centralCell F := by
    rcases hγ with he | hc
    · exact absurd hroot (he _)
    · exact hc
  obtain ⟨c, hc⟩ := AutomorphicForm.mem_centralCell_iff.mp hγc

  have hγL : ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) := generalLinearGroup_map_smul_one_coe c γ hc
  have hNeq : N = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
    have hP' : P⁻¹ * N * P = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := hP
    have h1 : N = P * Matrix.GeneralLinearGroup.map (algebraMap F L) γ * P⁻¹ := by
      rw [← hP']; group
    rw [h1]
    have h2 := conj_eq_self_of_coe_eq_smul_one (Matrix.GeneralLinearGroup.map (algebraMap F L) γ) P⁻¹
      (algebraMap F L c) hγL
    rw [inv_inv] at h2
    exact h2
  have hcA : algebraMap F L c = A := by
    have h := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L) 0 0) hNeq
    rw [hN00, hγL, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    exact h.symm

  have hNsc : sigmaNormPow (σG σ) (Module.finrank F L) (sc a) =
      Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
    have h1 : sigmaNormPow (σG σ) (Module.finrank F L) (sc a) =
        sc (sigmaNormPow (σU σ) (Module.finrank F L) a) := by
      rw [sigmaNormPow_def, sigmaNormPow_def, ← mul_one (sc a), sigmaPartialNorm_sc_mul,
        sigmaPartialNorm_one_left, mul_one]
    apply Units.ext
    rw [h1, coe_sc_sigmaNormPow hgen a, hγL, hcA]
  have hrep : IsNormRep σ γ (sc a) := ⟨1, by rw [inv_one, one_mul, mul_one]; exact hNsc⟩
  have hNsc' : normClassMap hgen (SigmaConjClasses.mk σ (sc a)) = ConjClasses.mk γ :=
    normClassMap_mk_eq_of_isNormRep hgen hrep

  have hmk : SigmaConjClasses.mk σ (sc a) = SigmaConjClasses.mk σ δ :=
    sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell hgen γ hγc (sc a) δ hNsc' hN
  obtain ⟨h, hh⟩ := SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mp hmk
  refine ⟨h, a, ?_⟩
  rw [hh, mul_assoc, ← mul_assoc, ← sc_comm a h⁻¹, mul_assoc]

end R3TriFam

end

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (hγ : γ ∈ AutomorphicForm.ellipticCell F ∨ γ ∈ AutomorphicForm.centralCell F)
    (hN : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ (h : Matrix.GeneralLinearGroup (Fin 2) L) (u : Lˣ),
      δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
        (h⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) :=
  R3TriFam.main hgen δ hδ γ hγ hN

end S_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk
end P2MW
export P2MW.S_LT_TwistedNorm_exists_eq_scalar_mul_inv_mul_map_of_apply_one_zero_eq_zero_of_normClassMap_eq_mk (solution)
