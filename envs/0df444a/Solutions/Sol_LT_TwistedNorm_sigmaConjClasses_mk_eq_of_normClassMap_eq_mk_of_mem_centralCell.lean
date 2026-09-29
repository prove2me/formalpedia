-- Prove2me | solution 1 for LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/78717f81-a230-55da-8856-f05e69b0c2a4

import Mathlib
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell

set_option autoImplicit false

namespace R2CentralInj

open Matrix LT.TwistedNorm LT.TwistedNorm.GL2 Finset

section Dedekind

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

theorem sum_algEquiv_eq_sum_range_of_generator {M : Type*} [AddCommMonoid M] {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (f : (L ≃ₐ[F] L) → M) :
    ∑ τ : L ≃ₐ[F] L, f τ = ∑ i ∈ Finset.range (Module.finrank F L), f (σ ^ i) := by
  classical
  have horder : orderOf σ = Module.finrank F L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    intro i j hij
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij)
  have hbij : Function.Bijective fun i : Fin (orderOf σ) => σ ^ (i : ℕ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [Fintype.card_fin, horder, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]⟩
  rw [← Fintype.sum_bijective _ hbij (fun i => f (σ ^ (i : ℕ))) f (fun _ => rfl),
    ← horder, ← Fin.sum_univ_eq_sum_range]

theorem orderOf_eq_finrank_of_generator {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) : orderOf σ = Module.finrank F L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]

theorem coeff_eq_of_sum_smul_pow_eq_pow {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (a : ℕ → L) (k : ℕ) (hk : k < Module.finrank F L)
    (h : ∀ x : L, (σ ^ k) x = ∑ l ∈ Finset.range (Module.finrank F L), a l * (σ ^ l) x)
    (l : ℕ) (hl : l < Module.finrank F L) : a l = if l = k then 1 else 0 := by
  classical
  set n := Module.finrank F L with hn

  let f : Fin n → (L →* L) := fun i => ((σ ^ (i : ℕ) : L ≃ₐ[F] L) : L →* L)
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hσij : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      apply AlgEquiv.ext
      intro x
      have := congrArg (fun g : L →* L => g x) hij
      simpa [f] using this
    have hio : (i : ℕ) < orderOf σ := by rw [orderOf_eq_finrank_of_generator hgen]; exact i.2
    have hjo : (j : ℕ) < orderOf σ := by rw [orderOf_eq_finrank_of_generator hgen]; exact j.2
    exact pow_injOn_Iio_orderOf hio hjo hσij
  have hli := (linearIndependent_monoidHom L L).comp f hf

  have hfx : ∀ (i : Fin n) (x : L), ((f i : L →* L) : L → L) x = (σ ^ (i : ℕ)) x := fun i x => rfl
  have hrel : ∑ i : Fin n, (a i - if (i : ℕ) = k then 1 else 0) • ((f i : L →* L) : L → L) = 0 := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, hfx]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin n, a i * (σ ^ (i : ℕ)) x = ∑ l ∈ Finset.range n, a l * (σ ^ l) x :=
      Fin.sum_univ_eq_sum_range (fun l => a l * (σ ^ l) x) n
    have h2 : ∑ i : Fin n, (if (i : ℕ) = k then (1 : L) else 0) * (σ ^ (i : ℕ)) x = (σ ^ k) x := by
      rw [Fin.sum_univ_eq_sum_range (fun l => (if l = k then (1 : L) else 0) * (σ ^ l) x) n]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hk, if_true]
    rw [h1, h2, ← h x, sub_self]
  have := linearIndependent_iff'.mp hli Finset.univ
    (fun i => a i - if (i : ℕ) = k then 1 else 0) hrel ⟨l, hl⟩ (Finset.mem_univ _)
  exact sub_eq_zero.mp this

theorem sum_basis_mul_pow_dualBasis {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F L)
    (k : ℕ) (hk : k < Module.finrank F L) :
    ∑ i, b i * (σ ^ k) ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b i)
      = if k = 0 then 1 else 0 := by
  classical
  set n := Module.finrank F L with hn
  set d := (Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b with hd

  set a : ℕ → L := fun l => ∑ i, (σ ^ l) (b i) * (σ ^ k) (d i) with ha
  have key : ∀ x : L, (σ ^ k) x = ∑ l ∈ Finset.range n, a l * (σ ^ l) x := by
    intro x

    have hx : x = ∑ i, Algebra.trace F L (x * b i) • d i := by
      conv_lhs => rw [← d.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    have hstep : (σ ^ k) x = ∑ i, algebraMap F L (Algebra.trace F L (x * b i)) * (σ ^ k) (d i) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
    rw [hstep]
    have htr : ∀ i, algebraMap F L (Algebra.trace F L (x * b i))
        = ∑ l ∈ Finset.range n, (σ ^ l) x * (σ ^ l) (b i) := by
      intro i
      rw [trace_eq_sum_automorphisms, sum_algEquiv_eq_sum_range_of_generator hgen]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul]
    simp_rw [htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ha]
    simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h0 := coeff_eq_of_sum_smul_pow_eq_pow hgen a k hk key 0 (Module.finrank_pos)
  rw [ha] at h0
  simp only [pow_zero, AlgEquiv.one_apply] at h0
  rw [h0]
  by_cases hk0 : k = 0
  · subst hk0; simp
  · simp [hk0, Ne.symm hk0]

end Dedekind

section Descent

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable (σ : L ≃ₐ[F] L) (δ₁ δ₂ : GL (Fin 2) L)

noncomputable def σM : Matrix (Fin 2) (Fin 2) L →+* Matrix (Fin 2) (Fin 2) L :=
  (σ : L →+* L).mapMatrix

noncomputable def σG : GL (Fin 2) L →* GL (Fin 2) L :=
  Matrix.GeneralLinearGroup.map (σ : L →+* L)

theorem σM_apply (M : Matrix (Fin 2) (Fin 2) L) (i j : Fin 2) : σM σ M i j = σ (M i j) := rfl

theorem σM_coe (P : GL (Fin 2) L) :
    σM σ (P : Matrix (Fin 2) (Fin 2) L) = ((σG σ P : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  rw [σG, coe_generalLinearGroup_map]; rfl

theorem σM_smul (x : L) (M : Matrix (Fin 2) (Fin 2) L) : σM σ (x • M) = σ x • σM σ M := by
  ext i j
  simp [σM_apply, Matrix.smul_apply]

theorem σM_iterate_apply (r : ℕ) (M : Matrix (Fin 2) (Fin 2) L) (i j : Fin 2) :
    ((σM σ)^[r] M) i j = (⇑σ)^[r] (M i j) := by
  induction r generalizing M with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]; rfl

noncomputable def Θ : Matrix (Fin 2) (Fin 2) L →+ Matrix (Fin 2) (Fin 2) L where
  toFun M := (δ₁ : Matrix (Fin 2) (Fin 2) L) * σM σ M * ((δ₂⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
  map_zero' := by simp
  map_add' M N := by rw [map_add, Matrix.mul_add, Matrix.add_mul]

theorem Θ_apply (M : Matrix (Fin 2) (Fin 2) L) :
    Θ σ δ₁ δ₂ M = (δ₁ : Matrix (Fin 2) (Fin 2) L) * σM σ M *
      ((δ₂⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := rfl

theorem Θ_smul (x : L) (M : Matrix (Fin 2) (Fin 2) L) :
    Θ σ δ₁ δ₂ (x • M) = σ x • Θ σ δ₁ δ₂ M := by
  rw [Θ_apply, Θ_apply, σM_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem Θ_iterate_add (r : ℕ) (M N : Matrix (Fin 2) (Fin 2) L) :
    (Θ σ δ₁ δ₂)^[r] (M + N) = (Θ σ δ₁ δ₂)^[r] M + (Θ σ δ₁ δ₂)^[r] N := by
  induction r generalizing M N with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_add, ih]

theorem Θ_iterate_smul (r : ℕ) (x : L) (M : Matrix (Fin 2) (Fin 2) L) :
    (Θ σ δ₁ δ₂)^[r] (x • M) = (⇑σ)^[r] x • (Θ σ δ₁ δ₂)^[r] M := by
  induction r generalizing x M with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        Θ_smul, ih]

theorem Θ_iterate (r : ℕ) (M : Matrix (Fin 2) (Fin 2) L) :
    (Θ σ δ₁ δ₂)^[r] M =
      ((sigmaPartialNorm (σG σ) δ₁ r : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (σM σ)^[r] M *
        (((sigmaPartialNorm (σG σ) δ₂ r)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
  induction r generalizing M with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, Θ_apply, Function.iterate_succ_apply']
      rw [map_mul, map_mul, σM_coe, σM_coe, sigmaPartialNorm_succ', sigmaPartialNorm_succ']
      rw [Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_inv]
      simp only [Matrix.mul_assoc]

noncomputable def avg (n : ℕ) (x : L) : Matrix (Fin 2) (Fin 2) L :=
  ∑ r ∈ Finset.range n, (Θ σ δ₁ δ₂)^[r] (x • (1 : Matrix (Fin 2) (Fin 2) L))

theorem avg_eq (n : ℕ) (x : L) :
    avg σ δ₁ δ₂ n x = ∑ r ∈ Finset.range n, (⇑σ)^[r] x • (Θ σ δ₁ δ₂)^[r] 1 := by
  unfold avg
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Θ_iterate_smul]

theorem Θ_avg (n : ℕ) (hΘn : ∀ M, (Θ σ δ₁ δ₂)^[n] M = M) (x : L) :
    Θ σ δ₁ δ₂ (avg σ δ₁ δ₂ n x) = avg σ δ₁ δ₂ n x := by
  unfold avg
  rw [map_sum]
  have h : ∀ r, Θ σ δ₁ δ₂ ((Θ σ δ₁ δ₂)^[r] (x • (1 : Matrix (Fin 2) (Fin 2) L)))
      = (Θ σ δ₁ δ₂)^[r + 1] (x • (1 : Matrix (Fin 2) (Fin 2) L)) := by
    intro r; rw [Function.iterate_succ_apply']
  simp_rw [h]
  have h1 := Finset.sum_range_succ' (fun r => (Θ σ δ₁ δ₂)^[r] (x • (1 : Matrix (Fin 2) (Fin 2) L))) n
  have h2 := Finset.sum_range_succ (fun r => (Θ σ δ₁ δ₂)^[r] (x • (1 : Matrix (Fin 2) (Fin 2) L))) n
  rw [hΘn] at h2
  rw [Function.iterate_zero, id_eq, h2] at h1
  exact (add_right_cancel h1).symm

theorem Θ_algebraMap_smul (a : F) (M : Matrix (Fin 2) (Fin 2) L) :
    Θ σ δ₁ δ₂ (algebraMap F L a • M) = algebraMap F L a • Θ σ δ₁ δ₂ M := by
  rw [Θ_smul, AlgEquiv.commutes]

section Infinite

variable [Infinite F]

theorem exists_fixed_det_ne_zero (m : ℕ) :
    ∀ (M₀ : Matrix (Fin 2) (Fin 2) L), Θ σ δ₁ δ₂ M₀ = M₀ →
    ∀ (Ms : Fin m → Matrix (Fin 2) (Fin 2) L), (∀ j, Θ σ δ₁ δ₂ (Ms j) = Ms j) →
    ∀ (c : Fin m → L), (M₀ + ∑ j, c j • Ms j).det ≠ 0 →
    ∃ M : Matrix (Fin 2) (Fin 2) L, Θ σ δ₁ δ₂ M = M ∧ M.det ≠ 0 := by
  induction m with
  | zero =>
      intro M₀ hM₀ Ms _ c hdet
      refine ⟨M₀, hM₀, ?_⟩
      simpa using hdet
  | succ m ih =>
      intro M₀ hM₀ Ms hMs c hdet
      classical

      set B : Matrix (Fin 2) (Fin 2) L := M₀ + ∑ j : Fin m, c j.succ • Ms j.succ with hB
      set N : Matrix (Fin 2) (Fin 2) L := Ms 0 with hN
      have hdet' : (B + c 0 • N).det ≠ 0 := by
        have : M₀ + ∑ j, c j • Ms j = B + c 0 • N := by
          rw [Fin.sum_univ_succ, hB, hN]; abel
        rwa [this] at hdet

      set Q : Matrix (Fin 2) (Fin 2) (Polynomial L) :=
        B.map Polynomial.C + (Polynomial.X : Polynomial L) • N.map Polynomial.C with hQ
      set p : Polynomial L := Q.det with hp
      have heval : ∀ t : L, p.eval t = (B + t • N).det := by
        intro t
        rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
        congr 1
        ext i j
        simp [hQ, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
        ring
      have hp0 : p ≠ 0 := by
        intro h0
        apply hdet'
        rw [← heval, h0, Polynomial.eval_zero]
      have hfin : {a : F | p.IsRoot (algebraMap F L a)}.Finite := by
        have := (Polynomial.finite_setOf_isRoot hp0).preimage
          ((algebraMap F L).injective.injOn)
        exact this
      obtain ⟨a, -, ha⟩ := Set.infinite_univ.exists_notMem_finite hfin
      have ha' : (B + algebraMap F L a • N).det ≠ 0 := by
        rw [← heval]
        simpa [Polynomial.IsRoot] using ha

      refine ih (M₀ + algebraMap F L a • N) ?_ (fun j => Ms j.succ) (fun j => hMs j.succ)
        (fun j => c j.succ) ?_
      · rw [map_add, hM₀, Θ_algebraMap_smul, hN, hMs 0]
      · have : M₀ + algebraMap F L a • N + ∑ j : Fin m, c j.succ • Ms j.succ
            = B + algebraMap F L a • N := by rw [hB]; abel
        rwa [this]

end Infinite

end Descent

section Main

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

theorem Θ_iterate_finrank_eq_self {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ₁ δ₂ : GL (Fin 2) L) (c : L)
    (h₁ : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        = c • (1 : Matrix (Fin 2) (Fin 2) L))
    (h₂ : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₂ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        = c • (1 : Matrix (Fin 2) (Fin 2) L))
    (M : Matrix (Fin 2) (Fin 2) L) :
    (Θ σ δ₁ δ₂)^[Module.finrank F L] M = M := by
  rw [Θ_iterate]
  have hσn : (σM σ)^[Module.finrank F L] M = M := by
    ext i j
    rw [σM_iterate_apply, iterate_finrank_apply_of_generator hgen]
  rw [hσn, ← sigmaNormPow_def, ← sigmaNormPow_def, h₁]
  set C := sigmaNormPow (σG σ) (Module.finrank F L) δ₂ with hC
  have hc0 : c ≠ 0 := by
    intro hc
    have hdet := congrArg Matrix.det h₂
    rw [hc, zero_smul, Matrix.det_zero] at hdet
    exact (Matrix.isUnits_det_units C).ne_zero hdet
  have hCinv : ((C⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) L) := by
    have hmul : (C : Matrix (Fin 2) (Fin 2) L) * ((C⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = 1 :=
      C.mul_inv
    rw [h₂, Matrix.smul_mul, Matrix.one_mul] at hmul
    have := congrArg (fun X => c⁻¹ • X) hmul
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    rw [this]
  rw [hCinv, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

theorem sum_basis_smul_avg_dualBasis {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ₁ δ₂ : GL (Fin 2) L)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F L) :
    ∑ i, b i • avg σ δ₁ δ₂ (Module.finrank F L)
        ((Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b i) = 1 := by
  classical
  set n := Module.finrank F L with hn
  set d := (Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b with hd
  simp_rw [avg_eq, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h : ∀ r ∈ Finset.range n,
      ∑ i, (b i * (⇑σ)^[r] (d i)) • (Θ σ δ₁ δ₂)^[r] (1 : Matrix (Fin 2) (Fin 2) L)
        = (if r = 0 then (1 : L) else 0) • (Θ σ δ₁ δ₂)^[r] (1 : Matrix (Fin 2) (Fin 2) L) := by
    intro r hr
    rw [← Finset.sum_smul]
    congr 1
    have := sum_basis_mul_pow_dualBasis hgen b r (Finset.mem_range.mp hr)
    simp_rw [AlgEquiv.coe_pow] at this
    exact this
  rw [Finset.sum_congr rfl h]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos Module.finrank_pos]
  rfl

theorem exists_fixed_isUnit [Infinite F] {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) (δ₁ δ₂ : GL (Fin 2) L) (c : L)
    (h₁ : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₁ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        = c • (1 : Matrix (Fin 2) (Fin 2) L))
    (h₂ : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₂ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        = c • (1 : Matrix (Fin 2) (Fin 2) L)) :
    ∃ M : Matrix (Fin 2) (Fin 2) L, Θ σ δ₁ δ₂ M = M ∧ M.det ≠ 0 := by
  classical
  set n := Module.finrank F L with hn
  let b := Module.finBasis F L
  set d := (Algebra.traceForm F L).dualBasis (traceForm_nondegenerate F L) b with hd
  have hΘn := Θ_iterate_finrank_eq_self hgen δ₁ δ₂ c h₁ h₂
  have hfix : ∀ i, Θ σ δ₁ δ₂ (avg σ δ₁ δ₂ n (d i)) = avg σ δ₁ δ₂ n (d i) :=
    fun i => Θ_avg σ δ₁ δ₂ n hΘn (d i)
  have hone := sum_basis_smul_avg_dualBasis hgen δ₁ δ₂ b
  refine exists_fixed_det_ne_zero σ δ₁ δ₂ (Module.finrank F L) 0 (map_zero _)
    (fun j => avg σ δ₁ δ₂ n (d j)) (fun j => hfix j) (fun j => b j) ?_
  rw [zero_add, hone, Matrix.det_one]
  exact one_ne_zero

theorem isNormRep_of_normClassMap_mk_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) : IsNormRep σ γ δ := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap F L) Q⁻¹, ?_⟩
  rw [← hQ, map_mul, map_mul, map_inv, ← hP]
  group

theorem exists_mk_eq_and_sigmaNormPow_eq {σ : L ≃ₐ[F] L}
    (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ) {δ : GL (Fin 2) L} {γ : GL (Fin 2) F}
    (h : IsNormRep σ γ δ) :
    ∃ δ' : GL (Fin 2) L, SigmaConjClasses.mk σ δ' = SigmaConjClasses.mk σ δ ∧
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ'
        = Matrix.GeneralLinearGroup.map (algebraMap F L) γ := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) P, ?_, ?_⟩
  · symm
    exact SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨P, rfl⟩
  · rw [sigmaNormPow_sigmaConj_generalLinearGroup (n := Fin 2) (σ := (σ : L →+* L))
      (fun a => iterate_finrank_apply_of_generator hgen a) P δ, hP]

theorem sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) F) (hγ : γ ∈ AutomorphicForm.centralCell F)
    (δ₁ δ₂ : GL (Fin 2) L)
    (h₁ : normClassMap hgen (SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : normClassMap hgen (SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    SigmaConjClasses.mk σ δ₁ = SigmaConjClasses.mk σ δ₂ := by
  classical
  obtain ⟨c, hc⟩ := (AutomorphicForm.mem_centralCell_iff.mp hγ)
  obtain ⟨δ₁', h₁', hN₁⟩ := exists_mk_eq_and_sigmaNormPow_eq hgen (isNormRep_of_normClassMap_mk_eq hgen h₁)
  obtain ⟨δ₂', h₂', hN₂⟩ := exists_mk_eq_and_sigmaNormPow_eq hgen (isNormRep_of_normClassMap_mk_eq hgen h₂)
  rw [← h₁', ← h₂']
  have hC : ((Matrix.GeneralLinearGroup.map (algebraMap F L) γ : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) :=
    generalLinearGroup_map_smul_one_coe c γ hc
  have hN₁' : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₁' : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [σG, hN₁, hC]
  have hN₂' : ((sigmaNormPow (σG σ) (Module.finrank F L) δ₂' : GL (Fin 2) L) :
      Matrix (Fin 2) (Fin 2) L) = algebraMap F L c • (1 : Matrix (Fin 2) (Fin 2) L) := by
    rw [σG, hN₂, hC]
  obtain ⟨M, hM, hMdet⟩ := exists_fixed_isUnit hgen δ₁' δ₂' (algebraMap F L c) hN₁' hN₂'

  set h : GL (Fin 2) L := Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet with hh
  refine SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, ?_⟩
  have hM' : (δ₁' : Matrix (Fin 2) (Fin 2) L) * ((σG σ h : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = (h : Matrix (Fin 2) (Fin 2) L) * (δ₂' : Matrix (Fin 2) (Fin 2) L) := by
    have hcoe : (h : Matrix (Fin 2) (Fin 2) L) = M := rfl
    have := hM
    rw [Θ_apply] at this

    have h3 := congrArg (fun X => X * (δ₂' : Matrix (Fin 2) (Fin 2) L)) this
    simp only [Matrix.mul_assoc] at h3
    rw [show ((δ₂'⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (δ₂' : Matrix (Fin 2) (Fin 2) L) = 1
      from δ₂'.inv_mul, Matrix.mul_one] at h3
    rw [← σM_coe, hcoe]
    exact h3

  have hGL : δ₁' * σG σ h = h * δ₂' := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hM')
  rw [σG] at hGL
  rw [mul_assoc, hGL]
  group

end Main

end R2CentralInj

theorem solution
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.centralCell F)
    (δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h₁ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    LT.TwistedNorm.SigmaConjClasses.mk σ δ₁ = LT.TwistedNorm.SigmaConjClasses.mk σ δ₂ :=
  R2CentralInj.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell hgen γ hγ δ₁ δ₂ h₁ h₂

end S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
end P2MW
export P2MW.S_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell (solution)
