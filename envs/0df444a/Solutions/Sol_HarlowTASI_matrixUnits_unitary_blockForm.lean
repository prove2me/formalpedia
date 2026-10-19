-- Prove2me | solution 1 for HarlowTASI.matrixUnits_unitary_blockForm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:40:33.439499+00:00
-- url     : https://prove2.me/submissions/237163ac-7f94-4953-917b-26206ede35c2

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix

namespace HTAux

variable {C : Type} [Fintype C] [DecidableEq C]

theorem proj_frame (P : Matrix C C ℂ) (hP : P * P = P) (hH : Pᴴ = P) (hne : P ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ φ : Fin r → C → ℂ,
      (∀ k l, star (φ k) ⬝ᵥ φ l = if k = l then 1 else 0) ∧
      (∀ k, P *ᵥ φ k = φ k) ∧
      ∑ k, vecMulVec (φ k) (star (φ k)) = P := by
  let W : Submodule ℂ (EuclideanSpace ℂ C) := LinearMap.range (Matrix.toEuclideanLin P)
  let b := stdOrthonormalBasis ℂ W
  let φ : Fin (Module.finrank ℂ W) → C → ℂ := fun k => ((b k : W) : EuclideanSpace ℂ C).ofLp
  have hPφ : ∀ k, P *ᵥ φ k = φ k := by
    intro k
    obtain ⟨v, hv⟩ := (b k).2
    have : φ k = P *ᵥ v.ofLp := by
      simp only [φ, ← hv, Matrix.toEuclideanLin_apply]
    rw [this, Matrix.mulVec_mulVec, hP]
  have hinner : ∀ (k : Fin (Module.finrank ℂ W)) (y : C → ℂ),
      inner ℂ ((b k : W) : EuclideanSpace ℂ C) (WithLp.toLp 2 y) = star (φ k) ⬝ᵥ y := by
    intro k y
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hS : ∑ k, vecMulVec (φ k) (star (φ k)) = P := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    simp only [Matrix.toLin'_apply]
    have hy : P *ᵥ y = ∑ k, (star (φ k) ⬝ᵥ y) • φ k := by
      have hmem : (WithLp.toLp 2 (P *ᵥ y) : EuclideanSpace ℂ C) ∈ W :=
        ⟨WithLp.toLp 2 y, by simp [Matrix.toEuclideanLin_apply]⟩
      have := b.sum_repr' ⟨_, hmem⟩
      have h2 := congrArg (fun w : W => ((w : EuclideanSpace ℂ C)).ofLp) this
      simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Submodule.coe_inner] at h2
      rw [← h2]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1
      rw [hinner]
      rw [Matrix.dotProduct_mulVec]
      have : star (φ k) ᵥ* P = star (φ k) := by
        have h := congrArg star (hPφ k)
        rw [Matrix.star_mulVec, hH] at h
        exact h
      rw [this]
    rw [hy, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ext c
    simp [Matrix.mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  refine ⟨Module.finrank ℂ W, ?_, φ, ?_, hPφ, hS⟩
  · rw [Module.finrank_pos_iff_exists_ne_zero]
    by_contra hcon
    push Not at hcon
    apply hne
    ext i j
    have hmem : (WithLp.toLp 2 (P *ᵥ Pi.single j 1) : EuclideanSpace ℂ C) ∈ W :=
      ⟨WithLp.toLp 2 (Pi.single j 1), by simp [Matrix.toEuclideanLin_apply]⟩
    have h0 := congrArg (fun w : W => ((w : EuclideanSpace ℂ C)).ofLp i) (hcon ⟨_, hmem⟩)
    simpa [Matrix.mulVec_single] using h0
  · intro k l
    have := b.orthonormal
    rw [orthonormal_iff_ite] at this
    have h := this k l
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm]
    exact h

end HTAux

open Matrix
open scoped Kronecker

namespace HTAux

variable {C : Type} [Fintype C] [DecidableEq C]

theorem vmv_mulVec (A B : Matrix C C ℂ) (u : C → ℂ) :
    vecMulVec (A *ᵥ u) (star (B *ᵥ u)) = A * vecMulVec u (star u) * Bᴴ := by
  ext c d
  simp only [vecMulVec_apply, mul_apply, mulVec, dotProduct, Pi.star_apply, star_sum, star_mul',
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  ring

theorem mul_blockDiag {N : ℕ} {ι : Fin N → Type} [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (V : Matrix C (Σ a, ι a) ℂ) (F : ∀ a, Matrix (ι a) (ι a) ℂ) (c : C) (b : Fin N) (t : ι b) :
    (V * blockDiagonal' F) c ⟨b, t⟩ = ∑ s, V c ⟨b, s⟩ * F b s t := by
  rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [blockDiagonal'_apply_eq]
  · intro a _ hab
    refine Finset.sum_eq_zero (fun s _ => ?_)
    rw [blockDiagonal'_apply_ne _ _ _ hab, mul_zero]
  · intro h; exact absurd (Finset.mem_univ b) h


open HarlowTASI in
theorem main {N : ℕ} (dr : Fin N → ℕ) (e : (a : Fin N) → Fin (dr a) → Fin (dr a) → Matrix C C ℂ)
    (hmul : ∀ a i j k l, e a i j * e a k l = if j = k then e a i l else 0)
    (horth : ∀ a b i j k l, a ≠ b → e a i j * e b k l = 0)
    (hstar : ∀ a i j, (e a i j)ᴴ = e a j i)
    (hne : ∀ a i, e a i i ≠ 0)
    (hsum : ∑ a, ∑ i, e a i i = 1) :
    ∃ (drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ),
      IsUnitaryMatrix U ∧ (∀ a, 0 < drb a) ∧
      ∀ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
        Uᴴ * blockLeftOp (drb := drb) x * U = ∑ a, ∑ i, ∑ j, x a i j • e a i j := by
  classical
  have hex : ∀ a, ∃ r : ℕ, 0 < r ∧ ∃ φ : Fin r → C → ℂ, ∀ h : 0 < dr a,
      (∀ k l, star (φ k) ⬝ᵥ φ l = if k = l then 1 else 0) ∧
      (∀ k, e a ⟨0, h⟩ ⟨0, h⟩ *ᵥ φ k = φ k) ∧
      ∑ k, vecMulVec (φ k) (star (φ k)) = e a ⟨0, h⟩ ⟨0, h⟩ := by
    intro a
    by_cases h : 0 < dr a
    · have hP : e a ⟨0, h⟩ ⟨0, h⟩ * e a ⟨0, h⟩ ⟨0, h⟩ = e a ⟨0, h⟩ ⟨0, h⟩ := by
        rw [hmul, if_pos rfl]
      obtain ⟨r, hr, φ, h1, h2, h3⟩ := proj_frame _ hP (hstar _ _ _) (hne _ _)
      exact ⟨r, hr, φ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, one_pos, 0, fun h' => absurd h' h⟩
  choose r hr φ hφ using hex
  let v : (a : Fin N) → Fin (dr a) → Fin (r a) → C → ℂ :=
    fun a i k => e a i ⟨0, i.pos⟩ *ᵥ φ a k
  let V : Matrix C (BlockIndex N dr r) ℂ := fun c p => v p.1 p.2.1 p.2.2 c
  have hLv : ∀ a (i j : Fin (dr a)),
      ∑ l, vecMulVec (v a i l) (star (v a j l)) = e a i j := by
    intro a i j
    simp only [v, vmv_mulVec]
    rw [← Finset.sum_mul, ← Finset.mul_sum, (hφ a i.pos).2.2, hstar, hmul, if_pos rfl, hmul,
      if_pos rfl]
  have hmain : ∀ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
      V * blockLeftOp (drb := r) x * Vᴴ = ∑ a, ∑ i, ∑ j, x a i j • e a i j := by
    intro x
    ext c d
    rw [mul_apply, Fintype.sum_sigma]
    simp only [blockLeftOp, mul_blockDiag, Fintype.sum_prod_type, kroneckerMap_apply,
      one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, conjTranspose_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hR : ∀ i j, x a i j * e a i j c d =
        ∑ l, x a i j * (V c ⟨a, (i, l)⟩ * star (V d ⟨a, (j, l)⟩)) := by
      intro i j
      rw [← hLv, Matrix.sum_apply, Finset.mul_sum]
      simp [V, vecMulVec_apply]
    simp_rw [hR, Finset.sum_mul]
    conv_lhs => enter [2, j]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun l _ => ?_)))
    ring
  refine ⟨r, Vᴴ, ⟨?_, ?_⟩, hr, ?_⟩
  · rw [conjTranspose_conjTranspose]
    have h1 : blockLeftOp (drb := r) (fun a => (1 : Matrix (Fin (dr a)) (Fin (dr a)) ℂ)) = 1 := by
      simp only [blockLeftOp, one_kronecker_one]
      exact blockDiagonal'_one
    have := hmain (fun a => 1)
    rw [h1, Matrix.mul_one] at this
    rw [this, ← hsum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [one_apply_ne (Ne.symm hji)]
    · simp
  · rw [conjTranspose_conjTranspose]
    ext ⟨a, i, k⟩ ⟨b, j, l⟩
    rw [mul_apply]
    have hdot : ∑ c, Vᴴ ⟨a, i, k⟩ c * V c ⟨b, j, l⟩ = star (v a i k) ⬝ᵥ v b j l := by
      simp only [conjTranspose_apply, dotProduct]
      rfl
    rw [hdot]
    simp only [v]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hstar]
    by_cases hab : a = b
    · subst hab
      rw [hmul]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, (hφ a i.pos).2.1, (hφ a i.pos).1]
        by_cases hkl : k = l
        · subst hkl; simp
        · rw [if_neg hkl, one_apply_ne]
          intro h
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
          first | exact hkl h | exact hkl h.2
      · rw [if_neg hij, zero_mulVec, dotProduct_zero, one_apply_ne]
        intro h
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
        exact hij h.1
    · rw [horth _ _ _ _ _ _ hab, zero_mulVec, dotProduct_zero, one_apply_ne]
      intro h
      exact hab (congrArg Sigma.fst h)
  · intro x
    rw [conjTranspose_conjTranspose]
    exact hmain x

end HTAux

open HarlowTASI in
theorem solution {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} (dr : Fin N → ℕ) (e : (a : Fin N) → Fin (dr a) → Fin (dr a) → Matrix C C ℂ)
    (hmul : ∀ a i j k l, e a i j * e a k l = if j = k then e a i l else 0)
    (horth : ∀ a b i j k l, a ≠ b → e a i j * e b k l = 0)
    (hstar : ∀ a i j, (e a i j)ᴴ = e a j i)
    (hne : ∀ a i, e a i i ≠ 0)
    (hsum : ∑ a, ∑ i, e a i i = 1) :
    ∃ (drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ),
      IsUnitaryMatrix U ∧ (∀ a, 0 < drb a) ∧
      ∀ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
        Uᴴ * blockLeftOp (drb := drb) x * U = ∑ a, ∑ i, ∑ j, x a i j • e a i j :=
  HTAux.main dr e hmul horth hstar hne hsum
