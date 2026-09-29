-- Prove2me | solution 1 for MarkovEntanglement.separable_implies_value_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:36:38.82052+00:00
-- url     : https://prove2.me/submissions/3d897ee9-4cc1-4e84-8126-b27dffd2a29d

import Definitions.Def_markov_entanglement_multi
import Theorems.Thm_MarkovEntanglement_separable_apply_local_reward

open scoped BigOperators
open MarkovEntanglement

/-- A vector fixed by `γ P` with `P` stochastic and `γ < 1` is zero. -/
private theorem eq_zero_of_eq_gamma_smul {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (d : ι → ℝ)
    (hd : ∀ p, d p = γ * ∑ q, P p q * d q) : d = 0 := by
  classical
  funext p
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact (hι.false p).elim
  obtain ⟨p0, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun p => |d p|)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hstep : |d p0| ≤ γ * |d p0| := by
    calc |d p0| = |γ * ∑ q, P p0 q * d q| := by rw [← hd p0]
      _ = γ * |∑ q, P p0 q * d q| := by rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ γ * ∑ q, |P p0 q * d q| := by
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hγ
      _ = γ * ∑ q, P p0 q * |d q| := by
          congr 1
          exact Finset.sum_congr rfl (fun q _ => by
            rw [abs_mul, abs_of_nonneg (hP.1 p0 q)])
      _ ≤ γ * ∑ q, P p0 q * |d p0| := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => ?_)) hγ
          exact mul_le_mul_of_nonneg_left (hmax q (Finset.mem_univ q)) (hP.1 p0 q)
      _ = γ * |d p0| := by rw [← Finset.sum_mul, hP.2 p0, one_mul]
  have h0 : |d p0| = 0 := by
    nlinarith [abs_nonneg (d p0)]
  have : |d p| ≤ 0 := by
    rw [← h0]; exact hmax p (Finset.mem_univ p)
  simpa using abs_nonpos_iff.mp this

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P) (hsep : IsSeparableN P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q) :
    ∃ Qi : ∀ i, S i → ℝ, IsValueDecomposition Q Qi := by
  classical
  obtain ⟨Kn, x, Pj, hPj, hx, hPeq⟩ := hsep
  -- the linear map sending local values to their sum
  let Phi : (∀ i, S i → ℝ) →ₗ[ℝ] (Joint S → ℝ) :=
    { toFun := fun h => fun p => ∑ i, h i (p i)
      map_add' := by intro a b; funext p; simp [Finset.sum_add_distrib]
      map_smul' := by intro c a; funext p; simp [Finset.mul_sum] }
  let L : (Joint S → ℝ) →ₗ[ℝ] (Joint S → ℝ) := LinearMap.id - γ • P.mulVecLin
  have hLapply : ∀ (v : Joint S → ℝ) (p : Joint S),
      L v p = v p - γ * ∑ q, P p q * v q := by
    intro v p
    simp [L, Matrix.mulVec, dotProduct]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine eq_zero_of_eq_gamma_smul P hP γ hγ hγ1 v (fun p => ?_)
    have := congrFun hv p
    rw [hLapply] at this
    simp only [Pi.zero_apply] at this
    linarith
  -- `P` maps decomposable functions to decomposable functions
  have hPD : ∀ h : ∀ i, S i → ℝ, ∃ h' : ∀ i, S i → ℝ,
      P.mulVecLin (Phi h) = Phi h' := by
    intro h
    refine ⟨fun i s => ∑ k, x k * ∑ t : S i, Pj k i s t * h i t, ?_⟩
    funext p
    show ∑ q, P p q * (∑ i, h i (q i)) = ∑ i, ∑ k, x k * ∑ t : S i, Pj k i (p i) t * h i t
    calc ∑ q : Joint S, P p q * (∑ i, h i (q i))
        = ∑ i, ∑ q : Joint S, P p q * h i (q i) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun q _ => Finset.mul_sum _ _ _)
      _ = ∑ i, ∑ k, x k * ∑ t : S i, Pj k i (p i) t * h i t := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show (fun q : Joint S => P p q * h i (q i))
                = (fun q : Joint S => (∑ k, x k • tensorProdN (Pj k)) p q * h i (q i)) from
              by rw [hPeq]]
          exact MarkovEntanglement.separable_apply_local_reward x Pj hPj hx i (h i) p
  set D : Submodule ℝ (Joint S → ℝ) := LinearMap.range Phi with hD
  have hLD : ∀ v ∈ D, L v ∈ D := by
    rintro v ⟨h, rfl⟩
    obtain ⟨h', hh'⟩ := hPD h
    refine ⟨h - γ • h', ?_⟩
    have : L (Phi h) = Phi h - γ • Phi h' := by
      simp [L, hh']
    rw [this, map_sub, map_smul]
  have hsurj : Function.Surjective (L.restrict hLD) := by
    rw [← LinearMap.injective_iff_surjective]
    intro a b hab
    apply Subtype.ext
    apply hLinj
    have := congrArg (fun w : D => (w : Joint S → ℝ)) hab
    simpa [LinearMap.restrict_apply] using this
  obtain ⟨Q', hQ'⟩ := hsurj ⟨Phi r, ⟨r, rfl⟩⟩
  have hQ'eq : L (Q' : Joint S → ℝ) = Phi r := congrArg Subtype.val hQ'
  have hQeq : L Q = Phi r := by
    funext p
    rw [hLapply]
    have := hQ p
    show Q p - γ * ∑ q, P p q * Q q = ∑ i, r i (p i)
    linarith [hQ p]
  have : Q = (Q' : Joint S → ℝ) := hLinj (by rw [hQeq, hQ'eq])
  obtain ⟨h, hh⟩ := Q'.2
  exact ⟨h, fun p => by rw [this, ← hh]; rfl⟩
