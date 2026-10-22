-- Prove2me | solution 1 for HTInsensBW.PhaseType.prop_P1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:51:15.110918+00:00
-- url     : https://prove2.me/submissions/c2cb2940-0db1-4fbb-92b5-f519befcaeb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct
import Theorems.Thm_HTInsensBW_PhaseType_lemma_5

namespace HTInsensBWP1

open HTInsensBW.PhaseType Matrix Finset

variable {L R : ℕ}

lemma vecMul_bd {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (A : ∀ i, Matrix (m i) (m i) ℝ) (b : (Σ i, m i) → ℝ) (r : ι) (k : m r) :
    (b ᵥ* blockDiagonal' A) ⟨r, k⟩ = ((fun k' => b ⟨r, k'⟩) ᵥ* A r) k := by
  simp only [vecMul, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro k' _
    rw [blockDiagonal'_apply_eq]
  · intro r' _ hne
    apply Finset.sum_eq_zero
    intro k' _
    rw [blockDiagonal'_apply_ne _ _ _ hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ r) h

lemma mulVec_bd {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → Type*} [∀ i, Fintype (m i)]
    (A : ∀ i, Matrix (m i) (m i) ℝ) (w : (Σ i, m i) → ℝ) (r : ι) (k : m r) :
    (blockDiagonal' A *ᵥ w) ⟨r, k⟩ = (A r *ᵥ (fun k' => w ⟨r, k'⟩)) k := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single r]
  · apply Finset.sum_congr rfl
    intro k' _
    rw [blockDiagonal'_apply_eq]
  · intro r' _ hne
    apply Finset.sum_eq_zero
    intro k' _
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hne), zero_mul]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- `⟨b^(ℓ), (-Sᵀ) v⟩ = Σ_r h_ℓr Σ_k v_{r,k}` (consequence of Lemma 5). -/
lemma inner_b (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (ℓ : Fin L) (v : Idx N → ℝ) :
    mInner N (bvec N ℓ) ((-Sfull N)ᵀ *ᵥ v) = ∑ r, N.H ℓ r * ∑ k, v ⟨r, k⟩ := by
  have h5 := lemma_5 N hκ hlam0
  unfold mInner
  rw [dotProduct_mulVec, dotProduct_mulVec, vecMul_transpose]
  have key : ∀ (r : Fin R) (k : Phase (N.D r)),
      ((-Sfull N) *ᵥ (bvec N ℓ ᵥ* Mfull N)) ⟨r, k⟩ = N.H ℓ r := by
    intro r k
    have e1 : (-Sfull N) *ᵥ (bvec N ℓ ᵥ* Mfull N) = -(Sfull N *ᵥ (bvec N ℓ ᵥ* Mfull N)) := by
      rw [Matrix.neg_mulVec]
    rw [e1, Pi.neg_apply, Sfull, mulVec_bd]
    have e2 : (fun k' => (bvec N ℓ ᵥ* Mfull N) ⟨r, k'⟩) =
        (N.H ℓ r / N.κ r) • (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r) := by
      funext k'
      rw [Mfull, vecMul_bd]
      simp only [vecMul, dotProduct, bvec, rho0, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e2]
    have h := congrFun (h5 r) k
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [← Matrix.vecMul_vecMul, vecMul_transpose] at h
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e3 : (-(subgen (N.D r) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k) =
        ((-subgen (N.D r)) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k := by
      rw [Matrix.neg_mulVec]; rfl
    have hk := (hκ r).ne'
    calc -(N.H ℓ r / N.κ r * (subgen (N.D r) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k)
        = N.H ℓ r * (1 / N.κ r * ((-subgen (N.D r)) *ᵥ (phaseLoad (N.D r) (N.lam0 r) ᵥ* Mr N r)) k) := by
          rw [← e3]; ring
      _ = N.H ℓ r := by rw [h, mul_one]
  simp only [dotProduct]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [key r k]

lemma sum_phaseLoad (N : BWNetwork L R) (r : Fin R) :
    ∑ k, rho0 N ⟨r, k⟩ = routeLoad0 N r := by
  simp only [rho0, phaseLoad, routeLoad0, meanSize, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  congr 1
  rw [dotProduct_mulVec]
  simp [dotProduct]

end HTInsensBWP1

open HTInsensBW.PhaseType HTInsensBWP1 Matrix

theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) (x : (Fin R → ℕ) → Fin R → ℝ) :
    ∀ (n : State N) (ℓ : Fin L),
      mInner N (bvec N ℓ) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) = unused N x n ℓ - slack N ℓ := by
  intro n ℓ
  rw [inner_b N hκ hlam0]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_phaseLoad, mul_sub, unused, slack]
  have e : ∀ r, ∑ k, nx N x n ⟨r, k⟩ = (routeCount N n r : ℝ) * x (routeCount N n) r := by
    intro r
    simp only [nx, routeCount, Nat.cast_sum, Finset.sum_mul]
  simp only [e]
  have e2 : ∀ r, N.H ℓ r * ((routeCount N n r : ℝ) * x (routeCount N n) r) =
      N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r := fun r => by ring
  simp only [e2]
  ring
