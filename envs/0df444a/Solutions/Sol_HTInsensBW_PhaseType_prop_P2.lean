-- Prove2me | solution 1 for HTInsensBW.PhaseType.prop_P2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:56:10.726026+00:00
-- url     : https://prove2.me/submissions/f126f7be-9d62-4c72-96a6-15675ad15b9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct
import Theorems.Thm_HTInsensBW_PhaseType_lemma_6
import Theorems.Thm_HTInsensBW_PhaseType_lemma_11

namespace HTInsensBWP2

open HTInsensBW.PhaseType Matrix Finset

variable {L R : ℕ}

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

/-- block form of `⟨w, (-Sᵀ) v⟩`. -/
lemma inner_block (N : BWNetwork L R) (w v : Idx N → ℝ) :
    mInner N w ((-Sfull N)ᵀ *ᵥ v) =
      ∑ r, (fun k => w ⟨r, k⟩) ⬝ᵥ (Mr N r *ᵥ ((-subgen (N.D r))ᵀ *ᵥ (fun k => v ⟨r, k⟩))) := by
  unfold mInner
  have hS : (-Sfull N)ᵀ = blockDiagonal' (fun r => (-subgen (N.D r))ᵀ) := by
    rw [Sfull, ← blockDiagonal'_neg, blockDiagonal'_transpose]; rfl
  rw [hS]
  simp only [dotProduct]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [Mfull, mulVec_bd]
  congr 2
  funext k'
  rw [mulVec_bd]

lemma msq_block (N : BWNetwork L R) (w : Idx N → ℝ) :
    msq N w = ∑ r, (fun k => w ⟨r, k⟩) ⬝ᵥ (Mr N r *ᵥ (fun k => w ⟨r, k⟩)) := by
  unfold msq mInner
  simp only [dotProduct]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro k _
  rw [Mfull, mulVec_bd]

end HTInsensBWP2

open HTInsensBW.PhaseType HTInsensBWP2 Matrix Finset

theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) (x : (Fin R → ℕ) → Fin R → ℝ) :
    ∃ ηmin : ℝ, 0 < ηmin ∧ ∀ (n : State N) (ℓ : Fin L),
      kappaMin N * ηmin * msq N (bvec N ℓ - bhat N x n ℓ) ≤
        mInner N (bvec N ℓ - bhat N x n ℓ) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) := by
  choose η hη0 hηpsd using lemma_6 N hκ hlam0
  have h11 := lemma_11 N hκ hlam0
  set ηm : ℝ := 1 / (1 + ∑ r, 1 / η r) with hηm
  have hsum0 : 0 ≤ ∑ r, 1 / η r := Finset.sum_nonneg (fun r _ => (one_div_pos.2 (hη0 r)).le)
  have hηm0 : 0 < ηm := by positivity
  have hηmle : ∀ r, ηm ≤ η r := by
    intro r
    have h1 : 1 / η r ≤ ∑ r, 1 / η r :=
      Finset.single_le_sum (f := fun r => 1 / η r) (fun r _ => (one_div_pos.2 (hη0 r)).le)
        (Finset.mem_univ r)
    rw [hηm, div_le_iff₀ (by positivity)]
    have : η r * (1 / η r) = 1 := by field_simp [(hη0 r).ne']
    nlinarith [hη0 r]
  have hkmin0 : 0 ≤ kappaMin N := Real.iInf_nonneg (fun r => (hκ r).le)
  have hkminle : ∀ r, kappaMin N ≤ N.κ r := fun r => ciInf_le (Finite.bddBelow_range _) r
  refine ⟨ηm, hηm0, fun n ℓ => ?_⟩
  set v : Idx N → ℝ := rho0 N - nx N x n with hv
  set c : Fin R → ℝ := fun r => N.H ℓ r / N.κ r with hc
  have hc0 : ∀ r, 0 ≤ c r := fun r => by
    rcases hH01 ℓ r with h | h <;> simp [hc, h, (hκ r).le]
  have hcκ : ∀ r, kappaMin N * c r ≤ 1 := fun r => by
    rcases hH01 ℓ r with h | h
    · simp [hc, h]
    · simp only [hc, h]
      rw [mul_one_div, div_le_one (hκ r)]; exact hkminle r
  have hd : bvec N ℓ - bhat N x n ℓ = fun i => c i.1 * v i := by
    funext i; simp only [Pi.sub_apply, bvec, bhat, hv, hc]; ring
  rw [hd, inner_block, msq_block, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  set vr : Phase (N.D r) → ℝ := fun k => v ⟨r, k⟩ with hvr
  have hw : (fun k => c (⟨r, k⟩ : Idx N).1 * v ⟨r, k⟩) = c r • vr := by
    funext k; simp [hvr]
  rw [hw]
  set M := Mr N r with hM
  set T := (-subgen (N.D r))ᵀ with hT
  have hMpd := (h11.1 r).2
  have hMsym : Mᵀ = M := by
    have := hMpd.isHermitian
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hq0 : 0 ≤ vr ⬝ᵥ (M *ᵥ vr) := by
    have := hMpd.posSemidef.dotProduct_mulVec_nonneg vr
    simpa using this
  -- key: vᵀ M (-Sᵀ) v ≥ η vᵀ M v
  have hkey : η r * (vr ⬝ᵥ (M *ᵥ vr)) ≤ vr ⬝ᵥ (M *ᵥ (T *ᵥ vr)) := by
    have hp := (hηpsd r).dotProduct_mulVec_nonneg vr
    simp only [star_trivial] at hp
    rw [sub_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, dotProduct_sub,
      dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul] at hp
    have e1 : vr ⬝ᵥ ((M * (-subgen (N.D r))ᵀ) *ᵥ vr) = vr ⬝ᵥ (M *ᵥ (T *ᵥ vr)) := by
      rw [mulVec_mulVec]
    have e2 : vr ⬝ᵥ (((-subgen (N.D r)) * M) *ᵥ vr) = vr ⬝ᵥ (M *ᵥ (T *ᵥ vr)) := by
      calc vr ⬝ᵥ (((-subgen (N.D r)) * M) *ᵥ vr) = (T *ᵥ vr) ⬝ᵥ (M *ᵥ vr) := by
            rw [← mulVec_mulVec, dotProduct_mulVec, hT, mulVec_transpose]
        _ = (M *ᵥ vr) ⬝ᵥ (T *ᵥ vr) := dotProduct_comm _ _
        _ = (vr ᵥ* Mᵀ) ⬝ᵥ (T *ᵥ vr) := by rw [vecMul_transpose]
        _ = vr ⬝ᵥ (Mᵀ *ᵥ (T *ᵥ vr)) := (dotProduct_mulVec _ _ _).symm
        _ = _ := by rw [hMsym]
    rw [e1, e2] at hp
    linarith
  have hlhs : (c r • vr) ⬝ᵥ (M *ᵥ (T *ᵥ vr)) = c r * (vr ⬝ᵥ (M *ᵥ (T *ᵥ vr))) := by
    rw [smul_dotProduct, smul_eq_mul]
  have hrhs : (c r • vr) ⬝ᵥ (M *ᵥ (c r • vr)) = c r * c r * (vr ⬝ᵥ (M *ᵥ vr)) := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
  rw [hlhs, hrhs]
  have h1 : kappaMin N * ηm * (c r * c r * (vr ⬝ᵥ (M *ᵥ vr))) ≤
      ηm * c r * (vr ⬝ᵥ (M *ᵥ vr)) := by
    have := hcκ r
    have hcr := hc0 r
    have : kappaMin N * ηm * (c r * c r * (vr ⬝ᵥ (M *ᵥ vr))) =
        (kappaMin N * c r) * (ηm * c r * (vr ⬝ᵥ (M *ᵥ vr))) := by ring
    rw [this]
    have hnn : 0 ≤ ηm * c r * (vr ⬝ᵥ (M *ᵥ vr)) := by positivity
    nlinarith
  have h2 : ηm * c r * (vr ⬝ᵥ (M *ᵥ vr)) ≤ c r * (η r * (vr ⬝ᵥ (M *ᵥ vr))) := by
    have := hηmle r
    have hcr := hc0 r
    have : ηm * (c r * (vr ⬝ᵥ (M *ᵥ vr))) ≤ η r * (c r * (vr ⬝ᵥ (M *ᵥ vr))) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  have h3 : c r * (η r * (vr ⬝ᵥ (M *ᵥ vr))) ≤ c r * (vr ⬝ᵥ (M *ᵥ (T *ᵥ vr))) :=
    mul_le_mul_of_nonneg_left hkey (hc0 r)
  linarith
