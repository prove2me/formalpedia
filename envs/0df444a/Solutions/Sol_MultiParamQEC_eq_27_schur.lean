-- Prove2me | solution 1 for MultiParamQEC.eq_27_schur
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:56:19.179996+00:00
-- url     : https://prove2.me/submissions/817ea51c-405e-4399-a328-63d16c3f2e5a

import Mathlib

open scoped Matrix

theorem solution {P : ℕ} (K M : Matrix (Fin P) (Fin P) ℝ) :
    (Matrix.fromBlocks K 1 1 M).PosSemidef ↔ M.PosDef ∧ (K - M⁻¹).PosSemidef := by
  constructor
  · intro h
    have hQ : ∀ x y : Fin P → ℝ,
        0 ≤ ∑ i, x i * (K *ᵥ x) i + 2 * ∑ i, x i * y i + ∑ i, y i * (M *ᵥ y) i := by
      intro x y
      have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 (Sum.elim x y)
      rw [Matrix.fromBlocks_mulVec] at this
      simp only [star_trivial, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Pi.add_apply, Function.comp_def, Matrix.one_mulVec, mul_add,
        Finset.sum_add_distrib] at this
      have hc : ∑ i, y i * x i = ∑ i, x i * y i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      linarith
    have hMh : M.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp h.1).2.2.2
    have hKpsd : ∀ x : Fin P → ℝ, 0 ≤ ∑ i, x i * (K *ᵥ x) i := by
      intro x
      have := hQ x 0
      simpa using this
    have hMpd : M.PosDef := by
      refine Matrix.PosDef.of_dotProduct_mulVec_pos hMh (fun v hv => ?_)
      rw [star_trivial]
      show 0 < ∑ i, v i * (M *ᵥ v) i
      have hc0 : 0 ≤ ∑ i, v i * (M *ᵥ v) i := by
        have := hQ 0 v
        simpa using this
      by_contra hc
      push_neg at hc
      have hc' : ∑ i, v i * (M *ᵥ v) i = 0 := le_antisymm hc hc0
      have hb : 0 < ∑ i, v i * v i := by
        have hnn : 0 ≤ ∑ i, v i * v i := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
        rcases eq_or_lt_of_le hnn with h0 | h0
        · exact absurd (dotProduct_self_eq_zero.mp h0.symm) hv
        · exact h0
      obtain ⟨a, ha⟩ : ∃ a, a = ∑ i, v i * (K *ᵥ v) i := ⟨_, rfl⟩
      obtain ⟨b, hbd⟩ : ∃ b, b = ∑ i, v i * v i := ⟨_, rfl⟩
      have ha0 : 0 ≤ a := by rw [ha]; exact hKpsd v
      have hq := hQ ((-(b / (a + 1))) • v) v
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at hq
      have e1 : ∑ i, -(b / (a + 1)) * v i * (-(b / (a + 1)) * (K *ᵥ v) i) =
          (b / (a + 1)) ^ 2 * a := by
        rw [ha, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -(b / (a + 1)) * v i * v i = -(b / (a + 1)) * b := by
        rw [hbd, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2, hc'] at hq
      rw [← hbd] at hb
      have ht : 0 < b / (a + 1) := div_pos hb (by linarith)
      have htd : b / (a + 1) * (a + 1) = b := div_mul_cancel₀ _ (by linarith)
      nlinarith
    refine ⟨hMpd, ?_⟩
    haveI := hMpd.isUnit.invertible
    have h' := (Matrix.PosDef.fromBlocks₂₂ K (1 : Matrix (Fin P) (Fin P) ℝ) hMpd).mp
      (by rw [Matrix.conjTranspose_one]; exact h)
    simpa using h'
  · rintro ⟨hM, hK⟩
    haveI := hM.isUnit.invertible
    have h' := (Matrix.PosDef.fromBlocks₂₂ K (1 : Matrix (Fin P) (Fin P) ℝ) hM).mpr
      (by simpa using hK)
    rwa [Matrix.conjTranspose_one] at h'
