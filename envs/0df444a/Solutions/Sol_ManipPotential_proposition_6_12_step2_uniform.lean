-- Prove2me | solution 1 for ManipPotential.proposition_6_12_step2_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:03:56.359053+00:00
-- url     : https://prove2.me/submissions/f7a18321-ae7b-4821-945a-d7a47878ad09

import Mathlib
import Definitions.Def_ManipPotential_TransferVectors
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

open ManipPotential

/-- Proposition 6.12, Step 2, uniform formulation. -/
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (lam : ℝ) (T : Submodule ℝ (Ranking m → ℝ))
    (hTfin : Module.finrank ℝ T = m.factorial - m + 1)
    (M : Fin m → Fin m → Set (Ranking m → ℝ))
    (hMc : ∀ i j, IsClosed (M i j)) (hMx : ∀ i j, Convex ℝ (M i j))
    (hM0 : ∀ i j, 0 ∈ M i j)
    (hMs : ∀ i j ⦃a : ℝ⦄, 0 ≤ a → ∀ ⦃x : Ranking m → ℝ⦄, x ∈ M i j → a • x ∈ M i j)
    (hTM : ∀ i j, (T : Set (Ranking m → ℝ)) ⊆ M i j)
    (hUM : ∀ i j, TransferVectors lam i j ⊆ M i j)
    (hV : ∀ i j, i ≠ j → -(unitVec (ell i) - unitVec (ell j)) ∉ M i j) :
    ∃ W : Submodule ℝ (Ranking m → ℝ), Module.finrank ℝ W = m - 1 ∧
      ∀ i j : Fin m, i ≠ j → ∃ w ∈ W, w ∈ Cmp lam i j ∧
        dotProduct w (unitVec (ell i) - unitVec (ell j)) = 1 := by
  let e : EuclideanSpace ℝ (Ranking m) ≃ₗ[ℝ] (Ranking m → ℝ) :=
    WithLp.linearEquiv 2 ℝ (Ranking m → ℝ)
  let TE : Submodule ℝ (EuclideanSpace ℝ (Ranking m)) := T.map e.symm.toLinearMap
  let WE : Submodule ℝ (EuclideanSpace ℝ (Ranking m)) := TE.orthogonal
  have hfinE : Module.finrank ℝ (EuclideanSpace ℝ (Ranking m)) = m.factorial := by
    rw [e.finrank_eq, Module.finrank_pi, Fintype.card_perm, Fintype.card_fin]
  have hTEfin : Module.finrank ℝ TE = m.factorial - m + 1 := by
    dsimp [TE]
    rw [LinearEquiv.finrank_map_eq]
    exact hTfin
  have hWEfin : Module.finrank ℝ WE = m - 1 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal TE
    rw [hTEfin, hfinE] at hsum
    change Module.finrank ℝ TE.orthogonal = m - 1
    have hf := Nat.self_le_factorial m
    omega
  refine ⟨WE.map e.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hWEfin
  · intro i j hij
    let V : Ranking m → ℝ := unitVec (ell i) - unitVec (ell j)
    let ME : Set (EuclideanSpace ℝ (Ranking m)) := e ⁻¹' M i j
    have hME0 : (0 : EuclideanSpace ℝ (Ranking m)) ∈ ME := by
      change e 0 ∈ M i j
      simpa using hM0 i j
    have hMEclosed : IsClosed ME := by
      exact (hMc i j).preimage (LinearMap.continuous_of_finiteDimensional e.toLinearMap)
    have hMEconvex : Convex ℝ ME := (hMx i j).linear_preimage e.toLinearMap
    let u : EuclideanSpace ℝ (Ranking m) := e.symm (-V)
    obtain ⟨p, hpM, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex
      ⟨0, hME0⟩ hMEclosed.isComplete hMEconvex u
    let w0 : EuclideanSpace ℝ (Ranking m) := p - u
    have hvar : ∀ x ∈ ME, 0 ≤ inner ℝ w0 (x - p) := by
      intro x hx
      have h := (norm_eq_iInf_iff_real_inner_le_zero hMEconvex hpM).mp hpmin x hx
      have hw0eq : w0 = -(u - p) := by
        dsimp [w0]
        abel
      rw [hw0eq, inner_neg_left]
      exact neg_nonneg.mpr h
    have hp2 : (2 : ℝ) • p ∈ ME := by
      change e ((2 : ℝ) • p) ∈ M i j
      rw [map_smul]
      exact hMs i j (by norm_num) hpM
    have hp_le : inner ℝ w0 p ≤ 0 := by
      have h := hvar 0 hME0
      simpa only [zero_sub, inner_neg_right, neg_nonneg] using h
    have hp_ge : 0 ≤ inner ℝ w0 p := by
      have h := hvar ((2 : ℝ) • p) hp2
      have heq : (2 : ℝ) • p - p = p := by module
      rwa [heq] at h
    have hp0 : inner ℝ w0 p = 0 := le_antisymm hp_le hp_ge
    have hwnonneg : ∀ x ∈ ME, 0 ≤ inner ℝ w0 x := by
      intro x hx
      have h := hvar x hx
      rwa [inner_sub_right, hp0, sub_zero] at h
    have hw0 : w0 ≠ 0 := by
      intro hw
      apply hV i j hij
      have hpu : p = u := by
        apply sub_eq_zero.mp
        exact hw
      have huM : u ∈ ME := by rwa [← hpu]
      change e u ∈ M i j at huM
      simpa [u, V] using huM
    have hVw : e.symm V = w0 - p := by
      dsimp [w0, u]
      simp only [map_neg, LinearEquiv.apply_symm_apply]
      abel
    have hpos : 0 < inner ℝ w0 (e.symm V) := by
      rw [hVw, inner_sub_right, hp0, sub_zero, real_inner_self_eq_norm_sq]
      exact sq_pos_of_pos (norm_pos_iff.mpr hw0)
    have hw0W : w0 ∈ WE := by
      change w0 ∈ TE.orthogonal
      rw [Submodule.mem_orthogonal']
      intro t ht
      rcases ht with ⟨t0, ht0, rfl⟩
      have htME : e.symm t0 ∈ ME := by
        change e (e.symm t0) ∈ M i j
        simpa using hTM i j ht0
      have hntME : -e.symm t0 ∈ ME := by
        change e (-e.symm t0) ∈ M i j
        rw [map_neg]
        simpa using hTM i j (T.neg_mem ht0)
      have h1 := hwnonneg (e.symm t0) htME
      have h2 := hwnonneg (-e.symm t0) hntME
      rw [inner_neg_right] at h2
      exact le_antisymm (neg_nonneg.mp h2) h1
    have hw0Wraw : e w0 ∈ WE.map e.toLinearMap := by
      rw [Submodule.mem_map]
      exact ⟨w0, hw0W, rfl⟩
    have inner_eq_dot (x y : EuclideanSpace ℝ (Ranking m)) :
        inner ℝ x y = dotProduct (e x) (e y) := by
      simp [PiLp.inner_apply, dotProduct, e, WithLp.linearEquiv, RCLike.inner_apply,
        mul_comm]
    have hdot : dotProduct (e w0) V = inner ℝ w0 (e.symm V) := by
      rw [inner_eq_dot]
      simp
    have hnonneg_transfer : ∀ v ∈ TransferVectors lam i j, 0 ≤ dotProduct (e w0) v := by
      intro v hv
      have hvM : v ∈ M i j := hUM i j hv
      have hvME : e.symm v ∈ ME := by
        change e (e.symm v) ∈ M i j
        simpa using hvM
      have h := hwnonneg (e.symm v) hvME
      rw [inner_eq_dot] at h
      simpa using h
    have hw0Cmp : e w0 ∈ Cmp lam i j := by
      constructor
      · intro r s hrs
        have h := hnonneg_transfer (lam • unitVec r - unitVec s)
          (Or.inl ⟨r, s, hrs, rfl⟩)
        simp only [dotProduct_sub, dotProduct_smul, unitVec, dotProduct_single,
          smul_eq_mul, mul_one] at h
        linarith
      · intro r s hrs
        have h := hnonneg_transfer (unitVec s - lam • unitVec r)
          (Or.inr ⟨r, s, hrs, rfl⟩)
        simp only [dotProduct_sub, dotProduct_smul, unitVec, dotProduct_single,
          smul_eq_mul, mul_one] at h
        linarith
    let c : ℝ := inner ℝ w0 (e.symm V)
    have hc : 0 < c := hpos
    let w : Ranking m → ℝ := c⁻¹ • e w0
    refine ⟨w, ?_, ?_, ?_⟩
    · exact (WE.map e.toLinearMap).smul_mem c⁻¹ hw0Wraw
    · rcases hw0Cmp with ⟨hw1, hw2⟩
      constructor
      · intro r s hrs
        have h := hw1 r s hrs
        change c⁻¹ * e w0 s ≤ lam * (c⁻¹ * e w0 r)
        calc
          c⁻¹ * e w0 s ≤ c⁻¹ * (lam * e w0 r) :=
            mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hc))
          _ = lam * (c⁻¹ * e w0 r) := by ring
      · intro r s hrs
        have h := hw2 r s hrs
        change lam * (c⁻¹ * e w0 r) ≤ c⁻¹ * e w0 s
        calc
          lam * (c⁻¹ * e w0 r) = c⁻¹ * (lam * e w0 r) := by ring
          _ ≤ c⁻¹ * e w0 s := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hc))
    · change dotProduct (c⁻¹ • e w0) V = 1
      rw [smul_dotProduct, hdot]
      change c⁻¹ * c = 1
      exact inv_mul_cancel₀ (ne_of_gt hc)
