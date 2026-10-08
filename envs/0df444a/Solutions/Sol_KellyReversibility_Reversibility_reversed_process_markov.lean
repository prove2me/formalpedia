-- Prove2me | solution 1 for KellyReversibility.Reversibility.reversed_process_markov
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:48:37.166979+00:00
-- url     : https://prove2.me/submissions/b1f5ac3e-f9c9-4afa-b02f-1e09bc7c2149

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyReversibility_Reversibility_StationaryLaw
import Definitions.Def_KellyReversibility_Reversibility_MarkovProcess

set_option autoImplicit false

namespace CC0BRev

open KellyReversibility.Reversibility

/-- the sorted-order product -/
noncomputable def W {S : Type*} (T : ℝ → Matrix S S ℝ) (π : S → ℝ) {n : ℕ}
    (u : Fin (n + 1) → ℝ) (a : Fin (n + 1) → S) : ℝ :=
  π (a 0) * ∏ r : Fin n, T (u r.succ - u r.castSucc) (a r.castSucc) (a r.succ)

lemma fdd_eq_W {S : Type*} (T : ℝ → Matrix S S ℝ) (π : S → ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) :
    fdd T π t j = W T π (t ∘ Tuple.sort t) (j ∘ Tuple.sort t) := rfl

lemma tie_const {S : Type*} [DecidableEq S] (T : ℝ → Matrix S S ℝ) (hT : T 0 = 1)
    (π : S → ℝ) {n : ℕ} (v : Fin (n + 1) → ℝ) (a : Fin (n + 1) → S) (hv : Monotone v)
    (hW : W T π v a ≠ 0) : ∀ m m' : Fin (n + 1), v m = v m' → a m = a m' := by
  unfold W at hW
  have hprod := right_ne_zero_of_mul hW
  rw [Finset.prod_ne_zero_iff] at hprod
  have hcons : ∀ r : Fin n, v r.castSucc = v r.succ → a r.castSucc = a r.succ := by
    intro r hr
    have h := hprod r (Finset.mem_univ _)
    rw [hr, sub_self, hT, Matrix.one_apply] at h
    by_contra hne
    exact h (if_neg hne)
  have key : ∀ k : ℕ, ∀ m m' : Fin (n + 1), m.val + k = m'.val → v m = v m' → a m = a m' := by
    intro k
    induction k with
    | zero =>
      intro m m' h _
      have : m = m' := Fin.ext (by simpa using h)
      rw [this]
    | succ k ih =>
      intro m m' h hvm
      have hlt : m.val + k < n := by have := m'.isLt; omega
      let r : Fin n := ⟨m.val + k, hlt⟩
      have h1 : r.succ = m' := Fin.ext (by simp [r]; omega)
      have h2 : m ≤ r.castSucc := by
        rw [Fin.le_iff_val_le_val]; simp [r]
      have h3 : r.castSucc ≤ m' := by
        rw [Fin.le_iff_val_le_val]; simp [r]; omega
      have hv1 : v m ≤ v r.castSucc := hv h2
      have hv2 : v r.castSucc ≤ v m' := hv h3
      have hvr : v m = v r.castSucc := le_antisymm hv1 (hvm ▸ hv2)
      have e1 := ih m r.castSucc (by simp [r]) hvr
      rw [e1, ← h1]
      exact hcons r (by rw [h1, ← hvr, hvm])
  intro m m' hmm
  rcases le_total m m' with h | h
  · exact key (m'.val - m.val) m m' (by rw [Fin.le_iff_val_le_val] at h; omega) hmm
  · exact (key (m.val - m'.val) m' m (by rw [Fin.le_iff_val_le_val] at h; omega) hmm.symm).symm

lemma W_sort_indep {S : Type*} [DecidableEq S] (T : ℝ → Matrix S S ℝ) (hT : T 0 = 1)
    (π : S → ℝ) {n : ℕ} (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S)
    (σ ρ : Equiv.Perm (Fin (n + 1))) (hσ : Monotone (t ∘ σ)) (hρ : Monotone (t ∘ ρ)) :
    W T π (t ∘ σ) (j ∘ σ) = W T π (t ∘ ρ) (j ∘ ρ) := by
  have htt : t ∘ σ = t ∘ ρ := Tuple.unique_monotone hσ hρ
  -- if one side nonzero then j respects ties, hence the state sequences agree
  have aux : ∀ σ ρ : Equiv.Perm (Fin (n + 1)), Monotone (t ∘ σ) → t ∘ σ = t ∘ ρ →
      W T π (t ∘ σ) (j ∘ σ) ≠ 0 → j ∘ σ = j ∘ ρ := by
    intro σ ρ hσ htt hW
    have hc := tie_const T hT π (t ∘ σ) (j ∘ σ) hσ hW
    -- j constant on tie classes of t
    have hj : ∀ i i', t i = t i' → j i = j i' := by
      intro i i' hii
      have := hc (σ.symm i) (σ.symm i') (by simpa using hii)
      simpa using this
    funext m
    exact hj _ _ (congrFun htt m)
  by_cases h1 : W T π (t ∘ σ) (j ∘ σ) = 0
  · by_cases h2 : W T π (t ∘ ρ) (j ∘ ρ) = 0
    · rw [h1, h2]
    · have := aux ρ σ hρ htt.symm h2
      rw [htt, this]
  · have := aux σ ρ hσ htt h1
    rw [htt, this]

lemma fdd_eq_W_of_mono {S : Type*} [DecidableEq S] (T : ℝ → Matrix S S ℝ) (hT : T 0 = 1)
    (π : S → ℝ) {n : ℕ} (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S)
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : Monotone (t ∘ σ)) :
    fdd T π t j = W T π (t ∘ σ) (j ∘ σ) := by
  rw [fdd_eq_W]
  exact W_sort_indep T hT π t j _ _ (Tuple.monotone_sort t) hσ

lemma W_reverse {S : Type*} (T T' : ℝ → Matrix S S ℝ) (π : S → ℝ) (hπ : ∀ x, π x ≠ 0)
    (hTT : ∀ s x y, T' s x y = π y * T s y x / π x) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (a : Fin (n + 1) → S) (τ : ℝ) :
    W T' π (fun i => v (Fin.rev i)) (fun i => a (Fin.rev i)) =
      W T π (fun i => τ - v i) a := by
  unfold W
  simp_rw [hTT]
  rw [← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n)]
  simp only [Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev, Fin.rev_zero]
  have hsub : ∀ r : Fin n, (τ - v r.succ) - (τ - v r.castSucc) = v r.castSucc - v r.succ := by
    intro r; ring
  simp_rw [hsub]
  have e : ∀ r : Fin n, π (a r.castSucc) * T (v r.castSucc - v r.succ) (a r.castSucc) (a r.succ)
      / π (a r.succ) = (π (a r.castSucc) / π (a r.succ)) *
        T (v r.castSucc - v r.succ) (a r.castSucc) (a r.succ) := by
    intro r; ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, ← mul_assoc]
  congr 1
  have hs : ∏ r : Fin n, π (a r.succ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r _ => hπ _
  have h1 := Fin.prod_univ_castSucc (fun i => π (a i))
  have h2 := Fin.prod_univ_succ (fun i => π (a i))
  rw [mul_div_assoc', div_eq_iff hs, mul_comm, ← h1, h2]

lemma generator_reversed {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (π : S → ℝ) (hπ : ∀ x, π x ≠ 0) (hfb : KellyStochasticNetworks.FullBalance π q) :
    generator (KellyStochasticNetworks.reversedRates π q) =
      Matrix.diagonal (fun x => (π x)⁻¹) * Matrix.transpose (generator q) * Matrix.diagonal π := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [generator, KellyStochasticNetworks.reversedRates, Matrix.sub_apply,
    Matrix.of_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  have hrow : ∑ k, π k * q k x / π x = ∑ k, q x k := by
    have := hfb x
    simp only [tsum_fintype] at this
    rw [← Finset.sum_div, ← this]
    field_simp [hπ x]
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true]
    rw [hrow]
    field_simp [hπ x]
  · simp only [hxy, if_false, Ne.symm hxy, sub_zero]
    field_simp [hπ x]

lemma transition_reversed {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ)
    (π : S → ℝ) (hπ : ∀ x, π x ≠ 0) (hfb : KellyStochasticNetworks.FullBalance π q)
    (s : ℝ) (x y : S) :
    transition (KellyStochasticNetworks.reversedRates π q) s x y =
      π y * transition q s y x / π x := by
  let U : (Matrix S S ℝ)ˣ :=
    { val := Matrix.diagonal π
      inv := Matrix.diagonal (fun x => (π x)⁻¹)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        convert Matrix.diagonal_one with z
        exact mul_inv_cancel₀ (hπ z)
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        convert Matrix.diagonal_one with z
        exact inv_mul_cancel₀ (hπ z) }
  have hU : (↑U⁻¹ : Matrix S S ℝ) = Matrix.diagonal (fun x => (π x)⁻¹) := rfl
  have hU' : (↑U : Matrix S S ℝ) = Matrix.diagonal π := rfl
  unfold transition
  rw [generator_reversed q π hπ hfb]
  have : s • (Matrix.diagonal (fun x => (π x)⁻¹) * Matrix.transpose (generator q) * Matrix.diagonal π) =
      ((U⁻¹ : (Matrix S S ℝ)ˣ) : Matrix S S ℝ) * Matrix.transpose (s • generator q) *
        (U : Matrix S S ℝ) := by
    rw [hU, hU', Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_units_conj', hU, hU', Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.exp_transpose, Matrix.transpose_apply]
  field_simp [hπ x]

lemma transition_zero {S : Type*} [Fintype S] [DecidableEq S] (q : S → S → ℝ) :
    transition q 0 = 1 := by
  unfold transition
  rw [zero_smul, NormedSpace.exp_zero]

end CC0BRev

open KellyReversibility.Reversibility in
theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (q : S → S → ℝ) (hq : ∀ j k, j ≠ k → 0 ≤ q j k) (hq0 : ∀ j, q j j = 0)
    (hirr : RatesIrreducible q)
    (π : S → ℝ) (hπ : IsEquilibrium π q) :
    IsEquilibrium π (KellyStochasticNetworks.reversedRates π q) ∧
      ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1) → S) (τ : ℝ),
        fdd (transition q) π (fun r => τ - t r) j =
          fdd (transition (KellyStochasticNetworks.reversedRates π q)) π t j := by
  obtain ⟨hpos, hsum, hfb⟩ := hπ
  have hne : ∀ x, π x ≠ 0 := fun x => (hpos x).ne'
  refine ⟨⟨hpos, hsum, ?_⟩, ?_⟩
  · intro x
    have := hfb x
    simp only [tsum_fintype] at this ⊢
    simp only [KellyStochasticNetworks.reversedRates]
    have e1 : π x * ∑ i, π i * q i x / π x = ∑ i, π i * q i x := by
      rw [← Finset.sum_div]; field_simp [hne x]
    have e2 : ∑ k, π k * (π x * q x k / π k) = π x * ∑ k, q x k := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [hne k]
    rw [e1, e2, this]
  · intro n t j τ
    set σ := Tuple.sort (fun r => τ - t r) with hσdef
    have hσ : Monotone ((fun r => τ - t r) ∘ σ) := Tuple.monotone_sort _
    let σ' : Equiv.Perm (Fin (n + 1)) := Fin.revPerm.trans σ
    have hσ' : Monotone (t ∘ σ') := by
      intro i i' hii
      have := hσ (Fin.rev_le_rev.mpr hii)
      simp only [Function.comp_apply] at this
      simp only [Function.comp_apply, σ', Equiv.trans_apply, Fin.revPerm_apply]
      linarith
    rw [CC0BRev.fdd_eq_W (transition q), CC0BRev.fdd_eq_W_of_mono _
      (CC0BRev.transition_zero _) π t j σ' hσ']
    have := CC0BRev.W_reverse (transition q)
      (transition (KellyStochasticNetworks.reversedRates π q)) π hne
      (CC0BRev.transition_reversed q π hne hfb) (t ∘ σ) (j ∘ σ) τ
    convert this.symm using 1 <;> rfl
