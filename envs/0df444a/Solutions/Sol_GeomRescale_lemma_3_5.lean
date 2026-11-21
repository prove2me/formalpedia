-- Prove2me | solution 1 for GeomRescale.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:33:41.890699+00:00
-- url     : https://prove2.me/submissions/30ab8ee4-2feb-4d3b-8f82-999cb3b554b5

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_qnorm
import Definitions.Def_GeomRescale_vnStart
import Definitions.Def_GeomRescale_VNStep
import Definitions.Def_GeomRescale_IsCorrectOutput

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_lemma_3_5
open GeomRescale

theorem mem_before {n : ℕ} (σ : Equiv.Perm (Fin n)) (u v : Fin n) :
    u ∈ before σ v ↔ σ u < σ v := by
  simp [before]

theorem univ_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsLowerIdeal σ Finset.univ :=
  fun _ _ w _ => Finset.mem_univ w

theorem dimret {n : ℕ} {f : Finset (Fin n) → ℝ} (hsub : Submodular f) {A B : Finset (Fin n)}
    (hAB : A ⊆ B) {v : Fin n} (hv : v ∉ B) :
    f (insert v B) - f B ≤ f (insert v A) - f A := by
  have h := hsub (insert v A) B
  have h1 : insert v A ∪ B = insert v B := by
    ext x
    have := @hAB x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have h2 : insert v A ∩ B = A := by
    ext x
    have := @hAB x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, h'⟩
      · subst h
        exact absurd h' hv
      · exact h
    · intro h
      exact ⟨Or.inr h, this h⟩
  rw [h1, h2] at h
  linarith

theorem xsum_insert {n : ℕ} (x : Fin n → ℝ) {a : Fin n} {s : Finset (Fin n)} (ha : a ∉ s) :
    xsum x (insert a s) = x a + xsum x s := by
  unfold xsum
  rw [Finset.sum_insert ha]

theorem greedy_le {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f)
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) :
    xsum (greedy f σ) U ≤ f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hs : s ⊆ before σ a := by
      intro x hx
      rw [mem_before]
      rcases lt_or_eq_of_le (hmax x hx) with h | h
      · exact h
      · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hnot : a ∉ before σ a := by
      rw [mem_before]
      exact lt_irrefl _
    have h1 := dimret hsub hs hnot
    rw [xsum_insert _ ha]
    have h3 : greedy f σ a = f (insert a (before σ a)) - f (before σ a) := rfl
    linarith

theorem greedy_eq {n : ℕ} (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n))
    (U : Finset (Fin n)) (hU : IsLowerIdeal σ U) : xsum (greedy f σ) U = f U - f ∅ := by
  induction U using Finset.induction_on_max_value (fun v => σ v) with
  | empty => simp [xsum]
  | insert a s ha hmax ih =>
    have hb : before σ a = s := by
      ext x
      rw [mem_before]
      constructor
      · intro h
        have hx := hU a (Finset.mem_insert_self a s) x h
        rcases Finset.mem_insert.mp hx with hx | hx
        · subst hx
          exact absurd h (lt_irrefl _)
        · exact hx
      · intro hx
        rcases lt_or_eq_of_le (hmax x hx) with h | h
        · exact h
        · exact absurd (by rw [← σ.injective h]; exact hx) ha
    have hs : IsLowerIdeal σ s := by
      intro u hu w hw
      have := hU u (Finset.mem_insert_of_mem hu) w hw
      rcases Finset.mem_insert.mp this with h | h
      · subst h
        exact absurd (lt_of_lt_of_le hw (hmax u hu)) (lt_irrefl _)
      · exact h
    rw [xsum_insert _ ha, ih hs]
    show f (insert a (before σ a)) - f (before σ a) + (f s - f ∅) = f (insert a s) - f ∅
    rw [hb]
    ring

theorem greedy_mem {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (σ : Equiv.Perm (Fin n)) : greedy f σ ∈ baseB f := by
  simp only [baseB, Set.mem_setOf_eq]
  refine ⟨fun U => ?_, ?_⟩
  · have := greedy_le f hsub σ U
    linarith
  · have := greedy_eq f σ Finset.univ (univ_lower σ)
    linarith

theorem mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin n) :
    v ∈ pref σ i ↔ (σ v : ℕ) < i := by
  simp [pref]

theorem pref_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : pref σ 0 = ∅ := by
  ext v
  simp [pref]

theorem pref_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    pref σ (k + 1) = insert (σ.symm ⟨k, hk⟩) (pref σ k) := by
  ext v
  rw [Finset.mem_insert, mem_pref, mem_pref]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact Or.inr h
    · left
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
  · rintro (h | h)
    · subst h
      simp
    · omega

theorem not_mem_pref {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k < n) :
    σ.symm ⟨k, hk⟩ ∉ pref σ k := by
  rw [mem_pref]
  simp

theorem pref_le {n : ℕ} (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : n ≤ k) :
    pref σ k = Finset.univ := by
  ext v
  simp only [mem_pref, Finset.mem_univ, iff_true]
  exact lt_of_lt_of_le (σ v).isLt hk

theorem pref_lower {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : IsLowerIdeal σ (pref σ k) := by
  intro u hu w hw
  rw [mem_pref] at hu ⊢
  exact lt_trans (Fin.lt_iff_val_lt_val.mp hw) hu

theorem abel (a b : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), b j * a j =
      ∑ j ∈ Finset.range k, (∑ i ∈ Finset.range (j + 1), a i) * (b j - b (j + 1)) +
        (∑ i ∈ Finset.range (k + 1), a i) * b k := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ (fun j => b j * a j) (k + 1), ih]
    simp only [Finset.sum_range_succ]
    ring

noncomputable def seq {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (j : ℕ) : ℝ :=
  if h : j < N then x (σ.symm ⟨j, h⟩) else 0

theorem seq_of_lt {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) {j : ℕ} (h : j < N) :
    seq x σ j = x (σ.symm ⟨j, h⟩) := by
  rw [seq, dif_pos h]

theorem xsum_pref {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∀ k, k ≤ N → xsum x (pref σ k) = ∑ j ∈ Finset.range k, seq x σ j
  | 0, _ => by simp [pref_zero, xsum]
  | k + 1, hk => by
    have hk' : k < N := hk
    rw [pref_succ σ hk', Finset.sum_range_succ, ← xsum_pref x σ k (le_of_lt hk'),
      xsum_insert _ (not_mem_pref σ hk'), seq_of_lt x σ hk']
    ring

theorem dot_eq {N : ℕ} (w x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range N, seq w σ j * seq x σ j := by
  have h1 : ∑ v, w v * x v = ∑ i, w (σ.symm i) * x (σ.symm i) :=
    (Equiv.sum_comp σ.symm (fun v => w v * x v)).symm
  unfold dotProduct
  rw [h1, ← Fin.sum_univ_eq_sum_range (fun j => seq w σ j * seq x σ j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [seq_of_lt w σ i.isLt, seq_of_lt x σ i.isLt]

theorem key_abel {m : ℕ} (w x : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) :
    w ⬝ᵥ x = ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
      xsum x Finset.univ * seq w σ m := by
  rw [dot_eq w x σ, abel]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [xsum_pref x σ (j + 1) (by omega)]
  · rw [← pref_le σ (le_refl (m + 1)), xsum_pref x σ (m + 1) (le_refl _)]

theorem sorted_step {m : ℕ} (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) {j : ℕ} (hj : j < m) : seq w σ j ≤ seq w σ (j + 1) := by
  rw [seq_of_lt w σ (show j < m + 1 by omega), seq_of_lt w σ (show j + 1 < m + 1 by omega)]
  apply hσ
  simp [Fin.lt_iff_val_lt_val]

theorem greedy_min_aux {m : ℕ} (f : Finset (Fin (m + 1)) → ℝ) (hsub : Submodular f)
    (hf0 : f ∅ = 0) (w : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : IsSortedBy w σ) :
    greedy f σ ∈ baseB f ∧
      (∀ x ∈ baseB f, w ⬝ᵥ greedy f σ ≤ w ⬝ᵥ x) ∧
      w ⬝ᵥ greedy f σ =
        ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
          f Finset.univ * seq w σ m := by
  have hg : ∀ k, xsum (greedy f σ) (pref σ k) = f (pref σ k) := by
    intro k
    rw [greedy_eq f σ _ (pref_lower σ k), hf0, sub_zero]
  have hgu : xsum (greedy f σ) Finset.univ = f Finset.univ := by
    rw [greedy_eq f σ _ (univ_lower σ), hf0, sub_zero]
  have hform : w ⬝ᵥ greedy f σ =
      ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) +
        f Finset.univ * seq w σ m := by
    rw [key_abel w (greedy f σ) σ, hgu]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hg]
  refine ⟨greedy_mem f hsub hf0 σ, ?_, hform⟩
  intro x hx
  simp only [baseB, Set.mem_setOf_eq] at hx
  rw [hform, key_abel w x σ, hx.2]
  have : ∑ j ∈ Finset.range m, f (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) ≤
      ∑ j ∈ Finset.range m, xsum x (pref σ (j + 1)) * (seq w σ j - seq w σ (j + 1)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have h1 := sorted_step w σ hσ hj
    exact mul_le_mul_of_nonpos_right (hx.1 _) (by linarith)
  linarith

theorem enl_empty {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m ∅ = 0 :=
  if_pos (Or.inl rfl)

theorem enl_univ {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) : enlarge f m Finset.univ = 0 :=
  if_pos (Or.inr rfl)

theorem enl_mid {n : ℕ} (f : Finset (Fin n) → ℝ) (m : ℝ) (U : Finset (Fin n)) (h1 : U ≠ ∅)
    (h2 : U ≠ Finset.univ) : enlarge f m U = f U + m :=
  if_neg (not_or.mpr ⟨h1, h2⟩)

theorem enlarge_sub {n : ℕ} (f : Finset (Fin n) → ℝ) (hsub : Submodular f) (hf0 : f ∅ = 0)
    (μ : ℝ) (hμ : max 0 (-f Finset.univ) ≤ μ) : Submodular (enlarge f μ) := by
  have hμ0 : 0 ≤ μ := le_trans (le_max_left _ _) hμ
  have hμ1 : -f Finset.univ ≤ μ := le_trans (le_max_right _ _) hμ
  have hg0 : ∀ m, enlarge f m ∅ = 0 := fun m => if_pos (Or.inl rfl)
  have hgu : ∀ m, enlarge f m Finset.univ = 0 := fun m => if_pos (Or.inr rfl)
  have hgp : ∀ m U, U ≠ ∅ → U ≠ Finset.univ → enlarge f m U = f U + m :=
    fun m U h1 h2 => if_neg (not_or.mpr ⟨h1, h2⟩)
  intro S T
  by_cases hS0 : S = ∅
  · rw [hS0, Finset.empty_union, Finset.empty_inter, hg0] <;> linarith
  by_cases hT0 : T = ∅
  · rw [hT0, Finset.union_empty, Finset.inter_empty, hg0] <;> linarith
  by_cases hSu : S = Finset.univ
  · rw [hSu, Finset.union_eq_left.2 (Finset.subset_univ T),
      Finset.inter_eq_right.2 (Finset.subset_univ T), hgu] <;> linarith
  by_cases hTu : T = Finset.univ
  · rw [hTu, Finset.union_eq_right.2 (Finset.subset_univ S),
      Finset.inter_eq_left.2 (Finset.subset_univ S), hgu] <;> linarith
  rw [hgp μ S hS0 hSu, hgp μ T hT0 hTu]
  have hST := hsub S T
  have hU0 : S ∪ T ≠ ∅ := fun h => hS0 (Finset.union_eq_empty.mp h).1
  have hIu : S ∩ T ≠ Finset.univ := by
    intro h
    apply hSu
    refine Finset.eq_univ_of_forall (fun x => ?_)
    have hx := Finset.mem_univ x
    rw [← h] at hx
    exact (Finset.mem_inter.mp hx).1
  by_cases hUu : S ∪ T = Finset.univ
  · rw [hUu, hgu]
    rw [hUu] at hST
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith
  · rw [hgp μ _ hU0 hUu]
    by_cases hI0 : S ∩ T = ∅
    · rw [hI0, hg0]; rw [hI0, hf0] at hST; linarith
    · rw [hgp μ _ hI0 hIu]; linarith

theorem qd_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (x y : Fin n → ℝ) :
    qdot Q x y = qdot Q y x := by
  have hT : Q.transpose = Q := by
    have h := hQ.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  unfold qdot
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]

theorem qd_eq_dot {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (y x : Fin n → ℝ) :
    qdot Q y x = (Q.mulVec y) ⬝ᵥ x := by
  rw [qd_symm hQ]
  unfold qdot
  rw [dotProduct_comm]

theorem qd_nonneg {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (x : Fin n → ℝ) :
    0 ≤ qdot Q x x := by
  have h := hQ.posSemidef.dotProduct_mulVec_nonneg x
  unfold qdot
  simpa using h

theorem qn_sq {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (x : Fin n → ℝ) :
    qnorm Q x ^ 2 = qdot Q x x :=
  Real.sq_sqrt (qd_nonneg hQ x)

theorem qd_add_l {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    qdot Q (x + y) z = qdot Q x z + qdot Q y z := by
  unfold qdot
  rw [add_dotProduct]

theorem qd_add_r {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    qdot Q x (y + z) = qdot Q x y + qdot Q x z := by
  unfold qdot
  rw [Matrix.mulVec_add, dotProduct_add]

theorem qd_sub_l {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    qdot Q (x - y) z = qdot Q x z - qdot Q y z := by
  unfold qdot
  rw [sub_dotProduct]

theorem qd_sub_r {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (x y z : Fin n → ℝ) :
    qdot Q x (y - z) = qdot Q x y - qdot Q x z := by
  unfold qdot
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem qd_smul_l {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (x z : Fin n → ℝ) :
    qdot Q (s • x) z = s * qdot Q x z := by
  unfold qdot
  rw [smul_dotProduct, smul_eq_mul]

theorem qd_smul_r {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (s : ℝ) (x z : Fin n → ℝ) :
    qdot Q x (s • z) = s * qdot Q x z := by
  unfold qdot
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem unit_c {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (y g : Fin n → ℝ) :
    qdot Q y (unitQ Q g) = (qnorm Q g)⁻¹ * qdot Q y g := by
  unfold unitQ
  rw [qd_smul_r]

theorem unit_b {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (g : Fin n → ℝ) :
    qdot Q (unitQ Q g) (unitQ Q g) ≤ 1 ∧ 0 ≤ qdot Q (unitQ Q g) (unitQ Q g) := by
  refine ⟨?_, qd_nonneg hQ _⟩
  unfold unitQ
  rw [qd_smul_l, qd_smul_r, ← qn_sq hQ g, ← mul_assoc]
  by_cases h : qnorm Q g = 0
  · rw [h]
    simp
  · have : (qnorm Q g)⁻¹ * (qnorm Q g)⁻¹ * qnorm Q g ^ 2 = 1 := by
      field_simp
    linarith

theorem upd_vec {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (y g : Fin n → ℝ)
    (hy : 0 < qdot Q y y) (hc : qdot Q y g ≤ 0) (lam : ℝ)
    (hlam : lam = qdot Q (y - unitQ Q g) y / qnorm Q (y - unitQ Q g) ^ 2) :
    0 ≤ lam ∧ lam ≤ 1 ∧
      qdot Q ((1 - lam) • y + lam • unitQ Q g) ((1 - lam) • y + lam • unitQ Q g) *
        (1 + qdot Q y y) ≤ qdot Q y y := by
  obtain ⟨hb1, hb0⟩ := unit_b hQ g
  have hcu : qdot Q y (unitQ Q g) ≤ 0 := by
    rw [unit_c]
    exact mul_nonpos_iff.mpr (Or.inl ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), hc⟩)
  obtain ⟨u, hu⟩ : ∃ u, u = unitQ Q g := ⟨_, rfl⟩
  rw [← hu] at hlam hb1 hb0 hcu ⊢
  obtain ⟨a, ha⟩ : ∃ a, a = qdot Q y y := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = qdot Q u u := ⟨_, rfl⟩
  obtain ⟨c, hc'⟩ : ∃ c, c = qdot Q y u := ⟨_, rfl⟩
  have hD : qnorm Q (y - u) ^ 2 = a - 2 * c + b := by
    rw [qn_sq hQ]
    simp only [qd_sub_l, qd_sub_r]
    rw [qd_symm hQ u y, ← ha, ← hb, ← hc']
    ring
  have hN : qdot Q (y - u) y = a - c := by
    rw [qd_sub_l, qd_symm hQ u y, ← ha, ← hc']
  rw [hD, hN] at hlam
  have hexp : qdot Q ((1 - lam) • y + lam • u) ((1 - lam) • y + lam • u) =
      (1 - lam) ^ 2 * a + 2 * (1 - lam) * lam * c + lam ^ 2 * b := by
    simp only [qd_add_l, qd_add_r, qd_smul_l, qd_smul_r]
    rw [qd_symm hQ u y, ← ha, ← hb, ← hc']
    ring
  rw [← hb] at hb0 hb1
  rw [← hc'] at hcu
  rw [← ha] at hy
  have hDpos : 0 < a - 2 * c + b := by linarith
  have hDne : a - 2 * c + b ≠ 0 := hDpos.ne'
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    exact div_nonneg (by linarith) hDpos.le
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one hDpos]
    linarith
  refine ⟨hlam0, hlam1, ?_⟩
  rw [hexp, ← ha]
  have hLD : lam * (a - 2 * c + b) = a - c := by
    rw [hlam, div_mul_cancel₀ _ hDne]
  have hED : ((1 - lam) ^ 2 * a + 2 * (1 - lam) * lam * c + lam ^ 2 * b) * (a - 2 * c + b) =
      a * b - c ^ 2 := by
    linear_combination (lam * (a - 2 * c + b) - (a - c)) * hLD
  refine le_of_mul_le_mul_right ?_ hDpos
  have e1 : ((1 - lam) ^ 2 * a + 2 * (1 - lam) * lam * c + lam ^ 2 * b) * (1 + a) *
      (a - 2 * c + b) = ((1 - lam) ^ 2 * a + 2 * (1 - lam) * lam * c + lam ^ 2 * b) *
      (a - 2 * c + b) * (1 + a) := by ring
  rw [e1, hED]
  nlinarith [mul_nonneg (sq_nonneg a) (show 0 ≤ 1 - b by linarith),
    mul_nonneg hy.le (show 0 ≤ -c by linarith),
    mul_nonneg (sq_nonneg c) (show 0 ≤ 1 + a by linarith)]

theorem vn_guard {n : ℕ} {f : Finset (Fin n) → ℤ} {Q : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    {v v' : VN n} (h : VNStep f Q ε v v') : ε < qnorm Q v.y := by
  cases h with
  | plain _ h1 _ _ => exact h1
  | slide _ _ h1 _ _ _ => exact h1

theorem sum_ite_pos {N : ℕ} (σ : Equiv.Perm (Fin N)) (δ : ℝ) (k : ℕ) (hk : k < N) :
    ∑ v, (if (σ v : ℕ) = k then δ else 0) = δ := by
  rw [Finset.sum_eq_single (σ.symm ⟨k, hk⟩)]
  · simp
  · intro b _ hb
    have : (σ b : ℕ) ≠ k := by
      intro h
      apply hb
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_ind0 {N : ℕ} (w : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (δ : ℝ) (k : ℕ)
    (hk : k < N) :
    ∑ v, w v * (if (σ v : ℕ) = k then δ else 0) = δ * w (σ.symm ⟨k, hk⟩) := by
  rw [Finset.sum_eq_single (σ.symm ⟨k, hk⟩)]
  · simp [mul_comm]
  · intro b _ hb
    have : (σ b : ℕ) ≠ k := by
      intro h
      apply hb
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem dot_patch {m : ℕ} (w g : Fin (m + 1) → ℝ) (σ : Equiv.Perm (Fin (m + 1))) (δ : ℝ) :
    w ⬝ᵥ patch σ δ g =
      w ⬝ᵥ g + δ * w (σ.symm ⟨0, by omega⟩) - δ * w (σ.symm ⟨m, by omega⟩) := by
  have h1 : ∀ v, w v * patch σ δ g v = w v * g v + w v * (if (σ v : ℕ) = 0 then δ else 0) -
      w v * (if (σ v : ℕ) = m then δ else 0) := by
    intro v
    simp only [patch]
    split_ifs <;> first | ring1 | omega
  unfold dotProduct
  rw [Finset.sum_congr rfl (fun v _ => h1 v), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_ind0 w σ δ 0 (by omega), sum_ind0 w σ δ m (by omega)]

theorem slide_neg {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef)
    (F : Finset (Fin n) → ℝ) (hF0 : F ∅ = 0) (hFV : F Finset.univ = 0) (y : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (hσ : IsSortedBy (Q.mulVec y) σ) (W' : Finset (Fin n))
    (hW' : IsMinSet F σ W') :
    qdot Q y (patch σ (-(F W')) (greedy F σ)) ≤ 0 := by
  rcases n with _ | m
  · unfold qdot dotProduct
    simp
  rw [qd_eq_dot hQ]
  obtain ⟨w, hw⟩ : ∃ w, w = Q.mulVec y := ⟨_, rfl⟩
  rw [← hw] at hσ ⊢
  rw [dot_patch, key_abel w _ σ]
  have hgu : xsum (greedy F σ) Finset.univ = 0 := by
    rw [greedy_eq F σ _ (univ_lower σ), hF0, hFV, sub_zero]
  rw [hgu, zero_mul, add_zero]
  have hb : ∑ j ∈ Finset.range m, xsum (greedy F σ) (pref σ (j + 1)) *
      (seq w σ j - seq w σ (j + 1)) ≤
      ∑ j ∈ Finset.range m, F W' * (seq w σ j - seq w σ (j + 1)) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rw [greedy_eq F σ _ (pref_lower σ _), hF0, sub_zero]
    have h1 := sorted_step w σ hσ hj
    have h2 := hW'.2 (j + 1) (by omega)
    exact mul_le_mul_of_nonpos_right h2 (by linarith)
  have htel : ∑ j ∈ Finset.range m, F W' * (seq w σ j - seq w σ (j + 1)) =
      F W' * (seq w σ 0 - seq w σ m) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub']
  rw [seq_of_lt w σ (show 0 < m + 1 by omega), seq_of_lt w σ (show m < m + 1 by omega)] at htel
  linarith

theorem minset_lt {n : ℕ} (F : Finset (Fin n) → ℝ) (hF0 : F ∅ = 0) (hFV : F Finset.univ = 0)
    (w : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (hσ : IsSortedBy w σ) (W' : Finset (Fin n))
    (hW' : IsMinSet F σ W') (hpos : 0 < w ⬝ᵥ greedy F σ) : F W' < 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ k, k ≤ n → 0 ≤ F (pref σ k) := fun k hk => le_trans hcon (hW'.2 k hk)
  rcases n with _ | m
  · have : w ⬝ᵥ greedy F σ = 0 := by
      unfold dotProduct
      simp
    linarith
  · rw [key_abel w _ σ] at hpos
    have hgu : xsum (greedy F σ) Finset.univ = 0 := by
      rw [greedy_eq F σ _ (univ_lower σ), hF0, hFV, sub_zero]
    rw [hgu, zero_mul, add_zero] at hpos
    have : ∑ j ∈ Finset.range m, xsum (greedy F σ) (pref σ (j + 1)) *
        (seq w σ j - seq w σ (j + 1)) ≤ 0 := by
      refine Finset.sum_nonpos (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      rw [greedy_eq F σ _ (pref_lower σ _), hF0, sub_zero]
      have h1 := sorted_step w σ hσ hj
      exact mul_nonpos_iff.mpr (Or.inl ⟨hall (j + 1) (by omega), by linarith⟩)
    linarith

theorem patch_mem {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) (g : Fin n → ℝ)
    (μ0 δ : ℝ) (hδ : 0 ≤ δ) (hg : g ∈ baseB (enlarge F μ0)) :
    patch σ δ g ∈ baseB (enlarge F (μ0 + δ)) := by
  simp only [baseB, Set.mem_setOf_eq] at hg ⊢
  have hA0 : ∀ v, 0 ≤ (if (σ v : ℕ) = 0 then δ else 0) := fun v => by
    split_ifs <;> linarith
  have hB0 : ∀ v, 0 ≤ (if (σ v : ℕ) + 1 = n then δ else 0) := fun v => by
    split_ifs <;> linarith
  have hsplit : ∀ U, xsum (patch σ δ g) U = xsum g U +
      ∑ v ∈ U, (if (σ v : ℕ) = 0 then δ else 0) -
      ∑ v ∈ U, (if (σ v : ℕ) + 1 = n then δ else 0) := by
    intro U
    unfold xsum patch
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAle : ∑ v, (if (σ v : ℕ) = 0 then δ else 0) ≤ δ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simpa using hδ
    · rw [sum_ite_pos σ δ 0 h]
  have hAB : ∑ v, (if (σ v : ℕ) = 0 then δ else 0) =
      ∑ v, (if (σ v : ℕ) + 1 = n then δ else 0) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have : ∀ v : Fin (m + 1), (if (σ v : ℕ) + 1 = m + 1 then δ else 0) =
          (if (σ v : ℕ) = m then δ else 0) := by
        intro v
        split_ifs <;> first | rfl | omega
      rw [Finset.sum_congr rfl (fun v _ => this v), sum_ite_pos σ δ 0 h,
        sum_ite_pos σ δ m (by omega)]
  refine ⟨fun U => ?_, ?_⟩
  · rw [hsplit]
    have h1 : ∑ v ∈ U, (if (σ v : ℕ) = 0 then δ else 0) ≤ δ :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun v _ _ => hA0 v)) hAle
    have h2 : 0 ≤ ∑ v ∈ U, (if (σ v : ℕ) + 1 = n then δ else 0) :=
      Finset.sum_nonneg (fun v _ => hB0 v)
    by_cases hU0 : U = ∅
    · subst hU0
      rw [enl_empty]
      simp [xsum]
    by_cases hUu : U = Finset.univ
    · subst hUu
      rw [enl_univ, hg.2, enl_univ, ← hAB]
      linarith
    · rw [enl_mid F _ U hU0 hUu]
      have h3 := hg.1 U
      rw [enl_mid F _ U hU0 hUu] at h3
      linarith
  · rw [hsplit, hg.2, enl_univ, enl_univ, ← hAB]
    ring

theorem baseB_mono {n : ℕ} (F : Finset (Fin n) → ℝ) {μ1 μ2 : ℝ} (h : μ1 ≤ μ2)
    {x : Fin n → ℝ} (hx : x ∈ baseB (enlarge F μ1)) : x ∈ baseB (enlarge F μ2) := by
  simp only [baseB, Set.mem_setOf_eq] at hx ⊢
  refine ⟨fun U => le_trans (hx.1 U) ?_, ?_⟩
  · unfold enlarge
    split_ifs <;> linarith
  · rw [hx.2, enl_univ, enl_univ]

theorem list_smul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (l : List ((Fin n → ℝ) × ℝ)) :
    (l.map (fun p => (c * p.2) • unitQ Q p.1)).sum =
      c • (l.map (fun p => p.2 • unitQ Q p.1)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, smul_add, mul_smul]

theorem upd_data {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (v0 : VN n)
    (B : Set (Fin n → ℝ)) (hB : ∀ p ∈ v0.data, p.1 ∈ B) (hgB : g ∈ B)
    (hw : ∀ p ∈ v0.data, 0 ≤ p.2) (hs : (v0.data.map Prod.snd).sum = 1)
    (hy : v0.y = (v0.data.map (fun p => p.2 • unitQ Q p.1)).sum)
    (h0 : 0 ≤ qdot Q (v0.y - unitQ Q g) v0.y / qnorm Q (v0.y - unitQ Q g) ^ 2)
    (h1 : qdot Q (v0.y - unitQ Q g) v0.y / qnorm Q (v0.y - unitQ Q g) ^ 2 ≤ 1) :
    (∀ p ∈ (vnUpdate Q g v0).data, p.1 ∈ B) ∧ (∀ p ∈ (vnUpdate Q g v0).data, 0 ≤ p.2) ∧
      ((vnUpdate Q g v0).data.map Prod.snd).sum = 1 ∧
      (vnUpdate Q g v0).y = ((vnUpdate Q g v0).data.map (fun p => p.2 • unitQ Q p.1)).sum := by
  obtain ⟨L, hL⟩ : ∃ L, L = qdot Q (v0.y - unitQ Q g) v0.y / qnorm Q (v0.y - unitQ Q g) ^ 2 :=
    ⟨_, rfl⟩
  have hd : (vnUpdate Q g v0).data = v0.data.map (fun p => (p.1, (1 - L) * p.2)) ++ [(g, L)] := by
    rw [hL]
    rfl
  have hyy : (vnUpdate Q g v0).y = (1 - L) • v0.y + L • unitQ Q g := by
    rw [hL]
    rfl
  rw [← hL] at h0 h1
  rw [hd, hyy]
  refine ⟨fun p hp => ?_, fun p hp => ?_, ?_, ?_⟩
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hB q hq
    · rw [List.mem_singleton] at hp
      rw [hp]
      exact hgB
  · rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact mul_nonneg (by linarith) (hw q hq)
    · rw [List.mem_singleton] at hp
      rw [hp]
      exact h0
  · rw [List.map_append, List.sum_append, List.map_map]
    have e : (Prod.snd ∘ fun p : (Fin n → ℝ) × ℝ => (p.1, (1 - L) * p.2)) =
        fun p => (1 - L) * p.2 := rfl
    rw [e, List.sum_map_mul_left, hs]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one]
    ring
  · rw [List.map_append, List.sum_append, List.map_map]
    have e : ((fun p : (Fin n → ℝ) × ℝ => p.2 • unitQ Q p.1) ∘
        fun p : (Fin n → ℝ) × ℝ => (p.1, (1 - L) * p.2)) =
        fun p => ((1 - L) * p.2) • unitQ Q p.1 := rfl
    rw [e, list_smul, ← hy]
    simp

theorem exists_sorted {n : ℕ} (w : Fin n → ℝ) : ∃ σ : Equiv.Perm (Fin n), IsSortedBy w σ := by
  refine ⟨(Tuple.sort w).symm, fun u v h => ?_⟩
  have hm := Tuple.monotone_sort w (le_of_lt h)
  simpa using hm

theorem step_dec {n : ℕ} {f : Finset (Fin n) → ℤ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) {ε : ℝ} (hε : 0 < ε) {v v' : VN n} (h : VNStep f Q ε v v') :
    qdot Q v'.y v'.y * (1 + qdot Q v.y v.y) ≤ qdot Q v.y v.y := by
  have hg := vn_guard h
  have hy : 0 < qdot Q v.y v.y := by
    have := pow_pos (lt_trans hε hg) 2
    rwa [qn_sq hQ] at this
  cases h with
  | plain σ h1 h2 h3 =>
    have hc : qdot Q v.y (greedy (enlarge (fR f) (v.μ : ℝ)) σ) ≤ 0 := not_lt.mp h3
    exact (upd_vec hQ v.y _ hy hc _ rfl).2.2
  | slide σ W' h1 h2 h3 h4 =>
    have hc := slide_neg hQ (enlarge (fR f) (v.μ : ℝ)) (enl_empty _ _) (enl_univ _ _) v.y σ h2
      W' h4
    exact (upd_vec hQ v.y _ hy hc _ rfl).2.2

theorem chain_bound {n : ℕ} {f : Finset (Fin n) → ℤ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∀ (l : List (VN n)) (v : VN n) (k : ℕ), (v :: l).IsChain (VNStep f Q ε) →
      qdot Q v.y v.y * ((k : ℝ) + 1) ≤ 1 → l ≠ [] → ((k : ℝ) + l.length) * ε ^ 2 < 1
  | [], _, _, _, _, hne => absurd rfl hne
  | v' :: l', v, k, hch, hk, _ => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨h1, h2⟩ := hch
    have hg := vn_guard h1
    have hε3 : ε ^ 2 < qdot Q v.y v.y := by
      have := pow_lt_pow_left₀ hg hε.le two_ne_zero
      rwa [qn_sq hQ] at this
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : ((k : ℝ) + 1) * ε ^ 2 < 1 := by
      nlinarith [mul_lt_mul_of_pos_right hε3 (show (0 : ℝ) < k + 1 by linarith)]
    by_cases hl : l' = []
    · subst hl
      simp only [List.length_singleton, Nat.cast_one]
      linarith
    · have hdec := step_dec hQ hε h1
      have ha0 := qd_nonneg hQ v.y
      have ha1 := qd_nonneg hQ v'.y
      have hk' : qdot Q v'.y v'.y * (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
        push_cast
        have h3 : qdot Q v'.y v'.y * ((k : ℝ) + 2) * (1 + qdot Q v.y v.y) ≤
            1 + qdot Q v.y v.y := by
          have := mul_le_mul_of_nonneg_right hdec (show (0 : ℝ) ≤ k + 2 by linarith)
          nlinarith
        have h4 : 0 < 1 + qdot Q v.y v.y := by linarith
        have h5 : qdot Q v'.y v'.y * ((k : ℝ) + 2) ≤ 1 := by
          by_contra hcon
          push_neg at hcon
          nlinarith [mul_lt_mul_of_pos_right hcon h4]
        linarith
      have := chain_bound hQ hε l' v' (k + 1) h2 hk' hl
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at this ⊢
      linarith

def Inv {n : ℕ} (f : Finset (Fin n) → ℤ) (Q : Matrix (Fin n) (Fin n) ℝ) (μ : ℤ) (v : VN n) :
    Prop :=
  μ ≤ v.μ ∧ f v.W = -v.μ ∧
    (∀ p ∈ v.data, p.1 ∈ SchrijverSFM.Alg.baseB (enlarge (fR f) (v.μ : ℝ))) ∧
    (∀ p ∈ v.data, 0 ≤ p.2) ∧
    (v.data.map Prod.snd).sum = 1 ∧
    v.y = (v.data.map (fun p => p.2 • unitQ Q p.1)).sum

theorem hmu_of {n : ℕ} (f : Finset (Fin n) → ℤ) (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ)
    (m : ℤ) (hm : μ ≤ m) : max 0 (-fR f Finset.univ) ≤ (m : ℝ) := by
  have h1 : (0 : ℤ) ≤ m := le_trans (le_trans (le_max_left _ _) hμ) hm
  have h2 : -f Finset.univ ≤ m := le_trans (le_trans (le_max_right _ _) hμ) hm
  show max 0 (-((f Finset.univ : ℤ) : ℝ)) ≤ (m : ℝ)
  refine max_le ?_ ?_
  · exact_mod_cast h1
  · exact_mod_cast h2

theorem inv_start {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n)) (hW : f W = -μ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n)) (e o : ℕ) :
    Inv f Q μ (vnStart f μ W Q σ e o) := by
  have hf0' : fR f ∅ = 0 := by simp [fR, hf0]
  have hgB := greedy_mem _ (enlarge_sub (fR f) hsub hf0' (μ : ℝ) (hmu_of f μ hμ μ le_rfl))
    (enl_empty _ _) σ
  refine ⟨le_refl _, hW, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : p = (greedy (enlarge (fR f) (μ : ℝ)) σ, 1) := List.mem_singleton.mp hp
    rw [hp']
    exact hgB
  · intro p hp
    have hp' : p = (greedy (enlarge (fR f) (μ : ℝ)) σ, 1) := List.mem_singleton.mp hp
    rw [hp']
    norm_num
  · show ([(greedy (enlarge (fR f) (μ : ℝ)) σ, (1 : ℝ))].map Prod.snd).sum = 1
    simp
  · show unitQ Q (greedy (enlarge (fR f) (μ : ℝ)) σ) =
      ([(greedy (enlarge (fR f) (μ : ℝ)) σ, (1 : ℝ))].map (fun p => p.2 • unitQ Q p.1)).sum
    simp

theorem inv_step {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef)
    (ε : ℝ) (hε : 0 < ε) (v v' : VN n) (hI : Inv f Q μ v) (h : VNStep f Q ε v v') :
    Inv f Q μ v' := by
  have hf0' : fR f ∅ = 0 := by simp [fR, hf0]
  have hg := vn_guard h
  have hy : 0 < qdot Q v.y v.y := by
    have := pow_pos (lt_trans hε hg) 2
    rwa [qn_sq hQ] at this
  cases h with
  | plain σ h1 h2 h3 =>
    have hgB := greedy_mem _ (enlarge_sub (fR f) hsub hf0' (v.μ : ℝ)
      (hmu_of f μ hμ v.μ hI.1)) (enl_empty _ _) σ
    have hc : qdot Q v.y (greedy (enlarge (fR f) (v.μ : ℝ)) σ) ≤ 0 := not_lt.mp h3
    obtain ⟨hl0, hl1, -⟩ := upd_vec hQ v.y _ hy hc _ rfl
    obtain ⟨d1, d2, d3, d4⟩ := upd_data Q (greedy (enlarge (fR f) (v.μ : ℝ)) σ)
      { v with evals := v.evals + n, ops := v.ops + sortCost n + n ^ 2 } _
      hI.2.2.1 hgB hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2 hl0 hl1
    exact ⟨hI.1, hI.2.1, d1, d2, d3, d4⟩
  | slide σ W' h1 h2 h3 h4 =>
    have hpos : 0 < (Q.mulVec v.y) ⬝ᵥ greedy (enlarge (fR f) (v.μ : ℝ)) σ := by
      rw [← qd_eq_dot hQ]
      exact h3
    have hFW : enlarge (fR f) (v.μ : ℝ) W' < 0 :=
      minset_lt _ (enl_empty _ _) (enl_univ _ _) _ σ h2 W' h4 hpos
    have hW0 : W' ≠ ∅ := by
      rintro rfl
      rw [enl_empty] at hFW
      exact lt_irrefl _ hFW
    have hWu : W' ≠ Finset.univ := by
      rintro rfl
      rw [enl_univ] at hFW
      exact lt_irrefl _ hFW
    have hFW' : enlarge (fR f) (v.μ : ℝ) W' = (f W' : ℝ) + v.μ := enl_mid _ _ _ hW0 hWu
    have hlt : v.μ < -f W' := by
      have h5 : (f W' : ℝ) + v.μ < 0 := by
        rw [← hFW']
        exact hFW
      have h6 : f W' + v.μ < 0 := by exact_mod_cast h5
      omega
    have hδ : 0 ≤ -(enlarge (fR f) (v.μ : ℝ) W') := by linarith
    have he : (v.μ : ℝ) + -(enlarge (fR f) (v.μ : ℝ) W') = ((-f W' : ℤ) : ℝ) := by
      rw [hFW']
      push_cast
      ring
    have hgB0 := greedy_mem _ (enlarge_sub (fR f) hsub hf0' (v.μ : ℝ)
      (hmu_of f μ hμ v.μ hI.1)) (enl_empty _ _) σ
    have hgB : patch σ (-(enlarge (fR f) (v.μ : ℝ) W')) (greedy (enlarge (fR f) (v.μ : ℝ)) σ) ∈
        baseB (enlarge (fR f) ((-f W' : ℤ) : ℝ)) := by
      rw [← he]
      exact patch_mem (fR f) σ _ (v.μ : ℝ) _ hδ hgB0
    have hc := slide_neg hQ (enlarge (fR f) (v.μ : ℝ)) (enl_empty _ _) (enl_univ _ _) v.y σ h2
      W' h4
    obtain ⟨hl0, hl1, -⟩ := upd_vec hQ v.y _ hy hc _ rfl
    have hle : (v.μ : ℝ) ≤ ((-f W' : ℤ) : ℝ) := by exact_mod_cast hlt.le
    have hold : ∀ p ∈ v.data, p.1 ∈ baseB (enlarge (fR f) ((-f W' : ℤ) : ℝ)) :=
      fun p hp => baseB_mono _ hle (hI.2.2.1 p hp)
    obtain ⟨d1, d2, d3, d4⟩ := upd_data Q
      (patch σ (-(enlarge (fR f) (v.μ : ℝ) W')) (greedy (enlarge (fR f) (v.μ : ℝ)) σ))
      { v with
          μ := -f W'
          W := W'
          evals := v.evals + n
          ops := v.ops + sortCost n + n ^ 2 + n } _
      hold hgB hI.2.2.2.1 hI.2.2.2.2.1 hI.2.2.2.2.2 hl0 hl1
    exact ⟨le_trans hI.1 hlt.le, (neg_neg (f W')).symm, d1, d2, d3, d4⟩

end Aux_GeomRescale_lemma_3_5

open GeomRescale Aux_GeomRescale_lemma_3_5 in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f)) (hf0 : f ∅ = 0)
    (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n)) (hW : f W = -μ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (ε : ℝ) (hε : 0 < ε)
    (σ : Equiv.Perm (Fin n)) (e o : ℕ) :
    (∀ v, Relation.ReflTransGen (VNStep f Q ε) (vnStart f μ W Q σ e o) v →
      ε < qnorm Q v.y → ∃ v', VNStep f Q ε v v') ∧
      (∀ l : List (VN n), (vnStart f μ W Q σ e o :: l).IsChain (VNStep f Q ε) →
        l.length ≤ ⌈1 / ε ^ 2⌉₊) ∧
      (∀ v, Relation.ReflTransGen (VNStep f Q ε) (vnStart f μ W Q σ e o) v →
        qnorm Q v.y ≤ ε → IsCorrectOutput f Q ε μ v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v _ hv
    obtain ⟨σ', hσ'⟩ := exists_sorted (Q.mulVec v.y)
    by_cases hpos : 0 < qdot Q v.y (greedy (enlarge (fR f) (v.μ : ℝ)) σ')
    · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range (n + 1))
        (fun i => enlarge (fR f) (v.μ : ℝ) (pref σ' i)) ⟨0, by simp⟩
      exact ⟨_, VNStep.slide v σ' (pref σ' i0) hv hσ' hpos
        ⟨⟨i0, Nat.lt_succ_iff.mp (Finset.mem_range.mp hi0), rfl⟩,
          fun i hi => hmin i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩⟩
    · exact ⟨_, VNStep.plain v σ' hv hσ' hpos⟩
  · intro l hl
    rcases eq_or_ne l [] with h | h
    · rw [h]
      simp
    have h0 : qdot Q (vnStart f μ W Q σ e o).y (vnStart f μ W Q σ e o).y *
        (((0 : ℕ) : ℝ) + 1) ≤ 1 := by
      have := (unit_b hQ (greedy (enlarge (fR f) (μ : ℝ)) σ)).1
      simp only [Nat.cast_zero, zero_add, mul_one]
      exact this
    have hc := chain_bound hQ hε l _ 0 hl h0 h
    simp only [Nat.cast_zero, zero_add] at hc
    have hlt : (l.length : ℝ) < 1 / ε ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      exact hc
    exact_mod_cast le_trans hlt.le (Nat.le_ceil _)
  · intro v hv
    have hinv : Inv f Q μ v := by
      induction hv with
      | refl => exact inv_start f hsub hf0 μ hμ W hW Q σ e o
      | tail _ hstep ih => exact inv_step f hsub hf0 μ hμ Q hQ ε hε _ _ ih hstep
    intro hle
    exact ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1, hinv.2.2.2.2.2, hle⟩

