-- Prove2me | solution 1 for GeomRescale.lemma_3_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:26:25.929949+00:00
-- url     : https://prove2.me/submissions/590d4bdb-115f-491c-b821-e926aa284918

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_qnorm
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace Aux_GeomRescale_lemma_3_13
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


theorem quad_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((A + B).mulVec x) = x ⬝ᵥ (A.mulVec x) + x ⬝ᵥ (B.mulVec x) := by
  rw [Matrix.add_mulVec, dotProduct_add]

theorem quad_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((c • A).mulVec x) = c * (x ⬝ᵥ (A.mulVec x)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_one {n : ℕ} (x : Fin n → ℝ) :
    x ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ).mulVec x) = ∑ v, x v ^ 2 := by
  rw [Matrix.one_mulVec]
  unfold dotProduct
  exact Finset.sum_congr rfl (fun v _ => by ring)

theorem quad_vmv {n : ℕ} (g x : Fin n → ℝ) :
    x ⬝ᵥ ((Matrix.vecMulVec g g).mulVec x) = (g ⬝ᵥ x) ^ 2 := by
  rw [sq]
  unfold dotProduct
  rw [Finset.sum_mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem quad_fsum {n : ℕ} {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ ((∑ i ∈ s, A i).mulVec x) = ∑ i ∈ s, x ⬝ᵥ ((A i).mulVec x) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]

theorem quad_lsum {n : ℕ} {α : Type} (l : List α) (A : α → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    x ⬝ᵥ (((l.map A).sum).mulVec x) = (l.map (fun a => x ⬝ᵥ ((A a).mulVec x))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, quad_add, ih, List.map_cons, List.sum_cons]

theorem psd_lsum {n : ℕ} {α : Type} (l : List α) (A : α → Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ a ∈ l, (A a).PosSemidef) : ((l.map A).sum).PosSemidef := by
  induction l with
  | nil => simpa using Matrix.PosSemidef.zero
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    exact (h a (List.mem_cons_self)).add (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem vmv_psd {n : ℕ} (g : Fin n → ℝ) : (Matrix.vecMulVec g g).PosSemidef := by
  simpa using Matrix.posSemidef_vecMulVec_self_star g

theorem rescaled_pd {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.PosDef) (data : List ((Fin n → ℝ) × ℝ)) (hw : ∀ p ∈ data, 0 ≤ p.2) :
    (rescaled ε Q R data).PosDef := by
  unfold rescaled
  have hpos : (0 : ℝ) < ((1 + ε) ^ 2)⁻¹ := inv_pos.mpr (by positivity)
  refine Matrix.PosDef.smul (hR.add_posSemidef (psd_lsum _ _ (fun p hp => ?_))) hpos
  exact (vmv_psd p.1).smul (div_nonneg (hw p hp) (sq_nonneg _))

theorem qd_zero {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) {x : Fin n → ℝ}
    (h : qdot Q x x = 0) : x = 0 := by
  by_contra hx
  have := hQ.dotProduct_mulVec_pos hx
  simp only [star_trivial] at this
  unfold qdot at h
  linarith

theorem qd_cs {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (x y : Fin n → ℝ) :
    qdot Q x y ^ 2 ≤ qdot Q x x * qdot Q y y := by
  have h : ∀ t : ℝ, 0 ≤ qdot Q x x - 2 * t * qdot Q x y + t ^ 2 * qdot Q y y := by
    intro t
    have h0 := qd_nonneg hQ (x - t • y)
    simp only [qd_sub_l, qd_sub_r, qd_smul_l, qd_smul_r] at h0
    rw [qd_symm hQ y x] at h0
    nlinarith [h0]
  obtain ⟨a, ha⟩ : ∃ a, a = qdot Q x x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = qdot Q x y := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = qdot Q y y := ⟨_, rfl⟩
  rw [← ha, ← hb, ← hc] at h ⊢
  have hc0 : 0 ≤ c := by rw [hc]; exact qd_nonneg hQ y
  rcases eq_or_lt_of_le hc0 with hc1 | hcpos
  · rw [← hc1]
    by_contra hcon
    push_neg at hcon
    have hb0 : b ≠ 0 := by
      intro hb0
      rw [hb0] at hcon
      simp at hcon
    have h2 := h ((a + 1) / (2 * b))
    rw [← hc1] at h2
    have e : 2 * ((a + 1) / (2 * b)) * b = a + 1 := by
      calc 2 * ((a + 1) / (2 * b)) * b = (a + 1) * ((2 * b) / (2 * b)) := by ring
        _ = a + 1 := by rw [div_self (mul_ne_zero two_ne_zero hb0), mul_one]
    nlinarith [e]
  · have h2 := h (b / c)
    have h3 : 0 ≤ (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c := mul_nonneg h2 hc0
    have ht : b / c * c = b := div_mul_cancel₀ b hcpos.ne'
    have e : (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c = a * c - b ^ 2 := by
      calc (a - 2 * (b / c) * b + (b / c) ^ 2 * c) * c
          = a * c - 2 * b * (b / c * c) + (b / c * c) ^ 2 := by ring
        _ = a * c - b ^ 2 := by rw [ht]; ring
    linarith

theorem dot_le_qnorm {n : ℕ} {Q R : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (hR : R.PosDef)
    (hQR : Q = R⁻¹) (w : Fin n → ℝ) (hw : w ⬝ᵥ R.mulVec w ≤ 1) (x : Fin n → ℝ) :
    x ⬝ᵥ w ≤ qnorm Q x := by
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hQRm : Q * R = 1 := by rw [hQR]; exact Matrix.nonsing_inv_mul R hdet
  have hw' : Q.mulVec (R.mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, hQRm, Matrix.one_mulVec]
  have hT : R.transpose = R := by
    have h := hR.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have e1 : x ⬝ᵥ w = qdot Q x (R.mulVec w) := by
    unfold qdot
    rw [hw']
  have e2 : qdot Q (R.mulVec w) (R.mulVec w) = w ⬝ᵥ R.mulVec w := by
    unfold qdot
    rw [hw', dotProduct_comm]
  have hcs := qd_cs hQ x (R.mulVec w)
  rw [← e1, e2] at hcs
  have hxx := qd_nonneg hQ x
  have hww : 0 ≤ w ⬝ᵥ R.mulVec w := by rw [← e2]; exact qd_nonneg hQ _
  have h1 : (x ⬝ᵥ w) ^ 2 ≤ qdot Q x x := by nlinarith
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h1)

theorem n2sq {n : ℕ} (z : Fin n → ℝ) : norm2 z ^ 2 = ∑ v, z v ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun v _ => sq_nonneg (z v)))

theorem nrm2_nonneg {n : ℕ} (z : Fin n → ℝ) : 0 ≤ norm2 z := Real.sqrt_nonneg _

theorem eps_pos {n : ℕ} (hn : 1 ≤ n) : 0 < eps n := by
  unfold eps
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

theorem list_sum_dot {n : ℕ} {α : Type} (l : List α) (F : α → Fin n → ℝ) (w : Fin n → ℝ) :
    (l.map F).sum ⬝ᵥ w = (l.map (fun a => F a ⬝ᵥ w)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, add_dotProduct, ih, List.map_cons,
      List.sum_cons]

theorem vn_mu_mono {n : ℕ} {f : Finset (Fin n) → ℤ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosDef) {ε : ℝ} {v v' : VN n} (h : VNStep f Q ε v v') : v.μ ≤ v'.μ := by
  cases h with
  | plain σ h1 h2 h3 => exact le_refl _
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
    have h5 : (f W' : ℝ) + v.μ < 0 := by
      rw [← hFW']
      exact hFW
    have h6 : f W' + v.μ < 0 := by exact_mod_cast h5
    show v.μ ≤ -f W'
    omega

theorem upd_pos {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) (y g : Fin n → ℝ)
    (hy : 0 < qdot Q y y) (hc : qdot Q y g ≤ 0) (lam : ℝ)
    (hlam : lam = qdot Q (y - unitQ Q g) y / qnorm Q (y - unitQ Q g) ^ 2)
    (hne : (1 - lam) • y + lam • unitQ Q g ≠ 0) : 0 < lam ∧ lam < 1 ∧ g ≠ 0 := by
  have hcu : qdot Q y (unitQ Q g) ≤ 0 := by
    rw [unit_c]
    exact mul_nonpos_iff.mpr (Or.inl ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), hc⟩)
  have hb0 := qd_nonneg hQ (unitQ Q g)
  have hD : qnorm Q (y - unitQ Q g) ^ 2 =
      qdot Q y y - 2 * qdot Q y (unitQ Q g) + qdot Q (unitQ Q g) (unitQ Q g) := by
    rw [qn_sq hQ]
    simp only [qd_sub_l, qd_sub_r]
    rw [qd_symm hQ (unitQ Q g) y]
    ring
  have hN : qdot Q (y - unitQ Q g) y = qdot Q y y - qdot Q y (unitQ Q g) := by
    rw [qd_sub_l, qd_symm hQ (unitQ Q g) y]
  rw [hD, hN] at hlam
  have hDpos : 0 < qdot Q y y - 2 * qdot Q y (unitQ Q g) + qdot Q (unitQ Q g) (unitQ Q g) := by
    linarith
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact div_pos (by linarith) hDpos
  have hu0 : ¬ (qdot Q (unitQ Q g) (unitQ Q g) = 0 ∧ qdot Q y (unitQ Q g) = 0) := by
    rintro ⟨h1, h2⟩
    have hu : unitQ Q g = 0 := qd_zero hQ h1
    apply hne
    have hl1 : lam = 1 := by
      rw [hlam, h1, h2, mul_zero, sub_zero, add_zero, div_self hy.ne']
    rw [hl1, hu]
    simp
  have hlam1 : lam < 1 := by
    rw [hlam, div_lt_one hDpos]
    by_contra hcon
    push_neg at hcon
    exact hu0 ⟨by linarith, by linarith⟩
  refine ⟨hlam0, hlam1, ?_⟩
  intro hg
  apply hu0
  have hu : unitQ Q g = 0 := by
    rw [hg]
    unfold unitQ
    simp
  rw [hu]
  unfold qdot
  simp

def VInv {n : ℕ} (f : Finset (Fin n) → ℤ) (Q : Matrix (Fin n) (Fin n) ℝ) (v : VN n) : Prop :=
  Inv f Q (max 0 (-f Finset.univ)) v ∧
    (v.y ≠ 0 → ∀ p ∈ v.data, 0 < p.2 ∧ p.1 ≠ 0) ∧
    qdot Q v.y v.y * (v.data.length : ℝ) ≤ 1 ∧
    (v.data.length : ℝ) ≤ 1 + 1 / eps n ^ 2

theorem vinv_start {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (μ : ℤ) (hμ : max 0 (-f Finset.univ) ≤ μ) (W : Finset (Fin n))
    (hW : f W = -μ) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (σ : Equiv.Perm (Fin n))
    (e o : ℕ) : VInv f Q (vnStart f μ W Q σ e o) := by
  have hI := inv_start f hsub hf0 μ hμ W hW Q σ e o
  refine ⟨⟨hμ, hI.2⟩, ?_, ?_, ?_⟩
  · intro hy p hp
    have hp' : p = (greedy (enlarge (fR f) (μ : ℝ)) σ, 1) := List.mem_singleton.mp hp
    rw [hp']
    refine ⟨by norm_num, ?_⟩
    intro hg
    have hg' : greedy (enlarge (fR f) (μ : ℝ)) σ = 0 := hg
    apply hy
    show unitQ Q (greedy (enlarge (fR f) (μ : ℝ)) σ) = 0
    rw [hg']
    unfold unitQ
    simp
  · have := (unit_b hQ (greedy (enlarge (fR f) (μ : ℝ)) σ)).1
    show qdot Q (unitQ Q (greedy (enlarge (fR f) (μ : ℝ)) σ))
      (unitQ Q (greedy (enlarge (fR f) (μ : ℝ)) σ)) *
      (([(greedy (enlarge (fR f) (μ : ℝ)) σ, (1 : ℝ))].length : ℕ) : ℝ) ≤ 1
    simpa using this
  · show (([(greedy (enlarge (fR f) (μ : ℝ)) σ, (1 : ℝ))].length : ℕ) : ℝ) ≤ 1 + 1 / eps n ^ 2
    have : 0 ≤ 1 / eps n ^ 2 := by positivity
    simp only [List.length_singleton, Nat.cast_one]
    linarith

theorem vinv_step {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (v v' : VN n)
    (hV : VInv f Q v) (h : VNStep f Q (eps n) v v') : VInv f Q v' := by
  have hε := eps_pos hn
  obtain ⟨hI, hP, hL1, hL2⟩ := hV
  have hI' := inv_step f hsub hf0 _ (le_refl _) Q hQ (eps n) hε v v' hI h
  have hg := vn_guard h
  have hy : 0 < qdot Q v.y v.y := by
    have := pow_pos (lt_trans hε hg) 2
    rwa [qn_sq hQ] at this
  have hy0 : v.y ≠ 0 := by
    intro h0
    rw [h0] at hy
    unfold qdot at hy
    simp at hy
  have hdec := step_dec hQ hε h
  have hε3 : eps n ^ 2 < qdot Q v.y v.y := by
    have := pow_lt_pow_left₀ hg hε.le two_ne_zero
    rwa [qn_sq hQ] at this
  have hlen : v'.data.length = v.data.length + 1 := by
    cases h with
    | plain σ h1 h2 h3 => simp [vnUpdate]
    | slide σ W' h1 h2 h3 h4 => simp [vnUpdate]
  have ha1 := qd_nonneg hQ v'.y
  have hLpos : (0 : ℝ) ≤ v.data.length := Nat.cast_nonneg _
  refine ⟨hI', ?_, ?_, ?_⟩
  · intro hy' p hp
    cases h with
    | plain σ h1 h2 h3 =>
      have hc : qdot Q v.y (greedy (enlarge (fR f) (v.μ : ℝ)) σ) ≤ 0 := not_lt.mp h3
      obtain ⟨hl0, hl1, hgne⟩ := upd_pos hQ v.y _ hy hc _ rfl hy'
      have hd : (vnUpdate Q (greedy (enlarge (fR f) (v.μ : ℝ)) σ)
          { v with evals := v.evals + n, ops := v.ops + sortCost n + n ^ 2 }).data =
          v.data.map (fun p => (p.1, (1 - (qdot Q (v.y - unitQ Q (greedy (enlarge (fR f)
            (v.μ : ℝ)) σ)) v.y / qnorm Q (v.y - unitQ Q (greedy (enlarge (fR f)
            (v.μ : ℝ)) σ)) ^ 2)) * p.2)) ++
            [(greedy (enlarge (fR f) (v.μ : ℝ)) σ, qdot Q (v.y - unitQ Q (greedy (enlarge (fR f)
            (v.μ : ℝ)) σ)) v.y / qnorm Q (v.y - unitQ Q (greedy (enlarge (fR f)
            (v.μ : ℝ)) σ)) ^ 2)] := rfl
      rw [hd] at hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨hq1, hq2⟩ := hP hy0 q hq
        exact ⟨mul_pos (by linarith) hq1, hq2⟩
      · rw [List.mem_singleton] at hp
        rw [hp]
        exact ⟨hl0, hgne⟩
    | slide σ W' h1 h2 h3 h4 =>
      have hc := slide_neg hQ (enlarge (fR f) (v.μ : ℝ)) (enl_empty _ _) (enl_univ _ _) v.y σ h2
        W' h4
      obtain ⟨hl0, hl1, hgne⟩ := upd_pos hQ v.y _ hy hc _ rfl hy'
      have hd : (vnUpdate Q (patch σ (-(enlarge (fR f) (v.μ : ℝ) W'))
            (greedy (enlarge (fR f) (v.μ : ℝ)) σ))
          { v with
            μ := -f W'
            W := W'
            evals := v.evals + n
            ops := v.ops + sortCost n + n ^ 2 + n }).data =
          v.data.map (fun p => (p.1, (1 - (qdot Q (v.y - unitQ Q (patch σ
            (-(enlarge (fR f) (v.μ : ℝ) W')) (greedy (enlarge (fR f) (v.μ : ℝ)) σ))) v.y /
            qnorm Q (v.y - unitQ Q (patch σ (-(enlarge (fR f) (v.μ : ℝ) W'))
            (greedy (enlarge (fR f) (v.μ : ℝ)) σ))) ^ 2)) * p.2)) ++
            [(patch σ (-(enlarge (fR f) (v.μ : ℝ) W')) (greedy (enlarge (fR f) (v.μ : ℝ)) σ),
              qdot Q (v.y - unitQ Q (patch σ (-(enlarge (fR f) (v.μ : ℝ) W'))
              (greedy (enlarge (fR f) (v.μ : ℝ)) σ))) v.y /
              qnorm Q (v.y - unitQ Q (patch σ (-(enlarge (fR f) (v.μ : ℝ) W'))
              (greedy (enlarge (fR f) (v.μ : ℝ)) σ))) ^ 2)] := rfl
      rw [hd] at hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨hq1, hq2⟩ := hP hy0 q hq
        exact ⟨mul_pos (by linarith) hq1, hq2⟩
      · rw [List.mem_singleton] at hp
        rw [hp]
        exact ⟨hl0, hgne⟩
  · rw [hlen]
    push_cast
    have h3 : qdot Q v'.y v'.y * ((v.data.length : ℝ) + 1) * (1 + qdot Q v.y v.y) ≤
        1 + qdot Q v.y v.y := by
      have := mul_le_mul_of_nonneg_right hdec (show (0 : ℝ) ≤ v.data.length + 1 by linarith)
      nlinarith
    have h4 : 0 < 1 + qdot Q v.y v.y := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul_of_pos_right hcon h4]
  · rw [hlen]
    push_cast
    have h5 : (v.data.length : ℝ) * eps n ^ 2 ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_right hε3.le hLpos]
    have h6 : (v.data.length : ℝ) ≤ 1 / eps n ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact h5
    linarith

def OInv {n : ℕ} (f : Finset (Fin n) → ℤ) (s : St n) : Prop :=
  s.R.PosDef ∧ s.Q = s.R⁻¹ ∧
    (s.mode = Mode.start → s.vn.μ = 0 ∧ s.Γ = [] ∧ s.i = 0 ∧ s.R = 1) ∧
    (s.mode ≠ Mode.start → max 0 (-f Finset.univ) ≤ s.vn.μ ∧ f s.vn.W = -s.vn.μ) ∧
    (∀ g ∈ s.Γ, g ∈ baseB (enlarge (fR f) (s.vn.μ : ℝ)) ∧ g ≠ 0) ∧
    (∃ κ : (Fin n → ℝ) → ℝ, (∀ g ∈ s.Γ, 0 < κ g) ∧
      s.R = (1 / (1 + eps n) ^ (2 * s.i)) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        ∑ g ∈ s.Γ.toFinset, κ g • Matrix.vecMulVec g g) ∧
    ((s.mode = Mode.inner ∨ s.mode = Mode.afterCall) → VInv f s.Q s.vn) ∧
    (s.mode = Mode.afterCall → qnorm s.Q s.vn.y ≤ eps n) ∧
    (∀ w : Fin n → ℝ, (∀ x ∈ baseB (enlarge (fR f) (s.vn.μ : ℝ)), 0 ≤ w ⬝ᵥ x) →
      norm2 w ≤ 1 → w ⬝ᵥ s.R.mulVec w ≤ 1)

theorem oinv_init {n : ℕ} (f : Finset (Fin n) → ℤ) : OInv f (init n) := by
  refine ⟨Matrix.PosDef.one, (inv_one).symm, fun _ => ⟨rfl, rfl, rfl, rfl⟩,
    fun h => (h rfl).elim, fun g hg => (by cases hg), ⟨fun _ => 0, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    cases hg
  · show (1 : Matrix (Fin n) (Fin n) ℝ) = (1 / (1 + eps n) ^ (2 * 0)) • 1 +
      ∑ g ∈ ([] : List (Fin n → ℝ)).toFinset, (0 : ℝ) • Matrix.vecMulVec g g
    simp
  · rintro (h | h) <;> cases h
  · intro h
    cases h
  · intro w _ hw
    show w ⬝ᵥ (1 : Matrix (Fin n) (Fin n) ℝ).mulVec w ≤ 1
    rw [quad_one, ← n2sq]
    have := nrm2_nonneg w
    nlinarith

theorem kappa_regroup {n : ℕ} (S : Finset (Fin n → ℝ)) (d : (Fin n → ℝ) × ℝ → ℝ)
    (data : List ((Fin n → ℝ) × ℝ)) (hS : ∀ p ∈ data, p.1 ∈ S) :
    ∑ g ∈ S, (data.map (fun p => if p.1 = g then d p else 0)).sum • Matrix.vecMulVec g g =
      (data.map (fun p => d p • Matrix.vecMulVec p.1 p.1)).sum := by
  induction data with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib]
    rw [ih (fun q hq => hS q (List.mem_cons_of_mem p hq))]
    congr 1
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), zero_smul]
    · intro h
      exact absurd (hS p (by simp)) h

theorem kappa_step {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (Q R : Matrix (Fin n) (Fin n) ℝ)
    (Γ : List (Fin n → ℝ)) (i : ℕ) (κ : (Fin n → ℝ) → ℝ) (hκ : ∀ g ∈ Γ, 0 < κ g)
    (hR : R = (1 / (1 + ε) ^ (2 * i)) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      ∑ g ∈ Γ.toFinset, κ g • Matrix.vecMulVec g g)
    (data : List ((Fin n → ℝ) × ℝ)) (hd : ∀ p ∈ data, 0 < p.2 / qnorm Q p.1 ^ 2) :
    ∃ κ' : (Fin n → ℝ) → ℝ, (∀ g ∈ Γ ++ data.map Prod.fst, 0 < κ' g) ∧
      rescaled ε Q R data = (1 / (1 + ε) ^ (2 * (i + 1))) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        ∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, κ' g • Matrix.vecMulVec g g := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((1 + ε) ^ 2)⁻¹ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  let d : (Fin n → ℝ) × ℝ → ℝ := fun p => p.2 / qnorm Q p.1 ^ 2
  let A : (Fin n → ℝ) → ℝ := fun g => if g ∈ Γ then κ g else 0
  let B : (Fin n → ℝ) → ℝ := fun g => (data.map (fun p => if p.1 = g then d p else 0)).sum
  have hB0 : ∀ g, 0 ≤ B g := by
    intro g
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact (hd p hp).le
    · exact le_refl _
  have hA0 : ∀ g, 0 ≤ A g := by
    intro g
    show 0 ≤ (if g ∈ Γ then κ g else 0)
    split_ifs with h
    · exact (hκ g h).le
    · exact le_refl _
  refine ⟨fun g => c * (A g + B g), ?_, ?_⟩
  · intro g hg
    apply mul_pos hcpos
    rcases List.mem_append.mp hg with hg | hg
    · have : A g = κ g := if_pos hg
      have := hκ g hg
      have := hB0 g
      linarith
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      have h1 : d p ≤ B p.1 := by
        apply List.single_le_sum
        · intro x hx
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
          split_ifs
          · exact (hd q hq).le
          · exact le_refl _
        · exact List.mem_map.mpr ⟨p, hp, if_pos rfl⟩
      have h2 := hd p hp
      have := hA0 p.1
      show 0 < A p.1 + B p.1
      have : 0 < d p := h2
      linarith
  · beta_reduce
    unfold rescaled
    rw [hR, ← hc]
    have hsplit : ∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, (c * (A g + B g)) •
        Matrix.vecMulVec g g =
        c • (∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, A g • Matrix.vecMulVec g g +
          ∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, B g • Matrix.vecMulVec g g) := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [smul_add, smul_smul, smul_smul, ← add_smul, mul_add]
    rw [hsplit]
    have hA : ∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, A g • Matrix.vecMulVec g g =
        ∑ g ∈ Γ.toFinset, κ g • Matrix.vecMulVec g g := by
      symm
      apply Finset.sum_subset_zero_on_sdiff
      · intro g hg
        rw [List.mem_toFinset] at hg ⊢
        exact List.mem_append_left _ hg
      · intro g hg
        rw [Finset.mem_sdiff, List.mem_toFinset, List.mem_toFinset] at hg
        show (if g ∈ Γ then κ g else 0) • Matrix.vecMulVec g g = 0
        rw [if_neg hg.2, zero_smul]
      · intro g hg
        rw [List.mem_toFinset] at hg
        show κ g • Matrix.vecMulVec g g = (if g ∈ Γ then κ g else 0) • Matrix.vecMulVec g g
        rw [if_pos hg]
    have hBs : ∑ g ∈ (Γ ++ data.map Prod.fst).toFinset, B g • Matrix.vecMulVec g g =
        (data.map (fun p => (p.2 / qnorm Q p.1 ^ 2) • Matrix.vecMulVec p.1 p.1)).sum := by
      apply kappa_regroup
      intro p hp
      rw [List.mem_toFinset]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have hcoef : (1 / (1 + ε) ^ (2 * (i + 1)) : ℝ) = c * (1 / (1 + ε) ^ (2 * i)) := by
      rw [hc, show 2 * (i + 1) = 2 * i + 2 by ring, pow_add, one_div, one_div, mul_inv]
      ring
    rw [hA, hBs, hcoef]
    simp only [smul_add, smul_smul, add_assoc]

theorem ell_step {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (Q R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef)
    (hQR : Q = R⁻¹) (data : List ((Fin n → ℝ) × ℝ)) (y : Fin n → ℝ)
    (hy : y = (data.map (fun p => p.2 • unitQ Q p.1)).sum) (hq : qnorm Q y ≤ ε)
    (hw0 : ∀ p ∈ data, 0 ≤ p.2) (w : Fin n → ℝ) (hwR : w ⬝ᵥ R.mulVec w ≤ 1)
    (hwB : ∀ p ∈ data, 0 ≤ p.1 ⬝ᵥ w) :
    w ⬝ᵥ (rescaled ε Q R data).mulVec w ≤ 1 := by
  have hQ : Q.PosDef := by rw [hQR]; exact hR.inv
  have ht : ∀ p ∈ data, (qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w) ≤ 1 ∧
      0 ≤ (qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w) := by
    intro p hp
    have h1 := dot_le_qnorm hQ hR hQR w hwR p.1
    have h2 := hwB p hp
    have h3 : 0 ≤ qnorm Q p.1 := Real.sqrt_nonneg _
    refine ⟨?_, mul_nonneg (inv_nonneg.mpr h3) h2⟩
    rcases eq_or_lt_of_le h3 with h4 | h4
    · rw [← h4, inv_zero, zero_mul]
      exact zero_le_one
    · rw [inv_mul_le_iff₀ h4]
      linarith
  have hterm : ∀ p ∈ data, w ⬝ᵥ ((p.2 / qnorm Q p.1 ^ 2) • Matrix.vecMulVec p.1 p.1).mulVec w ≤
      p.2 * ((qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w)) := by
    intro p hp
    rw [quad_smul, quad_vmv]
    obtain ⟨h1, h2⟩ := ht p hp
    have e : p.2 / qnorm Q p.1 ^ 2 * (p.1 ⬝ᵥ w) ^ 2 =
        p.2 * ((qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w)) ^ 2 := by
      rw [div_eq_mul_inv, mul_pow, inv_pow]
      ring
    rw [e]
    have h4 : ((qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w)) ^ 2 ≤ (qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w) := by
      nlinarith
    exact mul_le_mul_of_nonneg_left h4 (hw0 p hp)
  have hsum : (data.map (fun p => p.2 * ((qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w)))).sum = y ⬝ᵥ w := by
    rw [hy, list_sum_dot]
    congr 1
    apply List.map_congr_left
    intro p _
    unfold unitQ
    rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hyw : y ⬝ᵥ w ≤ ε := le_trans (dot_le_qnorm hQ hR hQR w hwR y) hq
  have hL : (data.map (fun p => w ⬝ᵥ ((p.2 / qnorm Q p.1 ^ 2) •
      Matrix.vecMulVec p.1 p.1).mulVec w)).sum ≤ ε := by
    calc _ ≤ (data.map (fun p => p.2 * ((qnorm Q p.1)⁻¹ * (p.1 ⬝ᵥ w)))).sum :=
          List.sum_le_sum hterm
      _ = y ⬝ᵥ w := hsum
      _ ≤ ε := hyw
  have hq2 : w ⬝ᵥ ((data.map (fun p => (p.2 / qnorm Q p.1 ^ 2) •
      Matrix.vecMulVec p.1 p.1)).sum).mulVec w ≤ ε := by
    rw [quad_lsum]
    exact hL
  unfold rescaled
  rw [quad_smul, quad_add]
  have hpos : (0 : ℝ) < (1 + ε) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  nlinarith [hq2, hwR]

theorem oinv_step {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (s s' : St n) (hI : OInv f s) (h : Step f Λ s s') :
    OInv f s' := by
  obtain ⟨hR, hQR, h3, h4, h5, h6, h7, h8, h9⟩ := hI
  have hQ : s.Q.PosDef := by rw [hQR]; exact hR.inv
  have hε := eps_pos hn
  cases h with
  | start hm =>
    obtain ⟨hμ0, hΓ0, hi0, hR1⟩ := h3 hm
    refine ⟨hR, hQR, fun h => (by cases h), fun _ => ⟨le_refl _, ?_⟩, ?_, h6, ?_, ?_, ?_⟩
    · show f (if f Finset.univ < 0 then Finset.univ else ∅) = -max 0 (-f Finset.univ)
      split_ifs with hfu
      · rw [max_eq_right (by omega)]
        ring
      · rw [hf0, max_eq_left (by omega)]
        simp
    · intro g hg
      have hg' : g ∈ s.Γ := hg
      rw [hΓ0] at hg'
      cases hg'
    · rintro (h | h) <;> cases h
    · intro h
      cases h
    · intro w _ hw
      show w ⬝ᵥ s.R.mulVec w ≤ 1
      rw [hR1, quad_one, ← n2sq]
      have := nrm2_nonneg w
      nlinarith
  | finish hm hT =>
    have h4' := h4 (by rw [hm]; intro h; cases h)
    refine ⟨hR, hQR, fun h => (by cases h), fun _ => h4', h5, h6, ?_, ?_, h9⟩
    · rintro (h | h) <;> cases h
    · intro h
      cases h
  | call σ hm hT =>
    have h4' := h4 (by rw [hm]; intro h; cases h)
    refine ⟨hR, hQR, fun h => (by cases h), fun _ => h4', h5, h6, ?_, ?_, h9⟩
    · intro _
      exact vinv_start hn f hsub hf0 s.vn.μ h4'.1 s.vn.W h4'.2 s.Q hQ σ s.vn.evals s.vn.ops
    · intro h
      cases h
  | iterate v' hm hv =>
    have hV := h7 (Or.inl hm)
    have hV' := vinv_step hn f hsub hf0 s.Q hQ s.vn v' hV hv
    have hmono := vn_mu_mono hQ hv
    have hmono' : (s.vn.μ : ℝ) ≤ (v'.μ : ℝ) := by exact_mod_cast hmono
    refine ⟨hR, hQR, ?_, ?_, ?_, h6, fun _ => hV', ?_, ?_⟩
    · intro h
      have h' : s.mode = Mode.start := h
      rw [hm] at h'
      cases h'
    · intro _
      exact ⟨hV'.1.1, hV'.1.2.1⟩
    · intro g hg
      obtain ⟨hgB, hg0⟩ := h5 g hg
      exact ⟨baseB_mono _ hmono' hgB, hg0⟩
    · intro h
      have h' : s.mode = Mode.afterCall := h
      rw [hm] at h'
      cases h'
    · intro w hw hw1
      exact h9 w (fun x hx => hw x (baseB_mono _ hmono' hx)) hw1
  | exit hm hq =>
    have h4' := h4 (by rw [hm]; intro h; cases h)
    refine ⟨hR, hQR, fun h => (by cases h), fun _ => h4', h5, h6, fun _ => h7 (Or.inl hm),
      fun _ => hq, h9⟩
  | stop hm hy =>
    have h4' := h4 (by rw [hm]; intro h; cases h)
    refine ⟨hR, hQR, fun h => (by cases h), fun _ => h4', h5, h6, ?_, ?_, h9⟩
    · rintro (h | h) <;> cases h
    · intro h
      cases h
  | rescale hm hy =>
    have h4' := h4 (by rw [hm]; intro h; cases h)
    obtain ⟨hInv, hP, hL1, hL2⟩ := h7 (Or.inr hm)
    obtain ⟨_, _, hB, hw, hs, hyy⟩ := hInv
    have hq := h8 hm
    have hP' := hP hy
    obtain ⟨κ, hκ, hRκ⟩ := h6
    have hd : ∀ p ∈ s.vn.data, 0 < p.2 / qnorm s.Q p.1 ^ 2 := by
      intro p hp
      obtain ⟨h1, h2⟩ := hP' p hp
      have h3 : 0 < qdot s.Q p.1 p.1 := by
        rcases eq_or_lt_of_le (qd_nonneg hQ p.1) with h5 | h5
        · exact absurd (qd_zero hQ h5.symm) h2
        · exact h5
      rw [qn_sq hQ]
      exact div_pos h1 h3
    obtain ⟨κ', hκ', hR'⟩ := kappa_step (eps n) hε.le s.Q s.R s.Γ s.i κ hκ hRκ s.vn.data hd
    refine ⟨rescaled_pd (eps n) hε.le s.Q s.R hR s.vn.data hw, rfl, fun h => (by cases h),
      fun _ => h4', ?_, ⟨κ', hκ', hR'⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h5 g hg
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
        exact ⟨hB p hp, (hP' p hp).2⟩
    · rintro (h | h) <;> cases h
    · intro h
      cases h
    · intro w hwS hw1
      exact ell_step (eps n) hε.le s.Q s.R hR hQR s.vn.data s.vn.y hyy hq hw w (h9 w hwS hw1)
        (fun p hp => by rw [dotProduct_comm]; exact hwS p.1 (hB p hp))

theorem oinv_reach {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (s : St n) (hs : Reachable f Λ s) : OInv f s := by
  induction hs with
  | refl => exact oinv_init f
  | tail _ hstep ih => exact oinv_step hn f hsub hf0 Λ _ _ ih hstep

theorem dsq' {n : ℕ} (v : Fin n → ℝ) : norm2 v ^ 2 = v ⬝ᵥ v := by
  rw [n2sq]
  unfold dotProduct
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem norm2_pos3 {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < norm2 x := by
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hx
  unfold norm2
  apply Real.sqrt_pos.mpr
  have h1 : x v ^ 2 ≤ ∑ u, x u ^ 2 :=
    Finset.single_le_sum (f := fun u => x u ^ 2) (fun u _ => sq_nonneg (x u)) (Finset.mem_univ v)
  have h2 : 0 < x v ^ 2 := by
    have : x v ≠ 0 := hv
    positivity
  linarith

theorem trace_Q_vmv {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    (Q * Matrix.vecMulVec g g).trace = qdot Q g g := by
  unfold Matrix.trace qdot
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem amgm_det {n : ℕ} (hn : 1 ≤ n) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    R.det ^ (1 / (n : ℝ)) ≤ R.trace / n := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos' : (0 : ℝ) < n := by linarith
  have hn0 : (n : ℝ) ≠ 0 := hNpos'.ne'
  have hpos : ∀ i, 0 < hR.1.eigenvalues i := hR.eigenvalues_pos
  have hdet : R.det = ∏ i, hR.1.eigenvalues i := by
    rw [hR.1.det_eq_prod_eigenvalues]
    exact Finset.prod_congr rfl (fun i _ => by simp)
  have htr : R.trace = ∑ i, hR.1.eigenvalues i := by
    rw [hR.1.trace_eq_sum_eigenvalues]
    exact Finset.sum_congr rfl (fun i _ => by simp)
  have hw : ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hn0]
  have hg : ∏ i ∈ (Finset.univ : Finset (Fin n)), hR.1.eigenvalues i ^ (1 / (n : ℝ)) ≤
      ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * hR.1.eigenvalues i :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / (n : ℝ)) hR.1.eigenvalues
      (fun i _ => le_of_lt (one_div_pos.mpr hNpos')) hw (fun i _ => (hpos i).le)
  rw [Real.finsetProd_rpow Finset.univ hR.1.eigenvalues (fun i _ => (hpos i).le)] at hg
  rw [hdet, htr]
  have e : ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * hR.1.eigenvalues i =
      (∑ i, hR.1.eigenvalues i) / n := by
    rw [← Finset.mul_sum]
    ring
  rw [e] at hg
  exact hg

end Aux_GeomRescale_lemma_3_13

open GeomRescale Aux_GeomRescale_lemma_3_13 in
theorem solution {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s : St n) (hs : Reachable f Λ s)
    (hΓ : s.Γ ≠ []) :
    ∃ g ∈ s.Γ, qnorm s.Q g * √(s.R.det ^ (1 / (n : ℝ)) - 1) ≤ norm2 g := by
  obtain ⟨hRpd, hQR, _, _, h5, ⟨κ, hκ, hR⟩, _⟩ := oinv_reach hn f hsub hf0 Λ s hs
  have hQ : s.Q.PosDef := by rw [hQR]; exact hRpd.inv
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 + eps n) ^ (2 * s.i) := ⟨_, rfl⟩
  rw [← hc] at hR
  have hε := eps_pos hn
  have hpow : (1 : ℝ) ≤ (1 + eps n) ^ (2 * s.i) := one_le_pow₀ (show (1 : ℝ) ≤ 1 + eps n by linarith)
  have hpow0 : (0 : ℝ) < (1 + eps n) ^ (2 * s.i) := by linarith
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg zero_le_one hpow0.le
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hpow0]
    exact hpow
  -- traces
  have htrR : s.R.trace = c * n + ∑ g ∈ s.Γ.toFinset, κ g * norm2 g ^ 2 := by
    rw [hR, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Matrix.trace_sum,
      Fintype.card_fin, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul, dsq']
  have hdet : IsUnit s.R.det := (Matrix.isUnit_iff_isUnit_det s.R).mp hRpd.isUnit
  have hQRm : s.Q * s.R = 1 := by rw [hQR]; exact Matrix.nonsing_inv_mul s.R hdet
  have htrQR : (s.Q * s.R).trace = n := by rw [hQRm, Matrix.trace_one, Fintype.card_fin]
  have htrQR2 : (s.Q * s.R).trace =
      c * s.Q.trace + ∑ g ∈ s.Γ.toFinset, κ g * qdot s.Q g g := by
    rw [hR, mul_add, Matrix.mul_smul, mul_one, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      Finset.mul_sum, Matrix.trace_sum]
    congr 1
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_Q_vmv]
  have htrQ : 0 ≤ s.Q.trace := by
    unfold Matrix.trace
    exact Finset.sum_nonneg (fun i _ => le_of_lt hQ.diag_pos)
  have hb : ∑ g ∈ s.Γ.toFinset, κ g * qdot s.Q g g ≤ n := by
    have := mul_nonneg hc0 htrQ
    linarith
  have hamgm := amgm_det hn s.R hRpd
  rw [htrR] at hamgm
  -- choose the minimiser
  have hne : s.Γ.toFinset.Nonempty := by
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil s.Γ hΓ
    exact ⟨g, List.mem_toFinset.mpr hg⟩
  obtain ⟨g0, hg0, hmin⟩ := Finset.exists_min_image s.Γ.toFinset
    (fun g => qdot s.Q g g / norm2 g ^ 2) hne
  have hg0Γ : g0 ∈ s.Γ := List.mem_toFinset.mp hg0
  have hg0n := norm2_pos3 (h5 g0 hg0Γ).2
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = qdot s.Q g0 g0 / norm2 g0 ^ 2 := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg (qd_nonneg hQ g0) (sq_nonneg _)
  have hqm : qdot s.Q g0 g0 = m * norm2 g0 ^ 2 := by
    rw [hm, div_mul_cancel₀ _ (pow_ne_zero 2 hg0n.ne')]
  have hma : m * ∑ g ∈ s.Γ.toFinset, κ g * norm2 g ^ 2 ≤
      ∑ g ∈ s.Γ.toFinset, κ g * qdot s.Q g g := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun g hg => ?_)
    have hgΓ : g ∈ s.Γ := List.mem_toFinset.mp hg
    have h1 : m ≤ qdot s.Q g g / norm2 g ^ 2 := by rw [hm]; exact hmin g hg
    have h2 := norm2_pos3 (h5 g hgΓ).2
    have h3 : 0 ≤ κ g * norm2 g ^ 2 := mul_nonneg (hκ g hgΓ).le (sq_nonneg _)
    have h4 : m * (κ g * norm2 g ^ 2) ≤ qdot s.Q g g / norm2 g ^ 2 * (κ g * norm2 g ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h3
    have h5' : qdot s.Q g g / norm2 g ^ 2 * (κ g * norm2 g ^ 2) = κ g * qdot s.Q g g := by
      calc qdot s.Q g g / norm2 g ^ 2 * (κ g * norm2 g ^ 2)
          = κ g * qdot s.Q g g * (norm2 g ^ 2 / norm2 g ^ 2) := by ring
        _ = κ g * qdot s.Q g g := by rw [div_self (pow_ne_zero 2 h2.ne'), mul_one]
    linarith
  -- combine
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = s.R.det ^ (1 / (n : ℝ)) := ⟨_, rfl⟩
  rw [← hD] at hamgm ⊢
  have hDn : (D - 1) * n ≤ ∑ g ∈ s.Γ.toFinset, κ g * norm2 g ^ 2 := by
    rw [le_div_iff₀ hNpos] at hamgm
    have h1 := mul_le_mul_of_nonneg_right hc1 hNpos.le
    have e : (D - 1) * n = D * n - n := by ring
    linarith
  have hmD : m * (D - 1) ≤ 1 := by
    have h1 : m * ((D - 1) * n) ≤ m * ∑ g ∈ s.Γ.toFinset, κ g * norm2 g ^ 2 :=
      mul_le_mul_of_nonneg_left hDn hm0
    have e : (m * (D - 1) - 1) * n = m * ((D - 1) * n) - n := by ring
    have h2 : (m * (D - 1) - 1) * n ≤ 0 := by linarith
    by_contra hcon
    push_neg at hcon
    have h3 : 0 < (m * (D - 1) - 1) * n := mul_pos (by linarith) hNpos
    linarith
  refine ⟨g0, hg0Γ, ?_⟩
  rcases le_or_gt D 1 with hD1 | hD1
  · rw [Real.sqrt_eq_zero_of_nonpos (show D - 1 ≤ 0 by linarith), mul_zero]
    exact nrm2_nonneg g0
  · have hq0 := qd_nonneg hQ g0
    have e1 : qnorm s.Q g0 * √(D - 1) = √(qdot s.Q g0 g0 * (D - 1)) := by
      show √(qdot s.Q g0 g0) * √(D - 1) = _
      rw [Real.sqrt_mul hq0]
    rw [e1]
    have e2 : norm2 g0 = √(norm2 g0 ^ 2) := (Real.sqrt_sq (nrm2_nonneg g0)).symm
    rw [e2]
    apply Real.sqrt_le_sqrt
    rw [hqm]
    have h6 : 0 ≤ norm2 g0 ^ 2 := sq_nonneg _
    have h7 := mul_le_mul_of_nonneg_right hmD h6
    have e : m * norm2 g0 ^ 2 * (D - 1) = m * (D - 1) * norm2 g0 ^ 2 := by ring
    linarith

