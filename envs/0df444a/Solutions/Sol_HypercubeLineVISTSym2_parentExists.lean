-- Prove2me | solution 1 for HypercubeLineVISTSym2_parentExists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:35:59.963127+00:00
-- url     : https://prove2.me/submissions/c5a0b8eb-bdd2-4531-b995-7911b1a55496

import Mathlib

set_option autoImplicit false

namespace HVS2

variable {α K : Type*} [DecidableEq α]

noncomputable def par (a b : α) (c : K → α) (k : K) (v : Sym2 α) : Sym2 α :=
  if v = s(a, b) then s(a, b)
  else if v = s(a, c k) then s(a, b)
  else if a ∈ v ∨ c k ∈ v then s(a, c k)
  else s(v.out.1, c k)

variable {a b : α} {c : K → α}

lemma h_ne_r (hcb : ∀ k, c k ≠ b) (k : K) : s(a, c k) ≠ s(a, b) := by
  intro h; exact hcb k (Sym2.congr_right.mp h)

lemma par_r (k : K) : par a b c k s(a, b) = s(a, b) := by
  unfold par; rw [if_pos rfl]

lemma par_h (hcb : ∀ k, c k ≠ b) (k : K) : par a b c k s(a, c k) = s(a, b) := by
  unfold par; rw [if_neg (h_ne_r hcb k), if_pos rfl]

lemma par_mem (k : K) (w : Sym2 α) (hw : a ∈ w ∨ c k ∈ w) :
    par a b c k w = s(a, b) ∨ par a b c k w = s(a, c k) := by
  by_cases h1 : w = s(a, b)
  · left; unfold par; rw [if_pos h1]
  by_cases h2 : w = s(a, c k)
  · left; unfold par; rw [if_neg h1, if_pos h2]
  right; unfold par; rw [if_neg h1, if_neg h2, if_pos hw]

lemma par_shape (k : K) (v : Sym2 α) :
    par a b c k v = s(a, b) ∨ par a b c k v = s(a, c k) ∨
      par a b c k v = s(v.out.1, c k) := by
  unfold par; split_ifs <;> simp

lemma par_eq_r (hca : ∀ k, c k ≠ a) (hcb : ∀ k, c k ≠ b) (k : K) (v : Sym2 α)
    (h : par a b c k v = s(a, b)) : v = s(a, b) ∨ v = s(a, c k) := by
  unfold par at h
  split_ifs at h with h1 h2 h3
  · left; exact h1
  · right; exact h2
  · exact absurd h (h_ne_r hcb k)
  · exfalso
    have : c k ∈ s(a, b) := h ▸ Sym2.mem_mk_right _ _
    rcases Sym2.mem_iff.mp this with h' | h'
    · exact hca k h'
    · exact hcb k h'

lemma par_adj (k : K) (v : Sym2 α) (hv : v ≠ s(a, b)) :
    ∃ x y1 y2 : α, v = s(x, y1) ∧ par a b c k v = s(x, y2) := by
  by_cases h2 : v = s(a, c k)
  · refine ⟨a, c k, b, h2, ?_⟩
    unfold par; rw [if_neg hv, if_pos h2]
  by_cases h3 : a ∈ v
  · obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp h3
    refine ⟨a, y, c k, hy, ?_⟩
    unfold par; rw [if_neg hv, if_neg h2, if_pos (Or.inl h3)]
  by_cases h4 : c k ∈ v
  · obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp h4
    refine ⟨c k, y, a, hy, ?_⟩
    unfold par; rw [if_neg hv, if_neg h2, if_pos (Or.inr h4), Sym2.eq_swap]
  obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp (Sym2.out_fst_mem v)
  refine ⟨v.out.1, y, c k, hy, ?_⟩
  unfold par
  rw [if_neg hv, if_neg h2, if_neg (by tauto)]

lemma par_two (hcb : ∀ k, c k ≠ b) (k : K) (w : Sym2 α) (hw : a ∈ w ∨ c k ∈ w) :
    par a b c k (par a b c k w) = s(a, b) := by
  rcases par_mem k w hw with h | h
  · rw [h, par_r]
  · rw [h, par_h hcb]

lemma par_mem_par (k : K) (v : Sym2 α) :
    a ∈ par a b c k v ∨ c k ∈ par a b c k v := by
  rcases par_shape (a := a) (b := b) k v with h | h | h <;> rw [h] <;> simp

lemma iter3 (hcb : ∀ k, c k ≠ b) (k : K) (v : Sym2 α) :
    (par a b c k)^[3] v = s(a, b) := by
  show par a b c k (par a b c k (par a b c k v)) = s(a, b)
  exact par_two hcb k _ (par_mem_par k v)

lemma reach (hcb : ∀ k, c k ≠ b) (k : K) (v : Sym2 α) (m : ℕ) :
    (par a b c k)^[m] v = s(a, b) ∨ (par a b c k)^[m] v = v ∨
      (par a b c k)^[m] v = s(a, c k) ∨ (par a b c k)^[m] v = s(v.out.1, c k) := by
  induction m with
  | zero => right; left; rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h | h <;> rw [h]
    · left; exact par_r k
    · rcases par_shape (a := a) (b := b) k v with h' | h' | h'
      · left; exact h'
      · right; right; left; exact h'
      · right; right; right; exact h'
    · left; exact par_h hcb k
    · rcases par_mem (a := a) (b := b) k _ (Or.inr (Sym2.mem_mk_right _ _)) with h' | h'
      · left; exact h'
      · right; right; left; exact h'

lemma key (hc : Function.Injective c) (hca : ∀ k, c k ≠ a) {k l : K} (hkl : k ≠ l)
    (o x y : α) (hx : x = a ∨ x = o) (hy : y = a ∨ y = o)
    (h : s(x, c k) = s(y, c l)) : False := by
  rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact hkl (hc h2)
  · rcases hy with hy | hy
    · exact hca k (h2.trans hy)
    rcases hx with hx | hx
    · exact hca l (h1.symm.trans hx)
    · exact hkl (hc (h2.trans (hy.trans (hx.symm.trans h1))))

lemma cond4 (hc : Function.Injective c) (hca : ∀ k, c k ≠ a) (hcb : ∀ k, c k ≠ b)
    {k l : K} (hkl : k ≠ l) (v u : Sym2 α)
    (hk : ∃ mk : ℕ, (par a b c k)^[mk] v = u) (hl : ∃ ml : ℕ, (par a b c l)^[ml] v = u) :
    u = s(a, b) ∨ u = v := by
  obtain ⟨mk, hmk⟩ := hk
  obtain ⟨ml, hml⟩ := hl
  have Rk := reach (a := a) hcb k v mk
  have Rl := reach (a := a) hcb l v ml
  rw [hmk] at Rk
  rw [hml] at Rl
  rcases Rk with h | h | hk1 | hk1
  · exact Or.inl h
  · exact Or.inr h
  all_goals rcases Rl with h | h | hl1 | hl1
  all_goals first
    | exact Or.inl h
    | exact Or.inr h
    | exact (key hc hca hkl v.out.1 _ _ (Or.inl rfl) (Or.inl rfl) (hk1.symm.trans hl1)).elim
    | exact (key hc hca hkl v.out.1 _ _ (Or.inl rfl) (Or.inr rfl) (hk1.symm.trans hl1)).elim
    | exact (key hc hca hkl v.out.1 _ _ (Or.inr rfl) (Or.inl rfl) (hk1.symm.trans hl1)).elim
    | exact (key hc hca hkl v.out.1 _ _ (Or.inr rfl) (Or.inr rfl) (hk1.symm.trans hl1)).elim

lemma cond5 (hc : Function.Injective c) (hca : ∀ k, c k ≠ a) (hcb : ∀ k, c k ≠ b)
    {k l : K} (hkl : k ≠ l) (v : Sym2 α) (hv : v ≠ s(a, b))
    (h : par a b c k v = s(a, b)) : par a b c l v ≠ s(a, b) := by
  rcases par_eq_r hca hcb k v h with h1 | h1
  · exact absurd h1 hv
  intro h'
  rcases par_eq_r hca hcb l v h' with h2 | h2
  · exact hv h2
  · exact key hc hca hkl a a a (Or.inl rfl) (Or.inl rfl) (h1.symm.trans h2)

lemma two_mul_le_pow : ∀ m : ℕ, 2 * (m + 1) ≤ 2 ^ (m + 1)
  | 0 => by norm_num
  | m + 1 => by
    have := two_mul_le_pow m
    rw [pow_succ]
    omega

end HVS2

theorem solution (n : Nat) (hn : 3 < n) :
    ∀ (rSym2 : Sym2 (Fin n → Bool)) (a b : Fin n → Bool) (d0 : Fin n),
      rSym2 = Sym2.mk a b →
      ∃ parentSym2 : Fin (2 * n - 2) → Sym2 (Fin n → Bool) → Sym2 (Fin n → Bool),
        (∀ k : Fin (2 * n - 2), parentSym2 k rSym2 = rSym2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
          ∃ x y1 y2 : Fin n → Bool, v = Sym2.mk x y1 ∧ parentSym2 k v = Sym2.mk x y2) ∧
        (∀ k : Fin (2 * n - 2), ∀ v : Sym2 (Fin n → Bool),
          ∃ m : Nat, (parentSym2 k)^[m] v = rSym2) ∧
        (∀ k l : Fin (2 * n - 2), k ≠ l →
          ∀ v u : Sym2 (Fin n → Bool),
            (∃ mk : Nat, (parentSym2 k)^[mk] v = u) →
            (∃ ml : Nat, (parentSym2 l)^[ml] v = u) →
            u = rSym2 ∨ u = v) ∧
        (∀ k l : Fin (2 * n - 2), k ≠ l →
          ∀ v : Sym2 (Fin n → Bool), v ≠ rSym2 →
            parentSym2 k v = rSym2 → parentSym2 l v ≠ rSym2) := by
  intro rSym2 a b _ hr
  subst hr
  have hcard : Fintype.card (Fin (2 * n - 2)) ≤
      Fintype.card {x : Fin n → Bool // x ≠ a ∧ x ≠ b} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    have hsub : (Finset.univ : Finset (Fin n → Bool)) ⊆
        Finset.univ.filter (fun x => x ≠ a ∧ x ≠ b) ∪ {a, b} := by
      intro x _
      by_cases hxa : x = a
      · simp [hxa]
      by_cases hxb : x = b
      · simp [hxb]
      simp [hxa, hxb]
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Finset.univ.filter (fun x : Fin n → Bool => x ≠ a ∧ x ≠ b))
      ({a, b} : Finset (Fin n → Bool))
    have h3 : ({a, b} : Finset (Fin n → Bool)).card ≤ 2 := Finset.card_le_two
    have h4 : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      rw [Finset.card_univ]; simp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h5 := HVS2.two_mul_le_pow m
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let c : Fin (2 * n - 2) → (Fin n → Bool) := fun k => (e k).1
  have hc : Function.Injective c := fun i j h => e.injective (Subtype.ext h)
  have hca : ∀ k, c k ≠ a := fun k => (e k).2.1
  have hcb : ∀ k, c k ≠ b := fun k => (e k).2.2
  exact ⟨HVS2.par a b c, fun k => HVS2.par_r k, fun k v hv => HVS2.par_adj k v hv,
    fun k v => ⟨3, HVS2.iter3 hcb k v⟩,
    fun k l hkl v u hk hl => HVS2.cond4 hc hca hcb hkl v u hk hl,
    fun k l hkl v hv h => HVS2.cond5 hc hca hcb hkl v hv h⟩
