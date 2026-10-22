-- Prove2me | solution 1 for LLLFactor.Reduction.step_preserves_situation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:12:02.169846+00:00
-- url     : https://prove2.me/submissions/b95a484c-9d4b-4c9e-a776-b5ecba5e6e42

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm



namespace LLLFactor.Reduction
open LLLFactor.RedBasis

section GS
variable {n : ℕ}

lemma gs_orth (b : Fin n → Vec n) {i j : Fin n} (h : i ≠ j) :
    inner ℝ (gs b i) (gs b j) = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal ℝ b h

lemma mu_eq (b : Fin n → Vec n) (i j : Fin n) :
    mu b i j = inner ℝ (gs b j) (b i) / inner ℝ (gs b j) (gs b j) := by
  unfold mu; rw [real_inner_comm]

lemma b_eq (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
  have h := InnerProductSpace.gramSchmidt_def'' ℝ b i
  conv_lhs => rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mu_eq]
  simp only [gs, real_inner_self_eq_norm_sq]
  simp

lemma proj_id (b : Fin n → Vec n) (i : Fin n) (δ : Vec n)
    (hδ : δ ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∑ j ∈ Finset.Iio i, (inner ℝ (gs b j) δ / inner ℝ (gs b j) (gs b j)) • gs b j = δ := by
  induction hδ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : l ∈ Finset.Iio i := by simpa using hl
    rw [Finset.sum_eq_single_of_mem l hl']
    · by_cases h0 : gs b l = 0
      · simp [h0]
      · have : inner ℝ (gs b l) (gs b l) ≠ 0 := by simpa using h0
        rw [div_self this, one_smul]
    · intro j _ hj
      rw [gs_orth b hj, zero_div, zero_smul]
  | zero => simp
  | add x y _ _ ihx ihy =>
    simp only [inner_add_right, add_div, add_smul, Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ihx =>
    simp only [inner_smul_right, mul_div_assoc, mul_smul, ← Finset.smul_sum, ihx]

lemma gs_shift (b b' : Fin n → Vec n) (t : Fin n)
    (h : ∀ i ≤ t, b' i - b i ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∀ i ≤ t, gs b' i = gs b i := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  intro hi
  have key : ∀ j ∈ Finset.Iio i, gs b' j = gs b j := fun j hj =>
    ih j (Finset.mem_Iio.1 hj) ((Finset.mem_Iio.1 hj).le.trans hi)
  have h1 := b_eq b i
  have h2 := b_eq b' i
  have hp := proj_id b i (b' i - b i) (h i hi)
  have hb' : b' i = b i + (b' i - b i) := by abel
  have e1 : b i - gs b i = ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
    rw [sub_eq_iff_eq_add']; exact h1
  have hsum : ∑ j ∈ Finset.Iio i, mu b' i j • gs b' j =
      (b i - gs b i) + (b' i - b i) := by
    rw [← hp, e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mu_eq, mu_eq, key j hj, ← add_smul, ← add_div, ← inner_add_right, add_sub_cancel]
  have : gs b' i = gs b i := by
    have := h2
    rw [hsum] at this
    have h3 : gs b' i = b' i - ((b i - gs b i) + (b' i - b i)) := by
      rw [eq_sub_iff_add_eq]; exact this.symm
    rw [h3]; abel
  exact this


lemma gs_prefix (b b' : Fin n → Vec n) (t : Fin n) (h : ∀ j ≤ t, b' j = b j) :
    ∀ i ≤ t, gs b' i = gs b i :=
  gs_shift b b' t (fun i hi => by rw [h i hi, sub_self]; exact Submodule.zero_mem _)

lemma reduceBy_self (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    reduceBy c κ l r κ = c κ - (r : ℝ) • c l := by
  simp [reduceBy]

lemma reduceBy_ne (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) (j : Fin n) (h : j ≠ κ) :
    reduceBy c κ l r j = c j := by
  simp [reduceBy, Function.update_of_ne h]

lemma gs_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i : Fin n) :
    gs (reduceBy c κ l r) i = gs c i := by
  refine gs_shift c (reduceBy c κ l r) i ?_ i le_rfl
  intro i' _
  by_cases h : i' = κ
  · subst h
    rw [reduceBy_self]
    have h1 : c l ∈ Submodule.span ℝ (gs c '' Set.Iic l) :=
      InnerProductSpace.mem_span_gramSchmidt ℝ c (le_refl l)
    have h2 : c l ∈ Submodule.span ℝ (gs c '' Set.Iio i') :=
      Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.2 hl)) h1
    have : c i' - (r : ℝ) • c l - c i' = -((r : ℝ) • c l) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ h2)
  · rw [reduceBy_ne c κ l r i' h, sub_self]; exact Submodule.zero_mem _

lemma mu_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i j : Fin n) :
    mu (reduceBy c κ l r) i j = if i = κ then mu c κ j - r * mu c l j else mu c i j := by
  rw [mu_eq, gs_reduceBy c κ l hl]
  by_cases h : i = κ
  · subst h
    rw [if_pos rfl, reduceBy_self, mu_eq, mu_eq, inner_sub_right, real_inner_smul_right, sub_div,
      mul_div_assoc]
  · rw [if_neg h, reduceBy_ne c κ l r i h, mu_eq]

lemma mu_self (c : Fin n → Vec n) (l : Fin n) (h : gs c l ≠ 0) : mu c l l = 1 := by
  rw [mu_eq]
  have h1 := b_eq c l
  have h2 : inner ℝ (gs c l) (c l) = inner ℝ (gs c l) (gs c l) := by
    conv_lhs => rw [h1]
    rw [inner_add_right, inner_sum]
    have : ∑ x ∈ Finset.Iio l, inner ℝ (gs c l) (mu c l x • gs c x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [real_inner_smul_right, gs_orth c (Finset.mem_Iio.1 hx).ne', mul_zero]
    rw [this, add_zero]
  rw [h2]
  exact div_self (by simpa using h)

lemma mu_zero_of_lt (c : Fin n → Vec n) {i j : Fin n} (h : i < j) : mu c i j = 0 := by
  have := InnerProductSpace.gramSchmidt_inv_triangular ℝ c h
  rw [mu_eq]; change inner ℝ (InnerProductSpace.gramSchmidt ℝ c j) (c i) = 0 at this
  rw [show inner ℝ (gs c j) (c i) = 0 from this, zero_div]


lemma Sit_mono {b : Fin n → Vec n} {k k' : ℕ} (h : Situation b k) (hk : k' ≤ k) :
    Situation b k' :=
  ⟨fun i j hji hik => h.1 i j hji (by omega), fun i h2 hik hin => h.2 i h2 (by omega) hin⟩

lemma Cond120_congr {b b' : Fin n → Vec n} {i : ℕ} (hbb : ∀ j : Fin n, (j : ℕ) < i → b' j = b j)
    (h : Cond120 b i) : Cond120 b' i := by
  obtain ⟨hi, h0⟩ := h
  refine ⟨hi, ?_⟩
  have hg : ∀ m : Fin n, (m : ℕ) < i → gs b' m = gs b m := fun m hm =>
    gs_prefix b b' m (fun j hj => hbb j (lt_of_le_of_lt hj hm)) m le_rfl
  have e1 := hg ⟨i - 1, by omega⟩ (by simp; omega)
  have e2 := hg ⟨i - 2, by omega⟩ (by simp; omega)
  have e3 : mu b' ⟨i - 1, by omega⟩ ⟨i - 2, by omega⟩ = mu b ⟨i - 1, by omega⟩ ⟨i - 2, by omega⟩ := by
    rw [mu_eq, mu_eq, e2, hbb ⟨i - 1, by omega⟩ (by simp; omega)]
  rw [e1, e2, e3]
  exact h0

lemma Sit_congr {b b' : Fin n → Vec n} {k : ℕ} (hbb : ∀ j : Fin n, (j : ℕ) + 1 < k → b' j = b j)
    (h : Situation b k) : Situation b' k := by
  constructor
  · intro i j hji hik
    have := h.1 i j hji hik
    have e2 : gs b' j = gs b j :=
      gs_prefix b b' j (fun m hm => hbb m (by have : (m:ℕ) ≤ j := hm; have : (j:ℕ) < i := hji; omega))
        j le_rfl
    rw [mu_eq, e2, hbb i hik, ← mu_eq]
    exact this
  · intro i h2 hik hin
    exact Cond120_congr (fun j hj => hbb j (by omega)) (h.2 i h2 hik hin)

lemma achieve118_cases {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') :
    (b' = b ∧ ∀ (hk : 2 ≤ k ∧ k ≤ n),
        |mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2) ∨
    (∃ (hk : 2 ≤ k ∧ k ≤ n) (r : ℤ),
        b' = reduceBy b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ r ∧
        IsNearestInt r (mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩)) := by
  unfold Achieve118 at h
  split_ifs at h with hk
  · rcases h with ⟨h1, h2⟩ | ⟨h1, r, h2, h3⟩
    · left; exact ⟨h2, fun _ => h1⟩
    · right; exact ⟨hk, r, h3, h2⟩
  · left; exact ⟨h, fun hk' => absurd hk' hk⟩

lemma achieve118_ne {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') (j : Fin n)
    (hj : (j : ℕ) ≠ k - 1) : b' j = b j := by
  rcases achieve118_cases h with ⟨h1, _⟩ | ⟨hk, r, h1, _⟩
  · rw [h1]
  · rw [h1, reduceBy_ne]
    intro e; apply hj; rw [e]

lemma achieve118_gs {b b' : Fin n → Vec n} {k : ℕ} (h : Achieve118 b k b') (i : Fin n) :
    gs b' i = gs b i := by
  rcases achieve118_cases h with ⟨h1, _⟩ | ⟨hk, r, h1, _⟩
  · rw [h1]
  · rw [h1]
    exact gs_reduceBy b _ _ (by simp [Fin.lt_def]; omega) r i

lemma achieve118_mu {b b' : Fin n → Vec n} {k : ℕ} (hb : LinearIndependent ℝ b)
    (h : Achieve118 b k b') (hk : 2 ≤ k ∧ k ≤ n) :
    |mu b' ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2 := by
  rcases achieve118_cases h with ⟨h1, h2⟩ | ⟨hk', r, h1, h2⟩
  · rw [h1]; exact h2 hk
  · have hlt : (⟨k - 2, by omega⟩ : Fin n) < ⟨k - 1, by omega⟩ := by simp [Fin.lt_def]; omega
    rw [h1, mu_reduceBy _ _ _ hlt, if_pos rfl,
      mu_self b _ (InnerProductSpace.gramSchmidt_ne_zero _ hb), mul_one]
    exact h2

lemma loopstep_props {κ : Fin n} {c c' : Fin n → Vec n} (h : LoopStep κ c c') :
    (∀ i, gs c' i = gs c i) ∧ (∀ j, j ≠ κ → c' j = c j) ∧
    (∀ p : Fin n, (p : ℕ) + 1 = κ → |mu c κ p| ≤ 1 / 2 → mu c' κ p = mu c κ p) := by
  obtain ⟨l, hl, hbig, _, r, _, rfl⟩ := h
  refine ⟨gs_reduceBy c κ l hl r, fun j hj => reduceBy_ne c κ l r j hj, ?_⟩
  intro p hp hle
  have hlp : l < p := by
    have h1 : (l : ℕ) < κ := hl
    have h2 : l ≠ p := by
      rintro rfl; linarith
    have h3 : (l : ℕ) ≠ p := fun e => h2 (Fin.ext e)
    rw [Fin.lt_def]; omega
  rw [mu_reduceBy c κ l hl, if_pos rfl, mu_zero_of_lt c hlp]
  simp

lemma loop_props {κ : Fin n} {c c' : Fin n → Vec n}
    (h : Relation.ReflTransGen (LoopStep κ) c c') :
    (∀ i, gs c' i = gs c i) ∧ (∀ j, j ≠ κ → c' j = c j) ∧
    (∀ p : Fin n, (p : ℕ) + 1 = κ → |mu c κ p| ≤ 1 / 2 → mu c' κ p = mu c κ p) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | tail _ hs ih =>
    obtain ⟨g1, g2, g3⟩ := ih
    obtain ⟨s1, s2, s3⟩ := loopstep_props hs
    refine ⟨fun i => (s1 i).trans (g1 i), fun j hj => (s2 j hj).trans (g2 j hj), ?_⟩
    intro p hp hle
    have := g3 p hp hle
    rw [s3 p hp (by rw [this]; exact hle), this]


theorem step_core {n : ℕ} (b b' : Fin n → Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hsit : Situation b k)
    (hstep : Step (b, k) (b', k')) :
    Situation b' k' ∧ 1 ≤ k' ∧ k' ≤ n + 1 := by
  rcases hstep with h | h
  · obtain ⟨hk, b'', h118, h119, hb', hk'⟩ := h
    have hk1 : 2 ≤ k := hk.1
    have hk2 : k ≤ n := hk.2
    have hk'' : k' = k - 1 := hk'
    have hb'e : b' = b'' ∘ Equiv.swap (⟨k - 2, by omega⟩ : Fin n) ⟨k - 1, by omega⟩ := hb'
    subst hk''
    refine ⟨?_, by omega, by omega⟩
    refine Sit_congr ?_ (Sit_mono hsit (by omega))
    intro j hj
    rw [hb'e]
    have hj1 : j ≠ (⟨k - 2, by omega⟩ : Fin n) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have hj2 : j ≠ (⟨k - 1, by omega⟩ : Fin n) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp only [Function.comp]
    rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2, achieve118_ne h118 j (by omega)]
  · obtain ⟨hk, b'', h118, hc, hloop, hbig, hk'⟩ := h
    have hk1 : 1 ≤ k := hk.1
    have hk2 : k ≤ n := hk.2
    have hk'' : k' = k + 1 := hk'
    subst hk''
    refine ⟨?_, by omega, by omega⟩
    obtain ⟨g1, g2, g3⟩ := loop_props hloop
    have gsb : ∀ i, gs b' i = gs b i := fun i => (g1 i).trans (achieve118_gs h118 i)
    have eqb : ∀ j : Fin n, (j : ℕ) ≠ k - 1 → b' j = b j := fun j hj =>
      (g2 j (fun e => hj (by rw [e]))).trans (achieve118_ne h118 j hj)
    constructor
    · intro i j hji hik
      by_cases hi : (i : ℕ) = k - 1
      · have e : i = ⟨k - 1, by omega⟩ := Fin.ext hi
        rw [e]
        exact hbig j (by have : (j : ℕ) < i := hji; omega)
      · have e : mu b' i j = mu b i j := by rw [mu_eq, mu_eq, gsb, eqb i hi]
        rw [e]; exact hsit.1 i j hji (by omega)
    · intro i h2 hik hin
      by_cases hi : i < k
      · exact Cond120_congr (b := b) (fun j hj => eqb j (by omega)) (hsit.2 i h2 hi hin)
      · have hik' : i = k := by omega
        subst hik'
        rcases hc with hc | hc
        · omega
        · obtain ⟨hh, h0⟩ := hc
          refine ⟨hh, ?_⟩
          have e := g3 ⟨i - 2, by omega⟩ (by simp; omega) (achieve118_mu hb h118 ⟨h2, hin⟩)
          rw [g1, g1, e]
          exact h0

end GS
end LLLFactor.Reduction

open LLLFactor.Reduction


theorem solution {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hsit : Situation b k)
    (hstep : Step (b, k) (b', k')) :
    Situation b' k' ∧ 1 ≤ k' ∧ k' ≤ n + 1 := by
  exact step_core b b' k k' hb hsit hstep
