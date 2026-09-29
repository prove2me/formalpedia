-- Prove2me | solution 1 for LovaszSchrijver.OddHole.two_var_system_infeasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:41:44.283784+00:00
-- url     : https://prove2.me/submissions/e84331bc-bc99-40cf-90b8-8eba35d90832

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_AlternatingWalk

namespace LovaszSchrijver.OddHole

theorem aux_tvs_altB_succ {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 2) → W) :
    altB a b v = b s(v 0, v 1) + altA a b (Fin.tail v) := by
  unfold altB altA
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, Even.zero, if_true,
    Fin.val_succ, Nat.even_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.tail, Fin.succ_castSucc]
  split_ifs <;> rfl

theorem aux_tvs_altA_succ {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 2) → W) :
    altA a b v = -a s(v 0, v 1) + altB a b (Fin.tail v) := by
  unfold altB altA
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.val_zero, Even.zero, if_true,
    Fin.val_succ, Nat.even_add_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.tail, Fin.succ_castSucc]
  split_ifs <;> rfl

theorem aux_tvs_walk_tail {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 2) → W)
    (hv : IsWalkSeq H v) : IsWalkSeq H (Fin.tail v) := by
  intro t
  show H.Adj (v t.castSucc.succ) (v t.succ.succ)
  rw [Fin.succ_castSucc]
  exact hv t.succ

theorem aux_tvs_walk_cons {W : Type} (H : SimpleGraph W) {p : ℕ} (i : W) (w : Fin (p + 1) → W)
    (hw : IsWalkSeq H w) (hi : H.Adj i (w 0)) :
    IsWalkSeq H (Fin.cons i w : Fin (p + 2) → W) := by
  intro t
  refine Fin.cases ?_ ?_ t
  · simpa using hi
  · intro s
    have := hw s
    simpa [← Fin.succ_castSucc] using this

theorem aux_tvs_rev_walk {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 1) → W)
    (hv : IsWalkSeq H v) : IsWalkSeq H (fun t => v (Fin.rev t)) := by
  intro t
  simp only [Fin.rev_castSucc, Fin.rev_succ]
  exact (hv (Fin.rev t)).symm

theorem aux_tvs_rev_altB {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W)
    (hp : Even p) : altB a b (fun t => v (Fin.rev t)) = altA a b v := by
  unfold altB altA
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
  have hpar : Even (Fin.rev t).val ↔ ¬ Even t.val := by
    rw [Fin.val_rev, Nat.even_sub (by omega), Nat.even_add_one]
    tauto
  rw [Sym2.eq_swap (a := v t.succ)]
  by_cases ht : Even t.val
  · rw [if_neg (by tauto), if_pos ht]
  · rw [if_pos (by tauto), if_neg ht]

theorem aux_tvs_tele {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (y : W → ℝ)
    (hy : ∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) :
    ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v →
      y (v 0) + (-1 : ℝ) ^ (p + 1) * y (v (Fin.last p)) ≤ altB a b v ∧
      -(y (v 0) + (-1 : ℝ) ^ (p + 1) * y (v (Fin.last p))) ≤ altA a b v := by
  intro p
  induction p with
  | zero =>
    intro v _
    have : (Fin.last 0) = (0 : Fin 1) := rfl
    simp [altB, altA, this]
  | succ q ih =>
    intro v hv
    have h0 := hy _ _ (hv 0)
    obtain ⟨h1, h2⟩ := ih (Fin.tail v) (aux_tvs_walk_tail H v hv)
    rw [aux_tvs_altB_succ, aux_tvs_altA_succ]
    have e1 : Fin.tail v 0 = v 1 := rfl
    have e2 : Fin.tail v (Fin.last q) = v (Fin.last (q + 1)) := by
      simp [Fin.tail, Fin.succ_last]
    have e3 : (Fin.castSucc (0 : Fin (q + 1))) = 0 := rfl
    have e4 : (Fin.succ (0 : Fin (q + 1))) = 1 := rfl
    rw [e1, e2] at h1 h2
    rw [e3, e4] at h0
    have hs : (-1 : ℝ) ^ (q + 1 + 1) = -(-1 : ℝ) ^ (q + 1) := by ring
    rw [hs]
    constructor <;> nlinarith [h0.1, h0.2]

def aux_tvs_Up {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W) (i : W) :
    Set ℝ :=
  {r | ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧ v 0 = i ∧
      (Odd p ∨ (Even p ∧ v (Fin.last p) ∈ U)) ∧ r = altB a b v}

def aux_tvs_Lo {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W) (i : W) :
    Set ℝ :=
  {r | ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧ v 0 = i ∧
      (Even p ∨ (Odd p ∧ v (Fin.last p) ∈ U)) ∧ r = -altA a b v}

theorem aux_tvs_zero_mem_Lo {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i : W) : (0 : ℝ) ∈ aux_tvs_Lo H a b U i := by
  refine ⟨0, fun _ => i, fun t => t.elim0, rfl, Or.inl Even.zero, ?_⟩
  simp [altA]

theorem aux_tvs_zero_mem_Up {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i : W) (hi : i ∈ U) : (0 : ℝ) ∈ aux_tvs_Up H a b U i := by
  refine ⟨0, fun _ => i, fun t => t.elim0, rfl, Or.inr ⟨Even.zero, hi⟩, ?_⟩
  simp [altB]

theorem aux_tvs_Up_cons {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i j : W) (hij : H.Adj i j) (r : ℝ) (hr : r ∈ aux_tvs_Lo H a b U j) :
    b s(i, j) - r ∈ aux_tvs_Up H a b U i := by
  obtain ⟨p, w, hw, hw0, hpar, rfl⟩ := hr
  refine ⟨p + 1, Fin.cons i w, aux_tvs_walk_cons H i w hw (hw0 ▸ hij), rfl, ?_, ?_⟩
  · rcases hpar with h | ⟨h, hU⟩
    · exact Or.inl h.add_one
    · exact Or.inr ⟨h.add_one, by simpa [Fin.cons_last] using hU⟩
  · rw [aux_tvs_altB_succ]
    simp [Fin.cons_one, Fin.tail_cons, hw0]

theorem aux_tvs_Lo_cons {W : Type} (H : SimpleGraph W) (a b : Sym2 W → ℝ) (U : Finset W)
    (i j : W) (hij : H.Adj i j) (r : ℝ) (hr : r ∈ aux_tvs_Up H a b U j) :
    a s(i, j) - r ∈ aux_tvs_Lo H a b U i := by
  obtain ⟨p, w, hw, hw0, hpar, rfl⟩ := hr
  refine ⟨p + 1, Fin.cons i w, aux_tvs_walk_cons H i w hw (hw0 ▸ hij), rfl, ?_, ?_⟩
  · rcases hpar with h | ⟨h, hU⟩
    · exact Or.inl h.add_one
    · exact Or.inr ⟨h.add_one, by simpa [Fin.cons_last] using hU⟩
  · rw [aux_tvs_altA_succ]
    simp [Fin.cons_one, Fin.tail_cons, hw0]
    ring

theorem aux_tvs_construct {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (U : Finset W)
    (hA : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Odd p → 0 ≤ altB a b v)
    (hC : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Even p → v (Fin.last p) ∈ U →
      0 ≤ altB a b v)
    (hD : ∀ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v → Odd p → v 0 ∈ U →
      v (Fin.last p) ∈ U → 0 ≤ altA a b v) :
    ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0) := by
  -- basic facts
  have Up_nonneg : ∀ i, ∀ r ∈ aux_tvs_Up H a b U i, 0 ≤ r := by
    rintro i r ⟨p, v, hv, _, hpar, rfl⟩
    rcases hpar with h | ⟨h, hU⟩
    · exact hA p v hv h
    · exact hC p v hv h hU
  have Up_bdd : ∀ i, BddBelow (aux_tvs_Up H a b U i) := fun i => ⟨0, Up_nonneg i⟩
  have Lo_bdd : ∀ i, BddAbove (aux_tvs_Lo H a b U i) := by
    intro i
    refine ⟨∑ z : W, |b s(z, i)|, ?_⟩
    intro r hr
    have hr' := hr
    obtain ⟨p, w, hw, hw0, hpar, hrw⟩ := hr
    rcases p with _ | q
    · rw [hrw]; simp only [altA, Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
      exact Finset.sum_nonneg (fun z _ => abs_nonneg _)
    · have hadj : H.Adj (w 1) i := by
        have := hw 0
        rw [← hw0]; exact this.symm
      have h1 := Up_nonneg _ _ (aux_tvs_Up_cons H a b U (w 1) i hadj r hr')
      have h2 : b s(w 1, i) ≤ |b s(w 1, i)| := le_abs_self _
      have h3 : |b s(w 1, i)| ≤ ∑ z : W, |b s(z, i)| :=
        Finset.single_le_sum (f := fun z => |b s(z, i)|) (fun z _ => abs_nonneg _)
          (Finset.mem_univ _)
      linarith
  have Lo_ne : ∀ i, (aux_tvs_Lo H a b U i).Nonempty :=
    fun i => ⟨0, aux_tvs_zero_mem_Lo H a b U i⟩
  have Up_ne : ∀ i j, H.Adj i j → (aux_tvs_Up H a b U i).Nonempty :=
    fun i j hij => ⟨_, aux_tvs_Up_cons H a b U i j hij 0 (aux_tvs_zero_mem_Lo H a b U j)⟩
  set P : W → ℝ := fun i => sInf (aux_tvs_Up H a b U i) with hP
  set Q : W → ℝ := fun i => sSup (aux_tvs_Lo H a b U i) with hQ
  have P_nonneg : ∀ i, 0 ≤ P i := fun i => Real.sInf_nonneg (Up_nonneg i)
  have Q_nonneg : ∀ i, 0 ≤ Q i := fun i => le_csSup (Lo_bdd i) (aux_tvs_zero_mem_Lo H a b U i)
  have key1 : ∀ i j, H.Adj i j → P i + Q j ≤ b s(i, j) := by
    intro i j hij
    have : Q j ≤ b s(i, j) - P i := by
      apply csSup_le (Lo_ne j)
      intro r hr
      have := csInf_le (Up_bdd i) (aux_tvs_Up_cons H a b U i j hij r hr)
      simp only [hP] at this ⊢
      linarith
    linarith
  have key2 : ∀ i j, H.Adj i j → a s(i, j) ≤ Q i + P j := by
    intro i j hij
    have : a s(i, j) - Q i ≤ P j := by
      apply le_csInf (Up_ne j i hij.symm)
      intro r hr
      have := le_csSup (Lo_bdd i) (aux_tvs_Lo_cons H a b U i j hij r hr)
      simp only [hQ] at this ⊢
      linarith
    linarith
  refine ⟨fun i => (P i + Q i) / 2, ?_, ?_, ?_⟩
  · intro i j hij
    have k1 := key1 i j hij
    have k1' := key1 j i hij.symm
    have k2 := key2 i j hij
    have k2' := key2 j i hij.symm
    rw [Sym2.eq_swap] at k1' k2'
    constructor <;> simp only <;> linarith
  · intro i
    have := P_nonneg i
    have := Q_nonneg i
    simp only
    linarith
  · intro i hi
    have hP0 : P i ≤ 0 := csInf_le (Up_bdd i) (aux_tvs_zero_mem_Up H a b U i hi)
    have hQ0 : Q i ≤ 0 := by
      apply csSup_le (Lo_ne i)
      rintro r ⟨p, w, hw, hw0, hpar, rfl⟩
      rcases hpar with h | ⟨h, hU⟩
      · have := hC p (fun t => w (Fin.rev t)) (aux_tvs_rev_walk H w hw) h
          (by simpa [hw0] using hi)
        rw [aux_tvs_rev_altB a b w h] at this
        linarith
      · have := hD p w hw h (hw0 ▸ hi) hU
        linarith
    have := P_nonneg i
    have := Q_nonneg i
    simp only
    linarith

end LovaszSchrijver.OddHole

open LovaszSchrijver.OddHole

theorem solution {W : Type} [Fintype W] (H : SimpleGraph W)
    (a b : Sym2 W → ℝ) (hab : ∀ e ∈ H.edgeSet, 0 ≤ a e ∧ a e ≤ b e) (U : Finset W) :
    (¬ ∃ y : W → ℝ,
        (∀ i j, H.Adj i j → a s(i, j) ≤ y i + y j ∧ y i + y j ≤ b s(i, j)) ∧
        (∀ i, 0 ≤ y i) ∧ (∀ i ∈ U, y i = 0)) ↔
      ∃ (p : ℕ) (v : Fin (p + 1) → W), IsWalkSeq H v ∧
        ((Odd p ∧ altB a b v < 0) ∨
         (Even p ∧ v 0 = v (Fin.last p) ∧ altB a b v < 0) ∨
         (Even p ∧ v (Fin.last p) ∈ U ∧ altB a b v < 0) ∨
         (Odd p ∧ v 0 ∈ U ∧ v (Fin.last p) ∈ U ∧ altA a b v < 0)) := by
  constructor
  · intro hno
    by_contra hw
    apply hno
    apply aux_tvs_construct H a b U
    · intro p v hv hp
      by_contra h
      exact hw ⟨p, v, hv, Or.inl ⟨hp, lt_of_not_ge h⟩⟩
    · intro p v hv hp hU
      by_contra h
      exact hw ⟨p, v, hv, Or.inr (Or.inr (Or.inl ⟨hp, hU, lt_of_not_ge h⟩))⟩
    · intro p v hv hp h0 hU
      by_contra h
      exact hw ⟨p, v, hv, Or.inr (Or.inr (Or.inr ⟨hp, h0, hU, lt_of_not_ge h⟩))⟩
  · rintro ⟨p, v, hv, h⟩ ⟨y, hy, hy0, hyU⟩
    obtain ⟨hB, hA⟩ := aux_tvs_tele H a b y hy p v hv
    have n0 := hy0 (v 0)
    have nl := hy0 (v (Fin.last p))
    rcases h with ⟨hp, hlt⟩ | ⟨hp, heq, hlt⟩ | ⟨hp, hU, hlt⟩ | ⟨hp, h0, hU, hlt⟩
    · rw [(show Even (p + 1) from hp.add_one).neg_one_pow] at hB
      linarith
    · rw [(show Odd (p + 1) from hp.add_one).neg_one_pow, ← heq] at hB
      linarith
    · rw [(show Odd (p + 1) from hp.add_one).neg_one_pow, hyU _ hU] at hB
      linarith
    · rw [(show Even (p + 1) from hp.add_one).neg_one_pow, hyU _ hU, hyU _ h0] at hA
      linarith
