-- Prove2me | solution 1 for MasekPaterson.Necessity.editDist_eq_pathMin
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:28:16.056694+00:00
-- url     : https://prove2.me/submissions/a885e1f2-597c-45f7-9012-d182ec5e8e5b

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
open MasekPaterson.Shared


namespace MasekPaterson.Necessity

section EdCore
variable {α : Type*}

noncomputable def mpdp (γ : EditOp α → ℝ) : List α → List α → ℝ
  | [], [] => 0
  | x :: xs, [] => delCost γ x + mpdp γ xs []
  | [], y :: ys => insCost γ y + mpdp γ [] ys
  | x :: xs, y :: ys => min (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys))

variable (γ : EditOp α → ℝ)

lemma mpdp_nn : mpdp γ [] [] = 0 := by rw [mpdp]
lemma mpdp_cn (x : α) xs : mpdp γ (x :: xs) [] = delCost γ x + mpdp γ xs [] := by rw [mpdp]
lemma mpdp_nc (y : α) ys : mpdp γ [] (y :: ys) = insCost γ y + mpdp γ [] ys := by rw [mpdp]
lemma mpdp_cc (x y : α) xs ys : mpdp γ (x :: xs) (y :: ys) =
    min (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys)) := by rw [mpdp]

lemma mpdp_cc_cases (x y : α) xs ys :
    mpdp γ (x :: xs) (y :: ys) = delCost γ x + mpdp γ xs (y :: ys) ∨
    mpdp γ (x :: xs) (y :: ys) = insCost γ y + mpdp γ (x :: xs) ys ∨
    mpdp γ (x :: xs) (y :: ys) = replCost γ x y + mpdp γ xs ys := by
  rw [mpdp_cc]
  rcases min_choice (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys)) with h | h
  · left; rw [h]
  · rw [h]
    rcases min_choice (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys) with h' | h'
    · right; left; rw [h']
    · right; right; rw [h']

lemma mpdp_le_del (x : α) xs ys : mpdp γ (x :: xs) ys ≤ delCost γ x + mpdp γ xs ys := by
  cases ys with
  | nil => rw [mpdp_cn]
  | cons y ys => rw [mpdp_cc]; exact min_le_left _ _

lemma mpdp_le_ins xs (y : α) ys : mpdp γ xs (y :: ys) ≤ insCost γ y + mpdp γ xs ys := by
  cases xs with
  | nil => rw [mpdp_nc]
  | cons x xs => rw [mpdp_cc]; exact le_trans (min_le_right _ _) (min_le_left _ _)

lemma mpdp_le_rep (x : α) xs y ys : mpdp γ (x :: xs) (y :: ys) ≤ replCost γ x y + mpdp γ xs ys := by
  rw [mpdp_cc]; exact le_trans (min_le_right _ _) (min_le_right _ _)

def MPTri : Prop :=
  (∀ o, 0 ≤ γ o) ∧ (∀ x y b : α, replCost γ x b ≤ replCost γ x y + replCost γ y b) ∧
  (∀ x y : α, delCost γ x ≤ replCost γ x y + delCost γ y) ∧
  (∀ y b : α, insCost γ b ≤ insCost γ y + replCost γ y b) ∧ (∀ x : α, replCost γ x x ≤ 0)

variable {γ}

lemma mp_rep_base (h : MPTri γ) (x y : α) τ : ∀ B, mpdp γ (x :: τ) B ≤ replCost γ x y + mpdp γ (y :: τ) B := by
  intro B
  induction B with
  | nil => rw [mpdp_cn, mpdp_cn]; linarith [h.2.2.1 x y]
  | cons b B ih =>
    rcases mpdp_cc_cases γ y b τ B with h1 | h1 | h1 <;> rw [h1]
    · linarith [mpdp_le_del γ x τ (b :: B), h.2.2.1 x y]
    · linarith [mpdp_le_ins γ (x :: τ) b B]
    · linarith [mpdp_le_rep γ x τ b B, h.2.1 x y b]

lemma mp_ins_base (h : MPTri γ) (y : α) τ : ∀ B, mpdp γ τ B ≤ insCost γ y + mpdp γ (y :: τ) B := by
  have h0 : 0 ≤ insCost γ y + delCost γ y := add_nonneg (h.1 _) (h.1 _)
  intro B
  induction B with
  | nil => rw [mpdp_cn]; linarith
  | cons b B ih =>
    rcases mpdp_cc_cases γ y b τ B with h1 | h1 | h1 <;> rw [h1]
    · linarith
    · linarith [mpdp_le_ins γ τ b B]
    · linarith [mpdp_le_ins γ τ b B, h.2.2.2.1 y b]

lemma mp_edit_one (h : MPTri γ) (o : EditOp α) (τ : List α) :
    ∀ σ B, mpdp γ (σ ++ o.src.toList ++ τ) B ≤ γ o + mpdp γ (σ ++ o.tgt.toList ++ τ) B := by
  intro σ
  induction σ with
  | nil =>
    intro B
    rcases o with ⟨_ | x, _ | y, hn⟩
    · exact absurd ⟨rfl, rfl⟩ hn
    · exact mp_ins_base h y τ B
    · exact mpdp_le_del γ x τ B
    · exact mp_rep_base h x y τ B
  | cons x σ ih =>
    intro B
    simp only [List.cons_append]
    induction B with
    | nil => rw [mpdp_cn, mpdp_cn]; linarith [ih []]
    | cons b B ihB =>
      rcases mpdp_cc_cases γ x b (σ ++ o.tgt.toList ++ τ) B with h1 | h1 | h1 <;> rw [h1]
      · linarith [mpdp_le_del γ x (σ ++ o.src.toList ++ τ) (b :: B), ih (b :: B)]
      · linarith [mpdp_le_ins γ (x :: (σ ++ o.src.toList ++ τ)) b B]
      · linarith [mpdp_le_rep γ x (σ ++ o.src.toList ++ τ) b B, ih B]

lemma mpdp_self (h : MPTri γ) : ∀ A : List α, mpdp γ A A ≤ 0 := by
  intro A
  induction A with
  | nil => rw [mpdp_nn]
  | cons x A ih => linarith [mpdp_le_rep γ x A x A, h.2.2.2.2 x]

lemma mp_takes_lower (h : MPTri γ) {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) :
    mpdp γ A B ≤ seqCost γ S := by
  induction hS with
  | nil A => simpa [seqCost] using mpdp_self h A
  | @cons s S' A' C' B' hy _ ih =>
    obtain ⟨σ, τ, rfl, rfl⟩ := hy
    simp only [seqCost, List.map_cons, List.sum_cons] at ih ⊢
    linarith [mp_edit_one h s τ σ B']

lemma mp_yields_del (x : α) xs : Yields (delOp x) (x :: xs) xs := ⟨[], xs, by simp [delOp], by simp [delOp]⟩
lemma mp_yields_ins (y : α) xs : Yields (insOp y) xs (y :: xs) := ⟨[], xs, by simp [insOp], by simp [insOp]⟩
lemma mp_yields_rep (x y : α) xs : Yields (replOp x y) (x :: xs) (y :: xs) :=
  ⟨[], xs, by simp [replOp], by simp [replOp]⟩

lemma mp_takes_lift {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) (c : α) :
    Takes S (c :: A) (c :: B) := by
  induction hS with
  | nil A => exact Takes.nil _
  | cons hy _ ih =>
    obtain ⟨σ, τ, h1, h2⟩ := hy
    exact Takes.cons ⟨c :: σ, τ, by simp [h1], by simp [h2]⟩ ih

variable (γ)

theorem mp_realize : ∀ xs ys : List α, ∃ S, Takes S xs ys ∧ seqCost γ S ≤ mpdp γ xs ys
  | [], [] => ⟨[], Takes.nil _, by simp [seqCost, mpdp_nn]⟩
  | x :: xs, [] => by
    obtain ⟨S, hS, hc⟩ := mp_realize xs []
    refine ⟨delOp x :: S, Takes.cons (mp_yields_del x xs) hS, ?_⟩
    rw [mpdp_cn]; simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
    exact add_le_add le_rfl hc
  | [], y :: ys => by
    obtain ⟨S, hS, hc⟩ := mp_realize [] ys
    refine ⟨insOp y :: S, Takes.cons (mp_yields_ins y []) (mp_takes_lift hS y), ?_⟩
    rw [mpdp_nc]; simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
    exact add_le_add le_rfl hc
  | x :: xs, y :: ys => by
    rcases mpdp_cc_cases γ x y xs ys with h1 | h1 | h1 <;> rw [h1]
    · obtain ⟨S, hS, hc⟩ := mp_realize xs (y :: ys)
      refine ⟨delOp x :: S, Takes.cons (mp_yields_del x xs) hS, ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc
    · obtain ⟨S, hS, hc⟩ := mp_realize (x :: xs) ys
      refine ⟨insOp y :: S, Takes.cons (mp_yields_ins y _) (mp_takes_lift hS y), ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc
    · obtain ⟨S, hS, hc⟩ := mp_realize xs ys
      refine ⟨replOp x y :: S, Takes.cons (mp_yields_rep x y xs) (mp_takes_lift hS y), ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc

variable {γ}

theorem mp_editDist_eq (h : MPTri γ) (xs ys : List α) : editDist γ xs ys = mpdp γ xs ys := by
  obtain ⟨S, hS, hc⟩ := mp_realize γ xs ys
  apply le_antisymm
  · refine le_trans (csInf_le ⟨mpdp γ xs ys, ?_⟩ ⟨S, hS, rfl⟩) hc
    rintro c ⟨T, hT, rfl⟩; exact mp_takes_lower h hT
  · exact le_csInf ⟨_, S, hS, rfl⟩ (by rintro c ⟨T, hT, rfl⟩; exact mp_takes_lower h hT)

/-! paths -/

def mpseg (A : ℕ → α) (p n : ℕ) : List α := List.ofFn fun t : Fin n => A (p + t.val + 1)

lemma mpseg_zero (A : ℕ → α) p : mpseg A p 0 = [] := by simp [mpseg]
lemma mpseg_succ (A : ℕ → α) p n : mpseg A p (n + 1) = A (p + 1) :: mpseg A (p + 1) n := by
  simp only [mpseg, List.ofFn_succ, Fin.val_zero, Fin.val_succ, Nat.add_zero]
  congr 1
  apply List.ofFn_inj.mpr
  funext t; congr 1; omega

lemma mp_pathEnd_ge : ∀ (ms : List Move) (x : ℕ × ℕ), x.1 ≤ (pathEnd x ms).1 ∧ x.2 ≤ (pathEnd x ms).2
  | [], x => by simp [pathEnd]
  | m :: ms, x => by
    have := mp_pathEnd_ge ms (m.next x)
    cases m <;> simp only [pathEnd, Move.next] at this ⊢ <;> omega

lemma mp_path_lower (A B : ℕ → α) : ∀ (ms : List Move) (p q n m : ℕ),
    pathEnd (p, q) ms = (p + n, q + m) →
    mpdp γ (mpseg A p n) (mpseg B q m) ≤ pathCost γ A B (p, q) ms
  | [], p, q, n, m, he => by
    simp only [pathEnd, Prod.mk.injEq] at he
    obtain rfl : n = 0 := by omega
    obtain rfl : m = 0 := by omega
    simp [mpseg_zero, mpdp_nn, pathCost]
  | mv :: ms, p, q, n, m, he => by
    have hg := mp_pathEnd_ge ms (mv.next (p, q))
    simp only [pathEnd] at he
    rw [he] at hg
    cases mv with
    | del =>
      simp only [Move.next] at hg he
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have := mp_path_lower A B ms (p + 1) q n' m (by rw [he]; congr 1; omega)
      rw [mpseg_succ]
      simp only [pathCost, Move.cost, Move.next]
      linarith [mpdp_le_del γ (A (p + 1)) (mpseg A (p + 1) n') (mpseg B q m)]
    | ins =>
      simp only [Move.next] at hg he
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have := mp_path_lower A B ms p (q + 1) n m' (by rw [he]; congr 1; omega)
      rw [mpseg_succ B q m']
      simp only [pathCost, Move.cost, Move.next]
      linarith [mpdp_le_ins γ (mpseg A p n) (B (q + 1)) (mpseg B (q + 1) m')]
    | rep =>
      simp only [Move.next] at hg he
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have := mp_path_lower A B ms (p + 1) (q + 1) n' m' (by rw [he]; congr 1 <;> omega)
      rw [mpseg_succ, mpseg_succ B q m']
      simp only [pathCost, Move.cost, Move.next]
      linarith [mpdp_le_rep γ (A (p + 1)) (mpseg A (p + 1) n') (B (q + 1)) (mpseg B (q + 1) m')]

variable (γ)

lemma mp_path_realize (A B : ℕ → α) : ∀ n m p q : ℕ, ∃ ms : List Move,
    pathEnd (p, q) ms = (p + n, q + m) ∧
    pathCost γ A B (p, q) ms ≤ mpdp γ (mpseg A p n) (mpseg B q m) := by
  intro n
  induction n with
  | zero =>
    intro m
    induction m with
    | zero => intro p q; exact ⟨[], by simp [pathEnd], by simp [pathCost, mpseg_zero, mpdp_nn]⟩
    | succ m ih =>
      intro p q
      obtain ⟨ms, he, hc⟩ := ih p (q + 1)
      refine ⟨Move.ins :: ms, ?_, ?_⟩
      · simp only [pathEnd, Move.next, he]; congr 1; omega
      · rw [mpseg_succ B q m, mpseg_zero, mpdp_nc]
        rw [mpseg_zero] at hc
        simp only [pathCost, Move.cost, Move.next]; linarith
  | succ n ihn =>
    intro m
    induction m with
    | zero =>
      intro p q
      obtain ⟨ms, he, hc⟩ := ihn 0 (p + 1) q
      refine ⟨Move.del :: ms, ?_, ?_⟩
      · simp only [pathEnd, Move.next, he]; congr 1; omega
      · rw [mpseg_succ A p n, mpseg_zero, mpdp_cn]
        rw [mpseg_zero] at hc
        simp only [pathCost, Move.cost, Move.next]; linarith
    | succ m ihm =>
      intro p q
      rw [mpseg_succ A p n, mpseg_succ B q m]
      rcases mpdp_cc_cases γ (A (p + 1)) (B (q + 1)) (mpseg A (p + 1) n) (mpseg B (q + 1) m)
        with h1 | h1 | h1 <;> rw [h1]
      · obtain ⟨ms, he, hc⟩ := ihn (m + 1) (p + 1) q
        rw [mpseg_succ B q m] at hc
        refine ⟨Move.del :: ms, ?_, ?_⟩
        · simp only [pathEnd, Move.next, he]; congr 1; omega
        · simp only [pathCost, Move.cost, Move.next]; linarith
      · obtain ⟨ms, he, hc⟩ := ihm p (q + 1)
        rw [mpseg_succ A p n] at hc
        refine ⟨Move.ins :: ms, ?_, ?_⟩
        · simp only [pathEnd, Move.next, he]; congr 1; omega
        · simp only [pathCost, Move.cost, Move.next]; linarith
      · obtain ⟨ms, he, hc⟩ := ihn m (p + 1) (q + 1)
        refine ⟨Move.rep :: ms, ?_, ?_⟩
        · simp only [pathEnd, Move.next, he]; congr 1 <;> omega
        · simp only [pathCost, Move.cost, Move.next]; linarith

variable {γ}

theorem mp_pathMin_eq (A B : ℕ → α) (p q n m : ℕ) :
    pathMin γ A B (p, q) (p + n, q + m) = mpdp γ (mpseg A p n) (mpseg B q m) := by
  obtain ⟨ms, he, hc⟩ := mp_path_realize γ A B n m p q
  apply le_antisymm
  · refine le_trans (csInf_le ⟨mpdp γ (mpseg A p n) (mpseg B q m), ?_⟩ ⟨ms, he, rfl⟩) hc
    rintro c ⟨T, hT, rfl⟩; exact mp_path_lower A B T p q n m hT
  · exact le_csInf ⟨_, ms, he, rfl⟩
      (by rintro c ⟨T, hT, rfl⟩; exact mp_path_lower A B T p q n m hT)

lemma mp_seqCost_nonneg (hγ : ∀ o, 0 ≤ γ o) (S : List (EditOp α)) : 0 ≤ seqCost γ S := by
  unfold seqCost
  exact List.sum_nonneg (by intro x hx; obtain ⟨o, _, rfl⟩ := List.mem_map.mp hx; exact hγ o)

lemma mp_editDist_le (hγ : ∀ o, 0 ≤ γ o) {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) :
    editDist γ A B ≤ seqCost γ S :=
  csInf_le ⟨0, by rintro c ⟨T, _, rfl⟩; exact mp_seqCost_nonneg hγ T⟩ ⟨S, hS, rfl⟩

theorem mp_tri_of_norm (hγ : ∀ o, 0 ≤ γ o) (hnorm : IsNormalized γ) : MPTri γ := by
  refine ⟨hγ, ?_, ?_, ?_, ?_⟩
  · intro x y b
    have h1 := hnorm (replOp x b)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_rep x y []) (Takes.cons (mp_yields_rep y b [])
      (Takes.nil _)))
    simp only [replOp, Option.toList_some] at h1
    simp only [replCost, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h2 ⊢
    linarith
  · intro x y
    have h1 := hnorm (delOp x)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_rep x y []) (Takes.cons (mp_yields_del y [])
      (Takes.nil _)))
    simp only [delOp, Option.toList_some, Option.toList_none] at h1
    simp only [delCost, replCost, delOp, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h2 ⊢
    linarith
  · intro y b
    have h1 := hnorm (insOp b)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_ins y []) (Takes.cons (mp_yields_rep y b [])
      (Takes.nil _)))
    simp only [insOp, Option.toList_some, Option.toList_none] at h1
    simp only [insCost, replCost, insOp, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h2 ⊢
    linarith
  · intro x
    have h1 := hnorm (replOp x x)
    have h2 := mp_editDist_le hγ (Takes.nil [x])
    simp only [replOp, Option.toList_some] at h1
    simp only [replCost, replOp, seqCost, List.map_nil, List.sum_nil] at h2 ⊢
    linarith

theorem editDist_eq_pathMin_core (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hnorm : IsNormalized γ) (A B : ℕ → α) (i j : ℕ) :
    editDist γ (List.ofFn fun t : Fin i => A (t.val + 1))
        (List.ofFn fun t : Fin j => B (t.val + 1)) =
      pathMin γ A B (0, 0) (i, j) := by
  have h := mp_pathMin_eq (γ := γ) A B 0 0 i j
  simp only [Nat.zero_add] at h
  rw [h, mp_editDist_eq (mp_tri_of_norm hγ hnorm)]
  simp [mpseg]

end EdCore

end MasekPaterson.Necessity

open MasekPaterson.Necessity


theorem solution {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hnorm : IsNormalized γ) (A B : ℕ → α) (i j : ℕ) :
    editDist γ (List.ofFn fun t : Fin i => A (t.val + 1))
        (List.ofFn fun t : Fin j => B (t.val + 1)) =
      pathMin γ A B (0, 0) (i, j) := by
  exact editDist_eq_pathMin_core γ hγ hnorm A B i j
