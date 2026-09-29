-- Prove2me | solution 1 for MasekPaterson.Necessity.Pstar_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:42:20.86819+00:00
-- url     : https://prove2.me/submissions/096a76ba-bc42-49a2-968f-4ad1945ba10d

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
import Definitions.Def_MasekPaterson_Shared_steps
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

section Ex

lemma mp_half (n : ℕ) : (n : ℝ) - 1 ≤ 2 * ((n / 2 : ℕ) : ℝ) ∧ 2 * ((n / 2 : ℕ) : ℝ) ≤ n := by
  constructor
  · have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  · exact_mod_cast (by omega : 2 * (n / 2) ≤ n)

lemma mp_half_odd (n : ℕ) (h : n % 2 = 1) : 2 * ((n / 2 : ℕ) : ℝ) = n - 1 := by
  have : 2 * (n / 2) + 1 = n := by omega
  have : 2 * ((n / 2 : ℕ) : ℝ) + 1 = n := by exact_mod_cast this
  linarith

lemma mu_le (n : ℕ) : 2 * Real.pi * mu n + mu n ≤ 2 * ((n / 2 : ℕ) : ℝ) := by
  have hK : 0 < 2 * Real.pi + 1 := by positivity
  have h := Nat.floor_le (a := ((2 * (n / 2) : ℕ) : ℝ) / (2 * Real.pi + 1)) (by positivity)
  rw [le_div_iff₀ hK] at h
  unfold mu
  push_cast at h ⊢
  linarith

lemma mu_gt (n : ℕ) : 2 * ((n / 2 : ℕ) : ℝ) < 2 * Real.pi * mu n + mu n + 2 * Real.pi + 1 := by
  have hK : 0 < 2 * Real.pi + 1 := by positivity
  have h := Nat.lt_floor_add_one (((2 * (n / 2) : ℕ) : ℝ) / (2 * Real.pi + 1))
  rw [div_lt_iff₀ hK] at h
  unfold mu
  push_cast at h ⊢
  linarith

lemma mu_succ_of_even (n : ℕ) (h : n % 2 = 0) : mu (n + 1) = mu n := by
  unfold mu; rw [show (n + 1) / 2 = n / 2 by omega]

lemma mu_succ (n : ℕ) : mu (n + 1) = mu n ∨ mu (n + 1) = mu n + 1 := by
  have hpi := Real.pi_gt_three
  have e1 : ((n / 2 : ℕ) : ℝ) ≤ ((n + 1) / 2 : ℕ) := by exact_mod_cast (by omega : n / 2 ≤ (n + 1) / 2)
  have e2 : (((n + 1) / 2 : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : (n + 1) / 2 ≤ n / 2 + 1)
  have a1 := mu_le n; have a2 := mu_gt n; have b1 := mu_le (n + 1); have b2 := mu_gt (n + 1)
  have h1 : (mu n : ℝ) < mu (n + 1) + 1 := by
    by_contra hc; push_neg at hc
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 2 * Real.pi + 1)
    nlinarith
  have h2 : (mu (n + 1) : ℝ) < mu n + 2 := by
    by_contra hc; push_neg at hc
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 2 * Real.pi + 1)
    nlinarith
  have h1' : mu n < mu (n + 1) + 1 := by exact_mod_cast h1
  have h2' : mu (n + 1) < mu n + 2 := by exact_mod_cast h2
  omega

lemma mu_mono : Monotone mu :=
  monotone_nat_of_le_succ (fun n => by rcases mu_succ n with h | h <;> omega)

lemma mu_zero : mu 0 = 0 := by simp [mu]
lemma mu_one : mu 1 = 0 := by simp [mu]

lemma mu_up (n : ℕ) : (n : ℝ) < 2 * Real.pi * mu n + mu n + 2 * Real.pi + 2 := by
  linarith [mu_gt n, (mp_half n).1]

lemma mu_lo (n : ℕ) : 2 * Real.pi * mu n + mu n ≤ n := by
  linarith [mu_le n, (mp_half n).2]

lemma mu_lo_odd (n : ℕ) (h : n % 2 = 1) : 2 * Real.pi * mu n + mu n ≤ n - 1 := by
  linarith [mu_le n, mp_half_odd n h]

lemma mp_L3 (a b : ℕ) (hab : (a + b) % 2 = 0) :
    2 * Real.pi * ((mu (a + 1) : ℝ) + mu b) + mu a + mu b ≤ a + b := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  · rw [mu_succ_of_even a ha]; linarith [mu_lo a, mu_lo b]
  · have hb : b % 2 = 1 := by omega
    rcases mu_succ a with h | h
    · rw [h]; linarith [mu_lo_odd a ha, mu_lo_odd b hb]
    · have := mu_lo (a + 1)
      rw [h] at this ⊢; push_cast at this ⊢
      linarith [mu_lo_odd b hb]

lemma mp_L4 (a b : ℕ) :
    (a : ℝ) + 1 + b - mu (a + 1) - mu b ≤ 18 + 2 * Real.pi * ((mu a : ℝ) + mu b) := by
  have hpi := Real.pi_lt_d2
  rcases mu_succ a with h | h <;> rw [h] <;> push_cast <;> linarith [mu_up a, mu_up b]

lemma exA_cases (i : ℕ) :
    (exA (i + 1) = .b ∧ mu (i + 1) = mu i ∧ i % 2 = 0) ∨
    (exA (i + 1) = .a ∧ mu (i + 1) = mu i ∧ i % 2 = 1) ∨
    (exA (i + 1) = .c ∧ mu (i + 1) = mu i + 1 ∧ i % 2 = 1) := by
  unfold exA
  rw [Nat.add_sub_cancel]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · left; refine ⟨by rw [if_pos (by omega)], mu_succ_of_even i hi, hi⟩
  · rw [if_neg (by omega)]
    rcases mu_succ i with h | h
    · right; left; refine ⟨by rw [if_neg (by omega)], h, hi⟩
    · right; right; refine ⟨by rw [if_pos (by omega)], h, hi⟩

lemma exB_cases (i : ℕ) :
    (exB (i + 1) = .a ∧ mu (i + 1) = mu i ∧ i % 2 = 0) ∨
    (exB (i + 1) = .b ∧ mu (i + 1) = mu i ∧ i % 2 = 1) ∨
    (exB (i + 1) = .c ∧ mu (i + 1) = mu i + 1 ∧ i % 2 = 1) := by
  unfold exB
  rw [Nat.add_sub_cancel]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · left; refine ⟨by rw [if_pos (by omega)], mu_succ_of_even i hi, hi⟩
  · rw [if_neg (by omega)]
    rcases mu_succ i with h | h
    · right; left; refine ⟨by rw [if_neg (by omega)], h, hi⟩
    · right; right; refine ⟨by rw [if_pos (by omega)], h, hi⟩

lemma diag_even (i j : ℕ) (h : (i + j) % 2 = 0) :
    1 - ((mu (i + 1) : ℝ) - mu i) ≤ exRepl (exA (i + 1)) (exB (j + 1)) ∧
    1 - ((mu (j + 1) : ℝ) - mu j) ≤ exRepl (exA (i + 1)) (exB (j + 1)) := by
  have hpi := Real.pi_gt_three
  rcases exA_cases i with ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ <;>
  rcases exB_cases j with ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ <;>
  (try omega) <;> rw [ha, hb, hma, hmb] <;> simp only [exRepl] <;> push_cast <;>
  constructor <;> linarith

lemma diag_odd (i j : ℕ) (h : (i + j) % 2 = 1) :
    exRepl (exA (i + 1)) (exB (j + 1)) =
      Real.pi * (((mu (i + 1) : ℝ) - mu i) + ((mu (j + 1) : ℝ) - mu j)) := by
  rcases exA_cases i with ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ <;>
  rcases exB_cases j with ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ <;>
  (try omega) <;> rw [ha, hb, hma, hmb] <;> simp only [exRepl] <;> push_cast <;> ring

lemma diag_center (i : ℕ) :
    exRepl (exA (i + 1)) (exB (i + 1)) = 1 - ((mu (i + 1) : ℝ) - mu i) := by
  rcases exA_cases i with ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ | ⟨ha, hma, hi⟩ <;>
  rcases exB_cases i with ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ | ⟨hb, hmb, hj⟩ <;>
  (try omega) <;> rw [ha, hb, hma] <;> simp only [exRepl] <;>
  push_cast <;> ring

noncomputable def mpphi (x : ℕ × ℕ) : ℝ :=
  if (x.1 + x.2) % 2 = 0 then ((x.1 : ℝ) + x.2 - mu x.1 - mu x.2) / 2
  else 5 + Real.pi * ((mu x.1 : ℝ) + mu x.2)

lemma ex_cost_del (x : ℕ × ℕ) : Move.cost exCost exA exB .del x = 5 := rfl
lemma ex_cost_ins (x : ℕ × ℕ) : Move.cost exCost exA exB .ins x = 5 := rfl
lemma ex_cost_rep (x : ℕ × ℕ) :
    Move.cost exCost exA exB .rep x = exRepl (exA (x.1 + 1)) (exB (x.2 + 1)) := rfl

lemma phi_del (i j : ℕ) :
    mpphi (i + 1, j) + (if (i + 1 + j) % 2 = 0 then 1 else 0) ≤ mpphi (i, j) + 5 := by
  unfold mpphi
  dsimp only
  have l3 := mp_L3 i j; have l4 := mp_L4 i j
  rcases Nat.mod_two_eq_zero_or_one (i + j) with h | h
  · rw [if_neg (show ¬ (i + 1 + j) % 2 = 0 by omega), if_neg (show ¬ (i + 1 + j) % 2 = 0 by omega),
      if_pos h]; push_cast; linarith [l3 h]
  · rw [if_pos (show (i + 1 + j) % 2 = 0 by omega), if_pos (show (i + 1 + j) % 2 = 0 by omega),
      if_neg (show ¬ (i + j) % 2 = 0 by omega)]; push_cast; linarith

lemma phi_ins (i j : ℕ) :
    mpphi (i, j + 1) + (if (i + (j + 1)) % 2 = 0 then 1 else 0) ≤ mpphi (i, j) + 5 := by
  unfold mpphi
  dsimp only
  have l3 := mp_L3 j i; have l4 := mp_L4 j i
  rcases Nat.mod_two_eq_zero_or_one (i + j) with h | h
  · rw [if_neg (show ¬ (i + (j + 1)) % 2 = 0 by omega), if_neg (show ¬ (i + (j + 1)) % 2 = 0 by omega),
      if_pos h]; push_cast; linarith [l3 (by omega)]
  · rw [if_pos (show (i + (j + 1)) % 2 = 0 by omega), if_pos (show (i + (j + 1)) % 2 = 0 by omega),
      if_neg (show ¬ (i + j) % 2 = 0 by omega)]; push_cast; linarith

lemma phi_rep (i j : ℕ) :
    mpphi (i + 1, j + 1) ≤ mpphi (i, j) + exRepl (exA (i + 1)) (exB (j + 1)) := by
  unfold mpphi
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one (i + j) with h | h
  · rw [if_pos (show (i + 1 + (j + 1)) % 2 = 0 by omega), if_pos h]
    have := diag_even i j h; push_cast; linarith [this.1, this.2]
  · rw [if_neg (show ¬ (i + 1 + (j + 1)) % 2 = 0 by omega), if_neg (show ¬ (i + j) % 2 = 0 by omega)]
    have := diag_odd i j h; push_cast; rw [this]; linarith

lemma phi_move (m : Move) (x : ℕ × ℕ) : mpphi (m.next x) ≤ mpphi x + m.cost exCost exA exB x := by
  obtain ⟨i, j⟩ := x
  cases m with
  | rep => exact phi_rep i j
  | del =>
    have := phi_del i j
    show mpphi (i + 1, j) ≤ mpphi (i, j) + 5
    split_ifs at this <;> linarith
  | ins =>
    have := phi_ins i j
    show mpphi (i, j + 1) ≤ mpphi (i, j) + 5
    split_ifs at this <;> linarith

noncomputable def mppsi (d0 : ℤ) (C : ℝ) (x : ℕ × ℕ) : ℝ :=
  mpphi x + if ((x.1 : ℤ) - x.2 = d0) then ((mu x.2 : ℝ) - mu x.1) / 2 + C else 0

lemma psi_move (d0 : ℤ) (C : ℝ) (hd : d0 % 2 = 0)
    (hadj : ∀ i j : ℕ, (i : ℤ) - j = d0 → 0 ≤ ((mu j : ℝ) - mu i) / 2 + C ∧
      ((mu j : ℝ) - mu i) / 2 + C ≤ 1) (m : Move) (x : ℕ × ℕ) :
    mppsi d0 C (m.next x) ≤ mppsi d0 C x + m.cost exCost exA exB x := by
  obtain ⟨i, j⟩ := x
  cases m with
  | rep =>
    show mppsi d0 C (i + 1, j + 1) ≤ mppsi d0 C (i, j) + exRepl (exA (i + 1)) (exB (j + 1))
    have hφ := phi_rep i j
    unfold mppsi
    dsimp only
    by_cases h1 : ((i : ℤ) - j = d0)
    · have h1' : (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = d0) := by push_cast; omega
      rw [if_pos h1, if_pos h1']
      have hp : (i + j) % 2 = 0 := by omega
      have := diag_even i j hp
      unfold mpphi
      dsimp only
      rw [if_pos (show (i + 1 + (j + 1)) % 2 = 0 by omega), if_pos hp]
      push_cast; linarith [this.1]
    · have h1' : ¬ (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = d0) := by push_cast; omega
      rw [if_neg h1, if_neg h1']; linarith
  | del =>
    show mppsi d0 C (i + 1, j) ≤ mppsi d0 C (i, j) + 5
    have hφ := phi_del i j
    unfold mppsi
    dsimp only
    by_cases h1 : ((i : ℤ) - j = d0)
    · have h1' : ¬ (((i + 1 : ℕ) : ℤ) - (j : ℤ) = d0) := by push_cast; omega
      rw [if_pos h1, if_neg h1']
      have := hadj i j h1
      split_ifs at hφ <;> linarith
    · by_cases h2 : (((i + 1 : ℕ) : ℤ) - (j : ℤ) = d0)
      · rw [if_neg h1, if_pos h2]
        have := hadj (i + 1) j h2
        rw [if_pos (show (i + 1 + j) % 2 = 0 by push_cast at h2; omega)] at hφ
        linarith
      · rw [if_neg h1, if_neg h2]; split_ifs at hφ <;> linarith
  | ins =>
    show mppsi d0 C (i, j + 1) ≤ mppsi d0 C (i, j) + 5
    have hφ := phi_ins i j
    unfold mppsi
    dsimp only
    by_cases h1 : ((i : ℤ) - j = d0)
    · have h1' : ¬ ((i : ℤ) - ((j + 1 : ℕ) : ℤ) = d0) := by push_cast; omega
      rw [if_pos h1, if_neg h1']
      have := hadj i j h1
      split_ifs at hφ <;> linarith
    · by_cases h2 : ((i : ℤ) - ((j + 1 : ℕ) : ℤ) = d0)
      · rw [if_neg h1, if_pos h2]
        have := hadj i (j + 1) h2
        rw [if_pos (show (i + (j + 1)) % 2 = 0 by push_cast at h2; omega)] at hφ
        linarith
      · rw [if_neg h1, if_neg h2]; split_ifs at hφ <;> linarith

lemma V_path (V : ℕ × ℕ → ℝ) (hV : ∀ (m : Move) (x : ℕ × ℕ), V (m.next x) ≤ V x + m.cost exCost exA exB x) :
    ∀ (ms : List Move) (x : ℕ × ℕ), V (pathEnd x ms) ≤ V x + pathCost exCost exA exB x ms
  | [], x => by simp [pathEnd, pathCost]
  | m :: ms, x => by
    simp only [pathEnd, pathCost]
    linarith [V_path V hV ms (m.next x), hV m x]

lemma diag_end (k : ℕ) : ∀ i j : ℕ, pathEnd (i, j) (List.replicate k Move.rep) = (i + k, j + k) := by
  induction k with
  | zero => intro i j; simp [pathEnd]
  | succ k ih =>
    intro i j
    rw [List.replicate_succ]
    simp only [pathEnd, Move.next]
    rw [ih]; ext <;> simp <;> omega

lemma diag_points (k : ℕ) : ∀ i j : ℕ, ∀ x ∈ pathPoints (i, j) (List.replicate k Move.rep),
    ecc x = ecc (i, j) := by
  induction k with
  | zero => intro i j x hx; simp [pathPoints] at hx; rw [hx]
  | succ k ih =>
    intro i j x hx
    rw [List.replicate_succ] at hx
    simp only [pathPoints, Move.next, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rfl
    · rw [ih (i + 1) (j + 1) x hx]; simp only [ecc]; push_cast; ring_nf

lemma diag_tight (i j : ℕ) (h : i = j ∨ (i + j) % 2 = 1) :
    exRepl (exA (i + 1)) (exB (j + 1)) = mpphi (i + 1, j + 1) - mpphi (i, j) := by
  unfold mpphi
  dsimp only
  rcases h with rfl | h
  · rw [if_pos (show (i + 1 + (i + 1)) % 2 = 0 by omega), if_pos (show (i + i) % 2 = 0 by omega),
      diag_center]
    push_cast; ring
  · rw [if_neg (show ¬ (i + 1 + (j + 1)) % 2 = 0 by omega), if_neg (show ¬ (i + j) % 2 = 0 by omega),
      diag_odd i j h]
    push_cast; ring

lemma diag_cost (k : ℕ) : ∀ i j : ℕ, (i = j ∨ (i + j) % 2 = 1) →
    pathCost exCost exA exB (i, j) (List.replicate k Move.rep) = mpphi (i + k, j + k) - mpphi (i, j) := by
  induction k with
  | zero => intro i j _; simp [pathCost]
  | succ k ih =>
    intro i j h
    rw [List.replicate_succ]
    simp only [pathCost, Move.next]
    rw [ex_cost_rep, ih (i + 1) (j + 1) (by omega)]
    dsimp only
    rw [diag_tight i j h]
    rw [show i + 1 + k = i + (k + 1) by omega, show j + 1 + k = j + (k + 1) by omega]
    ring

lemma pm_ge (V : ℕ × ℕ → ℝ) (hV : ∀ (m : Move) (x : ℕ × ℕ), V (m.next x) ≤ V x + m.cost exCost exA exB x)
    (x y : ℕ × ℕ) (ms0 : List Move) (h0 : pathEnd x ms0 = y) :
    V y - V x ≤ pathMin exCost exA exB x y :=
  le_csInf ⟨_, ms0, h0, rfl⟩ (by
    rintro c ⟨ms, hms, rfl⟩
    have := V_path V hV ms x; rw [hms] at this; linarith)

lemma pm_le (V : ℕ × ℕ → ℝ) (hV : ∀ (m : Move) (x : ℕ × ℕ), V (m.next x) ≤ V x + m.cost exCost exA exB x)
    (x y : ℕ × ℕ) (ms0 : List Move) (h0 : pathEnd x ms0 = y) :
    pathMin exCost exA exB x y ≤ pathCost exCost exA exB x ms0 :=
  csInf_le ⟨V y - V x, by
    rintro c ⟨ms, hms, rfl⟩
    have := V_path V hV ms x; rw [hms] at this; linarith⟩ ⟨ms0, h0, rfl⟩

lemma ex_tri : MPTri exCost := by
  have hpi := Real.pi_gt_three
  have hR : ∀ x y, replCost exCost x y = exRepl x y := fun _ _ => rfl
  have hD : ∀ x, delCost exCost x = 5 := fun _ => rfl
  have hI : ∀ x, insCost exCost x = 5 := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨_ | x, _ | y, h⟩
    · show (0:ℝ) ≤ 5; norm_num
    · show (0:ℝ) ≤ 5; norm_num
    · show (0:ℝ) ≤ 5; norm_num
    · show 0 ≤ exRepl x y
      cases x <;> cases y <;> simp only [exRepl] <;> linarith
  · intro x y b; rw [hR, hR, hR]
    cases x <;> cases y <;> cases b <;> simp only [exRepl] <;> linarith
  · intro x y; rw [hR, hD, hD]
    cases x <;> cases y <;> simp only [exRepl] <;> linarith
  · intro y b; rw [hR, hI, hI]
    cases y <;> cases b <;> simp only [exRepl] <;> linarith
  · intro x; rw [hR]; cases x <;> simp only [exRepl] <;> norm_num

lemma exDelta_eq (i j : ℕ) : exDelta i j = pathMin exCost exA exB (0, 0) (i, j) := by
  have h1 := mp_editDist_eq ex_tri (exAPre i) (exBPre j)
  have h2 := mp_pathMin_eq (γ := exCost) exA exB 0 0 i j
  simp only [Nat.zero_add] at h2
  unfold exDelta; rw [h1, h2]
  congr 1 <;> simp [mpseg, exAPre, exBPre]

lemma phi_zero : mpphi (0, 0) = 0 := by simp [mpphi, mu_zero]

lemma exDelta_of_path (i j : ℕ) (ms : List Move) (h0 : pathEnd (0, 0) ms = (i, j))
    (hc : pathCost exCost exA exB (0, 0) ms = mpphi (i, j)) : exDelta i j = mpphi (i, j) := by
  rw [exDelta_eq]
  apply le_antisymm
  · rw [← hc]; exact pm_le mpphi phi_move _ _ ms h0
  · have := pm_ge mpphi phi_move _ _ ms h0; rw [phi_zero] at this; linarith

theorem center_diagonals_core (k : ℕ) :
    exDelta k k = (k : ℝ) - (mu k : ℝ) ∧
    (exDelta k (k + 1) = exDelta (k + 1) k ∧
      exDelta (k + 1) k = 5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi) := by
  have e0 : exDelta k k = mpphi (k, k) := by
    apply exDelta_of_path k k (List.replicate k Move.rep)
    · rw [diag_end]; simp
    · rw [diag_cost k 0 0 (Or.inl rfl), phi_zero]; simp
  have e1 : exDelta k (k + 1) = mpphi (k, k + 1) := by
    apply exDelta_of_path k (k + 1) (Move.ins :: List.replicate k Move.rep)
    · simp only [pathEnd, Move.next]; rw [diag_end]; ext <;> simp; omega
    · simp only [pathCost, Move.next]
      rw [ex_cost_ins, diag_cost k 0 (0 + 1) (Or.inr (by omega))]
      simp [mpphi, mu_zero, mu_one]; ring_nf
  have e2 : exDelta (k + 1) k = mpphi (k + 1, k) := by
    apply exDelta_of_path (k + 1) k (Move.del :: List.replicate k Move.rep)
    · simp only [pathEnd, Move.next]; rw [diag_end]; ext <;> simp; omega
    · simp only [pathCost, Move.next]
      rw [ex_cost_del, diag_cost k (0 + 1) 0 (Or.inr (by omega))]
      simp [mpphi, mu_zero, mu_one]; ring_nf
  have p0 : mpphi (k, k) = (k : ℝ) - mu k := by
    unfold mpphi; dsimp only; rw [if_pos (by omega)]; ring
  have p1 : mpphi (k, k + 1) = 5 + ((mu (k + 1) : ℝ) + mu k) * Real.pi := by
    unfold mpphi; dsimp only; rw [if_neg (by omega)]; ring
  have p2 : mpphi (k + 1, k) = 5 + ((mu (k + 1) : ℝ) + mu k) * Real.pi := by
    unfold mpphi; dsimp only; rw [if_neg (by omega)]; ring
  refine ⟨by rw [e0, p0], by rw [e1, e2, p1, p2], by rw [e2, p2]⟩

lemma pstar_ge (V : ℕ × ℕ → ℝ)
    (hV : ∀ (m : Move) (x : ℕ × ℕ), V (m.next x) ≤ V x + m.cost exCost exA exB x) (i j k : ℕ) :
    V (i + k, j + k) - V (i, j) ≤ exPstar i j k :=
  le_csInf ⟨_, List.replicate k Move.rep, diag_end k i j,
      fun x hx => (diag_points k i j x hx).ge, rfl⟩ (by
    rintro c ⟨ms, hms, _, rfl⟩
    have := V_path V hV ms (i, j); rw [hms] at this; linarith)

lemma mu_diff_close (i j i' j' : ℕ) (h : (i : ℤ) - j = i' - j') (hp : (i + j) % 2 = 0) :
    ((mu i' : ℤ) - mu j') - (mu i - mu j) ≤ 1 ∧ -1 ≤ ((mu i' : ℤ) - mu j') - (mu i - mu j) := by
  have hN : 2 * (i / 2) + 2 * (j' / 2) = 2 * (i' / 2) + 2 * (j / 2) := by omega
  have hR : 2 * ((i / 2 : ℕ) : ℝ) + 2 * ((j' / 2 : ℕ) : ℝ) = 2 * ((i' / 2 : ℕ) : ℝ) + 2 * ((j / 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have a1 := mu_le i; have a2 := mu_gt i; have b1 := mu_le j; have b2 := mu_gt j
  have c1 := mu_le i'; have c2 := mu_gt i'; have d1 := mu_le j'; have d2 := mu_gt j'
  have hK : (0:ℝ) < 2 * Real.pi + 1 := by positivity
  set X : ℝ := ((mu i' : ℝ) - mu j') - (mu i - mu j) with hXdef
  have hX1 : X < 2 := by
    by_contra hc; push_neg at hc
    have := mul_nonneg hK.le (sub_nonneg.mpr hc)
    nlinarith
  have hX2 : -2 < X := by
    by_contra hc; push_neg at hc
    have := mul_nonneg hK.le (sub_nonneg.mpr hc)
    nlinarith
  have e : (((((mu i' : ℤ) - mu j') - (mu i - mu j)) : ℤ) : ℝ) = X := by rw [hXdef]; push_cast; ring
  have h1 : (((mu i' : ℤ) - mu j') - (mu i - mu j)) < 2 := by exact_mod_cast (e ▸ hX1)
  have h2 : -2 < (((mu i' : ℤ) - mu j') - (mu i - mu j)) := by exact_mod_cast (e ▸ hX2)
  omega

theorem Pstar_lower_bound_core (i j k : ℕ) :
    (Even ((i : ℤ) - j) →
      (k : ℝ) - (mu (i + k) : ℝ) + (mu i : ℝ) ≤ exPstar i j k) ∧
    (Odd ((i : ℤ) - j) →
      ((mu (i + k) : ℝ) - (mu i : ℝ) + (mu (j + k) : ℝ) - (mu j : ℝ)) * Real.pi
        ≤ exPstar i j k) := by
  constructor
  · intro he
    obtain ⟨r, hr⟩ := he
    have hp : (i + j) % 2 = 0 := by omega
    set C : ℝ := ((mu i : ℝ) - mu j) / 2 + 1 / 2 with hC
    have hadj : ∀ i' j' : ℕ, (i' : ℤ) - j' = (i : ℤ) - j → 0 ≤ ((mu j' : ℝ) - mu i') / 2 + C ∧
        ((mu j' : ℝ) - mu i') / 2 + C ≤ 1 := by
      intro i' j' h'
      obtain ⟨u1, u2⟩ := mu_diff_close i j i' j' h'.symm hp
      have v1 : (((mu i' : ℤ) - mu j') - (mu i - mu j) : ℤ) ≤ 1 := u1
      have w1 : ((((mu i' : ℤ) - mu j') - (mu i - mu j) : ℤ) : ℝ) ≤ 1 := by exact_mod_cast v1
      have w2 : (-1 : ℝ) ≤ ((((mu i' : ℤ) - mu j') - (mu i - mu j) : ℤ) : ℝ) := by exact_mod_cast u2
      push_cast at w1 w2
      rw [hC]; constructor <;> linarith
    have := pstar_ge (mppsi ((i : ℤ) - j) C) (psi_move _ C (by omega) hadj) i j k
    refine le_trans (le_of_eq ?_) this
    unfold mppsi mpphi
    dsimp only
    rw [if_pos (show (i + k + (j + k)) % 2 = 0 by omega), if_pos hp, if_pos (by push_cast; ring),
      if_pos rfl]
    push_cast; ring
  · intro ho
    obtain ⟨r, hr⟩ := ho
    have hp : (i + j) % 2 = 1 := by omega
    have := pstar_ge mpphi phi_move i j k
    refine le_trans (le_of_eq ?_) this
    unfold mpphi
    dsimp only
    rw [if_neg (show ¬ (i + k + (j + k)) % 2 = 0 by omega), if_neg (show ¬ (i + j) % 2 = 0 by omega)]
    ring

theorem Pstar_split_bound_core (k k' : ℕ) (hk' : k' ≤ k) :
    5 + ((mu (k + 1) : ℝ) + (mu k : ℝ)) * Real.pi
      ≤ exPstar 0 0 k' + 5 + exPstar (k' + 1) k' (k - k') := by
  obtain ⟨t, rfl⟩ : ∃ t, k = k' + t := ⟨k - k', by omega⟩
  have h1 := (Pstar_lower_bound_core 0 0 k').1 (by simp)
  have h2 := (Pstar_lower_bound_core (k' + 1) k' t).2 (by push_cast; exact ⟨0, by ring⟩)
  rw [show k' + t - k' = t by omega] 
  rw [show k' + 1 + t = k' + t + 1 by omega] at h2
  have l3 := mp_L3 k' k' (by omega)
  simp only [Nat.zero_add, mu_zero, CharP.cast_eq_zero, add_zero] at h1
  nlinarith

theorem steps_unbounded_core :
    Function.Injective (fun k : ℕ => exDelta k (k + 1) - exDelta k k) ∧
    ¬ (possibleSteps exCost).Finite := by
  have hf : ∀ k, exDelta k (k + 1) - exDelta k k =
      5 + ((mu (k + 1) : ℝ) + mu k) * Real.pi - ((k : ℝ) - mu k) := by
    intro k
    obtain ⟨a, b, c⟩ := center_diagonals_core k
    rw [a, b, c]
  have hinj : Function.Injective (fun k : ℕ => exDelta k (k + 1) - exDelta k k) := by
    have key : ∀ a b : ℕ, a < b → exDelta a (a + 1) - exDelta a a ≠ exDelta b (b + 1) - exDelta b b := by
      intro a b hlt hab
      rw [hf, hf] at hab
      by_cases hS : mu (a + 1) + mu a = mu (b + 1) + mu b
      · have m1 := mu_mono (show a ≤ b by omega)
        have m2 := mu_mono (show a + 1 ≤ b + 1 by omega)
        have hma : mu a = mu b := by omega
        have hS' : ((mu (a + 1) : ℝ) + mu a) = mu (b + 1) + mu b := by exact_mod_cast hS
        have hma' : (mu a : ℝ) = mu b := by exact_mod_cast hma
        rw [hS'] at hab
        have : (a : ℝ) = b := by linarith
        have : a = b := by exact_mod_cast this
        omega
      · have hn : ((mu (a + 1) : ℤ) + mu a - (mu (b + 1) + mu b)) ≠ 0 := by omega
        have hirr := irrational_pi.mul_intCast hn
        apply hirr.ne_int ((a : ℤ) - mu a - (b - mu b))
        push_cast
        linarith
    intro a b hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key a b h hab
    · exact key b a h hab.symm
  refine ⟨hinj, ?_⟩
  refine Set.infinite_of_injective_forall_mem hinj (fun k => ?_)
  refine ⟨exAPre k, exBPre (k + 1), k, k + 1, Or.inr ⟨by simp [exAPre], by omega, by simp [exBPre], ?_⟩⟩
  have hB : (exBPre (k + 1)).take k = exBPre k := by
    unfold exBPre
    rw [List.ofFn_succ', List.concat_eq_append, List.take_append_of_le_length (by simp)]
    simp
  have hA : (exAPre k).take k = exAPre k := List.take_of_length_le (by simp [exAPre])
  have hB' : (exBPre (k + 1)).take (k + 1) = exBPre (k + 1) := List.take_of_length_le (by simp [exBPre])
  simp only [dmat, Nat.add_sub_cancel, hA, hB, hB', exDelta]

end Ex

end MasekPaterson.Necessity

open MasekPaterson.Necessity


theorem solution (i j k : ℕ) :
    (Even ((i : ℤ) - j) →
      (k : ℝ) - (mu (i + k) : ℝ) + (mu i : ℝ) ≤ exPstar i j k) ∧
    (Odd ((i : ℤ) - j) →
      ((mu (i + k) : ℝ) - (mu i : ℝ) + (mu (j + k) : ℝ) - (mu j : ℝ)) * Real.pi
        ≤ exPstar i j k) := by
  exact Pstar_lower_bound_core i j k
