-- Prove2me | solution 1 for GroupIsoPoly.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:34:39.499128+00:00
-- url     : https://prove2.me/submissions/5c6d36c2-ae56-4ee5-8647-92b4b25a3a11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_encPair
import Theorems.Thm_GroupIsoPoly_theorem_9_1

set_option autoImplicit false

namespace GroupIsoPoly.KeepHead
open Turing

variable (tm : FinTM2)

/-- translate a statement of `tm`, redirecting `halt` to the cleanup label -/
def tr : TM2.Stmt tm.Γ tm.Λ tm.σ → TM2.Stmt tm.Γ (tm.Λ ⊕ Bool) (tm.σ × Bool × Bool)
  | .push k f q => .push k (fun s => f s.1) (tr q)
  | .peek k f q => .peek k (fun s o => (f s.1 o, s.2)) (tr q)
  | .pop k f q => .pop k (fun s o => (f s.1 o, s.2)) (tr q)
  | .load a q => .load (fun s => (a s.1, s.2)) (tr q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (tr q₁) (tr q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr false)

/-- the program of the composed machine -/
def prog (dec : tm.Γ tm.k₁ ≃ Bool) :
    tm.Λ ⊕ Bool → TM2.Stmt tm.Γ (tm.Λ ⊕ Bool) (tm.σ × Bool × Bool)
  | .inl l => tr tm (tm.m l)
  | .inr false => .pop tm.k₁ (fun s o => (s.1, (match o with | some g => dec g | none => false), false))
      (.goto fun _ => .inr true)
  | .inr true => .pop tm.k₁ (fun s o => (s.1, s.2.1, o.isSome))
      (.branch (fun s => s.2.2) (.goto fun _ => .inr true)
        (.push tm.k₁ (fun s => dec.symm s.2.1)
          (.load (fun _ => (tm.initialState, false, false)) .halt)))

/-- the composed machine -/
def tm' (dec : tm.Γ tm.k₁ ≃ Bool) : FinTM2 :=
  @FinTM2.mk tm.K tm.kDecidableEq tm.kFin tm.k₀ tm.k₁ tm.Γ (tm.Λ ⊕ Bool) (.inl tm.main)
    (@instFintypeSum _ _ tm.ΛFin _) (tm.σ × Bool × Bool) (tm.initialState, false, false)
    (@instFintypeProd _ _ tm.σFin _) tm.Γk₀Fin (prog tm dec)

/-- keep only the first output bit -/
def keepHead (M : TM2ComputableAux Bool Bool) : TM2ComputableAux Bool Bool where
  tm := tm' M.tm M.outputAlphabet
  inputAlphabet := M.inputAlphabet
  outputAlphabet := M.outputAlphabet

/-- embedding of configurations -/
def E (dec : tm.Γ tm.k₁ ≃ Bool) (c : tm.Cfg) : (tm' tm dec).Cfg :=
  ⟨some (match c.l with | some l => .inl l | none => .inr false), (c.var, false, false), c.stk⟩

lemma stepAux_tr (dec : tm.Γ tm.k₁ ≃ Bool) (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ)
    (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (tr tm q) ((v, false, false) : tm.σ × Bool × Bool) S =
      E tm dec (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr, TM2.stepAux]
    cases f v
    · exact ih₂ _ _
    · exact ih₁ _ _
  | goto f => rfl
  | halt => rfl


variable {tm}

lemma step_E (dec : tm.Γ tm.k₁ ≃ Bool) (c : tm.Cfg) (l : tm.Λ) (hl : c.l = some l) :
    (tm' tm dec).step (E tm dec c) = some (E tm dec (TM2.stepAux (tm.m l) c.var c.stk)) := by
  obtain ⟨l', v, S⟩ := c
  simp only at hl
  subst hl
  exact congrArg some (stepAux_tr tm dec (tm.m l) v S)

lemma iter_none {α : Type*} (f : α → Option α) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma iter_sim (dec : tm.Γ tm.k₁ ≃ Bool) (n : ℕ) :
    ∀ c d : tm.Cfg, (flip bind tm.step)^[n] (some c) = some d →
      (flip bind (tm' tm dec).step)^[n] (some (E tm dec c)) = some (E tm dec d) := by
  induction n with
  | zero => intro c d h; simp only [Function.iterate_zero, id] at h ⊢; rw [Option.some_inj.mp h]
  | succ n ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h ⊢
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      have : (flip bind tm.step) (some (⟨none, v, S⟩ : tm.Cfg)) = none := rfl
      rw [this, iter_none] at h
      exact absurd h (by simp)
    | some l =>
      have h1 : (flip bind tm.step) (some (⟨some l, v, S⟩ : tm.Cfg)) =
          some (TM2.stepAux (tm.m l) v S) := rfl
      have h2 : (flip bind (tm' tm dec).step) (some (E tm dec ⟨some l, v, S⟩)) =
          some (E tm dec (TM2.stepAux (tm.m l) v S)) := step_E dec ⟨some l, v, S⟩ l rfl
      rw [h1] at h
      rw [h2]
      exact ih _ _ h

lemma loop (dec : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (v : tm.σ) (L : List (tm.Γ tm.k₁)) :
    ∀ (x : Bool) (S : ∀ k, List (tm.Γ k)), S tm.k₁ = L →
      (flip bind (tm' tm dec).step)^[L.length + 1]
          (some (⟨some (.inr true), (v, b, x), S⟩ : (tm' tm dec).Cfg)) =
        some ⟨none, (tm.initialState, false, false), Function.update S tm.k₁ [dec.symm b]⟩ := by
  induction L with
  | nil =>
    intro x S hS
    simp only [List.length_nil, zero_add, Function.iterate_one]
    show some (TM2.stepAux (prog tm dec (.inr true)) (v, b, x) S) = _
    simp only [prog, TM2.stepAux, hS, List.head?_nil, Option.isSome_none, cond_false,
      Function.update_self, List.tail_nil, Function.update_idem]
    rfl
  | cons a L ih =>
    intro x S hS
    rw [List.length_cons, Function.iterate_succ_apply]
    have h1 : (flip bind (tm' tm dec).step)
        (some (⟨some (.inr true), (v, b, x), S⟩ : (tm' tm dec).Cfg)) =
        some ⟨some (.inr true), (v, b, true), Function.update S tm.k₁ L⟩ := by
      show some (TM2.stepAux (prog tm dec (.inr true)) (v, b, x) S) = _
      simp [prog, TM2.stepAux, hS]
      rfl
    rw [h1]
    refine (ih true (Function.update S tm.k₁ L) (by simp)).trans ?_
    exact congrArg (fun st => some (⟨none, (tm.initialState, false, false), st⟩ : (tm' tm dec).Cfg))
      (Function.update_idem _ _ _)


lemma haltList_stk_self (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

lemma haltList_stk_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) (k : tm.K) (hk : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := by
  simp [haltList, hk]

theorem keepHead_outputs (M : TM2ComputableAux Bool Bool) (inp : List Bool) (b : Bool)
    (rest : List Bool) (T : ℕ) (h : HMBinPacking.OutputsWithin M inp (b :: rest) T) :
    HMBinPacking.OutputsWithin (keepHead M) inp [b] (T + rest.length + 2) := by
  obtain ⟨⟨⟨n, hn⟩, hle⟩⟩ := h
  have h1 := iter_sim M.outputAlphabet n _ _ hn
  set S0 := (haltList M.tm ((b :: rest).map M.outputAlphabet.symm)).stk with hS0
  have hS0k : S0 M.tm.k₁ = M.outputAlphabet.symm b :: rest.map M.outputAlphabet.symm := by
    rw [hS0, haltList_stk_self]; rfl
  have h2 : (flip bind (tm' M.tm M.outputAlphabet).step)
      (some (E M.tm M.outputAlphabet (haltList M.tm ((b :: rest).map M.outputAlphabet.symm)))) =
      some ⟨some (.inr true), (M.tm.initialState, b, false),
        Function.update S0 M.tm.k₁ (rest.map M.outputAlphabet.symm)⟩ := by
    show some (TM2.stepAux (prog M.tm M.outputAlphabet (.inr false))
      (M.tm.initialState, false, false) S0) = _
    simp only [prog, TM2.stepAux, hS0k, List.head?_cons, List.tail_cons, Equiv.apply_symm_apply]
    rfl
  have h3 := loop M.outputAlphabet b M.tm.initialState (rest.map M.outputAlphabet.symm) false
    (Function.update S0 M.tm.k₁ (rest.map M.outputAlphabet.symm)) (by simp)
  have key : (flip bind (tm' M.tm M.outputAlphabet).step)^[(rest.map M.outputAlphabet.symm).length
      + 1 + (1 + n)] (some (E M.tm M.outputAlphabet (initList M.tm (inp.map M.inputAlphabet.symm)))) =
      some ⟨none, (M.tm.initialState, false, false), Function.update (Function.update S0 M.tm.k₁
        (rest.map M.outputAlphabet.symm)) M.tm.k₁ [M.outputAlphabet.symm b]⟩ := by
    rw [Function.iterate_add_apply _ _ (1 + n), Function.iterate_add_apply _ 1 n, h1,
      Function.iterate_one, h2]
    exact h3
  refine ⟨⟨⟨(rest.map M.outputAlphabet.symm).length + 1 + (1 + n), key.trans ?_⟩, ?_⟩⟩
  · simp only [Option.map_some]
    congr 1
    show (⟨none, (M.tm.initialState, false, false), _⟩ : (tm' M.tm M.outputAlphabet).Cfg) =
      haltList (tm' M.tm M.outputAlphabet) ([b].map M.outputAlphabet.symm)
    have hst : ∀ k, Function.update (Function.update S0 M.tm.k₁ (rest.map M.outputAlphabet.symm))
        M.tm.k₁ [M.outputAlphabet.symm b] k =
        (haltList (tm' M.tm M.outputAlphabet) ([b].map M.outputAlphabet.symm)).stk k := by
      intro k
      by_cases hk : k = M.tm.k₁
      · subst hk
        erw [Function.update_self]
        exact (haltList_stk_self (tm' M.tm M.outputAlphabet) _).symm
      · erw [Function.update_of_ne hk, Function.update_of_ne hk, hS0, haltList_stk_ne _ _ _ hk]
        exact (haltList_stk_ne (tm' M.tm M.outputAlphabet) _ k hk).symm
    show _ = (⟨none, (M.tm.initialState, false, false), _⟩ : (tm' M.tm M.outputAlphabet).Cfg)
    congr 1
    funext k
    exact hst k
  · have hle' : n ≤ T := hle
    simp only [List.length_map]
    omega


section growth

/-- maximal number of pushes along an execution path of a statement -/
def pushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

/-- total stack size -/
def tot (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) : ℕ :=
  @Finset.sum tm.K ℕ _ (@Finset.univ tm.K tm.kFin) fun k => (S k).length

/-- pushes per step -/
def P (tm : FinTM2) : ℕ :=
  @Finset.sum tm.Λ ℕ _ (@Finset.univ tm.Λ tm.ΛFin) fun l => pushes (tm.m l)

lemma tot_update (tm : FinTM2) (S : ∀ k, List (tm.Γ k)) (k : tm.K) (L : List (tm.Γ k)) :
    tot tm (Function.update S k L) + (S k).length = tot tm S + L.length := by
  letI := tm.kFin
  unfold tot
  have h : ∀ k', (Function.update S k L k').length =
      Function.update (fun k' => (S k').length) k L.length k' := by
    intro k'
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk]
  simp_rw [h]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ (fun k' => (S k').length) (Finset.mem_univ k)]
  omega

lemma stepAux_tot (tm : FinTM2) (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    tot tm (TM2.stepAux q v S).stk ≤ tot tm S + pushes q := by
  induction q generalizing v S with
  | push k f q ih =>
    have h1 := ih v (Function.update S k (f v :: S k))
    have h2 := tot_update tm S k (f v :: S k)
    simp only [List.length_cons] at h2
    simp only [TM2.stepAux, pushes]
    omega
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have h1 := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have h2 := tot_update tm S k (S k).tail
    have h3 : (S k).tail.length ≤ (S k).length := by simp
    simp only [TM2.stepAux, pushes]
    omega
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · have := ih₂ v S; simp only [cond_false]; omega
    · have := ih₁ v S; simp only [cond_true]; omega
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

lemma iter_tot (tm : FinTM2) (n : ℕ) :
    ∀ c d : tm.Cfg, (flip bind tm.step)^[n] (some c) = some d →
      tot tm d.stk ≤ tot tm c.stk + P tm * n := by
  induction n with
  | zero => intro c d h; simp only [Function.iterate_zero, id, Option.some_inj] at h; subst h; simp
  | succ n ih =>
    intro c d h
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      have : (flip bind tm.step) (some (⟨none, v, S⟩ : tm.Cfg)) = none := rfl
      rw [this, iter_none] at h
      exact absurd h (by simp)
    | some l =>
      have h1 : (flip bind tm.step) (some (⟨some l, v, S⟩ : tm.Cfg)) =
          some (TM2.stepAux (tm.m l) v S) := rfl
      rw [h1] at h
      have h2 := ih _ _ h
      have h3 := stepAux_tot tm (tm.m l) v S
      have h4 : pushes (tm.m l) ≤ P tm := by
        letI := tm.ΛFin
        exact Finset.single_le_sum (f := fun l => pushes (tm.m l)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ l)
      simp only at h2 ⊢
      rw [Nat.mul_succ]
      omega

lemma tot_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tot tm (initList tm s).stk = s.length := by
  letI := tm.kFin
  unfold tot
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk; simp [initList, hk]
  · simp

lemma le_tot_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : s.length ≤ tot tm (haltList tm s).stk := by
  letI := tm.kFin
  unfold tot
  have := Finset.single_le_sum (f := fun k => ((haltList tm s).stk k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ tm.k₁)
  simp only [haltList_stk_self] at this
  exact this

theorem out_len (M : TM2ComputableAux Bool Bool) (inp out : List Bool) (T : ℕ)
    (h : HMBinPacking.OutputsWithin M inp out T) : out.length ≤ inp.length + P M.tm * T := by
  obtain ⟨⟨⟨n, hn⟩, hle⟩⟩ := h
  have hle' : n ≤ T := hle
  have h1 := iter_tot M.tm n _ _ hn
  rw [tot_initList] at h1
  have h2 := le_tot_haltList M.tm (out.map M.outputAlphabet.symm)
  simp only [List.length_map] at h1 h2
  have h3 : P M.tm * n ≤ P M.tm * T := Nat.mul_le_mul_left _ hle'
  omega

end growth

end GroupIsoPoly.KeepHead

namespace GroupIsoPoly.KeepHead
open ExponomialAssortment.FPTAS (encodeNat)

lemma encodeNat_len (x : ℕ) : (encodeNat x).length ≤ 2 * x + 1 := by
  have h : x.bits.length ≤ x := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Nat.lt_two_pow_self
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

lemma encTable_len (N : ℕ) (t : Fin N → Fin N → Fin N) :
    (encTable N t).length ≤ N * (N * (2 * N + 1)) := by
  unfold encTable
  rw [List.length_flatten]
  have h1 : ∀ x ∈ (List.ofFn fun i : Fin N =>
      (List.ofFn fun j : Fin N => encodeNat (t i j : ℕ)).flatten).map List.length,
      x ≤ N * (2 * N + 1) := by
    intro x hx
    simp only [List.mem_map, List.mem_ofFn] at hx
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hx
    rw [List.length_flatten]
    have h2 : ∀ y ∈ (List.ofFn fun j : Fin N => encodeNat (t i j : ℕ)).map List.length,
        y ≤ 2 * N + 1 := by
      intro y hy
      simp only [List.mem_map, List.mem_ofFn] at hy
      obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hy
      have := encodeNat_len (t i j : ℕ)
      have := (t i j).isLt
      omega
    have := List.sum_le_card_nsmul _ _ h2
    simpa using this
  have := List.sum_le_card_nsmul _ _ h1
  simpa using this

lemma encPair_len (N : ℕ) (tG tH : Fin N → Fin N → Fin N) :
    (encPair N tG tH).length ≤ 4 * (N + 1) ^ 3 := by
  unfold encPair
  simp only [List.length_append]
  have h1 := encodeNat_len N
  have h2 := encTable_len N tG
  have h3 := encTable_len N tH
  nlinarith

lemma outputsWithin_mono {M : Turing.TM2ComputableAux Bool Bool} {i o : List Bool} {t t' : ℕ}
    (h : HMBinPacking.OutputsWithin M i o t) (ht : t ≤ t') : HMBinPacking.OutputsWithin M i o t' := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo, h.steps_le_m.trans ht⟩⟩

end GroupIsoPoly.KeepHead

open GroupIsoPoly GroupIsoPoly.KeepHead

open Classical in
theorem solution :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (N : ℕ) (G H : Type) [Group G] [Group H] (eG : G ≃ Fin N) (eH : H ≃ Fin N),
        HMBinPacking.OutputsWithin M (encPair N (cayley eG) (cayley eH))
          [decide (Nonempty (G ≃* H))] (C * (N + 1) ^ C) := by
  obtain ⟨M, C, hM⟩ := GroupIsoPoly.theorem_9_1
  refine ⟨keepHead M, (C + 1) * (P M.tm + 1) + 6, ?_⟩
  intro N G H _ _ eG eH
  obtain ⟨ans, hcorr, hout⟩ := hM N G H eG eH
  obtain ⟨rest, hrest⟩ : ∃ rest, encIsoAnswer eG eH ans = decide (Nonempty (G ≃* H)) :: rest := by
    cases ans with
    | none =>
      refine ⟨[], ?_⟩
      have h0 : (Set.univ : Set (G ≃* H)) = ∅ := hcorr.1.mp rfl
      have hne : ¬ Nonempty (G ≃* H) := fun ⟨φ⟩ => by
        have := Set.mem_univ φ
        rw [h0] at this
        exact this
      simp [encIsoAnswer, encAnswer, hne]
    | some a =>
      have hne : Nonempty (G ≃* H) := ⟨a.1⟩
      rw [decide_eq_true hne]
      exact ⟨_, rfl⟩
  rw [hrest] at hout
  have hlen := out_len M _ _ _ hout
  have hk := keepHead_outputs M _ _ rest _ hout
  refine outputsWithin_mono hk ?_
  have hin := encPair_len N (cayley eG) (cayley eH)
  simp only [List.length_cons] at hlen
  set X := N + 1 with hX
  set D := (C + 1) * (P M.tm + 1) + 6 with hD
  have hX1 : 1 ≤ X := by omega
  have e1 : X ^ C ≤ X ^ D := Nat.pow_le_pow_right hX1 (by nlinarith)
  have e2 : X ^ 3 ≤ X ^ D := Nat.pow_le_pow_right hX1 (by nlinarith)
  have e3 : 1 ≤ X ^ D := Nat.one_le_pow _ _ hX1
  have e4 : P M.tm * (C * X ^ C) ≤ P M.tm * (C * X ^ D) := by
    apply Nat.mul_le_mul_left; exact Nat.mul_le_mul_left _ e1
  have e5 : C * X ^ C ≤ C * X ^ D := Nat.mul_le_mul_left _ e1
  have e6 : (P M.tm + 1) * C + 5 ≤ D := by rw [hD]; nlinarith
  calc C * X ^ C + rest.length + 2
      ≤ C * X ^ D + (4 * X ^ D + P M.tm * (C * X ^ D)) + 2 := by omega
    _ = ((P M.tm + 1) * C + 4) * X ^ D + 2 := by ring
    _ ≤ ((P M.tm + 1) * C + 5) * X ^ D + X ^ D := by nlinarith
    _ ≤ D * X ^ D := by nlinarith
