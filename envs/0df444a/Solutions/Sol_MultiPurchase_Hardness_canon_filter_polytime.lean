-- Prove2me | solution 1 for MultiPurchase.Hardness.canon_filter_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:36:26.765066+00:00
-- url     : https://prove2.me/submissions/f361fb99-13a0-4aea-bf27-26f72472aca8

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

namespace CanonFilter

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

/-! ## Alphabet, registers, and basic stack-program helpers -/

abbrev Sym : Type := Option (BSym ⊕ Bool)

abbrev symZero  : Sym := some (Sum.inl BSym.zero)
abbrev symOne   : Sym := some (Sum.inl BSym.one)
abbrev symMinus : Sym := some (Sum.inl BSym.minus)
abbrev symSep   : Sym := some (Sum.inl BSym.sep)
abbrev symHash  : Sym := none

inductive K
  | ki | ko | fail | A | B | T1 | T2 | C
  deriving DecidableEq

instance : Fintype K :=
  ⟨⟨([K.ki, K.ko, K.fail, K.A, K.B, K.T1, K.T2, K.C] : List K), by decide⟩,
   by intro x; cases x <;> decide⟩

def noop : StackProg K Sym := .act (fun _ _ => .keep)

lemma exec_noop (s : K → List Sym) : noop.Exec s s 1 := by
  have h := StackProg.Exec.act (fun (_ : K → Option Sym) (_ : K) => (StackAct.keep : StackAct Sym)) s
  have heq : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
    funext k; rfl
  rwa [heq] at h

lemma exec_det {p : StackProg K Sym} {s s₁ s₂ : K → List Sym} {t₁ t₂ : ℕ}
    (h₁ : p.Exec s s₁ t₁) (h₂ : p.Exec s s₂ t₂) : s₁ = s₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing s₂ t₂ with
  | act f s =>
    cases h₂
    exact ⟨rfl, rfl⟩
  | seq hp hq ihp ihq =>
    cases h₂ with
    | seq hp2 hq2 =>
      obtain ⟨rfl, rfl⟩ := ihp hp2
      obtain ⟨rfl, rfl⟩ := ihq hq2
      exact ⟨rfl, rfl⟩
  | branchTrue ht hp ih =>
    cases h₂ with
    | branchTrue _ hp2 =>
      obtain ⟨rfl, rfl⟩ := ih hp2
      exact ⟨rfl, rfl⟩
    | branchFalse hf _ => rw [ht] at hf; cases hf
  | branchFalse hf hq ih =>
    cases h₂ with
    | branchTrue ht _ => rw [hf] at ht; cases ht
    | branchFalse _ hq2 =>
      obtain ⟨rfl, rfl⟩ := ih hq2
      exact ⟨rfl, rfl⟩
  | loopFalse hf =>
    cases h₂ with
    | loopFalse _ => exact ⟨rfl, rfl⟩
    | loopTrue ht _ _ => rw [hf] at ht; cases ht
  | loopTrue ht hp hl ihp ihl =>
    cases h₂ with
    | loopFalse hf => rw [ht] at hf; cases hf
    | loopTrue _ hp2 hl2 =>
      obtain ⟨rfl, rfl⟩ := ihp hp2
      obtain ⟨rfl, rfl⟩ := ihl hl2
      exact ⟨rfl, rfl⟩

lemma exec_transfer_single (src dst : K) (hne : src ≠ dst) (s : K → List Sym) :
    (transferProg src (fun k => decide (k = dst))).Exec s
      (Function.update (Function.update s src []) dst ((s src).reverse ++ s dst))
      (3 * (s src).length + 1) := by
  have h := CookPvsNP.stack_transfer src (fun k => decide (k = dst)) s
  have heq : transferStore src (fun k => decide (k = dst)) s =
      Function.update (Function.update s src []) dst ((s src).reverse ++ s dst) := by
    funext k
    unfold transferStore
    by_cases h1 : k = dst
    · subst k
      simp [hne.symm]
    · by_cases h2 : k = src
      · subst k; simp [h1]
      · simp [h1, h2]
  rwa [heq] at h

/-! ## Binary representation of natural numbers on stacks -/

def bitSym (b : Bool) : Sym := if b then symOne else symZero

def natStack (n : ℕ) : List Sym := (Nat.bits n).map bitSym

def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * ofBits bs + if b then 1 else 0

lemma bitSym_inj {a b : Bool} (h : bitSym a = bitSym b) : a = b := by
  cases a <;> cases b <;> simp [bitSym] at h ⊢

@[simp] lemma bitSym_false : bitSym false = symZero := rfl
@[simp] lemma bitSym_true : bitSym true = symOne := rfl

lemma ofBits_bits (n : ℕ) : ofBits (Nat.bits n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b m h ih =>
    rw [Nat.bits_append_bit m b h, ofBits, ih]
    cases b <;> simp [Nat.bit]

lemma ofBits_append_false (l : List Bool) : ofBits (l ++ [false]) = ofBits l := by
  induction l with
  | nil => rfl
  | cons b t ih => simp [ofBits, ih]

lemma ofBits_dropWhile_rev (r : List Bool) :
    ofBits (r.dropWhile (fun b => !b)).reverse = ofBits r.reverse := by
  induction r with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simp only [List.dropWhile_cons, Bool.not_false, ↓reduceIte, List.reverse_cons]
      rw [ih, ofBits_append_false]
    · simp

lemma bits_ofBits_of_last_true : ∀ (l : List Bool),
    (∀ hne : l ≠ [], l.getLast hne = true) → Nat.bits (ofBits l) = l
  | [], _ => by simp [ofBits]
  | [b], h => by
    have hb : b = true := h (by simp)
    subst hb
    simp [ofBits]
  | b :: c :: t, h => by
    have hct : ∀ hne : c :: t ≠ [], (c :: t).getLast hne = true := by
      intro hne
      have := h (by simp)
      simpa using this
    have ih := bits_ofBits_of_last_true (c :: t) hct
    have hne0 : ofBits (c :: t) ≠ 0 := by
      intro hz
      rw [hz, Nat.zero_bits] at ih
      cases ih
    have heq : ofBits (b :: c :: t) = Nat.bit b (ofBits (c :: t)) := by
      cases b <;> simp [ofBits, Nat.bit]
    rw [heq, Nat.bits_append_bit _ _ (fun h0 => absurd h0 hne0), ih]

lemma dropWhile_rev_last_true : ∀ (r : List Bool) (hne : (r.dropWhile (fun b => !b)).reverse ≠ []),
    (r.dropWhile (fun b => !b)).reverse.getLast hne = true
  | [], hne => by simp at hne
  | false :: t, hne => dropWhile_rev_last_true t (by simpa using hne)
  | true :: t, _ => by simp

lemma dropWhile_rev_eq_bits (r : List Bool) :
    (r.dropWhile (fun b => !b)).reverse = Nat.bits (ofBits r.reverse) := by
  rw [← ofBits_dropWhile_rev r]
  exact (bits_ofBits_of_last_true _ (dropWhile_rev_last_true r)).symm

lemma natStack_zero : natStack 0 = [] := by simp [natStack]
lemma natStack_one : natStack 1 = [symOne] := by simp [natStack]

lemma natStack_eq_nil_iff {n : ℕ} : natStack n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hb : Nat.bits n = [] := by
      unfold natStack at h
      exact List.map_eq_nil_iff.mp h
    have := ofBits_bits n
    rw [hb] at this
    exact this.symm
  · rintro rfl; exact natStack_zero

lemma natStack_even {n : ℕ} (hn : n ≠ 0) (he : n % 2 = 0) :
    natStack n = symZero :: natStack (n / 2) := by
  have h2 : 2 * (n / 2) = n := by omega
  have hne : n / 2 ≠ 0 := by omega
  unfold natStack
  conv_lhs => rw [← h2]
  rw [Nat.bit0_bits (n / 2) hne]
  rfl

lemma natStack_odd {n : ℕ} (ho : n % 2 = 1) :
    natStack n = symOne :: natStack (n / 2) := by
  have h2 : 2 * (n / 2) + 1 = n := by omega
  unfold natStack
  conv_lhs => rw [← h2]
  rw [Nat.bit1_bits (n / 2)]
  rfl

lemma natStack_eq_one_iff {n : ℕ} : natStack n = [symOne] ↔ n = 1 := by
  constructor
  · intro h
    have hb : Nat.bits n = [true] := by
      unfold natStack at h
      cases hbits : Nat.bits n with
      | nil => rw [hbits] at h; cases h
      | cons x xs =>
        rw [hbits] at h
        simp only [List.map_cons, List.cons.injEq] at h
        have hx : x = true := bitSym_inj h.1
        have hxs : xs = [] := List.map_eq_nil_iff.mp h.2
        simp [hx, hxs]
    have := ofBits_bits n
    rw [hb] at this
    simpa [ofBits] using this.symm
  · rintro rfl; exact natStack_one

lemma natStack_head?_zero {n : ℕ} : (natStack n).head? = some symZero ↔ n ≠ 0 ∧ n % 2 = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn; simp [natStack_zero] at h
    · by_cases he : n % 2 = 0
      · exact ⟨hn, he⟩
      · have ho : n % 2 = 1 := by omega
        rw [natStack_odd ho] at h
        simp at h
  · rintro ⟨hn, he⟩
    rw [natStack_even hn he]
    rfl

lemma natStack_head?_one {n : ℕ} : (natStack n).head? = some symOne ↔ n % 2 = 1 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn; simp [natStack_zero] at h
    · by_cases he : n % 2 = 0
      · rw [natStack_even hn he] at h; simp at h
      · omega
  · intro ho
    rw [natStack_odd ho]
    rfl

lemma bits_length_mono : ∀ {n m : ℕ}, m ≤ n → (Nat.bits m).length ≤ (Nat.bits n).length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hmn
    by_cases hm : m = 0
    · subst hm; simp
    · have hn : n ≠ 0 := by omega
      have hdiv_le : m / 2 ≤ n / 2 := Nat.div_le_div_right hmn
      have hdiv_lt : n / 2 < n := by omega
      have hrec := ih (n / 2) hdiv_lt hdiv_le
      have hlm : (Nat.bits m).length = (Nat.bits (m / 2)).length + 1 := by
        by_cases he : m % 2 = 0
        · have := natStack_even hm he
          unfold natStack at this
          have := congrArg List.length this
          simpa using this
        · have := natStack_odd (by omega : m % 2 = 1)
          unfold natStack at this
          have := congrArg List.length this
          simpa using this
      have hln : (Nat.bits n).length = (Nat.bits (n / 2)).length + 1 := by
        by_cases he : n % 2 = 0
        · have := natStack_even hn he
          unfold natStack at this
          have := congrArg List.length this
          simpa using this
        · have := natStack_odd (by omega : n % 2 = 1)
          unfold natStack at this
          have := congrArg List.length this
          simpa using this
      omega

lemma natStack_length_odd_sub_div2 {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (hba : b < a) :
    (natStack ((a - b) / 2)).length < (natStack a).length := by
  unfold natStack
  simp only [List.length_map]
  have hle : (a - b) / 2 ≤ a / 2 := by omega
  have h1 := bits_length_mono hle
  have h2 : (Nat.bits a).length = (Nat.bits (a / 2)).length + 1 := by
    have := natStack_odd ha
    unfold natStack at this
    have := congrArg List.length this
    simpa using this
  omega

/-! ## Number theory helpers for binary GCD -/

lemma gcd_div2_left_of_odd {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd (a / 2) b = Nat.gcd a b := by
  have hcop : Nat.Coprime 2 b := by
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hb
  have h2 : 2 * (a / 2) = a := by omega
  conv_rhs => rw [← h2]
  exact (hcop.gcd_mul_left_cancel (a / 2)).symm

lemma gcd_odd_sub_div2_left {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (hba : b < a) :
    Nat.gcd ((a - b) / 2) b = Nat.gcd a b := by
  have he : (a - b) % 2 = 0 := by omega
  rw [gcd_div2_left_of_odd he hb]
  have hadd : a - b + b = a := by omega
  conv_rhs => rw [← hadd]
  exact (Nat.gcd_add_self_left b (a - b)).symm

lemma gcd_ne_one_of_both_even {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    Nat.gcd a b ≠ 1 := by
  intro h1
  have h2a : 2 ∣ a := Nat.dvd_of_mod_eq_zero ha
  have h2b : 2 ∣ b := Nat.dvd_of_mod_eq_zero hb
  have h2g : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2a h2b
  rw [h1] at h2g
  omega

/-! ## Helper: strip leading `symZero`s -/

def stripZerosProg (k : K) : StackProg K Sym :=
  .loop (fun h => decide (h k = some symZero)) (popProg k)

lemma exec_stripZeros (k : K) :
    ∀ (l : List Sym) (s : K → List Sym), s k = l →
      ∃ t ≤ 3 * l.length + 1,
        (stripZerosProg k).Exec s
          (Function.update s k (l.dropWhile (fun x => decide (x = symZero)))) t := by
  intro l
  induction l with
  | nil =>
    intro s hs
    refine ⟨1, by omega, ?_⟩
    have h := StackProg.Exec.loopFalse (p := popProg k)
      (test := fun h => decide (h k = some symZero)) (s := s) (by simp [hs])
    have hu : Function.update s k [] = s := by
      funext j; by_cases hj : j = k
      · subst j; simp [hs]
      · simp [hj]
    simpa [stripZerosProg, hu] using h
  | cons x xs ih =>
    intro s hs
    by_cases hx : x = symZero
    · subst x
      have hpop := (CookPvsNP.stack_basic_macros k s).2.1
      rw [hs] at hpop
      simp only [List.tail_cons] at hpop
      obtain ⟨t, ht, hex⟩ := ih (Function.update s k xs) (by simp)
      refine ⟨1 + 1 + 1 + t, by simp; omega, ?_⟩
      have hloop := StackProg.Exec.loopTrue (test := fun h => decide (h k = some symZero))
        (by simp [hs]) hpop hex
      have hu : Function.update (Function.update s k xs) k (xs.dropWhile (fun x => decide (x = symZero))) =
          Function.update s k ((symZero :: xs).dropWhile (fun x => decide (x = symZero))) := by
        simp [Function.update_idem]
      rwa [hu] at hloop
    · refine ⟨1, by simp, ?_⟩
      have h := StackProg.Exec.loopFalse (p := popProg k)
        (test := fun h => decide (h k = some symZero)) (s := s) (by simp [hs, hx])
      have hdw : (x :: xs).dropWhile (fun y => decide (y = symZero)) = x :: xs := by
        simp [hx]
      have hu : Function.update s k (x :: xs) = s := by
        funext j; by_cases hj : j = k
        · subst j; simp [hs]
        · simp [hj]
      simpa [stripZerosProg, hdw, hu] using h

lemma dropWhile_map_bitSym (r : List Bool) :
    (r.map bitSym).dropWhile (fun x => decide (x = symZero)) = (r.dropWhile (fun b => !b)).map bitSym := by
  induction r with
  | nil => rfl
  | cons b t ih =>
    cases b
    · simp [ih]
    · simp

/-! ## Comparison subroutine `cmpABProg` -/

def cmpAct (h : K → Option Sym) (k : K) : StackAct Sym :=
  match k with
  | .A => .pop
  | .B => .pop
  | .T1 => match h .A with | some a => .push a | none => .keep
  | .T2 => match h .B with | some b => .push b | none => .keep
  | .C =>
      let bx := decide (h .A = some symOne)
      let by_ := decide (h .B = some symOne)
      if bx == by_ then .keep
      else if bx then .push symOne
      else .push symZero
  | _ => .keep

def cmpLoopProg : StackProg K Sym :=
  .loop (fun h => (h .A).isSome || (h .B).isSome) (.act cmpAct)

def cmpABProg : StackProg K Sym :=
  .seq cmpLoopProg
    (.seq (transferProg .T1 (fun k => decide (k = .A)))
          (transferProg .T2 (fun k => decide (k = .B))))

def cmpRun : List Bool → List Bool → List Sym → List Sym
  | [], [], c => c
  | x :: xs, [], c => cmpRun xs [] (if x then symOne :: c else c)
  | [], y :: ys, c => cmpRun [] ys (if y then symZero :: c else c)
  | x :: xs, y :: ys, c =>
      cmpRun xs ys (if x == y then c else if x then symOne :: c else symZero :: c)

lemma cmpRun_length : ∀ (u v : List Bool) (c : List Sym),
    (cmpRun u v c).length ≤ max u.length v.length + c.length
  | [], [], c => by simp [cmpRun]
  | x :: xs, [], c => by
    have ih := cmpRun_length xs [] (if x then symOne :: c else c)
    cases x <;> simp [cmpRun] at ih ⊢ <;> omega
  | [], y :: ys, c => by
    have ih := cmpRun_length [] ys (if y then symZero :: c else c)
    cases y <;> simp [cmpRun] at ih ⊢ <;> omega
  | x :: xs, y :: ys, c => by
    have ih := cmpRun_length xs ys (if x == y then c else if x then symOne :: c else symZero :: c)
    cases x <;> cases y <;> simp [cmpRun] at ih ⊢ <;> omega

lemma cmpRun_head? : ∀ (u v : List Bool) (c : List Sym),
    (cmpRun u v c).head? =
      if ofBits u < ofBits v then some symZero
      else if ofBits v < ofBits u then some symOne
      else c.head?
  | [], [], c => by simp [cmpRun, ofBits]
  | x :: xs, [], c => by
    rw [cmpRun, cmpRun_head? xs []]
    simp only [ofBits, Nat.not_lt_zero, ↓reduceIte]
    cases x <;> simp
  | [], y :: ys, c => by
    rw [cmpRun, cmpRun_head? [] ys]
    simp only [ofBits, Nat.not_lt_zero, ↓reduceIte]
    cases y <;> simp
  | x :: xs, y :: ys, c => by
    rw [cmpRun, cmpRun_head? xs ys]
    simp only [ofBits]
    cases x <;> cases y <;> simp <;> split_ifs <;> first | rfl | omega

def cmpEndState (u v : List Bool) (s : K → List Sym) : K → List Sym := fun k =>
  match k with
  | .A => []
  | .B => []
  | .T1 => (u.map bitSym).reverse ++ s .T1
  | .T2 => (v.map bitSym).reverse ++ s .T2
  | .C => cmpRun u v (s .C)
  | _ => s k

lemma exec_cmpLoop : ∀ (u v : List Bool) (s : K → List Sym),
    s .A = u.map bitSym → s .B = v.map bitSym →
    cmpLoopProg.Exec s (cmpEndState u v s) (3 * max u.length v.length + 1)
  | [], [], s, hA, hB => by
    have h := StackProg.Exec.loopFalse (p := .act cmpAct)
      (test := fun (h : K → Option Sym) => (h .A).isSome || (h .B).isSome) (s := s) (by simp [hA, hB])
    have heq : cmpEndState [] [] s = s := by
      funext k; cases k <;> simp [cmpEndState, cmpRun, hA, hB]
    simpa [cmpLoopProg, heq] using h
  | x :: xs, [], s, hA, hB => by
    have hstep := StackProg.Exec.act cmpAct s
    set s1 := StackProg.applyAct cmpAct s
    have hs1A : s1 .A = xs.map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hA, StackAct.apply]
    have hs1B : s1 .B = [].map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hB, StackAct.apply]
    have ih := exec_cmpLoop xs [] s1 hs1A hs1B
    have hloop := StackProg.Exec.loopTrue (test := fun (h : K → Option Sym) => (h .A).isSome || (h .B).isSome)
      (by simp [hA]) hstep ih
    have heq : cmpEndState xs [] s1 = cmpEndState (x :: xs) [] s := by
      funext k
      cases k <;> simp [cmpEndState, s1, StackProg.applyAct, cmpAct, hA, hB, StackAct.apply, cmpRun]
      · cases x <;> simp
    have ht : 1 + 1 + 1 + (3 * max xs.length 0 + 1) = 3 * max (x :: xs).length 0 + 1 := by
      simp; omega
    simp only [List.length_nil] at hloop ⊢
    rw [heq, ht] at hloop
    exact hloop
  | [], y :: ys, s, hA, hB => by
    have hstep := StackProg.Exec.act cmpAct s
    set s1 := StackProg.applyAct cmpAct s
    have hs1A : s1 .A = [].map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hA, StackAct.apply]
    have hs1B : s1 .B = ys.map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hB, StackAct.apply]
    have ih := exec_cmpLoop [] ys s1 hs1A hs1B
    have hloop := StackProg.Exec.loopTrue (test := fun (h : K → Option Sym) => (h .A).isSome || (h .B).isSome)
      (by simp [hB]) hstep ih
    have heq : cmpEndState [] ys s1 = cmpEndState [] (y :: ys) s := by
      funext k
      cases k <;> simp [cmpEndState, s1, StackProg.applyAct, cmpAct, hA, hB, StackAct.apply, cmpRun]
      · cases y <;> simp
    have ht : 1 + 1 + 1 + (3 * max 0 ys.length + 1) = 3 * max 0 (y :: ys).length + 1 := by
      simp; omega
    simp only [List.length_nil] at hloop ⊢
    rw [heq, ht] at hloop
    exact hloop
  | x :: xs, y :: ys, s, hA, hB => by
    have hstep := StackProg.Exec.act cmpAct s
    set s1 := StackProg.applyAct cmpAct s
    have hs1A : s1 .A = xs.map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hA, StackAct.apply]
    have hs1B : s1 .B = ys.map bitSym := by simp [s1, StackProg.applyAct, cmpAct, hB, StackAct.apply]
    have ih := exec_cmpLoop xs ys s1 hs1A hs1B
    have hloop := StackProg.Exec.loopTrue (test := fun (h : K → Option Sym) => (h .A).isSome || (h .B).isSome)
      (by simp [hA]) hstep ih
    have heq : cmpEndState xs ys s1 = cmpEndState (x :: xs) (y :: ys) s := by
      funext k
      cases k <;> simp [cmpEndState, s1, StackProg.applyAct, cmpAct, hA, hB, StackAct.apply, cmpRun]
      · cases x <;> cases y <;> simp
    have ht : 1 + 1 + 1 + (3 * max xs.length ys.length + 1) =
        3 * max (x :: xs).length (y :: ys).length + 1 := by
      simp; omega
    rw [heq, ht] at hloop
    exact hloop

lemma exec_cmpAB (s : K → List Sym) (a b : ℕ)
    (hA : s .A = natStack a) (hB : s .B = natStack b)
    (hT1 : s .T1 = []) (hT2 : s .T2 = []) (hC : s .C = []) :
    ∃ (cL : List Sym) (t : ℕ),
      t ≤ 6 * ((natStack a).length + (natStack b).length) + 5 ∧
      cmpABProg.Exec s (Function.update s .C cL) t ∧
      cL.length ≤ max (natStack a).length (natStack b).length ∧
      cL.head? = (if a < b then some symZero else if b < a then some symOne else none) := by
  have h1 := exec_cmpLoop (Nat.bits a) (Nat.bits b) s hA hB
  set s1 := cmpEndState (Nat.bits a) (Nat.bits b) s
  have h2 := exec_transfer_single .T1 .A (by decide) s1
  set s2 := Function.update (Function.update s1 .T1 []) .A ((s1 .T1).reverse ++ s1 .A)
  have h3 := exec_transfer_single .T2 .B (by decide) s2
  set s3 := Function.update (Function.update s2 .T2 []) .B ((s2 .T2).reverse ++ s2 .B)
  have hex := StackProg.Exec.seq h1 (StackProg.Exec.seq h2 h3)
  have hs3 : s3 = Function.update s .C (cmpRun (Nat.bits a) (Nat.bits b) []) := by
    funext k
    cases k <;> simp [s3, s2, s1, cmpEndState, hA, hB, hT1, hT2, hC, natStack]
  have hlen1 : (s1 .T1).length = (natStack a).length := by
    simp [s1, cmpEndState, hT1, natStack]
  have hlen2 : (s2 .T2).length = (natStack b).length := by
    simp [s2, s1, cmpEndState, hT2, natStack]
  have hcLen : (cmpRun (Nat.bits a) (Nat.bits b) []).length ≤
      max (natStack a).length (natStack b).length := by
    have := cmpRun_length (Nat.bits a) (Nat.bits b) []
    simpa [natStack] using this
  have hcHead : (cmpRun (Nat.bits a) (Nat.bits b) []).head? =
      if a < b then some symZero else if b < a then some symOne else none := by
    rw [cmpRun_head?, ofBits_bits, ofBits_bits]
    rfl
  refine ⟨cmpRun (Nat.bits a) (Nat.bits b) [], _, ?_, by rwa [hs3] at hex, hcLen, hcHead⟩
  rw [hlen1, hlen2]; simp [natStack]; omega

/-! ## Subtraction subroutine `subProg` -/

def setBitAct (cur next : Bool) : StackAct Sym :=
  match cur, next with
  | false, false => .keep
  | false, true  => .push symOne
  | true,  true  => .keep
  | true,  false => .pop

def borrowStack (b : Bool) : List Sym := if b then [symOne] else []

lemma setBitAct_apply (cur next : Bool) :
    (setBitAct cur next).apply (borrowStack cur) = borrowStack next := by
  cases cur <;> cases next <;> rfl

lemma borrowStack_head?_isSome (b : Bool) : (borrowStack b).head?.isSome = b := by
  cases b <;> rfl

def subBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | x :: xs, [], br =>
      xor x br :: subBits xs [] (!x && br)
  | [], y :: ys, br =>
      xor y br :: subBits [] ys (y || br)
  | x :: xs, y :: ys, br =>
      xor (xor x y) br :: subBits xs ys ((!x && y) || (!x && br) || (y && br))

def subBorrow : List Bool → List Bool → Bool → Bool
  | [], [], br => br
  | x :: xs, [], br => subBorrow xs [] (!x && br)
  | [], y :: ys, br => subBorrow [] ys (y || br)
  | x :: xs, y :: ys, br => subBorrow xs ys ((!x && y) || (!x && br) || (y && br))

lemma subBits_length : ∀ (u v : List Bool) (br : Bool),
    (subBits u v br).length = max u.length v.length
  | [], [], _ => by simp [subBits]
  | x :: xs, [], br => by simp [subBits, subBits_length xs []]
  | [], y :: ys, br => by simp [subBits, subBits_length [] ys]
  | x :: xs, y :: ys, br => by simp [subBits, subBits_length xs ys]

lemma ofBits_subBits : ∀ (u v : List Bool) (br : Bool),
    ofBits v + br.toNat ≤ ofBits u →
    ofBits (subBits u v br) + ofBits v + br.toNat = ofBits u
  | [], [], br, h => by
    cases br <;> simp [subBits, ofBits] at h ⊢
  | x :: xs, [], br, h => by
    simp only [ofBits, subBits] at h ⊢
    cases x <;> cases br <;> simp [Bool.toNat] at h ⊢
    · have ih := ofBits_subBits xs [] false (by simp [ofBits, Bool.toNat])
      simp [ofBits, Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs [] true (by simp [ofBits, Bool.toNat]; omega)
      simp [ofBits, Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs [] false (by simp [ofBits, Bool.toNat])
      simp [ofBits, Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs [] false (by simp [ofBits, Bool.toNat])
      simp [ofBits, Bool.toNat] at ih; omega
  | [], y :: ys, br, h => by
    simp only [ofBits, subBits] at h ⊢
    cases y <;> cases br <;> simp [Bool.toNat] at h ⊢
    · have ih := ofBits_subBits [] ys false (by simp [ofBits, Bool.toNat]; omega)
      simp [ofBits, Bool.toNat] at ih; omega
  | x :: xs, y :: ys, br, h => by
    simp only [ofBits, subBits] at h ⊢
    cases x <;> cases y <;> cases br <;> simp [Bool.toNat] at h ⊢
    · have ih := ofBits_subBits xs ys false (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys true (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys true (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys true (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys false (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys false (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys false (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega
    · have ih := ofBits_subBits xs ys true (by simp [Bool.toNat]; omega)
      simp [Bool.toNat] at ih; omega

def subAct (big small : K) (h : K → Option Sym) (k : K) : StackAct Sym :=
  let bx := decide (h big = some symOne)
  let by_ := decide (h small = some symOne)
  let br := (h .C).isSome
  let d := xor (xor bx by_) br
  let br' := (!bx && by_) || (!bx && br) || (by_ && br)
  if k = big then .pop
  else if k = small then .pop
  else if k = .T1 then .push (bitSym d)
  else if k = .T2 then match h small with | some s => .push s | none => .keep
  else if k = .C then setBitAct br br'
  else .keep

def subLoopProg (big small : K) : StackProg K Sym :=
  .loop (fun h => (h big).isSome || (h small).isSome) (.act (subAct big small))

def subProg (big small : K) : StackProg K Sym :=
  .seq (subLoopProg big small)
    (.seq (stripZerosProg .T1)
      (.seq (transferProg .T1 (fun k => decide (k = big)))
        (.seq (transferProg .T2 (fun k => decide (k = small)))
              (popProg .C))))

def subEndState (big small : K) (u v : List Bool) (br : Bool) (s : K → List Sym) : K → List Sym :=
  fun k =>
    if k = big then []
    else if k = small then []
    else if k = .T1 then (subBits u v br).reverse.map bitSym ++ s .T1
    else if k = .T2 then (v.map bitSym).reverse ++ s .T2
    else if k = .C then borrowStack (subBorrow u v br)
    else s k

lemma exec_subLoop (big small : K) (hbs : big ≠ small)
    (hb1 : big ≠ .T1) (hb2 : big ≠ .T2) (hbC : big ≠ .C)
    (hs1 : small ≠ .T1) (hs2 : small ≠ .T2) (hsC : small ≠ .C) :
    ∀ (u v : List Bool) (br : Bool) (s : K → List Sym),
      s big = u.map bitSym → s small = v.map bitSym → s .C = borrowStack br →
      (subLoopProg big small).Exec s (subEndState big small u v br s) (3 * max u.length v.length + 1)
  | [], [], br, s, hbig, hsmall, hC => by
    have h := StackProg.Exec.loopFalse (p := .act (subAct big small))
      (test := fun h => (h big).isSome || (h small).isSome) (s := s) (by simp [hbig, hsmall])
    have heq : subEndState big small [] [] br s = s := by
      funext k
      unfold subEndState
      by_cases h1 : k = big
      · subst k; simp [hbig]
      · by_cases h2 : k = small
        · subst k; simp [h1, hsmall]
        · by_cases h3 : k = .T1
          · subst k; simp [h1, h2, subBits]
          · by_cases h4 : k = .T2
            · subst k; simp [h1, h2, h3]
            · by_cases h5 : k = .C
              · subst k; simp [h1, h2, h3, h4, subBorrow, hC]
              · simp [h1, h2, h3, h4, h5]
    simpa [subLoopProg, heq] using h
  | x :: xs, [], br, s, hbig, hsmall, hC => by
    have hstep := StackProg.Exec.act (subAct big small) s
    set s1 := StackProg.applyAct (subAct big small) s
    have hs1big : s1 big = xs.map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbig, StackAct.apply]
    have hs1small : s1 small = [].map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbs.symm, hsmall, StackAct.apply]
    have hs1C : s1 .C = borrowStack (!x && br) := by
      simp only [s1, StackProg.applyAct, subAct, hbC.symm, hsC.symm, ↓reduceIte,
        show (K.C = K.T1) = false by decide, show (K.C = K.T2) = false by decide, hbig, hsmall, hC,
        List.map_cons, List.head?_cons, List.map_nil, List.head?_nil, borrowStack_head?_isSome]
      cases x <;> cases br <;> simp [setBitAct, borrowStack, StackAct.apply]
    have ih := exec_subLoop big small hbs hb1 hb2 hbC hs1 hs2 hsC xs [] (!x && br) s1
      hs1big hs1small hs1C
    have hloop := StackProg.Exec.loopTrue
      (test := fun (h : K → Option Sym) => (h big).isSome || (h small).isSome)
      (by simp [hbig]) hstep ih
    have heq : subEndState big small xs [] (!x && br) s1 = subEndState big small (x :: xs) [] br s := by
      funext k
      unfold subEndState
      by_cases h1 : k = big
      · subst k; simp
      · by_cases h2 : k = small
        · subst k; simp [h1]
        · by_cases h3 : k = .T1
          · subst k
            simp only [h1, h2, ↓reduceIte, subBits, List.reverse_cons, List.map_append,
              List.map_singleton, List.append_assoc, List.singleton_append]
            congr 1
            simp only [s1, StackProg.applyAct, subAct, hb1.symm, hs1.symm, ↓reduceIte, hbig, hsmall,
              hC, List.map_cons, List.head?_cons, List.map_nil, List.head?_nil,
              borrowStack_head?_isSome, StackAct.apply]
            cases x <;> cases br <;> simp
          · by_cases h4 : k = .T2
            · subst k
              simp [h1, h2, h3, s1, StackProg.applyAct, subAct, hsmall, StackAct.apply]
            · by_cases h5 : k = .C
              · subst k; simp [h1, h2, h3, h4, subBorrow]
              · simp [h1, h2, h3, h4, h5, s1, StackProg.applyAct, subAct, StackAct.apply]
    have ht : 1 + 1 + 1 + (3 * max xs.length 0 + 1) = 3 * max (x :: xs).length 0 + 1 := by
      simp; omega
    simp only [List.length_nil] at hloop ⊢
    rw [heq, ht] at hloop
    exact hloop
  | [], y :: ys, br, s, hbig, hsmall, hC => by
    have hstep := StackProg.Exec.act (subAct big small) s
    set s1 := StackProg.applyAct (subAct big small) s
    have hs1big : s1 big = [].map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbig, StackAct.apply]
    have hs1small : s1 small = ys.map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbs.symm, hsmall, StackAct.apply]
    have hs1C : s1 .C = borrowStack (y || br) := by
      simp only [s1, StackProg.applyAct, subAct, hbC.symm, hsC.symm, ↓reduceIte,
        show (K.C = K.T1) = false by decide, show (K.C = K.T2) = false by decide, hbig, hsmall, hC,
        List.map_cons, List.head?_cons, List.map_nil, List.head?_nil, borrowStack_head?_isSome]
      cases y <;> cases br <;> simp [setBitAct, borrowStack, StackAct.apply]
    have ih := exec_subLoop big small hbs hb1 hb2 hbC hs1 hs2 hsC [] ys (y || br) s1
      hs1big hs1small hs1C
    have hloop := StackProg.Exec.loopTrue
      (test := fun (h : K → Option Sym) => (h big).isSome || (h small).isSome)
      (by simp [hsmall]) hstep ih
    have heq : subEndState big small [] ys (y || br) s1 = subEndState big small [] (y :: ys) br s := by
      funext k
      unfold subEndState
      by_cases h1 : k = big
      · subst k; simp
      · by_cases h2 : k = small
        · subst k; simp [h1]
        · by_cases h3 : k = .T1
          · subst k
            simp only [h1, h2, ↓reduceIte, subBits, List.reverse_cons, List.map_append,
              List.map_singleton, List.append_assoc, List.singleton_append]
            congr 1
            simp only [s1, StackProg.applyAct, subAct, hb1.symm, hs1.symm, ↓reduceIte, hbig, hsmall,
              hC, List.map_cons, List.head?_cons, List.map_nil, List.head?_nil,
              borrowStack_head?_isSome, StackAct.apply]
            cases y <;> cases br <;> simp
          · by_cases h4 : k = .T2
            · subst k
              simp [h1, h2, h3, s1, StackProg.applyAct, subAct, hsmall, StackAct.apply]
            · by_cases h5 : k = .C
              · subst k; simp [h1, h2, h3, h4, subBorrow]
              · simp [h1, h2, h3, h4, h5, s1, StackProg.applyAct, subAct, StackAct.apply]
    have ht : 1 + 1 + 1 + (3 * max 0 ys.length + 1) = 3 * max 0 (y :: ys).length + 1 := by
      simp; omega
    simp only [List.length_nil] at hloop ⊢
    rw [heq, ht] at hloop
    exact hloop
  | x :: xs, y :: ys, br, s, hbig, hsmall, hC => by
    have hstep := StackProg.Exec.act (subAct big small) s
    set s1 := StackProg.applyAct (subAct big small) s
    have hs1big : s1 big = xs.map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbig, StackAct.apply]
    have hs1small : s1 small = ys.map bitSym := by
      simp [s1, StackProg.applyAct, subAct, hbs.symm, hsmall, StackAct.apply]
    have hs1C : s1 .C = borrowStack ((!x && y) || (!x && br) || (y && br)) := by
      simp only [s1, StackProg.applyAct, subAct, hbC.symm, hsC.symm, ↓reduceIte,
        show (K.C = K.T1) = false by decide, show (K.C = K.T2) = false by decide, hbig, hsmall, hC,
        List.map_cons, List.head?_cons, borrowStack_head?_isSome]
      cases x <;> cases y <;> cases br <;> simp [setBitAct, borrowStack, StackAct.apply]
    have ih := exec_subLoop big small hbs hb1 hb2 hbC hs1 hs2 hsC xs ys
      ((!x && y) || (!x && br) || (y && br)) s1 hs1big hs1small hs1C
    have hloop := StackProg.Exec.loopTrue
      (test := fun (h : K → Option Sym) => (h big).isSome || (h small).isSome)
      (by simp [hbig]) hstep ih
    have heq : subEndState big small xs ys ((!x && y) || (!x && br) || (y && br)) s1 =
        subEndState big small (x :: xs) (y :: ys) br s := by
      funext k
      unfold subEndState
      by_cases h1 : k = big
      · subst k; simp
      · by_cases h2 : k = small
        · subst k; simp [h1]
        · by_cases h3 : k = .T1
          · subst k
            simp only [h1, h2, ↓reduceIte, subBits, List.reverse_cons, List.map_append,
              List.map_singleton, List.append_assoc, List.singleton_append]
            congr 1
            simp only [s1, StackProg.applyAct, subAct, hb1.symm, hs1.symm, ↓reduceIte, hbig, hsmall,
              hC, List.map_cons, List.head?_cons, borrowStack_head?_isSome, StackAct.apply]
            cases x <;> cases y <;> cases br <;> simp
          · by_cases h4 : k = .T2
            · subst k
              simp [h1, h2, h3, s1, StackProg.applyAct, subAct, hsmall, StackAct.apply]
            · by_cases h5 : k = .C
              · subst k; simp [h1, h2, h3, h4, subBorrow]
              · simp [h1, h2, h3, h4, h5, s1, StackProg.applyAct, subAct, StackAct.apply]
    have ht : 1 + 1 + 1 + (3 * max xs.length ys.length + 1) =
        3 * max (x :: xs).length (y :: ys).length + 1 := by
      simp; omega
    rw [heq, ht] at hloop
    exact hloop

lemma exec_sub (big small : K) (hbs : big ≠ small)
    (hb1 : big ≠ .T1) (hb2 : big ≠ .T2) (hbC : big ≠ .C)
    (hs1 : small ≠ .T1) (hs2 : small ≠ .T2) (hsC : small ≠ .C)
    (s : K → List Sym) (x y : ℕ) (hxy : y ≤ x)
    (hbig : s big = natStack x) (hsmall : s small = natStack y)
    (hT1 : s .T1 = []) (hT2 : s .T2 = []) (hC : s .C = []) :
    ∃ t ≤ 12 * ((natStack x).length + (natStack y).length) + 10,
      (subProg big small).Exec s (Function.update s big (natStack (x - y))) t := by
  have h1 := exec_subLoop big small hbs hb1 hb2 hbC hs1 hs2 hsC
    (Nat.bits x) (Nat.bits y) false s hbig hsmall hC
  set s1 := subEndState big small (Nat.bits x) (Nat.bits y) false s
  have hs1T1 : s1 .T1 = (subBits (Nat.bits x) (Nat.bits y) false).reverse.map bitSym := by
    simp [s1, subEndState, hb1.symm, hs1.symm, hT1]
  obtain ⟨t2, ht2, h2⟩ := exec_stripZeros .T1
    ((subBits (Nat.bits x) (Nat.bits y) false).reverse.map bitSym) s1 hs1T1
  set s2 := Function.update s1 .T1
    (((subBits (Nat.bits x) (Nat.bits y) false).reverse.map bitSym).dropWhile (fun z => decide (z = symZero)))
  have h3 := exec_transfer_single .T1 big hb1.symm s2
  set s3 := Function.update (Function.update s2 .T1 []) big ((s2 .T1).reverse ++ s2 big)
  have h4 := exec_transfer_single .T2 small hs2.symm s3
  set s4 := Function.update (Function.update s3 .T2 []) small ((s3 .T2).reverse ++ s3 small)
  have h5 := (CookPvsNP.stack_basic_macros .C s4).2.1
  set s5 := Function.update s4 .C (s4 .C).tail
  have hex := StackProg.Exec.seq h1 (StackProg.Exec.seq h2
    (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 h5)))
  have hsubVal : ofBits (subBits (Nat.bits x) (Nat.bits y) false) = x - y := by
    have hle : ofBits (Nat.bits y) + false.toNat ≤ ofBits (Nat.bits x) := by
      simp [ofBits_bits, hxy]
    have := ofBits_subBits (Nat.bits x) (Nat.bits y) false hle
    simp only [ofBits_bits, Bool.toNat_false, Nat.add_zero] at this
    omega
  have hs2T1_rev : (s2 .T1).reverse = natStack (x - y) := by
    simp only [s2, Function.update_self, dropWhile_map_bitSym, ← List.map_reverse]
    rw [dropWhile_rev_eq_bits, List.reverse_reverse, hsubVal]
    rfl
  have hs4C_tail : (s4 .C).tail = [] := by
    have hCeq : s4 .C = borrowStack (subBorrow (Nat.bits x) (Nat.bits y) false) := by
      simp [s4, s3, s2, s1, subEndState, hbC.symm, hsC.symm]
    rw [hCeq]
    cases subBorrow (Nat.bits x) (Nat.bits y) false <;> rfl
  have hs5 : s5 = Function.update s big (natStack (x - y)) := by
    funext k
    by_cases hk1 : k = .C
    · subst k
      simp [s5, hs4C_tail, hbC.symm, hC]
    · by_cases hk2 : k = small
      · subst k
        simp [s5, s4, s3, s2, s1, subEndState, hk1, hbs.symm, hs1, hs2.symm, hb2.symm,
          hT2, hsmall, natStack]
      · by_cases hk3 : k = .T2
        · subst k
          simp [s5, s4, hk1, hk2, hb2.symm, hT2]
        · by_cases hk4 : k = big
          · subst k
            simp only [s5, s4, s3, Function.update_of_ne hk1, Function.update_of_ne hk2,
              Function.update_of_ne hk3, Function.update_self]
            rw [hs2T1_rev]
            simp [s2, s1, subEndState, hb1]
          · by_cases hk5 : k = .T1
            · subst k
              simp [s5, s4, s3, hk1, hk2, hk3, hk4, hT1]
            · simp [s5, s4, s3, s2, s1, subEndState, hk1, hk2, hk3, hk4, hk5]
  have hlen_sub : ((subBits (Nat.bits x) (Nat.bits y) false).reverse.map bitSym).length =
      max (Nat.bits x).length (Nat.bits y).length := by
    simp [subBits_length]
  have hlen_s2T1 : (s2 .T1).length ≤ max (Nat.bits x).length (Nat.bits y).length := by
    simp only [s2, Function.update_self]
    have := List.length_dropWhile_le (p := fun z => decide (z = symZero))
      ((subBits (Nat.bits x) (Nat.bits y) false).reverse.map bitSym)
    omega
  have hlen_s3T2 : (s3 .T2).length = (Nat.bits y).length := by
    simp [s3, s2, s1, subEndState, hb2.symm, hs2.symm, hT2]
  refine ⟨_, ?_, by rwa [hs5] at hex⟩
  rw [hlen_sub] at ht2
  rw [hlen_s3T2]
  simp only [natStack, List.length_map]
  omega

/-! ## Binary GCD (Stein's algorithm) and `gcdCheckProg` -/

def steinGuard (h : K → Option Sym) : Bool :=
  (h .A).isSome && (h .B).isSome && !(decide (h .A = some symZero) && decide (h .B = some symZero))

def steinBodyProg : StackProg K Sym :=
  .branch (fun h => decide (h .A = some symZero))
    (popProg .A)
    (.branch (fun h => decide (h .B = some symZero))
      (popProg .B)
      (.seq cmpABProg
        (.branch (fun h => (h .C).isNone)
          (clearProg .B)
          (.branch (fun h => decide (h .C = some symOne))
            (.seq (clearProg .C) (.seq (subProg .A .B) (popProg .A)))
            (.seq (clearProg .C) (.seq (subProg .B .A) (popProg .B)))))))

def steinLoopProg : StackProg K Sym :=
  .loop steinGuard steinBodyProg

def checkOneBranchProg : StackProg K Sym :=
  .branch (fun h => (h .A).isNone && decide (h .B = some symOne))
    (.seq (popProg .B) (.branch (fun h => (h .B).isNone) noop (pushProg .fail symOne)))
    (.branch (fun h => (h .B).isNone && decide (h .A = some symOne))
      (.seq (popProg .A) (.branch (fun h => (h .A).isNone) noop (pushProg .fail symOne)))
      (pushProg .fail symOne))

def checkOneProg : StackProg K Sym :=
  .seq checkOneBranchProg (.seq (clearProg .A) (clearProg .B))

def gcdCheckProg : StackProg K Sym :=
  .seq steinLoopProg checkOneProg

lemma exec_steinBody (s : K → List Sym) (a b : ℕ)
    (hA : s .A = natStack a) (hB : s .B = natStack b)
    (hT1 : s .T1 = []) (hT2 : s .T2 = []) (hC : s .C = [])
    (hg : steinGuard (fun k => (s k).head?) = true) :
    ∃ (a' b' : ℕ) (t : ℕ),
      t ≤ 24 * ((natStack a).length + (natStack b).length) + 30 ∧
      steinBodyProg.Exec s
        (Function.update (Function.update s .A (natStack a')) .B (natStack b')) t ∧
      Nat.gcd a' b' = Nat.gcd a b ∧
      (natStack a').length + (natStack b').length < (natStack a).length + (natStack b).length := by
  have hAne : a ≠ 0 := by
    intro ha0
    have h1 : (s .A).head?.isSome = true := by
      unfold steinGuard at hg
      simp only [Bool.and_eq_true] at hg
      exact hg.1.1
    simp [hA, ha0, natStack_zero] at h1
  have hBne : b ≠ 0 := by
    intro hb0
    have h1 : (s .B).head?.isSome = true := by
      unfold steinGuard at hg
      simp only [Bool.and_eq_true] at hg
      exact hg.1.2
    simp [hB, hb0, natStack_zero] at h1
  have hnotBothEven : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
    rintro ⟨ha, hb⟩
    unfold steinGuard at hg
    have hAz := natStack_head?_zero.mpr ⟨hAne, ha⟩
    have hBz := natStack_head?_zero.mpr ⟨hBne, hb⟩
    simp [hA, hB, hAz, hBz] at hg
  by_cases haEven : a % 2 = 0
  · have hbOdd : b % 2 = 1 := by omega
    have hAz := natStack_head?_zero.mpr ⟨hAne, haEven⟩
    have hpop := (CookPvsNP.stack_basic_macros .A s).2.1
    have htail : (s .A).tail = natStack (a / 2) := by
      rw [hA, natStack_even hAne haEven]; rfl
    rw [htail] at hpop
    have hex : steinBodyProg.Exec s (Function.update s .A (natStack (a / 2))) (1 + 1) :=
      StackProg.Exec.branchTrue (by simp [hA, hAz]) hpop
    have hu : Function.update (Function.update s .A (natStack (a / 2))) .B (natStack b) =
        Function.update s .A (natStack (a / 2)) := by
      funext k; by_cases hk : k = .B
      · subst k; simp [hB]
      · simp [hk]
    refine ⟨a / 2, b, 1 + 1, by omega, by rwa [hu], gcd_div2_left_of_odd haEven hbOdd, ?_⟩
    rw [natStack_even hAne haEven]; simp
  · have haOdd : a % 2 = 1 := by omega
    have hAone := natStack_head?_one.mpr haOdd
    have hAnotZ : decide ((s .A).head? = some symZero) = false := by
      rw [hA, hAone]; decide
    by_cases hbEven : b % 2 = 0
    · have hBz := natStack_head?_zero.mpr ⟨hBne, hbEven⟩
      have hpop := (CookPvsNP.stack_basic_macros .B s).2.1
      have htail : (s .B).tail = natStack (b / 2) := by
        rw [hB, natStack_even hBne hbEven]; rfl
      rw [htail] at hpop
      have hex : steinBodyProg.Exec s (Function.update s .B (natStack (b / 2))) (1 + (1 + 1)) :=
        StackProg.Exec.branchFalse hAnotZ
          (StackProg.Exec.branchTrue (by simp [hB, hBz]) hpop)
      have hu : Function.update (Function.update s .A (natStack a)) .B (natStack (b / 2)) =
          Function.update s .B (natStack (b / 2)) := by
        funext k; by_cases hk : k = .B
        · subst k; simp
        · by_cases hk2 : k = .A
          · subst k; simp [hA]
          · simp [hk, hk2]
      refine ⟨a, b / 2, 1 + (1 + 1), by omega, by rwa [hu], ?_, ?_⟩
      · rw [Nat.gcd_comm, gcd_div2_left_of_odd hbEven haOdd, Nat.gcd_comm]
      · rw [natStack_even hBne hbEven]; simp
    · have hbOdd : b % 2 = 1 := by omega
      have hBone := natStack_head?_one.mpr hbOdd
      have hBnotZ : decide ((s .B).head? = some symZero) = false := by
        rw [hB, hBone]; decide
      obtain ⟨cL, tcmp, htcmp, hcmp, hcLen, hcHead⟩ := exec_cmpAB s a b hA hB hT1 hT2 hC
      set s1 := Function.update s .C cL
      by_cases hab : a = b
      · subst hab
        have hcNone : cL.head? = none := by simpa using hcHead
        have hcNil : cL = [] := List.head?_eq_none_iff.mp hcNone
        have hs1eq : s1 = s := by
          funext k; by_cases hk : k = .C
          · subst k; simp [s1, hcNil, hC]
          · simp [s1, hk]
        have hclr := (CookPvsNP.stack_basic_macros .B s1).2.2
        have hex : steinBodyProg.Exec s (Function.update s1 .B [])
            (1 + (1 + (tcmp + 1 + (1 + (3 * (s1 .B).length + 1))))) :=
          StackProg.Exec.branchFalse hAnotZ
            (StackProg.Exec.branchFalse hBnotZ
              (StackProg.Exec.seq hcmp
                (StackProg.Exec.branchTrue (by simp [s1, hcNone]) hclr)))
        have hu : Function.update s1 .B [] =
            Function.update (Function.update s .A (natStack a)) .B (natStack 0) := by
          rw [hs1eq, natStack_zero]
          funext k; by_cases hk : k = .B
          · subst k; simp
          · by_cases hk2 : k = .A
            · subst k; simp [hA]
            · simp [hk, hk2]
        have hs1Blen : (s1 .B).length = (natStack a).length := by simp [s1, hB]
        refine ⟨a, 0, _, ?_, by rwa [hu] at hex, by simp, ?_⟩
        · rw [hs1Blen]; omega
        · rw [natStack_zero, natStack_odd haOdd]; simp
      · by_cases hgt : b < a
        · have hnotlt : ¬ a < b := by omega
          have hcOne : cL.head? = some symOne := by simpa [hnotlt, hgt] using hcHead
          have hclrC := (CookPvsNP.stack_basic_macros .C s1).2.2
          have hs2eq : Function.update s1 .C [] = s := by
            funext k; by_cases hk : k = .C
            · subst k; simp [hC]
            · simp [s1, hk]
          rw [hs2eq] at hclrC
          obtain ⟨tsub, htsub, hsub⟩ := exec_sub .A .B (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) s a b (by omega) hA hB hT1 hT2 hC
          set s3 := Function.update s .A (natStack (a - b))
          have hpop := (CookPvsNP.stack_basic_macros .A s3).2.1
          have hsubNe : a - b ≠ 0 := by omega
          have hsubEven : (a - b) % 2 = 0 := by omega
          have htail : (s3 .A).tail = natStack ((a - b) / 2) := by
            simp only [s3, Function.update_self]
            rw [natStack_even hsubNe hsubEven]; rfl
          rw [htail] at hpop
          have hex : steinBodyProg.Exec s (Function.update s3 .A (natStack ((a - b) / 2)))
              (1 + (1 + (tcmp + 1 + (1 + (1 + ((3 * (s1 .C).length + 1) + 1 + (tsub + 1 + 1))))))) :=
            StackProg.Exec.branchFalse hAnotZ
              (StackProg.Exec.branchFalse hBnotZ
                (StackProg.Exec.seq hcmp
                  (StackProg.Exec.branchFalse (by simp [s1, hcOne])
                    (StackProg.Exec.branchTrue (by simp [s1, hcOne])
                      (StackProg.Exec.seq hclrC (StackProg.Exec.seq hsub hpop))))))
          have hu : Function.update s3 .A (natStack ((a - b) / 2)) =
              Function.update (Function.update s .A (natStack ((a - b) / 2))) .B (natStack b) := by
            funext k; by_cases hk : k = .B
            · subst k; simp [s3, hB]
            · by_cases hk2 : k = .A
              · subst k; simp [s3]
              · simp [s3, hk, hk2]
          have hs1Clen : (s1 .C).length = cL.length := by simp [s1]
          refine ⟨(a - b) / 2, b, _, ?_, by rwa [hu] at hex,
            gcd_odd_sub_div2_left haOdd hbOdd hgt, ?_⟩
          · rw [hs1Clen]; omega
          · have := natStack_length_odd_sub_div2 haOdd hbOdd hgt; omega
        · have hlt : a < b := by omega
          have hcZero : cL.head? = some symZero := by simpa [hlt] using hcHead
          have hclrC := (CookPvsNP.stack_basic_macros .C s1).2.2
          have hs2eq : Function.update s1 .C [] = s := by
            funext k; by_cases hk : k = .C
            · subst k; simp [hC]
            · simp [s1, hk]
          rw [hs2eq] at hclrC
          obtain ⟨tsub, htsub, hsub⟩ := exec_sub .B .A (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) s b a (by omega) hB hA hT1 hT2 hC
          set s3 := Function.update s .B (natStack (b - a))
          have hpop := (CookPvsNP.stack_basic_macros .B s3).2.1
          have hsubNe : b - a ≠ 0 := by omega
          have hsubEven : (b - a) % 2 = 0 := by omega
          have htail : (s3 .B).tail = natStack ((b - a) / 2) := by
            simp only [s3, Function.update_self]
            rw [natStack_even hsubNe hsubEven]; rfl
          rw [htail] at hpop
          have hex : steinBodyProg.Exec s (Function.update s3 .B (natStack ((b - a) / 2)))
              (1 + (1 + (tcmp + 1 + (1 + (1 + ((3 * (s1 .C).length + 1) + 1 + (tsub + 1 + 1))))))) :=
            StackProg.Exec.branchFalse hAnotZ
              (StackProg.Exec.branchFalse hBnotZ
                (StackProg.Exec.seq hcmp
                  (StackProg.Exec.branchFalse (by simp [s1, hcZero])
                    (StackProg.Exec.branchFalse (by simp [s1, hcZero])
                      (StackProg.Exec.seq hclrC (StackProg.Exec.seq hsub hpop))))))
          have hu : Function.update s3 .B (natStack ((b - a) / 2)) =
              Function.update (Function.update s .A (natStack a)) .B (natStack ((b - a) / 2)) := by
            funext k; by_cases hk : k = .B
            · subst k; simp [s3]
            · by_cases hk2 : k = .A
              · subst k; simp [s3, hA]
              · simp [s3, hk, hk2]
          have hs1Clen : (s1 .C).length = cL.length := by simp [s1]
          refine ⟨a, (b - a) / 2, _, ?_, by rwa [hu] at hex, ?_, ?_⟩
          · rw [hs1Clen]; omega
          · rw [Nat.gcd_comm, gcd_odd_sub_div2_left hbOdd haOdd hlt, Nat.gcd_comm]
          · have := natStack_length_odd_sub_div2 hbOdd haOdd hlt; omega

lemma exec_steinLoop_aux : ∀ (L : ℕ) (s : K → List Sym) (a b : ℕ),
    (natStack a).length + (natStack b).length ≤ L →
    s .A = natStack a → s .B = natStack b →
    s .T1 = [] → s .T2 = [] → s .C = [] →
    ∃ (a' b' : ℕ) (t : ℕ),
      t ≤ L * (24 * L + 32) + 1 ∧
      steinLoopProg.Exec s
        (Function.update (Function.update s .A (natStack a')) .B (natStack b')) t ∧
      Nat.gcd a' b' = Nat.gcd a b ∧
      (natStack a').length + (natStack b').length ≤ L ∧
      (a' = 0 ∨ b' = 0 ∨ (a' % 2 = 0 ∧ b' % 2 = 0)) := by
  intro L
  induction L with
  | zero =>
    intro s a b hL hA hB hT1 hT2 hC
    have ha0 : a = 0 := natStack_eq_nil_iff.mp (List.eq_nil_of_length_eq_zero (by omega))
    have hb0 : b = 0 := natStack_eq_nil_iff.mp (List.eq_nil_of_length_eq_zero (by omega))
    have hstop : steinGuard (fun k => (s k).head?) = false := by
      simp [steinGuard, hA, ha0, natStack_zero]
    have hloop := StackProg.Exec.loopFalse (p := steinBodyProg) hstop
    have hu : Function.update (Function.update s .A (natStack a)) .B (natStack b) = s := by
      funext k; by_cases hk : k = .B
      · subst k; simp [hB]
      · by_cases hk2 : k = .A
        · subst k; simp [hA]
        · simp [hk, hk2]
    exact ⟨a, b, 1, by omega, by rwa [hu], rfl, hL, Or.inl ha0⟩
  | succ L ih =>
    intro s a b hL hA hB hT1 hT2 hC
    by_cases hg : steinGuard (fun k => (s k).head?) = true
    · obtain ⟨a1, b1, tbody, htbody, hbody, hgcd1, hlt⟩ :=
        exec_steinBody s a b hA hB hT1 hT2 hC hg
      set s1 := Function.update (Function.update s .A (natStack a1)) .B (natStack b1)
      have hL1 : (natStack a1).length + (natStack b1).length ≤ L := by omega
      obtain ⟨a', b', trec, htrec, hrec, hgcd2, hL', hterm⟩ :=
        ih s1 a1 b1 hL1 (by simp [s1]) (by simp [s1]) (by simp [s1, hT1]) (by simp [s1, hT2])
          (by simp [s1, hC])
      have hloop := StackProg.Exec.loopTrue hg hbody hrec
      have hu : Function.update (Function.update s1 .A (natStack a')) .B (natStack b') =
          Function.update (Function.update s .A (natStack a')) .B (natStack b') := by
        funext k; by_cases hk : k = .B
        · subst k; simp [s1]
        · by_cases hk2 : k = .A
          · subst k; simp [s1]
          · simp [s1, hk, hk2]
      refine ⟨a', b', 1 + tbody + 1 + trec, ?_, by rwa [hu] at hloop,
        hgcd2.trans hgcd1, by omega, hterm⟩
      nlinarith
    · have hstop : steinGuard (fun k => (s k).head?) = false := by
        cases h : steinGuard (fun k => (s k).head?)
        · rfl
        · exact absurd h hg
      have hloop := StackProg.Exec.loopFalse (p := steinBodyProg) hstop
      have hu : Function.update (Function.update s .A (natStack a)) .B (natStack b) = s := by
        funext k; by_cases hk : k = .B
        · subst k; simp [hB]
        · by_cases hk2 : k = .A
          · subst k; simp [hA]
          · simp [hk, hk2]
      have hterm : a = 0 ∨ b = 0 ∨ (a % 2 = 0 ∧ b % 2 = 0) := by
        by_contra hnot
        push Not at hnot
        obtain ⟨ha0, hb0, hne⟩ := hnot
        have hAne : (natStack a).head?.isSome = true := by
          cases hna : natStack a with
          | nil => exact absurd (natStack_eq_nil_iff.mp hna) ha0
          | cons _ _ => rfl
        have hBne : (natStack b).head?.isSome = true := by
          cases hnb : natStack b with
          | nil => exact absurd (natStack_eq_nil_iff.mp hnb) hb0
          | cons _ _ => rfl
        have hnotZ : (decide ((natStack a).head? = some symZero) &&
            decide ((natStack b).head? = some symZero)) = false := by
          by_cases hae : a % 2 = 0
          · have hbo : b % 2 = 1 := by have := hne hae; omega
            rw [natStack_head?_one.mpr hbo]; simp
          · have hao : a % 2 = 1 := by omega
            rw [natStack_head?_one.mpr hao]; simp
        unfold steinGuard at hstop
        simp [hA, hB, hAne, hBne, hnotZ] at hstop
      exact ⟨a, b, 1, by omega, by rwa [hu], rfl, hL, hterm⟩

lemma exec_checkOne (s : K → List Sym) (a b : ℕ)
    (hA : s .A = natStack a) (hB : s .B = natStack b)
    (hterm : a = 0 ∨ b = 0 ∨ (a % 2 = 0 ∧ b % 2 = 0)) :
    ∃ t ≤ 3 * ((natStack a).length + (natStack b).length) + 12,
      checkOneProg.Exec s
        (Function.update (Function.update
          (Function.update s .fail (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail))
          .A []) .B []) t := by
  have finish : ∀ (s1 : K → List Sym),
      (s1 .A).length ≤ (natStack a).length → (s1 .B).length ≤ (natStack b).length →
      (∀ k, k ≠ .A → k ≠ .B → k ≠ .fail → s1 k = s k) →
      s1 .fail = (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail) →
      ∃ t ≤ 3 * ((natStack a).length + (natStack b).length) + 3,
        (StackProg.seq (clearProg .A) (clearProg .B)).Exec s1
          (Function.update (Function.update
            (Function.update s .fail (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail))
            .A []) .B []) t := by
    intro s1 hAl hBl hfr hf
    have hclA := (CookPvsNP.stack_basic_macros .A s1).2.2
    have hclB := (CookPvsNP.stack_basic_macros .B (Function.update s1 .A [])).2.2
    have hex := StackProg.Exec.seq hclA hclB
    have hu : Function.update (Function.update s1 .A []) .B [] =
        Function.update (Function.update
          (Function.update s .fail (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail))
          .A []) .B [] := by
      funext k
      by_cases hkB : k = .B
      · subst k; simp
      · by_cases hkA : k = .A
        · subst k; simp [hkB]
        · by_cases hkF : k = .fail
          · subst k; simp [hkA, hkB, hf]
          · simp [hkA, hkB, hkF, hfr k hkA hkB hkF]
    refine ⟨_, ?_, by rwa [hu] at hex⟩
    simp only [Function.update_of_ne (show K.B ≠ K.A by decide)]
    omega
  by_cases hc1 : a = 0 ∧ b % 2 = 1
  · obtain ⟨rfl, hbo⟩ := hc1
    have hA' : s .A = [] := by rw [hA, natStack_zero]
    have hB' : s .B = symOne :: natStack (b / 2) := by rw [hB, natStack_odd hbo]
    have hcond1 : ((s .A).head?.isNone && decide ((s .B).head? = some symOne)) = true := by
      simp [hA', hB']
    have hpopB := (CookPvsNP.stack_basic_macros .B s).2.1
    rw [hB'] at hpopB
    simp only [List.tail_cons] at hpopB
    set s1 := Function.update s .B (natStack (b / 2))
    by_cases hb1 : b = 1
    · subst hb1
      have hB1 : s1 .B = [] := by simp [s1, natStack_zero]
      have hbr : checkOneBranchProg.Exec s s1 (1 + (1 + 1 + (1 + 1))) :=
        StackProg.Exec.branchTrue hcond1
          (StackProg.Exec.seq hpopB
            (StackProg.Exec.branchTrue (by simp [hB1]) (exec_noop s1)))
      obtain ⟨tcl, htcl, hcl⟩ := finish s1 (by simp [s1, hA])
        (by simp [s1, natStack_one, natStack_zero])
        (fun k _ hkB _ => by simp [s1, hkB])
        (by simp [s1])
      exact ⟨_, by omega, StackProg.Exec.seq hbr hcl⟩
    · have hbdiv : b / 2 ≠ 0 := by omega
      have hB1ne : (s1 .B).head?.isNone = false := by
        simp only [s1, Function.update_self]
        cases hn : natStack (b / 2) with
        | nil => exact absurd (natStack_eq_nil_iff.mp hn) hbdiv
        | cons _ _ => rfl
      have hpush := (CookPvsNP.stack_basic_macros .fail s1).1 symOne
      have hbr : checkOneBranchProg.Exec s (Function.update s1 .fail (symOne :: s1 .fail))
          (1 + (1 + 1 + (1 + 1))) :=
        StackProg.Exec.branchTrue hcond1
          (StackProg.Exec.seq hpopB
            (StackProg.Exec.branchFalse hB1ne hpush))
      obtain ⟨tcl, htcl, hcl⟩ := finish (Function.update s1 .fail (symOne :: s1 .fail))
        (by simp [s1, hA])
        (by simp [s1]; rw [natStack_odd hbo]; simp)
        (fun k _ hkB hkF => by simp [s1, hkB, hkF])
        (by simp [s1, hb1])
      exact ⟨_, by omega, StackProg.Exec.seq hbr hcl⟩
  · have hcond1 : ((s .A).head?.isNone && decide ((s .B).head? = some symOne)) = false := by
      cases h1 : (s .A).head?.isNone
      · simp
      · cases h2 : decide ((s .B).head? = some symOne)
        · simp
        · exfalso
          have ha0 : a = 0 := natStack_eq_nil_iff.mp
            (List.head?_eq_none_iff.mp (Option.isNone_iff_eq_none.mp (by rwa [hA] at h1)))
          have hbo : b % 2 = 1 := natStack_head?_one.mp (of_decide_eq_true (by rwa [hB] at h2))
          exact hc1 ⟨ha0, hbo⟩
    by_cases hc2 : b = 0 ∧ a % 2 = 1
    · obtain ⟨rfl, hao⟩ := hc2
      have hB' : s .B = [] := by rw [hB, natStack_zero]
      have hA' : s .A = symOne :: natStack (a / 2) := by rw [hA, natStack_odd hao]
      have hcond2 : ((s .B).head?.isNone && decide ((s .A).head? = some symOne)) = true := by
        simp [hA', hB']
      have hpopA := (CookPvsNP.stack_basic_macros .A s).2.1
      rw [hA'] at hpopA
      simp only [List.tail_cons] at hpopA
      set s1 := Function.update s .A (natStack (a / 2))
      by_cases ha1 : a = 1
      · subst ha1
        have hA1 : s1 .A = [] := by simp [s1, natStack_zero]
        have hbr : checkOneBranchProg.Exec s s1 (1 + (1 + (1 + 1 + (1 + 1)))) :=
          StackProg.Exec.branchFalse hcond1
            (StackProg.Exec.branchTrue hcond2
              (StackProg.Exec.seq hpopA
                (StackProg.Exec.branchTrue (by simp [hA1]) (exec_noop s1))))
        obtain ⟨tcl, htcl, hcl⟩ := finish s1
          (by simp [s1, natStack_one, natStack_zero])
          (by simp [s1, hB])
          (fun k hkA _ _ => by simp [s1, hkA])
          (by simp [s1])
        exact ⟨_, by omega, StackProg.Exec.seq hbr hcl⟩
      · have hadiv : a / 2 ≠ 0 := by omega
        have hA1ne : (s1 .A).head?.isNone = false := by
          simp only [s1, Function.update_self]
          cases hn : natStack (a / 2) with
          | nil => exact absurd (natStack_eq_nil_iff.mp hn) hadiv
          | cons _ _ => rfl
        have hpush := (CookPvsNP.stack_basic_macros .fail s1).1 symOne
        have hbr : checkOneBranchProg.Exec s (Function.update s1 .fail (symOne :: s1 .fail))
            (1 + (1 + (1 + 1 + (1 + 1)))) :=
          StackProg.Exec.branchFalse hcond1
            (StackProg.Exec.branchTrue hcond2
              (StackProg.Exec.seq hpopA
                (StackProg.Exec.branchFalse hA1ne hpush)))
        obtain ⟨tcl, htcl, hcl⟩ := finish (Function.update s1 .fail (symOne :: s1 .fail))
          (by simp [s1]; rw [natStack_odd hao]; simp)
          (by simp [s1, hB])
          (fun k hkA _ hkF => by simp [s1, hkA, hkF])
          (by simp [s1, ha1])
        exact ⟨_, by omega, StackProg.Exec.seq hbr hcl⟩
    · have hcond2 : ((s .B).head?.isNone && decide ((s .A).head? = some symOne)) = false := by
        cases h1 : (s .B).head?.isNone
        · simp
        · cases h2 : decide ((s .A).head? = some symOne)
          · simp
          · exfalso
            have hb0 : b = 0 := natStack_eq_nil_iff.mp
              (List.head?_eq_none_iff.mp (Option.isNone_iff_eq_none.mp (by rwa [hB] at h1)))
            have hao : a % 2 = 1 := natStack_head?_one.mp (of_decide_eq_true (by rwa [hA] at h2))
            exact hc2 ⟨hb0, hao⟩
      have hgcdNe : Nat.gcd a b ≠ 1 := by
        rcases hterm with rfl | rfl | ⟨hae, hbe⟩
        · intro h; simp at h; exact hc1 ⟨rfl, by omega⟩
        · intro h; simp at h; exact hc2 ⟨rfl, by omega⟩
        · exact gcd_ne_one_of_both_even hae hbe
      have hpush := (CookPvsNP.stack_basic_macros .fail s).1 symOne
      have hbr : checkOneBranchProg.Exec s (Function.update s .fail (symOne :: s .fail))
          (1 + (1 + 1)) :=
        StackProg.Exec.branchFalse hcond1
          (StackProg.Exec.branchFalse hcond2 hpush)
      obtain ⟨tcl, htcl, hcl⟩ := finish (Function.update s .fail (symOne :: s .fail))
        (by simp [hA]) (by simp [hB])
        (fun k _ _ hkF => by simp [hkF])
        (by simp [hgcdNe])
      exact ⟨_, by omega, StackProg.Exec.seq hbr hcl⟩

lemma exec_gcdCheck (s : K → List Sym) (a b : ℕ)
    (hA : s .A = natStack a) (hB : s .B = natStack b)
    (hT1 : s .T1 = []) (hT2 : s .T2 = []) (hC : s .C = []) :
    let L := (natStack a).length + (natStack b).length
    ∃ t ≤ 24 * L * L + 35 * L + 15,
      gcdCheckProg.Exec s
        (Function.update (Function.update
          (Function.update s .fail (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail))
          .A []) .B []) t := by
  intro L
  obtain ⟨a', b', t1, ht1, h1, hgcd, hL', hterm⟩ :=
    exec_steinLoop_aux L s a b (le_refl L) hA hB hT1 hT2 hC
  set s1 := Function.update (Function.update s .A (natStack a')) .B (natStack b')
  obtain ⟨t2, ht2, h2⟩ := exec_checkOne s1 a' b' (by simp [s1]) (by simp [s1]) hterm
  have hex := StackProg.Exec.seq h1 h2
  have hu : Function.update (Function.update
      (Function.update s1 .fail (if Nat.gcd a' b' = 1 then s1 .fail else symOne :: s1 .fail))
      .A []) .B [] =
    Function.update (Function.update
      (Function.update s .fail (if Nat.gcd a b = 1 then s .fail else symOne :: s .fail))
      .A []) .B [] := by
    funext k
    by_cases hkB : k = .B
    · subst k; simp
    · by_cases hkA : k = .A
      · subst k; simp [hkB]
      · by_cases hkF : k = .fail
        · subst k; simp [s1, hkA, hkB, hgcd]
        · simp [s1, hkA, hkB, hkF]
  refine ⟨t1 + 1 + t2, ?_, by rwa [hu] at hex⟩
  nlinarith

/-! ## Input parsing: reading integers, skipping the header, and main loop -/

def isBit (x : Option Sym) : Bool :=
  decide (x = some symZero) || decide (x = some symOne)

def readBitsAct (h : K → Option Sym) (k : K) : StackAct Sym :=
  if k = .ki then .pop
  else if k = .T1 then match h .ki with | some a => .push a | none => .keep
  else .keep

def readBitsProg : StackProg K Sym :=
  .loop (fun h => isBit (h .ki)) (.act readBitsAct)

def popIfProg (k : K) (x : Sym) : StackProg K Sym :=
  .branch (fun h => decide (h k = some x)) (popProg k) noop

def readNumProg : StackProg K Sym :=
  .seq (popIfProg .ki symMinus)
    (.seq readBitsProg
      (.seq (popIfProg .ki symSep)
        (.seq (stripZerosProg .T1)
              (transferProg .T1 (fun k => decide (k = .A))))))

def popMinusFailAct (_h : K → Option Sym) (k : K) : StackAct Sym :=
  if k = .ki then .pop
  else if k = .fail then .push symOne
  else .keep

def readDenProg : StackProg K Sym :=
  .seq (.branch (fun h => decide (h .ki = some symMinus)) (.act popMinusFailAct) noop)
    (.seq readBitsProg
      (.seq (popIfProg .ki symSep)
        (.seq (stripZerosProg .T1)
          (.seq (transferProg .T1 (fun k => decide (k = .B)))
                (.branch (fun h => (h .B).isNone) (pushProg .fail symOne) noop)))))

def testPairs (h : K → Option Sym) : Bool :=
  match h .ki with
  | some (some (Sum.inl _)) => true
  | _ => false

def pairStepProg : StackProg K Sym :=
  .seq readNumProg (.seq readDenProg gcdCheckProg)

def pairsLoopProg : StackProg K Sym :=
  .loop testPairs pairStepProg

def skipFirstProg : StackProg K Sym :=
  .seq
    (.loop (fun h => match h .ki with
      | some (some (Sum.inl .sep)) => false
      | some (some (Sum.inl _)) => true
      | _ => false) (popProg .ki))
    (popIfProg .ki symSep)

def finalizeProg : StackProg K Sym :=
  .branch (fun h => (h .fail).isSome) (clearProg .ko) noop

def mainProg : StackProg K Sym :=
  .seq (copyProg .ki .ko .T1)
    (.seq skipFirstProg
      (.seq pairsLoopProg finalizeProg))

def bitsPrefix : List Sym → List Bool
  | some (Sum.inl BSym.zero) :: t => false :: bitsPrefix t
  | some (Sum.inl BSym.one) :: t => true :: bitsPrefix t
  | _ => []

def bitsRest : List Sym → List Sym
  | some (Sum.inl BSym.zero) :: t => bitsRest t
  | some (Sum.inl BSym.one) :: t => bitsRest t
  | l => l

lemma bitsPrefix_bitsRest_length (l : List Sym) :
    (bitsPrefix l).length + (bitsRest l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rcases x with _ | (b | b)
    · simp [bitsPrefix, bitsRest]
    · cases b <;> simp [bitsPrefix, bitsRest] <;> omega
    · simp [bitsPrefix, bitsRest]

lemma exec_readBits : ∀ (l : List Sym) (s : K → List Sym), s .ki = l →
    readBitsProg.Exec s
      (Function.update (Function.update s .ki (bitsRest l)) .T1
        ((bitsPrefix l).reverse.map bitSym ++ s .T1))
      (3 * (bitsPrefix l).length + 1)
  | [], s, hki => by
    have h := StackProg.Exec.loopFalse (p := .act readBitsAct)
      (test := fun (h : K → Option Sym) => isBit (h .ki)) (s := s) (by simp [isBit, hki])
    have hu : Function.update (Function.update s .ki []) .T1 (s .T1) = s := by
      funext k; by_cases h1 : k = .T1
      · subst k; simp
      · by_cases h2 : k = .ki
        · subst k; simp [h1, hki]
        · simp [h1, h2]
    simpa [readBitsProg, bitsPrefix, bitsRest, hu] using h
  | x :: t, s, hki => by
    rcases x with _ | (b | b)
    · have h := StackProg.Exec.loopFalse (p := .act readBitsAct)
        (test := fun (h : K → Option Sym) => isBit (h .ki)) (s := s) (by simp [isBit, hki])
      have hu : Function.update (Function.update s .ki (none :: t)) .T1 (s .T1) = s := by
        funext k; by_cases h1 : k = .T1
        · subst k; simp
        · by_cases h2 : k = .ki
          · subst k; simp [h1, hki]
          · simp [h1, h2]
      simpa [readBitsProg, bitsPrefix, bitsRest, hu] using h
    · cases b with
      | zero =>
        have hstep := StackProg.Exec.act readBitsAct s
        set s1 := StackProg.applyAct readBitsAct s
        have hs1ki : s1 .ki = t := by simp [s1, StackProg.applyAct, readBitsAct, hki, StackAct.apply]
        have ih := exec_readBits t s1 hs1ki
        have hloop := StackProg.Exec.loopTrue (test := fun (h : K → Option Sym) => isBit (h .ki))
          (by simp [isBit, hki]) hstep ih
        have hu : Function.update (Function.update s1 .ki (bitsRest t)) .T1
            ((bitsPrefix t).reverse.map bitSym ++ s1 .T1) =
          Function.update (Function.update s .ki (bitsRest (symZero :: t))) .T1
            ((bitsPrefix (symZero :: t)).reverse.map bitSym ++ s .T1) := by
          funext k
          by_cases h1 : k = .T1
          · subst k
            simp [s1, StackProg.applyAct, readBitsAct, hki, StackAct.apply, bitsPrefix]
          · by_cases h2 : k = .ki
            · subst k; simp [h1, bitsRest]
            · simp [s1, StackProg.applyAct, readBitsAct, h1, h2, StackAct.apply]
        have ht : 1 + 1 + 1 + (3 * (bitsPrefix t).length + 1) =
            3 * (bitsPrefix (symZero :: t)).length + 1 := by
          simp [bitsPrefix]; omega
        rw [hu, ht] at hloop; exact hloop
      | one =>
        have hstep := StackProg.Exec.act readBitsAct s
        set s1 := StackProg.applyAct readBitsAct s
        have hs1ki : s1 .ki = t := by simp [s1, StackProg.applyAct, readBitsAct, hki, StackAct.apply]
        have ih := exec_readBits t s1 hs1ki
        have hloop := StackProg.Exec.loopTrue (test := fun (h : K → Option Sym) => isBit (h .ki))
          (by simp [isBit, hki]) hstep ih
        have hu : Function.update (Function.update s1 .ki (bitsRest t)) .T1
            ((bitsPrefix t).reverse.map bitSym ++ s1 .T1) =
          Function.update (Function.update s .ki (bitsRest (symOne :: t))) .T1
            ((bitsPrefix (symOne :: t)).reverse.map bitSym ++ s .T1) := by
          funext k
          by_cases h1 : k = .T1
          · subst k
            simp [s1, StackProg.applyAct, readBitsAct, hki, StackAct.apply, bitsPrefix]
          · by_cases h2 : k = .ki
            · subst k; simp [h1, bitsRest]
            · simp [s1, StackProg.applyAct, readBitsAct, h1, h2, StackAct.apply]
        have ht : 1 + 1 + 1 + (3 * (bitsPrefix t).length + 1) =
            3 * (bitsPrefix (symOne :: t)).length + 1 := by
          simp [bitsPrefix]; omega
        rw [hu, ht] at hloop; exact hloop
      | minus =>
        have h := StackProg.Exec.loopFalse (p := .act readBitsAct)
          (test := fun (h : K → Option Sym) => isBit (h .ki)) (s := s) (by simp [isBit, hki])
        have hu : Function.update (Function.update s .ki (symMinus :: t)) .T1 (s .T1) = s := by
          funext k; by_cases h1 : k = .T1
          · subst k; simp
          · by_cases h2 : k = .ki
            · subst k; simp [h1, hki]
            · simp [h1, h2]
        simpa [readBitsProg, bitsPrefix, bitsRest, hu] using h
      | sep =>
        have h := StackProg.Exec.loopFalse (p := .act readBitsAct)
          (test := fun (h : K → Option Sym) => isBit (h .ki)) (s := s) (by simp [isBit, hki])
        have hu : Function.update (Function.update s .ki (symSep :: t)) .T1 (s .T1) = s := by
          funext k; by_cases h1 : k = .T1
          · subst k; simp
          · by_cases h2 : k = .ki
            · subst k; simp [h1, hki]
            · simp [h1, h2]
        simpa [readBitsProg, bitsPrefix, bitsRest, hu] using h
    · have h := StackProg.Exec.loopFalse (p := .act readBitsAct)
        (test := fun (h : K → Option Sym) => isBit (h .ki)) (s := s) (by simp [isBit, hki])
      have hu : Function.update (Function.update s .ki (some (Sum.inr b) :: t)) .T1 (s .T1) = s := by
        funext k; by_cases h1 : k = .T1
        · subst k; simp
        · by_cases h2 : k = .ki
          · subst k; simp [h1, hki]
          · simp [h1, h2]
      simpa [readBitsProg, bitsPrefix, bitsRest, hu] using h

lemma exec_popIf (k : K) (x : Sym) (s : K → List Sym) :
    (popIfProg k x).Exec s
      (Function.update s k (if (s k).head? = some x then (s k).tail else s k)) 2 := by
  by_cases hx : (s k).head? = some x
  · have hpop := (CookPvsNP.stack_basic_macros k s).2.1
    simpa [popIfProg, hx] using StackProg.Exec.branchTrue (test := fun h => decide (h k = some x))
      (by simp [hx]) hpop
  · have hu : Function.update s k (s k) = s := by
      funext j; by_cases hj : j = k
      · subst j; simp
      · simp [hj]
    simpa [popIfProg, hx, hu] using StackProg.Exec.branchFalse
      (test := fun h => decide (h k = some x)) (by simp [hx]) (exec_noop s)

lemma exec_readNum_any (s : K → List Sym) (hA : s .A = []) (hT1 : s .T1 = []) :
    ∃ (a : ℕ) (ki' : List Sym) (t : ℕ),
      t ≤ 9 * (s .ki).length + 12 ∧
      ki'.length ≤ (s .ki).length ∧
      (testPairs (fun k => (s k).head?) = true → ki'.length < (s .ki).length) ∧
      (natStack a).length ≤ (s .ki).length ∧
      readNumProg.Exec s (Function.update (Function.update s .ki ki') .A (natStack a)) t := by
  have h1 := exec_popIf .ki symMinus s
  set l1 := if (s .ki).head? = some symMinus then (s .ki).tail else s .ki
  set s1 := Function.update s .ki l1
  have h2 := exec_readBits l1 s1 (by simp [s1])
  set s2 := Function.update (Function.update s1 .ki (bitsRest l1)) .T1
    ((bitsPrefix l1).reverse.map bitSym ++ s1 .T1)
  have h3 := exec_popIf .ki symSep s2
  set l3 := if (bitsRest l1).head? = some symSep then (bitsRest l1).tail else bitsRest l1
  set s3 := Function.update s2 .ki l3
  have hs3_eq : s3 = Function.update s2 .ki (if (s2 .ki).head? = some symSep then (s2 .ki).tail else s2 .ki) := by
    simp [s3, l3, s2]
  rw [← hs3_eq] at h3
  have hs3T1 : s3 .T1 = (bitsPrefix l1).reverse.map bitSym := by
    simp [s3, s2, s1, hT1]
  obtain ⟨t4, ht4, h4⟩ := exec_stripZeros .T1 ((bitsPrefix l1).reverse.map bitSym) s3 hs3T1
  set s4 := Function.update s3 .T1
    (((bitsPrefix l1).reverse.map bitSym).dropWhile (fun x => decide (x = symZero)))
  have h5 := exec_transfer_single .T1 .A (by decide) s4
  set s5 := Function.update (Function.update s4 .T1 []) .A ((s4 .T1).reverse ++ s4 .A)
  have hex := StackProg.Exec.seq h1 (StackProg.Exec.seq h2
    (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 h5)))
  set a := ofBits (bitsPrefix l1)
  have hs4T1_rev : (s4 .T1).reverse = natStack a := by
    simp only [s4, Function.update_self, dropWhile_map_bitSym, ← List.map_reverse]
    rw [dropWhile_rev_eq_bits, List.reverse_reverse]
    rfl
  have hs5eq : s5 = Function.update (Function.update s .ki l3) .A (natStack a) := by
    funext k
    by_cases hkA : k = .A
    · subst k
      simp only [s5, Function.update_self]
      rw [hs4T1_rev]
      simp [s4, s3, s2, s1, hA]
    · by_cases hkT1 : k = .T1
      · subst k; simp [s5, hkA, hT1]
      · by_cases hkki : k = .ki
        · subst k; simp [s5, s4, s3, hkA, hkT1]
        · simp [s5, s4, s3, s2, s1, hkA, hkT1, hkki]
  have hl1_le : l1.length ≤ (s .ki).length := by
    dsimp [l1]; split_ifs <;> simp
  have hbr_le := bitsPrefix_bitsRest_length l1
  have hl3_le : l3.length ≤ (bitsRest l1).length := by
    dsimp [l3]; split_ifs <;> simp
  have hstrict : testPairs (fun k => (s k).head?) = true → l3.length < (s .ki).length := by
    intro htp
    cases hki : s .ki with
    | nil => simp [testPairs, hki] at htp
    | cons x xs =>
      rcases x with _ | (b | b)
      · simp [testPairs, hki] at htp
      · cases b with
        | minus =>
          have hl1eq : l1 = xs := by simp [l1, hki]
          have := bitsPrefix_bitsRest_length xs
          rw [hl1eq] at hl3_le
          simp only [List.length_cons]
          omega
        | zero =>
          have hl1eq : l1 = symZero :: xs := by simp [l1, hki]
          have := bitsPrefix_bitsRest_length xs
          rw [hl1eq] at hl3_le
          simp only [bitsRest, List.length_cons] at hl3_le ⊢
          omega
        | one =>
          have hl1eq : l1 = symOne :: xs := by simp [l1, hki]
          have := bitsPrefix_bitsRest_length xs
          rw [hl1eq] at hl3_le
          simp only [bitsRest, List.length_cons] at hl3_le ⊢
          omega
        | sep =>
          have hl1eq : l1 = symSep :: xs := by simp [l1, hki]
          have hl3eq : l3 = xs := by simp [l3, hl1eq, bitsRest]
          simp [hl3eq]
      · simp [testPairs, hki] at htp
  have ha_len : (natStack a).length ≤ (bitsPrefix l1).length := by
    rw [← hs4T1_rev, List.length_reverse]
    simp only [s4, Function.update_self]
    have := List.length_dropWhile_le (p := fun x => decide (x = symZero))
      ((bitsPrefix l1).reverse.map bitSym)
    simpa using this
  have hs4T1_len : (s4 .T1).length ≤ (bitsPrefix l1).length := by
    have := List.length_dropWhile_le (p := fun x => decide (x = symZero))
      ((bitsPrefix l1).reverse.map bitSym)
    simpa [s4] using this
  refine ⟨a, l3, _, ?_, by omega, hstrict, by omega, by rwa [hs5eq] at hex⟩
  simp only [List.length_map, List.length_reverse] at ht4
  omega

lemma exec_readDen_any (s : K → List Sym) (hB : s .B = []) (hT1 : s .T1 = []) :
    ∃ (b : ℕ) (ki' fail' : List Sym) (t : ℕ),
      t ≤ 9 * (s .ki).length + 15 ∧
      ki'.length ≤ (s .ki).length ∧
      (natStack b).length ≤ (s .ki).length ∧
      readDenProg.Exec s
        (Function.update (Function.update (Function.update s .ki ki') .B (natStack b)) .fail fail') t := by
  have h1 : ∃ (l1 fail1 : List Sym),
      l1.length ≤ (s .ki).length ∧
      (StackProg.branch (fun h => decide (h .ki = some symMinus)) (.act popMinusFailAct) noop).Exec s
        (Function.update (Function.update s .ki l1) .fail fail1) 2 := by
    by_cases hm : (s .ki).head? = some symMinus
    · refine ⟨(s .ki).tail, symOne :: s .fail, by simp, ?_⟩
      have hact := StackProg.Exec.act popMinusFailAct s
      have heq : StackProg.applyAct popMinusFailAct s =
          Function.update (Function.update s .ki (s .ki).tail) .fail (symOne :: s .fail) := by
        funext k; cases k <;> simp [StackProg.applyAct, popMinusFailAct, StackAct.apply]
      rw [heq] at hact
      exact StackProg.Exec.branchTrue (by simp [hm]) hact
    · refine ⟨s .ki, s .fail, le_refl _, ?_⟩
      have heq : Function.update (Function.update s .ki (s .ki)) .fail (s .fail) = s := by
        funext k; cases k <;> simp
      rw [heq]
      exact StackProg.Exec.branchFalse (by simp [hm]) (exec_noop s)
  obtain ⟨l1, fail1, hl1_le, h1exec⟩ := h1
  set s1 := Function.update (Function.update s .ki l1) .fail fail1
  have h2 := exec_readBits l1 s1 (by simp [s1])
  set s2 := Function.update (Function.update s1 .ki (bitsRest l1)) .T1
    ((bitsPrefix l1).reverse.map bitSym ++ s1 .T1)
  have h3 := exec_popIf .ki symSep s2
  set l3 := if (bitsRest l1).head? = some symSep then (bitsRest l1).tail else bitsRest l1
  set s3 := Function.update s2 .ki l3
  have hs3_eq : s3 = Function.update s2 .ki (if (s2 .ki).head? = some symSep then (s2 .ki).tail else s2 .ki) := by
    simp [s3, l3, s2]
  rw [← hs3_eq] at h3
  have hs3T1 : s3 .T1 = (bitsPrefix l1).reverse.map bitSym := by
    simp [s3, s2, s1, hT1]
  obtain ⟨t4, ht4, h4⟩ := exec_stripZeros .T1 ((bitsPrefix l1).reverse.map bitSym) s3 hs3T1
  set s4 := Function.update s3 .T1
    (((bitsPrefix l1).reverse.map bitSym).dropWhile (fun x => decide (x = symZero)))
  have h5 := exec_transfer_single .T1 .B (by decide) s4
  set s5 := Function.update (Function.update s4 .T1 []) .B ((s4 .T1).reverse ++ s4 .B)
  set b := ofBits (bitsPrefix l1)
  have hs4T1_rev : (s4 .T1).reverse = natStack b := by
    simp only [s4, Function.update_self, dropWhile_map_bitSym, ← List.map_reverse]
    rw [dropWhile_rev_eq_bits, List.reverse_reverse]
    rfl
  have hs5eq : s5 = Function.update (Function.update (Function.update s .ki l3) .B (natStack b)) .fail fail1 := by
    funext k
    by_cases hkF : k = .fail
    · subst k; simp [s5, s4, s3, s2, s1]
    · by_cases hkB : k = .B
      · subst k
        simp only [s5, Function.update_self, Function.update_of_ne hkF]
        rw [hs4T1_rev]
        simp [s4, s3, s2, s1, hB]
      · by_cases hkT1 : k = .T1
        · subst k; simp [s5, hkB, hkF, hT1]
        · by_cases hkki : k = .ki
          · subst k; simp [s5, s4, s3, hkB, hkT1, hkF]
          · simp [s5, s4, s3, s2, s1, hkB, hkT1, hkki, hkF]
  have h6 : ∃ fail2 : List Sym,
      (StackProg.branch (fun h => (h .B).isNone) (pushProg .fail symOne) noop).Exec s5
        (Function.update s5 .fail fail2) 2 := by
    by_cases hb0 : (s5 .B).head?.isNone = true
    · exact ⟨symOne :: s5 .fail, StackProg.Exec.branchTrue hb0
        ((CookPvsNP.stack_basic_macros .fail s5).1 symOne)⟩
    · have hb0f : (s5 .B).head?.isNone = false := by
        cases h : (s5 .B).head?.isNone <;> simp_all
      have hu : Function.update s5 .fail (s5 .fail) = s5 := by
        funext k; by_cases hk : k = .fail <;> simp [hk]
      refine ⟨s5 .fail, ?_⟩
      rw [hu]
      exact StackProg.Exec.branchFalse hb0f (exec_noop s5)
  obtain ⟨fail2, h6exec⟩ := h6
  have hex := StackProg.Exec.seq h1exec (StackProg.Exec.seq h2
    (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 (StackProg.Exec.seq h5 h6exec))))
  have hu : Function.update s5 .fail fail2 =
      Function.update (Function.update (Function.update s .ki l3) .B (natStack b)) .fail fail2 := by
    rw [hs5eq, Function.update_idem]
  have hbr_le := bitsPrefix_bitsRest_length l1
  have hl3_le : l3.length ≤ (bitsRest l1).length := by
    dsimp [l3]; split_ifs <;> simp
  have hb_len : (natStack b).length ≤ (bitsPrefix l1).length := by
    rw [← hs4T1_rev, List.length_reverse]
    simp only [s4, Function.update_self]
    have := List.length_dropWhile_le (p := fun x => decide (x = symZero))
      ((bitsPrefix l1).reverse.map bitSym)
    simpa using this
  have hs4T1_len : (s4 .T1).length ≤ (bitsPrefix l1).length := by
    have := List.length_dropWhile_le (p := fun x => decide (x = symZero))
      ((bitsPrefix l1).reverse.map bitSym)
    simpa [s4] using this
  refine ⟨b, l3, fail2, _, ?_, by omega, by omega, by rwa [hu] at hex⟩
  simp only [List.length_map, List.length_reverse] at ht4
  omega

lemma exec_pairsLoop_any : ∀ (N : ℕ) (s : K → List Sym),
    (s .ki).length ≤ N →
    s .A = [] → s .B = [] → s .T1 = [] → s .T2 = [] → s .C = [] →
    ∃ (s' : K → List Sym) (t : ℕ),
      t ≤ N * (96 * N * N + 90 * N + 50) + 1 ∧
      pairsLoopProg.Exec s s' t ∧
      s' .ko = s .ko := by
  intro N
  induction N with
  | zero =>
    intro s hN _ _ _ _ _
    have hki : s .ki = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hstop : testPairs (fun k => (s k).head?) = false := by simp [testPairs, hki]
    exact ⟨s, 1, by omega, StackProg.Exec.loopFalse hstop, rfl⟩
  | succ N ih =>
    intro s hN hA hB hT1 hT2 hC
    by_cases htp : testPairs (fun k => (s k).head?) = true
    · obtain ⟨a, ki1, t1, ht1, hki1_le, hki1_lt, ha_len, h1⟩ := exec_readNum_any s hA hT1
      set s1 := Function.update (Function.update s .ki ki1) .A (natStack a)
      obtain ⟨b, ki2, fail2, t2, ht2, hki2_le, hb_len, h2⟩ :=
        exec_readDen_any s1 (by simp [s1, hB]) (by simp [s1, hT1])
      set s2 := Function.update (Function.update (Function.update s1 .ki ki2) .B (natStack b)) .fail fail2
      obtain ⟨t3, ht3, h3⟩ := exec_gcdCheck s2 a b (by simp [s2, s1]) (by simp [s2])
        (by simp [s2, s1, hT1]) (by simp [s2, s1, hT2]) (by simp [s2, s1, hC])
      set s3 := Function.update (Function.update
        (Function.update s2 .fail (if Nat.gcd a b = 1 then s2 .fail else symOne :: s2 .fail))
        .A []) .B []
      have hbody := StackProg.Exec.seq h1 (StackProg.Exec.seq h2 h3)
      have hki1_lt' : ki1.length < (s .ki).length := hki1_lt htp
      have hs1ki_len : (s1 .ki).length = ki1.length := by simp [s1]
      have hs3ki_len : (s3 .ki).length ≤ N := by
        have h3eq : s3 .ki = ki2 := by simp [s3, s2]
        rw [h3eq]
        rw [hs1ki_len] at hki2_le
        omega
      obtain ⟨s', trec, htrec, hrec, hko⟩ := ih s3 hs3ki_len (by simp [s3]) (by simp [s3])
        (by simp [s3, s2, s1, hT1]) (by simp [s3, s2, s1, hT2]) (by simp [s3, s2, s1, hC])
      have hloop := StackProg.Exec.loopTrue htp hbody hrec
      have hs3ko : s3 .ko = s .ko := by simp [s3, s2, s1]
      refine ⟨s', _, ?_, hloop, hko.trans hs3ko⟩
      have hLle : (natStack a).length + (natStack b).length ≤ 2 * (N + 1) := by
        rw [hs1ki_len] at hb_len; omega
      rw [hs1ki_len] at ht2
      nlinarith
    · have hstop : testPairs (fun k => (s k).head?) = false := by
        cases h : testPairs (fun k => (s k).head?) <;> simp_all
      exact ⟨s, 1, by omega, StackProg.Exec.loopFalse hstop, rfl⟩

lemma exec_skipFirstLoop : ∀ (l : List Sym) (s : K → List Sym), s .ki = l →
    ∃ (l' : List Sym) (t : ℕ),
      t ≤ 3 * l.length + 1 ∧
      l'.length ≤ l.length ∧
      (StackProg.loop (fun h => match h .ki with
        | some (some (Sum.inl .sep)) => false
        | some (some (Sum.inl _)) => true
        | _ => false) (popProg .ki)).Exec s (Function.update s .ki l') t
  | [], s, hki => by
    have hu : Function.update s .ki [] = s := by
      funext k; by_cases hk : k = .ki <;> simp [hk, hki]
    exact ⟨[], 1, by simp, le_refl _, by rw [hu]; exact StackProg.Exec.loopFalse (by simp [hki])⟩
  | x :: xs, s, hki => by
    set test : (K → Option Sym) → Bool := fun h => match h .ki with
      | some (some (Sum.inl .sep)) => false
      | some (some (Sum.inl _)) => true
      | _ => false
    by_cases ht : test (fun k => (s k).head?) = true
    · have hpop := (CookPvsNP.stack_basic_macros .ki s).2.1
      rw [hki] at hpop
      simp only [List.tail_cons] at hpop
      obtain ⟨l', t', ht', hl', hex⟩ := exec_skipFirstLoop xs (Function.update s .ki xs) (by simp)
      refine ⟨l', 1 + 1 + 1 + t', by simp; omega, by simp; omega, ?_⟩
      have hloop := StackProg.Exec.loopTrue ht hpop hex
      simpa [Function.update_idem] using hloop
    · have hf : test (fun k => (s k).head?) = false := by
        cases h : test (fun k => (s k).head?) <;> simp_all
      have hu : Function.update s .ki (x :: xs) = s := by
        funext k; by_cases hk : k = .ki <;> simp [hk, hki]
      exact ⟨x :: xs, 1, by simp, le_refl _, by rw [hu]; exact StackProg.Exec.loopFalse hf⟩

lemma mainProg_terminates (w : List Sym) :
    ∃ (s : K → List Sym) (t : ℕ),
      t ≤ 96 * (w.length + 1) ^ 3 + 100 * (w.length + 1) ^ 2 + 100 * (w.length + 1) + 100 ∧
      mainProg.Exec (fun j => if j = .ki then w else []) s t := by
  set s0 : K → List Sym := fun j => if j = .ki then w else []
  have hcopy := CookPvsNP.stack_copy .ki .ko .T1 (by decide) (by decide) (by decide) s0 (by simp [s0])
  set s1 := Function.update s0 .ko (s0 .ki ++ s0 .ko)
  have hs1ki : s1 .ki = w := by simp [s1, s0]
  have hs1ko : s1 .ko = w := by simp [s1, s0]
  obtain ⟨l1, tsk, htsk, hl1, hsk1⟩ := exec_skipFirstLoop w s1 hs1ki
  set s2 := Function.update s1 .ki l1
  have hsk2 := exec_popIf .ki symSep s2
  set l2 := if (s2 .ki).head? = some symSep then (s2 .ki).tail else s2 .ki
  set s3 := Function.update s2 .ki l2
  have hsk := StackProg.Exec.seq hsk1 hsk2
  have hl2 : (s3 .ki).length ≤ w.length := by
    have : l2.length ≤ l1.length := by
      dsimp [l2]; split_ifs <;> simp [s2]
    simp only [s3, Function.update_self]; omega
  obtain ⟨s4, tlp, htlp, hlp, hs4ko⟩ := exec_pairsLoop_any w.length s3 hl2
    (by simp [s3, s2, s1, s0]) (by simp [s3, s2, s1, s0])
    (by simp [s3, s2, s1, s0]) (by simp [s3, s2, s1, s0]) (by simp [s3, s2, s1, s0])
  have hs4ko_w : s4 .ko = w := by
    rw [hs4ko]; simp [s3, s2, hs1ko]
  have hfin : ∃ (s5 : K → List Sym) (tf : ℕ), tf ≤ 3 * w.length + 2 ∧ finalizeProg.Exec s4 s5 tf := by
    by_cases hf : (s4 .fail).head?.isSome = true
    · have hclr := (CookPvsNP.stack_basic_macros .ko s4).2.2
      exact ⟨Function.update s4 .ko [], 1 + (3 * (s4 .ko).length + 1),
        by rw [hs4ko_w]; omega,
        StackProg.Exec.branchTrue (test := fun (h : K → Option Sym) => (h .fail).isSome) hf hclr⟩
    · have hff : (s4 .fail).head?.isSome = false := by
        cases h : (s4 .fail).head?.isSome <;> simp_all
      exact ⟨s4, 1 + 1, by omega,
        StackProg.Exec.branchFalse (test := fun (h : K → Option Sym) => (h .fail).isSome) hff (exec_noop s4)⟩
  obtain ⟨s5, tf, htf, hfinexec⟩ := hfin
  have hex := StackProg.Exec.seq hcopy (StackProg.Exec.seq hsk (StackProg.Exec.seq hlp hfinexec))
  refine ⟨s5, _, ?_, hex⟩
  have hs0ki : (s0 .ki).length = w.length := by simp [s0]
  rw [hs0ki]
  nlinarith

/-! ## Correctness on empty input and well-formed `chkWord c d` -/

lemma mainProg_nil :
    ∃ (s : K → List Sym) (t : ℕ),
      mainProg.Exec (fun j => if j = .ki then [] else []) s t ∧ s .ko = [] := by
  set s0 : K → List Sym := fun j => if j = .ki then [] else []
  have hcopy := CookPvsNP.stack_copy .ki .ko .T1 (by decide) (by decide) (by decide) s0 rfl
  have hs1 : Function.update s0 .ko (s0 .ki ++ s0 .ko) = s0 := by
    funext k; by_cases hk : k = .ko <;> simp [s0, hk]
  rw [hs1] at hcopy
  have hsk1 := StackProg.Exec.loopFalse (p := popProg .ki)
    (test := fun (h : K → Option Sym) => match h .ki with
      | some (some (Sum.inl .sep)) => false
      | some (some (Sum.inl _)) => true
      | _ => false) (s := s0) (by simp [s0])
  have hsk2 := StackProg.Exec.branchFalse (test := fun (h : K → Option Sym) => decide (h .ki = some symSep))
    (p := popProg .ki) (by simp [s0]) (exec_noop s0)
  have hlp := StackProg.Exec.loopFalse (p := pairStepProg) (test := testPairs)
    (s := s0) (by simp [testPairs, s0])
  have hfin := StackProg.Exec.branchFalse (test := fun (h : K → Option Sym) => (h .fail).isSome)
    (p := clearProg .ko) (by simp [s0]) (exec_noop s0)
  exact ⟨s0, _, StackProg.Exec.seq hcopy (StackProg.Exec.seq (StackProg.Exec.seq hsk1 hsk2)
    (StackProg.Exec.seq hlp hfin)), by simp [s0]⟩

def encIntSym (z : ℤ) : List Sym := (encInt z).map (some ∘ Sum.inl)
def encIntsSym (cs : List ℤ) : List Sym := (encInts cs).map (some ∘ Sum.inl)

lemma encIntSym_eq (z : ℤ) :
    encIntSym z = (if z < 0 then [symMinus] else []) ++ natStack z.natAbs ++ [symSep] := by
  unfold encIntSym encInt encNat natStack bitSym
  split_ifs <;> simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
    List.nil_append, List.append_assoc, Function.comp_def]
  · congr 2; apply List.map_congr_left; intro b _; cases b <;> rfl
  · congr 1; apply List.map_congr_left; intro b _; cases b <;> rfl

lemma encIntsSym_nil : encIntsSym [] = [] := rfl

lemma encIntsSym_cons (z : ℤ) (zs : List ℤ) :
    encIntsSym (z :: zs) = encIntSym z ++ encIntsSym zs := by
  simp [encIntsSym, encIntSym, encInts, List.flatMap_cons, List.map_append]

lemma bitsPrefix_bitsRest_bits (bs : List Bool) (rest : List Sym) :
    bitsPrefix (bs.map bitSym ++ symSep :: rest) = bs ∧
    bitsRest (bs.map bitSym ++ symSep :: rest) = symSep :: rest := by
  induction bs with
  | nil => simp [bitsPrefix, bitsRest]
  | cons b t ih =>
    cases b <;> simp [bitsPrefix, bitsRest, ih]

lemma exec_skipFirst_encInt (z : ℤ) (rest : List Sym) (s : K → List Sym)
    (hki : s .ki = encIntSym z ++ rest) :
    ∃ t, skipFirstProg.Exec s (Function.update s .ki rest) t := by
  have hloop_list : ∀ (pref : List Sym) (s1 : K → List Sym),
      s1 .ki = pref ++ symSep :: rest →
      (∀ x ∈ pref, match x with | some (Sum.inl .sep) => False | some (Sum.inl _) => True | _ => False) →
      ∃ t, (StackProg.loop (fun h => match h .ki with
        | some (some (Sum.inl .sep)) => false
        | some (some (Sum.inl _)) => true
        | _ => false) (popProg .ki)).Exec s1 (Function.update s1 .ki (symSep :: rest)) t := by
    intro pref
    induction pref with
    | nil =>
      intro s1 hs1 _
      have hu : Function.update s1 .ki (symSep :: rest) = s1 := by
        funext k; by_cases hk : k = .ki <;> simp [hk, hs1]
      exact ⟨1, by rw [hu]; exact StackProg.Exec.loopFalse (by simp [hs1])⟩
    | cons x xs ih =>
      intro s1 hs1 hmem
      have hx := hmem x (by simp)
      have htest : (match (s1 .ki).head? with
        | some (some (Sum.inl .sep)) => false
        | some (some (Sum.inl _)) => true
        | _ => false) = true := by
        rw [hs1]; rcases x with _ | (b | b)
        · cases hx
        · cases b <;> simp at hx ⊢
        · cases hx
      have hpop := (CookPvsNP.stack_basic_macros .ki s1).2.1
      rw [hs1] at hpop
      simp only [List.cons_append, List.tail_cons] at hpop
      obtain ⟨t', ht'⟩ := ih (Function.update s1 .ki (xs ++ symSep :: rest)) (by simp)
        (fun y hy => hmem y (by simp [hy]))
      have hu : Function.update (Function.update s1 .ki (xs ++ symSep :: rest)) .ki (symSep :: rest) =
          Function.update s1 .ki (symSep :: rest) := by simp [Function.update_idem]
      exact ⟨_, by rw [hu] at ht'; exact StackProg.Exec.loopTrue htest hpop ht'⟩
  have hki' : s .ki = ((if z < 0 then [symMinus] else []) ++ natStack z.natAbs) ++ symSep :: rest := by
    rw [hki, encIntSym_eq]; simp [List.append_assoc]
  obtain ⟨t1, h1⟩ := hloop_list _ s hki' (by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with h1 | h2
    · split_ifs at h1
      · simp at h1; subst h1; trivial
      · simp at h1
    · unfold natStack at h2
      simp only [List.mem_map] at h2
      obtain ⟨b, _, rfl⟩ := h2
      cases b <;> trivial)
  set s1 := Function.update s .ki (symSep :: rest)
  have h2 := exec_popIf .ki symSep s1
  have hs2 : Function.update s1 .ki (if (s1 .ki).head? = some symSep then (s1 .ki).tail else s1 .ki) =
      Function.update s .ki rest := by
    simp [s1, Function.update_idem]
  rw [hs2] at h2
  exact ⟨_, StackProg.Exec.seq h1 h2⟩

lemma exec_readNum_enc (z : ℤ) (rest : List Sym) (s : K → List Sym)
    (hki : s .ki = encIntSym z ++ rest) (hA : s .A = []) (hT1 : s .T1 = []) :
    ∃ t, readNumProg.Exec s (Function.update (Function.update s .ki rest) .A (natStack z.natAbs)) t := by
  have h1 := exec_popIf .ki symMinus s
  have hl1 : (if (s .ki).head? = some symMinus then (s .ki).tail else s .ki) =
      natStack z.natAbs ++ symSep :: rest := by
    rw [hki, encIntSym_eq]
    by_cases hz : z < 0
    · simp [hz]
    · simp only [hz, ↓reduceIte, List.nil_append, List.append_assoc, List.singleton_append]
      cases hnb : Nat.bits z.natAbs with
      | nil => simp [natStack, hnb]
      | cons b t => cases b <;> simp [natStack, hnb]
  rw [hl1] at h1
  set s1 := Function.update s .ki (natStack z.natAbs ++ symSep :: rest)
  have h2 := exec_readBits (natStack z.natAbs ++ symSep :: rest) s1 (by simp [s1])
  obtain ⟨hbp, hbr⟩ := bitsPrefix_bitsRest_bits (Nat.bits z.natAbs) rest
  unfold natStack at h2
  rw [hbp, hbr] at h2
  set s2 := Function.update (Function.update s1 .ki (symSep :: rest)) .T1
    ((Nat.bits z.natAbs).reverse.map bitSym ++ s1 .T1)
  have h3 := exec_popIf .ki symSep s2
  have hs3eq : Function.update s2 .ki (if (s2 .ki).head? = some symSep then (s2 .ki).tail else s2 .ki) =
      Function.update s2 .ki rest := by simp [s2]
  rw [hs3eq] at h3
  set s3 := Function.update s2 .ki rest
  have hs3T1 : s3 .T1 = (Nat.bits z.natAbs).reverse.map bitSym := by simp [s3, s2, s1, hT1]
  obtain ⟨t4, _, h4⟩ := exec_stripZeros .T1 ((Nat.bits z.natAbs).reverse.map bitSym) s3 hs3T1
  set s4 := Function.update s3 .T1
    (((Nat.bits z.natAbs).reverse.map bitSym).dropWhile (fun x => decide (x = symZero)))
  have h5 := exec_transfer_single .T1 .A (by decide) s4
  have hs4rev : (s4 .T1).reverse = natStack z.natAbs := by
    simp only [s4, Function.update_self, dropWhile_map_bitSym, ← List.map_reverse]
    rw [dropWhile_rev_eq_bits, List.reverse_reverse, ofBits_bits]
    rfl
  have hs5 : Function.update (Function.update s4 .T1 []) .A ((s4 .T1).reverse ++ s4 .A) =
      Function.update (Function.update s .ki rest) .A (natStack z.natAbs) := by
    funext k
    by_cases hkA : k = .A
    · subst k
      simp only [Function.update_self]
      rw [hs4rev]
      simp [s4, s3, s2, s1, hA]
    · by_cases hkT1 : k = .T1
      · subst k; simp [hkA, hT1]
      · by_cases hkki : k = .ki
        · subst k; simp [s4, s3, hkA, hkT1]
        · simp [s4, s3, s2, s1, hkA, hkT1, hkki]
  rw [hs5] at h5
  exact ⟨_, StackProg.Exec.seq h1 (StackProg.Exec.seq h2
    (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 h5)))⟩

lemma exec_readDen_enc (z : ℤ) (rest : List Sym) (s : K → List Sym)
    (hki : s .ki = encIntSym z ++ rest) (hB : s .B = []) (hT1 : s .T1 = []) :
    ∃ (fail' : List Sym) (t : ℕ),
      (fail'.head?.isSome ↔ (s .fail).head?.isSome ∨ ¬ (0 < z)) ∧
      readDenProg.Exec s
        (Function.update (Function.update (Function.update s .ki rest) .B (natStack z.natAbs)) .fail fail') t := by
  have h1 : ∃ fail1 : List Sym,
      (fail1.head?.isSome ↔ (s .fail).head?.isSome ∨ z < 0) ∧
      (StackProg.branch (fun h => decide (h .ki = some symMinus)) (.act popMinusFailAct) noop).Exec s
        (Function.update (Function.update s .ki (natStack z.natAbs ++ symSep :: rest)) .fail fail1) 2 := by
    by_cases hz : z < 0
    · refine ⟨symOne :: s .fail, by simp [hz], ?_⟩
      have hcond : decide ((s .ki).head? = some symMinus) = true := by
        rw [hki, encIntSym_eq]; simp [hz]
      have hact := StackProg.Exec.act popMinusFailAct s
      have heq : StackProg.applyAct popMinusFailAct s =
          Function.update (Function.update s .ki (natStack z.natAbs ++ symSep :: rest)) .fail (symOne :: s .fail) := by
        funext k; cases k <;> simp [StackProg.applyAct, popMinusFailAct, StackAct.apply, hki, encIntSym_eq, hz]
      rw [heq] at hact
      exact StackProg.Exec.branchTrue hcond hact
    · refine ⟨s .fail, by simp [hz], ?_⟩
      have hki' : s .ki = natStack z.natAbs ++ symSep :: rest := by
        rw [hki, encIntSym_eq]; simp [hz]
      have hcond : decide ((s .ki).head? = some symMinus) = false := by
        rw [hki']
        cases hnb : Nat.bits z.natAbs with
        | nil => simp [natStack, hnb]
        | cons b t => cases b <;> simp [natStack, hnb]
      have heq : Function.update (Function.update s .ki (natStack z.natAbs ++ symSep :: rest)) .fail (s .fail) = s := by
        funext k; cases k <;> simp [hki']
      rw [heq]
      exact StackProg.Exec.branchFalse hcond (exec_noop s)
  obtain ⟨fail1, hfail1, h1exec⟩ := h1
  set s1 := Function.update (Function.update s .ki (natStack z.natAbs ++ symSep :: rest)) .fail fail1
  have h2 := exec_readBits (natStack z.natAbs ++ symSep :: rest) s1 (by simp [s1])
  obtain ⟨hbp, hbr⟩ := bitsPrefix_bitsRest_bits (Nat.bits z.natAbs) rest
  unfold natStack at h2
  rw [hbp, hbr] at h2
  set s2 := Function.update (Function.update s1 .ki (symSep :: rest)) .T1
    ((Nat.bits z.natAbs).reverse.map bitSym ++ s1 .T1)
  have h3 := exec_popIf .ki symSep s2
  have hs3eq : Function.update s2 .ki (if (s2 .ki).head? = some symSep then (s2 .ki).tail else s2 .ki) =
      Function.update s2 .ki rest := by simp [s2]
  rw [hs3eq] at h3
  set s3 := Function.update s2 .ki rest
  have hs3T1 : s3 .T1 = (Nat.bits z.natAbs).reverse.map bitSym := by simp [s3, s2, s1, hT1]
  obtain ⟨t4, _, h4⟩ := exec_stripZeros .T1 ((Nat.bits z.natAbs).reverse.map bitSym) s3 hs3T1
  set s4 := Function.update s3 .T1
    (((Nat.bits z.natAbs).reverse.map bitSym).dropWhile (fun x => decide (x = symZero)))
  have h5 := exec_transfer_single .T1 .B (by decide) s4
  have hs4rev : (s4 .T1).reverse = natStack z.natAbs := by
    simp only [s4, Function.update_self, dropWhile_map_bitSym, ← List.map_reverse]
    rw [dropWhile_rev_eq_bits, List.reverse_reverse, ofBits_bits]
    rfl
  set s5 := Function.update (Function.update (Function.update s .ki rest) .B (natStack z.natAbs)) .fail fail1
  have hs5eq : Function.update (Function.update s4 .T1 []) .B ((s4 .T1).reverse ++ s4 .B) = s5 := by
    funext k
    by_cases hkF : k = .fail
    · subst k; simp [s5, s4, s3, s2, s1]
    · by_cases hkB : k = .B
      · subst k
        simp only [s5, Function.update_self, Function.update_of_ne hkF]
        rw [hs4rev]
        simp [s4, s3, s2, s1, hB]
      · by_cases hkT1 : k = .T1
        · subst k; simp [s5, hkB, hkF, hT1]
        · by_cases hkki : k = .ki
          · subst k; simp [s5, s4, s3, hkB, hkT1, hkF]
          · simp [s5, s4, s3, s2, s1, hkB, hkT1, hkki, hkF]
  rw [hs5eq] at h5
  by_cases hz0 : z = 0
  · subst hz0
    have hB0 : (s5 .B).head?.isNone = true := by simp [s5, natStack_zero]
    have h6 : (StackProg.branch (fun h => (h .B).isNone) (pushProg .fail symOne) noop).Exec s5
        (Function.update s5 .fail (symOne :: s5 .fail)) (1 + 1) :=
      StackProg.Exec.branchTrue hB0 ((CookPvsNP.stack_basic_macros .fail s5).1 symOne)
    have hu : Function.update s5 .fail (symOne :: s5 .fail) =
        Function.update (Function.update (Function.update s .ki rest) .B (natStack (0 : ℤ).natAbs))
          .fail (symOne :: fail1) := by
      simp [s5, Function.update_idem]
    rw [hu] at h6
    exact ⟨symOne :: fail1, _, by simp, StackProg.Exec.seq h1exec (StackProg.Exec.seq h2
      (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 (StackProg.Exec.seq h5 h6))))⟩
  · have hnatNe : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz0
    have hBne : (s5 .B).head?.isNone = false := by
      simp only [s5, Function.update_of_ne (show K.B ≠ K.fail by decide), Function.update_self]
      cases hn : natStack z.natAbs with
      | nil => exact absurd (natStack_eq_nil_iff.mp hn) hnatNe
      | cons _ _ => rfl
    have h6 : (StackProg.branch (fun h => (h .B).isNone) (pushProg .fail symOne) noop).Exec s5 s5 (1 + 1) :=
      StackProg.Exec.branchFalse hBne (exec_noop s5)
    have hiff : fail1.head?.isSome ↔ (s .fail).head?.isSome ∨ ¬ (0 < z) := by
      rw [hfail1]
      constructor
      · intro h; exact h.elim Or.inl (fun h => Or.inr (by omega))
      · intro h; exact h.elim Or.inl (fun h => Or.inr (by omega))
    exact ⟨fail1, _, hiff, StackProg.Exec.seq h1exec (StackProg.Exec.seq h2
      (StackProg.Exec.seq h3 (StackProg.Exec.seq h4 (StackProg.Exec.seq h5 h6))))⟩

def PairsCanon : List ℤ → Prop
  | [] => True
  | [_] => False
  | num :: den :: tail => (0 < den ∧ Int.gcd num den = 1) ∧ PairsCanon tail

lemma exec_pairsLoop_enc (tailSym : List Sym) (d : List Bool) (htail : tailSym = symHash :: d.map (some ∘ Sum.inr)) :
    ∀ (rest : List ℤ), Even rest.length →
    ∀ (s : K → List Sym),
      s .ki = encIntsSym rest ++ tailSym →
      s .A = [] → s .B = [] → s .T1 = [] → s .T2 = [] → s .C = [] →
      ∃ (s' : K → List Sym) (t : ℕ),
        pairsLoopProg.Exec s s' t ∧
        s' .ko = s .ko ∧
        ((s' .fail).head?.isSome ↔ (s .fail).head?.isSome ∨ ¬ PairsCanon rest) := by
  intro rest
  match rest with
  | [] =>
    intro _ s hki _ _ _ _ _
    have hstop : testPairs (fun k => (s k).head?) = false := by
      simp [testPairs, hki, encIntsSym_nil, htail]
    exact ⟨s, 1, StackProg.Exec.loopFalse hstop, rfl, by simp [PairsCanon]⟩
  | [x] =>
    intro hev
    exfalso
    rcases hev with ⟨m, hm⟩
    simp at hm; omega
  | num :: den :: tl =>
    intro hev s hki hA hB hT1 hT2 hC
    have hev' : Even tl.length := by
      rcases hev with ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      simp at hm; omega
    have hki' : s .ki = encIntSym num ++ (encIntSym den ++ (encIntsSym tl ++ tailSym)) := by
      rw [hki, encIntsSym_cons, encIntsSym_cons]; simp [List.append_assoc]
    have htp : testPairs (fun k => (s k).head?) = true := by
      unfold testPairs
      dsimp only
      rw [hki', encIntSym_eq]
      by_cases hneg : num < 0
      · simp [hneg]
      · simp only [hneg, ↓reduceIte, List.nil_append, List.append_assoc, List.singleton_append]
        cases hnb : Nat.bits num.natAbs with
        | nil => simp [natStack, hnb]
        | cons b ts => cases b <;> simp [natStack, hnb]
    obtain ⟨t1, h1⟩ := exec_readNum_enc num (encIntSym den ++ (encIntsSym tl ++ tailSym)) s hki' hA hT1
    set s1 := Function.update (Function.update s .ki (encIntSym den ++ (encIntsSym tl ++ tailSym)))
      .A (natStack num.natAbs)
    obtain ⟨fail2, t2, hfail2, h2⟩ := exec_readDen_enc den (encIntsSym tl ++ tailSym) s1
      (by simp [s1]) (by simp [s1, hB]) (by simp [s1, hT1])
    set s2 := Function.update (Function.update (Function.update s1 .ki (encIntsSym tl ++ tailSym))
      .B (natStack den.natAbs)) .fail fail2
    obtain ⟨t3, _, h3⟩ := exec_gcdCheck s2 num.natAbs den.natAbs
      (by simp [s2, s1]) (by simp [s2]) (by simp [s2, s1, hT1]) (by simp [s2, s1, hT2])
      (by simp [s2, s1, hC])
    set s3 := Function.update (Function.update
      (Function.update s2 .fail (if Nat.gcd num.natAbs den.natAbs = 1 then s2 .fail else symOne :: s2 .fail))
      .A []) .B []
    have hbody := StackProg.Exec.seq h1 (StackProg.Exec.seq h2 h3)
    obtain ⟨s', trec, hrec, hko, hfailRec⟩ := exec_pairsLoop_enc tailSym d htail tl hev' s3
      (by simp [s3, s2]) (by simp [s3]) (by simp [s3])
      (by simp [s3, s2, s1, hT1]) (by simp [s3, s2, s1, hT2]) (by simp [s3, s2, s1, hC])
    have hs3ko : s3 .ko = s .ko := by simp [s3, s2, s1]
    have hs3fail : (s3 .fail).head?.isSome ↔
        (s .fail).head?.isSome ∨ ¬ (0 < den ∧ Int.gcd num den = 1) := by
      have hs1fail : s1 .fail = s .fail := by simp [s1]
      have hs2fail : s2 .fail = fail2 := by simp [s2]
      have hs3f : s3 .fail = if Nat.gcd num.natAbs den.natAbs = 1 then fail2 else symOne :: fail2 := by
        simp [s3, hs2fail]
      rw [hs3f]
      have hgcdEq : Int.gcd num den = Nat.gcd num.natAbs den.natAbs := rfl
      rw [hgcdEq]
      by_cases hg : Nat.gcd num.natAbs den.natAbs = 1
      · simp only [hg, ↓reduceIte, and_true]
        rwa [hs1fail] at hfail2
      · simp [hg]
    refine ⟨s', _, StackProg.Exec.loopTrue htp hbody hrec, hko.trans hs3ko, ?_⟩
    rw [hfailRec, hs3fail]
    simp only [PairsCanon, not_and_or, or_assoc]

lemma canonOK_iff_pairsCanon (c0 : ℤ) (rest : List ℤ) (M : ℕ)
    (hlen : rest.length = 2 * M) (hM : M = numRats ((c0 :: rest).getD 0 0).toNat) :
    CanonOK (c0 :: rest) ↔ PairsCanon rest := by
  have aux : ∀ (k : ℕ) (r : List ℤ), r.length = 2 * k →
      ((∀ t < k, 0 < r.getD (2 * t + 1) 0 ∧ Int.gcd (r.getD (2 * t) 0) (r.getD (2 * t + 1) 0) = 1) ↔
        PairsCanon r) := by
    intro k
    induction k with
    | zero =>
      intro r hr
      have hr0 : r = [] := List.eq_nil_of_length_eq_zero hr
      subst hr0
      simp [PairsCanon]
    | succ k ih =>
      intro r hr
      match r with
      | [] => simp at hr
      | [_] => simp at hr; omega
      | num :: den :: tl =>
        have htl : tl.length = 2 * k := by simp at hr; omega
        rw [PairsCanon, ← ih tl htl]
        constructor
        · intro h
          refine ⟨?_, ?_⟩
          · simpa using h 0 (Nat.zero_lt_succ k)
          · intro t ht
            have := h (t + 1) (Nat.succ_lt_succ ht)
            simpa [show 2 * (t + 1) = 2 * t + 2 by omega,
              show 2 * (t + 1) + 1 = 2 * t + 3 by omega] using this
        · rintro ⟨h0, hrest⟩ t ht
          cases t with
          | zero => simpa using h0
          | succ t =>
            have := hrest t (Nat.lt_of_succ_lt_succ ht)
            simpa [show 2 * (t + 1) = 2 * t + 2 by omega,
              show 2 * (t + 1) + 1 = 2 * t + 3 by omega] using this
  unfold CanonOK chkNum chkDen
  rw [← hM, ← aux M rest hlen]
  constructor <;> intro h t ht <;> simpa using h t ht

open Classical in
lemma mainProg_valid (c : List ℤ) (d : List Bool) (hshape : ShapeOK c d) :
    ∃ (s : K → List Sym) (t : ℕ),
      mainProg.Exec (fun j => if j = .ki then chkWord c d else []) s t ∧
      s .ko = if CanonOK c then chkWord c d else [] := by
  set M := numRats (c.getD 0 0).toNat
  have hclen : c.length = 2 * M + 1 := hshape.2.1
  cases hc : c with
  | nil => rw [hc] at hclen; simp at hclen
  | cons c0 rest =>
    rw [hc] at hclen
    have hrestLen : rest.length = 2 * M := by simp at hclen; omega
    have hword : chkWord (c0 :: rest) d =
        encIntSym c0 ++ (encIntsSym rest ++ symHash :: d.map (some ∘ Sum.inr)) := by
      unfold chkWord
      change encIntsSym (c0 :: rest) ++ symHash :: d.map (some ∘ Sum.inr) = _
      rw [encIntsSym_cons, List.append_assoc]
    set s0 : K → List Sym := fun j => if j = .ki then chkWord (c0 :: rest) d else []
    have hcopy := CookPvsNP.stack_copy .ki .ko .T1 (by decide) (by decide) (by decide) s0 (by simp [s0])
    set s1 := Function.update s0 .ko (s0 .ki ++ s0 .ko)
    have hs1ki : s1 .ki = encIntSym c0 ++ (encIntsSym rest ++ symHash :: d.map (some ∘ Sum.inr)) := by
      simp [s1, s0, hword]
    have hs1ko : s1 .ko = chkWord (c0 :: rest) d := by simp [s1, s0]
    obtain ⟨tsk, hsk⟩ := exec_skipFirst_encInt c0 (encIntsSym rest ++ symHash :: d.map (some ∘ Sum.inr)) s1 hs1ki
    set s2 := Function.update s1 .ki (encIntsSym rest ++ symHash :: d.map (some ∘ Sum.inr))
    obtain ⟨s3, tlp, hlp, hs3ko, hs3fail⟩ :=
      exec_pairsLoop_enc (symHash :: d.map (some ∘ Sum.inr)) d rfl rest ⟨M, by omega⟩ s2
        (by simp [s2]) (by simp [s2, s1, s0]) (by simp [s2, s1, s0])
        (by simp [s2, s1, s0]) (by simp [s2, s1, s0]) (by simp [s2, s1, s0])
    have hs3ko' : s3 .ko = chkWord (c0 :: rest) d := by rw [hs3ko]; simp [s2, hs1ko]
    have hs2fail : (s2 .fail).head?.isSome = false := by simp [s2, s1, s0]
    have hcanonIff : CanonOK (c0 :: rest) ↔ PairsCanon rest :=
      canonOK_iff_pairsCanon c0 rest M hrestLen (by simp [M, hc])
    have hfailIff : (s3 .fail).head?.isSome = true ↔ ¬ CanonOK (c0 :: rest) := by
      rw [hs3fail, hs2fail, hcanonIff]
      simp
    by_cases hcan : CanonOK (c0 :: rest)
    · have hf : (s3 .fail).head?.isSome = false := by
        cases h : (s3 .fail).head?.isSome
        · rfl
        · exact absurd hcan (hfailIff.mp h)
      have hfin : finalizeProg.Exec s3 s3 (1 + 1) :=
        StackProg.Exec.branchFalse hf (exec_noop s3)
      refine ⟨s3, _, StackProg.Exec.seq hcopy (StackProg.Exec.seq hsk (StackProg.Exec.seq hlp hfin)), ?_⟩
      simp [hcan, hs3ko']
    · have hf : (s3 .fail).head?.isSome = true := hfailIff.mpr hcan
      have hclr := (CookPvsNP.stack_basic_macros .ko s3).2.2
      have hfin : finalizeProg.Exec s3 (Function.update s3 .ko []) (1 + (3 * (s3 .ko).length + 1)) :=
        StackProg.Exec.branchTrue hf hclr
      refine ⟨Function.update s3 .ko [], _,
        StackProg.Exec.seq hcopy (StackProg.Exec.seq hsk (StackProg.Exec.seq hlp hfin)), ?_⟩
      simp [hcan]

end CanonFilter

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

open Classical in
theorem solution :
    ∃ g : List (Option (BSym ⊕ Bool)) → List (Option (BSym ⊕ Bool)),
      PolyTimeComputable g ∧ g [] = [] ∧
        ∀ c d, ShapeOK c d → g (chkWord c d) = if CanonOK c then chkWord c d else [] := by
  let g : List (Option (BSym ⊕ Bool)) → List (Option (BSym ⊕ Bool)) :=
    fun w => (Classical.choose (CanonFilter.mainProg_terminates w)) .ko
  obtain ⟨k, hk⟩ := CookPvsNP.polynomial_absorb 296 3 100
  have hpoly : PolyTimeComputable g := by
    apply CookPvsNP.stack_program_polytime CanonFilter.mainProg .ki .ko g k
    intro w
    set s := Classical.choose (CanonFilter.mainProg_terminates w)
    obtain ⟨t, ht, hex⟩ := Classical.choose_spec (CanonFilter.mainProg_terminates w)
    refine ⟨s, t, ?_, hex, rfl⟩
    have h1 : 96 * (w.length + 1) ^ 3 + 100 * (w.length + 1) ^ 2 + 100 * (w.length + 1) + 100 ≤
        296 * (w.length + 1) ^ 3 + 100 := by
      have hp1 : (w.length + 1) ^ 2 ≤ (w.length + 1) ^ 3 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hp2 : w.length + 1 ≤ (w.length + 1) ^ 3 := by
        calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
        _ ≤ (w.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact le_trans ht (le_trans h1 (hk w.length))
  have hnil : g [] = [] := by
    obtain ⟨t1, _, hex1⟩ := Classical.choose_spec (CanonFilter.mainProg_terminates [])
    obtain ⟨s2, t2, hex2, hko2⟩ := CanonFilter.mainProg_nil
    obtain ⟨hs, _⟩ := CanonFilter.exec_det hex1 hex2
    change (Classical.choose (CanonFilter.mainProg_terminates [])) .ko = []
    rw [hs, hko2]
  have hvalid : ∀ c d, ShapeOK c d → g (chkWord c d) = if CanonOK c then chkWord c d else [] := by
    intro c d hshape
    obtain ⟨t1, _, hex1⟩ := Classical.choose_spec (CanonFilter.mainProg_terminates (chkWord c d))
    obtain ⟨s2, t2, hex2, hko2⟩ := CanonFilter.mainProg_valid c d hshape
    obtain ⟨hs, _⟩ := CanonFilter.exec_det hex1 hex2
    change (Classical.choose (CanonFilter.mainProg_terminates (chkWord c d))) .ko = _
    rw [hs, hko2]
  exact ⟨g, hpoly, hnil, hvalid⟩
