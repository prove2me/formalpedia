-- Prove2me | solution 1 for MultiPurchase.Hardness.shape_filter_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:27:01.270874+00:00
-- url     : https://prove2.me/submissions/a48fedee-3a6f-4305-9c80-991d1e03fe18

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model
import Definitions.Def_MultiPurchase_Hardness_Checker
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_CookPvsNP_StackCompare
import Definitions.Def_CookPvsNP_StackRepeat
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_polynomial_absorb

set_option autoImplicit false

namespace MPShape

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness

/-! ## Alphabet, symbols, and stack keys -/

abbrev A := Option (BSym ⊕ Bool)

def ι1 (b : BSym) : A := some (Sum.inl b)
def ι2 (b : Bool) : A := some (Sum.inr b)
def dg (b : Bool) : BSym := if b then BSym.one else BSym.zero
def mkA : A := none

/-- Sign tag for an integer: `ι1 .one` for `> 0`, `ι1 .zero` for `= 0`, `ι1 .minus` for `< 0`. -/
def sgnSym (z : ℤ) : A :=
  if 0 < z then ι1 .one else if z = 0 then ι1 .zero else ι1 .minus

lemma sgnSym_eq_one_iff (z : ℤ) : sgnSym z = ι1 .one ↔ 0 < z := by
  unfold sgnSym
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · constructor
    · intro h; simp [ι1] at h
    · intro h; omega
  · constructor
    · intro h; simp [ι1] at h
    · intro h; omega

lemma sgnSym_ne_minus_iff (z : ℤ) : sgnSym z ≠ ι1 .minus ↔ 0 ≤ z := by
  unfold sgnSym
  split_ifs with h1 h2
  · constructor
    · intro _; omega
    · intro _; simp [ι1]
  · constructor
    · intro _; omega
    · intro _; simp [ι1]
  · constructor
    · intro h; exact absurd rfl h
    · intro h; omega

lemma chkWord_eq (c : List ℤ) (d : List Bool) :
    chkWord c d = (encInts c).map ι1 ++ none :: d.map ι2 := rfl

lemma encInts_nil : encInts [] = [] := rfl
lemma encInts_cons (z : ℤ) (c : List ℤ) : encInts (z :: c) = encInt z ++ encInts c := by
  simp [encInts]

lemma encNat_dg (k : ℕ) : encNat k = (Nat.bits k).map dg ++ [BSym.sep] := rfl

lemma encInt_nat (k : ℕ) : encInt (k : ℤ) = (Nat.bits k).map dg ++ [BSym.sep] := by
  have h : ¬ ((k : ℤ) < 0) := by omega
  simp only [encInt, if_neg h, Int.natAbs_natCast, List.nil_append]; rfl

lemma encInt_nonneg (z : ℤ) (hz : 0 ≤ z) :
    encInt z = (Nat.bits z.natAbs).map dg ++ [BSym.sep] := by
  have h : ¬ (z < 0) := by omega
  simp only [encInt, if_neg h, List.nil_append]; rfl

lemma encInt_neg (k : ℕ) (hk : k ≠ 0) :
    encInt (-(k : ℤ)) = BSym.minus :: ((Nat.bits k).map dg ++ [BSym.sep]) := by
  have h : (-(k : ℤ)) < 0 := by omega
  simp only [encInt, if_pos h, Int.natAbs_neg, Int.natAbs_natCast, List.singleton_append]; rfl

lemma encInt_neg' (z : ℤ) (hz : z < 0) :
    encInt z = BSym.minus :: ((Nat.bits z.natAbs).map dg ++ [BSym.sep]) := by
  simp only [encInt, if_pos hz, List.singleton_append]; rfl

/-! ## Injectivity of `chkWord` -/

lemma split_at {α : Type} (x : α) : ∀ (l₁ l₂ r₁ r₂ : List α), x ∉ l₁ → x ∉ l₂ →
    l₁ ++ x :: r₁ = l₂ ++ x :: r₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ _ h₂ h
    cases l₂ with
    | nil => simpa using h
    | cons b l₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | cons a l₁ ih =>
    intro l₂ r₁ r₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₁
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨e1, e2⟩ := ih l₂ r₁ r₂ (fun hm => h₁ (List.mem_cons_of_mem _ hm))
        (fun hm => h₂ (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [e1], e2⟩

lemma dg_inj : Function.Injective dg := by
  intro a b h; cases a <;> cases b <;> simp_all [dg]

lemma sep_not_mem_dg (L : List Bool) : BSym.sep ∉ L.map dg := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _ h; cases b <;> simp [dg] at h

lemma bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth, Nat.testBit_eq_inth, h]

lemma encNat_app (a b : ℕ) (s t : List BSym) (h : encNat a ++ s = encNat b ++ t) :
    a = b ∧ s = t := by
  rw [encNat_dg, encNat_dg] at h
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  obtain ⟨e1, e2⟩ := split_at BSym.sep _ _ _ _ (sep_not_mem_dg _) (sep_not_mem_dg _) h
  exact ⟨bits_inj (List.map_injective_iff.mpr dg_inj e1), e2⟩

lemma encNat_head (k : ℕ) (s : List BSym) :
    ∃ x l, encNat k ++ s = x :: l ∧ x ≠ BSym.minus := by
  rw [encNat_dg]
  cases hb : Nat.bits k with
  | nil => exact ⟨BSym.sep, s, by simp, by decide⟩
  | cons b L => exact ⟨dg b, L.map dg ++ [BSym.sep] ++ s, rfl, by cases b <;> simp [dg]⟩

lemma encInt_app (a b : ℤ) (s t : List BSym) (h : encInt a ++ s = encInt b ++ t) :
    a = b ∧ s = t := by
  unfold encInt at h
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp only [ha, hb, if_true, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
    obtain ⟨e1, e2⟩ := encNat_app _ _ _ _ h
    exact ⟨by omega, e2⟩
  · simp only [ha, hb, if_true, if_false, List.cons_append, List.nil_append] at h
    obtain ⟨x, l, hx, hne⟩ := encNat_head b.natAbs t
    rw [hx] at h
    exact absurd (List.cons.inj h).1.symm hne
  · simp only [ha, hb, if_true, if_false, List.cons_append, List.nil_append] at h
    obtain ⟨x, l, hx, hne⟩ := encNat_head a.natAbs s
    rw [hx] at h
    exact absurd (List.cons.inj h).1 hne
  · simp only [ha, hb, if_false, List.nil_append] at h
    obtain ⟨e1, e2⟩ := encNat_app _ _ _ _ h
    exact ⟨by omega, e2⟩

lemma encInt_ne_nil (a : ℤ) : encInt a ≠ [] := by
  simp [encInt, encNat]

lemma encInts_inj : ∀ (c c' : List ℤ), encInts c = encInts c' → c = c' := by
  intro c
  induction c with
  | nil =>
    intro c' h
    cases c' with
    | nil => rfl
    | cons b l =>
      rw [encInts_cons, encInts_nil] at h
      exact absurd h.symm (by simp [encInt_ne_nil])
  | cons a l ih =>
    intro c' h
    cases c' with
    | nil =>
      rw [encInts_cons, encInts_nil] at h
      exact absurd h (by simp [encInt_ne_nil])
    | cons b l' =>
      rw [encInts_cons, encInts_cons] at h
      obtain ⟨e1, e2⟩ := encInt_app _ _ _ _ h
      rw [e1, ih l' e2]

lemma chkWord_inj (c c' : List ℤ) (d d' : List Bool) (h : chkWord c d = chkWord c' d') :
    c = c' ∧ d = d' := by
  unfold chkWord at h
  have hn : ∀ (w : List BSym), (none : A) ∉ w.map (some ∘ Sum.inl) := by
    intro w; simp
  obtain ⟨e1, e2⟩ := split_at _ _ _ _ _ (hn _) (hn _) h
  have i1 : Function.Injective (some ∘ Sum.inl : BSym → A) := by
    intro x y hxy; simpa using hxy
  have i2 : Function.Injective (some ∘ Sum.inr : Bool → A) := by
    intro x y hxy; simpa using hxy
  exact ⟨encInts_inj _ _ (List.map_injective_iff.mpr i1 e1), List.map_injective_iff.mpr i2 e2⟩

/-! ## Arithmetic and decomposition lemmas for `ShapeOK` -/

lemma two_mul_numRats_add_one (n : ℕ) : 2 * numRats n + 1 = n * n + 3 * n + 5 := by
  unfold numRats
  cases n with
  | zero => simp
  | succ k =>
    have hev : Even (k * (k + 1)) := Nat.even_mul_succ_self k
    have hmul : (k + 1) * k / 2 * 2 = (k + 1) * k := by
      rw [mul_comm (k + 1) k]
      exact Nat.div_two_mul_two_of_even hev
    simp only [Nat.add_sub_cancel]
    nlinarith

lemma numRats_ge_two_add (n : ℕ) : n + 2 ≤ numRats n := by
  unfold numRats; omega

lemma len_encInts (c : List ℤ) : c.length ≤ (encInts c).length := by
  induction c with
  | nil => simp
  | cons z c ih =>
    rw [encInts_cons, List.length_append, List.length_cons]
    have : 1 ≤ (encInt z).length := by
      unfold encInt encNat; simp; omega
    omega

lemma bits_len_le_encInt (z : ℤ) : (Nat.bits z.natAbs).length ≤ (encInt z).length := by
  unfold encInt encNat; simp; omega

lemma list_decomp (c : List ℤ) (n : ℕ) (hlen : c.length = 2 * numRats n + 1) :
    ∃ (z v0n v0d kn kd : ℤ) (revL wtL : List ℤ),
      c = z :: (revL ++ wtL ++ [v0n, v0d, kn, kd]) ∧
      revL.length = 2 * n ∧
      wtL.length = 2 * (numRats n - 2 - n) ∧
      z = c.getD 0 0 ∧
      v0n = chkNum c (numRats n - 2) ∧
      (∀ i < n, revL.getD (2 * i) 0 = chkNum c i) ∧
      (∀ j < numRats n - 2 - n, wtL.getD (2 * j) 0 = chkNum c (n + j)) := by
  have hge := numRats_ge_two_add n
  rcases c with _ | ⟨z, tail⟩
  · simp at hlen
  · have htail : tail.length = 2 * numRats n := by simp at hlen; omega
    set revL := tail.take (2 * n)
    set rest1 := tail.drop (2 * n)
    set wtL := rest1.take (2 * (numRats n - 2 - n))
    set last4 := rest1.drop (2 * (numRats n - 2 - n))
    have hrevL : revL.length = 2 * n := by simp [revL, htail]; omega
    have hrest1 : rest1.length = 2 * (numRats n - n) := by simp [rest1, htail]; omega
    have hwtL : wtL.length = 2 * (numRats n - 2 - n) := by simp [wtL, hrest1]; omega
    have hlast4 : last4.length = 4 := by simp [last4, hrest1]; omega
    have hsp1 : revL ++ rest1 = tail := List.take_append_drop (2 * n) tail
    have hsp2 : wtL ++ last4 = rest1 := List.take_append_drop (2 * (numRats n - 2 - n)) rest1
    have hsplit : tail = revL ++ wtL ++ last4 := by
      rw [← hsp1, ← hsp2, List.append_assoc]
    rcases hl4 : last4 with _ | ⟨v0n, _ | ⟨v0d, _ | ⟨kn, _ | ⟨kd, _ | ⟨_, _⟩⟩⟩⟩⟩
    · rw [hl4] at hlast4; simp at hlast4
    · rw [hl4] at hlast4; simp at hlast4
    · rw [hl4] at hlast4; simp at hlast4
    · rw [hl4] at hlast4; simp at hlast4
    · have hteq : tail = revL ++ wtL ++ [v0n, v0d, kn, kd] := by rw [hsplit, hl4]
      refine ⟨z, v0n, v0d, kn, kd, revL, wtL, by rw [hteq], hrevL, hwtL, by simp, ?_, ?_, ?_⟩
      · unfold chkNum
        rw [List.getD_cons_succ, hteq]
        rw [List.getD_append_right _ _ _ _ (by simp [hrevL, hwtL]; omega)]
        simp [hrevL, hwtL, show 2 * (numRats n - 2) - (2 * n + 2 * (numRats n - 2 - n)) = 0 by omega]
      · intro i hi
        unfold chkNum
        rw [List.getD_cons_succ, hteq, List.append_assoc]
        rw [List.getD_append _ _ _ _ (by omega)]
      · intro j hj
        unfold chkNum
        rw [List.getD_cons_succ, hteq]
        rw [List.getD_append _ _ _ _ (by simp [hrevL, hwtL]; omega)]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [hrevL, show 2 * (n + j) - 2 * n = 2 * j by omega]
    · rw [hl4] at hlast4; simp at hlast4

lemma shapeOK_iff (c : List ℤ) (d : List Bool) :
    ShapeOK c d ↔
      c.length = d.length * d.length + 3 * d.length + 5 ∧
      0 ≤ c.getD 0 0 ∧
      (c.getD 0 0).natAbs = d.length ∧
      0 < chkNum c (numRats d.length - 2) ∧
      (∀ i < d.length, 0 < chkNum c i) ∧
      (∀ j < numRats d.length - 2 - d.length, 0 ≤ chkNum c (d.length + j)) := by
  unfold ShapeOK
  constructor
  · rintro ⟨h0, hlen, hd, hpos, hnn, hv0⟩
    have hto : (c.getD 0 0).toNat = d.length := hd.symm
    have hnat : (c.getD 0 0).natAbs = d.length := by omega
    rw [hto, two_mul_numRats_add_one] at hlen
    rw [hto] at hpos hnn hv0
    refine ⟨hlen, h0, hnat, hv0, hpos, ?_⟩
    intro j hj
    exact hnn (d.length + j) (by omega) (by omega)
  · rintro ⟨hlen, h0, hnat, hv0, hpos, hnn⟩
    have hto : (c.getD 0 0).toNat = d.length := by omega
    refine ⟨h0, ?_, hto.symm, ?_, ?_, ?_⟩
    · rw [hto, two_mul_numRats_add_one]; exact hlen
    · rw [hto]; exact hpos
    · rw [hto]
      intro t ht1 ht2
      have := hnn (t - d.length) (by omega)
      rwa [show d.length + (t - d.length) = t by omega] at this
    · rw [hto]; exact hv0

/-! ## Generic Mealy scan -/

section Scan
variable {K' A' : Type} [DecidableEq K']

def scanAct (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A')
    (h : K' → Option A') (k : K') : StackAct A' :=
  match h ki with
  | none => .keep
  | some a =>
    if k = ki then .pop else if k = st then .push (δ (h st) a)
    else match out k (h st) a with
      | some b => .push b
      | none => .keep

def scanProg (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') :
    StackProg K' A' :=
  .loop (fun h => (h ki).isSome) (.act (scanAct ki st δ out))

def scanStep (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A')
    (s : K' → List A') (a : A') : K' → List A' := fun k =>
  if k = ki then (s ki).tail else if k = st then δ (s st).head? a :: s st
  else (out k (s st).head? a).toList ++ s k

def scanRun (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') :
    List A' → (K' → List A') → (K' → List A')
  | [], s => s
  | a :: l, s => scanRun ki st δ out l (scanStep ki st δ out s a)

lemma applyAct_scan (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A')
    (s : K' → List A') (a : A') (l : List A') (hs : s ki = a :: l) :
    StackProg.applyAct (scanAct ki st δ out) s = scanStep ki st δ out s a := by
  funext k
  simp only [StackProg.applyAct, scanAct, scanStep, hs, List.head?_cons]
  by_cases h1 : k = ki
  · subst h1; simp [StackAct.apply, hs]
  · by_cases h2 : k = st
    · subst h2; simp [h1, StackAct.apply]
    · simp only [h1, h2, if_false]
      cases out k (s st).head? a <;> simp [StackAct.apply]

lemma exec_scan (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') :
    ∀ (l : List A') (s : K' → List A'), s ki = l →
      (scanProg ki st δ out).Exec s (scanRun ki st δ out l s) (3 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
    intro s hs
    exact StackProg.Exec.loopFalse (by simp [hs])
  | cons a l ih =>
    intro s hs
    have h1 := StackProg.Exec.act (scanAct ki st δ out) s
    rw [applyAct_scan ki st δ out s a l hs] at h1
    have h2 := ih (scanStep ki st δ out s a) (by simp [scanStep, hs])
    have h3 := StackProg.Exec.loopTrue (test := fun h => (h ki).isSome) (by simp [hs]) h1 h2
    simp only [scanRun, List.length_cons]
    have e : 3 * (l.length + 1) + 1 = 1 + 1 + 1 + (3 * l.length + 1) := by ring
    rw [e]; exact h3

def runQ (δ : Option A' → A' → A') : Option A' → List A' → Option A'
  | q, [] => q
  | q, a :: l => runQ δ (some (δ q a)) l

def emitR (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') (k : K') :
    Option A' → List A' → List A'
  | _, [] => []
  | q, a :: l => emitR δ out k (some (δ q a)) l ++ (out k q a).toList

lemma runQ_append (δ : Option A' → A' → A') :
    ∀ (l₁ l₂ : List A') (q : Option A'), runQ δ q (l₁ ++ l₂) = runQ δ (runQ δ q l₁) l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ q; rfl
  | cons a l₁ ih => intro l₂ q; simp [runQ, ih]

omit [DecidableEq K'] in
lemma emitR_append (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') (k : K') :
    ∀ (l₁ l₂ : List A') (q : Option A'),
      emitR δ out k q (l₁ ++ l₂) =
        emitR δ out k (runQ δ q l₁) l₂ ++ emitR δ out k q l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ q; simp [emitR, runQ]
  | cons a l₁ ih =>
    intro l₂ q
    simp [emitR, runQ, ih, List.append_assoc]

lemma scanRun_ki (ki st : K') (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') :
    ∀ (l : List A') (s : K' → List A'), s ki = l → scanRun ki st δ out l s ki = [] := by
  intro l
  induction l with
  | nil => intro s hs; simpa [scanRun] using hs
  | cons a l ih => intro s hs; exact ih _ (by simp [scanStep, hs])

lemma scanRun_st (ki st : K') (hks : ki ≠ st) (δ : Option A' → A' → A')
    (out : K' → Option A' → A' → Option A') :
    ∀ (l : List A') (s : K' → List A'),
      (scanRun ki st δ out l s st).head? = runQ δ (s st).head? l := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, Ne.symm hks, runQ]

lemma scanRun_other (ki st : K') (hks : ki ≠ st) (δ : Option A' → A' → A')
    (out : K' → Option A' → A' → Option A') (k : K') (hk1 : k ≠ ki) (hk2 : k ≠ st) :
    ∀ (l : List A') (s : K' → List A'),
      scanRun ki st δ out l s k = emitR δ out k (s st).head? l ++ s k := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [scanRun, ih]
    simp [scanStep, hk1, hk2, Ne.symm hks, emitR]

omit [DecidableEq K'] in
lemma emitR_indep (δ : Option A' → A' → A') (out : K' → Option A' → A' → Option A') (k : K')
    (g : A' → Option A') (h : ∀ q a, out k q a = g a) :
    ∀ (l : List A') (q : Option A'), emitR δ out k q l = (l.filterMap g).reverse := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih =>
    intro q
    simp only [emitR, h, ih, List.filterMap_cons]
    cases g a <;> simp

end Scan

/-! ## The 6-state shape DFA for `chkWord c d` -/

inductive DS
  | S0 | M | Z | O | T | X
  deriving DecidableEq

open DS

def dstep : DS → A → DS
  | S0, some (.inl .minus) => M
  | S0, some (.inl .sep)   => S0
  | O,  some (.inl .sep)   => S0
  | S0, none               => T
  | S0, some (.inl .zero)  => Z
  | M,  some (.inl .zero)  => Z
  | Z,  some (.inl .zero)  => Z
  | O,  some (.inl .zero)  => Z
  | S0, some (.inl .one)   => O
  | M,  some (.inl .one)   => O
  | Z,  some (.inl .one)   => O
  | O,  some (.inl .one)   => O
  | T,  some (.inr _)      => T
  | _,  _                  => X

def runD (q : DS) (l : List A) : DS := l.foldl dstep q

@[simp] lemma runD_nil (q : DS) : runD q [] = q := rfl
@[simp] lemma runD_cons (q : DS) (a : A) (l : List A) : runD q (a :: l) = runD (dstep q a) l := rfl
lemma runD_append (q : DS) (l l' : List A) : runD q (l ++ l') = runD (runD q l) l' := by
  simp [runD, List.foldl_append]

@[simp] lemma runD_X : ∀ l : List A, runD X l = X := by
  intro l; induction l with
  | nil => rfl
  | cons a l ih => rw [runD_cons]; cases a <;> exact ih

lemma canon_bits : ∀ bs : List Bool, (bs = [] ∨ bs.getLast? = some true) → ∃ k, Nat.bits k = bs := by
  intro bs
  induction bs with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons b bs ih =>
    intro h
    rcases bs with _ | ⟨b', bs'⟩
    · have hb : b = true := by simpa using h
      subst hb
      exact ⟨1, by
        have := Nat.bits_append_bit 0 true (by simp)
        simp⟩
    · have hl : (b' :: bs').getLast? = some true := by
        rcases h with h | h
        · simp at h
        · rw [List.getLast?_cons_cons] at h; exact h
      obtain ⟨k, hk⟩ := ih (Or.inr hl)
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      refine ⟨Nat.bit b k, ?_⟩
      rw [Nat.bits_append_bit _ _ (fun h => absurd h hk0), hk]

lemma dpart_sound : ∀ (l : List A), runD T l = T → ∃ d : List Bool, l = d.map ι2 := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a l ih =>
    intro h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · simp [dstep] at h
    · cases b <;> simp [dstep] at h
    · obtain ⟨d, hd⟩ := ih (by simpa [dstep] using h)
      exact ⟨b :: d, by simp [hd, ι2]⟩

lemma dpart_complete : ∀ (d : List Bool), runD T (d.map ι2) = T := by
  intro d
  induction d with
  | nil => rfl
  | cons b d ih => simpa [ι2, dstep] using ih

lemma cpart_digits : ∀ (l : List A) (q : DS), (q = M ∨ q = Z ∨ q = O) → runD q l = T →
    ∃ (bs : List Bool) (rest : List A), l = bs.map (ι1 ∘ dg) ++ ι1 .sep :: rest ∧
      (bs.getLast? = some true ∨ (bs = [] ∧ q = O)) ∧ runD S0 rest = T := by
  intro l
  induction l with
  | nil => intro q hq h; rcases hq with rfl | rfl | rfl <;> simp at h
  | cons a l ih =>
    intro q hq h
    rw [runD_cons] at h
    rcases a with _ | (b | b)
    · rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
    · cases b with
      | zero =>
        have hd : dstep q (some (.inl .zero)) = Z := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih Z (Or.inr (Or.inl rfl)) h
        refine ⟨false :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨_, h2⟩
        · rw [List.getLast?_cons]; simp [h2]
        · exact absurd h2 (by decide)
      | one =>
        have hd : dstep q (some (.inl .one)) = O := by rcases hq with rfl | rfl | rfl <;> rfl
        rw [hd] at h
        obtain ⟨bs, rest, h1, h2, h3⟩ := ih O (Or.inr (Or.inr rfl)) h
        refine ⟨true :: bs, rest, by simp [h1, ι1, dg], Or.inl ?_, h3⟩
        rcases h2 with h2 | ⟨h2, _⟩
        · rw [List.getLast?_cons]; simp [h2]
        · subst h2; simp
      | minus => rcases hq with rfl | rfl | rfl <;> simp [dstep] at h
      | sep =>
        rcases hq with rfl | rfl | rfl
        · simp [dstep] at h
        · simp [dstep] at h
        · exact ⟨[], l, rfl, Or.inr ⟨rfl, rfl⟩, by simpa [dstep] using h⟩
    · rcases hq with rfl | rfl | rfl <;> simp [dstep] at h

lemma cpart_sound : ∀ (L : ℕ) (l : List A), l.length ≤ L → runD S0 l = T →
    ∃ (c : List ℤ) (d : List Bool), l = chkWord c d := by
  intro L
  induction L with
  | zero =>
    intro l hl h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp at h
  | succ L ih =>
    intro l hl h
    rcases l with _ | ⟨a, l⟩
    · simp at h
    rw [runD_cons] at h
    simp only [List.length_cons] at hl
    rcases a with _ | (b | b)
    · obtain ⟨d, hd⟩ := dpart_sound l (by simpa [dstep] using h)
      exact ⟨[], d, by simp [chkWord_eq, hd, encInts]⟩
    · cases b with
      | sep =>
        obtain ⟨c, d, hcd⟩ := ih l (by omega) (by simpa [dstep] using h)
        exact ⟨0 :: c, d, by simp [hcd, chkWord_eq, encInts_cons, encInt, encNat, ι1]⟩
      | minus =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l M (Or.inl rfl) (by simpa [dstep] using h)
        have hl2 : bs.getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · exact h2
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ (Or.inr hl2)
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; subst hk; simp at hl2
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨-(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [chkWord_eq, encInts_cons, encInt_neg k hk0, hk]
        simp [ι1]
      | zero =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l Z (Or.inr (Or.inl rfl))
          (by simpa [dstep] using h)
        have hc : (false :: bs) = [] ∨ (false :: bs).getLast? = some true := by
          rcases h2 with h2 | ⟨_, h2⟩
          · right; rw [List.getLast?_cons]; simp [h2]
          · exact absurd h2 (by decide)
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [chkWord_eq, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
      | one =>
        obtain ⟨bs, rest, h1, h2, h3⟩ := cpart_digits l O (Or.inr (Or.inr rfl))
          (by simpa [dstep] using h)
        have hc : (true :: bs) = [] ∨ (true :: bs).getLast? = some true := by
          right
          rcases h2 with h2 | ⟨h2, _⟩
          · rw [List.getLast?_cons]; simp [h2]
          · subst h2; simp
        obtain ⟨k, hk⟩ := canon_bits _ hc
        have hlen : rest.length ≤ L := by
          have := congrArg List.length h1; simp at this; omega
        obtain ⟨c, d, hcd⟩ := ih rest hlen h3
        refine ⟨(k : ℤ) :: c, d, ?_⟩
        rw [h1, hcd]
        simp only [chkWord_eq, encInts_cons, encInt_nat k, hk]
        simp [ι1, dg]
    · simp [dstep] at h

lemma cpart_bits : ∀ (k : ℕ) (q : DS), (q = S0 ∨ q = M ∨ q = Z ∨ q = O) → k ≠ 0 →
    runD q ((Nat.bits k).map (ι1 ∘ dg)) = O := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro q _ h; exact absurd rfl h
  | bit b n hn ih =>
    intro q hq _
    rw [Nat.bits_append_bit _ _ hn, List.map_cons, runD_cons]
    by_cases h0 : n = 0
    · subst h0
      have hb := hn rfl; subst hb
      rcases hq with rfl | rfl | rfl | rfl <;> rfl
    · apply ih _ _ h0
      rcases hq with rfl | rfl | rfl | rfl <;> cases b <;> simp [dstep, ι1, dg]

lemma cpart_int (z : ℤ) : runD S0 ((encInt z).map ι1) = S0 := by
  by_cases hz : z = 0
  · subst hz; simp [encInt, encNat, ι1, dstep]
  · by_cases hlt : z < 0
    · have hk : z.natAbs ≠ 0 := by omega
      rw [encInt_neg' z hlt, List.map_cons, runD_cons]
      change runD M (((Nat.bits z.natAbs).map dg ++ [BSym.sep]).map ι1) = S0
      rw [List.map_append, runD_append, List.map_map,
        cpart_bits z.natAbs M (Or.inr (Or.inl rfl)) hk]
      rfl
    · have hk : z.natAbs ≠ 0 := by omega
      rw [encInt_nonneg z (by omega), List.map_append, runD_append, List.map_map,
        cpart_bits z.natAbs S0 (Or.inl rfl) hk]
      rfl

lemma cpart_ints : ∀ (c : List ℤ), runD S0 ((encInts c).map ι1) = S0 := by
  intro c
  induction c with
  | nil => rfl
  | cons z c ih =>
    rw [encInts_cons, List.map_append, runD_append, cpart_int z, ih]

lemma cpart_complete (c : List ℤ) (d : List Bool) : runD S0 (chkWord c d) = T := by
  rw [chkWord_eq, runD_append, cpart_ints c, runD_cons]
  exact dpart_complete d

theorem runD_iff (u : List A) : runD S0 u = T ↔ ∃ (c : List ℤ) (d : List Bool), u = chkWord c d :=
  ⟨cpart_sound u.length u le_rfl, fun ⟨c, d, h⟩ => h ▸ cpart_complete c d⟩

/-! ## Stack keys, DFA state encoding, and Phase 0 scan -/

inductive K
  | ki | ko | sc | st | dlen | sgnR | sgn | W | U | T | C | H | P | Bd
  deriving DecidableEq

instance : Fintype K := Fintype.ofList
  [K.ki, K.ko, K.sc, K.st, K.dlen, K.sgnR, K.sgn, K.W, K.U, K.T, K.C, K.H, K.P, K.Bd]
  (by intro x; cases x <;> simp)

abbrev SP := StackProg K A

def dsA : DS → A
  | S0 => ι1 .sep
  | M  => ι1 .minus
  | Z  => ι1 .zero
  | O  => ι1 .one
  | T  => ι2 true
  | X  => ι2 false

def decS : Option A → DS
  | none                       => S0
  | some (some (.inl .sep))    => S0
  | some (some (.inl .minus))  => M
  | some (some (.inl .zero))   => Z
  | some (some (.inl .one))    => O
  | some (some (.inr true))    => T
  | some (some (.inr false))   => X
  | some none                  => X

@[simp] lemma decS_none : decS none = S0 := rfl
@[simp] lemma decS_dsA (q : DS) : decS (some (dsA q)) = q := by cases q <;> rfl

lemma dsA_inj {q q' : DS} (h : dsA q = dsA q') : q = q' := by
  have := congrArg (fun a => decS (some a)) h
  simpa using this

def δA (q : Option A) (a : A) : A := dsA (dstep (decS q) a)

lemma runQ_some : ∀ (l : List A) (q : DS), runQ δA (some (dsA q)) l = some (dsA (runD q l)) := by
  intro l
  induction l with
  | nil => intro q; rfl
  | cons a l ih =>
    intro q
    simp only [runQ, δA, decS_dsA, runD_cons]
    exact ih (dstep q a)

lemma runQ_dec (l : List A) (q : Option A) (hl : l ≠ []) :
    runQ δA q l = some (dsA (runD (decS q) l)) := by
  rcases l with _ | ⟨a, l⟩
  · exact absurd rfl hl
  · simp only [runQ, δA, runD_cons]
    exact runQ_some l (dstep (decS q) a)

lemma runQ_none_accept (u : List A) :
    runQ δA none u = some (dsA T) ↔ ∃ c d, u = chkWord c d := by
  rcases u with _ | ⟨a, l⟩
  · constructor
    · intro h; simp [runQ] at h
    · rintro ⟨c, d, h⟩; simp [chkWord] at h
  · rw [runQ_dec _ _ (List.cons_ne_nil _ _), decS_none, Option.some.injEq]
    exact ⟨fun h => (runD_iff _).1 (dsA_inj h), fun h => congrArg dsA ((runD_iff _).2 h)⟩

def outA (k : K) (q : Option A) (a : A) : Option A :=
  if k = K.dlen then
    match a with
    | some (.inr _) => some mkA
    | _ => none
  else if k = K.sgnR then
    if decS q = S0 then
      match a with
      | some (.inl .zero)  => some (ι1 .one)
      | some (.inl .one)   => some (ι1 .one)
      | some (.inl .sep)   => some (ι1 .zero)
      | some (.inl .minus) => some (ι1 .minus)
      | _ => none
    else none
  else none

def gd (a : A) : Option A :=
  match a with
  | some (.inr _) => some mkA
  | _ => none

lemma fm_dlen (c : List ℤ) (d : List Bool) :
    (chkWord c d).filterMap gd = List.replicate d.length mkA := by
  rw [chkWord_eq, List.filterMap_append, List.filterMap_cons]
  have h1 : ((encInts c).map ι1).filterMap gd = [] := by
    induction (encInts c) with
    | nil => rfl
    | cons b l ih => simp [ι1, gd]
  have h2 : (d.map ι2).filterMap gd = List.replicate d.length mkA := by
    induction d with
    | nil => rfl
    | cons b l ih => simp [ι2, gd, ih, List.replicate_succ]
  simp [h1, h2, gd]

lemma emitR_sgnR_nonS0 : ∀ (bs : List Bool) (q : DS), (q = M ∨ q = Z ∨ q = O) →
    emitR δA outA K.sgnR (some (dsA q)) (bs.map (ι1 ∘ dg)) = [] := by
  intro bs
  induction bs with
  | nil => intro q _; rfl
  | cons b bs ih =>
    intro q hq
    simp only [List.map_cons, Function.comp_apply, emitR, δA, decS_dsA]
    have hneq : q ≠ S0 := by rcases hq with rfl | rfl | rfl <;> decide
    have hout : outA K.sgnR (some (dsA q)) (ι1 (dg b)) = none := by
      simp [outA, hneq]
    have hstep : dstep q (ι1 (dg b)) = M ∨ dstep q (ι1 (dg b)) = Z ∨ dstep q (ι1 (dg b)) = O := by
      rcases hq with rfl | rfl | rfl <;> cases b <;> simp [dstep, ι1, dg]
    rw [hout, ih _ hstep]
    rfl

lemma emitR_sgnR_int (z : ℤ) (q : Option A) (hq : decS q = S0) :
    emitR δA outA K.sgnR q ((encInt z).map ι1) = [sgnSym z] ∧
    decS (runQ δA q ((encInt z).map ι1)) = S0 := by
  have hrun : decS (runQ δA q ((encInt z).map ι1)) = S0 := by
    rw [runQ_dec _ _ (by simp [encInt_ne_nil]), hq, cpart_int z, decS_dsA]
  refine ⟨?_, hrun⟩
  by_cases hz : z = 0
  · subst hz
    simp [encInt, encNat, ι1, emitR, outA, hq, sgnSym]
  · by_cases hlt : z < 0
    · have hk : z.natAbs ≠ 0 := by omega
      rw [encInt_neg' z hlt, List.map_cons, emitR]
      have hout1 : outA K.sgnR q (ι1 .minus) = some (ι1 .minus) := by
        simp [outA, hq, ι1]
      have hsgn : sgnSym z = ι1 .minus := by
        unfold sgnSym; rw [if_neg (by omega), if_neg hz]
      have hδ1 : δA q (ι1 .minus) = dsA M := by simp [δA, hq, ι1, dstep]
      rw [hout1, hδ1]
      have hbody : ((Nat.bits z.natAbs).map dg ++ [BSym.sep]).map ι1 =
          (Nat.bits z.natAbs).map (ι1 ∘ dg) ++ [ι1 .sep] := by
        simp [List.map_append, List.map_map]
      rw [hbody, emitR_append, emitR_sgnR_nonS0 _ M (Or.inl rfl), List.append_nil]
      rw [runQ_some, cpart_bits z.natAbs M (Or.inr (Or.inl rfl)) hk]
      simp [emitR, outA, ι1, hsgn]
    · have hpos : 0 < z := by omega
      have hk : z.natAbs ≠ 0 := by omega
      have hsgn : sgnSym z = ι1 .one := by unfold sgnSym; rw [if_pos hpos]
      rcases hbits : Nat.bits z.natAbs with _ | ⟨b, bs⟩
      · have : z.natAbs = 0 := bits_inj (hbits.trans (by simp : [] = Nat.bits 0))
        omega
      · rw [encInt_nonneg z (by omega), hbits, List.map_cons, List.cons_append, List.map_cons,
          emitR]
        have hout1 : outA K.sgnR q (ι1 (dg b)) = some (ι1 .one) := by
          cases b <;> simp [outA, hq, ι1, dg]
        have hstep1 : dstep S0 (ι1 (dg b)) = Z ∨ dstep S0 (ι1 (dg b)) = O := by
          cases b <;> simp [dstep, ι1, dg]
        have hδ1 : δA q (ι1 (dg b)) = dsA (dstep S0 (ι1 (dg b))) := by simp [δA, hq]
        rw [hout1, hδ1]
        have hbody : (bs.map dg ++ [BSym.sep]).map ι1 = bs.map (ι1 ∘ dg) ++ [ι1 .sep] := by
          simp [List.map_append, List.map_map]
        rw [hbody, emitR_append, emitR_sgnR_nonS0 bs _ (Or.inr hstep1), List.append_nil]
        have hrunO : runD (dstep S0 (ι1 (dg b))) (bs.map (ι1 ∘ dg)) = O := by
          have hc := cpart_bits z.natAbs S0 (Or.inl rfl) hk
          rw [hbits, List.map_cons, runD_cons] at hc
          exact hc
        rw [runQ_some, hrunO]
        simp [emitR, outA, ι1, hsgn]

lemma emitR_sgnR_ints : ∀ (c : List ℤ) (q : Option A), decS q = S0 →
    emitR δA outA K.sgnR q ((encInts c).map ι1) = (c.map sgnSym).reverse ∧
    decS (runQ δA q ((encInts c).map ι1)) = S0 := by
  intro c
  induction c with
  | nil => intro q hq; exact ⟨rfl, hq⟩
  | cons z c ih =>
    intro q hq
    rw [encInts_cons, List.map_append, emitR_append, runQ_append]
    obtain ⟨he1, hr1⟩ := emitR_sgnR_int z q hq
    obtain ⟨he2, hr2⟩ := ih _ hr1
    rw [he1, he2]
    exact ⟨by simp, hr2⟩

lemma emitR_sgnR_tail : ∀ (d : List Bool),
    emitR δA outA K.sgnR (some (dsA T)) (d.map ι2) = [] := by
  intro d
  induction d with
  | nil => rfl
  | cons b d ih =>
    simp only [List.map_cons, emitR, δA, decS_dsA, ι2, dstep, ih]
    simp [outA]

lemma emitR_sgnR_chkWord (c : List ℤ) (d : List Bool) :
    emitR δA outA K.sgnR none (chkWord c d) = (c.map sgnSym).reverse := by
  rw [chkWord_eq, emitR_append]
  obtain ⟨he1, hr1⟩ := emitR_sgnR_ints c none decS_none
  rw [he1]
  simp only [emitR, δA, hr1, dstep, emitR_sgnR_tail]
  simp [outA]

lemma scan_result (u : List A) (s : K → List A)
    (hki : s K.ki = u) (hst : s K.st = []) (hdl : s K.dlen = []) (hsr : s K.sgnR = []) :
    let t := scanRun K.ki K.st δA outA u s
    (scanProg K.ki K.st δA outA).Exec s t (3 * u.length + 1) ∧
    ((t K.st).head? = some (dsA T) ↔ ∃ c d, u = chkWord c d) ∧
    (∀ c d, u = chkWord c d →
      t K.dlen = List.replicate d.length mkA ∧ t K.sgnR = (c.map sgnSym).reverse) ∧
    (∀ k, k ≠ K.ki → k ≠ K.st → k ≠ K.dlen → k ≠ K.sgnR → t k = s k) := by
  refine ⟨exec_scan K.ki K.st δA outA u s hki, ?_, ?_, ?_⟩
  · rw [scanRun_st K.ki K.st (by decide), hst, List.head?_nil]
    exact runQ_none_accept u
  · intro c d hu
    constructor
    · rw [scanRun_other K.ki K.st (by decide) δA outA K.dlen (by decide) (by decide), hdl,
        List.append_nil, emitR_indep δA outA K.dlen gd (fun q a => by simp [outA, gd]), hu,
        fm_dlen c d, List.reverse_replicate]
    · rw [scanRun_other K.ki K.st (by decide) δA outA K.sgnR (by decide) (by decide), hsr,
        List.append_nil, hst, List.head?_nil, hu, emitR_sgnR_chkWord c d]
  · intro k h1 h2 h3 h4
    rw [scanRun_other K.ki K.st (by decide) δA outA k h1 h2]
    have hem : emitR δA outA k (s K.st).head? u = [] := by
      rw [emitR_indep δA outA k (fun _ => none) (fun q a => by simp [outA, h3, h4])]
      simp
    rw [hem, List.nil_append]

/-! ## Halving and binary-vs-unary comparison (`hcLoop`) -/

section HalvCmp
variable {K' A' : Type} [DecidableEq K']

def halveAct (U H P : K') (mk : A') (h : K' → Option A') (k : K') : StackAct A' :=
  if k = U then .pop
  else if k = P then (if (h P).isSome then .pop else .push mk)
  else if k = H then (if (h P).isSome then .push mk else .keep) else .keep

def halveProg (U H P : K') (mk : A') : StackProg K' A' :=
  .loop (fun h => (h U).isSome) (.act (halveAct U H P mk))

lemma exec_halve (U H P : K') (hUH : U ≠ H) (hUP : U ≠ P) (hHP : H ≠ P) (mk : A') :
    ∀ (L p0 : ℕ) (s : K' → List A'), (s U).length = L → p0 ≤ 1 → s P = List.replicate p0 mk →
      (halveProg U H P mk).Exec s
        (Function.update (Function.update (Function.update s U []) P
          (List.replicate ((p0 + L) % 2) mk)) H
          (List.replicate ((p0 + L) / 2) mk ++ s H)) (3 * L + 1) := by
  intro L
  induction L with
  | zero =>
    intro p0 s hL hp hP
    have hU : s U = [] := List.eq_nil_of_length_eq_zero hL
    have hpost : Function.update (Function.update (Function.update s U []) P
        (List.replicate ((p0 + 0) % 2) mk)) H (List.replicate ((p0 + 0) / 2) mk ++ s H) = s := by
      have h1 : (p0 + 0) % 2 = p0 := by omega
      have h2 : (p0 + 0) / 2 = 0 := by omega
      rw [h1, h2, ← hP, ← hU]
      funext k
      by_cases k1 : k = H
      · subst k1; simp
      by_cases k2 : k = P
      · subst k2; simp [k1]
      by_cases k3 : k = U
      · subst k3; simp [k1]
      · simp [k1]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simp [hU])
  | succ L ih =>
    intro p0 s hL hp hP
    obtain ⟨a, l, hU⟩ : ∃ a l, s U = a :: l := by
      rcases h : s U with _ | ⟨a, l⟩
      · rw [h] at hL; simp at hL
      · exact ⟨a, l, rfl⟩
    set s1 := StackProg.applyAct (halveAct U H P mk) s with hs1
    have e1U : s1 U = l := by simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hU]
    have hlen : (s1 U).length = L := by rw [e1U]; rw [hU] at hL; simpa using hL
    rcases (show p0 = 0 ∨ p0 = 1 by omega) with rfl | rfl
    · have e1P : s1 P = List.replicate 1 mk := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUP]
      have e1H : s1 H = s H := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUH, hHP]
      have h2 := ih 1 s1 hlen le_rfl e1P
      have hpost : Function.update (Function.update (Function.update s1 U []) P
          (List.replicate ((1 + L) % 2) mk)) H (List.replicate ((1 + L) / 2) mk ++ s1 H) =
          Function.update (Function.update (Function.update s U []) P
          (List.replicate ((0 + (L + 1)) % 2) mk)) H
          (List.replicate ((0 + (L + 1)) / 2) mk ++ s H) := by
        rw [e1H, show (1 + L) % 2 = (0 + (L + 1)) % 2 by omega,
          show (1 + L) / 2 = (0 + (L + 1)) / 2 by omega]
        funext k
        by_cases k1 : k = H
        · subst k1; simp
        by_cases k2 : k = P
        · subst k2; simp [k1]
        by_cases k3 : k = U
        · subst k3; simp [k1, k2]
        · simp [k1, k2, k3, hs1, StackProg.applyAct, halveAct, StackAct.apply]
      rw [← hpost]
      have := StackProg.Exec.loopTrue (test := fun h => (h U).isSome) (by simp [hU])
        (StackProg.Exec.act (halveAct U H P mk) s) h2
      rw [show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]; exact this
    · have e1P : s1 P = List.replicate 0 mk := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUP]
      have e1H : s1 H = mk :: s H := by
        simp [hs1, StackProg.applyAct, halveAct, StackAct.apply, hP, Ne.symm hUH, hHP]
      have h2 := ih 0 s1 hlen (by omega) e1P
      have hpost : Function.update (Function.update (Function.update s1 U []) P
          (List.replicate ((0 + L) % 2) mk)) H (List.replicate ((0 + L) / 2) mk ++ s1 H) =
          Function.update (Function.update (Function.update s U []) P
          (List.replicate ((1 + (L + 1)) % 2) mk)) H
          (List.replicate ((1 + (L + 1)) / 2) mk ++ s H) := by
        rw [e1H, show (0 + L) % 2 = (1 + (L + 1)) % 2 by omega,
          show (1 + (L + 1)) / 2 = (0 + L) / 2 + 1 by omega, List.replicate_succ',
          List.append_assoc, List.singleton_append]
        funext k
        by_cases k1 : k = H
        · subst k1; simp
        by_cases k2 : k = P
        · subst k2; simp [k1]
        by_cases k3 : k = U
        · subst k3; simp [k1, k2]
        · simp [k1, k2, k3, hs1, StackProg.applyAct, halveAct, StackAct.apply]
      rw [← hpost]
      have := StackProg.Exec.loopTrue (test := fun h => (h U).isSome) (by simp [hU])
        (StackProg.Exec.act (halveAct U H P mk) s) h2
      rw [show 3 * (L + 1) + 1 = 1 + 1 + 1 + (3 * L + 1) by ring]; exact this

def mism : List Bool → ℕ → ℕ
  | [], _ => 0
  | b :: bs, v => mism bs (v / 2) + (if (decide (v % 2 = 1) != b) = true then 1 else 0)

lemma mism_bits : ∀ (k v : ℕ),
    (mism (Nat.bits k) v = 0 ∧ v / 2 ^ (Nat.bits k).length = 0) ↔ k = v := by
  intro k
  induction k using Nat.binaryRec' with
  | zero => intro v; simp [mism]; omega
  | bit b n hn ih =>
    intro v
    rw [Nat.bits_append_bit _ _ hn, mism, List.length_cons, pow_succ', ← Nat.div_div_eq_div_mul]
    have h := ih (v / 2)
    constructor
    · rintro ⟨h1, h2⟩
      have hm : mism n.bits (v / 2) = 0 := by omega
      have hb : (decide (v % 2 = 1) != b) = false := by
        by_contra hc; simp only [Bool.not_eq_false] at hc; rw [if_pos hc] at h1; omega
      have hn' := h.1 ⟨hm, h2⟩
      rw [Nat.bit_val]
      cases b <;> simp at hb ⊢ <;> omega
    · intro hv
      subst hv
      rw [Nat.bit_val] at h ⊢
      have e1 : (2 * n + b.toNat) / 2 = n := by
        cases b
        · simp
        · simp; omega
      rw [e1] at h ⊢
      obtain ⟨h1, h2⟩ := h.2 rfl
      refine ⟨?_, h2⟩
      rw [h1]
      cases b <;> simp

def hcAct (T P B : K') (mk : A') (isOne : Option A' → Bool) (h : K' → Option A') (k : K') :
    StackAct A' :=
  if k = T then .pop
  else if k = P then (if (h P).isSome then .pop else .keep)
  else if k = B then (if ((h P).isSome != isOne (h T)) = true then .push mk else .keep)
  else .keep

def hcLoop (T U H P B : K') (mk : A') (isD isOne : Option A' → Bool) : StackProg K' A' :=
  .loop (fun h => isD (h T))
    (.seq (halveProg U H P mk) (.seq (.act (hcAct T P B mk isOne))
      (transferProg H (fun k => decide (k = U)))))

def hcPost (T U B : K') (mk : A') (s : K' → List A') (bs : List Bool) (v : ℕ) (r : List A') :
    K' → List A' :=
  Function.update (Function.update (Function.update s T r) U
    (List.replicate (v / 2 ^ bs.length) mk)) B (List.replicate (mism bs v) mk ++ s B)

lemma exec_hc (T U H P B : K') (hTU : T ≠ U) (hTH : T ≠ H) (hTP : T ≠ P) (hTB : T ≠ B)
    (hUH : U ≠ H) (hUP : U ≠ P) (hUB : U ≠ B) (hHP : H ≠ P) (hHB : H ≠ B) (hPB : P ≠ B)
    (mk : A') (dsym : Bool → A') (isD isOne : Option A' → Bool)
    (hD : ∀ b, isD (some (dsym b)) = true) (hO : ∀ b, isOne (some (dsym b)) = b)
    (r : List A') (hr : isD r.head? = false) :
    ∀ (bs : List Bool) (v : ℕ) (s : K' → List A'), s T = bs.map dsym ++ r →
      s U = List.replicate v mk → s H = [] → s P = [] →
      ∃ n ≤ bs.length * (6 * v + 12) + 1,
        (hcLoop T U H P B mk isD isOne).Exec s (hcPost T U B mk s bs v r) n := by
  intro bs
  induction bs with
  | nil =>
    intro v s hT hU hH hP
    refine ⟨1, by simp, ?_⟩
    have hpost : hcPost T U B mk s [] v r = s := by
      funext k
      simp only [hcPost, mism, List.length_nil, pow_zero, Nat.div_one, List.replicate_zero,
        List.nil_append]
      by_cases k1 : k = B
      · subst k1; simp
      by_cases k2 : k = U
      · subst k2; simp [k1, hU]
      by_cases k3 : k = T
      · subst k3; simp [k1, k2, hT]
      · simp [k1, k2, k3]
    rw [hpost]
    exact StackProg.Exec.loopFalse (by simpa [hT] using hr)
  | cons b bs ih =>
    intro v s hT hU hH hP
    have e1 := exec_halve U H P hUH hUP hHP mk v 0 s (by simp [hU]) (by omega) (by simp [hP])
    set s1 := Function.update (Function.update (Function.update s U []) P
      (List.replicate ((0 + v) % 2) mk)) H (List.replicate ((0 + v) / 2) mk ++ s H) with hs1
    set s2 := StackProg.applyAct (hcAct T P B mk isOne) s1 with hs2
    have e2 := StackProg.Exec.act (hcAct T P B mk isOne) s1
    have h1T : s1 T = dsym b :: (bs.map dsym ++ r) := by
      simp [hs1, hTU, hTH, hTP, hT]
    have h1P : s1 P = List.replicate (v % 2) mk := by simp [hs1, Ne.symm hHP]
    have h1H : s1 H = List.replicate (v / 2) mk := by simp [hs1, hH]
    have h1U : s1 U = [] := by simp [hs1, hUH, hUP]
    have hpar : (s1 P).head?.isSome = decide (v % 2 = 1) := by
      rw [h1P]; rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    have e3 := CookPvsNP.stack_transfer H (fun k => decide (k = U)) s2
    set mb := if (decide (v % 2 = 1) != b) = true then 1 else 0 with hmb
    set s' := Function.update (Function.update (Function.update s T (bs.map dsym ++ r)) U
      (List.replicate (v / 2) mk)) B (List.replicate mb mk ++ s B) with hs'
    have hsB : s1 B = s B := by simp [hs1, Ne.symm hHB, Ne.symm hPB, Ne.symm hUB]
    have h2T : s2 T = bs.map dsym ++ r := by
      simp [hs2, StackProg.applyAct, hcAct, StackAct.apply, h1T]
    have h2P : s2 P = [] := by
      simp only [hs2, StackProg.applyAct, hcAct, if_neg (Ne.symm hTP), if_true, h1P]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h, StackAct.apply]
    have h2B : s2 B = List.replicate mb mk ++ s B := by
      have hx : ((s1 P).head?.isSome != isOne (s1 T).head?) = (decide (v % 2 = 1) != b) := by
        rw [hpar, h1T, List.head?_cons, hO]
      simp only [hs2, StackProg.applyAct, hcAct, if_neg (Ne.symm hTB), if_neg (Ne.symm hPB),
        if_true, hx]
      by_cases hc : (decide (v % 2 = 1) != b) = true <;> simp [hc, hmb, StackAct.apply, hsB]
    have h2o : ∀ k, k ≠ T → k ≠ P → k ≠ B → s2 k = s1 k := by
      intro k k1 k2 k3
      simp [hs2, StackProg.applyAct, hcAct, StackAct.apply, k1, k2, k3]
    have hs2H : s2 H = List.replicate (v / 2) mk := by
      rw [h2o H (Ne.symm hTH) hHP hHB, h1H]
    have hs2U : s2 U = [] := by rw [h2o U (Ne.symm hTU) hUP hUB, h1U]
    have h3 : transferStore H (fun k => decide (k = U)) s2 = s' := by
      funext k
      by_cases k1 : k = H
      · rw [k1]; simp [transferStore, hs', Ne.symm hTH, hUH.symm, hHB, hH]
      by_cases k2 : k = U
      · rw [k2]; simp [transferStore, hs', hUB, hs2H, hs2U, hUH]
      by_cases k3 : k = T
      · rw [k3]; simp [transferStore, hs', hTB, hTU, hTH, h2T]
      by_cases k4 : k = P
      · rw [k4]; simp [transferStore, hs', hPB, hUP.symm, hTP.symm, hHP.symm, h2P, hP]
      by_cases k5 : k = B
      · rw [k5]; simp [transferStore, hs', hHB.symm, hUB.symm, h2B]
      · simp only [transferStore, k1, k2, if_false, decide_false, Bool.false_eq_true]
        rw [h2o k k3 k4 k5]
        simp [hs', hs1, k1, k2, k3, k4, k5]
    rw [h3] at e3
    obtain ⟨n', hn', e4⟩ := ih (v / 2) s' (by simp [hs', hTB, hTU])
      (by simp [hs', hUB])
      (by simp [hs', Ne.symm hUH, hHB, Ne.symm hTH, hH])
      (by simp [hs', Ne.symm hUP, hPB, Ne.symm hTP, hP])
    have hpost : hcPost T U B mk s' bs (v / 2) r = hcPost T U B mk s (b :: bs) v r := by
      have hdiv : v / 2 / 2 ^ bs.length = v / 2 ^ (b :: bs).length := by
        rw [List.length_cons, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
      funext k
      simp only [hcPost, hdiv, mism]
      by_cases k1 : k = B
      · rw [k1]
        have hB' : s' B = List.replicate mb mk ++ s B := by simp [hs']
        simp only [Function.update_self, hB', hmb, List.replicate_add, List.append_assoc]
      by_cases k2 : k = U
      · subst k2; simp [k1]
      by_cases k3 : k = T
      · subst k3; simp [k1, k2]
      · simp [hs', k1, k2, k3]
    rw [← hpost]
    refine ⟨1 + ((3 * v + 1) + 1 + (1 + 1 + (3 * (s2 H).length + 1))) + 1 + n', ?_,
      StackProg.Exec.loopTrue (by simp [hT, hD]) (StackProg.Exec.seq (by simpa using e1)
        (StackProg.Exec.seq e2 e3)) e4⟩
    have hmul := Nat.mul_le_mul_left bs.length (show 6 * (v / 2) + 12 ≤ 6 * v + 12 by omega)
    have hexp : (bs.length + 1) * (6 * v + 12) = bs.length * (6 * v + 12) + (6 * v + 12) := by ring
    rw [hs2H, List.length_replicate, List.length_cons, hexp]
    generalize bs.length * (6 * v + 12) = X at hmul ⊢
    generalize bs.length * (6 * (v / 2) + 12) = Y at hmul hn'
    omega

end HalvCmp

/-! ## Guarded stages and helper macros -/

def Res (s t : K → List A) (Q : Prop) : Prop := (Q → t K.ko = s K.ko) ∧ (¬Q → t K.ko = [])

lemma exec_congr {p : SP} {s t t' : K → List A} {n : ℕ} (h : p.Exec s t n) (e : t = t') :
    p.Exec s t' n := e ▸ h

def flagProg (t : (K → Option A) → Bool) : SP :=
  .act (fun h k => if k = K.Bd ∧ t h = true then .push mkA else .keep)

def skipProg : SP := .act (fun _ _ => .keep)

def guard (step rest : SP) : SP :=
  .seq step (.branch (fun h => (h K.Bd).isNone) rest (clearProg K.ko))

lemma exec_flag (t : (K → Option A) → Bool) (s : K → List A) :
    (flagProg t).Exec s (Function.update s K.Bd
      (if t (fun k => (s k).head?) = true then mkA :: s K.Bd else s K.Bd)) 1 := by
  unfold flagProg
  refine exec_congr (StackProg.Exec.act _ s) ?_
  funext k
  by_cases hk : k = K.Bd
  · subst hk
    by_cases ht : t (fun k => (s k).head?) = true <;> simp [StackProg.applyAct, StackAct.apply, ht]
  · simp [StackProg.applyAct, StackAct.apply, hk]

lemma exec_skip (s : K → List A) : skipProg.Exec s s 1 := by
  unfold skipProg
  refine exec_congr (StackProg.Exec.act _ s) ?_
  funext k; simp [StackProg.applyAct, StackAct.apply]

lemma exec_guard (step rest : SP) (s t : K → List A) (n R : ℕ) (P1 P2 : Prop)
    (hst : step.Exec s t n) (hko : t K.ko = s K.ko) (hc : t K.Bd = [] ↔ P1)
    (hrest : t K.Bd = [] → ∃ t' m, m ≤ R ∧ rest.Exec t t' m ∧ Res t t' P2) :
    ∃ t' m, m ≤ n + R + 3 * (s K.ko).length + 4 ∧ (guard step rest).Exec s t' m ∧
      Res s t' (P1 ∧ P2) := by
  by_cases hb : t K.Bd = []
  · obtain ⟨t', m, hm, he, h1, h2⟩ := hrest hb
    refine ⟨t', n + 1 + (1 + m), by omega,
      StackProg.Exec.seq hst (StackProg.Exec.branchTrue (by simp [hb]) he), ?_, ?_⟩
    · rintro ⟨-, h⟩; rw [h1 h, hko]
    · intro h; exact h2 (fun h' => h ⟨hc.1 hb, h'⟩)
  · have he := (CookPvsNP.stack_basic_macros K.ko t).2.2
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hb
    refine ⟨_, n + 1 + (1 + (3 * (t K.ko).length + 1)), by rw [hko]; omega,
      StackProg.Exec.seq hst (StackProg.Exec.branchFalse (by simp [hal]) he), ?_, ?_⟩
    · rintro ⟨h, -⟩; exact absurd (hc.2 h) hb
    · intro _; simp

lemma flatten_replicate_replicate {α : Type} (m n : ℕ) (a : α) :
    (List.replicate m (List.replicate n a)).flatten = List.replicate (m * n) a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm, List.replicate_add]

/-! ## Stage 3: Sign checks (`posPairLoop`, `nnPairLoop`, `prog3`) -/

def posPairBody : SP :=
  .seq (popProg K.dlen)
    (.seq (flagProg (fun h => !decide (h K.sgn = some (ι1 .one))))
      (.seq (popProg K.sgn) (popProg K.sgn)))

def posPairLoop : SP :=
  .loop (fun h => (h K.dlen).isSome) posPairBody

lemma exec_posPairLoop : ∀ (n : ℕ) (revL : List ℤ) (tail : List A) (s : K → List A),
    revL.length = 2 * n →
    s K.dlen = List.replicate n mkA →
    s K.sgn = revL.map sgnSym ++ tail →
    ∃ t m, m ≤ 10 * n + 1 ∧ posPairLoop.Exec s t m ∧
      t K.dlen = [] ∧
      t K.sgn = tail ∧
      t K.ko = s K.ko ∧
      (t K.Bd = [] ↔ s K.Bd = [] ∧ ∀ i < n, 0 < revL.getD (2 * i) 0) := by
  intro n
  induction n with
  | zero =>
    intro revL tail s hlen hdl hsgn
    have hrev : revL = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrev
    refine ⟨s, 1, by simp, StackProg.Exec.loopFalse (by simp [hdl]), by simpa using hdl,
      by simpa using hsgn, rfl, by simp⟩
  | succ n ih =>
    intro revL tail s hlen hdl hsgn
    rcases revL with _ | ⟨a, _ | ⟨b, revL'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : revL'.length = 2 * n := by simp at hlen; omega
      have e1 := (CookPvsNP.stack_basic_macros K.dlen s).2.1
      set s1 := Function.update s K.dlen (s K.dlen).tail with hs1
      have e2 := exec_flag (fun h => !decide (h K.sgn = some (ι1 .one))) s1
      set s2 := Function.update s1 K.Bd
        (if (!decide ((s1 K.sgn).head? = some (ι1 .one))) = true
         then mkA :: s1 K.Bd else s1 K.Bd) with hs2
      have e3 := (CookPvsNP.stack_basic_macros K.sgn s2).2.1
      set s3 := Function.update s2 K.sgn (s2 K.sgn).tail with hs3
      have e4 := (CookPvsNP.stack_basic_macros K.sgn s3).2.1
      set s4 := Function.update s3 K.sgn (s3 K.sgn).tail with hs4
      have h1dl : s1 K.dlen = List.replicate n mkA := by
        simp [hs1, hdl, List.replicate_succ]
      have h1sgn : s1 K.sgn = sgnSym a :: sgnSym b :: (revL'.map sgnSym ++ tail) := by
        simp [hs1, hsgn]
      have h1Bd : s1 K.Bd = s K.Bd := by simp [hs1]
      have h1ko : s1 K.ko = s K.ko := by simp [hs1]
      have h4dl : s4 K.dlen = List.replicate n mkA := by simp [hs4, hs3, hs2, h1dl]
      have h4sgn : s4 K.sgn = revL'.map sgnSym ++ tail := by
        simp [hs4, hs3, hs2, h1sgn]
      have h4ko : s4 K.ko = s K.ko := by simp [hs4, hs3, hs2, h1ko]
      have h4Bd : s4 K.Bd = [] ↔ s K.Bd = [] ∧ 0 < a := by
        have hhd : (s1 K.sgn).head? = some (sgnSym a) := by rw [h1sgn]; rfl
        have h4eq : s4 K.Bd = s2 K.Bd := by simp [hs4, hs3]
        rw [h4eq, hs2, Function.update_self, h1Bd, hhd]
        by_cases ha : sgnSym a = ι1 .one
        · have hpos : 0 < a := (sgnSym_eq_one_iff a).1 ha
          simp [ha, hpos]
        · have hnpos : ¬ 0 < a := fun h => ha ((sgnSym_eq_one_iff a).2 h)
          simp [ha, hnpos]
      obtain ⟨t, m, hm, he, tdl, tsgn, tko, tBd⟩ := ih revL' tail s4 hlen' h4dl h4sgn
      have hbody : posPairBody.Exec s s4 7 :=
        StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3 e4))
      refine ⟨t, 1 + 7 + 1 + m, by omega,
        StackProg.Exec.loopTrue (by simp [hdl, List.replicate_succ]) hbody he,
        tdl, tsgn, by rw [tko, h4ko], ?_⟩
      rw [tBd, h4Bd]
      constructor
      · rintro ⟨⟨hB, ha⟩, hrest⟩
        refine ⟨hB, fun i hi => ?_⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
          have h2 : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
          simpa [h2] using hrest i (by omega)
      · rintro ⟨hB, hall⟩
        refine ⟨⟨hB, by simpa using hall 0 (by omega)⟩, fun i hi => ?_⟩
        have h2 : 2 * (i + 1) = (2 * i + 1) + 1 := by ring
        simpa [h2] using hall (i + 1) (by omega)

def nnPairBody : SP :=
  .seq (flagProg (fun h => decide (h K.sgn = some (ι1 .minus))))
    (.seq (popProg K.sgn) (popProg K.sgn))

def nnPairLoop : SP :=
  .loop (fun h => (h K.sgn).isSome) nnPairBody

lemma exec_nnPairLoop : ∀ (m : ℕ) (wtL : List ℤ) (s : K → List A),
    wtL.length = 2 * m →
    s K.sgn = wtL.map sgnSym →
    ∃ t n, n ≤ 8 * m + 1 ∧ nnPairLoop.Exec s t n ∧
      t K.sgn = [] ∧
      t K.ko = s K.ko ∧
      (t K.Bd = [] ↔ s K.Bd = [] ∧ ∀ j < m, 0 ≤ wtL.getD (2 * j) 0) := by
  intro m
  induction m with
  | zero =>
    intro wtL s hlen hsgn
    have hwt : wtL = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hwt
    refine ⟨s, 1, by simp, StackProg.Exec.loopFalse (by simp [hsgn]), by simpa using hsgn,
      rfl, by simp⟩
  | succ m ih =>
    intro wtL s hlen hsgn
    rcases wtL with _ | ⟨a, _ | ⟨b, wtL'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : wtL'.length = 2 * m := by simp at hlen; omega
      have hsgn' : s K.sgn = sgnSym a :: sgnSym b :: wtL'.map sgnSym := by simpa using hsgn
      have e1 := exec_flag (fun h => decide (h K.sgn = some (ι1 .minus))) s
      set s1 := Function.update s K.Bd
        (if decide ((s K.sgn).head? = some (ι1 .minus)) = true
         then mkA :: s K.Bd else s K.Bd) with hs1
      have e2 := (CookPvsNP.stack_basic_macros K.sgn s1).2.1
      set s2 := Function.update s1 K.sgn (s1 K.sgn).tail with hs2
      have e3 := (CookPvsNP.stack_basic_macros K.sgn s2).2.1
      set s3 := Function.update s2 K.sgn (s2 K.sgn).tail with hs3
      have h3sgn : s3 K.sgn = wtL'.map sgnSym := by simp [hs3, hs2, hs1, hsgn']
      have h3ko : s3 K.ko = s K.ko := by simp [hs3, hs2, hs1]
      have h3Bd : s3 K.Bd = [] ↔ s K.Bd = [] ∧ 0 ≤ a := by
        have hhd : (s K.sgn).head? = some (sgnSym a) := by rw [hsgn']; rfl
        have h3eq : s3 K.Bd = s1 K.Bd := by simp [hs3, hs2]
        rw [h3eq, hs1, Function.update_self, hhd]
        by_cases ha : sgnSym a = ι1 .minus
        · have hneg : ¬ 0 ≤ a := fun h => ((sgnSym_ne_minus_iff a).2 h) ha
          simp [ha, hneg]
        · have hnn : 0 ≤ a := (sgnSym_ne_minus_iff a).1 ha
          simp [ha, hnn]
      obtain ⟨t, n, hn, he, tsgn, tko, tBd⟩ := ih wtL' s3 hlen' h3sgn
      have hbody : nnPairBody.Exec s s3 5 :=
        StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)
      refine ⟨t, 1 + 5 + 1 + n, by omega,
        StackProg.Exec.loopTrue (by simp [hsgn']) hbody he,
        tsgn, by rw [tko, h3ko], ?_⟩
      rw [tBd, h3Bd]
      constructor
      · rintro ⟨⟨hB, ha⟩, hrest⟩
        refine ⟨hB, fun j hj => ?_⟩
        cases j with
        | zero => simpa using ha
        | succ j =>
          have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
          simpa [h2] using hrest j (by omega)
      · rintro ⟨hB, hall⟩
        refine ⟨⟨hB, by simpa using hall 0 (by omega)⟩, fun j hj => ?_⟩
        have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
        simpa [h2] using hall (j + 1) (by omega)

def step3 : SP :=
  .seq (popProg K.sgnR)
    (.seq (popProg K.sgnR)
      (.seq (popProg K.sgnR)
        (.seq (flagProg (fun h => !decide (h K.sgnR = some (ι1 .one))))
          (.seq (popProg K.sgnR)
            (.seq (transferProg K.sgnR (fun k => decide (k = K.sgn)))
              (.seq (popProg K.sgn)
                (.seq posPairLoop nnPairLoop)))))))

def prog3 : SP := guard step3 skipProg

lemma st3 (s : K → List A) (c : List ℤ) (n L : ℕ)
    (hlen : c.length = 2 * numRats n + 1)
    (hsr : s K.sgnR = (c.map sgnSym).reverse)
    (hdl : s K.dlen = List.replicate n mkA)
    (hsgn : s K.sgn = [])
    (hBd : s K.Bd = [])
    (hcn : c.length ≤ L) (hkoL : (s K.ko).length ≤ L) :
    ∃ t m, m ≤ 30 * L + 30 ∧ prog3.Exec s t m ∧
      Res s t (0 < chkNum c (numRats n - 2) ∧
        (∀ i < n, 0 < chkNum c i) ∧
        (∀ j < numRats n - 2 - n, 0 ≤ chkNum c (n + j))) := by
  obtain ⟨z, v0n, v0d, kn, kd, revL, wtL, hc, hrevL, hwtL, _, hv0n, hrevG, hwtG⟩ :=
    list_decomp c n hlen
  have hsr_eq : s K.sgnR =
      sgnSym kd :: sgnSym kn :: sgnSym v0d :: sgnSym v0n ::
        ((revL ++ wtL).map sgnSym).reverse ++ [sgnSym z] := by
    rw [hsr, hc]
    simp [List.map_append, List.reverse_append, List.append_assoc]
  have e1 := (CookPvsNP.stack_basic_macros K.sgnR s).2.1
  set s1 := Function.update s K.sgnR (s K.sgnR).tail with hs1
  have e2 := (CookPvsNP.stack_basic_macros K.sgnR s1).2.1
  set s2 := Function.update s1 K.sgnR (s1 K.sgnR).tail with hs2
  have e3 := (CookPvsNP.stack_basic_macros K.sgnR s2).2.1
  set s3 := Function.update s2 K.sgnR (s2 K.sgnR).tail with hs3
  have h3sr : s3 K.sgnR = sgnSym v0n :: (((revL ++ wtL).map sgnSym).reverse ++ [sgnSym z]) := by
    simp [hs3, hs2, hs1, hsr_eq]
  have e4 := exec_flag (fun h => !decide (h K.sgnR = some (ι1 .one))) s3
  set s4 := Function.update s3 K.Bd
    (if (!decide ((s3 K.sgnR).head? = some (ι1 .one))) = true
     then mkA :: s3 K.Bd else s3 K.Bd) with hs4
  have e5 := (CookPvsNP.stack_basic_macros K.sgnR s4).2.1
  set s5 := Function.update s4 K.sgnR (s4 K.sgnR).tail with hs5
  have h5sr : s5 K.sgnR = ((revL ++ wtL).map sgnSym).reverse ++ [sgnSym z] := by
    simp [hs5, hs4, h3sr]
  have h5sgn : s5 K.sgn = [] := by simp [hs5, hs4, hs3, hs2, hs1, hsgn]
  have e6 := CookPvsNP.stack_transfer K.sgnR (fun k => decide (k = K.sgn)) s5
  set s6 := transferStore K.sgnR (fun k => decide (k = K.sgn)) s5 with hs6
  have h6sgn : s6 K.sgn = sgnSym z :: (revL.map sgnSym ++ wtL.map sgnSym) := by
    simp [hs6, transferStore, h5sr, h5sgn, List.reverse_append, List.map_append]
  have e7 := (CookPvsNP.stack_basic_macros K.sgn s6).2.1
  set s7 := Function.update s6 K.sgn (s6 K.sgn).tail with hs7
  have h7sgn : s7 K.sgn = revL.map sgnSym ++ wtL.map sgnSym := by simp [hs7, h6sgn]
  have h7dl : s7 K.dlen = List.replicate n mkA := by
    simp [hs7, hs6, transferStore, hs5, hs4, hs3, hs2, hs1, hdl]
  have h7ko : s7 K.ko = s K.ko := by
    simp [hs7, hs6, transferStore, hs5, hs4, hs3, hs2, hs1]
  have h7Bd : s7 K.Bd = [] ↔ 0 < v0n := by
    have h7eq : s7 K.Bd = s4 K.Bd := by simp [hs7, hs6, transferStore, hs5]
    have h3Bd : s3 K.Bd = [] := by simp [hs3, hs2, hs1, hBd]
    have hhd : (s3 K.sgnR).head? = some (sgnSym v0n) := by rw [h3sr]; rfl
    rw [h7eq, hs4, Function.update_self, h3Bd, hhd]
    by_cases hv : sgnSym v0n = ι1 .one
    · have hp : 0 < v0n := (sgnSym_eq_one_iff v0n).1 hv
      simp [hv, hp]
    · have hnp : ¬ 0 < v0n := fun h => hv ((sgnSym_eq_one_iff v0n).2 h)
      simp [hv, hnp]
  obtain ⟨s8, m8, hm8, e8, _, h8sgn, h8ko, h8Bd⟩ :=
    exec_posPairLoop n revL (wtL.map sgnSym) s7 hrevL h7dl h7sgn
  obtain ⟨s9, m9, hm9, e9, _, h9ko, h9Bd⟩ :=
    exec_nnPairLoop (numRats n - 2 - n) wtL s8 hwtL h8sgn
  have hstep : step3.Exec s s9
      (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 +
        ((3 * (s5 K.sgnR).length + 1) + 1 + (1 + 1 + (m8 + 1 + m9)))))))) :=
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6
        (StackProg.Exec.seq e7 (StackProg.Exec.seq e8 e9)))))))
  have h9Bd_iff : s9 K.Bd = [] ↔
      (0 < chkNum c (numRats n - 2) ∧
        (∀ i < n, 0 < chkNum c i) ∧
        (∀ j < numRats n - 2 - n, 0 ≤ chkNum c (n + j))) := by
    rw [h9Bd, h8Bd, h7Bd, hv0n]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun i hi => ?_, fun j hj => ?_⟩
      · rw [← hrevG i hi]; exact h2 i hi
      · rw [← hwtG j hj]; exact h3 j hj
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, fun i hi => ?_⟩, fun j hj => ?_⟩
      · rw [hrevG i hi]; exact h2 i hi
      · rw [hwtG j hj]; exact h3 j hj
  have hs5len : (s5 K.sgnR).length ≤ L := by
    have : (s5 K.sgnR).length = revL.length + wtL.length + 1 := by simp [h5sr]; omega
    have hge := numRats_ge_two_add n
    omega
  have hnL : n ≤ L := by
    have hge := numRats_ge_two_add n
    omega
  have hwtmL : numRats n - 2 - n ≤ L := by
    have hge := numRats_ge_two_add n
    omega
  have hguard := exec_guard step3 skipProg s s9 _ 1
    (0 < chkNum c (numRats n - 2) ∧
      (∀ i < n, 0 < chkNum c i) ∧
      (∀ j < numRats n - 2 - n, 0 ≤ chkNum c (n + j)))
    True hstep (by rw [h9ko, h8ko, h7ko]) h9Bd_iff
    (fun _ => ⟨s9, 1, le_rfl, exec_skip s9, fun _ => rfl, fun h => absurd trivial h⟩)
  obtain ⟨t, m, hm, he, hres⟩ := hguard
  refine ⟨t, m, by omega, he, ?_⟩
  exact ⟨fun h => hres.1 ⟨h, trivial⟩, fun h => hres.2 (fun ⟨h', _⟩ => h h')⟩

/-! ## Stage 2b: Check `z.natAbs = n` using `hcLoop` -/

def isDA (o : Option A) : Bool := decide (o = some (ι1 .zero)) || decide (o = some (ι1 .one))
def isOneA (o : Option A) : Bool := decide (o = some (ι1 .one))
def dsymA (b : Bool) : A := ι1 (dg b)

lemma isDA_dsymA (b : Bool) : isDA (some (dsymA b)) = true := by cases b <;> rfl
lemma isOneA_dsymA (b : Bool) : isOneA (some (dsymA b)) = b := by cases b <;> rfl

def step2b : SP :=
  .seq (copyProg K.dlen K.U K.sc)
    (.seq (hcLoop K.W K.U K.H K.P K.Bd mkA isDA isOneA)
      (flagProg (fun h => (h K.U).isSome)))

def prog2b : SP := guard step2b prog3

lemma st2b (s : K → List A) (c : List ℤ) (d : List Bool) (L : ℕ)
    (hlen : c.length = 2 * numRats d.length + 1)
    (hz0 : 0 ≤ c.getD 0 0)
    (hW : s K.W = chkWord c d)
    (hsr : s K.sgnR = (c.map sgnSym).reverse)
    (hdl : s K.dlen = List.replicate d.length mkA)
    (hsc : s K.sc = []) (hU : s K.U = []) (hH : s K.H = []) (hP : s K.P = [])
    (hsgn : s K.sgn = []) (hBd : s K.Bd = [])
    (huL : (chkWord c d).length ≤ L) (hkoL : (s K.ko).length ≤ L) :
    ∃ t m, m ≤ 10 * (L + 1) ^ 2 + 40 * L + 60 ∧ prog2b.Exec s t m ∧
      Res s t ((c.getD 0 0).natAbs = d.length ∧
        0 < chkNum c (numRats d.length - 2) ∧
        (∀ i < d.length, 0 < chkNum c i) ∧
        (∀ j < numRats d.length - 2 - d.length, 0 ≤ chkNum c (d.length + j))) := by
  obtain ⟨z, c', hc⟩ : ∃ z c', c = z :: c' :=
    List.exists_cons_of_ne_nil (by intro h; rw [h] at hlen; simp at hlen)
  have hz_eq : c.getD 0 0 = z := by simp [hc]
  rw [hz_eq] at hz0 ⊢
  have hdL : d.length ≤ L := by
    have : d.length ≤ (chkWord c d).length := by
      simp only [chkWord_eq, List.length_append, List.length_cons, List.length_map]; omega
    omega
  have hcL : c.length ≤ L := by
    have h1 := len_encInts c
    have h2 : (encInts c).length ≤ (chkWord c d).length := by
      simp only [chkWord_eq, List.length_append, List.length_cons, List.length_map]; omega
    omega
  have hbitsL : (Nat.bits z.natAbs).length ≤ L := by
    have h1 := bits_len_le_encInt z
    have h2 : (encInt z).length ≤ (encInts c).length := by
      rw [hc, encInts_cons, List.length_append]; omega
    have h3 : (encInts c).length ≤ (chkWord c d).length := by
      simp only [chkWord_eq, List.length_append, List.length_cons, List.length_map]; omega
    omega
  have e1 := CookPvsNP.stack_copy K.dlen K.U K.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s K.U (s K.dlen ++ s K.U) with hs1
  have h1U : s1 K.U = List.replicate d.length mkA := by simp [hs1, hdl, hU]
  have h1H : s1 K.H = [] := by simp [hs1, hH]
  have h1P : s1 K.P = [] := by simp [hs1, hP]
  have h1Bd : s1 K.Bd = [] := by simp [hs1, hBd]
  set rtail : List A := ι1 .sep :: ((encInts c').map ι1 ++ none :: d.map ι2)
  have h1W : s1 K.W = (Nat.bits z.natAbs).map dsymA ++ rtail := by
    simp only [hs1, Function.update_of_ne (by decide : K.W ≠ K.U), hW, hc, chkWord_eq,
      encInts_cons, encInt_nonneg z hz0, List.map_append, List.map_map, List.append_assoc]
    rfl
  obtain ⟨nhc, hnhc, e2⟩ := exec_hc K.W K.U K.H K.P K.Bd
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) mkA dsymA isDA isOneA isDA_dsymA isOneA_dsymA
    rtail rfl (Nat.bits z.natAbs) d.length s1 h1W h1U h1H h1P
  set s2 := hcPost K.W K.U K.Bd mkA s1 (Nat.bits z.natAbs) d.length rtail with hs2
  have e3 := exec_flag (fun h => (h K.U).isSome) s2
  set s3 := Function.update s2 K.Bd
    (if (s2 K.U).head?.isSome = true then mkA :: s2 K.Bd else s2 K.Bd) with hs3
  have hstep : step2b.Exec s s3 ((6 * (s K.dlen).length + 3) + 1 + (nhc + 1 + 1)) :=
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 e3)
  have h3ko : s3 K.ko = s K.ko := by simp [hs3, hs2, hcPost, hs1]
  have h3sr : s3 K.sgnR = (c.map sgnSym).reverse := by simp [hs3, hs2, hcPost, hs1, hsr]
  have h3dl : s3 K.dlen = List.replicate d.length mkA := by simp [hs3, hs2, hcPost, hs1, hdl]
  have h3sgn : s3 K.sgn = [] := by simp [hs3, hs2, hcPost, hs1, hsgn]
  have h3Bd : s3 K.Bd = [] ↔ z.natAbs = d.length := by
    rw [hs3, Function.update_self, hs2, hcPost]
    simp only [Function.update_self, Function.update_of_ne (by decide : K.U ≠ K.Bd), h1Bd,
      List.append_nil]
    rw [← mism_bits z.natAbs d.length]
    cases hdiv : d.length / 2 ^ (Nat.bits z.natAbs).length with
    | zero =>
      cases hm : mism (Nat.bits z.natAbs) d.length with
      | zero => simp
      | succ k => simp
    | succ q => simp
  have hguard := exec_guard step2b prog3 s s3 _ (30 * L + 30)
    (z.natAbs = d.length)
    (0 < chkNum c (numRats d.length - 2) ∧
      (∀ i < d.length, 0 < chkNum c i) ∧
      (∀ j < numRats d.length - 2 - d.length, 0 ≤ chkNum c (d.length + j)))
    hstep h3ko h3Bd
    (fun hBd3 => st3 s3 c d.length L hlen h3sr h3dl h3sgn hBd3 hcL (by rw [h3ko]; exact hkoL))
  obtain ⟨t, m, hm, he, hres⟩ := hguard
  refine ⟨t, m, ?_, he, hres⟩
  have hdlen_eq : (s K.dlen).length = d.length := by simp [hdl]
  rw [hdlen_eq] at hm
  have hmul : (Nat.bits z.natAbs).length * (6 * d.length + 12) ≤ L * (6 * L + 12) :=
    Nat.mul_le_mul hbitsL (by omega)
  nlinarith

/-! ## Stage 2a: Copy `ko` to `W` and check `0 ≤ c.getD 0 0` -/

def step2a : SP :=
  .seq (copyProg K.ko K.W K.sc)
    (flagProg (fun h => decide (h K.W = some (ι1 .minus))))

def prog2a : SP := guard step2a prog2b

lemma head_chkWord_eq_minus_iff (c : List ℤ) (d : List Bool) (hc : c ≠ []) :
    (chkWord c d).head? = some (ι1 .minus) ↔ c.getD 0 0 < 0 := by
  rcases c with _ | ⟨z, c'⟩
  · exact absurd rfl hc
  simp only [List.getD_cons_zero, chkWord_eq, encInts_cons, List.map_append, List.append_assoc]
  by_cases hz : z < 0
  · rw [encInt_neg' z hz]
    simp [hz, ι1]
  · rw [encInt_nonneg z (by omega)]
    cases hb : Nat.bits z.natAbs with
    | nil => simp [hz, ι1]
    | cons b bs =>
      cases b <;> simp [hz, ι1, dg]

lemma st2a (s : K → List A) (c : List ℤ) (d : List Bool) (L : ℕ)
    (hlen : c.length = 2 * numRats d.length + 1)
    (hko : s K.ko = chkWord c d)
    (hsr : s K.sgnR = (c.map sgnSym).reverse)
    (hdl : s K.dlen = List.replicate d.length mkA)
    (hsc : s K.sc = []) (hW : s K.W = []) (hU : s K.U = []) (hH : s K.H = [])
    (hP : s K.P = []) (hsgn : s K.sgn = []) (hBd : s K.Bd = [])
    (huL : (chkWord c d).length ≤ L) :
    ∃ t m, m ≤ 10 * (L + 1) ^ 2 + 50 * L + 80 ∧ prog2a.Exec s t m ∧
      Res s t (0 ≤ c.getD 0 0 ∧
        (c.getD 0 0).natAbs = d.length ∧
        0 < chkNum c (numRats d.length - 2) ∧
        (∀ i < d.length, 0 < chkNum c i) ∧
        (∀ j < numRats d.length - 2 - d.length, 0 ≤ chkNum c (d.length + j))) := by
  have hcne : c ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  have e1 := CookPvsNP.stack_copy K.ko K.W K.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s K.W (s K.ko ++ s K.W) with hs1
  have e2 := exec_flag (fun h => decide (h K.W = some (ι1 .minus))) s1
  set s2 := Function.update s1 K.Bd
    (if decide ((s1 K.W).head? = some (ι1 .minus)) = true
     then mkA :: s1 K.Bd else s1 K.Bd) with hs2
  have hstep : step2a.Exec s s2 ((6 * (s K.ko).length + 3) + 1 + 1) :=
    StackProg.Exec.seq e1 e2
  have h2W : s2 K.W = chkWord c d := by simp [hs2, hs1, hko, hW]
  have h2ko : s2 K.ko = s K.ko := by simp [hs2, hs1]
  have h2sr : s2 K.sgnR = (c.map sgnSym).reverse := by simp [hs2, hs1, hsr]
  have h2dl : s2 K.dlen = List.replicate d.length mkA := by simp [hs2, hs1, hdl]
  have h2sc : s2 K.sc = [] := by simp [hs2, hs1, hsc]
  have h2U : s2 K.U = [] := by simp [hs2, hs1, hU]
  have h2H : s2 K.H = [] := by simp [hs2, hs1, hH]
  have h2P : s2 K.P = [] := by simp [hs2, hs1, hP]
  have h2sgn : s2 K.sgn = [] := by simp [hs2, hs1, hsgn]
  have h2Bd : s2 K.Bd = [] ↔ 0 ≤ c.getD 0 0 := by
    have h1W : s1 K.W = chkWord c d := by simp [hs1, hko, hW]
    have h1Bd : s1 K.Bd = [] := by simp [hs1, hBd]
    rw [hs2, Function.update_self, h1W, h1Bd]
    by_cases hm : (chkWord c d).head? = some (ι1 .minus)
    · have hlt : c.getD 0 0 < 0 := (head_chkWord_eq_minus_iff c d hcne).1 hm
      simp only [hm, decide_true, ↓reduceIte, List.cons_ne_nil, false_iff]
      omega
    · have hge : 0 ≤ c.getD 0 0 := by
        have := (head_chkWord_eq_minus_iff c d hcne).not.1 hm
        omega
      simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, true_iff]
      exact hge
  have hguard := exec_guard step2a prog2b s s2 _ (10 * (L + 1) ^ 2 + 40 * L + 60)
    (0 ≤ c.getD 0 0)
    ((c.getD 0 0).natAbs = d.length ∧
      0 < chkNum c (numRats d.length - 2) ∧
      (∀ i < d.length, 0 < chkNum c i) ∧
      (∀ j < numRats d.length - 2 - d.length, 0 ≤ chkNum c (d.length + j)))
    hstep h2ko h2Bd
    (fun hBd2 => st2b s2 c d L hlen (h2Bd.1 hBd2) h2W h2sr h2dl h2sc h2U h2H h2P h2sgn hBd2
      huL (by rw [h2ko, hko]; exact huL))
  obtain ⟨t, m, hm, he, hres⟩ := hguard
  refine ⟨t, m, ?_, he, hres⟩
  rw [hko] at hm
  omega

/-! ## Stage 1: Length check `c.length = n * n + 3 * n + 5` -/

def rMul : Fin 4 ↪ K :=
  ⟨![K.dlen, K.T, K.U, K.sc], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

lemma rMul_0 : rMul 0 = K.dlen := rfl
lemma rMul_1 : rMul 1 = K.T := rfl
lemma rMul_2 : rMul 2 = K.U := rfl
lemma rMul_3 : rMul 3 = K.sc := rfl

lemma head?_isSome_eq_false_iff {α : Type} (l : List α) :
    l.head?.isSome = false ↔ l = [] := by
  cases l <;> simp

def mulTargetProg : SP :=
  .seq (copyProg K.dlen K.U K.sc) (repeatCopyProg rMul)

lemma exec_mulTarget (s : K → List A) (n : ℕ)
    (hdl : s K.dlen = List.replicate n mkA) (hsc : s K.sc = []) (hU : s K.U = []) (hT : s K.T = []) :
    ∃ m ≤ 6 * n * n + 13 * n + 6,
      mulTargetProg.Exec s (Function.update s K.T (List.replicate (n * n) mkA)) m := by
  have e1 := CookPvsNP.stack_copy K.dlen K.U K.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s K.U (s K.dlen ++ s K.U) with hs1
  have h1sc : s1 (rMul 3) = [] := by rw [rMul_3]; simp [hs1, hsc]
  have e2 := CookPvsNP.stack_repeat_copy rMul s1 h1sc
  rw [rMul_0, rMul_1, rMul_2] at e2
  have h1dl : s1 K.dlen = List.replicate n mkA := by simp [hs1, hdl]
  have h1U : s1 K.U = List.replicate n mkA := by simp [hs1, hdl, hU]
  have h1T : s1 K.T = [] := by simp [hs1, hT]
  have hpost : Function.update (Function.update s1 K.U []) K.T
      ((List.replicate (s1 K.U).length (s1 K.dlen)).flatten ++ s1 K.T) =
      Function.update s K.T (List.replicate (n * n) mkA) := by
    rw [h1U, h1dl, h1T, List.length_replicate, flatten_replicate_replicate, List.append_nil]
    funext k
    by_cases hk1 : k = K.T
    · subst hk1; simp
    by_cases hk2 : k = K.U
    · subst hk2; simp [hk1, hU]
    · simp [hk1, hk2, hs1]
  have he := StackProg.Exec.seq e1 (exec_congr e2 hpost)
  refine ⟨(6 * (s K.dlen).length + 3) + 1 + ((6 * (s1 K.dlen).length + 7) * (s1 K.U).length + 1),
    ?_, he⟩
  rw [hdl, h1dl, h1U]
  simp only [List.length_replicate]
  nlinarith

def add3n5Prog : SP :=
  .seq (copyProg K.dlen K.T K.sc)
    (.seq (copyProg K.dlen K.T K.sc)
      (.seq (copyProg K.dlen K.T K.sc)
        (.seq (pushProg K.T mkA)
          (.seq (pushProg K.T mkA)
            (.seq (pushProg K.T mkA)
              (.seq (pushProg K.T mkA) (pushProg K.T mkA)))))))

lemma exec_add3n5 (s : K → List A) (n : ℕ)
    (hdl : s K.dlen = List.replicate n mkA) (hsc : s K.sc = []) :
    ∃ m ≤ 18 * n + 30,
      add3n5Prog.Exec s
        (Function.update s K.T (List.replicate (3 * n + 5) mkA ++ s K.T)) m := by
  have e1 := CookPvsNP.stack_copy K.dlen K.T K.sc (by decide) (by decide) (by decide) s hsc
  set s1 := Function.update s K.T (s K.dlen ++ s K.T) with hs1
  have e2 := CookPvsNP.stack_copy K.dlen K.T K.sc (by decide) (by decide) (by decide) s1
    (by simp [hs1, hsc])
  set s2 := Function.update s1 K.T (s1 K.dlen ++ s1 K.T) with hs2
  have e3 := CookPvsNP.stack_copy K.dlen K.T K.sc (by decide) (by decide) (by decide) s2
    (by simp [hs2, hs1, hsc])
  set s3 := Function.update s2 K.T (s2 K.dlen ++ s2 K.T) with hs3
  have e4 := (CookPvsNP.stack_basic_macros K.T s3).1 mkA
  set s4 := Function.update s3 K.T (mkA :: s3 K.T) with hs4
  have e5 := (CookPvsNP.stack_basic_macros K.T s4).1 mkA
  set s5 := Function.update s4 K.T (mkA :: s4 K.T) with hs5
  have e6 := (CookPvsNP.stack_basic_macros K.T s5).1 mkA
  set s6 := Function.update s5 K.T (mkA :: s5 K.T) with hs6
  have e7 := (CookPvsNP.stack_basic_macros K.T s6).1 mkA
  set s7 := Function.update s6 K.T (mkA :: s6 K.T) with hs7
  have e8 := (CookPvsNP.stack_basic_macros K.T s7).1 mkA
  set s8 := Function.update s7 K.T (mkA :: s7 K.T) with hs8
  have h1dl : s1 K.dlen = List.replicate n mkA := by simp [hs1, hdl]
  have h2dl : s2 K.dlen = List.replicate n mkA := by simp [hs2, h1dl]
  have hpost : s8 = Function.update s K.T (List.replicate (3 * n + 5) mkA ++ s K.T) := by
    funext k
    by_cases hk : k = K.T
    · subst hk
      have hrep : mkA :: mkA :: mkA :: mkA :: mkA ::
          (List.replicate n mkA ++ (List.replicate n mkA ++ (List.replicate n mkA ++ s K.T))) =
          List.replicate (3 * n + 5) mkA ++ s K.T := by
        have h3n : List.replicate n mkA ++ List.replicate n mkA ++ List.replicate n mkA =
            List.replicate (3 * n) mkA := by
          rw [← List.replicate_add, ← List.replicate_add, show n + n + n = 3 * n by omega]
        rw [← List.append_assoc, ← List.append_assoc, h3n]
        have h5 : List.replicate (3 * n + 5) mkA =
            mkA :: mkA :: mkA :: mkA :: mkA :: List.replicate (3 * n) mkA := by
          rw [show 3 * n + 5 = 5 + 3 * n by omega, List.replicate_add]; rfl
        rw [h5]; rfl
      simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_self,
        Function.update_of_ne (by decide : K.dlen ≠ K.T), hdl]
      exact hrep
    · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hk]
  have he := StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
    (StackProg.Exec.seq e4 (StackProg.Exec.seq e5 (StackProg.Exec.seq e6
      (StackProg.Exec.seq e7 (exec_congr e8 hpost)))))))
  refine ⟨_, ?_, he⟩
  rw [hdl, h1dl, h2dl]
  simp only [List.length_replicate]
  omega

def step1 : SP :=
  .seq mulTargetProg
    (.seq add3n5Prog
      (.seq (copyProg K.sgnR K.C K.sc)
        (.seq (syncPopProg K.C K.T)
          (flagProg (fun h => (h K.C).isSome || (h K.T).isSome)))))

def prog1 : SP := guard step1 prog2a

lemma st1 (s : K → List A) (c : List ℤ) (d : List Bool) (L : ℕ)
    (hko : s K.ko = chkWord c d)
    (hsr : s K.sgnR = (c.map sgnSym).reverse)
    (hdl : s K.dlen = List.replicate d.length mkA)
    (hsc : s K.sc = []) (hW : s K.W = []) (hU : s K.U = []) (hT : s K.T = [])
    (hC : s K.C = []) (hH : s K.H = []) (hP : s K.P = []) (hsgn : s K.sgn = []) (hBd : s K.Bd = [])
    (huL : (chkWord c d).length ≤ L) :
    ∃ t m, m ≤ 20 * (L + 1) ^ 2 + 100 * L + 120 ∧ prog1.Exec s t m ∧
      Res s t (ShapeOK c d) := by
  set n := d.length
  have hnL : n ≤ L := by
    have : n ≤ (chkWord c d).length := by
      simp only [n, chkWord_eq, List.length_append, List.length_cons, List.length_map]; omega
    omega
  have hcL : c.length ≤ L := by
    have h1 := len_encInts c
    have h2 : (encInts c).length ≤ (chkWord c d).length := by
      simp only [chkWord_eq, List.length_append, List.length_cons, List.length_map]; omega
    omega
  obtain ⟨m1, hm1, e1⟩ := exec_mulTarget s n hdl hsc hU hT
  set s1 := Function.update s K.T (List.replicate (n * n) mkA) with hs1
  obtain ⟨m2, hm2, e2⟩ := exec_add3n5 s1 n (by simp [hs1, hdl]) (by simp [hs1, hsc])
  set s2 := Function.update s1 K.T (List.replicate (3 * n + 5) mkA ++ s1 K.T) with hs2
  have h2Tlen : (s2 K.T).length = n * n + 3 * n + 5 := by
    simp [hs2, hs1]; omega
  have h2sc : s2 K.sc = [] := by simp [hs2, hs1, hsc]
  have h2sr : s2 K.sgnR = (c.map sgnSym).reverse := by simp [hs2, hs1, hsr]
  have h2C : s2 K.C = [] := by simp [hs2, hs1, hC]
  have e3 := CookPvsNP.stack_copy K.sgnR K.C K.sc (by decide) (by decide) (by decide) s2 h2sc
  set s3 := Function.update s2 K.C (s2 K.sgnR ++ s2 K.C) with hs3
  have h3Clen : (s3 K.C).length = c.length := by simp [hs3, h2sr, h2C]
  have h3Tlen : (s3 K.T).length = n * n + 3 * n + 5 := by simp [hs3, h2Tlen]
  have e4 := CookPvsNP.stack_sync_pop K.C K.T (by decide) s3
  set mm := min (s3 K.C).length (s3 K.T).length with hmm
  set s4 := Function.update (Function.update s3 K.C ((s3 K.C).drop mm)) K.T
    ((s3 K.T).drop mm) with hs4
  have e5 := exec_flag (fun h => (h K.C).isSome || (h K.T).isSome) s4
  set s5 := Function.update s4 K.Bd
    (if ((s4 K.C).head?.isSome || (s4 K.T).head?.isSome) = true
     then mkA :: s4 K.Bd else s4 K.Bd) with hs5
  have hstep : step1.Exec s s5 _ :=
    StackProg.Exec.seq e1 (StackProg.Exec.seq e2 (StackProg.Exec.seq e3
      (StackProg.Exec.seq e4 e5)))
  have h5ko : s5 K.ko = s K.ko := by simp [hs5, hs4, hs3, hs2, hs1]
  have h5sr : s5 K.sgnR = (c.map sgnSym).reverse := by simp [hs5, hs4, hs3, h2sr]
  have h5dl : s5 K.dlen = List.replicate n mkA := by simp [hs5, hs4, hs3, hs2, hs1, hdl]
  have h5sc : s5 K.sc = [] := by simp [hs5, hs4, hs3, h2sc]
  have h5W : s5 K.W = [] := by simp [hs5, hs4, hs3, hs2, hs1, hW]
  have h5U : s5 K.U = [] := by simp [hs5, hs4, hs3, hs2, hs1, hU]
  have h5H : s5 K.H = [] := by simp [hs5, hs4, hs3, hs2, hs1, hH]
  have h5P : s5 K.P = [] := by simp [hs5, hs4, hs3, hs2, hs1, hP]
  have h5sgn : s5 K.sgn = [] := by simp [hs5, hs4, hs3, hs2, hs1, hsgn]
  have h5Bd : s5 K.Bd = [] ↔ c.length = n * n + 3 * n + 5 := by
    have h4Bd : s4 K.Bd = [] := by simp [hs4, hs3, hs2, hs1, hBd]
    have h4C : s4 K.C = (s3 K.C).drop mm := by simp [hs4]
    have h4T : s4 K.T = (s3 K.T).drop mm := by simp [hs4]
    have hCdrop : (s4 K.C).head?.isSome = false ↔ c.length ≤ n * n + 3 * n + 5 := by
      rw [head?_isSome_eq_false_iff, h4C, List.drop_eq_nil_iff, hmm, h3Clen, h3Tlen]
      omega
    have hTdrop : (s4 K.T).head?.isSome = false ↔ n * n + 3 * n + 5 ≤ c.length := by
      rw [head?_isSome_eq_false_iff, h4T, List.drop_eq_nil_iff, hmm, h3Clen, h3Tlen]
      omega
    rw [hs5, Function.update_self, h4Bd]
    cases hc1 : (s4 K.C).head?.isSome <;> cases ht1 : (s4 K.T).head?.isSome
    · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, true_iff]
      have := hCdrop.1 hc1; have := hTdrop.1 ht1; omega
    · simp only [Bool.false_or, ↓reduceIte, List.cons_ne_nil, false_iff]
      intro heq; have := hTdrop.2 (by omega); rw [ht1] at this; exact absurd this (by decide)
    · simp only [Bool.true_or, ↓reduceIte, List.cons_ne_nil, false_iff]
      intro heq; have := hCdrop.2 (by omega); rw [hc1] at this; exact absurd this (by decide)
    · simp only [Bool.true_or, ↓reduceIte, List.cons_ne_nil, false_iff]
      intro heq; have := hCdrop.2 (by omega); rw [hc1] at this; exact absurd this (by decide)
  have hguard := exec_guard step1 prog2a s s5 _ (10 * (L + 1) ^ 2 + 50 * L + 80)
    (c.length = n * n + 3 * n + 5)
    (0 ≤ c.getD 0 0 ∧
      (c.getD 0 0).natAbs = n ∧
      0 < chkNum c (numRats n - 2) ∧
      (∀ i < n, 0 < chkNum c i) ∧
      (∀ j < numRats n - 2 - n, 0 ≤ chkNum c (n + j)))
    hstep h5ko h5Bd
    (fun hBd5 => st2a s5 c d L
      (by rw [two_mul_numRats_add_one]; exact h5Bd.1 hBd5)
      (by rw [h5ko, hko]) h5sr h5dl h5sc h5W h5U h5H h5P h5sgn hBd5 huL)
  obtain ⟨t, m, hm, he, hres⟩ := hguard
  refine ⟨t, m, ?_, he, ?_⟩
  · have h2sr_len : (s2 K.sgnR).length = c.length := by simp [h2sr]
    have hmm_le : mm ≤ c.length := by rw [hmm, h3Clen]; exact min_le_left _ _
    rw [h2sr_len, hko] at hm
    have hnn : n * n ≤ L * L := Nat.mul_le_mul hnL hnL
    clear * - hm hm1 hm2 hnL hcL huL hmm_le hnn
    nlinarith
  · exact ⟨fun h => hres.1 ((shapeOK_iff c d).1 h),
      fun h => hres.2 (fun h' => h ((shapeOK_iff c d).2 h'))⟩

/-! ## Main program and top-level correctness -/

def mainProg : SP :=
  .seq (copyProg K.ki K.ko K.sc)
    (.seq (scanProg K.ki K.st δA outA)
      (.branch (fun h => decide (h K.st = some (dsA T))) prog1 (clearProg K.ko)))

open Classical in
theorem main (u : List A) : ∃ t n, n ≤ 25 * (u.length + 1) ^ 2 + 120 * u.length + 150 ∧
    mainProg.Exec (fun j => if j = K.ki then u else []) t n ∧
    t K.ko = (if ∃ c d, u = chkWord c d ∧ ShapeOK c d then u else []) := by
  have e1 := CookPvsNP.stack_copy K.ki K.ko K.sc (by decide) (by decide) (by decide)
    (fun j => if j = K.ki then u else []) (by simp)
  set s1 : K → List A := fun j => if j = K.ki ∨ j = K.ko then u else [] with hs1
  have e1' : (copyProg K.ki K.ko K.sc).Exec (fun j => if j = K.ki then u else []) s1
      (6 * u.length + 3) := by
    simpa using exec_congr e1 (by funext k; cases k <;> simp [hs1])
  obtain ⟨e2, hiff, hcont, hoth⟩ := scan_result u s1
    (by simp [hs1]) (by simp [hs1]) (by simp [hs1]) (by simp [hs1])
  set s2 := scanRun K.ki K.st δA outA u s1 with hs2
  have hko2 : s2 K.ko = u := by
    rw [hoth K.ko (by decide) (by decide) (by decide) (by decide)]; simp [hs1]
  have hemp : ∀ k, k ≠ K.ki → k ≠ K.st → k ≠ K.dlen → k ≠ K.sgnR → k ≠ K.ko → s2 k = [] := by
    intro k h0 h1 h2 h3 h4
    rw [hoth k h0 h1 h2 h3]; simp [hs1, h0, h4]
  by_cases hsh : ∃ c d, u = chkWord c d
  · obtain ⟨c, d, hu⟩ := hsh
    obtain ⟨hdl, hsr⟩ := hcont c d hu
    have hst : decide ((s2 K.st).head? = some (dsA T)) = true :=
      decide_eq_true (hiff.2 ⟨c, d, hu⟩)
    obtain ⟨t, m, hm, he, hres⟩ := st1 s2 c d u.length (by rw [hko2, hu]) hsr hdl
      (hemp K.sc (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.W (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.U (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.T (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.C (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.H (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.P (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.sgn (by decide) (by decide) (by decide) (by decide) (by decide))
      (hemp K.Bd (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [hu])
    refine ⟨t, (6 * u.length + 3) + 1 + ((3 * u.length + 1) + 1 + (1 + m)), ?_,
      StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchTrue hst he)), ?_⟩
    · clear * - hm; nlinarith
    · have key : (∃ c' d', u = chkWord c' d' ∧ ShapeOK c' d') ↔ ShapeOK c d := by
        constructor
        · rintro ⟨c', d', hu', hok⟩
          obtain ⟨rfl, rfl⟩ := chkWord_inj c' c d' d (hu'.symm.trans hu)
          exact hok
        · intro hok; exact ⟨c, d, hu, hok⟩
      split_ifs with h
      · rw [hres.1 (key.1 h), hko2]
      · exact hres.2 (fun hok => h (key.2 hok))
  · have hst : decide ((s2 K.st).head? = some (dsA T)) = false :=
      decide_eq_false (fun h => hsh (hiff.1 h))
    have he := (CookPvsNP.stack_basic_macros K.ko s2).2.2
    refine ⟨_, (6 * u.length + 3) + 1 + ((3 * u.length + 1) + 1 + (1 + (3 * (s2 K.ko).length + 1))),
      ?_, StackProg.Exec.seq e1' (StackProg.Exec.seq e2 (StackProg.Exec.branchFalse hst he)), ?_⟩
    · rw [hko2]; have : 0 ≤ (u.length + 1) ^ 2 := Nat.zero_le _; omega
    · have hno : ¬ ∃ c d, u = chkWord c d ∧ ShapeOK c d := by
        rintro ⟨c, d, hu, -⟩; exact hsh ⟨c, d, hu⟩
      rw [if_neg hno]
      simp

end MPShape

open CookPvsNP ProjSchedTW.Complexity MultiPurchase.Hardness in
open Classical in
theorem solution :
    PolyTimeComputable (fun u : List (Option (BSym ⊕ Bool)) =>
      if ∃ c d, u = chkWord c d ∧ ShapeOK c d then u else []) := by
  obtain ⟨k, hk⟩ := CookPvsNP.polynomial_absorb 145 2 150
  refine CookPvsNP.stack_program_polytime MPShape.mainProg MPShape.K.ki MPShape.K.ko _ k fun u => ?_
  obtain ⟨t, n, hn, he, hko⟩ := MPShape.main u
  refine ⟨t, n, le_trans ?_ (hk u.length), he, hko⟩
  nlinarith
