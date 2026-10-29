-- Prove2me | solution 1 for HHRControl.PV.approval_cc_in_NP
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T01:58:55.988586+00:00
-- url     : https://prove2.me/submissions/4392c00b-9db2-4570-b77a-34b0b17f6fd6

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_CookPvsNP_StackMacros
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_stack_copy
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_sync_pop
import Theorems.Thm_CookPvsNP_stack_repeat_copy
import Theorems.Thm_CookPvsNP_stack_basic_macros
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Theorems.Thm_CookPvsNP_mem_P_of_polyReducible
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_GTWSched_NPC_Problems

set_option autoImplicit false
set_option linter.all false

section Sec_Stk0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk

section Core
variable {K A : Type} [Fintype K] [DecidableEq K]

def S (s : K → List A) : ℕ := ∑ k, (s k).length

lemma apply_len (a : StackAct A) (l : List A) : (a.apply l).length ≤ l.length + 1 := by
  cases a <;> simp [StackAct.apply] <;> omega

lemma Exec_size {p : StackProg K A} {s t : K → List A} {n : ℕ} (h : p.Exec s t n) :
    S t ≤ S s + Fintype.card K * n := by
  induction h with
  | act f s =>
    unfold S
    calc ∑ k, ((StackProg.applyAct f s) k).length ≤ ∑ k, ((s k).length + 1) :=
          Finset.sum_le_sum (fun k _ => by simpa [StackProg.applyAct] using apply_len _ _)
      _ = ∑ k, (s k).length + Fintype.card K := by simp [Finset.sum_add_distrib]
      _ ≤ ∑ k, (s k).length + Fintype.card K * 1 := by omega
  | seq _ _ ih1 ih2 => nlinarith
  | branchTrue _ _ ih => nlinarith
  | branchFalse _ _ ih => nlinarith
  | loopFalse _ => nlinarith [Nat.zero_le (Fintype.card K)]
  | loopTrue _ _ _ ih1 ih2 => nlinarith

/-- polynomial-time specification of a program computing the store transformer `g` -/
def PolySpec (p : StackProg K A) (g : (K → List A) → (K → List A)) : Prop :=
  ∃ d : ℕ, ∀ s, ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

lemma pw_const {X : ℕ} (hX : 2 ≤ X) (c : ℕ) : c ≤ X ^ c :=
  le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left hX c)

lemma pw_mono {X : ℕ} (hX : 2 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right (by omega) h

lemma pw_add {X x y a b : ℕ} (hX : 2 ≤ X) (hx : x ≤ X ^ a) (hy : y ≤ X ^ b) :
    x + y ≤ X ^ (a + b + 1) := by
  have h1 : X ^ a ≤ X ^ (a + b) := pw_mono hX (by omega)
  have h2 : X ^ b ≤ X ^ (a + b) := pw_mono hX (by omega)
  have h3 : X ^ (a + b + 1) = X ^ (a + b) * X := pow_succ _ _
  have : 0 < X ^ (a + b) := by positivity
  nlinarith

lemma pw_mul {X x y a b : ℕ} (hx : x ≤ X ^ a) (hy : y ≤ X ^ b) : x * y ≤ X ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

lemma pw_pow {X x a b : ℕ} (hx : x ≤ X ^ a) : x ^ b ≤ X ^ (a * b) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx b

lemma pw_one {X : ℕ} (hX : 2 ≤ X) : 1 ≤ X ^ 1 := by simp; omega

lemma S_pos_ge (s : K → List A) : 2 ≤ S s + 2 := by omega

lemma ps_act (f : (K → Option A) → K → StackAct A) : PolySpec (.act f) (StackProg.applyAct f) := by
  refine ⟨1, fun s => ⟨1, ?_, StackProg.Exec.act f s⟩⟩
  simp


def PS (p : StackProg K A) (g : (K → List A) → (K → List A)) (d : ℕ) : Prop :=
  ∀ s, ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

lemma PS.poly {p : StackProg K A} {g : (K → List A) → (K → List A)} {d : ℕ} (h : PS p g d) :
    PolySpec p g := ⟨d, h⟩

lemma PS.mono {p : StackProg K A} {g : (K → List A) → (K → List A)} {d e : ℕ} (h : PS p g d)
    (he : d ≤ e) : PS p g e := by
  intro s
  obtain ⟨n, hn, ex⟩ := h s
  exact ⟨n, le_trans hn (pw_mono (S_pos_ge s) he), ex⟩

lemma ps_seq' {p q : StackProg K A} {g h : (K → List A) → (K → List A)} {d1 d2 : ℕ}
    (hp : PS p g d1) (hq : PS q h d2) :
    PS (.seq p q) (h ∘ g) (d1 + 3 + (Fintype.card K + d1 + 2) * d2) := by
  intro s
  obtain ⟨n1, hn1, e1⟩ := hp s
  obtain ⟨n2, hn2, e2⟩ := hq (g s)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

def hd (s : K → List A) : K → Option A := fun k => (s k).head?

lemma PolySpec.seq {p q : StackProg K A} {g h : (K → List A) → (K → List A)}
    (hp : PolySpec p g) (hq : PolySpec q h) : PolySpec (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  exact ⟨_, ps_seq' (p := p) (q := q) (g := g) (h := h) hp hq⟩

lemma PolySpec.branch {p q : StackProg K A} {g h : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool)
    (hp : PolySpec p g) (hq : PolySpec q h) :
    PolySpec (.branch t p q) (fun s => if t (hd s) = true then g s else h s) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨2 * max d1 d2 + 3, fun s => ?_⟩
  have hX : 2 ≤ S s + 2 := by omega
  have key : ∀ n, n ≤ (S s + 2) ^ (max d1 d2) → 1 + n ≤ (S s + 2) ^ (2 * max d1 d2 + 3) := by
    intro n hn
    have h2 : 1 ≤ (S s + 2) ^ (max d1 d2) := Nat.one_le_pow _ _ (by omega)
    have := pw_add hX h2 hn
    exact le_trans this (pw_mono hX (by omega))
  by_cases ht : t (hd s) = true
  · obtain ⟨n, hn, e⟩ := hp s
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_pos ht]; exact StackProg.Exec.branchTrue ht e
  · have ht' : t (hd s) = false := by simpa using ht
    obtain ⟨n, hn, e⟩ := hq s
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_neg ht]; exact StackProg.Exec.branchFalse ht' e

/-- a loop whose body is a single action; cost `3m+1` for `m` iterations. -/
lemma loop1_exec (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    ∀ s, ∃ n, n ≤ 3 * μ s + 1 ∧ (StackProg.loop t (.act f)).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s ht
    obtain ⟨n, hn, e⟩ := ih (μ (StackProg.applyAct f s)) (by omega) _ rfl
    refine ⟨1 + 1 + 1 + n, by omega, ?_⟩
    rw [hG]
    exact StackProg.Exec.loopTrue ht (StackProg.Exec.act f s) e
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, by omega, ?_⟩
    rw [hstop s ht']
    exact StackProg.Exec.loopFalse ht'

lemma PolySpec.loop1 (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hμ : ∀ s, μ s ≤ S s)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    PolySpec (.loop t (.act f)) G := by
  refine ⟨2, fun s => ?_⟩
  obtain ⟨n, hn, e⟩ := loop1_exec t f G μ hstop hstep s
  refine ⟨n, ?_, e⟩
  have := hμ s
  nlinarith

end Core
end Stk

end Sec_Stk0

section Sec_Stk1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Prims
variable {K A : Type} [Fintype K] [DecidableEq K]

def upd (s : K → List A) (k : K) (l : List A) : K → List A := Function.update s k l

@[simp] lemma upd_same (s : K → List A) (k : K) (l : List A) : upd s k l k = l := by
  simp [upd]
lemma upd_ne (s : K → List A) {k j : K} (l : List A) (h : j ≠ k) : upd s k l j = s j := by
  simp [upd, h]

def mvw (pred : A → Bool) : List A → List A → List A × List A
  | [], b => ([], b)
  | x :: a, b => if pred x then mvw pred a (x :: b) else (x :: a, b)

def mvwT (a : K) (pred : A → Bool) : (K → Option A) → Bool :=
  fun h => match h a with | some x => pred x | none => false

def mvwF (a b : K) : (K → Option A) → K → StackAct A :=
  fun h k => if k = a then .pop else if k = b then (match h a with | some x => .push x | none => .keep) else .keep

def mvwG (a b : K) (pred : A → Bool) (s : K → List A) : K → List A :=
  upd (upd s a (mvw pred (s a) (s b)).1) b (mvw pred (s a) (s b)).2

lemma mvw_len (pred : A → Bool) : ∀ (a b : List A), (mvw pred a b).1.length ≤ a.length
  | [], b => by simp [mvw]
  | x :: a, b => by
    unfold mvw
    split_ifs
    · have := mvw_len pred a (x :: b); simp; omega
    · simp

@[simp] lemma upd_apply (s : K → List A) (k j : K) (l : List A) :
    upd s k l j = if j = k then l else s j := by
  by_cases h : j = k <;> simp [upd, h]

lemma upd_self (s : K → List A) (k : K) : upd s k (s k) = s := by
  funext j; by_cases h : j = k <;> simp [upd, h]

lemma upd_comm_ext (s : K → List A) {a b : K} (hab : a ≠ b) (la lb : List A) :
    ∀ k, upd (upd s a la) b lb k = if k = b then lb else if k = a then la else s k := by
  intro k
  by_cases h1 : k = b
  · subst h1; simp
  · by_cases h2 : k = a
    · subst h2; simp [upd_ne _ _ h1, h1]
    · simp [upd_ne _ _ h1, upd_ne _ _ h2, h1, h2]

lemma ps_mvw (a b : K) (hab : a ≠ b) (pred : A → Bool) :
    PolySpec (.loop (mvwT a pred) (.act (mvwF a b))) (mvwG a b pred) := by
  apply PolySpec.loop1 _ _ _ (fun s => (s a).length)
  · intro s
    unfold S
    exact Finset.single_le_sum (f := fun k => (s k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  · intro s h
    unfold mvwT hd at h
    unfold mvwG
    funext k
    cases hs : s a with
    | nil => simp [mvw]; split_ifs <;> simp_all
    | cons x l =>
      simp [hs] at h
      simp [mvw, h]; split_ifs <;> simp_all
  · intro s h
    unfold mvwT hd at h
    cases hs : s a with
    | nil => simp [hs] at h
    | cons x l =>
      simp [hs] at h
      have hstep : StackProg.applyAct (mvwF a b) s = upd (upd s a l) b (x :: s b) := by
        funext k
        by_cases h1 : k = b
        · subst h1; simp [StackProg.applyAct, mvwF, hab.symm, hs, StackAct.apply, hd]
        · by_cases h2 : k = a
          · subst h2; simp [StackProg.applyAct, mvwF, hs, StackAct.apply, h1]
          · simp [StackProg.applyAct, mvwF, h1, h2, StackAct.apply]
      rw [hstep]
      refine ⟨by simp [hs, hab], ?_⟩
      unfold mvwG
      funext k
      simp [hs, mvw, h, hab, hab.symm]
      split_ifs <;> simp_all
end Prims
end Stk

end Sec_Stk1

section Sec_Stk2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Loop
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma S_upd (s : K → List A) (k : K) (l : List A) :
    S (upd s k l) + (s k).length = S s + l.length := by
  unfold S upd
  have h1 := Finset.sum_update_of_mem (f := fun j => (s j).length) (Finset.mem_univ k) (l.length)
  have h2 : ∑ j, (Function.update s k l j).length = ∑ j, Function.update (fun j => (s j).length) k l.length j := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = k <;> simp [Function.update, h]
  rw [h2, h1]
  have h3 : ∑ j ∈ (Finset.univ \ {k}), (s j).length + (s k).length = ∑ j, (s j).length := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    simp [Finset.sdiff_singleton_eq_erase]
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

lemma S_le_S_upd (s : K → List A) (k : K) (l : List A) :
    S (upd s k l) ≤ S s + l.length := by
  have := S_upd s k l; omega

/-- general loop lemma: body is a program with a polynomial spec and bounded size growth -/
lemma loop_exec {p : StackProg K A} {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PS p g d)
    (hgrow : ∀ s, t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s ht
    obtain ⟨n1, hn1, e1⟩ := hp s
    obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl
    refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
    · rw [← hm]
      have hg := hgrow s ht
      have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
        have : c * μ (g s) + c ≤ c * μ s := by
          have : μ (g s) + 1 ≤ μ s := hlt
          nlinarith
        omega
      have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
        le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
      have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
        le_trans hn2 (Nat.mul_le_mul_left _ (by
          have := Nat.pow_le_pow_left hY d; omega))
      have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
      have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
          (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
      nlinarith
    · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s ht']; exact StackProg.Exec.loopFalse ht'

lemma PolySpec.loop {p : StackProg K A} {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PS p g d) (hμ : ∀ s, μ s ≤ S s)
    (hgrow : ∀ s, t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, t (hd s) = false → G s = s)
    (hstep : ∀ s, t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PolySpec (.loop t p) G := by
  refine ⟨(c + 1) * d + 3, fun s => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_exec t G μ hp hgrow hstop hstep s
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

end Loop
end Stk

end Sec_Stk2

section Sec_Stk3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section PSI
variable {K A : Type} [Fintype K] [DecidableEq K]

/-- polynomial-time spec relative to an invariant `Inv` -/
def PSI (Inv : (K → List A) → Prop) (p : StackProg K A) (g : (K → List A) → (K → List A))
    (d : ℕ) : Prop :=
  ∀ s, Inv s → ∃ n, n ≤ (S s + 2) ^ d ∧ p.Exec s (g s) n

def PSp (Inv : (K → List A) → Prop) (p : StackProg K A) (g : (K → List A) → (K → List A)) : Prop :=
  ∃ d, PSI Inv p g d

lemma PSI.mono {Inv : (K → List A) → Prop} {p : StackProg K A} {g : (K → List A) → (K → List A)}
    {d e : ℕ} (h : PSI Inv p g d) (he : d ≤ e) : PSI Inv p g e := by
  intro s hs
  obtain ⟨n, hn, ex⟩ := h s hs
  exact ⟨n, le_trans hn (pw_mono (S_pos_ge s) he), ex⟩

lemma PSp.weaken {Inv Inv' : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} (h : PSp Inv p g) (hi : ∀ s, Inv' s → Inv s) :
    PSp Inv' p g := by
  obtain ⟨d, h⟩ := h
  exact ⟨d, fun s hs => h s (hi s hs)⟩

lemma PSp.congr {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g g' : (K → List A) → (K → List A)} (h : PSp Inv p g) (hg : ∀ s, Inv s → g s = g' s) :
    PSp Inv p g' := by
  obtain ⟨d, h⟩ := h
  refine ⟨d, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := h s hs
  exact ⟨n, hn, by rw [← hg s hs]; exact e⟩

lemma PSp.of_exec {Inv : (K → List A) → Prop} (p : StackProg K A)
    (g : (K → List A) → (K → List A)) (cost : (K → List A) → ℕ) (d : ℕ)
    (hex : ∀ s, Inv s → p.Exec s (g s) (cost s))
    (hc : ∀ s, Inv s → cost s ≤ (S s + 2) ^ d) : PSp Inv p g :=
  ⟨d, fun s hs => ⟨cost s, hc s hs, hex s hs⟩⟩

lemma PSp.act {Inv : (K → List A) → Prop} (f : (K → Option A) → K → StackAct A) :
    PSp Inv (.act f) (StackProg.applyAct f) :=
  ⟨1, fun s _ => ⟨1, by simp, StackProg.Exec.act f s⟩⟩

lemma PSp.seq {Inv : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)}
    (hp : PSp Inv p g) (hq : PSp Inv q h) (hi : ∀ s, Inv s → Inv (g s)) :
    PSp Inv (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨d1 + 3 + (Fintype.card K + d1 + 2) * d2, fun s hs => ?_⟩
  obtain ⟨n1, hn1, e1⟩ := hp s hs
  obtain ⟨n2, hn2, e2⟩ := hq (g s) (hi s hs)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

lemma PSp.branch {Inv : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)} (t : (K → Option A) → Bool)
    (hp : PSp Inv p g) (hq : PSp Inv q h) :
    PSp Inv (.branch t p q) (fun s => if t (hd s) = true then g s else h s) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨2 * max d1 d2 + 3, fun s hs => ?_⟩
  have hX : 2 ≤ S s + 2 := by omega
  have key : ∀ n, n ≤ (S s + 2) ^ (max d1 d2) → 1 + n ≤ (S s + 2) ^ (2 * max d1 d2 + 3) := by
    intro n hn
    have h2 : 1 ≤ (S s + 2) ^ (max d1 d2) := Nat.one_le_pow _ _ (by omega)
    have := pw_add hX h2 hn
    exact le_trans this (pw_mono hX (by omega))
  by_cases ht : t (hd s) = true
  · obtain ⟨n, hn, e⟩ := hp s hs
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_pos ht]; exact StackProg.Exec.branchTrue ht e
  · have ht' : t (hd s) = false := by simpa using ht
    obtain ⟨n, hn, e⟩ := hq s hs
    refine ⟨1 + n, key n (le_trans hn (pw_mono hX (by omega))), ?_⟩
    show (StackProg.branch t p q).Exec s (if t (hd s) = true then g s else h s) _
    rw [if_neg ht]; exact StackProg.Exec.branchFalse ht' e

lemma loop_execI {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl (hinv s hs ht)
    refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
    · rw [← hm]
      have hg := hgrow s hs ht
      have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
        have : c * μ (g s) + c ≤ c * μ s := by
          have : μ (g s) + 1 ≤ μ s := hlt
          nlinarith
        omega
      have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
        le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
      have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
        le_trans hn2 (Nat.mul_le_mul_left _ (by
          have := Nat.pow_le_pow_left hY d; omega))
      have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
      have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
          (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
      nlinarith
    · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loop {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨(c + 1) * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execI t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

/-- single-action loop: growth is at most `card K` per iteration -/
lemma PSp.loop1 {Inv : (K → List A) → Prop}
    (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s ∧
        G s = G (StackProg.applyAct f s)) :
    PSp Inv (.loop t (.act f)) G := by
  refine PSp.loop (c := Fintype.card K) t G μ (PSp.act f) hμ hinv ?_ hstop hstep
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

end PSI
end Stk

end Sec_Stk3

section Sec_Stk4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Run
variable {K A : Type} [Fintype K] [DecidableEq K]

/-- fuel-bounded iteration of a guarded step -/
def iter (t : (K → List A) → Bool) (g : (K → List A) → (K → List A)) :
    ℕ → (K → List A) → (K → List A)
  | 0, s => s
  | n + 1, s => if t s = true then iter t g n (g s) else s

lemma iter_false (t : (K → List A) → Bool) (g : (K → List A) → (K → List A))
    (s : K → List A) (h : t s = false) (n : ℕ) : iter t g n s = s := by
  cases n <;> simp [iter, h]

lemma iter_succ_true (t : (K → List A) → Bool) (g : (K → List A) → (K → List A))
    (s : K → List A) (h : t s = true) (n : ℕ) : iter t g (n + 1) s = iter t g n (g s) := by
  simp [iter, h]

lemma iter_stable (Inv : (K → List A) → Prop) (t : (K → List A) → Bool)
    (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (hinv : ∀ s, Inv s → t s = true → Inv (g s))
    (hdec : ∀ s, Inv s → t s = true → μ (g s) < μ s) :
    ∀ n s, Inv s → μ s ≤ n → iter t g n s = iter t g (μ s) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hI h
    by_cases ht : t s = true
    · have hm := hdec s hI ht
      obtain ⟨j, hj⟩ : ∃ j, μ s = j + 1 := ⟨μ s - 1, by omega⟩
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      subst hn'
      rw [hj, iter_succ_true t g s ht, iter_succ_true t g s ht]
      rw [ih n' (by omega) (g s) (hinv s hI ht) (by omega),
        ih j (by omega) (g s) (hinv s hI ht) (by omega)]
    · have ht' : t s = false := by simpa using ht
      rw [iter_false t g s ht', iter_false t g s ht']

/-- the closed-form store map of a loop: iterate the body while the test holds -/
def lrun (t : (K → Option A) → Bool) (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (s : K → List A) : K → List A :=
  iter (fun s => t (hd s)) g (μ s) s

lemma lrun_false (t : (K → Option A) → Bool) (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (s : K → List A) (h : t (hd s) = false) : lrun t g μ s = s :=
  iter_false _ _ s h _

lemma lrun_true (Inv : (K → List A) → Prop) (t : (K → Option A) → Bool)
    (g : (K → List A) → (K → List A))
    (μ : (K → List A) → ℕ) (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s)
    (s : K → List A) (hI : Inv s) (h : t (hd s) = true) : lrun t g μ s = lrun t g μ (g s) := by
  have hm := hdec s hI h
  obtain ⟨j, hj⟩ : ∃ j, μ s = j + 1 := ⟨μ s - 1, by omega⟩
  unfold lrun
  rw [hj, iter_succ_true _ _ s h]
  exact iter_stable Inv (fun s => t (hd s)) g μ hinv hdec j (g s) (hinv s hI h) (by omega)

lemma PSp.loopI {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → S (g s) ≤ S s + c)
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s) :
    PSp Inv (.loop t p) (lrun t g μ) := by
  refine PSp.loop (c := c) t (lrun t g μ) μ hp hμ hinv hgrow
    (fun s _ h => lrun_false t g μ s h)
    (fun s hs h => ⟨hdec s hs h, lrun_true Inv t g μ hinv hdec s hs h⟩)

lemma lrun_rel (Inv : (K → List A) → Prop) (t : (K → Option A) → Bool)
    (g : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s)
    (Q : (K → List A) → (K → List A) → Prop)
    (hstop : ∀ s, Inv s → t (hd s) = false → Q s s)
    (hstep : ∀ s, Inv s → t (hd s) = true → Q (g s) (lrun t g μ (g s)) → Q s (lrun t g μ (g s))) :
    ∀ s, Inv s → Q s (lrun t g μ s) := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hI
  by_cases h : t (hd s) = true
  · rw [lrun_true Inv t g μ hinv hdec s hI h]
    exact hstep s hI h (ih (μ (g s)) (by have := hdec s hI h; omega) (g s) rfl (hinv s hI h))
  · have h' : t (hd s) = false := by simpa using h
    rw [lrun_false t g μ s h']
    exact hstop s hI h'

lemma PSp.loop1I {Inv : (K → List A) → Prop}
    (t : (K → Option A) → Bool) (f : (K → Option A) → K → StackAct A)
    (μ : (K → List A) → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (hdec : ∀ s, Inv s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s) :
    PSp Inv (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ) := by
  refine PSp.loopI (c := Fintype.card K) t μ (PSp.act f) hμ hinv ?_ hdec
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

lemma S_frame (R : Finset K) (s s' : K → List A) (h : ∀ k, k ∉ R → s' k = s k) :
    S s' + ∑ k ∈ R, (s k).length = S s + ∑ k ∈ R, (s' k).length := by
  unfold S
  have e : ∀ u : K → List A, ∑ k, (u k).length = ∑ k ∈ R, (u k).length + ∑ k ∈ Rᶜ, (u k).length := by
    intro u; rw [Finset.sum_add_sum_compl]
  rw [e s', e s]
  have : ∑ k ∈ Rᶜ, (s' k).length = ∑ k ∈ Rᶜ, (s k).length :=
    Finset.sum_congr rfl (fun k hk => by rw [h k (by simpa using hk)])
  omega

lemma len_le_S (s : K → List A) (k : K) : (s k).length ≤ S s :=
  Finset.single_le_sum (f := fun k => (s k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end Run
end Stk

end Sec_Stk4

section Sec_Stk5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP
namespace Stk
section Macros
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma sq_aux (x S' : ℕ) (h : x ≤ S') : 6 * x + 3 ≤ (S' + 2) ^ 2 := by
  have h2 : 2 * S' ≤ S' * S' + 1 := by
    zify; nlinarith [sq_nonneg ((S' : ℤ) - 1)]
  nlinarith

lemma PSp.push (Inv : (K → List A) → Prop) (r : K) (a : A) :
    PSp Inv (pushProg r a) (fun s => upd s r (a :: s r)) :=
  PSp.of_exec _ _ (fun _ => 1) 1 (fun s _ => (stack_basic_macros r s).1 a)
    (fun s _ => by simp)

lemma PSp.pop (Inv : (K → List A) → Prop) (r : K) :
    PSp Inv (popProg r) (fun s => upd s r (s r).tail) :=
  PSp.of_exec _ _ (fun _ => 1) 1 (fun s _ => (stack_basic_macros r s).2.1)
    (fun s _ => by simp)

lemma PSp.clear (Inv : (K → List A) → Prop) (r : K) :
    PSp Inv (clearProg r) (fun s => upd s r []) := by
  refine PSp.of_exec _ _ (fun s => 3 * (s r).length + 1) 2
    (fun s _ => (stack_basic_macros r s).2.2) (fun s _ => ?_)
  have := sq_aux _ _ (len_le_S s r)
  omega

lemma PSp.mvAll (Inv : (K → List A) → Prop) (a b : K) (hab : a ≠ b) :
    PSp Inv (transferProg a (fun k => decide (k = b)))
      (fun s => upd (upd s a []) b ((s a).reverse ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => 3 * (s a).length + 1) 2 (fun s _ => ?_) (fun s _ => ?_)
  · have := stack_transfer a (fun k => decide (k = b)) s
    convert this using 1
    funext k
    by_cases h1 : k = a
    · subst h1; simp [transferStore, upd, Function.update_apply, hab]
    · by_cases h2 : k = b
      · subst h2; simp [transferStore, upd, h1]
      · simp [transferStore, upd, h1, h2]
  · have := sq_aux _ _ (len_le_S s a)
    omega

lemma PSp.copy (Inv : (K → List A) → Prop) (a b c : K) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    PSp (fun s => Inv s ∧ s c = []) (copyProg a b c) (fun s => upd s b (s a ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => 6 * (s a).length + 3) 2 (fun s hs => ?_) (fun s _ => ?_)
  · exact stack_copy a b c hab hac hbc s hs.2
  · have := sq_aux _ _ (len_le_S s a)
    omega

def emb4 (a b c d : K) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : Fin 4 ↪ K :=
  ⟨![a, b, c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

lemma PSp.repcopy (Inv : (K → List A) → Prop) (a b c d : K) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    PSp (fun s => Inv s ∧ s d = []) (repeatCopyProg (emb4 a b c d hab hac had hbc hbd hcd))
      (fun s => upd (upd s c []) b ((List.replicate (s c).length (s a)).flatten ++ s b)) := by
  refine PSp.of_exec _ _ (fun s => (6 * (s a).length + 7) * (s c).length + 1) 3
    (fun s hs => ?_) (fun s _ => ?_)
  · exact stack_repeat_copy (emb4 a b c d hab hac had hbc hbd hcd) s hs.2
  · have h1 := len_le_S s a
    have h2 := len_le_S s c
    have h3 : (6 * (s a).length + 7) * (s c).length + 1 ≤ (6 * S s + 7) * S s + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul (by omega) h2) 1
    have h4 : (6 * S s + 7) * S s + 1 ≤ (S s + 2) ^ 3 := by
      zify; nlinarith [sq_nonneg ((S s : ℤ)), sq_nonneg ((S s : ℤ) - 1), Nat.zero_le (S s)]
    omega

lemma PSp.syncpop (Inv : (K → List A) → Prop) (i j : K) (hij : i ≠ j) :
    PSp Inv (syncPopProg i j)
      (fun s => upd (upd s i ((s i).drop (min (s i).length (s j).length)))
        j ((s j).drop (min (s i).length (s j).length))) := by
  refine PSp.of_exec _ _ (fun s => 3 * min (s i).length (s j).length + 1) 2
    (fun s _ => stack_sync_pop i j hij s) (fun s _ => ?_)
  have := sq_aux _ _ (le_trans (min_le_left (s i).length (s j).length) (len_le_S s i))
  omega

end Macros
end Stk

end Sec_Stk5

section Sec_TmNe
open CookPvsNP
set_option autoImplicit false

namespace Stk

inductive NQ | q0 | acc | rej
  deriving DecidableEq

instance : Fintype NQ where
  elems := {NQ.q0, NQ.acc, NQ.rej}
  complete := by intro x; cases x <;> simp

def neTM (Γ : Type) : TM Γ where
  Q := NQ
  q₀ := NQ.q0
  qaccept := NQ.acc
  qreject := NQ.rej
  accept_ne_reject := by decide
  δ := fun q s => match q with
    | NQ.q0 => ((if s.isSome then NQ.acc else NQ.rej), s, Move.right)
    | q => (q, s, Move.right)

lemma neTM_run (Γ : Type) (w : List Γ) (n : ℕ) :
    ((neTM Γ).run (n + 1) ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
  have h1 : ((neTM Γ).step ((neTM Γ).init w)).state = if w = [] then NQ.rej else NQ.acc := by
    cases w <;> simp [TM.step, TM.init, TM.IsHalting, neTM]
  have hfix : ∀ c : Cfg Γ (neTM Γ).Q, (c.state = NQ.acc ∨ c.state = NQ.rej) → (neTM Γ).step c = c := by
    intro c hc
    have : (neTM Γ).IsHalting c := hc
    unfold TM.step; rw [if_pos this]
  have hst : ∀ m, ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state =
      if w = [] then NQ.rej else NQ.acc := by
    intro m
    induction m with
    | zero => simpa [TM.run] using h1
    | succ m ih =>
      have h2 : (neTM Γ).run (m + 1 + 1) ((neTM Γ).init w) =
          (neTM Γ).step ((neTM Γ).run (m + 1) ((neTM Γ).init w)) := by
        simp only [TM.run]; rw [Function.iterate_succ_apply']
      rw [h2]
      have hh : ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.acc ∨
          ((neTM Γ).run (m + 1) ((neTM Γ).init w)).state = NQ.rej := by
        rw [ih]; split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
      exact (congrArg Cfg.state (hfix _ hh)).trans ih
  exact hst n

theorem neLang_mem_P (Γ : Type) [Fintype Γ] : {w : List Γ | w ≠ []} ∈ P Γ := by
  have e : ∀ w : List Γ, w.map (⇑(Function.Embedding.refl Γ)) = w := fun w => List.map_id w
  refine ⟨Γ, inferInstance, Function.Embedding.refl Γ, neTM Γ, 1, ?_, ?_⟩
  · intro w
    obtain ⟨m, hm⟩ : ∃ m, w.length ^ 1 + 1 = m + 1 := ⟨w.length, by simp⟩
    have := neTM_run Γ w m
    rw [e]
    unfold TM.HaltsWithin TM.IsHalting
    rw [hm]
    show _ = NQ.acc ∨ _ = NQ.rej
    rw [this]
    split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl
  · intro w
    rw [e]
    constructor
    · intro hw
      refine ⟨1, ?_⟩
      have := neTM_run Γ w 0
      rw [if_neg hw] at this
      exact this
    · rintro ⟨n, hn⟩ rfl
      cases n with
      | zero => exact absurd hn (by simp [TM.run, TM.init, neTM])
      | succ n =>
        have := neTM_run Γ ([] : List Γ) n
        rw [if_pos rfl] at this
        have h2 : NQ.rej = NQ.acc := this.symm.trans hn
        exact absurd h2 (by decide)

end Stk

end Sec_TmNe

section Sec_Ver1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

inductive Reg
  | 
IN  | WR  | W  | N  | K  | TR  | T  | TMP  | MB  | NB  | KB  | U  | F  | HU  | C  | RC  | BAD  | OUT  | KP  | NC  | PP  | TC  | T2  | K2  | TM  | NC2  | TT  | FP  | H  | MR  | KR  | LT
  deriving DecidableEq

instance : Fintype Reg where
  elems := {Reg.IN, Reg.WR, Reg.W, Reg.N, Reg.K, Reg.TR, Reg.T, Reg.TMP, Reg.MB, Reg.NB, Reg.KB, Reg.U, Reg.F, Reg.HU, Reg.C, Reg.RC, Reg.BAD, Reg.OUT, Reg.KP, Reg.NC, Reg.PP, Reg.TC, Reg.T2, Reg.K2, Reg.TM, Reg.NC2, Reg.TT, Reg.FP, Reg.H, Reg.MR, Reg.KR, Reg.LT}
  complete := by intro x; cases x <;> decide

abbrev Al : Type := Option (BSym ⊕ BSym)
abbrev St : Type := Reg → List Al
abbrev Prog : Type := StackProg Reg Al

def tk (b : BSym) : Al := some (Sum.inl b)
def ty (b : BSym) : Al := some (Sum.inr b)
def mk : Al := none

/-- test: top of `r` satisfies `p` -/
def topP (r : Reg) (p : Al → Bool) (h : Reg → Option Al) : Bool :=
  match h r with | some x => p x | none => false
def topS (r : Reg) (h : Reg → Option Al) : Bool := (h r).isSome
def topN (r : Reg) (h : Reg → Option Al) : Bool := (h r).isNone

/-- skip -/
def skipP : Prog := .act (fun _ _ => .keep)

lemma applyAct_keep (s : St) : StackProg.applyAct (fun _ _ => StackAct.keep) s = s := by
  funext k; simp [StackProg.applyAct, StackAct.apply]

def Gi (s : St) : Prop := s Reg.C = [] ∧ s Reg.RC = []

def wb (s : St) (c : ℕ) : St := upd s Reg.BAD (List.replicate c mk ++ s Reg.BAD)

lemma wb_apply (s : St) (c : ℕ) (r : Reg) :
    wb s c r = if r = Reg.BAD then List.replicate c mk ++ s Reg.BAD else s r := by
  simp [wb]

def badIf (t : (Reg → Option Al) → Bool) : Prog := .branch t (pushProg Reg.BAD mk) skipP

lemma PSp.skip (Inv : St → Prop) : PSp Inv skipP id := by
  have := PSp.act (Inv := Inv) (fun _ _ => (StackAct.keep : StackAct Al))
  refine PSp.congr this ?_
  intro s _
  exact applyAct_keep s

lemma PSp.badIf (Inv : St → Prop) (t : (Reg → Option Al) → Bool) :
    PSp Inv (badIf t) (fun s => if t (hd s) = true then wb s 1 else s) := by
  have h := PSp.branch (Inv := Inv) t (PSp.push Inv Reg.BAD mk) (PSp.skip Inv)
  refine PSp.congr h ?_
  intro s _
  simp [wb, mk]

end Stk

end Sec_Ver1

section Sec_Ver2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma mvw_eq (p : Al → Bool) : ∀ (a b : List Al),
    mvw p a b = (a.dropWhile p, (a.takeWhile p).reverse ++ b)
  | [], b => by simp [mvw]
  | x :: a, b => by
    unfold mvw
    by_cases h : p x = true
    · simp [h, mvw_eq p a (x :: b), List.takeWhile_cons_of_pos, List.dropWhile_cons_of_pos]
    · have h' : p x = false := by simpa using h
      simp [h']

def safe (r : Reg) : Prop := r ≠ Reg.C ∧ r ≠ Reg.RC

instance (r : Reg) : Decidable (safe r) := by unfold safe; infer_instance

def Gad (p : Prog) (g : St → St) : Prop := PSp Gi p g ∧ ∀ s, Gi s → Gi (g s)

lemma Gi_upd (s : St) (r : Reg) (l : List Al) (hr : safe r) (h : Gi s) : Gi (upd s r l) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨r1, r2⟩ := hr
  simp [Gi, upd_apply, r1, r2, r1.symm, r2.symm, h1, h2]

lemma Gad.seq {p q : Prog} {g h : St → St} (hp : Gad p g) (hq : Gad q h) :
    Gad (.seq p q) (fun s => h (g s)) :=
  ⟨PSp.seq hp.1 hq.1 hp.2, fun s hs => hq.2 _ (hp.2 s hs)⟩

lemma Gad.branch {p q : Prog} {g h : St → St} (t : (Reg → Option Al) → Bool)
    (hp : Gad p g) (hq : Gad q h) :
    Gad (.branch t p q) (fun s => if t (hd s) = true then g s else h s) :=
  ⟨PSp.branch t hp.1 hq.1, fun s hs => by
    by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact hp.2 s hs
    · simp only [ht, if_false]; exact hq.2 s hs⟩

lemma Gad.congr {p : Prog} {g g' : St → St} (h : Gad p g) (hg : ∀ s, Gi s → g s = g' s) :
    Gad p g' :=
  ⟨PSp.congr h.1 hg, fun s hs => by rw [← hg s hs]; exact h.2 s hs⟩

lemma Gad.skip : Gad skipP id := ⟨PSp.skip Gi, fun _ h => h⟩

lemma Gi_wb (s : St) (c : ℕ) (h : Gi s) : Gi (wb s c) := by
  unfold wb; exact Gi_upd s _ _ (by decide) h

lemma Gad.badIf (t : (Reg → Option Al) → Bool) :
    Gad (badIf t) (fun s => if t (hd s) = true then wb s 1 else s) :=
  ⟨PSp.badIf Gi t, fun s hs => by
    by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact Gi_wb s 1 hs
    · simp only [ht, if_false]; exact hs⟩

lemma Gad.push (r : Reg) (a : Al) (hr : safe r) :
    Gad (pushProg r a) (fun s => upd s r (a :: s r)) :=
  ⟨PSp.push Gi r a, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.pop (r : Reg) (hr : safe r) :
    Gad (popProg r) (fun s => upd s r (s r).tail) :=
  ⟨PSp.pop Gi r, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.clear (r : Reg) (hr : safe r) :
    Gad (clearProg r) (fun s => upd s r []) :=
  ⟨PSp.clear Gi r, fun s hs => Gi_upd s r _ hr hs⟩

lemma Gad.mvA (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) :
    Gad (transferProg a (fun k => decide (k = b)))
      (fun s => upd (upd s a []) b ((s a).reverse ++ s b)) :=
  ⟨PSp.mvAll Gi a b hab, fun s hs => Gi_upd _ _ _ hb (Gi_upd _ _ _ ha hs)⟩

lemma Gad.copy (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) :
    Gad (copyProg a b Reg.C) (fun s => upd s b (s a ++ s b)) := by
  refine ⟨?_, fun s hs => Gi_upd _ _ _ hb hs⟩
  have := PSp.copy Gi a b Reg.C hab ha.1 hb.1
  exact PSp.weaken this (fun s hs => ⟨hs, hs.1⟩)

lemma Gad.syncpop (i j : Reg) (hij : i ≠ j) (hi : safe i) (hj : safe j) :
    Gad (syncPopProg i j)
      (fun s => upd (upd s i ((s i).drop (min (s i).length (s j).length)))
        j ((s j).drop (min (s i).length (s j).length))) :=
  ⟨PSp.syncpop Gi i j hij, fun s hs => Gi_upd _ _ _ hj (Gi_upd _ _ _ hi hs)⟩

lemma Gad.mvP (a b : Reg) (hab : a ≠ b) (ha : safe a) (hb : safe b) (p : Al → Bool) :
    Gad (StackProg.loop (mvwT a p) (.act (mvwF a b)))
      (fun s => upd (upd s a ((s a).dropWhile p)) b (((s a).takeWhile p).reverse ++ s b)) := by
  obtain ⟨d, hd⟩ := ps_mvw a b hab p
  have h : Gad (StackProg.loop (mvwT a p) (.act (mvwF a b))) (mvwG a b p) :=
    ⟨⟨d, fun s _ => hd s⟩, fun s hs => by
      unfold mvwG; exact Gi_upd _ _ _ hb (Gi_upd _ _ _ ha hs)⟩
  refine Gad.congr h (fun s _ => ?_)
  simp [mvwG, mvw_eq]

end Stk

end Sec_Ver2

section Sec_Ver3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def isInl : Al → Bool | some (Sum.inl _) => true | _ => false
def isA (c : Al) : Al → Bool := fun a => decide (a = c)
def isBitY : Al → Bool := fun a => decide (a = ty BSym.zero ∨ a = ty BSym.one)
def isBitW : Al → Bool := fun a => decide (a = tk BSym.zero ∨ a = tk BSym.one)

def sq (p q : Prog) : Prog := .seq p q
def mvP (a b : Reg) (p : Al → Bool) : Prog := StackProg.loop (mvwT a p) (.act (mvwF a b))
def mvA (a b : Reg) : Prog := transferProg a (fun k => decide (k = b))
def popIf (r : Reg) (p : Al → Bool) : Prog := .branch (topP r p) (popProg r) (pushProg Reg.BAD mk)

def gMvP (a b : Reg) (p : Al → Bool) (s : St) : St :=
  upd (upd s a ((s a).dropWhile p)) b (((s a).takeWhile p).reverse ++ s b)
def gMvA (a b : Reg) (s : St) : St := upd (upd s a []) b ((s a).reverse ++ s b)
def gPopIf (r : Reg) (p : Al → Bool) (s : St) : St :=
  if topP r p (hd s) = true then upd s r (s r).tail else wb s 1
def gBadIf (t : (Reg → Option Al) → Bool) (s : St) : St := if t (hd s) = true then wb s 1 else s
def gPush (r : Reg) (a : Al) (s : St) : St := upd s r (a :: s r)
def gPop (r : Reg) (s : St) : St := upd s r (s r).tail
def gClear (r : Reg) (s : St) : St := upd s r []
def gCopy (a b : Reg) (s : St) : St := upd s b (s a ++ s b)

lemma gad_mvP (a b : Reg) (p : Al → Bool) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (mvP a b p) (gMvP a b p) := Gad.mvP a b hab ha hb p
lemma gad_mvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (mvA a b) (gMvA a b) := Gad.mvA a b hab ha hb
lemma gad_popIf (r : Reg) (p : Al → Bool) (hr : safe r := by decide) :
    Gad (popIf r p) (gPopIf r p) := by
  have h := Gad.branch (topP r p) (Gad.pop r hr) (Gad.push Reg.BAD mk (by decide))
  refine Gad.congr h (fun s _ => ?_)
  simp [gPopIf, wb, mk]
lemma gad_badIf (t : (Reg → Option Al) → Bool) : Gad (badIf t) (gBadIf t) := Gad.badIf t
lemma gad_push (r : Reg) (a : Al) (hr : safe r := by decide) :
    Gad (pushProg r a) (gPush r a) := Gad.push r a hr
lemma gad_pop (r : Reg) (hr : safe r := by decide) : Gad (popProg r) (gPop r) := Gad.pop r hr
lemma gad_clear (r : Reg) (hr : safe r := by decide) : Gad (clearProg r) (gClear r) :=
  Gad.clear r hr
lemma gad_copy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) : Gad (copyProg a b Reg.C) (gCopy a b) := Gad.copy a b hab ha hb


def Sticky (g : St → St) : Prop := ∀ s, s Reg.BAD ≠ [] → g s Reg.BAD ≠ []

def Gs (p : Prog) (g T : St → St) (ok : St → Prop) : Prop :=
  Gad p g ∧ Sticky g ∧ (∀ s, T s Reg.BAD = s Reg.BAD) ∧
    ∀ s, Gi s → s Reg.BAD = [] → ((g s Reg.BAD = [] ↔ ok s) ∧ (ok s → g s = T s))

lemma Gs.seq {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 : St → Prop}
    (h1 : Gs p g1 T1 ok1) (h2 : Gs q g2 T2 ok2) :
    Gs (.seq p q) (fun s => g2 (g1 s)) (fun s => T2 (T1 s)) (fun s => ok1 s ∧ ok2 (T1 s)) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.seq a1 a2, fun s hs => st2 _ (st1 s hs), fun s => by show T2 (T1 s) _ = _; rw [c2, c1], ?_⟩
  intro s hi hb
  obtain ⟨e1, f1⟩ := s1 s hi hb
  by_cases ho : ok1 s
  · have hg := f1 ho
    have hb' : T1 s Reg.BAD = [] := by rw [c1]; exact hb
    have hi' : Gi (T1 s) := by rw [← hg]; exact a1.2 s hi
    obtain ⟨e2, f2⟩ := s2 _ hi' hb'
    simp only [hg]
    exact ⟨by rw [e2]; simp [ho], fun h => f2 h.2⟩
  · have : g1 s Reg.BAD ≠ [] := fun h => ho (e1.1 h)
    refine ⟨?_, fun h => absurd h.1 ho⟩
    simp only
    constructor
    · intro h; exact absurd h (st2 _ this)
    · intro h; exact absurd h.1 ho

lemma Gs.branch {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 : St → Prop}
    (t : (Reg → Option Al) → Bool)
    (h1 : Gs p g1 T1 ok1) (h2 : Gs q g2 T2 ok2) :
    Gs (.branch t p q) (fun s => if t (hd s) = true then g1 s else g2 s)
      (fun s => if t (hd s) = true then T1 s else T2 s)
      (fun s => if t (hd s) = true then ok1 s else ok2 s) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.branch t a1 a2, fun s hs => ?_, fun s => ?_, fun s hi hb => ?_⟩
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact st1 s hs
    · simp only [ht, if_false]; exact st2 s hs
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact c1 s
    · simp only [ht, if_false]; exact c2 s
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact s1 s hi hb
    · simp only [ht, if_false]; exact s2 s hi hb

lemma Gs.congr {p : Prog} {g T T' : St → St} {ok ok' : St → Prop} (h : Gs p g T ok)
    (hT : ∀ s, Gi s → T s = T' s) (hok : ∀ s, Gi s → (ok s ↔ ok' s))
    (hT' : ∀ s, T' s Reg.BAD = s Reg.BAD) : Gs p g T' ok' := by
  obtain ⟨a, st, c, s⟩ := h
  refine ⟨a, st, hT', fun s' hi hb => ?_⟩
  obtain ⟨e, f⟩ := s s' hi hb
  exact ⟨by rw [e, hok s' hi], fun h => by rw [← hT s' hi]; exact f ((hok s' hi).2 h)⟩

lemma Gs.total {p : Prog} {g : St → St} (h : Gad p g) (hb : ∀ s, g s Reg.BAD = s Reg.BAD) :
    Gs p g g (fun _ => True) :=
  ⟨h, fun s hs => by rw [hb]; exact hs, hb, fun s _ h0 => ⟨by simp [hb, h0], fun _ => rfl⟩⟩

lemma gMvP_BAD (a b : Reg) (p : Al → Bool) (ha : a ≠ Reg.BAD) (hb : b ≠ Reg.BAD) (s : St) :
    gMvP a b p s Reg.BAD = s Reg.BAD := by simp [gMvP, upd_apply, ha, hb, ha.symm, hb.symm]
lemma gMvA_BAD (a b : Reg) (ha : a ≠ Reg.BAD) (hb : b ≠ Reg.BAD) (s : St) :
    gMvA a b s Reg.BAD = s Reg.BAD := by simp [gMvA, upd_apply, ha, hb, ha.symm, hb.symm]
lemma gPush_BAD (r : Reg) (a : Al) (hr : r ≠ Reg.BAD) (s : St) :
    gPush r a s Reg.BAD = s Reg.BAD := by simp [gPush, upd_apply, hr, hr.symm]
lemma gPop_BAD (r : Reg) (hr : r ≠ Reg.BAD) (s : St) :
    gPop r s Reg.BAD = s Reg.BAD := by simp [gPop, upd_apply, hr, hr.symm]
lemma gClear_BAD (r : Reg) (hr : r ≠ Reg.BAD) (s : St) :
    gClear r s Reg.BAD = s Reg.BAD := by simp [gClear, upd_apply, hr, hr.symm]
lemma gCopy_BAD (a b : Reg) (hb : b ≠ Reg.BAD) (s : St) :
    gCopy a b s Reg.BAD = s Reg.BAD := by simp [gCopy, upd_apply, hb, hb.symm]

lemma gs_mvP (a b : Reg) (p : Al → Bool) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (mvP a b p) (gMvP a b p) (gMvP a b p) (fun _ => True) :=
  Gs.total (gad_mvP a b p hab ha hb) (gMvP_BAD a b p ha' hb')
lemma gs_mvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (mvA a b) (gMvA a b) (gMvA a b) (fun _ => True) :=
  Gs.total (gad_mvA a b hab ha hb) (gMvA_BAD a b ha' hb')
lemma gs_push (r : Reg) (a : Al) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (pushProg r a) (gPush r a) (gPush r a) (fun _ => True) :=
  Gs.total (gad_push r a hr) (gPush_BAD r a hr')
lemma gs_pop (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (popProg r) (gPop r) (gPop r) (fun _ => True) :=
  Gs.total (gad_pop r hr) (gPop_BAD r hr')
lemma gs_clear (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (clearProg r) (gClear r) (gClear r) (fun _ => True) :=
  Gs.total (gad_clear r hr) (gClear_BAD r hr')
lemma gs_copy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (hb' : b ≠ Reg.BAD := by decide) :
    Gs (copyProg a b Reg.C) (gCopy a b) (gCopy a b) (fun _ => True) :=
  Gs.total (gad_copy a b hab ha hb) (gCopy_BAD a b hb')

lemma gs_badIf (t : (Reg → Option Al) → Bool) :
    Gs (badIf t) (gBadIf t) id (fun s => t (hd s) = false) := by
  refine ⟨gad_badIf t, fun s hs => ?_, fun _ => rfl, fun s _ hb => ?_⟩
  · unfold gBadIf; split_ifs <;> simp [wb, hs]
  · unfold gBadIf
    by_cases ht : t (hd s) = true
    · simp [ht, wb, hb]
    · have : t (hd s) = false := by simpa using ht
      simp [this, hb]

lemma gs_popIf (r : Reg) (p : Al → Bool) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) :
    Gs (popIf r p) (gPopIf r p) (gPop r) (fun s => topP r p (hd s) = true) := by
  refine ⟨gad_popIf r p hr, fun s hs => ?_, gPop_BAD r hr', fun s _ hb => ?_⟩
  · unfold gPopIf; split_ifs <;> simp [wb, upd_apply, hs, hr', hr'.symm]
  · unfold gPopIf
    by_cases ht : topP r p (hd s) = true
    · simp [ht, gPop, hb, upd_apply, hr', hr'.symm]
    · simp [ht, wb, hb, mk]

end Stk

end Sec_Ver3

section Sec_Ver4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def init (x : List Al) : St := fun r => if r = Reg.IN then x else []
lemma Gi_init (x : List Al) : Gi (init x) := by simp [Gi, init]

def tyb (b : Bool) : Al := ty (if b then BSym.one else BSym.zero)
def tkb (b : Bool) : Al := tk (if b then BSym.one else BSym.zero)

lemma pre_split {p : Al → Bool} {A rest : List Al} (hA : ∀ a ∈ A, p a = true)
    (hr : ∀ a, rest.head? = some a → p a = false) :
    (A ++ rest).takeWhile p = A ∧ (A ++ rest).dropWhile p = rest := by
  refine ⟨?_, List.dropWhile_append_of_pos hA |>.trans ?_⟩
  · rw [List.takeWhile_append_of_pos hA]
    cases rest with
    | nil => simp
    | cons a r => simp [hr a rfl]
  · cases rest with
    | nil => simp
    | cons a r => simp [hr a rfl]

lemma tw_split (p : Al → Bool) (l : List Al) :
    l = l.takeWhile p ++ l.dropWhile p ∧ (∀ a ∈ l.takeWhile p, p a = true) :=
  ⟨List.takeWhile_append_dropWhile.symm, fun _ h => List.mem_takeWhile_imp h⟩

lemma isA_iff {c a : Al} : isA c a = true ↔ a = c := by simp [isA]

lemma rep_of_all {c : Al} {l : List Al} (h : ∀ a ∈ l, isA c a = true) :
    l = List.replicate l.length c :=
  List.eq_replicate_iff.2 ⟨rfl, fun b hb => isA_iff.1 (h b hb)⟩

lemma bits_of_all {l : List Al} (h : ∀ a ∈ l, isBitY a = true) : ∃ t : List Bool, l = t.map tyb := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    simp only [isBitY, decide_eq_true_eq] at ha
    rcases ha with ha | ha
    · exact ⟨false :: t, by simp [tyb, ha, ht]⟩
    · exact ⟨true :: t, by simp [tyb, ha, ht]⟩

lemma inl_of_all {l : List Al} (h : ∀ a ∈ l, isInl a = true) : ∃ w : List BSym, l = w.map tk := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a r ih =>
    obtain ⟨t, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a (List.mem_cons_self ..)
    cases a with
    | none => simp [isInl] at ha
    | some v =>
      cases v with
      | inl b => exact ⟨b :: t, by simp [tk, ht]⟩
      | inr b => simp [isInl] at ha


def Fm (w : List BSym) (a b : ℕ) (t : List Bool) : List Al :=
  w.map tk ++ mk :: (List.replicate a (ty BSym.sep) ++ List.replicate b (ty BSym.minus) ++ t.map tyb)

def stA : Prog :=
  sq (mvP Reg.IN Reg.WR isInl) <| sq (popIf Reg.IN (isA mk)) <| sq (mvA Reg.WR Reg.W) <|
  sq (mvP Reg.IN Reg.N (isA (ty BSym.sep))) <| sq (mvP Reg.IN Reg.K (isA (ty BSym.minus))) <|
  sq (mvP Reg.IN Reg.TR isBitY) <| sq (mvA Reg.TR Reg.T) <| badIf (topS Reg.IN)

def A1 (s : St) : St := gMvP Reg.IN Reg.WR isInl s
def A2 (s : St) : St := gPop Reg.IN (A1 s)
def A3 (s : St) : St := gMvA Reg.WR Reg.W (A2 s)
def A4 (s : St) : St := gMvP Reg.IN Reg.N (isA (ty BSym.sep)) (A3 s)
def A5 (s : St) : St := gMvP Reg.IN Reg.K (isA (ty BSym.minus)) (A4 s)
def A6 (s : St) : St := gMvP Reg.IN Reg.TR isBitY (A5 s)
def A7 (s : St) : St := gMvA Reg.TR Reg.T (A6 s)
def okA (s : St) : Prop := topP Reg.IN (isA mk) (hd (A1 s)) = true ∧ topS Reg.IN (hd (A7 s)) = false

def gA : St → St := fun s =>
  gBadIf (topS Reg.IN) (gMvA Reg.TR Reg.T (gMvP Reg.IN Reg.TR isBitY (
  gMvP Reg.IN Reg.K (isA (ty BSym.minus)) (gMvP Reg.IN Reg.N (isA (ty BSym.sep)) (
  gMvA Reg.WR Reg.W (gPopIf Reg.IN (isA mk) (gMvP Reg.IN Reg.WR isInl s)))))))

lemma gs_stA : Gs stA gA A7 okA := by
  have h := Gs.seq (gs_mvP Reg.IN Reg.WR isInl) <|
    Gs.seq (gs_popIf Reg.IN (isA mk)) <|
    Gs.seq (gs_mvA Reg.WR Reg.W) <|
    Gs.seq (gs_mvP Reg.IN Reg.N (isA (ty BSym.sep))) <|
    Gs.seq (gs_mvP Reg.IN Reg.K (isA (ty BSym.minus))) <|
    Gs.seq (gs_mvP Reg.IN Reg.TR isBitY) <|
    Gs.seq (gs_mvA Reg.TR Reg.T) <|
    gs_badIf (topS Reg.IN)
  refine Gs.congr (p := stA) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp only [okA, A1, A2, A3, A4, A5, A6, A7, id]; tauto
  · simp [A7, A6, A5, A4, A3, A2, A1, gMvA, gMvP, gPop, upd_apply]


def stateA (w : List BSym) (a b : ℕ) (t : List Bool) : St := fun r =>
  match r with
  | Reg.W => w.map tk
  | Reg.N => List.replicate a (ty BSym.sep)
  | Reg.K => List.replicate b (ty BSym.minus)
  | Reg.T => t.map tyb
  | _ => []

lemma isInl_tk (b : BSym) : isInl (tk b) = true := by simp [tk, isInl]
lemma isA_self (c : Al) : isA c c = true := by simp [isA]
lemma isBitY_tyb (b : Bool) : isBitY (tyb b) = true := by cases b <;> simp [isBitY, tyb]

lemma stA_dec (x : List Al) :
    (okA (init x) → ∃ w a b t, x = Fm w a b t) := by
  intro ⟨h1, h2⟩
  simp only [A1, A2, A3, A4, A5, A6, A7, gMvP, gMvA, gPop, topP, topS, hd, init, upd_apply] at h1 h2
  simp at h1 h2
  obtain ⟨hx0, hw0⟩ := tw_split isInl x
  obtain ⟨w, hw⟩ := inl_of_all hw0
  generalize List.dropWhile isInl x = r1 at h1 h2 hx0
  cases r1 with
  | nil => simp at h1
  | cons c r2 =>
    simp only [List.head?_cons, isA_iff] at h1
    have hc : c = mk := h1
    subst hc
    obtain ⟨hx1, hs1⟩ := tw_split (isA (ty BSym.sep)) r2
    obtain ⟨hx2, hs2⟩ := tw_split (isA (ty BSym.minus)) (r2.dropWhile (isA (ty BSym.sep)))
    obtain ⟨tt, htt⟩ := bits_of_all h2
    simp only [List.tail_cons] at h2
    refine ⟨w, (r2.takeWhile (isA (ty BSym.sep))).length, ((r2.dropWhile (isA (ty BSym.sep))).takeWhile (isA (ty BSym.minus))).length, tt, ?_⟩
    rw [rep_of_all hs1] at hx1
    rw [rep_of_all hs2] at hx2
    unfold Fm
    rw [← htt, ← hw]
    rw [hx0]
    congr 2
    conv_lhs => rw [hx1, hx2]
    simp


lemma tyb_ne_sep (b : Bool) : isA (ty BSym.sep) (tyb b) = false := by cases b <;> simp [isA, tyb, ty]
lemma tyb_ne_minus (b : Bool) : isA (ty BSym.minus) (tyb b) = false := by cases b <;> simp [isA, tyb, ty]
lemma minus_ne_sep : isA (ty BSym.sep) (ty BSym.minus) = false := by simp [isA, ty]
lemma isInl_mk : isInl mk = false := by simp [mk, isInl]
lemma sep_isBitY : isBitY (ty BSym.sep) = false := by simp [isBitY, ty]
lemma minus_isBitY : isBitY (ty BSym.minus) = false := by simp [isBitY, ty]

lemma stA_eval (w : List BSym) (a b : ℕ) (t : List Bool) :
    okA (init (Fm w a b t)) ∧ A7 (init (Fm w a b t)) = stateA w a b t := by
  have e1 : (Fm w a b t).takeWhile isInl = w.map tk ∧ (Fm w a b t).dropWhile isInl =
      mk :: (List.replicate a (ty BSym.sep) ++ List.replicate b (ty BSym.minus) ++ t.map tyb) := by
    unfold Fm
    exact pre_split (fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isInl_tk y) (fun x hx => by
      simp only [List.head?_cons, Option.some.injEq] at hx; subst hx; exact isInl_mk)
  have e2 : (List.replicate a (ty BSym.sep) ++ (List.replicate b (ty BSym.minus) ++ t.map tyb)).takeWhile
      (isA (ty BSym.sep)) = List.replicate a (ty BSym.sep) ∧
      (List.replicate a (ty BSym.sep) ++ (List.replicate b (ty BSym.minus) ++ t.map tyb)).dropWhile
      (isA (ty BSym.sep)) = List.replicate b (ty BSym.minus) ++ t.map tyb := by
    refine pre_split (fun x hx => (isA_iff).2 (List.eq_of_mem_replicate hx)) (fun x hx => ?_)
    cases b with
    | zero =>
      cases t with
      | nil => simp at hx
      | cons c r => simp at hx; subst hx; exact tyb_ne_sep c
    | succ b => simp [List.replicate_succ] at hx; subst hx; exact minus_ne_sep
  have e3 : (List.replicate b (ty BSym.minus) ++ t.map tyb).takeWhile (isA (ty BSym.minus))
      = List.replicate b (ty BSym.minus) ∧
      (List.replicate b (ty BSym.minus) ++ t.map tyb).dropWhile (isA (ty BSym.minus)) = t.map tyb := by
    refine pre_split (fun x hx => (isA_iff).2 (List.eq_of_mem_replicate hx)) (fun x hx => ?_)
    cases t with
    | nil => simp at hx
    | cons c r => simp at hx; subst hx; exact tyb_ne_minus c
  have e4 : (t.map tyb).takeWhile isBitY = t.map tyb ∧ (t.map tyb).dropWhile isBitY = [] := by
    constructor
    · exact List.takeWhile_eq_self_iff.2 (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isBitY_tyb y)
    · exact List.dropWhile_eq_nil_iff.2 (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; exact isBitY_tyb y)
  have hA7 : A7 (init (Fm w a b t)) = stateA w a b t := by
    funext r
    cases r <;> simp [A7, A6, A5, A4, A3, A2, A1, gMvA, gMvP, gPop, init, upd_apply, stateA,
      e1.1, e1.2, e2.1, e3.1, e3.2, e4.1, e4.2, List.append_assoc, e2.2, List.reverse_replicate]
  refine ⟨⟨?_, ?_⟩, hA7⟩
  · simp [A1, gMvP, topP, hd, init, upd_apply, e1.2, isA_self]
  · rw [hA7]; simp [stateA, topS, hd]

end Stk

end Sec_Ver4

section Sec_Ver5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def bsb (b : Bool) : BSym := if b then BSym.one else BSym.zero
def encB (bl : List Bool) : List BSym := bl.map bsb ++ [BSym.sep]

lemma tkb_eq (b : Bool) : tkb b = tk (bsb b) := by simp [tkb, bsb]

def stNum (X : Reg) : Prog :=
  sq (mvP Reg.W Reg.TMP isBitW) <| sq (popIf Reg.W (isA (tk BSym.sep))) <| mvA Reg.TMP X

def B1 (s : St) : St := gMvP Reg.W Reg.TMP isBitW s
def B2 (s : St) : St := gPop Reg.W (B1 s)
def B3 (X : Reg) (s : St) : St := gMvA Reg.TMP X (B2 s)
def okNum (s : St) : Prop := topP Reg.W (isA (tk BSym.sep)) (hd (B1 s)) = true

lemma gs_stNum (X : Reg) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : Gs (stNum X) (fun s => gMvA Reg.TMP X (gPopIf Reg.W
      (isA (tk BSym.sep)) (gMvP Reg.W Reg.TMP isBitW s))) (B3 X) okNum := by
  have h := Gs.seq (gs_mvP Reg.W Reg.TMP isBitW) <|
    Gs.seq (gs_popIf Reg.W (isA (tk BSym.sep))) <|
      gs_mvA Reg.TMP X hX2 (by decide) hX (by decide) hX'
  refine Gs.congr (p := stNum X) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp [okNum, B1]
  · simp [B3, B2, B1, gMvA, gMvP, gPop, upd_apply, hX'.symm]

end Stk

end Sec_Ver5

section Sec_Ver6
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma Gad.loopG {p : Prog} {g : St → St} {c : ℕ} (hp : Gad p g)
    (t : (Reg → Option Al) → Bool) (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hgrow : ∀ s, Gi s → t (hd s) = true → S (g s) ≤ S s + c)
    (hdec : ∀ s, Gi s → t (hd s) = true → μ (g s) < μ s) :
    Gad (.loop t p) (lrun t g μ) := by
  refine ⟨PSp.loopI (c := c) t μ hp.1 hμ (fun s hs _ => hp.2 s hs) hgrow hdec, ?_⟩
  have := lrun_rel Gi t g μ (fun s hs _ => hp.2 s hs) hdec (fun s s' => Gi s')
    (fun s hs _ => hs) (fun s hs _ h => h)
  exact this

lemma Gad.loop1 (t : (Reg → Option Al) → Bool) (f : (Reg → Option Al) → Reg → StackAct Al)
    (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hC : ∀ h, f h Reg.C = StackAct.keep) (hRC : ∀ h, f h Reg.RC = StackAct.keep)
    (hdec : ∀ s, Gi s → t (hd s) = true → μ (StackProg.applyAct f s) < μ s) :
    Gad (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ) := by
  have hg : Gad (.act f) (StackProg.applyAct f) := by
    refine ⟨PSp.act f, fun s hs => ?_⟩
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, ?_⟩
    · simp [StackProg.applyAct, hC, StackAct.apply, h1]
    · simp [StackProg.applyAct, hRC, StackAct.apply, h2]
  refine Gad.loopG (c := Fintype.card Reg) hg t μ hμ ?_ hdec
  intro s _ _
  have := Exec_size (StackProg.Exec.act f s)
  omega

/-! halving -/
def hfAct : (Reg → Option Al) → Reg → StackAct Al := fun h k =>
  match k with
  | Reg.U => .pop
  | Reg.F => match h Reg.F with | none => .push mk | some _ => .pop
  | Reg.HU => match h Reg.F with | none => .keep | some _ => .push mk
  | _ => .keep

def halve : Prog := .loop (topS Reg.U) (.act hfAct)
def hfStep : St → St := StackProg.applyAct hfAct
def hfRun : St → St := lrun (topS Reg.U) hfStep (fun s => (s Reg.U).length)

lemma gad_halve : Gad halve hfRun := by
  refine Gad.loop1 (topS Reg.U) hfAct (fun s => (s Reg.U).length) (fun s => len_le_S s Reg.U)
    (fun h => rfl) (fun h => rfl) ?_
  intro s _ ht
  simp only [topS, hd, Option.isSome_iff_exists] at ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
    cases h : s Reg.U with
    | nil => simp [h] at ha
    | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
  simp [StackProg.applyAct, hfAct, StackAct.apply, hl]


def HI (s : St) : Prop := ∃ f, f ≤ 1 ∧ s Reg.F = List.replicate f mk

def hfRes (s : St) : St :=
  upd (upd (upd s Reg.U []) Reg.F (List.replicate (((s Reg.U).length + (s Reg.F).length) % 2) mk))
    Reg.HU (List.replicate (((s Reg.U).length + (s Reg.F).length) / 2) mk ++ s Reg.HU)

lemma hf_step0 (s : St) (a : Al) (l : List Al) (hl : s Reg.U = a :: l) (hF : s Reg.F = []) :
    hfStep s = upd (upd s Reg.U l) Reg.F [mk] := by
  funext k
  cases k <;> simp [hfStep, StackProg.applyAct, hfAct, StackAct.apply, hl, hF, hd]

lemma hf_step1 (s : St) (a : Al) (l : List Al) (hl : s Reg.U = a :: l) (b : Al) (r : List Al)
    (hF : s Reg.F = b :: r) :
    hfStep s = upd (upd (upd s Reg.U l) Reg.F r) Reg.HU (mk :: s Reg.HU) := by
  funext k
  cases k <;> simp [hfStep, StackProg.applyAct, hfAct, StackAct.apply, hl, hF, hd]

lemma hfRun_sem : ∀ s, HI s → hfRun s = hfRes s := by
  have key : ∀ s, HI s → (topS Reg.U) (hd s) = true → HI (hfStep s) ∧
      (s Reg.U).length ≥ 1 ∧ ((hfStep s) Reg.U).length < (s Reg.U).length ∧ hfRes (hfStep s) = hfRes s := by
    intro s ⟨f, hf, hF⟩ ht
    simp only [topS, hd, Option.isSome_iff_exists] at ht
    obtain ⟨a, ha⟩ := ht
    obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
      cases h : s Reg.U with
      | nil => simp [h] at ha
      | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
    have hfl : f = 0 ∨ f = 1 := by omega
    rcases hfl with rfl | rfl
    · rw [hf_step0 s a l hl (by simpa using hF)]
      refine ⟨⟨1, le_rfl, by simp⟩, by simp [hl], by simp [hl], ?_⟩
      funext k
      simp only [hfRes, upd_apply, hl, hF]
      split_ifs <;> simp_all <;> omega
    · rw [hf_step1 s a l hl mk [] (by simpa using hF)]
      refine ⟨⟨0, by omega, by simp⟩, by simp [hl], by simp [hl], ?_⟩
      funext k
      simp only [hfRes, upd_apply, hl, hF]
      split_ifs <;> simp_all
      · have : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
        rw [this, List.replicate_succ']; simp
      · omega
  have := lrun_rel HI (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun s hs ht => (key s hs ht).1) (fun s hs ht => (key s hs ht).2.2.1)
    (fun s s' => HI s → s' = hfRes s) ?_ ?_
  · exact fun s hs => this s hs hs
  · intro s hs ht hs'
    obtain ⟨f, hf, hF⟩ := hs
    simp only [topS, hd] at ht
    have hU : s Reg.U = [] := by
      cases h : s Reg.U with
      | nil => rfl
      | cons b l => simp [h] at ht
    funext k
    simp only [hfRes, upd_apply, hU, hF]
    have hfl : f = 0 ∨ f = 1 := by omega
    rcases hfl with rfl | rfl <;> (split_ifs <;> simp_all)
  · intro s hs ht ih hs'
    obtain ⟨h1, h2, h3, h4⟩ := key s hs ht
    rw [ih h1, h4]

end Stk

end Sec_Ver6

section Sec_Ver7
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def GsP (p : Prog) (g T : St → St) (ok pre : St → Prop) : Prop :=
  Gad p g ∧ Sticky g ∧ (∀ s, T s Reg.BAD = s Reg.BAD) ∧
    ∀ s, Gi s → pre s → s Reg.BAD = [] → ((g s Reg.BAD = [] ↔ ok s) ∧ (ok s → g s = T s))

lemma Gs.toP {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) (pre : St → Prop) :
    GsP p g T ok pre :=
  ⟨h.1, h.2.1, h.2.2.1, fun s hi _ hb => h.2.2.2 s hi hb⟩

lemma GsP.ofTrue {p : Prog} {g T : St → St} {ok : St → Prop} (h : GsP p g T ok (fun _ => True)) :
    Gs p g T ok :=
  ⟨h.1, h.2.1, h.2.2.1, fun s hi hb => h.2.2.2 s hi trivial hb⟩

lemma GsP.seq {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 pre1 pre2 : St → Prop}
    (h1 : GsP p g1 T1 ok1 pre1) (h2 : GsP q g2 T2 ok2 pre2)
    (hpre : ∀ s, Gi s → pre1 s → s Reg.BAD = [] → ok1 s → pre2 (T1 s)) :
    GsP (.seq p q) (fun s => g2 (g1 s)) (fun s => T2 (T1 s)) (fun s => ok1 s ∧ ok2 (T1 s)) pre1 := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.seq a1 a2, fun s hs => st2 _ (st1 s hs), fun s => by show T2 (T1 s) _ = _; rw [c2, c1], ?_⟩
  intro s hi hp hb
  obtain ⟨e1, f1⟩ := s1 s hi hp hb
  by_cases ho : ok1 s
  · have hg := f1 ho
    have hb' : T1 s Reg.BAD = [] := by rw [c1]; exact hb
    have hi' : Gi (T1 s) := by rw [← hg]; exact a1.2 s hi
    obtain ⟨e2, f2⟩ := s2 _ hi' (hpre s hi hp hb ho) hb'
    simp only [hg]
    exact ⟨by rw [e2]; simp [ho], fun h => f2 h.2⟩
  · have : g1 s Reg.BAD ≠ [] := fun h => ho (e1.1 h)
    refine ⟨?_, fun h => absurd h.1 ho⟩
    simp only
    constructor
    · intro h; exact absurd h (st2 _ this)
    · intro h; exact absurd h.1 ho

lemma GsP.congr {p : Prog} {g T T' : St → St} {ok ok' pre pre' : St → Prop} (h : GsP p g T ok pre)
    (hT : ∀ s, Gi s → pre s → T s = T' s) (hok : ∀ s, Gi s → pre s → (ok s ↔ ok' s))
    (hpre : ∀ s, Gi s → pre' s → pre s)
    (hT' : ∀ s, T' s Reg.BAD = s Reg.BAD) : GsP p g T' ok' pre' := by
  obtain ⟨a, st, c, s⟩ := h
  refine ⟨a, st, hT', fun s' hi hp hb => ?_⟩
  have hp' := hpre s' hi hp
  obtain ⟨e, f⟩ := s s' hi hp' hb
  exact ⟨by rw [e, hok s' hi hp'], fun h => by rw [← hT s' hi hp']; exact f ((hok s' hi hp').2 h)⟩

end Stk

end Sec_Ver7

section Sec_Ver8
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def mmT (X : Reg) (h : Reg → Option Al) : Bool :=
  match h X with
  | some x => decide (x ≠ (if (h Reg.F).isSome then tkb true else tkb false))
  | none => false

def eqBody (X : Reg) : Prog :=
  sq (badIf (topN Reg.U)) <| sq halve <| sq (mvA Reg.HU Reg.U) <| sq (badIf (mmT X)) <|
  sq (popProg X) (popProg Reg.F)

def gEqB (X : Reg) (s : St) : St :=
  gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))))

lemma gad_eqBody (X : Reg) (hX : safe X := by decide) : Gad (eqBody X) (gEqB X) := by
  have h := Gad.seq (gad_badIf (topN Reg.U)) <| Gad.seq gad_halve <|
    Gad.seq (gad_mvA Reg.HU Reg.U) <| Gad.seq (gad_badIf (mmT X)) <|
    Gad.seq (gad_pop X hX) (gad_pop Reg.F)
  exact h

def eqc (X : Reg) (s : St) (x : Al) : ℕ :=
  (if s Reg.U = [] then 1 else 0) +
  (if x ≠ tkb (decide ((s Reg.U).length % 2 = 1)) then 1 else 0)

lemma gEqB_formula (X : Reg) (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (s : St) (hF : s Reg.F = []) (hH : s Reg.HU = []) (x : Al) (X' : List Al)
    (hx : s X = x :: X') :
    gEqB X s = upd (upd (upd s Reg.BAD (List.replicate (eqc X s x) mk ++ s Reg.BAD)) Reg.U
      (List.replicate ((s Reg.U).length / 2) mk)) X X' := by
  have e1 : ∀ r, gBadIf (topN Reg.U) s r = if r = Reg.BAD then List.replicate (if s Reg.U = [] then 1 else 0) mk ++ s Reg.BAD else s r := by
    intro r
    unfold gBadIf
    by_cases hU : s Reg.U = []
    · simp [topN, hd, hU, wb_apply]
    · simp [topN, hd, hU]; rintro rfl; rfl
  have hI : HI (gBadIf (topN Reg.U) s) := ⟨0, by omega, by simp [e1, hF]⟩
  have e2 := hfRun_sem _ hI
  set u := (s Reg.U).length with hu
  have e3 : ∀ r, gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)) r =
      if r = Reg.BAD then List.replicate (if s Reg.U = [] then 1 else 0) mk ++ s Reg.BAD
      else if r = Reg.U then List.replicate (u / 2) mk
      else if r = Reg.F then List.replicate (u % 2) mk
      else if r = Reg.HU then [] else s r := by
    intro r
    rw [e2]
    cases r <;> simp [gMvA, hfRes, upd_apply, e1, hF, hH, hu]
  show gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s))))) = _
  generalize gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)) = E at e3 ⊢
  have eX : E X = x :: X' := by
    rw [e3 X]; simp [hXU, hXF, hXH, hXB, hx]
  have hm : mmT X (hd E) = decide (x ≠ tkb (decide (u % 2 = 1))) := by
    simp only [mmT, hd, eX, e3]
    simp [hXU, hXF, hXH, hXB]
    rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
    · simp [h0]
    · simp [h1]
  have hcl : eqc X s x = (if s Reg.U = [] then 1 else 0) + (if x ≠ tkb (decide (u % 2 = 1)) then 1 else 0) := rfl
  have hF' : E Reg.F = List.replicate (u % 2) mk := by rw [e3]; simp
  have hF'' : (E Reg.F).tail = [] := by
    rw [hF']; rcases Nat.mod_two_eq_zero_or_one u with h0 | h1
    · simp [h0]
    · simp [h1]
  unfold gBadIf
  rw [hm]
  funext r
  by_cases hrX : r = X
  · subst hrX
    by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
      simp [gPop, hxe, eX, upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, wb_apply, hF, hH]
  · by_cases hrF : r = Reg.F
    · subst hrF
      by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
        simp [gPop, hxe, upd_apply, hrX, hXF.symm, wb_apply, hF'', hF, hH]
    · have hrX' : ¬ X = r := fun h => hrX h.symm
      by_cases hxe : x = tkb (decide (u % 2 = 1)) <;>
      by_cases hrU : r = Reg.U <;> by_cases hrB : r = Reg.BAD <;> by_cases hrH : r = Reg.HU <;>
      simp_all [gPop, upd_apply, wb_apply, e3, eqc, mk, hF, hH, List.replicate_succ]
end Stk

end Sec_Ver8

section Sec_Ver9
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma hfStep_cases (s : St) (h : (topS Reg.U) (hd s) = true) :
    ∃ a l, s Reg.U = a :: l ∧
      ((s Reg.F = [] ∧ hfStep s = upd (upd s Reg.U l) Reg.F [mk]) ∨
       (∃ b r, s Reg.F = b :: r ∧
         hfStep s = upd (upd (upd s Reg.U l) Reg.F r) Reg.HU (mk :: s Reg.HU))) := by
  simp only [topS, hd, Option.isSome_iff_exists] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨l, hl⟩ : ∃ l, s Reg.U = a :: l := by
    cases h : s Reg.U with
    | nil => simp [h] at ha
    | cons b l => simp [h] at ha; exact ⟨l, by simp [ha]⟩
  refine ⟨a, l, hl, ?_⟩
  cases hF : s Reg.F with
  | nil => exact Or.inl ⟨rfl, hf_step0 s a l hl hF⟩
  | cons b r => exact Or.inr ⟨b, r, rfl, hf_step1 s a l hl b r hF⟩

lemma hfRun_frame (r : Reg) (h1 : r ≠ Reg.U) (h2 : r ≠ Reg.F) (h3 : r ≠ Reg.HU) :
    ∀ s : St, hfRun s r = s r := by
  have := lrun_rel (fun _ : St => True) (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, hl])
    (fun s s' => s' r = s r) (fun _ _ _ => rfl)
    (fun s _ ht ih => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, h1, h2, h3] at ih ⊢ <;> exact ih)
  exact fun s => this s trivial

lemma S_hfRun_le : ∀ s : St, S (hfRun s) ≤ S s := by
  have := lrun_rel (fun _ : St => True) (topS Reg.U) hfStep (fun s => (s Reg.U).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      rcases h with ⟨_, e⟩ | ⟨b, r', _, e⟩ <;> simp [e, hl])
    (fun s s' => S s' ≤ S s) (fun _ _ _ => le_rfl)
    (fun s _ ht ih => by
      obtain ⟨a, l, hl, h⟩ := hfStep_cases s ht
      have : S (hfStep s) ≤ S s := by
        rcases h with ⟨hF, e⟩ | ⟨b, r', hF, e⟩
        · rw [e]
          have := S_upd (upd s Reg.U l) Reg.F [mk]
          have := S_upd s Reg.U l
          simp [hl, hF] at *; omega
        · rw [e]
          have h1 := S_upd (upd (upd s Reg.U l) Reg.F r') Reg.HU (mk :: s Reg.HU)
          have h2 := S_upd (upd s Reg.U l) Reg.F r'
          have h3 := S_upd s Reg.U l
          simp [hl, hF] at *; omega
      omega)
  exact fun s => this s trivial

lemma S_gBadIf (t : (Reg → Option Al) → Bool) (s : St) : S (gBadIf t s) ≤ S s + 1 := by
  unfold gBadIf
  split_ifs
  · have := S_upd s Reg.BAD (List.replicate 1 mk ++ s Reg.BAD)
    simp [wb] at *; omega
  · omega

lemma S_gMvA (a b : Reg) (hab : a ≠ b) (s : St) : S (gMvA a b s) ≤ S s := by
  unfold gMvA
  have h1 := S_upd (upd s a []) b ((s a).reverse ++ s b)
  have h2 := S_upd s a []
  simp [hab.symm] at *; omega

lemma S_gPop (r : Reg) (s : St) : S (gPop r s) ≤ S s := by
  unfold gPop
  have := S_upd s r (s r).tail
  have := List.length_tail (l := s r)
  omega

lemma S_gEqB (X : Reg) (hXU : X ≠ Reg.U := by decide) (s : St) : S (gEqB X s) ≤ S s + 2 := by
  unfold gEqB
  have a1 := S_gBadIf (topN Reg.U) s
  have a2 := S_hfRun_le (gBadIf (topN Reg.U) s)
  have a3 := S_gMvA Reg.HU Reg.U (by decide) (hfRun (gBadIf (topN Reg.U) s))
  have a4 := S_gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))
  have a5 := S_gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s))))
  have a6 := S_gPop Reg.F (gPop X (gBadIf (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))))
  omega

end Stk

end Sec_Ver9

section Sec_Ver10
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma bits_step (u : ℕ) (hu : u ≠ 0) : Nat.bits u = decide (u % 2 = 1) :: Nat.bits (u / 2) := by
  have h : Nat.bit (decide (u % 2 = 1)) (u / 2) = u := by
    rw [Nat.bit_val]; rcases Nat.mod_two_eq_zero_or_one u with h | h <;> simp [h] <;> omega
  have h2 : u / 2 = 0 → decide (u % 2 = 1) = true := by
    intro h0; have : u % 2 = 1 := by omega
    simp [this]
  rw [← Nat.bits_append_bit (u/2) (decide (u % 2 = 1)) h2, h]

def chk : List Al → ℕ → Option ℕ
  | [], u => some u
  | x :: l, u => if u ≠ 0 ∧ x = tkb (decide (u % 2 = 1)) then chk l (u / 2) else none

lemma chk_eq : ∀ (l : List Al) (u : ℕ), chk l u = some 0 ↔ l = (Nat.bits u).map tkb := by
  intro l
  induction l with
  | nil =>
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chk]
    · rw [bits_step u hu]; simp [chk, hu]
  | cons x l ih =>
    intro u
    by_cases hu : u = 0
    · subst hu; simp [chk]
    · rw [bits_step u hu]
      simp only [chk, List.map_cons, List.cons.injEq]
      by_cases hc : x = tkb (decide (u % 2 = 1))
      · simp [hu, hc, ih]
      · simp [hu, hc]

def EqInv (s : St) : Prop :=
  s Reg.F = [] ∧ s Reg.HU = [] ∧ ∃ c, s Reg.U = List.replicate (s Reg.U).length c

lemma top_cons (X : Reg) (s : St) (h : topS X (hd s) = true) : ∃ x X', s X = x :: X' := by
  simp only [topS, hd] at h
  cases hs : s X with
  | nil => simp [hs] at h
  | cons x l => exact ⟨x, l, rfl⟩

lemma gBadIf_ne (t : (Reg → Option Al) → Bool) (s : St) (r : Reg) (h : r ≠ Reg.BAD) :
    gBadIf t s r = s r := by
  unfold gBadIf; split_ifs <;> simp [wb_apply, h]

lemma gMvA_ne (a b : Reg) (s : St) (r : Reg) (h1 : r ≠ a) (h2 : r ≠ b) : gMvA a b s r = s r := by
  simp [gMvA, h1, h2]

lemma gBadIf_BAD (t : (Reg → Option Al) → Bool) (s : St) :
    ∃ c, gBadIf t s Reg.BAD = List.replicate c mk ++ s Reg.BAD := by
  unfold gBadIf; split_ifs
  · exact ⟨1, by simp [wb_apply]⟩
  · exact ⟨0, by simp⟩

lemma gEqB_X (X : Reg) (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide) (s : St) :
    gEqB X s X = (s X).tail := by
  unfold gEqB
  simp only [gPop, upd_apply, hXF, if_false, if_true]
  rw [gBadIf_ne _ _ _ hXB, gMvA_ne _ _ _ _ hXH hXU, hfRun_frame X hXU hXF hXH,
    gBadIf_ne _ _ _ hXB]

lemma gEqB_BAD (X : Reg) (hXB : X ≠ Reg.BAD := by decide) (s : St) :
    ∃ c, gEqB X s Reg.BAD = List.replicate c mk ++ s Reg.BAD := by
  unfold gEqB
  obtain ⟨c1, h1⟩ := gBadIf_BAD (topN Reg.U) s
  obtain ⟨c2, h2⟩ := gBadIf_BAD (mmT X) (gMvA Reg.HU Reg.U (hfRun (gBadIf (topN Reg.U) s)))
  refine ⟨c2 + c1, ?_⟩
  simp only [gPop, upd_apply, if_neg (show Reg.BAD ≠ Reg.F by decide), if_neg (Ne.symm hXB)]
  rw [h2, gMvA_ne _ _ _ _ (by decide) (by decide),
    hfRun_frame Reg.BAD (by decide) (by decide) (by decide), h1, List.replicate_add, List.append_assoc]

end Stk

end Sec_Ver10

section Sec_Ver11
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def eqRun (X : Reg) : St → St := lrun (topS X) (gEqB X) (fun s => (s X).length)

lemma gad_eqLoop (X : Reg) (hX : safe X := by decide) (hXU : X ≠ Reg.U := by decide)
    (hXF : X ≠ Reg.F := by decide) (hXH : X ≠ Reg.HU := by decide)
    (hXB : X ≠ Reg.BAD := by decide) :
    Gad (.loop (topS X) (eqBody X)) (eqRun X) := by
  refine Gad.loopG (c := 2) (gad_eqBody X hX) (topS X) _ (fun s => len_le_S s X) ?_ ?_
  · intro s _ _; exact S_gEqB X hXU s
  · intro s _ ht
    obtain ⟨x, X', hx⟩ := top_cons X s ht
    rw [gEqB_X X hXU hXF hXH hXB, hx]; simp

lemma eqInv_step (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) (s : St) (hI : EqInv s) (x : Al) (X' : List Al)
    (hx : s X = x :: X') :
    gEqB X s = upd (upd (upd s Reg.BAD (List.replicate (eqc X s x) mk ++ s Reg.BAD)) Reg.U
      (List.replicate ((s Reg.U).length / 2) mk)) X X' :=
  gEqB_formula X hXU hXF hXH hXB s hI.1 hI.2.1 x X' hx

lemma eqloop_sem (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) :
    ∀ s : St, EqInv s →
      (∃ l, eqRun X s Reg.BAD = l ++ s Reg.BAD) ∧
      (chk (s X) (s Reg.U).length = none → eqRun X s Reg.BAD ≠ []) ∧
      (∀ u', chk (s X) (s Reg.U).length = some u' →
        (eqRun X s X = [] ∧ eqRun X s Reg.U = (if s X = [] then s Reg.U else List.replicate u' mk) ∧
         ∀ r, r ≠ Reg.U → r ≠ X → eqRun X s r = s r)) := by
  have key := lrun_rel EqInv (topS X) (gEqB X) (fun s => (s X).length)
    (fun s hI ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [eqInv_step X hXU hXF hXH hXB s hI x X' hx]
      refine ⟨?_, ?_, ⟨mk, ?_⟩⟩ <;> simp [upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, hI.1, hI.2.1, Ne.symm hXB] )
    (fun s hI ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [gEqB_X X hXU hXF hXH hXB, hx]; simp)
    (fun s s' => EqInv s → (∃ l, s' Reg.BAD = l ++ s Reg.BAD) ∧
      (chk (s X) (s Reg.U).length = none → s' Reg.BAD ≠ []) ∧
      (∀ u', chk (s X) (s Reg.U).length = some u' →
        (s' X = [] ∧ s' Reg.U = (if s X = [] then s Reg.U else List.replicate u' mk) ∧ ∀ r, r ≠ Reg.U → r ≠ X → s' r = s r)))
    (fun s hI ht => by
      have hX : s X = [] := by
        simp only [topS, hd] at ht
        cases hs : s X with
        | nil => rfl
        | cons a l => simp [hs] at ht
      refine fun _ => ⟨⟨[], by simp⟩, ?_, ?_⟩
      · simp [hX, chk]
      · intro u' hu'
        simp [hX, chk] at hu'
        exact ⟨hX, by simp [hX], fun _ _ _ => rfl⟩)
    (fun s hI ht ih => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      have hf := eqInv_step X hXU hXF hXH hXB s hI x X' hx
      have hI1 : EqInv (gEqB X s) := by
        rw [hf]
        refine ⟨?_, ?_, ⟨mk, ?_⟩⟩ <;> simp [upd_apply, hXU, hXF, hXH, hXB, hXU.symm, hXF.symm, hXH.symm, hXB.symm, hI.1, hI.2.1, Ne.symm hXB]
      obtain ⟨ih1, ih2, ih3⟩ := ih hI1
      intro _
      have hBAD1 : gEqB X s Reg.BAD = List.replicate (eqc X s x) mk ++ s Reg.BAD := by
        rw [hf]; simp [upd_apply, hXB.symm, Ne.symm hXB]
      have hX1 : gEqB X s X = X' := by rw [gEqB_X X hXU hXF hXH hXB, hx]; rfl
      have hU1 : (gEqB X s Reg.U).length = (s Reg.U).length / 2 := by
        rw [hf]; simp [upd_apply, hXU.symm]
      have hfr : ∀ r, r ≠ Reg.U → r ≠ X → r ≠ Reg.BAD → gEqB X s r = s r := by
        intro r h1 h2 h3; rw [hf]; simp [upd_apply, h1, h2, h3]
      simp only [hX1, hU1] at ih2 ih3
      rw [hx]
      simp only [chk]
      by_cases hc : (s Reg.U).length ≠ 0 ∧ x = tkb (decide ((s Reg.U).length % 2 = 1))
      · have he : eqc X s x = 0 := by
          obtain ⟨h1, h2⟩ := hc
          have : s Reg.U ≠ [] := fun h => h1 (by simp [h])
          simp [eqc, this, h2]
        rw [he] at hBAD1
        simp only [List.replicate_zero, List.nil_append] at hBAD1
        rw [if_pos hc]
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨l, hl⟩ := ih1; exact ⟨l, by rw [hl, hBAD1]⟩
        · intro h; exact ih2 h
        · intro u' h
          obtain ⟨a, b, c⟩ := ih3 u' h
          have b' : lrun (topS X) (gEqB X) (fun s => (s X).length) (gEqB X s) Reg.U = List.replicate u' mk := by
            by_cases hX' : X' = []
            · subst hX'
              simp only [chk, Option.some.injEq] at h
              have : lrun (topS X) (gEqB X) (fun s => (s X).length) (gEqB X s) Reg.U = gEqB X s Reg.U := by simpa using b
              rw [this, hf]; simp [upd_apply, hXU.symm, hU1, h]
            · simpa [hX'] using b
          refine ⟨a, by simpa using b', fun r h1 h2 => ?_⟩
          by_cases h3 : r = Reg.BAD
          · subst h3; rw [c _ h1 h2, hBAD1]
          · rw [c r h1 h2, hfr r h1 h2 h3]
      · rw [if_neg hc]
        have he : eqc X s x ≠ 0 := by
          intro h0
          apply hc
          simp only [eqc, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h0
          obtain ⟨h1, h2⟩ := h0
          exact ⟨fun h => h1 (List.length_eq_zero_iff.mp h), h2⟩
        refine ⟨?_, ?_, ?_⟩
        · obtain ⟨l, hl⟩ := ih1; exact ⟨l ++ List.replicate (eqc X s x) mk, by simp [hl, hBAD1]⟩
        · intro _
          obtain ⟨l, hl⟩ := ih1
          rw [hl, hBAD1]
          have : eqc X s x ≠ 0 := he
          intro h
          have := congrArg List.length h
          simp at this; omega
        · intro u' h; simp at h)
  exact fun s h => key s h h

end Stk

end Sec_Ver11

section Sec_Ver12
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma eqRun_BAD (X : Reg) (hXU : X ≠ Reg.U) (hXF : X ≠ Reg.F)
    (hXH : X ≠ Reg.HU) (hXB : X ≠ Reg.BAD) :
    ∀ s : St, ∃ l, eqRun X s Reg.BAD = l ++ s Reg.BAD := by
  have key := lrun_rel (fun _ : St => True) (topS X) (gEqB X) (fun s => (s X).length)
    (fun _ _ _ => trivial)
    (fun s _ ht => by
      obtain ⟨x, X', hx⟩ := top_cons X s ht
      rw [gEqB_X X hXU hXF hXH hXB, hx]; simp)
    (fun s s' => ∃ l, s' Reg.BAD = l ++ s Reg.BAD) (fun s _ _ => ⟨[], by simp⟩)
    (fun s _ ht ih => by
      obtain ⟨l, hl⟩ := ih
      obtain ⟨c, hc⟩ := gEqB_BAD X hXB s
      exact ⟨l ++ List.replicate c mk, by rw [hl, hc]; simp⟩)
  exact fun s => key s trivial

def okL (X : Reg) (s : St) : Prop := chk (s X) (s Reg.U).length ≠ none
def TL (X : Reg) (s : St) : St :=
  upd (upd s X []) Reg.U (if s X = [] then s Reg.U else List.replicate ((chk (s X) (s Reg.U).length).getD 0) mk)

lemma gsP_eqLoop (X : Reg) (hX : safe X := by decide) (hXU : X ≠ Reg.U := by decide)
    (hXF : X ≠ Reg.F := by decide) (hXH : X ≠ Reg.HU := by decide)
    (hXB : X ≠ Reg.BAD := by decide) :
    GsP (.loop (topS X) (eqBody X)) (eqRun X) (TL X) (okL X) EqInv := by
  refine ⟨gad_eqLoop X hX hXU hXF hXH hXB, ?_, ?_, ?_⟩
  · intro s hs h
    obtain ⟨l, hl⟩ := eqRun_BAD X hXU hXF hXH hXB s
    rw [hl] at h; exact hs (List.append_eq_nil_iff.mp h).2
  · intro s; simp [TL, upd_apply, hXB, Ne.symm hXB]
  · intro s hi hp hb
    obtain ⟨a1, a2, a3⟩ := eqloop_sem X hXU hXF hXH hXB s hp
    cases hc : chk (s X) (s Reg.U).length with
    | none =>
      have := a2 hc
      refine ⟨⟨fun h => absurd h this, fun h => absurd h (by simp [okL, hc])⟩, fun h => absurd h (by simp [okL, hc])⟩
    | some u' =>
      obtain ⟨b1, b2, b3⟩ := a3 u' hc
      have hr : eqRun X s = TL X s := by
        funext r
        by_cases h1 : r = X
        · subst h1; simp [TL, hXU, b1]
        · by_cases h2 : r = Reg.U
          · subst h2; simp [TL, hc, b2, Ne.symm hXU]
          · simp [TL, h1, h2, b3 r h2 h1]
      refine ⟨⟨fun _ => by simp [okL, hc], fun _ => ?_⟩, fun _ => hr⟩
      have := b3 Reg.BAD (Ne.symm (by decide)) (Ne.symm hXB)
      rw [this, hb]

end Stk

end Sec_Ver12

section Sec_Ver13
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def eqProg (X D : Reg) : Prog :=
  sq (sq (sq (sq (clearProg Reg.U) (sq (clearProg Reg.F) (sq (clearProg Reg.HU)
    (copyProg D Reg.U Reg.C)))) (.loop (topS X) (eqBody X))) (badIf (topS Reg.U))) (clearProg Reg.U)

def g0 (D : Reg) (s : St) : St := gCopy D Reg.U (gClear Reg.HU (gClear Reg.F (gClear Reg.U s)))
def eqG (X D : Reg) (s : St) : St := gClear Reg.U (gBadIf (topS Reg.U) (eqRun X (g0 D s)))
def eqT (X : Reg) (s : St) : St := upd (upd (upd (upd s X []) Reg.U []) Reg.F []) Reg.HU []

lemma g0_apply (D : Reg) (hDU : D ≠ Reg.U) (hDF : D ≠ Reg.F) (hDH : D ≠ Reg.HU) (s : St) (r : Reg) :
    g0 D s r = if r = Reg.U then s D else if r = Reg.F then [] else if r = Reg.HU then [] else s r := by
  unfold g0 gCopy gClear
  by_cases h1 : r = Reg.U
  · subst h1; simp [upd_apply, hDF, hDH, hDU]
  · by_cases h2 : r = Reg.F
    · subst h2; simp [upd_apply]
    · by_cases h3 : r = Reg.HU
      · subst h3; simp [upd_apply]
      · simp [upd_apply, h1, h2, h3]


lemma gsP_eq (X D : Reg) (hX : safe X := by decide) (hD : safe D := by decide)
    (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (hDU : D ≠ Reg.U := by decide) (hDF : D ≠ Reg.F := by decide)
    (hDH : D ≠ Reg.HU := by decide) :
    GsP (eqProg X D) (eqG X D) (eqT X) (fun s => s X = (Nat.bits (s D).length).map tkb)
      (fun s => ∃ c, s D = List.replicate (s D).length c) := by
  have c := Gs.seq (gs_clear Reg.U) (Gs.seq (gs_clear Reg.F) (Gs.seq (gs_clear Reg.HU)
    (gs_copy D Reg.U hDU.symm.symm hD)))
  have P1 := c.toP (fun s => ∃ c, s D = List.replicate (s D).length c)
  have P2 := gsP_eqLoop X hX hXU hXF hXH hXB
  have P12 := GsP.seq P1 P2 (fun s _ hp _ _ => by
    show EqInv (g0 D s)
    have e := g0_apply D hDU hDF hDH s
    have hU0 : g0 D s Reg.U = s D := by rw [e]; simp
    refine ⟨by rw [e]; simp, by rw [e]; simp, ?_⟩
    rw [hU0]; exact hp)
  have P3 := GsP.seq P12 ((gs_badIf (topS Reg.U)).toP (fun _ => True)) (fun _ _ _ _ _ => trivial)
  have P4 := GsP.seq P3 ((gs_clear Reg.U).toP (fun _ => True)) (fun _ _ _ _ _ => trivial)
  refine GsP.congr P4 ?_ ?_ (fun _ _ h => h) ?_
  · intro s _ _
    funext r
    show gClear Reg.U (id (TL X (g0 D s))) r = eqT X s r
    have e := g0_apply D hDU hDF hDH s
    simp only [gClear, id, TL, eqT, upd_apply, e]
    split_ifs <;> rfl
  · intro s hi hp
    have e := g0_apply D hDU hDF hDH s
    have hX0 : g0 D s X = s X := by rw [e]; simp [hXU, hXF, hXH]
    have hU0 : g0 D s Reg.U = s D := by rw [e]; simp
    change ((((True ∧ True ∧ True ∧ True) ∧ okL X (g0 D s)) ∧
          topS Reg.U (hd (TL X (g0 D s))) = false) ∧ True) ↔ _
    simp only [okL, TL, hX0, hU0, true_and, and_true, hd, topS, upd_apply, if_true]
    have hq := chk_eq (s X) (s D).length
    cases hc : chk (s X) (s D).length with
    | none =>
      rw [hc] at hq
      simp only [ne_eq, not_true_eq_false, false_and, false_iff]
      intro h; have := hq.2 h; simp at this
    | some u =>
      rw [hc] at hq
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, Option.getD_some]
      rw [← hq]
      by_cases hxe : s X = []
      · rw [hxe] at hc; simp [chk] at hc; subst hc
        simp [hxe]
      · simp [hxe]
  · intro s; simp [eqT, upd_apply, hXB, Ne.symm hXB]

end Stk

end Sec_Ver13

section Sec_Ver14
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma GsP.loop1x (t : (Reg → Option Al) → Bool) (f : (Reg → Option Al) → Reg → StackAct Al)
    (μ : St → ℕ) (hμ : ∀ s, μ s ≤ S s)
    (hC : ∀ h, f h Reg.C = StackAct.keep) (hRC : ∀ h, f h Reg.RC = StackAct.keep)
    (hBADf : ∀ h, f h Reg.BAD = StackAct.keep ∨ ∃ a, f h Reg.BAD = StackAct.push a)
    (hdec : ∀ s, t (hd s) = true → μ (StackProg.applyAct f s) < μ s)
    (Inv : St → Prop)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (StackProg.applyAct f s))
    (F : St → St) (e : St → List Al) (ok : St → Prop)
    (hstop : ∀ s, Inv s → t (hd s) = false → F s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → F (StackProg.applyAct f s) = F s)
    (hBAD : ∀ s, Inv s → F s Reg.BAD = e s ++ s Reg.BAD)
    (hok : ∀ s, Inv s → (e s = [] ↔ ok s)) :
    GsP (.loop t (.act f)) (lrun t (StackProg.applyAct f) μ)
      (fun s => upd (F s) Reg.BAD (s Reg.BAD)) ok Inv := by
  have hg := Gad.loop1 t f μ hμ hC hRC (fun s _ => hdec s)
  have hex : ∀ s, Inv s → lrun t (StackProg.applyAct f) μ s = F s := by
    have := lrun_rel Inv t (StackProg.applyAct f) μ hinv (fun s _ => hdec s)
      (fun s s' => s' = F s) (fun s hs ht => (hstop s hs ht).symm)
      (fun s hs ht h => by rw [h]; exact hstep s hs ht)
    exact this
  refine ⟨hg, ?_, fun s => by simp [upd_apply], ?_⟩
  · have := lrun_rel (fun _ : St => True) t (StackProg.applyAct f) μ (fun _ _ _ => trivial)
      (fun s _ => hdec s) (fun s s' => s Reg.BAD ≠ [] → s' Reg.BAD ≠ [])
      (fun s _ _ h => h)
      (fun s _ ht h hb => by
        apply h
        have e0 : (StackProg.applyAct f s) Reg.BAD = (f (hd s) Reg.BAD).apply (s Reg.BAD) := rfl
        rw [e0]
        rcases hBADf (hd s) with h1 | ⟨a, h1⟩
        · rw [h1]; simpa [StackAct.apply] using hb
        · rw [h1]; simp [StackAct.apply])
    exact fun s hs => this s trivial hs
  · intro s hi hp hb
    rw [hex s hp]
    have h1 := hBAD s hp
    rw [hb, List.append_nil] at h1
    refine ⟨by rw [h1]; exact hok s hp, fun ho => ?_⟩
    have he := (hok s hp).2 ho
    rw [he] at h1
    funext r
    by_cases hr : r = Reg.BAD
    · subst hr; simp [upd_apply, h1, hb]
    · simp [upd_apply, hr]

end Stk

end Sec_Ver14

section Sec_Ver15
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def dcAct (A B : Reg) (c : Al → Bool) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = A then StackAct.pop
  else if r = B then (if (match h A with | some x => c x | none => false) = true then StackAct.pop else StackAct.keep)
  else if r = Reg.BAD then (if (match h A with | some x => c x | none => false) = true ∧ (h B).isNone = true
      then StackAct.push mk else StackAct.keep)
  else StackAct.keep

def drainProg (A B : Reg) (c : Al → Bool) : Prog := .loop (topS A) (.act (dcAct A B c))

def dcF (A B : Reg) (c : Al → Bool) (s : St) : St :=
  upd (upd (upd s A []) B ((s B).drop ((s A).countP c))) Reg.BAD
    (List.replicate ((s A).countP c - (s B).length) mk ++ s Reg.BAD)

lemma dc_step (A B : Reg) (c : Al → Bool) (hAB : A ≠ B) (hA : A ≠ Reg.BAD) (hB : B ≠ Reg.BAD)
    (s : St) (x : Al) (l : List Al) (hx : s A = x :: l) :
    StackProg.applyAct (dcAct A B c) s =
      upd (upd (upd s A l) B (if c x = true then (s B).tail else s B)) Reg.BAD
        (if c x = true ∧ s B = [] then mk :: s Reg.BAD else s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct (dcAct A B c) s r = (dcAct A B c (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdA : hd s A = some x := by simp [hd, hx]
  by_cases h1 : r = A
  · subst h1; simp [dcAct, upd_apply, hx, StackAct.apply, hAB, hA]
  · by_cases h2 : r = B
    · subst h2
      simp only [dcAct, h1, if_false, if_true, hdA, upd_apply, hA.symm, h1, hAB.symm]
      split_ifs <;> simp [StackAct.apply]
    · by_cases h3 : r = Reg.BAD
      · subst h3
        simp only [dcAct, h1, h2, if_false, if_true, hdA, upd_apply, h1, h2]
        by_cases hcx : c x = true
        · by_cases hb : s B = []
          · have : (hd s B).isNone = true := by simp [hd, hb]
            simp [hcx, hb, this, StackAct.apply]
          · have : (hd s B).isNone = false := by
              cases hh : s B with
              | nil => exact absurd hh hb
              | cons b bl => simp [hd, hh]
            simp [hcx, hb, this, StackAct.apply]
        · simp [hcx, StackAct.apply]
      · simp [dcAct, h1, h2, h3, upd_apply, StackAct.apply]

lemma gsP_drain (A B : Reg) (c : Al → Bool) (hA : safe A) (hB : safe B) (hAB : A ≠ B)
    (hA' : A ≠ Reg.BAD) (hB' : B ≠ Reg.BAD) :
    GsP (drainProg A B c) (lrun (topS A) (StackProg.applyAct (dcAct A B c)) (fun s => (s A).length))
      (fun s => upd (dcF A B c s) Reg.BAD (s Reg.BAD)) (fun s => (s A).countP c ≤ (s B).length)
      (fun _ => True) := by
  have hAC := hA.1; have hAR := hA.2; have hBC := hB.1; have hBR := hB.2
  refine GsP.loop1x (topS A) (dcAct A B c) (fun s => (s A).length) (fun s => len_le_S s A)
    (fun h => by simp [dcAct, hAC.symm, hBC.symm])
    (fun h => by simp [dcAct, hAR.symm, hBR.symm])
    (fun h => by unfold dcAct; rw [if_neg hA'.symm, if_neg hB'.symm, if_pos rfl]; split_ifs <;> simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (dcF A B c)
    (fun s => List.replicate ((s A).countP c - (s B).length) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons A s ht
    rw [dc_step A B c hAB hA' hB' s x l hx]
    simp [upd_apply, hA', hAB, hx]
  · intro s _ ht
    have hAe : s A = [] := by
      simp only [topS, hd] at ht
      cases hs : s A with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = A
    · subst h1; simp [dcF, upd_apply, hAe, hA', hAB]
    · by_cases h2 : r = B
      · subst h2; simp [dcF, upd_apply, hAe, h1, hB']
      · by_cases h3 : r = Reg.BAD
        · subst h3; simp [dcF, upd_apply, hAe, h1, h2]
        · simp [dcF, upd_apply, h1, h2, h3]
  · intro s _ ht
    obtain ⟨x, l, hx⟩ := top_cons A s ht
    rw [dc_step A B c hAB hA' hB' s x l hx]
    funext r
    by_cases h1 : r = A
    · subst h1; simp [dcF, upd_apply, hx, hAB, hA']
    · by_cases h2 : r = B
      · subst h2
        by_cases hcx : c x = true
        · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
        · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
      · by_cases h3 : r = Reg.BAD
        · subst h3
          by_cases hcx : c x = true
          · by_cases hb : s B = []
            · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, hb, List.countP_cons, hAB.symm, List.replicate_succ']
            · have : 1 ≤ (s B).length := List.length_pos_iff.2 hb
              simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, hb, List.countP_cons, hAB.symm]
              have : (l.countP c + 1 - (s B).length) = l.countP c - ((s B).length - 1) := by omega
              rw [this]
          · simp [dcF, upd_apply, hx, hAB, hA', hB', hcx, List.countP_cons, hAB.symm]
        · simp [dcF, upd_apply, h1, h2, h3]
  · intro s _
    simp [dcF, upd_apply, hA'.symm, hB'.symm]
  · intro s _
    simp
    omega

end Stk

end Sec_Ver15

section Sec_Ver16
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def flAct (A B : Reg) (x : Al) : (Reg → Option Al) → Reg → StackAct Al := fun _ r =>
  if r = A then StackAct.pop else if r = B then StackAct.push x else StackAct.keep

def fillProg (A B : Reg) (x : Al) : Prog := .loop (topS A) (.act (flAct A B x))

def flF (A B : Reg) (x : Al) (s : St) : St :=
  upd (upd s A []) B (List.replicate (s A).length x ++ s B)

lemma rep_append_cons (n : ℕ) (x : Al) (t : List Al) :
    List.replicate n x ++ x :: t = x :: (List.replicate n x ++ t) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

lemma fl_step (A B : Reg) (x : Al) (hAB : A ≠ B) (s : St) (y : Al) (l : List Al) (hy : s A = y :: l) :
    StackProg.applyAct (flAct A B x) s = upd (upd s A l) B (x :: s B) := by
  funext r
  have e0 : StackProg.applyAct (flAct A B x) s r = (flAct A B x (hd s) r).apply (s r) := rfl
  rw [e0]
  by_cases h1 : r = A
  · subst h1; simp [flAct, upd_apply, hy, StackAct.apply, hAB]
  · by_cases h2 : r = B
    · subst h2; simp [flAct, upd_apply, StackAct.apply, h1]
    · simp [flAct, upd_apply, StackAct.apply, h1, h2]

lemma gsP_fill (A B : Reg) (x : Al) (hA : safe A) (hB : safe B) (hAB : A ≠ B)
    (hA' : A ≠ Reg.BAD) (hB' : B ≠ Reg.BAD) :
    GsP (fillProg A B x) (lrun (topS A) (StackProg.applyAct (flAct A B x)) (fun s => (s A).length))
      (fun s => upd (flF A B x s) Reg.BAD (s Reg.BAD)) (fun _ => True) (fun _ => True) := by
  have hAC := hA.1; have hAR := hA.2; have hBC := hB.1; have hBR := hB.2
  refine GsP.loop1x (topS A) (flAct A B x) (fun s => (s A).length) (fun s => len_le_S s A)
    (fun h => by simp [flAct, hAC.symm, hBC.symm])
    (fun h => by simp [flAct, hAR.symm, hBR.symm])
    (fun h => by unfold flAct; rw [if_neg hA'.symm, if_neg hB'.symm]; simp)
    ?_ (fun _ => True) (fun _ _ _ => trivial) (flF A B x) (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨y, l, hy⟩ := top_cons A s ht
    rw [fl_step A B x hAB s y l hy]
    simp [upd_apply, hA', hAB, hy]
  · intro s _ ht
    have hAe : s A = [] := by
      simp only [topS, hd] at ht
      cases hs : s A with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    by_cases h1 : r = A
    · subst h1; simp [flF, upd_apply, hAe, hAB]
    · by_cases h2 : r = B
      · subst h2; simp [flF, upd_apply, hAe, h1]
      · simp [flF, upd_apply, h1, h2]
  · intro s _ ht
    obtain ⟨y, l, hy⟩ := top_cons A s ht
    rw [fl_step A B x hAB s y l hy]
    funext r
    by_cases h1 : r = A
    · subst h1; simp [flF, upd_apply, hy, hAB]
    · by_cases h2 : r = B
      · subst h2; simp [flF, upd_apply, hy, hAB, h1, hAB.symm, List.replicate_succ, rep_append_cons]
      · simp [flF, upd_apply, h1, h2]
  · intro s _
    simp [flF, upd_apply, hA'.symm, hB'.symm]
  · intro s _; simp

end Stk

end Sec_Ver16

section Sec_Ver17
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def paAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.W then StackAct.pop
  else if r = Reg.MR then (if h Reg.W = some (tk BSym.sep) then
      StackAct.push (if (h Reg.FP).isSome then ty BSym.one else ty BSym.zero) else StackAct.keep)
  else if r = Reg.FP then (if h Reg.W = some (tk BSym.one) then
      (if (h Reg.FP).isNone then StackAct.push mk else StackAct.keep)
    else if h Reg.W = some (tk BSym.sep) then StackAct.pop else StackAct.keep)
  else if r = Reg.BAD then (if h Reg.W = some (tk BSym.one) then
      (if (h Reg.FP).isSome then StackAct.push mk else StackAct.keep)
    else if h Reg.W = some (tk BSym.sep) then StackAct.keep else StackAct.push mk)
  else StackAct.keep

def parseLoop : Prog := .loop (topS Reg.W) (.act paAct)

/-- state: (pending-one flag, matrix bits so far (reversed), bad count) -/
def ps (st : Bool × List Al × ℕ) (a : Al) : Bool × List Al × ℕ :=
  if a = tk BSym.one then (true, st.2.1, if st.1 then st.2.2 + 1 else st.2.2)
  else if a = tk BSym.sep then (false, (if st.1 then ty BSym.one else ty BSym.zero) :: st.2.1, st.2.2)
  else (st.1, st.2.1, st.2.2 + 1)

def PInv (s : St) : Prop := s Reg.FP = [] ∨ s Reg.FP = [mk]

def paF (s : St) : St :=
  let r := (s Reg.W).foldl ps (decide (s Reg.FP ≠ []), s Reg.MR, 0)
  upd (upd (upd (upd s Reg.W []) Reg.FP (if r.1 then [mk] else [])) Reg.MR r.2.1) Reg.BAD
    (List.replicate r.2.2 mk ++ s Reg.BAD)

lemma pa_step (s : St) (x : Al) (l : List Al) (hx : s Reg.W = x :: l) (hI : PInv s) :
    StackProg.applyAct paAct s =
      upd (upd (upd (upd s Reg.W l) Reg.FP
        (if (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1 then [mk] else [])) Reg.MR
        (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.1) Reg.BAD
        (List.replicate (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.2 mk ++ s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct paAct s r = (paAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdW : hd s Reg.W = some x := by simp [hd, hx]
  have hdF : (hd s Reg.FP) = if s Reg.FP = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  by_cases hx1 : x = tk BSym.one
  · subst hx1
    rcases hI with h | h
    · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx]
    · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx]
  · by_cases hx2 : x = tk BSym.sep
    · subst hx2
      rcases hI with h | h
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx, ty]
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, tk, mk, hx, ty]
    · rcases hI with h | h
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, hx, hx1, hx2, List.replicate_succ']
      · cases r <;> simp [paAct, hdW, hdF, h, ps, upd_apply, StackAct.apply, hx, hx1, hx2, List.replicate_succ']


lemma ps_add (l : List Al) : ∀ (r : Bool) (M : List Al) (n : ℕ),
    l.foldl ps (r, M, n) = ((l.foldl ps (r, M, 0)).1, (l.foldl ps (r, M, 0)).2.1,
      (l.foldl ps (r, M, 0)).2.2 + n) := by
  induction l with
  | nil => intro r M n; simp
  | cons a l ih =>
    intro r M n
    simp only [List.foldl_cons]
    rw [ih (ps (r, M, n) a).1 (ps (r, M, n) a).2.1 (ps (r, M, n) a).2.2,
      ih (ps (r, M, 0) a).1 (ps (r, M, 0) a).2.1 (ps (r, M, 0) a).2.2]
    unfold ps
    by_cases h1 : a = tk BSym.one <;> by_cases h2 : a = tk BSym.sep <;> simp [h1, h2] <;> (try split_ifs) <;> (try simp) <;> (try omega)

def paNB (s : St) : ℕ := ((s Reg.W).foldl ps (decide (s Reg.FP ≠ []), s Reg.MR, 0)).2.2

lemma paF_step (s : St) (x : Al) (l : List Al) (hx : s Reg.W = x :: l) (hI : PInv s) :
    paF (StackProg.applyAct paAct s) = paF s := by
  rw [pa_step s x l hx hI]
  have hk := ps_add l (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1
    (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.1 (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).2.2
  have e : paF s = upd (upd (upd (upd s Reg.W []) Reg.FP
        (if (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).1 then [mk] else [])) Reg.MR
        (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).2.1) Reg.BAD
        (List.replicate (l.foldl ps (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x)).2.2 mk ++ s Reg.BAD) := by
    unfold paF
    rw [hx]
    rfl
  rw [e]
  generalize (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x) = q at hk ⊢
  obtain ⟨b, M, n1⟩ := q
  simp only at hk
  rw [hk]
  funext r
  unfold paF
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if b = true then [mk] else []) ≠ []) = b := by cases b <;> simp
  rw [hb]
  by_cases h1 : r = Reg.BAD
  · subst h1; simp only [ite_true]; rw [List.replicate_add, List.append_assoc]
  · by_cases h2 : r = Reg.MR
    · subst h2; simp
    · by_cases h3 : r = Reg.FP
      · subst h3; simp
      · by_cases h4 : r = Reg.W
        · subst h4; simp
        · simp [h1, h2, h3, h4]

lemma gsP_parse : GsP parseLoop (lrun (topS Reg.W) (StackProg.applyAct paAct) (fun s => (s Reg.W).length))
    (fun s => upd (paF s) Reg.BAD (s Reg.BAD)) (fun s => paNB s = 0) PInv := by
  refine GsP.loop1x (topS Reg.W) paAct (fun s => (s Reg.W).length) (fun s => len_le_S s Reg.W)
    (fun h => by simp [paAct]) (fun h => by simp [paAct]) 
    (fun h => by simp only [paAct]; simp; split_ifs <;> simp)
    ?_ PInv ?_ paF (fun s => List.replicate (paNB s) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    have e0 : StackProg.applyAct paAct s Reg.W = (paAct (hd s) Reg.W).apply (s Reg.W) := rfl
    have e1 : paAct (hd s) Reg.W = StackAct.pop := by simp [paAct]
    show (StackProg.applyAct paAct s Reg.W).length < (s Reg.W).length
    rw [e0, e1, hx]
    simp [StackAct.apply]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    rw [pa_step s x l hx hI]
    unfold PInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : (ps (decide (s Reg.FP ≠ []), s Reg.MR, 0) x).1 = true <;> simp [hb]
  · intro s hI ht
    have hWe : s Reg.W = [] := by
      simp only [topS, hd] at ht
      cases hs : s Reg.W with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    unfold paF
    simp only [hWe, List.foldl_nil, upd_apply]
    have hb : (if decide (s Reg.FP ≠ []) = true then [mk] else []) = s Reg.FP := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = Reg.BAD
    · subst h1; simp
    · by_cases h2 : r = Reg.MR
      · subst h2; simp
      · by_cases h3 : r = Reg.FP
        · subst h3; simpa using hb
        · by_cases h4 : r = Reg.W
          · subst h4; simp [hWe]
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.W s ht
    exact paF_step s x l hx hI
  · intro s _
    simp [paF, upd_apply, paNB]
  · intro s _
    simp [paNB]

end Stk

end Sec_Ver17

section Sec_Ver18
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def scAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.TT then StackAct.pop
  else if r = Reg.KR then (if h Reg.TT = some (ty BSym.one) ∨ h Reg.TT = some (ty BSym.zero) then
      StackAct.pop else StackAct.keep)
  else if r = Reg.H then (if h Reg.TT = some mk then StackAct.pop
      else if h Reg.TT = some (ty BSym.one) ∧ h Reg.KR = some (ty BSym.one) ∧ (h Reg.H).isNone then
        StackAct.push mk else StackAct.keep)
  else if r = Reg.BAD then (if h Reg.TT = some mk then
      (if (h Reg.H).isNone then StackAct.push mk else StackAct.keep)
    else if h Reg.TT = some (ty BSym.one) ∨ h Reg.TT = some (ty BSym.zero) then
      (if (h Reg.KR).isNone then StackAct.push mk else StackAct.keep)
    else StackAct.push mk)
  else StackAct.keep

def scanLoop : Prog := .loop (topS Reg.TT) (.act scAct)

def ss (st : Bool × List Al × ℕ) (a : Al) : Bool × List Al × ℕ :=
  if a = mk then (false, st.2.1, if st.1 then st.2.2 else st.2.2 + 1)
  else if a = ty BSym.one then (st.1 || decide (st.2.1.head? = some (ty BSym.one)), st.2.1.tail,
      if st.2.1 = [] then st.2.2 + 1 else st.2.2)
  else if a = ty BSym.zero then (st.1, st.2.1.tail, if st.2.1 = [] then st.2.2 + 1 else st.2.2)
  else (st.1, st.2.1, st.2.2 + 1)

def SInv (s : St) : Prop := s Reg.H = [] ∨ s Reg.H = [mk]

def scF (s : St) : St :=
  let r := (s Reg.TT).foldl ss (decide (s Reg.H ≠ []), s Reg.KR, 0)
  upd (upd (upd (upd s Reg.TT []) Reg.H (if r.1 then [mk] else [])) Reg.KR r.2.1) Reg.BAD
    (List.replicate r.2.2 mk ++ s Reg.BAD)

lemma sc_step (s : St) (x : Al) (l : List Al) (hx : s Reg.TT = x :: l) (hI : SInv s) :
    StackProg.applyAct scAct s =
      upd (upd (upd (upd s Reg.TT l) Reg.H
        (if (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1 then [mk] else [])) Reg.KR
        (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.1) Reg.BAD
        (List.replicate (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.2 mk ++ s Reg.BAD) := by
  funext r
  have e0 : StackProg.applyAct scAct s r = (scAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdT : hd s Reg.TT = some x := by simp [hd, hx]
  have hdH : (hd s Reg.H) = if s Reg.H = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  have hdK : hd s Reg.KR = (s Reg.KR).head? := rfl
  cases hK : s Reg.KR with
  | nil =>
    have hdK' : hd s Reg.KR = none := by rw [hdK, hK]; rfl
    by_cases hx1 : x = mk
    · subst hx1
      rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
    · by_cases hx2 : x = ty BSym.one
      · subst hx2
        rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK] <;> (try split_ifs) <;> rfl
      · by_cases hx3 : x = ty BSym.zero
        · subst hx3
          rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
        · rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, hx, hK, hx1, hx2, hx3, List.replicate_succ']
  | cons y ky =>
    have hdK' : hd s Reg.KR = some y := by rw [hdK, hK]; rfl
    by_cases hx1 : x = mk
    · subst hx1
      rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
    · by_cases hx2 : x = ty BSym.one
      · subst hx2
        rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK] <;> (try split_ifs) <;> rfl
      · by_cases hx3 : x = ty BSym.zero
        · subst hx3
          rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, mk, ty, hx, hK]
        · rcases hI with h | h <;> cases r <;> simp [scAct, hdT, hdH, hdK', h, ss, upd_apply, StackAct.apply, hx, hK, hx1, hx2, hx3, List.replicate_succ']

lemma ss_add (l : List Al) : ∀ (r : Bool) (M : List Al) (n : ℕ),
    l.foldl ss (r, M, n) = ((l.foldl ss (r, M, 0)).1, (l.foldl ss (r, M, 0)).2.1,
      (l.foldl ss (r, M, 0)).2.2 + n) := by
  induction l with
  | nil => intro r M n; simp
  | cons a l ih =>
    intro r M n
    simp only [List.foldl_cons]
    rw [ih (ss (r, M, n) a).1 (ss (r, M, n) a).2.1 (ss (r, M, n) a).2.2,
      ih (ss (r, M, 0) a).1 (ss (r, M, 0) a).2.1 (ss (r, M, 0) a).2.2]
    unfold ss
    by_cases h1 : a = mk <;> by_cases h2 : a = ty BSym.one <;> by_cases h3 : a = ty BSym.zero <;> simp [h1, h2, h3] <;> (try split_ifs) <;> (try simp) <;> (try omega)

def scNB (s : St) : ℕ := ((s Reg.TT).foldl ss (decide (s Reg.H ≠ []), s Reg.KR, 0)).2.2

lemma scF_step (s : St) (x : Al) (l : List Al) (hx : s Reg.TT = x :: l) (hI : SInv s) :
    scF (StackProg.applyAct scAct s) = scF s := by
  rw [sc_step s x l hx hI]
  have hk := ss_add l (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1
    (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.1 (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).2.2
  have e : scF s = upd (upd (upd (upd s Reg.TT []) Reg.H
        (if (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).1 then [mk] else [])) Reg.KR
        (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).2.1) Reg.BAD
        (List.replicate (l.foldl ss (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x)).2.2 mk ++ s Reg.BAD) := by
    unfold scF
    rw [hx]
    rfl
  rw [e]
  generalize (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x) = q at hk ⊢
  obtain ⟨b, M, n1⟩ := q
  simp only at hk
  rw [hk]
  funext r
  unfold scF
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if b = true then [mk] else []) ≠ []) = b := by cases b <;> simp
  rw [hb]
  by_cases h1 : r = Reg.BAD
  · subst h1; simp only [ite_true]; rw [List.replicate_add, List.append_assoc]
  · by_cases h2 : r = Reg.KR
    · subst h2; simp
    · by_cases h3 : r = Reg.H
      · subst h3; simp
      · by_cases h4 : r = Reg.TT
        · subst h4; simp
        · simp [h1, h2, h3, h4]

lemma gsP_scan : GsP scanLoop (lrun (topS Reg.TT) (StackProg.applyAct scAct) (fun s => (s Reg.TT).length))
    (fun s => upd (scF s) Reg.BAD (s Reg.BAD)) (fun s => scNB s = 0) SInv := by
  refine GsP.loop1x (topS Reg.TT) scAct (fun s => (s Reg.TT).length) (fun s => len_le_S s Reg.TT)
    (fun h => by simp [scAct]) (fun h => by simp [scAct]) 
    (fun h => by simp only [scAct]; simp; split_ifs <;> simp)
    ?_ SInv ?_ scF (fun s => List.replicate (scNB s) mk) _ ?_ ?_ ?_ ?_
  · intro s ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    have e0 : StackProg.applyAct scAct s Reg.TT = (scAct (hd s) Reg.TT).apply (s Reg.TT) := rfl
    have e1 : scAct (hd s) Reg.TT = StackAct.pop := by simp [scAct]
    show (StackProg.applyAct scAct s Reg.TT).length < (s Reg.TT).length
    rw [e0, e1, hx]
    simp [StackAct.apply]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    rw [sc_step s x l hx hI]
    unfold SInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : (ss (decide (s Reg.H ≠ []), s Reg.KR, 0) x).1 = true <;> simp [hb]
  · intro s hI ht
    have hWe : s Reg.TT = [] := by
      simp only [topS, hd] at ht
      cases hs : s Reg.TT with
      | nil => rfl
      | cons x l => simp [hs] at ht
    funext r
    unfold scF
    simp only [hWe, List.foldl_nil, upd_apply]
    have hb : (if decide (s Reg.H ≠ []) = true then [mk] else []) = s Reg.H := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = Reg.BAD
    · subst h1; simp
    · by_cases h2 : r = Reg.KR
      · subst h2; simp
      · by_cases h3 : r = Reg.H
        · subst h3; simpa using hb
        · by_cases h4 : r = Reg.TT
          · subst h4; simp [hWe]
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    obtain ⟨x, l, hx⟩ := top_cons Reg.TT s ht
    exact scF_step s x l hx hI
  · intro s _
    simp [scF, upd_apply, scNB]
  · intro s _
    simp [scNB]

end Stk

end Sec_Ver18

section Sec_Ver19
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def rcProg (a b c : Reg) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : safe a) (hb : safe b)
    (hc : safe c) : Prog :=
  repeatCopyProg (emb4 a b c Reg.RC hab hac ha.2 hbc hb.2 hc.2)

def gRc (a b c : Reg) (s : St) : St := upd (upd s c []) b ((List.replicate (s c).length (s a)).flatten ++ s b)

lemma gRc_BAD (a b c : Reg) (hb : b ≠ Reg.BAD) (hc : c ≠ Reg.BAD) (s : St) :
    gRc a b c s Reg.BAD = s Reg.BAD := by simp [gRc, upd_apply, hb, hc, hb.symm, hc.symm]

lemma gs_repcopy (a b c : Reg) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : safe a) (hb : safe b)
    (hc : safe c) (hb' : b ≠ Reg.BAD) (hc' : c ≠ Reg.BAD) :
    Gs (rcProg a b c hab hac hbc ha hb hc) (gRc a b c) (gRc a b c) (fun _ => True) := by
  refine Gs.total ⟨?_, fun s hs => ?_⟩ (gRc_BAD a b c hb' hc')
  · have := PSp.repcopy Gi a b c Reg.RC hab hac ha.2 hbc hb.2 hc.2
    exact PSp.weaken this (fun s hs => ⟨hs, hs.2⟩)
  · unfold gRc
    exact Gi_upd _ _ _ hb (Gi_upd _ _ _ hc hs)

end Stk

end Sec_Ver19

section Sec_Ver20
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def cmpAct : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = Reg.MB then StackAct.pop
  else if r = Reg.KB then StackAct.pop
  else if r = Reg.H then
    (if h Reg.MB = some (tk BSym.one) ∧ h Reg.KB ≠ some (tk BSym.one) then
        (if (h Reg.H).isNone then StackAct.push mk else StackAct.keep)
      else if h Reg.MB ≠ some (tk BSym.one) ∧ h Reg.KB = some (tk BSym.one) then StackAct.pop
      else StackAct.keep)
  else StackAct.keep

def cmpT : (Reg → Option Al) → Bool := fun h => (h Reg.MB).isSome || (h Reg.KB).isSome
def cmpLoop : Prog := .loop cmpT (.act cmpAct)

def cs (g : Bool) (x y : Option Al) : Bool :=
  if decide (x = some (tk BSym.one)) = decide (y = some (tk BSym.one)) then g
  else decide (x = some (tk BSym.one))

def cf (xs ys : List Al) (g : Bool) : Bool :=
  (List.zipWithAll (fun x y => (x, y)) xs ys).foldl (fun g p => cs g p.1 p.2) g

def CInv (s : St) : Prop := s Reg.H = [] ∨ s Reg.H = [mk]

def cmpF (s : St) : St :=
  upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
    (if cf (s Reg.MB) (s Reg.KB) (decide (s Reg.H ≠ [])) then [mk] else [])

lemma cmp_step (s : St) (hI : CInv s) (ht : cmpT (hd s) = true) :
    StackProg.applyAct cmpAct s =
      upd (upd (upd s Reg.MB (s Reg.MB).tail) Reg.KB (s Reg.KB).tail) Reg.H
        (if cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head? then [mk] else []) := by
  funext r
  have e0 : StackProg.applyAct cmpAct s r = (cmpAct (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdH : (hd s Reg.H) = if s Reg.H = [] then none else some mk := by
    rcases hI with h | h <;> simp [hd, h]
  have h1 : hd s Reg.MB = (s Reg.MB).head? := rfl
  have h2 : hd s Reg.KB = (s Reg.KB).head? := rfl
  by_cases hr1 : r = Reg.MB
  · subst hr1; simp [cmpAct, StackAct.apply, upd_apply]
  by_cases hr2 : r = Reg.KB
  · subst hr2; simp [cmpAct, StackAct.apply, upd_apply]
  by_cases hr3 : r = Reg.H
  · subst hr3
    simp only [cmpAct, upd_apply, reduceCtorEq, ↓reduceIte, hdH, h1, h2, cs]
    rcases hI with h | h <;> simp [h, StackAct.apply] <;> split_ifs <;> simp_all [StackAct.apply]
  · simp [cmpAct, StackAct.apply, upd_apply, hr1, hr2, hr3]

lemma cf_step (xs ys : List Al) (g : Bool) (h : xs ≠ [] ∨ ys ≠ []) :
    cf xs ys g = cf xs.tail ys.tail (cs g xs.head? ys.head?) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp [cf, List.zipWithAll]
  | cons x xs =>
    cases ys with
    | nil => simp [cf, List.zipWithAll]
    | cons y ys => simp [cf, List.zipWithAll]

lemma cmpF_step (s : St) (hI : CInv s) (ht : cmpT (hd s) = true) :
    cmpF (StackProg.applyAct cmpAct s) = cmpF s := by
  rw [cmp_step s hI ht]
  have hne : s Reg.MB ≠ [] ∨ s Reg.KB ≠ [] := by
    simp only [cmpT, hd, Bool.or_eq_true] at ht
    rcases ht with h | h
    · left; intro h'; simp [h'] at h
    · right; intro h'; simp [h'] at h
  have e : cmpF s = upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
      (if cf (s Reg.MB).tail (s Reg.KB).tail
        (cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head?) then [mk] else []) := by
    unfold cmpF
    rw [cf_step _ _ _ hne]
  rw [e]
  generalize (cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head?) = g
  unfold cmpF
  funext r
  simp only [upd_apply, reduceCtorEq, ↓reduceIte]
  have hb : decide ((if g = true then [mk] else []) ≠ []) = g := by cases g <;> simp
  rw [hb]
  by_cases h1 : r = Reg.MB
  · subst h1; simp
  · by_cases h2 : r = Reg.KB
    · subst h2; simp
    · by_cases h3 : r = Reg.H
      · subst h3; simp
      · simp [h1, h2, h3]

lemma gsP_cmp : GsP cmpLoop (lrun cmpT (StackProg.applyAct cmpAct)
      (fun s => max (s Reg.MB).length (s Reg.KB).length))
    (fun s => upd (cmpF s) Reg.BAD (s Reg.BAD)) (fun _ => True) CInv := by
  refine GsP.loop1x cmpT cmpAct (fun s => max (s Reg.MB).length (s Reg.KB).length)
    (fun s => max_le (len_le_S s Reg.MB) (len_le_S s Reg.KB))
    (fun h => by simp [cmpAct]) (fun h => by simp [cmpAct])
    (fun h => by left; simp [cmpAct]) ?_ CInv ?_ cmpF (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    have e1 : StackProg.applyAct cmpAct s Reg.MB = (s Reg.MB).tail := by
      show (cmpAct (hd s) Reg.MB).apply (s Reg.MB) = _
      simp [cmpAct, StackAct.apply]
    have e2 : StackProg.applyAct cmpAct s Reg.KB = (s Reg.KB).tail := by
      show (cmpAct (hd s) Reg.KB).apply (s Reg.KB) = _
      simp [cmpAct, StackAct.apply]
    have hne : s Reg.MB ≠ [] ∨ s Reg.KB ≠ [] := by
      simp only [cmpT, hd, Bool.or_eq_true] at ht
      rcases ht with h | h
      · left; intro h'; simp [h'] at h
      · right; intro h'; simp [h'] at h
    show max (StackProg.applyAct cmpAct s Reg.MB).length (StackProg.applyAct cmpAct s Reg.KB).length < _
    rw [e1, e2]
    simp only [List.length_tail]
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  · intro s hI ht
    rw [cmp_step s hI ht]
    unfold CInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte]
    by_cases hb : cs (decide (s Reg.H ≠ [])) (s Reg.MB).head? (s Reg.KB).head? = true <;> simp [hb]
  · intro s hI ht
    have hMe : s Reg.MB = [] ∧ s Reg.KB = [] := by
      simp only [cmpT, hd, Bool.or_eq_false_iff] at ht
      constructor
      · cases hs : s Reg.MB with
        | nil => rfl
        | cons x l => simp [hs] at ht
      · cases hs : s Reg.KB with
        | nil => rfl
        | cons x l => simp [hs] at ht
    funext r
    unfold cmpF
    simp only [upd_apply, hMe.1, hMe.2]
    have hb : (if cf [] [] (decide (s Reg.H ≠ [])) = true then [mk] else []) = s Reg.H := by
      rcases hI with h | h <;> simp [cf, h]
    by_cases h1 : r = Reg.MB
    · subst h1; simp [hMe.1]
    · by_cases h2 : r = Reg.KB
      · subst h2; simp [hMe.2]
      · by_cases h3 : r = Reg.H
        · subst h3; simpa using hb
        · simp [h1, h2, h3]
  · intro s hI ht
    exact cmpF_step s hI ht
  · intro s _
    simp [cmpF, upd_apply]
  · intro s _
    simp

end Stk

end Sec_Ver20

section Sec_Ver21
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma GsP.branch {p q : Prog} {g1 g2 T1 T2 : St → St} {ok1 ok2 pre1 pre2 : St → Prop}
    (t : (Reg → Option Al) → Bool)
    (h1 : GsP p g1 T1 ok1 pre1) (h2 : GsP q g2 T2 ok2 pre2) :
    GsP (.branch t p q) (fun s => if t (hd s) = true then g1 s else g2 s)
      (fun s => if t (hd s) = true then T1 s else T2 s)
      (fun s => if t (hd s) = true then ok1 s else ok2 s)
      (fun s => if t (hd s) = true then pre1 s else pre2 s) := by
  obtain ⟨a1, st1, c1, s1⟩ := h1
  obtain ⟨a2, st2, c2, s2⟩ := h2
  refine ⟨Gad.branch t a1 a2, fun s hs => ?_, fun s => ?_, fun s hi hp hb => ?_⟩
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact st1 s hs
    · simp only [ht, if_false]; exact st2 s hs
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true]; exact c1 s
    · simp only [ht, if_false]; exact c2 s
  · by_cases ht : t (hd s) = true
    · simp only [ht, if_true] at hp ⊢; exact s1 s hi hp hb
    · simp only [ht, if_false] at hp ⊢; exact s2 s hi hp hb

structure GB where
  p : Prog
  g : St → St
  T : St → St
  ok : St → Prop
  pre : St → Prop
  h : GsP p g T ok pre

def GB.weak (a : GB) (pre' : St → Prop) (hp : ∀ s, pre' s → a.pre s) : GsP a.p a.g a.T a.ok pre' :=
  GsP.congr a.h (fun _ _ _ => rfl) (fun _ _ _ => Iff.rfl) (fun s _ h => hp s h) a.h.2.2.1

def GB.seq (a b : GB) : GB where
  p := .seq a.p b.p
  g := fun s => b.g (a.g s)
  T := fun s => b.T (a.T s)
  ok := fun s => a.ok s ∧ b.ok (a.T s)
  pre := fun s => a.pre s ∧ (Gi s → s Reg.BAD = [] → a.ok s → b.pre (a.T s))
  h := GsP.seq (a.weak (fun s => a.pre s ∧ (Gi s → s Reg.BAD = [] → a.ok s → b.pre (a.T s)))
      (fun s h => h.1)) b.h (fun s hi hp hb ho => hp.2 hi hb ho)

def GB.branch (t : (Reg → Option Al) → Bool) (a b : GB) : GB where
  p := .branch t a.p b.p
  g := fun s => if t (hd s) = true then a.g s else b.g s
  T := fun s => if t (hd s) = true then a.T s else b.T s
  ok := fun s => if t (hd s) = true then a.ok s else b.ok s
  pre := fun s => if t (hd s) = true then a.pre s else b.pre s
  h := GsP.branch t a.h b.h

def GB.ofGs {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) : GB where
  p := p
  g := g
  T := T
  ok := ok
  pre := fun _ => True
  h := h.toP _

end Stk

end Sec_Ver21

section Sec_Ver22
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def bStNum (X : Reg) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : GB := GB.ofGs (gs_stNum X hX hX' hX2)
def bCopy (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (hb' : b ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_copy a b hab ha hb hb')
def bPush (r : Reg) (a : Al) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_push r a hr hr')
def bPop (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_pop r hr hr')
def bClear (r : Reg) (hr : safe r := by decide) (hr' : r ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_clear r hr hr')
def bMvA (a b : Reg) (hab : a ≠ b := by decide) (ha : safe a := by decide)
    (hb : safe b := by decide) (ha' : a ≠ Reg.BAD := by decide) (hb' : b ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_mvA a b hab ha hb ha' hb')
def bBad (t : (Reg → Option Al) → Bool) : GB := GB.ofGs (gs_badIf t)
def bEq (X D : Reg) (hX : safe X := by decide) (hD : safe D := by decide)
    (hXU : X ≠ Reg.U := by decide) (hXF : X ≠ Reg.F := by decide)
    (hXH : X ≠ Reg.HU := by decide) (hXB : X ≠ Reg.BAD := by decide)
    (hDU : D ≠ Reg.U := by decide) (hDF : D ≠ Reg.F := by decide)
    (hDH : D ≠ Reg.HU := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_eq X D hX hD hXU hXF hXH hXB hDU hDF hDH⟩
def bFill (A B : Reg) (x : Al) (hA : safe A := by decide) (hB : safe B := by decide)
    (hAB : A ≠ B := by decide) (hA' : A ≠ Reg.BAD := by decide) (hB' : B ≠ Reg.BAD := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_fill A B x hA hB hAB hA' hB'⟩
def bDrain (A B : Reg) (c : Al → Bool) (hA : safe A := by decide) (hB : safe B := by decide)
    (hAB : A ≠ B := by decide) (hA' : A ≠ Reg.BAD := by decide) (hB' : B ≠ Reg.BAD := by decide) : GB :=
  ⟨_, _, _, _, _, gsP_drain A B c hA hB hAB hA' hB'⟩
def bRc (a b c : Reg) (hab : a ≠ b := by decide) (hac : a ≠ c := by decide)
    (hbc : b ≠ c := by decide) (ha : safe a := by decide) (hb : safe b := by decide)
    (hc : safe c := by decide) (hb' : b ≠ Reg.BAD := by decide) (hc' : c ≠ Reg.BAD := by decide) : GB :=
  GB.ofGs (gs_repcopy a b c hab hac hbc ha hb hc hb' hc')
def bParse : GB := ⟨_, _, _, _, _, gsP_parse⟩
def bScan : GB := ⟨_, _, _, _, _, gsP_scan⟩
def bCmp : GB := ⟨_, _, _, _, _, gsP_cmp⟩

def isNoneT (r : Reg) (h : Reg → Option Al) : Bool := (h r).isNone
def notOneT (r : Reg) (h : Reg → Option Al) : Bool := decide (h r ≠ some (tk BSym.one))

def posB : GB :=
  (bEq Reg.KB Reg.K).seq <| (bBad (isNoneT Reg.K)).seq <|
  (bCopy Reg.T Reg.TC).seq <| (bFill Reg.TC Reg.T2 mk).seq <| (bEq Reg.MB Reg.T2).seq <|
  (bCopy Reg.K Reg.NC).seq <| (bPush Reg.NC mk).seq <| (bRc Reg.N Reg.PP Reg.NC).seq <|
  (bPush Reg.PP mk).seq <| (bCopy Reg.K Reg.PP).seq <|
  (bCopy Reg.T Reg.TC).seq <| (bDrain Reg.PP Reg.TC (fun _ => true)).seq <| (bClear Reg.TC).seq <|
  (bCopy Reg.K Reg.K2).seq <| (bCopy Reg.T Reg.TC).seq <|
    (bDrain Reg.TC Reg.K2 (isA (ty BSym.one))).seq <|
  bParse.seq <| (bMvA Reg.MR Reg.KR).seq <| (bBad (topS Reg.FP)).seq <|
  (bPush Reg.TM mk).seq <| (bCopy Reg.T Reg.TM).seq <| (bCopy Reg.N Reg.NC2).seq <|
    (bRc Reg.TM Reg.TT Reg.NC2).seq <|
  bScan.seq <| bBad (topS Reg.KR)

def negB : GB :=
  (bBad (topS Reg.W)).seq <|
  (bCopy Reg.MB Reg.LT).seq <| (bMvA Reg.LT Reg.MR).seq <| (bBad (notOneT Reg.MR)).seq <|
    (bClear Reg.MR).seq <|
  (bCopy Reg.KB Reg.LT).seq <| (bMvA Reg.LT Reg.MR).seq <| (bBad (notOneT Reg.MR)).seq <|
    (bClear Reg.MR).seq <|
  bCmp.seq <| bBad (isNoneT Reg.H)

end Stk

end Sec_Ver22

section Sec_Ver23
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def outProg : Prog := .seq (clearProg Reg.OUT) (.branch (topS Reg.BAD) skipP (pushProg Reg.OUT mk))
def outG (s : St) : St := if topS Reg.BAD (hd s) = true then gClear Reg.OUT s else gPush Reg.OUT mk (gClear Reg.OUT s)

lemma gs_out : Gs outProg outG outG (fun _ => True) := by
  have h := Gs.seq (gs_clear Reg.OUT) (Gs.branch (topS Reg.BAD) (Gs.total Gad.skip (fun _ => rfl))
    (gs_push Reg.OUT mk))
  refine Gs.total ?_ (fun s => ?_)
  · exact h.1
  · unfold outG gClear gPush; split_ifs <;> simp [upd_apply, hd]

def bOut : GB := GB.ofGs gs_out

def topB : GB :=
  (bStNum Reg.MB).seq <| (bStNum Reg.NB).seq <| (bStNum Reg.KB).seq <| (bPop Reg.N).seq <|
  (bEq Reg.NB Reg.N).seq <| (GB.branch (topS Reg.N) posB negB)

def fullB : GB := (GB.ofGs gs_stA).seq (topB.seq bOut)

lemma outG_OUT (s : St) : outG s Reg.OUT = if s Reg.BAD = [] then [mk] else [] := by
  unfold outG gClear gPush
  by_cases h : s Reg.BAD = [] <;> simp [h, hd, topS, upd_apply]

end Stk

end Sec_Ver23

section Sec_Ver24
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def sP (bl1 bl3 : List Bool) (rest : List BSym) (n k : ℕ) (t : List Bool) : St := fun r =>
  match r with
  | Reg.W => rest.map tk
  | Reg.N => List.replicate n (ty BSym.sep)
  | Reg.K => List.replicate k (ty BSym.minus)
  | Reg.T => t.map tyb
  | Reg.MB => bl1.map tkb
  | Reg.KB => bl3.map tkb
  | _ => []

end Stk

end Sec_Ver24

section Sec_Ver25
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def val : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * val l + b.toNat

lemma val_cons (b : Bool) (l : List Bool) : val (b :: l) = 2 * val l + b.toNat := rfl

lemma bits_val_of_canon : ∀ (l : List Bool), l.getLast? = some true ∨ l = [] → Nat.bits (val l) = l
  | [] , _ => by simp [val]
  | b :: l, h => by
    have hl : l.getLast? = some true ∨ l = [] := by
      rcases h with h | h
      · cases l with
        | nil => right; rfl
        | cons x r => left; simpa [List.getLast?_cons_cons] using h
      · simp at h
    have ih := bits_val_of_canon l hl
    have e : val (b :: l) = Nat.bit b (val l) := by
      rw [val_cons, Nat.bit_val]
    rw [e, Nat.bits_append_bit _ _ ?_, ih]
    intro h0
    cases l with
    | nil =>
      rcases h with h | h
      · simpa using h
      · simp at h
    | cons x r =>
      have : Nat.bits (val (x :: r)) = x :: r := ih
      rw [h0] at this
      simp at this

lemma val_bits (n : ℕ) : val (Nat.bits n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [val]
  | bit b n ih =>
    by_cases h : Nat.bit b n = 0
    · rw [h]; simp [val]
    · have hn : n = 0 → b = true := by
        intro h0; subst h0
        cases b with
        | false => simp at h
        | true => rfl
      rw [Nat.bits_append_bit _ _ hn, val_cons, ih, Nat.bit_val]

lemma getLast_bits (n : ℕ) (h : n ≠ 0) : (Nat.bits n).getLast? = some true := by
  induction n using Nat.binaryRec with
  | zero => exact absurd rfl h
  | bit b n ih =>
    have hn : n = 0 → b = true := by
      intro h0; subst h0
      cases b with
      | false => simp at h
      | true => rfl
    rw [Nat.bits_append_bit _ _ hn]
    by_cases h0 : n = 0
    · subst h0; simp [hn rfl]
    · have := ih h0
      have hne : Nat.bits n ≠ [] := by
        intro he; rw [he] at this; simp at this
      obtain ⟨x, r, hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr] at this ⊢
      simpa [List.getLast?_cons_cons] using this

end Stk

end Sec_Ver25

section Sec_Ver26
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma cf_nil (g : Bool) : cf [] [] g = g := by simp [cf]

lemma tkb_one_iff (b : Bool) : (some (tkb b) = some (tk BSym.one)) ↔ b = true := by
  cases b <;> simp [tkb, tk]

lemma cf_val : ∀ (xs ys : List Bool) (g : Bool),
    cf (xs.map tkb) (ys.map tkb) g = decide (val ys < val xs ∨ (val xs = val ys ∧ g = true))
  | [], [], g => by simp [cf_nil, val]
  | x :: xs, [], g => by
    rw [List.map_cons, List.map_nil, cf_step _ _ _ (Or.inl (by simp))]
    have ih := cf_val xs [] (cs g (some (tkb x)) none)
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil] at ih ⊢
    rw [ih]
    cases x <;> cases g <;> simp [cs, tkb, tk, val] <;> omega
  | [], y :: ys, g => by
    rw [List.map_cons, List.map_nil, cf_step _ _ _ (Or.inr (by simp))]
    have ih := cf_val [] ys (cs g none (some (tkb y)))
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil] at ih ⊢
    rw [ih]
    cases y <;> cases g <;> simp [cs, tkb, tk, val] <;> omega
  | x :: xs, y :: ys, g => by
    rw [List.map_cons, List.map_cons, cf_step _ _ _ (Or.inl (by simp))]
    have ih := cf_val xs ys (cs g (some (tkb x)) (some (tkb y)))
    simp only [List.map_cons, List.tail_cons, List.head?_cons] at ih ⊢
    rw [ih]
    cases x <;> cases y <;> cases g <;> simp [cs, tkb, tk, val]
    all_goals first | omega | (apply decide_eq_decide.2; omega) | (simp only [← Bool.decide_or]; apply decide_eq_decide.2; omega)

end Stk

end Sec_Ver26

section Sec_Ver27
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def encBits (bs : List Bool) : List BSym :=
  bs.flatMap (fun b => if b then [BSym.one, BSym.sep] else [BSym.sep])

lemma encBits_cons (b : Bool) (bs : List Bool) :
    encBits (b :: bs) = (if b then [BSym.one, BSym.sep] else [BSym.sep]) ++ encBits bs := by
  simp [encBits]

lemma eb_sep (rest : List BSym) (bs : List Bool) :
    BSym.sep :: rest = encBits bs ↔ ∃ bs', bs = false :: bs' ∧ rest = encBits bs' := by
  cases bs with
  | nil => simp [encBits]
  | cons b bs =>
    cases b <;> simp [encBits_cons]

lemma eb_one (rest : List BSym) (bs : List Bool) :
    BSym.one :: rest = encBits bs ↔ ∃ bs', bs = true :: bs' ∧ rest = BSym.sep :: encBits bs' := by
  cases bs with
  | nil => simp [encBits]
  | cons b bs =>
    cases b <;> simp [encBits_cons]

lemma eb_zero (rest : List BSym) (bs : List Bool) : BSym.zero :: rest ≠ encBits bs := by
  cases bs with
  | nil => simp [encBits]
  | cons b bs => cases b <;> simp [encBits_cons]

lemma eb_minus (rest : List BSym) (bs : List Bool) : BSym.minus :: rest ≠ encBits bs := by
  cases bs with
  | nil => simp [encBits]
  | cons b bs => cases b <;> simp [encBits_cons]

lemma tk_inj_iff (a b : BSym) : tk a = tk b ↔ a = b := by simp [tk]

lemma parse_iff : ∀ (rest : List BSym) (r : Bool) (M : List Al) (nb : ℕ) (M' : List Al),
    ((rest.map tk).foldl ps (r, M, nb) = (false, M', 0) ↔
      nb = 0 ∧ ∃ bs, (if r then BSym.one :: rest else rest) = encBits bs ∧
        M' = bs.reverse.map tyb ++ M)
  | [], r, M, nb, M' => by
    cases r
    · simp only [List.map_nil, List.foldl_nil, Prod.mk.injEq, Bool.false_eq_true, if_false]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h2, [], by simp [encBits], by simp [h1]⟩
      · rintro ⟨h0, bs, h1, h2⟩
        have : bs = [] := by
          cases bs with
          | nil => rfl
          | cons b bs => cases b <;> simp [encBits_cons] at h1
        subst this
        simp at h2
        exact ⟨trivial, h2.symm, h0⟩
    · simp only [List.map_nil, List.foldl_nil, Prod.mk.injEq, if_true]
      constructor
      · rintro ⟨h, _⟩; simp at h
      · rintro ⟨_, bs, h1, _⟩
        rw [eb_one] at h1
        obtain ⟨bs', _, h⟩ := h1
        simp at h
  | c :: rest, r, M, nb, M' => by
    have ih := parse_iff rest
    simp only [List.map_cons, List.foldl_cons]
    cases c with
    | one =>
      cases r
      · have := ih true M nb M'
        simp only [ps, tk_inj_iff, if_true, Bool.false_eq_true, if_false] at this ⊢
        simpa using this
      · have := ih true M (nb + 1) M'
        simp only [ps, tk_inj_iff, if_true] at this ⊢
        rw [this]
        constructor
        · rintro ⟨h, _⟩; omega
        · rintro ⟨_, bs, h1, _⟩
          rw [eb_one] at h1
          obtain ⟨bs', _, h⟩ := h1
          cases bs' with
          | nil => simp [encBits] at h
          | cons b bs'' => cases b <;> simp [encBits_cons] at h
    | sep =>
      cases r
      · have := ih false (ty BSym.zero :: M) nb M'
        simp only [ps, tk_inj_iff, Bool.false_eq_true, if_false] at this ⊢
        simp only [reduceCtorEq, if_false, if_true]
        rw [this]
        constructor
        · rintro ⟨h0, bs, h1, h2⟩
          exact ⟨h0, false :: bs, by rw [encBits_cons]; simp [h1], by simp [h2, tyb]⟩
        · rintro ⟨h0, bs, h1, h2⟩
          rw [eb_sep] at h1
          obtain ⟨bs', rfl, h⟩ := h1
          exact ⟨h0, bs', h, by simpa [tyb] using h2⟩
      · have := ih false (ty BSym.one :: M) nb M'
        simp only [ps, tk_inj_iff, Bool.false_eq_true, if_false] at this ⊢
        simp only [reduceCtorEq, if_false, if_true]
        rw [this]
        constructor
        · rintro ⟨h0, bs, h1, h2⟩
          exact ⟨h0, true :: bs, by rw [encBits_cons]; simp [h1], by simp [h2, tyb]⟩
        · rintro ⟨h0, bs, h1, h2⟩
          rw [eb_one] at h1
          obtain ⟨bs', rfl, h⟩ := h1
          simp only [List.cons.injEq, true_and] at h
          exact ⟨h0, bs', h, by simpa [tyb] using h2⟩
    | zero =>
      have := ih r M (nb + 1) M'
      simp only [ps, tk_inj_iff, reduceCtorEq, if_false] at this ⊢
      rw [this]
      constructor
      · rintro ⟨h, _⟩; exact h.elim
      · rintro ⟨_, bs, h1, _⟩
        cases r
        · exact absurd h1 (eb_zero _ _)
        · simp only [eq_self, ↓reduceIte] at h1
          rw [eb_one] at h1
          obtain ⟨bs', _, h⟩ := h1
          cases bs' with
          | nil => simp [encBits] at h
          | cons b bs'' => cases b <;> simp [encBits_cons] at h
    | minus =>
      have := ih r M (nb + 1) M'
      simp only [ps, tk_inj_iff, reduceCtorEq, if_false] at this ⊢
      rw [this]
      constructor
      · rintro ⟨h, _⟩; exact h.elim
      · rintro ⟨_, bs, h1, _⟩
        cases r
        · exact absurd h1 (eb_minus _ _)
        · simp only [eq_self, ↓reduceIte] at h1
          rw [eb_one] at h1
          obtain ⟨bs', _, h⟩ := h1
          cases bs' with
          | nil => simp [encBits] at h
          | cons b bs'' => cases b <;> simp [encBits_cons] at h

end Stk

end Sec_Ver27

section Sec_Ver28
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def hitB : List Bool → List Bool → Bool
  | a :: t, b :: bs => (a && b) || hitB t bs
  | _, _ => false

lemma hitB_nil_right (t : List Bool) : hitB t [] = false := by cases t <;> simp [hitB]

lemma hitB_take : ∀ (t bs : List Bool), hitB t (bs.take t.length) = hitB t bs
  | [], bs => by simp [hitB]
  | a :: t, [] => by simp [hitB]
  | a :: t, b :: bs => by simp [hitB, hitB_take t bs]

lemma hitB_append : ∀ (t row rest : List Bool), row.length = t.length →
    hitB t (row ++ rest) = hitB t row
  | [], row, rest, h => by simp [hitB]
  | a :: t, [], rest, h => by simp at h
  | a :: t, b :: row, rest, h => by
    simp only [List.length_cons, add_left_inj] at h
    simp [hitB, hitB_append t row rest h]

lemma ty_inj (a b : BSym) : ty a = ty b ↔ a = b := by simp [ty]

lemma ss_one (st : Bool × List Al × ℕ) : ss st (ty BSym.one) =
    (st.1 || decide (st.2.1.head? = some (ty BSym.one)), st.2.1.tail, if st.2.1 = [] then st.2.2 + 1 else st.2.2) := by
  simp [ss, ty, mk]
lemma ss_zero (st : Bool × List Al × ℕ) : ss st (ty BSym.zero) =
    (st.1, st.2.1.tail, if st.2.1 = [] then st.2.2 + 1 else st.2.2) := by
  simp [ss, ty, mk]
lemma ss_mk (st : Bool × List Al × ℕ) : ss st mk =
    (false, st.2.1, if st.1 then st.2.2 else st.2.2 + 1) := by
  simp [ss]

lemma tyb_one_iff (b : Bool) : tyb b = ty BSym.one ↔ b = true := by cases b <;> simp [tyb, ty_inj]
lemma tyb_zero_iff (b : Bool) : tyb b = ty BSym.zero ↔ b = false := by cases b <;> simp [tyb, ty_inj]

lemma ss_row : ∀ (t bs : List Bool) (h : Bool) (nb : ℕ),
    (t.map tyb).foldl ss (h, bs.map tyb, nb) =
      (h || hitB t bs, (bs.drop t.length).map tyb, nb + (t.length - bs.length))
  | [], bs, h, nb => by simp [hitB]
  | a :: t, [], h, nb => by
    have ih := ss_row t [] (h || false) (nb + 1)
    cases a <;>
    · simp [tyb, ss_one, ss_zero, hitB_nil_right, ty_inj] at ih ⊢
      simp [ih, hitB_nil_right]
      try omega
  | a :: t, b :: bs, h, nb => by
    have ih := ss_row t bs
    cases a <;> cases b <;>
    · simp [tyb, ss_one, ss_zero, hitB, ih, ty_inj]
      try omega

end Stk

end Sec_Ver28

section Sec_Ver29
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def HitRows (t : List Bool) : ℕ → List Bool → Prop
  | 0, bs => bs = []
  | n + 1, bs => ∃ row rest, bs = row ++ rest ∧ row.length = t.length ∧ hitB t row = true ∧
      HitRows t n rest

lemma ss_rows (t : List Bool) : ∀ (n : ℕ) (bs : List Bool) (nb : ℕ),
    ((List.replicate n (t.map tyb ++ [mk])).flatten.foldl ss (false, bs.map tyb, nb) = (false, [], 0)) ↔
      (nb = 0 ∧ HitRows t n bs)
  | 0, bs, nb => by
    simp [HitRows, Prod.ext_iff, and_comm, and_left_comm]
  | n + 1, bs, nb => by
    have ih := ss_rows t n (bs.drop t.length)
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, List.foldl_append, ss_row]
    simp only [List.foldl_cons, List.foldl_nil, ss_mk, Bool.false_or]
    have key : ∀ (nb' : ℕ), ((List.replicate n (t.map tyb ++ [mk])).flatten.foldl ss
        (false, (bs.drop t.length).map tyb, nb') = (false, [], 0)) ↔ (nb' = 0 ∧ HitRows t n (bs.drop t.length)) :=
      fun nb' => ss_rows t n _ nb'
    rw [key]
    constructor
    · rintro ⟨h1, h2⟩
      have hb : hitB t bs = true := by
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        simp [hc] at h1
      have hl : t.length ≤ bs.length := by
        by_contra hc
        simp only [hb, if_true] at h1
        omega
      refine ⟨by simp only [hb, if_true] at h1; omega, bs.take t.length, bs.drop t.length, (List.take_append_drop _ _).symm, by simp; omega, ?_, h2⟩
      rw [hitB_take]; exact hb
    · rintro ⟨h0, row, rest, h1, h2, h3, h4⟩
      have hd : bs.drop t.length = rest := by
        rw [h1, List.drop_left' (by omega)]
      have hb : hitB t bs = true := by rw [h1, hitB_append _ _ _ h2]; exact h3
      rw [hd]
      refine ⟨?_, h4⟩
      simp only [hb, if_true]
      have : bs.length = row.length + rest.length := by rw [h1]; simp
      omega

end Stk

end Sec_Ver29

section Sec_Ver30
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma isBitW_tkb (b : Bool) : isBitW (tkb b) = true := by cases b <;> simp [isBitW, tkb, tk]
lemma isBitW_sep : isBitW (tk BSym.sep) = false := by simp [isBitW, tk]

lemma tw_calc : ∀ (bl : List Bool) (rest : List Al),
    (bl.map tkb ++ tk BSym.sep :: rest).takeWhile isBitW = bl.map tkb ∧
    (bl.map tkb ++ tk BSym.sep :: rest).dropWhile isBitW = tk BSym.sep :: rest
  | [], rest => by simp [isBitW_sep]
  | b :: bl, rest => by
    have := tw_calc bl rest
    simp [List.takeWhile_cons, List.dropWhile_cons, isBitW_tkb, this]

lemma bits_dec : ∀ (l : List Al), (∀ a ∈ l, isBitW a = true) → ∃ bl : List Bool, l = bl.map tkb
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨bl, hbl⟩ := bits_dec l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self)
    simp only [isBitW, decide_eq_true_eq] at ha
    rcases ha with ha | ha
    · exact ⟨false :: bl, by simp [hbl, ha, tkb, tk]⟩
    · exact ⟨true :: bl, by simp [hbl, ha, tkb, tk]⟩

lemma stNum_dec (s : St) : okNum s → ∃ (bl : List Bool) (rest : List Al),
    s Reg.W = bl.map tkb ++ tk BSym.sep :: rest := by
  intro h
  unfold okNum B1 gMvP at h
  simp only [topP, hd, upd_apply, reduceCtorEq, ↓reduceIte, if_true] at h
  cases hd' : (s Reg.W).dropWhile isBitW with
  | nil => simp [hd'] at h
  | cons x rest =>
    rw [hd'] at h
    simp only [List.head?_cons, isA, decide_eq_true_eq] at h
    subst h
    obtain ⟨bl, hbl⟩ := bits_dec ((s Reg.W).takeWhile isBitW) (fun a ha => List.mem_takeWhile_imp ha)
    refine ⟨bl, rest, ?_⟩
    rw [← hbl, ← hd']
    exact (List.takeWhile_append_dropWhile).symm

lemma stNum_calc (X : Reg) (s : St) (bl : List Bool) (rest : List Al)
    (hW : s Reg.W = bl.map tkb ++ tk BSym.sep :: rest) (hT : s Reg.TMP = [])
    (hXW : X ≠ Reg.W) (hXT : X ≠ Reg.TMP) :
    okNum s ∧ ∀ r, B3 X s r = if r = X then bl.map tkb ++ s X else if r = Reg.W then rest
      else if r = Reg.TMP then [] else s r := by
  have hc := tw_calc bl rest
  have hB1 : B1 s = upd (upd s Reg.W (tk BSym.sep :: rest)) Reg.TMP (bl.map tkb).reverse := by
    unfold B1 gMvP
    rw [hW, hc.1, hc.2]; simp [hT]
  constructor
  · unfold okNum; rw [hB1]; simp [topP, hd, upd_apply, isA]
  · intro r
    unfold B3 B2 gMvA gPop
    rw [hB1]
    by_cases h1 : r = X <;> by_cases h2 : r = Reg.W <;> by_cases h3 : r = Reg.TMP <;>
      simp [upd_apply, h1, h2, h3, hXW, hXT, hXW.symm, hXT.symm, hT] <;> subst_vars <;> simp_all

end Stk

end Sec_Ver30

section Sec_Ver31
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma al_dec : ∀ (bl : List Bool) (w : List BSym) (r : List Al),
    w.map tk = bl.map tkb ++ tk BSym.sep :: r → ∃ rest : List BSym, w = encB bl ++ rest ∧ r = rest.map tk
  | [], w, r, h => by
    cases w with
    | nil => simp at h
    | cons c w' =>
      simp only [List.map_cons, List.map_nil, List.nil_append, List.cons.injEq, tk_inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      exact ⟨w', by simp [encB, h1], h2.symm⟩
  | b :: bl, w, r, h => by
    cases w with
    | nil => simp at h
    | cons c w' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, tkb_eq, tk_inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨rest, h3, h4⟩ := al_dec bl w' r h2
      exact ⟨rest, by simp [encB, h1, h3], h4⟩

lemma stateA_W (w : List BSym) (a b : ℕ) (t : List Bool) : stateA w a b t Reg.W = w.map tk := rfl
lemma stateA_TMP (w : List BSym) (a b : ℕ) (t : List Bool) : stateA w a b t Reg.TMP = [] := rfl

lemma top_dec (w : List BSym) (a b : ℕ) (t : List Bool) (s0 : St) (hs : s0 = stateA w a b t)
    (h1 : okNum s0) (h2 : okNum (B3 Reg.MB s0)) (h3 : okNum (B3 Reg.NB (B3 Reg.MB s0))) :
    ∃ bl1 bl2 bl3 rest, w = encB bl1 ++ encB bl2 ++ encB bl3 ++ rest := by
  subst hs
  obtain ⟨bl1, r1, e1⟩ := stNum_dec _ h1
  obtain ⟨rest1, hw1, hr1⟩ := al_dec bl1 w r1 e1
  obtain ⟨_, c1⟩ := stNum_calc Reg.MB _ bl1 r1 e1 (stateA_TMP w a b t) (by decide) (by decide)
  obtain ⟨bl2, r2, e2⟩ := stNum_dec _ h2
  rw [c1 Reg.W] at e2
  simp only [reduceCtorEq, ↓reduceIte] at e2
  have e2' : r1 = bl2.map tkb ++ tk BSym.sep :: r2 := e2
  rw [hr1] at e2'
  obtain ⟨rest2, hw2, hr2⟩ := al_dec bl2 rest1 r2 e2'
  have hT1 : B3 Reg.MB (stateA w a b t) Reg.TMP = [] := by rw [c1]; simp [stateA_TMP]
  obtain ⟨_, c2⟩ := stNum_calc Reg.NB (B3 Reg.MB (stateA w a b t)) bl2 r2
    (by rw [c1 Reg.W]; simpa using e2) hT1 (by decide) (by decide)
  obtain ⟨bl3, r3, e3⟩ := stNum_dec _ h3
  rw [c2 Reg.W, c1 Reg.W] at e3
  simp only [reduceCtorEq, ↓reduceIte] at e3
  have e3' : r2 = bl3.map tkb ++ tk BSym.sep :: r3 := e3
  rw [hr2] at e3'
  obtain ⟨rest3, hw3, hr3⟩ := al_dec bl3 rest2 r3 e3'
  exact ⟨bl1, bl2, bl3, rest3, by rw [hw1, hw2, hw3]; simp⟩

end Stk

end Sec_Ver31

section Sec_Ver32
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def sQ3 (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) : St := fun r =>
  match r with
  | Reg.W => rest.map tk
  | Reg.N => List.replicate a (ty BSym.sep)
  | Reg.K => List.replicate b (ty BSym.minus)
  | Reg.T => t.map tyb
  | Reg.MB => bl1.map tkb
  | Reg.NB => bl2.map tkb
  | Reg.KB => bl3.map tkb
  | _ => []

lemma encB_map_tk (bl : List Bool) (rest : List BSym) :
    (encB bl ++ rest).map tk = bl.map tkb ++ tk BSym.sep :: rest.map tk := by
  simp [encB, tkb_eq, List.map_map, Function.comp_def]

lemma top_calc (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    let s0 := stateA (encB bl1 ++ encB bl2 ++ encB bl3 ++ rest) a b t
    (okNum s0 ∧ okNum (B3 Reg.MB s0) ∧ okNum (B3 Reg.NB (B3 Reg.MB s0))) ∧
    B3 Reg.KB (B3 Reg.NB (B3 Reg.MB s0)) = sQ3 bl1 bl2 bl3 rest a b t := by
  intro s0
  have hW0 : s0 Reg.W = bl1.map tkb ++ tk BSym.sep :: (encB bl2 ++ encB bl3 ++ rest).map tk := by
    show (encB bl1 ++ encB bl2 ++ encB bl3 ++ rest).map tk = _
    have := encB_map_tk bl1 (encB bl2 ++ encB bl3 ++ rest)
    simpa [List.append_assoc] using this
  obtain ⟨o1, c1⟩ := stNum_calc Reg.MB s0 bl1 _ hW0 (stateA_TMP _ a b t) (by decide) (by decide)
  have hW1 : B3 Reg.MB s0 Reg.W = bl2.map tkb ++ tk BSym.sep :: (encB bl3 ++ rest).map tk := by
    rw [c1 Reg.W]; simp only [reduceCtorEq, ↓reduceIte]
    rw [List.append_assoc, encB_map_tk]
  have hT1 : B3 Reg.MB s0 Reg.TMP = [] := by rw [c1]; simp
  obtain ⟨o2, c2⟩ := stNum_calc Reg.NB _ bl2 _ hW1 hT1 (by decide) (by decide)
  have hW2 : B3 Reg.NB (B3 Reg.MB s0) Reg.W = bl3.map tkb ++ tk BSym.sep :: rest.map tk := by
    rw [c2 Reg.W]; simp only [reduceCtorEq, ↓reduceIte]
    rw [encB_map_tk]
  have hT2 : B3 Reg.NB (B3 Reg.MB s0) Reg.TMP = [] := by rw [c2]; simp [hT1]
  obtain ⟨o3, c3⟩ := stNum_calc Reg.KB _ bl3 _ hW2 hT2 (by decide) (by decide)
  refine ⟨⟨o1, o2, o3⟩, ?_⟩
  have h0 : ∀ r, s0 r = stateA (encB bl1 ++ encB bl2 ++ encB bl3 ++ rest) a b t r := fun _ => rfl
  clear_value s0
  funext r
  rw [c3 r]
  cases r <;> simp [c2, c1, h0, stateA, sQ3, hT1]

end Stk

end Sec_Ver32

section Sec_Ver33
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma posB_pre (bl1 bl3 : List Bool) (rest : List BSym) (n k : ℕ) (t : List Bool) :
    posB.pre (sP bl1 bl3 rest n k t) := by
  simp only [posB, GB.seq, bEq, bBad, bCopy, bFill, bPush, bRc, bDrain, bParse, bScan, bMvA, bClear, GB.ofGs]
  simp only [eqT, gCopy, gPush, gRc, dcF, flF, upd_apply, sP, reduceCtorEq, ↓reduceIte, id, Gi]
  simp [hd, isNoneT, topS, PInv, SInv, paF, sP, gMvA, gClear]

lemma negB_pre (bl1 bl3 : List Bool) (rest : List BSym) (k : ℕ) (t : List Bool) :
    negB.pre (sP bl1 bl3 rest 0 k t) := by
  simp only [negB, GB.seq, bBad, bCopy, bClear, bMvA, bCmp, GB.ofGs]
  simp only [gCopy, upd_apply, sP, reduceCtorEq, ↓reduceIte, id, Gi]
  simp [hd, topS, sP, gMvA, gClear, cmpF, CInv]

def PosCl (bl1 bl3 : List Bool) (rest : List BSym) (n k : ℕ) (t : List Bool) : Prop :=
  List.map tkb bl3 = List.map tkb k.bits ∧ ¬k = 0 ∧ List.map tkb bl1 = List.map tkb t.length.bits ∧
  k + ((k + 1) * n + 1) ≤ t.length ∧ List.countP (isA (ty BSym.one) ∘ tyb) t ≤ k ∧
  (List.foldl ps (false, [], 0) (List.map tk rest)).2.2 = 0 ∧
  (List.foldl ps (false, [], 0) (List.map tk rest)).1 = false ∧
  (List.foldl ss (false, (List.foldl ps (false, [], 0) (List.map tk rest)).2.1.reverse, 0)
      (List.replicate n (List.map tyb t ++ [mk])).flatten).2.2 = 0 ∧
  (List.foldl ss (false, (List.foldl ps (false, [], 0) (List.map tk rest)).2.1.reverse, 0)
      (List.replicate n (List.map tyb t ++ [mk])).flatten).2.1 = []

lemma posB_ok_cl (bl1 bl3 : List Bool) (rest : List BSym) (n k : ℕ) (t : List Bool) :
    posB.ok (sP bl1 bl3 rest n k t) ↔ PosCl bl1 bl3 rest n k t := by
  simp only [posB, GB.seq, bEq, bBad, bCopy, bFill, bPush, bRc, bDrain, bParse, bScan, bMvA, bClear, GB.ofGs]
  simp only [eqT, gCopy, gPush, gRc, dcF, flF, upd_apply, sP, reduceCtorEq, ↓reduceIte, id]
  simp [hd, gClear, isNoneT, topS, paNB, scNB, sP, gMvA, paF, scF, upd_apply, PosCl]

def NegCl (bl1 bl3 : List Bool) (rest : List BSym) : Prop :=
  rest = [] ∧
    (¬bl1.getLast? = some false ∨ ¬tkb false = tk BSym.one → bl1.getLast? = some true ∧ tkb true = tk BSym.one) ∧
      (¬bl3.getLast? = some false ∨ ¬tkb false = tk BSym.one → bl3.getLast? = some true ∧ tkb true = tk BSym.one) ∧
        cf (List.map tkb bl1) (List.map tkb bl3) false = true

lemma negB_ok_cl (bl1 bl3 : List Bool) (rest : List BSym) (k : ℕ) (t : List Bool) :
    negB.ok (sP bl1 bl3 rest 0 k t) ↔ NegCl bl1 bl3 rest := by
  simp only [negB, GB.seq, bBad, bCopy, bClear, bMvA, bCmp, GB.ofGs]
  simp only [gCopy, upd_apply, sP, reduceCtorEq, ↓reduceIte, id, Gi]
  simp [hd, isNoneT, notOneT, topS, sP, gMvA, gClear, cmpF, upd_apply, NegCl]

end Stk

end Sec_Ver33

section Sec_Ver34
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma tkb_inj : Function.Injective tkb := by
  intro a b h
  cases a <;> cases b <;> simp_all [tkb, tk, bsb]

lemma map_tkb_eq (a b : List Bool) : a.map tkb = b.map tkb ↔ a = b :=
  List.map_inj_right tkb_inj

lemma countP_tyb (t : List Bool) : List.countP (isA (ty BSym.one) ∘ tyb) t = t.count true := by
  induction t with
  | nil => simp
  | cons b t ih =>
    cases b <;> simp [List.countP_cons, ih, isA, tyb, ty_inj, List.count_cons]

lemma ss_rows_fst (t : List Bool) : ∀ (n : ℕ) (bs : List Bool) (nb : ℕ),
    ((List.replicate n (t.map tyb ++ [mk])).flatten.foldl ss (false, bs.map tyb, nb)).1 = false
  | 0, bs, nb => by simp
  | n + 1, bs, nb => by
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, List.foldl_append, ss_row]
    simp only [List.foldl_cons, List.foldl_nil, ss_mk]
    exact ss_rows_fst t n _ _

lemma posB_ok_iff (bl1 bl3 : List Bool) (rest : List BSym) (n k : ℕ) (t : List Bool) :
    posB.ok (sP bl1 bl3 rest n k t) ↔
      (bl3 = k.bits ∧ k ≠ 0 ∧ bl1 = t.length.bits ∧ k + ((k + 1) * n + 1) ≤ t.length ∧
        t.count true ≤ k ∧ ∃ bs, rest = encBits bs ∧ HitRows t n bs) := by
  rw [posB_ok_cl]
  unfold PosCl
  rw [map_tkb_eq, map_tkb_eq, countP_tyb]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    set X := List.foldl ps (false, [], 0) (List.map tk rest) with hX
    have hX' : X = (false, X.2.1, 0) := by
      obtain ⟨a, b, c⟩ := X
      simp only at h6 h7
      simp [h6, h7]
    have hp := (parse_iff rest false [] 0 X.2.1).1 hX'
    obtain ⟨-, bs, hbs, hM⟩ := hp
    refine ⟨bs, by simpa using hbs, ?_⟩
    have hrev : X.2.1.reverse = bs.map tyb := by
      rw [hM]; simp [List.map_reverse]
    rw [hrev] at h8 h9
    have := (ss_rows t n bs 0).1 (by
      have hf := ss_rows_fst t n bs 0
      generalize List.foldl ss (false, bs.map tyb, 0) (List.replicate n (List.map tyb t ++ [mk])).flatten = Y at h8 h9 hf ⊢
      obtain ⟨a, b, c⟩ := Y
      simp only at h8 h9 hf
      simp [h8, h9, hf])
    exact this.2
  · rintro ⟨h1, h2, h3, h4, h5, bs, hbs, hh⟩
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    have hp := (parse_iff rest false [] 0 (bs.reverse.map tyb)).2 ⟨rfl, bs, by simpa using hbs, by simp⟩
    rw [hp]
    have hs := (ss_rows t n bs 0).2 ⟨rfl, hh⟩
    simp only [List.map_reverse, List.reverse_reverse, List.append_nil]
    simp [hs]

lemma negB_ok_iff (bl1 bl3 : List Bool) (rest : List BSym) (k : ℕ) (t : List Bool) :
    negB.ok (sP bl1 bl3 rest 0 k t) ↔
      (rest = [] ∧ bl1.getLast? = some true ∧ bl3.getLast? = some true ∧ val bl3 < val bl1) := by
  rw [negB_ok_cl]
  unfold NegCl
  rw [cf_val]
  have e1 : tkb false ≠ tk BSym.one := by simp [tkb, tk, bsb]
  have e2 : tkb true = tk BSym.one := by simp [tkb, tk, bsb]
  simp [e1, e2]

end Stk

end Sec_Ver34

section Sec_Ver35
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma eqT_pop (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    eqT Reg.NB (gPop Reg.N (sQ3 bl1 bl2 bl3 rest a b t)) = sP bl1 bl3 rest (a - 1) b t := by
  funext r
  cases r <;> simp [eqT, gPop, sQ3, sP, upd_apply, List.tail_replicate]

lemma pop_NB (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    gPop Reg.N (sQ3 bl1 bl2 bl3 rest a b t) Reg.NB = bl2.map tkb := by
  simp [gPop, sQ3, upd_apply]

lemma pop_N (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    (gPop Reg.N (sQ3 bl1 bl2 bl3 rest a b t) Reg.N).length = a - 1 := by
  simp [gPop, sQ3, upd_apply]

lemma pop_Nuni (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    ∃ c, gPop Reg.N (sQ3 bl1 bl2 bl3 rest a b t) Reg.N =
      List.replicate (gPop Reg.N (sQ3 bl1 bl2 bl3 rest a b t) Reg.N).length c := by
  refine ⟨ty BSym.sep, ?_⟩
  simp [gPop, sQ3, upd_apply, List.tail_replicate]

lemma topS_sP (bl1 bl3 : List Bool) (rest : List BSym) (n b : ℕ) (t : List Bool) :
    topS Reg.N (hd (sP bl1 bl3 rest n b t)) = true ↔ n ≠ 0 := by
  cases n <;> simp [topS, hd, sP, List.replicate_succ]

lemma topB_ok_iff (w : List BSym) (a b : ℕ) (t : List Bool) :
    topB.ok (stateA w a b t) ↔ ∃ bl1 bl2 bl3 rest, w = encB bl1 ++ encB bl2 ++ encB bl3 ++ rest ∧
      bl2 = (a - 1).bits ∧ ((a - 1 = 0 → negB.ok (sP bl1 bl3 rest 0 b t)) ∧
        (a - 1 ≠ 0 → posB.ok (sP bl1 bl3 rest (a - 1) b t))) := by
  simp only [topB, GB.seq, bStNum, bPop, bEq, GB.ofGs, GB.branch]
  constructor
  · rintro ⟨h1, h2, h3, -, h5, h6⟩
    obtain ⟨bl1, bl2, bl3, rest, hw⟩ := top_dec w a b t _ rfl h1 h2 h3
    subst hw
    have hc := (top_calc bl1 bl2 bl3 rest a b t).2
    try simp only at hc
    rw [hc] at h5 h6
    rw [pop_NB, pop_N, map_tkb_eq] at h5
    rw [eqT_pop] at h6
    refine ⟨bl1, bl2, bl3, rest, rfl, h5, ?_, ?_⟩
    · intro h0
      rw [if_neg] at h6
      · rw [h0] at h6; exact h6
      · simp [topS_sP, h0]
    · intro h0
      rw [if_pos] at h6
      · exact h6
      · simpa [topS_sP] using h0
  · rintro ⟨bl1, bl2, bl3, rest, hw, hb2, hneg, hpos⟩
    subst hw
    have hc := (top_calc bl1 bl2 bl3 rest a b t)
    try simp only at hc
    obtain ⟨⟨o1, o2, o3⟩, hc⟩ := hc
    refine ⟨o1, o2, o3, trivial, ?_, ?_⟩
    · rw [hc, pop_NB, pop_N, hb2]
    · rw [hc, eqT_pop]
      by_cases h0 : a - 1 = 0
      · rw [if_neg (by simp [topS_sP, h0])]
        have := hneg h0
        rw [h0]
        exact this
      · rw [if_pos (by simpa [topS_sP] using h0)]
        exact hpos h0

end Stk

end Sec_Ver35

section Sec_Ver36
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma topB_pre (w : List BSym) (a b : ℕ) (t : List Bool) : topB.pre (stateA w a b t) := by
  simp only [topB, GB.seq, bStNum, bPop, bEq, GB.ofGs, GB.branch]
  refine ⟨trivial, fun _ _ o1 => ⟨trivial, fun _ _ o2 => ⟨trivial, fun _ _ o3 => ⟨trivial, fun _ _ _ => ?_⟩⟩⟩⟩
  obtain ⟨bl1, bl2, bl3, rest, hw⟩ := top_dec w a b t _ rfl o1 o2 o3
  subst hw
  have hc := (top_calc bl1 bl2 bl3 rest a b t).2
  try simp only at hc
  rw [hc]
  refine ⟨pop_Nuni _ _ _ _ _ _ _, fun _ _ _ => ?_⟩
  rw [eqT_pop]
  by_cases h0 : a - 1 = 0
  · rw [if_neg (by simp [topS_sP, h0])]
    rw [h0]; exact negB_pre _ _ _ _ _
  · rw [if_pos (by simpa [topS_sP] using h0)]
    exact posB_pre _ _ _ _ _ _

lemma full_out (s : St) : fullB.g s Reg.OUT ≠ [] ↔ fullB.g s Reg.BAD = [] := by
  have hb := bOut.h.2.2.1
  simp only [fullB, GB.seq, bOut, GB.ofGs]
  generalize topB.g (gA s) = u
  have e1 : outG u Reg.BAD = u Reg.BAD := hb u
  have e2 := outG_OUT u
  rw [e1, e2]
  by_cases h : u Reg.BAD = [] <;> simp [h]

lemma full_pre (x : List Al) : fullB.pre (init x) := by
  simp only [fullB, GB.seq, GB.ofGs]
  refine ⟨trivial, fun _ _ hok => ?_⟩
  obtain ⟨w, a, b, t, hx⟩ := stA_dec x hok
  subst hx
  have hA := (stA_eval w a b t).2
  show topB.pre (A7 _) ∧ _
  rw [hA]
  refine ⟨topB_pre _ _ _ _, fun _ _ _ => trivial⟩

lemma full_iff (x : List Al) :
    fullB.g (init x) Reg.OUT ≠ [] ↔ ∃ w a b t, x = Fm w a b t ∧ topB.ok (stateA w a b t) := by
  rw [full_out]
  have gi : Gi (init x) := by simp [Gi, init]
  have hbad : init x Reg.BAD = [] := by simp [init]
  have key := (fullB.h.2.2.2 (init x) gi (full_pre x) hbad).1
  rw [key]
  simp only [fullB, GB.seq, bOut, GB.ofGs]
  constructor
  · rintro ⟨hok, hb, -⟩
    obtain ⟨w, a, b, t, hx⟩ := stA_dec x hok
    subst hx
    refine ⟨w, a, b, t, rfl, ?_⟩
    have hA := (stA_eval w a b t).2
    rw [hA] at hb
    exact hb
  · rintro ⟨w, a, b, t, hx, hok⟩
    subst hx
    obtain ⟨h1, h2⟩ := stA_eval w a b t
    refine ⟨h1, ?_, trivial⟩
    show topB.ok (A7 _)
    rw [h2]; exact hok

end Stk

end Sec_Ver36

section Sec_Ver37
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma S_init (x : List Al) : S (init x) = x.length := by
  unfold S init
  rw [Finset.sum_eq_single Reg.IN]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma poly_of_gad {p : Prog} {g : St → St} (h : Gad p g) :
    ∃ k, ∀ x : List Al, ∃ s n, n ≤ x.length ^ k + k ∧
      p.Exec (fun j => if j = Reg.IN then x else []) s n ∧ s = g (init x) := by
  obtain ⟨d, hd⟩ := h.1
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ d) d 0
  refine ⟨k, fun x => ?_⟩
  have gi : Gi (init x) := by simp [Gi, init]
  obtain ⟨n, hn, ex⟩ := hd (init x) gi
  refine ⟨g (init x), n, ?_, ex, rfl⟩
  rw [S_init] at hn
  have h1 := hk x.length
  have h2 : (x.length + 2) ^ d ≤ 2 ^ d * (x.length + 1) ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  omega

theorem mem_P_of_full (L : Lang Al) (hL : ∀ x, x ∈ L ↔ fullB.g (init x) Reg.OUT ≠ []) : L ∈ P Al := by
  have hpoly : PolyTimeComputable (fun x : List Al => fullB.g (init x) Reg.OUT) := by
    obtain ⟨k, hk⟩ := poly_of_gad fullB.h.1
    refine stack_program_polytime fullB.p Reg.IN Reg.OUT _ k (fun x => ?_)
    obtain ⟨s, n, hn, ex, hs⟩ := hk x
    exact ⟨s, n, hn, ex, by rw [hs]⟩
  refine mem_P_of_polyReducible L {w : List Al | w ≠ []} ⟨_, hpoly, fun x => ?_⟩ (neLang_mem_P Al)
  rw [hL]; rfl

end Stk

end Sec_Ver37

section Sec_Ver38
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def Rel (w : List BSym) (y : List BSym) : Prop :=
  ∃ a b t, y = List.replicate a BSym.sep ++ List.replicate b BSym.minus ++ t.map bsb ∧
    topB.ok (stateA w a b t)

lemma fm_eq (w : List BSym) (a b : ℕ) (t : List Bool) :
    Fm w a b t = w.map (some ∘ Sum.inl) ++ none ::
      ((List.replicate a BSym.sep ++ List.replicate b BSym.minus ++ t.map bsb).map (some ∘ Sum.inr)) := by
  unfold Fm
  simp only [List.map_append, List.map_replicate, List.map_map]
  rfl

lemma checkLang_iff (x : List Al) :
    x ∈ checkLang Rel ↔ ∃ w a b t, x = Fm w a b t ∧ topB.ok (stateA w a b t) := by
  constructor
  · rintro ⟨w, y, ⟨a, b, t, hy, hok⟩, hx⟩
    refine ⟨w, a, b, t, ?_, hok⟩
    rw [hx, hy, fm_eq]
  · rintro ⟨w, a, b, t, hx, hok⟩
    refine ⟨w, _, ⟨a, b, t, rfl, hok⟩, ?_⟩
    rw [hx, fm_eq]

theorem checkLang_mem_P : checkLang Rel ∈ P Al := by
  refine mem_P_of_full _ (fun x => ?_)
  rw [full_iff, checkLang_iff]

end Stk

end Sec_Ver38

section Sec_Ver39
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma hitB_iff : ∀ (t row : List Bool), hitB t row = true ↔
    ∃ j : ℕ, t[j]? = some true ∧ row[j]? = some true
  | [], row => by simp [hitB]
  | a :: t, [] => by simp [hitB]
  | a :: t, b :: row => by
    rw [show hitB (a :: t) (b :: row) = ((a && b) || hitB t row) from rfl]
    rw [Bool.or_eq_true, hitB_iff t row]
    constructor
    · rintro (h | ⟨j, h1, h2⟩)
      · refine ⟨0, ?_, ?_⟩ <;> simp_all
      · exact ⟨j + 1, by simpa using h1, by simpa using h2⟩
    · rintro ⟨j, h1, h2⟩
      cases j with
      | zero => left; simp_all
      | succ j => right; exact ⟨j, by simpa using h1, by simpa using h2⟩

lemma encNat_eq (k : ℕ) : encNat k = encB (Nat.bits k) := rfl

lemma encNats_bits : ∀ bs : List Bool,
    encNats (bs.map (fun b => if b then 1 else 0)) = encBits bs
  | [] => by simp [encNats, encBits]
  | b :: bs => by
    have ih := encNats_bits bs
    cases b
    · simp only [List.map_cons, encNats, List.flatMap_cons] at ih ⊢
      rw [ih, encBits_cons]
      simp [encNat]
    · simp only [List.map_cons, encNats, List.flatMap_cons] at ih ⊢
      rw [ih, encBits_cons]
      simp [encNat]

lemma HitRows_ofFn (t : List Bool) : ∀ (n : ℕ) (rows : Fin n → List Bool),
    (∀ i, (rows i).length = t.length ∧ hitB t (rows i) = true) →
    HitRows t n (List.ofFn rows).flatten
  | 0, rows, _ => by simp [HitRows]
  | n + 1, rows, h => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine ⟨rows 0, (List.ofFn fun i : Fin n => rows i.succ).flatten, rfl, (h 0).1, (h 0).2, ?_⟩
    exact HitRows_ofFn t n _ (fun i => h i.succ)

lemma HitRows_extract (t : List Bool) : ∀ (n : ℕ) (bs : List Bool), HitRows t n bs →
    ∃ rows : Fin n → List Bool, (∀ i, (rows i).length = t.length ∧ hitB t (rows i) = true) ∧
      bs = (List.ofFn rows).flatten
  | 0, bs, h => ⟨Fin.elim0, fun i => i.elim0, by simpa [HitRows] using h⟩
  | n + 1, bs, h => by
    obtain ⟨row, rest, hbs, hl, hh, hr⟩ := h
    obtain ⟨rows, hrows, hrest⟩ := HitRows_extract t n rest hr
    refine ⟨Fin.cons row rows, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ⟨hl, hh⟩
      · simpa using hrows j
    · rw [List.ofFn_succ, List.flatten_cons, hbs, hrest]
      simp

end Stk

end Sec_Ver39

section Sec_Ver40
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

def mat {m n : ℕ} (S : Fin n → Finset (Fin m)) : Fin n → List Bool :=
  fun i => List.ofFn fun j : Fin m => decide (j ∈ S i)

def tvec {m : ℕ} (B : Finset (Fin m)) : List Bool := List.ofFn fun j : Fin m => decide (j ∈ B)

lemma mat_length {m n : ℕ} (S : Fin n → Finset (Fin m)) (i : Fin n) : (mat S i).length = m := by
  simp [mat]

lemma tvec_length {m : ℕ} (B : Finset (Fin m)) : (tvec B).length = m := by simp [tvec]

lemma hsCode_eq (m n k : ℕ) (S : Fin n → Finset (Fin m)) :
    hsCode m n k S = encB m.bits ++ encB n.bits ++ encB k.bits ++ encBits (List.ofFn (mat S)).flatten := by
  unfold hsCode
  have e : (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => if j ∈ S i then 1 else 0).flatten =
      ((List.ofFn (mat S)).flatten).map (fun b : Bool => if b then 1 else 0) := by
    simp [mat, List.map_flatten, List.map_ofFn, Function.comp_def]
  rw [e, ← encNats_bits]
  simp [encNats, encNat_eq]

lemma count_tvec {m : ℕ} (B : Finset (Fin m)) : (tvec B).count true = B.card := by
  have h1 : ∀ l : List Bool, l.count true = (l.map Bool.toNat).sum := by
    intro l; induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [List.count_cons, ih] <;> omega
  rw [h1, tvec, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def]
  have : ∀ x : Fin m, (decide (x ∈ B)).toNat = if x ∈ B then 1 else 0 := fun x => by
    by_cases h : x ∈ B <;> simp [h]
  simp [this, Finset.sum_boole]

lemma hitB_mat {m n : ℕ} (S : Fin n → Finset (Fin m)) (B : Finset (Fin m)) (i : Fin n) :
    hitB (tvec B) (mat S i) = true ↔ (S i ∩ B).Nonempty := by
  rw [hitB_iff]
  constructor
  · rintro ⟨j, h1, h2⟩
    simp only [tvec, mat, List.getElem?_ofFn] at h1 h2
    by_cases hj : j < m
    · refine ⟨⟨j, hj⟩, ?_⟩
      simp [hj] at h1 h2
      simp [h1, h2]
    · simp [hj] at h1
  · rintro ⟨j, hj⟩
    rw [Finset.mem_inter] at hj
    refine ⟨j.1, ?_, ?_⟩
    · simp [tvec, List.getElem?_ofFn, hj.2]
    · simp [mat, List.getElem?_ofFn, hj.1]

end Stk

end Sec_Ver40

section Sec_Ver41
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma encBits_length_ge : ∀ bs : List Bool, bs.length ≤ (encBits bs).length
  | [] => by simp [encBits]
  | b :: bs => by
    have := encBits_length_ge bs
    rw [encBits_cons]; cases b <;> simp <;> omega

lemma mat_flat_length {m n : ℕ} (S : Fin n → Finset (Fin m)) :
    (List.ofFn (mat S)).flatten.length = n * m := by
  simp [List.length_flatten, List.map_ofFn, Function.comp_def, mat_length, List.sum_ofFn]

theorem sem_fwd (w : List BSym) (hw : w ∈ restrictedHSLang) :
    ∃ y : List BSym, y.length ≤ w.length ^ 2 ∧ Rel w y := by
  obtain ⟨m, n, k, S, hk, hmn, ⟨B, hB, hit⟩, rfl⟩ := hw
  rw [hsCode_eq]
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · refine ⟨[BSym.sep], ?_, 1, 0, [], by simp, ?_⟩
    · have : 1 ≤ (encB m.bits).length := by simp [encB]
      simp only [List.length_append]
      exact Nat.one_le_pow _ _ (by omega)
    rw [topB_ok_iff]
    refine ⟨m.bits, (1 - 1).bits, k.bits, [], ?_, rfl, fun _ => ?_, fun h => absurd rfl h⟩
    · simp [encBits]
    · rw [negB_ok_iff]
      refine ⟨rfl, getLast_bits _ (by omega), getLast_bits _ (by omega), ?_⟩
      rw [val_bits, val_bits]; omega
  · refine ⟨List.replicate (n + 1) BSym.sep ++ List.replicate k BSym.minus ++
      (tvec B).map bsb, ?_, n + 1, k, tvec B, rfl, ?_⟩
    · have h1 := encBits_length_ge (List.ofFn (mat S)).flatten
      rw [mat_flat_length] at h1
      have hy : (List.replicate (n + 1) BSym.sep ++ List.replicate k BSym.minus ++
          (tvec B).map bsb).length = n + 1 + k + m := by
        simp only [List.length_append, List.length_replicate, List.length_map, tvec_length]
      rw [hy]
      have h2 : n * m ≤ (encB m.bits ++ encB n.bits ++ encB k.bits ++
          encBits (List.ofFn (mat S)).flatten).length := by
        simp only [List.length_append]; omega
      generalize (encB m.bits ++ encB n.bits ++ encB k.bits ++
          encBits (List.ofFn (mat S)).flatten).length = L at h2 ⊢
      have h3 : m ≤ n * m := Nat.le_mul_of_pos_left m hn
      have h4 : n * (k + 1) = n * k + n := by ring
      have h5 : n + 1 + k ≤ m := by nlinarith
      have h6 : 2 ≤ m := by omega
      have h7 : m ≤ L := by omega
      have h8 : 2 * L ≤ L ^ 2 := by nlinarith
      omega
    · rw [topB_ok_iff]
      refine ⟨m.bits, n.bits, k.bits, encBits (List.ofFn (mat S)).flatten, ?_, by simp,
        fun h => absurd (by simpa using h) (by omega), fun _ => ?_⟩
      · rfl
      · simp only [Nat.add_sub_cancel]
        rw [posB_ok_iff]
        refine ⟨rfl, by omega, by rw [tvec_length], by rw [tvec_length]; nlinarith, by
          rw [count_tvec]; exact hB, _, rfl, HitRows_ofFn _ _ _ (fun i => ⟨?_, ?_⟩)⟩
        · rw [mat_length, tvec_length]
        · rw [hitB_mat]; exact hit i

end Stk

end Sec_Ver41

section Sec_Ver42
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma exists_fin (m : ℕ) (l : List Bool) (h : l.length = m) :
    ∃ F : Finset (Fin m), tvec F = l := by
  refine ⟨Finset.univ.filter (fun j : Fin m => l[j.1]? = some true), ?_⟩
  apply List.ext_getElem
  · simp [tvec, h]
  · intro i h1 h2
    have hi : i < m := by simpa [tvec] using h1
    simp [tvec, List.getElem_ofFn, Finset.mem_filter, List.getElem?_eq_getElem h2]

theorem sem_bwd (w y : List BSym) (h : Rel w y) : w ∈ restrictedHSLang := by
  obtain ⟨a, b, t, -, hok⟩ := h
  rw [topB_ok_iff] at hok
  obtain ⟨bl1, bl2, bl3, rest, hw, hbl2, h0, h1⟩ := hok
  by_cases ha : a - 1 = 0
  · have h0 := h0 ha
    rw [negB_ok_iff] at h0
    obtain ⟨hr, g1, g3, hv⟩ := h0
    have e1 := bits_val_of_canon bl1 (Or.inl g1)
    have e3 := bits_val_of_canon bl3 (Or.inl g3)
    have hk : 1 ≤ val bl3 := by
      by_contra hc
      have : val bl3 = 0 := by omega
      rw [this] at e3
      simp at e3
      subst e3
      simp at g3
    refine ⟨val bl1, 0, val bl3, fun i => Fin.elim0 i, hk, by omega,
      ⟨∅, by simp, fun i => Fin.elim0 i⟩, ?_⟩
    rw [hsCode_eq, hw, hbl2, ha, hr, e1, e3]
    simp [encBits]
  · have h1 := h1 ha
    rw [posB_ok_iff] at h1
    obtain ⟨e3, hk0, e1, hle, hcnt, bs, hrest, hr⟩ := h1
    obtain ⟨rows, hrows, hbs⟩ := HitRows_extract t (a - 1) bs hr
    have hS : ∀ i, ∃ F : Finset (Fin t.length), tvec F = rows i :=
      fun i => exists_fin _ _ (hrows i).1
    choose S hS using hS
    obtain ⟨B, hB⟩ := exists_fin t.length t rfl
    have hm : mat S = rows := by funext i; exact hS i
    refine ⟨t.length, a - 1, b, S, by omega, by rw [Nat.mul_comm]; omega,
      ⟨B, ?_, fun i => ?_⟩, ?_⟩
    · rw [← count_tvec, hB]; exact hcnt
    · rw [← hitB_mat, hB, show mat S i = rows i from congrFun hm i]
      exact (hrows i).2
    · rw [hsCode_eq, hw, hbl2, e1, e3, hm, ← hbs, hrest]

end Stk

end Sec_Ver42

section Sec_Ver43
set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity
namespace HHRControl.PV

theorem restrictedHS_in_NP : restrictedHSLang ∈ NP BSym := by
  refine ⟨BSym, inferInstance, ⟨BSym.zero⟩, Stk.Rel, 2, Stk.checkLang_mem_P, fun w => ⟨fun h => ?_, fun ⟨y, _, hy⟩ => ?_⟩⟩
  · exact Stk.sem_fwd w h
  · exact Stk.sem_bwd w y hy

end HHRControl.PV

end Sec_Ver43

section Sec_Ver44
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma loop_execJ {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    have hgs := hinv s hs ht
    by_cases ht2 : t (hd (g s)) = true
    · obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl hgs
      refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
      · rw [← hm]
        have hg := hgrow s hs ht ht2
        have hY : S (g s) + c * μ (g s) + 2 ≤ S s + c * μ s + 2 := by
          have : c * μ (g s) + c ≤ c * μ s := by
            have : μ (g s) + 1 ≤ μ s := hlt
            nlinarith
          omega
        have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h2 : n2 ≤ (μ (g s) + 1) * ((S s + c * μ s + 2) ^ d + 3) :=
          le_trans hn2 (Nat.mul_le_mul_left _ (by
            have := Nat.pow_le_pow_left hY d; omega))
        have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
        have h4 : (μ (g s) + 1 + 1) * ((S s + c * μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        nlinarith
      · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
    · have ht2' : t (hd (g s)) = false := by simpa using ht2
      refine ⟨1 + n1 + 1 + 1, ?_, ?_⟩
      · rw [← hm]
        have h1 : n1 ≤ (S s + c * μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h3 : 2 ≤ μ s + 1 := by omega
        have h4 : 2 * ((S s + c * μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        omega
      · have e3 : (StackProg.loop t p).Exec (g s) (G (g s)) 1 := by
          rw [hstop (g s) hgs ht2']; exact StackProg.Exec.loopFalse ht2'
        rw [hG]
        exact StackProg.Exec.loopTrue ht e1 e3
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + c * m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loopJ {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {c : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) ≤ S s + c)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨(c + 1) * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + c * μ s + 2 ≤ X ^ (c + 1) := by
    have : S s + c * μ s + 2 ≤ (c + 1) * X := by nlinarith
    have hc : c + 1 ≤ X ^ c := le_trans (Nat.lt_two_pow_self (n := c)) (Nat.pow_le_pow_left hX2 c)
    calc _ ≤ (c + 1) * X := this
      _ ≤ X ^ c * X := Nat.mul_le_mul_right _ hc
      _ = X ^ (c + 1) := by rw [pow_succ]
  have a2 : (S s + c * μ s + 2) ^ d ≤ X ^ ((c + 1) * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ ((c + 1) * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + c * μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + c * μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ ((c + 1) * d + 3) := by rw [hZ]; ring

lemma PSp.seq2 {I1 I2 : (K → List A) → Prop} {p q : StackProg K A}
    {g h : (K → List A) → (K → List A)}
    (hp : PSp I1 p g) (hq : PSp I2 q h) (hi : ∀ s, I1 s → I2 (g s)) :
    PSp I1 (.seq p q) (fun s => h (g s)) := by
  obtain ⟨d1, hp⟩ := hp
  obtain ⟨d2, hq⟩ := hq
  refine ⟨d1 + 3 + (Fintype.card K + d1 + 2) * d2, fun s hs => ?_⟩
  obtain ⟨n1, hn1, e1⟩ := hp s hs
  obtain ⟨n2, hn2, e2⟩ := hq (g s) (hi s hs)
  refine ⟨n1 + 1 + n2, ?_, StackProg.Exec.seq e1 e2⟩
  set X := S s + 2 with hXd
  have hX : 2 ≤ X := by omega
  have hsz := Exec_size e1
  have hY : S (g s) + 2 ≤ X ^ (Fintype.card K + d1 + 2) := by
    have a1 : X ≤ X ^ 1 := by simp
    have a2 : Fintype.card K * n1 ≤ X ^ (Fintype.card K + d1) :=
      pw_mul (pw_const hX (Fintype.card K)) hn1
    have := pw_add hX a1 a2
    calc S (g s) + 2 ≤ X + Fintype.card K * n1 := by omega
      _ ≤ X ^ (1 + (Fintype.card K + d1) + 1) := this
      _ = _ := by ring_nf
  have b1 : n2 ≤ X ^ ((Fintype.card K + d1 + 2) * d2) :=
    le_trans hn2 (pw_pow hY)
  have b2 : n1 + 1 ≤ X ^ (d1 + 0 + 1) := pw_add hX hn1 (show 1 ≤ X ^ 0 by simp)
  have := pw_add hX b2 b1
  exact le_trans this (pw_mono hX (by omega))

end PSJ
end Stk

end Sec_Ver44

section Sec_Ver45
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def isOne (x : Option Al) : Bool := decide (x = some (tk BSym.one))

def adSum (c : Bool) (p : Option Al × Option Al) : Bool := xor (xor (isOne p.1) (isOne p.2)) c
def adCar (c : Bool) (p : Option Al × Option Al) : Bool :=
  (isOne p.1 && isOne p.2) || (isOne p.1 && c) || (isOne p.2 && c)

def addAct (A X : Reg) : (Reg → Option Al) → Reg → StackAct Al := fun h r =>
  if r = A then StackAct.pop
  else if r = X then StackAct.pop
  else if r = Reg.LT then StackAct.push (tkb (adSum (h Reg.FP).isSome (h A, h X)))
  else if r = Reg.FP then
    (if (h Reg.FP).isSome then
      (if adCar (h Reg.FP).isSome (h A, h X) then StackAct.keep else StackAct.pop)
     else (if adCar false (h A, h X) then StackAct.push mk else StackAct.keep))
  else StackAct.keep

def addT (A X : Reg) : (Reg → Option Al) → Bool := fun h => (h A).isSome || (h X).isSome

def adf (acc : List Al) (c : Bool) (xs ys : List Al) : List Al × Bool :=
  (List.zipWithAll (fun x y => (x, y)) xs ys).foldl
    (fun st p => (tkb (adSum st.2 p) :: st.1, adCar st.2 p)) (acc, c)

lemma adf_step (acc : List Al) (c : Bool) (xs ys : List Al) (h : xs ≠ [] ∨ ys ≠ []) :
    adf acc c xs ys = adf (tkb (adSum c (xs.head?, ys.head?)) :: acc)
      (adCar c (xs.head?, ys.head?)) xs.tail ys.tail := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp [adf, List.zipWithAll]
  | cons x xs =>
    cases ys with
    | nil => simp [adf, List.zipWithAll]
    | cons y ys => simp [adf, List.zipWithAll]

lemma adf_nil (acc : List Al) (c : Bool) : adf acc c [] [] = (acc, c) := by simp [adf]

def AInv (s : St) : Prop := s Reg.FP = [] ∨ s Reg.FP = [mk]

def addF (A X : Reg) (s : St) : St :=
  upd (upd (upd (upd s A []) X []) Reg.LT
    (adf (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X)).1) Reg.FP
    (if (adf (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X)).2 then [mk] else [])

lemma add_step (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (s : St) (hI : AInv s) :
    StackProg.applyAct (addAct A X) s =
      upd (upd (upd (upd s A (s A).tail) X (s X).tail) Reg.LT
        (tkb (adSum (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?)) :: s Reg.LT)) Reg.FP
        (if adCar (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?) then [mk] else []) := by
  funext r
  have e0 : StackProg.applyAct (addAct A X) s r = (addAct A X (hd s) r).apply (s r) := rfl
  rw [e0]
  have hdH : (hd s Reg.FP).isSome = decide (s Reg.FP ≠ []) := by
    rcases hI with h | h <;> simp [hd, h]
  have h1 : hd s A = (s A).head? := rfl
  have h2 : hd s X = (s X).head? := rfl
  by_cases hr1 : r = A
  · subst hr1; simp [addAct, StackAct.apply, upd_apply, hAX, hAL, hAF]
  by_cases hr2 : r = X
  · subst hr2; simp [addAct, StackAct.apply, upd_apply, hAX, hXL, hXF, hr1]
  by_cases hr3 : r = Reg.LT
  · subst hr3; simp [addAct, StackAct.apply, upd_apply, hr1, hr2, hdH, h1, h2, hAL.symm, hXL.symm]
  by_cases hr4 : r = Reg.FP
  · subst hr4
    simp only [addAct, upd_apply, reduceCtorEq, ↓reduceIte, hdH, h1, h2, hr1, hr2, hr3]
    rcases hI with h | h <;> simp [h, StackAct.apply] <;> split_ifs <;> simp_all [StackAct.apply]
  · simp [addAct, StackAct.apply, upd_apply, hr1, hr2, hr3, hr4]

lemma addF_step (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (s : St) (hI : AInv s)
    (ht : addT A X (hd s) = true) :
    addF A X (StackProg.applyAct (addAct A X) s) = addF A X s := by
  rw [add_step A X hAX hAL hAF hXL hXF s hI]
  have hne : s A ≠ [] ∨ s X ≠ [] := by
    simp only [addT, hd, Bool.or_eq_true] at ht
    rcases ht with h | h
    · left; intro h'; simp [h'] at h
    · right; intro h'; simp [h'] at h
  have key := adf_step (s Reg.LT) (decide (s Reg.FP ≠ [])) (s A) (s X) hne
  unfold addF
  have hb : ∀ c : Bool, decide ((if c = true then [mk] else ([] : List Al)) ≠ []) = c := by
    intro c; cases c <;> simp
  simp only [upd_apply, reduceCtorEq, ↓reduceIte, hAL, hAF, hXL, hXF, hAL.symm, hXF.symm, hXL.symm,
    hAF.symm, hAX, hAX.symm, hb, if_true]
  rw [key]
  funext r
  simp only [upd_apply]
  split_ifs <;> simp_all

end Stk

end Sec_Ver45

section Sec_Ver46
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma gsP_addLoop (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT) (hAF : A ≠ Reg.FP)
    (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP) (hA : safe A) (hX : safe X)
    (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) :
    GsP (.loop (addT A X) (.act (addAct A X)))
      (lrun (addT A X) (StackProg.applyAct (addAct A X)) (fun s => max (s A).length (s X).length))
      (fun s => upd (addF A X s) Reg.BAD (s Reg.BAD)) (fun _ => True) AInv := by
  obtain ⟨hAC, hARC⟩ := hA
  obtain ⟨hXC, hXRC⟩ := hX
  refine GsP.loop1x (addT A X) (addAct A X) (fun s => max (s A).length (s X).length)
    (fun s => max_le (len_le_S s A) (len_le_S s X))
    (fun h => by simp [addAct, hAC, hXC, hAC.symm, hXC.symm])
    (fun h => by simp [addAct, hARC, hXRC, hARC.symm, hXRC.symm])
    (fun h => by left; simp [addAct, hAB, hXB, hAB.symm, hXB.symm]) ?_ AInv ?_ (addF A X) (fun _ => []) _ ?_ ?_ ?_ ?_
  · intro s ht
    have e1 : StackProg.applyAct (addAct A X) s A = (s A).tail := by
      show (addAct A X (hd s) A).apply (s A) = _
      simp [addAct, StackAct.apply]
    have e2 : StackProg.applyAct (addAct A X) s X = (s X).tail := by
      show (addAct A X (hd s) X).apply (s X) = _
      simp [addAct, StackAct.apply, hAX.symm]
    have hne : s A ≠ [] ∨ s X ≠ [] := by
      simp only [addT, hd, Bool.or_eq_true] at ht
      rcases ht with h | h
      · left; intro h'; simp [h'] at h
      · right; intro h'; simp [h'] at h
    show max (StackProg.applyAct (addAct A X) s A).length
      (StackProg.applyAct (addAct A X) s X).length < _
    rw [e1, e2]
    simp only [List.length_tail]
    rcases hne with h | h
    · have := List.length_pos_iff.2 h; omega
    · have := List.length_pos_iff.2 h; omega
  · intro s hI ht
    rw [add_step A X hAX hAL hAF hXL hXF s hI]
    unfold AInv
    simp only [upd_apply, reduceCtorEq, ↓reduceIte, hAF, hXF, hAF.symm, hXF.symm, hAX, hAX.symm]
    by_cases hb : adCar (decide (s Reg.FP ≠ [])) ((s A).head?, (s X).head?) = true <;> simp [hb]
  · intro s hI ht
    have hMe : s A = [] ∧ s X = [] := by
      simp only [addT, hd, Bool.or_eq_false_iff] at ht
      constructor
      · cases hs : s A with
        | nil => rfl
        | cons x l => simp [hs] at ht
      · cases hs : s X with
        | nil => rfl
        | cons x l => simp [hs] at ht
    funext r
    unfold addF
    simp only [upd_apply, hMe.1, hMe.2, adf_nil]
    have hb : (if (decide (s Reg.FP ≠ [])) = true then [mk] else []) = s Reg.FP := by
      rcases hI with h | h <;> simp [h]
    by_cases h1 : r = A
    · simp [h1, hMe.1, hAX, hAL, hAF]
    · by_cases h2 : r = X
      · simp [h2, hMe.2, hAX.symm, hXL, hXF]
      · by_cases h3 : r = Reg.LT
        · simp [h3, hAL.symm, hXL.symm]
        · by_cases h4 : r = Reg.FP
          · simp [h4, hAF.symm, hXF.symm]; simpa using hb
          · simp [h1, h2, h3, h4]
  · intro s hI ht
    exact addF_step A X hAX hAL hAF hXL hXF s hI ht
  · intro s _
    simp [addF, upd_apply, hAB.symm, hXB.symm]
  · intro s _
    simp

end Stk

end Sec_Ver46

section Sec_Ver47
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def abits : Bool → List Bool → List Bool → List Bool × Bool
  | c, [], [] => ([], c)
  | c, x :: xs, [] =>
    let r := abits ((x && false) || (x && c) || (false && c)) xs []
    (xor (xor x false) c :: r.1, r.2)
  | c, [], y :: ys =>
    let r := abits ((false && y) || (false && c) || (y && c)) [] ys
    (xor (xor false y) c :: r.1, r.2)
  | c, x :: xs, y :: ys =>
    let r := abits ((x && y) || (x && c) || (y && c)) xs ys
    (xor (xor x y) c :: r.1, r.2)

lemma isOne_tkb (b : Bool) : isOne (some (tkb b)) = b := by
  cases b <;> simp [isOne, tkb, tk]

lemma isOne_none : isOne none = false := by simp [isOne, tk]

lemma adSum_xx (c x y : Bool) : adSum c (some (tkb x), some (tkb y)) = xor (xor x y) c := by
  simp [adSum, isOne_tkb]
lemma adSum_xn (c x : Bool) : adSum c (some (tkb x), none) = xor (xor x false) c := by
  simp [adSum, isOne_tkb, isOne_none]
lemma adSum_nx (c y : Bool) : adSum c (none, some (tkb y)) = xor (xor false y) c := by
  simp [adSum, isOne_tkb, isOne_none]
lemma adCar_xx (c x y : Bool) :
    adCar c (some (tkb x), some (tkb y)) = ((x && y) || (x && c) || (y && c)) := by
  simp [adCar, isOne_tkb]
lemma adCar_xn (c x : Bool) :
    adCar c (some (tkb x), none) = ((x && false) || (x && c) || (false && c)) := by
  simp [adCar, isOne_tkb, isOne_none]
lemma adCar_nx (c y : Bool) :
    adCar c (none, some (tkb y)) = ((false && y) || (false && c) || (y && c)) := by
  simp [adCar, isOne_tkb, isOne_none]

lemma adf_bits : ∀ (c : Bool) (xs ys : List Bool) (acc : List Al),
    adf acc c (xs.map tkb) (ys.map tkb) =
      (((abits c xs ys).1.map tkb).reverse ++ acc, (abits c xs ys).2)
  | c, [], [], acc => by simp [abits, adf_nil]
  | c, x :: xs, [], acc => by
    rw [List.map_cons, List.map_nil, adf_step _ _ _ _ (Or.inl (by simp))]
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons,
      List.head?_nil, adSum_xn, adCar_xn]
    have ih := adf_bits ((x && false) || (x && c) || (false && c)) xs []
      (tkb (xor (xor x false) c) :: acc)
    simp only [List.map_nil] at ih
    rw [ih]
    simp [abits]
  | c, [], y :: ys, acc => by
    rw [List.map_cons, List.map_nil, adf_step _ _ _ _ (Or.inr (by simp))]
    simp only [List.map_cons, List.map_nil, List.tail_cons, List.tail_nil, List.head?_cons,
      List.head?_nil, adSum_nx, adCar_nx]
    have ih := adf_bits ((false && y) || (false && c) || (y && c)) [] ys
      (tkb (xor (xor false y) c) :: acc)
    simp only [List.map_nil] at ih
    rw [ih]
    simp [abits]
  | c, x :: xs, y :: ys, acc => by
    rw [List.map_cons, List.map_cons, adf_step _ _ _ _ (Or.inl (by simp))]
    simp only [List.map_cons, List.tail_cons, List.head?_cons, adSum_xx, adCar_xx]
    have ih := adf_bits ((x && y) || (x && c) || (y && c)) xs ys (tkb (xor (xor x y) c) :: acc)
    rw [ih]
    simp [abits]

lemma abits_len : ∀ (c : Bool) (xs ys : List Bool),
    ((abits c xs ys).1).length = max xs.length ys.length
  | c, [], [] => by simp [abits]
  | c, x :: xs, [] => by simp [abits, abits_len _ xs []]
  | c, [], y :: ys => by simp [abits, abits_len _ [] ys]
  | c, x :: xs, y :: ys => by simp [abits, abits_len _ xs ys]

lemma pmul2 (P k : ℕ) : P * 2 * k = 2 * (P * k) := by ring

lemma abits_val : ∀ (c : Bool) (xs ys : List Bool),
    val (abits c xs ys).1 + 2 ^ ((abits c xs ys).1).length * (abits c xs ys).2.toNat =
      val xs + val ys + c.toNat
  | c, [], [] => by simp [abits, val]
  | c, x :: xs, [] => by
    have ih := abits_val ((x && false) || (x && c) || (false && c)) xs []
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    have : val [] = 0 := rfl
    rw [this] at ih ⊢
    cases x <;> cases c <;> simp_all [Bool.toNat] <;> omega
  | c, [], y :: ys => by
    have ih := abits_val ((false && y) || (false && c) || (y && c)) [] ys
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    have : val [] = 0 := rfl
    rw [this] at ih ⊢
    cases y <;> cases c <;> simp_all [Bool.toNat] <;> omega
  | c, x :: xs, y :: ys => by
    have ih := abits_val ((x && y) || (x && c) || (y && c)) xs ys
    simp only [abits, List.length_cons, val_cons, pow_succ, pmul2] at ih ⊢
    cases x <;> cases y <;> cases c <;> simp_all [Bool.toNat] <;> omega

end Stk

end Sec_Ver47

section Sec_Ver48
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma val_append : ∀ (l1 l2 : List Bool), val (l1 ++ l2) = val l1 + 2 ^ l1.length * val l2
  | [], l2 => by simp [val]
  | b :: l1, l2 => by
    simp only [List.cons_append, val_cons, val_append l1 l2, List.length_cons, pow_succ]
    ring

def addBits (xs ys : List Bool) : List Bool :=
  (abits false xs ys).1 ++ (if (abits false xs ys).2 then [true] else [])

lemma val_addBits (xs ys : List Bool) : val (addBits xs ys) = val xs + val ys := by
  have h := abits_val false xs ys
  unfold addBits
  rw [val_append]
  cases hc : (abits false xs ys).2 <;> simp [hc, val] at h ⊢ <;> omega

def skipB : GB := GB.ofGs (Gs.total Gad.skip (fun _ => rfl))

def bAdd (A X : Reg) (hAX : A ≠ X := by decide) (hAL : A ≠ Reg.LT := by decide)
    (hAF : A ≠ Reg.FP := by decide) (hXL : X ≠ Reg.LT := by decide) (hXF : X ≠ Reg.FP := by decide)
    (hA : safe A := by decide) (hX : safe X := by decide)
    (hAB : A ≠ Reg.BAD := by decide) (hXB : X ≠ Reg.BAD := by decide) : GB :=
  (bClear Reg.LT).seq <| (bClear Reg.FP).seq <|
  (⟨_, _, _, _, _, gsP_addLoop A X hAX hAL hAF hXL hXF hA hX hAB hXB⟩ : GB).seq <|
  (GB.branch (topS Reg.FP) ((bPush Reg.LT (tkb true)).seq (bPop Reg.FP)) skipB).seq <|
  bMvA Reg.LT A hAL.symm (by decide) hA (by decide) hAB

end Stk

end Sec_Ver48

section Sec_Ver49
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma bAdd_pre (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).pre s := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply]
  simp [AInv, hd, topS]

end Stk
namespace Stk

lemma bAdd_ok (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).ok s := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply]
  simp

lemma bAdd_T (A X : Reg) (hAX : A ≠ X) (hAL : A ≠ Reg.LT)
    (hAF : A ≠ Reg.FP) (hXL : X ≠ Reg.LT) (hXF : X ≠ Reg.FP)
    (hA : safe A) (hX : safe X) (hAB : A ≠ Reg.BAD) (hXB : X ≠ Reg.BAD) (s : St)
    (bl1 bl2 : List Bool) (h1 : s A = bl1.map tkb) (h2 : s X = bl2.map tkb) :
    (bAdd A X hAX hAL hAF hXL hXF hA hX hAB hXB).T s =
      upd (upd (upd (upd s A ((addBits bl1 bl2).map tkb)) X []) Reg.LT []) Reg.FP [] := by
  simp only [bAdd, GB.seq, GB.branch, bClear, bPush, bPop, bMvA, skipB, GB.ofGs, gClear, upd_apply,
    gMvA, gPush, gPop]
  have hA1 : ∀ l : List Al, upd (upd s Reg.LT []) Reg.FP [] A = s A := by
    intro l; simp [upd_apply, hAL, hAF]
  have hX1 : upd (upd s Reg.LT []) Reg.FP [] X = s X := by simp [upd_apply, hXL, hXF]
  have hf := adf_bits false bl1 bl2 []
  funext r
  unfold addF
  simp only [hA1 [], hX1, h1, h2, hf, upd_apply, topS, hd]
  cases hc : (abits false bl1 bl2).2 <;> simp [hc, hf, addBits, hAL, hAF, hXL, hXF, hAL.symm, hAF.symm, hXL.symm, hXF.symm, hAB, hXB, hAB.symm, hXB.symm] <;>
    (by_cases e1 : r = A <;> by_cases e2 : r = X <;> by_cases e3 : r = Reg.LT <;> by_cases e4 : r = Reg.FP <;> by_cases e5 : r = Reg.BAD <;> simp_all)

end Stk

end Sec_Ver49

section Sec_Ver50
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

abbrev AddH (A X : Reg) : Prop := A ≠ X ∧ A ≠ Reg.LT ∧ A ≠ Reg.FP ∧ X ≠ Reg.LT ∧ X ≠ Reg.FP ∧
  safe A ∧ safe X ∧ A ≠ Reg.BAD ∧ X ≠ Reg.BAD

def addG (A X : Reg) (h : AddH A X := by decide) : GB :=
  bAdd A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

lemma addG_pre (A X : Reg) (h : AddH A X) (s : St) : (addG A X h).pre s :=
  bAdd_pre A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s

lemma seq_pre_all {a b : GB} (ha : ∀ s, a.pre s) (hb : ∀ s, b.pre s) : ∀ s, (a.seq b).pre s :=
  fun s => ⟨ha s, fun _ _ _ => hb _⟩

lemma branch_pre_all {a b : GB} (t : (Reg → Option Al) → Bool) (ha : ∀ s, a.pre s)
    (hb : ∀ s, b.pre s) : ∀ s, (GB.branch t a b).pre s := by
  intro s; simp only [GB.branch]; split_ifs
  · exact ha s
  · exact hb s

lemma ofGs_pre_all {p : Prog} {g T : St → St} {ok : St → Prop} (h : Gs p g T ok) :
    ∀ s, (GB.ofGs h).pre s := fun _ => trivial

lemma clear_pre (r : Reg) (hr : safe r) (hr' : r ≠ Reg.BAD) (s : St) : (bClear r hr hr').pre s := trivial
lemma bad_pre (t : (Reg → Option Al) → Bool) (s : St) : (bBad t).pre s := trivial

def cmpL (g : Bool) : GB :=
  (bClear Reg.H).seq <| (if g then bPush Reg.H mk else skipB).seq bCmp

lemma cmpL_pre (g : Bool) (s : St) : (cmpL g).pre s := by
  cases g <;> simp only [cmpL, GB.seq, bClear, bPush, skipB, GB.ofGs, bCmp, Bool.false_eq_true, if_false, if_true,
    gClear, gPush] <;> refine ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ => ?_⟩⟩ <;>
    simp [CInv, upd_apply]

end Stk

end Sec_Ver50

section Sec_Ver51
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def canonB : GB :=
  (bCopy Reg.MB Reg.LT).seq <| (bMvA Reg.LT Reg.MR).seq <| (bBad (notOneT Reg.MR)).seq <| bClear Reg.MR

def bodyG : GB :=
  (bStNum Reg.MB).seq <| canonB.seq <| (bCopy Reg.MB Reg.TM).seq <|
  (bCopy Reg.NB Reg.KB).seq <| (cmpL false).seq <| (bBad (isNoneT Reg.H)).seq <|
  (bStNum Reg.MB).seq <| canonB.seq <| (bCopy Reg.MB Reg.NC2).seq <|
  (bClear Reg.NB).seq <| (bCopy Reg.MB Reg.NB).seq <| (bCopy Reg.TM Reg.KB).seq <|
  (cmpL false).seq <| (bBad (isNoneT Reg.H)).seq <| (bClear Reg.H).seq <|
  (bBad (isNoneT Reg.T)).seq <|
  (GB.branch (topP Reg.T (isA (ty BSym.one)))
    ((addG Reg.K2 Reg.NC2).seq (addG Reg.T2 Reg.TM))
    ((addG Reg.K2 Reg.TM).seq (addG Reg.T2 Reg.NC2))).seq <|
  bPop Reg.T

lemma canonB_pre : ∀ s, canonB.pre s :=
  fun s => by simp only [canonB, GB.seq, bCopy, bMvA, bBad, bClear, GB.ofGs]; simp

lemma bodyG_pre : ∀ s, bodyG.pre s := by
  have h1 : ∀ s, (bStNum Reg.MB).pre s := fun _ => trivial
  have h2 : ∀ s, canonB.pre s := canonB_pre
  have h3 : ∀ s, (bCopy Reg.MB Reg.TM).pre s := fun _ => trivial
  have h4 : ∀ s, (bCopy Reg.NB Reg.KB).pre s := fun _ => trivial
  have h5 : ∀ s, (cmpL false).pre s := cmpL_pre false
  have h6 : ∀ s, (bBad (isNoneT Reg.H)).pre s := fun _ => trivial
  have h7 : ∀ s, (bCopy Reg.MB Reg.NC2).pre s := fun _ => trivial
  have h8 : ∀ s, (bClear Reg.NB).pre s := fun _ => trivial
  have h9 : ∀ s, (bCopy Reg.MB Reg.NB).pre s := fun _ => trivial
  have h10 : ∀ s, (bCopy Reg.TM Reg.KB).pre s := fun _ => trivial
  have h11 : ∀ s, (bClear Reg.H).pre s := fun _ => trivial
  have h12 : ∀ s, (bBad (isNoneT Reg.T)).pre s := fun _ => trivial
  have h13 : ∀ s, (bPop Reg.T).pre s := fun _ => trivial
  have h14 : ∀ s, (GB.branch (topP Reg.T (isA (ty BSym.one)))
    ((addG Reg.K2 Reg.NC2).seq (addG Reg.T2 Reg.TM))
    ((addG Reg.K2 Reg.TM).seq (addG Reg.T2 Reg.NC2))).pre s :=
    branch_pre_all _ (seq_pre_all (addG_pre _ _ _) (addG_pre _ _ _))
      (seq_pre_all (addG_pre _ _ _) (addG_pre _ _ _))
  unfold bodyG
  exact seq_pre_all h1 (seq_pre_all h2 (seq_pre_all h3 (seq_pre_all h4 (seq_pre_all h5
    (seq_pre_all h6 (seq_pre_all h1 (seq_pre_all h2 (seq_pre_all h7 (seq_pre_all h8
    (seq_pre_all h9 (seq_pre_all h10 (seq_pre_all h5 (seq_pre_all h6 (seq_pre_all h11
    (seq_pre_all h12 (seq_pre_all h14 h13))))))))))))))))

end Stk

end Sec_Ver51

section Sec_Ver52
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

structure Q where
  w : List BSym
  t : List Bool
  pv : List Bool
  s1 : List Bool
  s2 : List Bool
  mb : List Bool
  kb : List Bool
  ra : List Bool
  rb : List Bool
  hh : Bool

def QSt (q : Q) : St := fun r =>
  match r with
  | Reg.W => q.w.map tk
  | Reg.T => q.t.map tyb
  | Reg.NB => q.pv.map tkb
  | Reg.K2 => q.s1.map tkb
  | Reg.T2 => q.s2.map tkb
  | Reg.MB => q.mb.map tkb
  | Reg.KB => q.kb.map tkb
  | Reg.TM => q.ra.map tkb
  | Reg.NC2 => q.rb.map tkb
  | Reg.H => if q.hh then [mk] else []
  | _ => []

def canon (a : List Bool) : Prop := a.getLast? = some true

lemma segN_ok (q : Q) (a : List Bool) (r : List BSym) (hw : q.w = encB a ++ r) (hmb : q.mb = [])
    (hc : canon a) :
    ((bStNum Reg.MB).seq canonB).ok (QSt q) ∧
    ((bStNum Reg.MB).seq canonB).T (QSt q) = QSt { q with w := r, mb := a } := by
  have hW : QSt q Reg.W = a.map tkb ++ tk BSym.sep :: r.map tk := by
    show q.w.map tk = _
    rw [hw]; exact encB_map_tk a r
  obtain ⟨o1, c1⟩ := stNum_calc Reg.MB (QSt q) a (r.map tk) hW rfl (by decide) (by decide)
  simp only [canonB, GB.seq, bStNum, bCopy, bMvA, bBad, bClear, GB.ofGs]
  have hB3 : B3 Reg.MB (QSt q) = QSt { q with w := r, mb := a } := by
    funext r'; rw [c1]; cases r' <;> simp [QSt, hmb]
  rw [hB3]
  have hl : (a.map tkb).reverse.head? = some (tkb true) := by
    rw [← List.map_reverse, List.head?_map]
    have : a.reverse.head? = some true := by rw [List.head?_reverse]; exact hc
    rw [this]; rfl
  refine ⟨⟨o1, trivial, trivial, ?_, trivial⟩, ?_⟩
  · simp [notOneT, hd, gMvA, gCopy, upd_apply, QSt, hl, tkb, tk]
  · funext r'; cases r' <;> simp [gClear, gMvA, gCopy, upd_apply, QSt]

lemma segN_dec (q : Q) (hmb : q.mb = [])
    (h : ((bStNum Reg.MB).seq canonB).ok (QSt q)) :
    ∃ a r, q.w = encB a ++ r ∧ canon a := by
  have o1 : okNum (QSt q) := by
    simp only [canonB, GB.seq, bStNum, bCopy, bMvA, bBad, bClear, GB.ofGs] at h
    exact h.1
  obtain ⟨a, rest, e1⟩ := stNum_dec _ o1
  have e1' : q.w.map tk = a.map tkb ++ tk BSym.sep :: rest := e1
  obtain ⟨r, hw, hr⟩ := al_dec a q.w rest e1'
  refine ⟨a, r, hw, ?_⟩
  obtain ⟨o1, c1⟩ := stNum_calc Reg.MB (QSt q) a rest e1 rfl (by decide) (by decide)
  have hB3 : B3 Reg.MB (QSt q) = QSt { q with w := r, mb := a } := by
    funext r'; rw [c1]; cases r' <;> simp [QSt, hmb, hr]
  simp only [canonB, GB.seq, bStNum, bCopy, bMvA, bBad, bClear, GB.ofGs] at h
  have h4 := h.2.2.2.1
  rw [hB3] at h4
  have hh : hd (gMvA Reg.LT Reg.MR (gCopy Reg.MB Reg.LT (QSt { q with w := r, mb := a }))) Reg.MR
      = a.reverse.head?.map tkb := by
    simp [hd, gMvA, gCopy, upd_apply, QSt, List.map_reverse, List.head?_map]
  unfold notOneT at h4
  rw [hh] at h4
  unfold canon
  rw [← List.head?_reverse]
  cases hg : a.reverse.head? with
  | none => simp [hg] at h4
  | some b =>
    cases b
    · simp [hg, tkb, tk] at h4
    · rfl

end Stk

end Sec_Ver52

section Sec_Ver53
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma QSt_H (q : Q) : QSt q Reg.H = if q.hh then [mk] else [] := rfl

lemma cmpF_Q (q : Q) : cmpF (QSt q) = QSt { q with mb := [], kb := [], hh := decide (val q.kb < val q.mb ∨ (val q.mb = val q.kb ∧ q.hh = true)) } := by
  have hg : decide (QSt q Reg.H ≠ []) = q.hh := by rw [QSt_H]; cases q.hh <;> simp
  have h1 : cf (QSt q Reg.MB) (QSt q Reg.KB) (decide (QSt q Reg.H ≠ [])) =
      decide (val q.kb < val q.mb ∨ (val q.mb = val q.kb ∧ q.hh = true)) := by
    rw [hg]; exact cf_val q.mb q.kb q.hh
  unfold cmpF
  rw [h1]
  funext r
  cases r <;> simp [QSt, upd_apply]

lemma upd_H_nil (q : Q) : upd (QSt q) Reg.H [] = QSt { q with hh := false } := by
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]

lemma push_H (q : Q) : gPush Reg.H mk (QSt { q with hh := false }) = QSt { q with hh := true } := by
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply, gPush]

lemma upd_BAD_Q (q : Q) : upd (QSt q) Reg.BAD (QSt q Reg.BAD) = QSt q := by
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]

lemma upd_BAD_nil (q : Q) : upd (QSt q) Reg.BAD [] = QSt q := by
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]

lemma QSt_BAD (q : Q) : QSt q Reg.BAD = [] := rfl

lemma cmpL_Q (g : Bool) (q : Q) : (cmpL g).T (QSt q) = QSt { q with mb := [], kb := [], hh := decide (val q.kb < val q.mb ∨ (val q.mb = val q.kb ∧ g = true)) } := by
  cases g <;> simp only [cmpL, GB.seq, bClear, bPush, skipB, GB.ofGs, bCmp, gClear, upd_H_nil,
    Bool.false_eq_true, if_false, if_true, id, push_H, cmpF_Q, upd_BAD_Q]
  all_goals simp [upd_BAD_nil, QSt_BAD]

end Stk

end Sec_Ver53

section Sec_Ver54
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma gCopy_MB_TM (q : Q) : gCopy Reg.MB Reg.TM (QSt q) = QSt { q with ra := q.mb ++ q.ra } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_NB_KB (q : Q) : gCopy Reg.NB Reg.KB (QSt q) = QSt { q with kb := q.pv ++ q.kb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_MB_NC2 (q : Q) : gCopy Reg.MB Reg.NC2 (QSt q) = QSt { q with rb := q.mb ++ q.rb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_MB_NB (q : Q) : gCopy Reg.MB Reg.NB (QSt q) = QSt { q with pv := q.mb ++ q.pv } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_TM_KB (q : Q) : gCopy Reg.TM Reg.KB (QSt q) = QSt { q with kb := q.ra ++ q.kb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gClear_NB (q : Q) : gClear Reg.NB (QSt q) = QSt { q with pv := [] } := by
  funext r; cases r <;> first | rfl | simp [QSt, gClear, upd_apply]
lemma gClear_H (q : Q) : gClear Reg.H (QSt q) = QSt { q with hh := false } := upd_H_nil q

@[simp] lemma bCopy_ok (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : b ≠ Reg.BAD) (s : St) :
    (bCopy a b h1 h2 h3 h4).ok s = True := rfl
@[simp] lemma bCopy_T (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : b ≠ Reg.BAD) (s : St) :
    (bCopy a b h1 h2 h3 h4).T s = gCopy a b s := rfl
@[simp] lemma bClear_ok (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bClear a h1 h2).ok s = True := rfl
@[simp] lemma bClear_T (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bClear a h1 h2).T s = gClear a s := rfl
@[simp] lemma bPop_ok (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPop a h1 h2).ok s = True := rfl
@[simp] lemma bPop_T (a : Reg) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPop a h1 h2).T s = gPop a s := rfl
@[simp] lemma bBad_ok (t : (Reg → Option Al) → Bool) (s : St) :
    (bBad t).ok s = (t (hd s) = false) := rfl
@[simp] lemma bBad_T (t : (Reg → Option Al) → Bool) (s : St) : (bBad t).T s = s := rfl
@[simp] lemma seq_ok (a b : GB) (s : St) : (a.seq b).ok s = (a.ok s ∧ b.ok (a.T s)) := rfl
@[simp] lemma seq_T (a b : GB) (s : St) : (a.seq b).T s = b.T (a.T s) := rfl
@[simp] lemma cmpL_ok (g : Bool) (s : St) : (cmpL g).ok s = True := by
  cases g <;> simp [cmpL, bPush, skipB, GB.ofGs, bCmp]

def eoB2 : GB := (bCopy Reg.MB Reg.TM).seq <| (bCopy Reg.NB Reg.KB).seq <|
  (cmpL false).seq <| bBad (isNoneT Reg.H)

lemma eoB2_spec (q : Q) (hra : q.ra = []) (hkb : q.kb = []) :
    (eoB2.ok (QSt q) ↔ val q.pv < val q.mb) ∧
    (val q.pv < val q.mb → eoB2.T (QSt q) = QSt { q with ra := q.mb, kb := [], mb := [], hh := true }) := by
  have e3 := cmpL_Q false (({ q with ra := q.mb, kb := q.pv }) : Q)
  simp only [eoB2, seq_ok, seq_T, bCopy_ok, bCopy_T, cmpL_ok, bBad_ok, bBad_T, gCopy_MB_TM, gCopy_NB_KB, hra, hkb,
    List.append_nil, e3, true_and]
  refine ⟨?_, fun h => ?_⟩
  · simp [isNoneT, hd, QSt]
  · simp [h]

end Stk

end Sec_Ver54

section Sec_Ver55
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma addG_ok (A X : Reg) (h : AddH A X) (s : St) : (addG A X h).ok s :=
  bAdd_ok A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s

lemma addG_T (A X : Reg) (h : AddH A X) (s : St) (bl1 bl2 : List Bool) (h1 : s A = bl1.map tkb)
    (h2 : s X = bl2.map tkb) :
    (addG A X h).T s = upd (upd (upd (upd s A ((addBits bl1 bl2).map tkb)) X []) Reg.LT []) Reg.FP [] :=
  bAdd_T A X h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2 s bl1 bl2 h1 h2

lemma add_K2_NC2 (q : Q) : (addG Reg.K2 Reg.NC2).T (QSt q) =
    QSt { q with s1 := addBits q.s1 q.rb, rb := [] } := by
  rw [addG_T _ _ _ _ q.s1 q.rb rfl rfl]
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]
lemma add_T2_TM (q : Q) : (addG Reg.T2 Reg.TM).T (QSt q) =
    QSt { q with s2 := addBits q.s2 q.ra, ra := [] } := by
  rw [addG_T _ _ _ _ q.s2 q.ra rfl rfl]
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]
lemma add_K2_TM (q : Q) : (addG Reg.K2 Reg.TM).T (QSt q) =
    QSt { q with s1 := addBits q.s1 q.ra, ra := [] } := by
  rw [addG_T _ _ _ _ q.s1 q.ra rfl rfl]
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]
lemma add_T2_NC2 (q : Q) : (addG Reg.T2 Reg.NC2).T (QSt q) =
    QSt { q with s2 := addBits q.s2 q.rb, rb := [] } := by
  rw [addG_T _ _ _ _ q.s2 q.rb rfl rfl]
  funext r; cases r <;> first | rfl | simp [QSt, upd_apply]

def eoB5 : GB :=
  (bClear Reg.H).seq <| (bBad (isNoneT Reg.T)).seq <|
  (GB.branch (topP Reg.T (isA (ty BSym.one)))
    ((addG Reg.K2 Reg.NC2).seq (addG Reg.T2 Reg.TM))
    ((addG Reg.K2 Reg.TM).seq (addG Reg.T2 Reg.NC2))).seq <|
  bPop Reg.T

lemma gPop_T' (q : Q) : gPop Reg.T (QSt q) = QSt { q with t := q.t.tail } := by
  funext r; cases r <;> first | rfl | simp [QSt, gPop, upd_apply]

lemma gPop_T (q : Q) (c : Bool) (t' : List Bool) (h : q.t = c :: t') :
    gPop Reg.T (QSt q) = QSt { q with t := t' } := by
  funext r; cases r <;> first | rfl | simp [QSt, gPop, upd_apply, h]

lemma eoB5_spec (q : Q) (c : Bool) (t' : List Bool) (h : q.t = c :: t') :
    eoB5.ok (QSt q) ∧ eoB5.T (QSt q) = QSt { q with t := t', ra := [], rb := [], s1 := (if c then addBits q.s1 q.rb else addBits q.s1 q.ra), s2 := (if c then addBits q.s2 q.ra else addBits q.s2 q.rb), hh := false } := by
  have htop : ∀ q' : Q, q'.t = c :: t' → topP Reg.T (isA (ty BSym.one)) (hd (QSt q')) = c := by
    intro q' hq'
    cases c <;> simp [topP, hd, QSt, hq', isA, tyb, ty]
  have hq0 : ({ q with hh := false } : Q).t = c :: t' := h
  have ht := htop _ hq0
  cases c <;>
  · simp only [eoB5, seq_ok, seq_T, GB.branch, bClear_ok, bClear_T, gClear_H, bBad_ok, bBad_T, bPop_ok, bPop_T, ht,
      Bool.false_eq_true, if_false, if_true, addG_ok, add_K2_NC2, add_T2_TM, add_K2_TM, add_T2_NC2, gPop_T']
    refine ⟨?_, ?_⟩
    · simp [isNoneT, hd, QSt, h]
    · simp [h]

lemma eoB5_dec (q : Q) (h : eoB5.ok (QSt q)) : ∃ c t', q.t = c :: t' := by
  simp only [eoB5, seq_ok, seq_T, bClear_ok, bClear_T, gClear_H, bBad_ok, bBad_T] at h
  have h2 := h.2.1
  cases hq : q.t with
  | nil => simp [isNoneT, hd, QSt, hq] at h2
  | cons c t' => exact ⟨c, t', rfl⟩

def eoB4 : GB := (bCopy Reg.MB Reg.NC2).seq <| (bClear Reg.NB).seq <| (bCopy Reg.MB Reg.NB).seq <|
  (bCopy Reg.TM Reg.KB).seq <| (cmpL false).seq <| bBad (isNoneT Reg.H)

lemma eoB4_spec (q : Q) (hrb : q.rb = []) (hkb : q.kb = []) :
    (eoB4.ok (QSt q) ↔ val q.ra < val q.mb) ∧
    (val q.ra < val q.mb → eoB4.T (QSt q) = QSt { q with rb := q.mb, pv := q.mb, kb := [], mb := [], hh := true }) := by
  have e3 := cmpL_Q false (({ q with rb := q.mb, pv := q.mb, kb := q.ra }) : Q)
  simp only [eoB4, seq_ok, seq_T, bCopy_ok, bCopy_T, cmpL_ok, bBad_ok, bBad_T, bClear_ok, bClear_T, gCopy_MB_NC2,
    gClear_NB, gCopy_MB_NB, gCopy_TM_KB, hrb, hkb, List.append_nil, e3, true_and]
  refine ⟨?_, fun h => ?_⟩
  · simp [isNoneT, hd, QSt]
  · simp [h]

end Stk

end Sec_Ver55

section Sec_Ver56
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

structure LD where
  w : List BSym
  t : List Bool
  pv : List Bool
  s1 : List Bool
  s2 : List Bool

def LQ (d : LD) : Q := ⟨d.w, d.t, d.pv, d.s1, d.s2, [], [], [], [], false⟩
def LSt (d : LD) : St := QSt (LQ d)

def eoB1 : GB := (bStNum Reg.MB).seq canonB

lemma bodyG_ok_iff (s : St) : bodyG.ok s ↔ eoB1.ok s ∧ eoB2.ok (eoB1.T s) ∧ eoB1.ok (eoB2.T (eoB1.T s)) ∧
    eoB4.ok (eoB1.T (eoB2.T (eoB1.T s))) ∧ eoB5.ok (eoB4.T (eoB1.T (eoB2.T (eoB1.T s)))) := by
  simp only [bodyG, eoB1, eoB2, eoB4, eoB5, seq_ok, seq_T]
  simp only [and_assoc]

lemma bodyG_T_eq (s : St) : bodyG.T s = eoB5.T (eoB4.T (eoB1.T (eoB2.T (eoB1.T s)))) := by
  simp only [bodyG, eoB1, eoB2, eoB4, eoB5, seq_T]

def StepR (d d' : LD) : Prop := ∃ (a b : List Bool) (w' : List BSym) (c : Bool) (t' : List Bool),
  d.w = encB a ++ encB b ++ w' ∧ d.t = c :: t' ∧ canon a ∧ canon b ∧ val d.pv < val a ∧ val a < val b ∧
  d' = ⟨w', t', b, (if c then addBits d.s1 b else addBits d.s1 a), (if c then addBits d.s2 a else addBits d.s2 b)⟩

lemma body_step (d d' : LD) (h : StepR d d') : bodyG.ok (LSt d) ∧ bodyG.T (LSt d) = LSt d' := by
  obtain ⟨a, b, w', c, t', hw, ht, ca, cb, hpa, hab, rfl⟩ := h
  have hw' : d.w = encB a ++ (encB b ++ w') := by rw [hw]; simp
  let q1 : Q := ⟨encB b ++ w', d.t, d.pv, d.s1, d.s2, a, [], [], [], false⟩
  let q2 : Q := ⟨encB b ++ w', d.t, d.pv, d.s1, d.s2, [], [], a, [], true⟩
  let q3 : Q := ⟨w', d.t, d.pv, d.s1, d.s2, b, [], a, [], true⟩
  let q4 : Q := ⟨w', d.t, b, d.s1, d.s2, [], [], a, b, true⟩
  obtain ⟨o1, T1⟩ := segN_ok (LQ d) a (encB b ++ w') hw' rfl ca
  have T1' : eoB1.T (LSt d) = QSt q1 := T1
  obtain ⟨o2, T2⟩ := eoB2_spec q1 rfl rfl
  have T2' : eoB2.T (QSt q1) = QSt q2 := T2 hpa
  obtain ⟨o3, T3⟩ := segN_ok q2 b w' rfl rfl cb
  have T3' : eoB1.T (QSt q2) = QSt q3 := T3
  obtain ⟨o4, T4⟩ := eoB4_spec q3 rfl rfl
  have T4' : eoB4.T (QSt q3) = QSt q4 := T4 hab
  obtain ⟨o5, T5⟩ := eoB5_spec q4 c t' ht
  constructor
  · rw [bodyG_ok_iff, T1', T2', T3', T4']
    exact ⟨o1, o2.2 hpa, o3, o4.2 hab, o5⟩
  · rw [bodyG_T_eq, T1', T2', T3', T4', T5]
    cases c <;> rfl

lemma body_dec (d : LD) (h : bodyG.ok (LSt d)) : ∃ d', StepR d d' := by
  rw [bodyG_ok_iff] at h
  obtain ⟨o1, o2, o3, o4, o5⟩ := h
  obtain ⟨a, r, hw, ca⟩ := segN_dec (LQ d) rfl o1
  obtain ⟨o1', T1⟩ := segN_ok (LQ d) a r hw rfl ca
  let q1 : Q := ⟨r, d.t, d.pv, d.s1, d.s2, a, [], [], [], false⟩
  have T1' : eoB1.T (LSt d) = QSt q1 := T1
  rw [T1'] at o2 o3 o4 o5
  obtain ⟨p2, T2⟩ := eoB2_spec q1 rfl rfl
  have hpa : val d.pv < val a := p2.1 o2
  let q2 : Q := ⟨r, d.t, d.pv, d.s1, d.s2, [], [], a, [], true⟩
  have T2' : eoB2.T (QSt q1) = QSt q2 := T2 hpa
  rw [T2'] at o3 o4 o5
  obtain ⟨b, r2, hr, cb⟩ := segN_dec q2 rfl o3
  obtain ⟨o3', T3⟩ := segN_ok q2 b r2 hr rfl cb
  let q3 : Q := ⟨r2, d.t, d.pv, d.s1, d.s2, b, [], a, [], true⟩
  have T3' : eoB1.T (QSt q2) = QSt q3 := T3
  rw [T3'] at o4 o5
  obtain ⟨p4, T4⟩ := eoB4_spec q3 rfl rfl
  have hab : val a < val b := p4.1 o4
  let q4 : Q := ⟨r2, d.t, b, d.s1, d.s2, [], [], a, b, true⟩
  have T4' : eoB4.T (QSt q3) = QSt q4 := T4 hab
  rw [T4'] at o5
  obtain ⟨c, t', ht⟩ := eoB5_dec q4 o5
  exact ⟨_, a, b, r2, c, t', by have hw0 : d.w = encB a ++ r := hw; have hr0 : r = encB b ++ r2 := hr; rw [hw0, hr0]; simp, ht, ca, cb, hpa, hab, rfl⟩

end Stk

end Sec_Ver56

section Sec_Ver57
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma loop_execJ2 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)} {d : ℕ}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSI Inv p g d)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    ∀ s, Inv s → ∃ n, n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) ∧
      (StackProg.loop t p).Exec s (G s) n := by
  intro s
  induction' hm : μ s using Nat.strong_induction_on with m ih generalizing s
  intro hs
  by_cases ht : t (hd s) = true
  · obtain ⟨hlt, hG⟩ := hstep s hs ht
    obtain ⟨n1, hn1, e1⟩ := hp s hs
    have hgs := hinv s hs ht
    by_cases ht2 : t (hd (g s)) = true
    · obtain ⟨n2, hn2, e2⟩ := ih (μ (g s)) (by omega) (g s) rfl hgs
      refine ⟨1 + n1 + 1 + n2, ?_, ?_⟩
      · rw [← hm]
        have hg := hgrow s hs ht ht2
        have hY : S (g s) + μ (g s) + 2 ≤ S s + μ s + 2 := by omega
        have h1 : n1 ≤ (S s + μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h2 : n2 ≤ (μ (g s) + 1) * ((S s + μ s + 2) ^ d + 3) :=
          le_trans hn2 (Nat.mul_le_mul_left _ (by
            have := Nat.pow_le_pow_left hY d; omega))
        have h3 : μ (g s) + 1 + 1 ≤ μ s + 1 := by omega
        have h4 : (μ (g s) + 1 + 1) * ((S s + μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        nlinarith
      · rw [hG]; exact StackProg.Exec.loopTrue ht e1 e2
    · have ht2' : t (hd (g s)) = false := by simpa using ht2
      refine ⟨1 + n1 + 1 + 1, ?_, ?_⟩
      · rw [← hm]
        have h1 : n1 ≤ (S s + μ s + 2) ^ d :=
          le_trans hn1 (Nat.pow_le_pow_left (by omega) d)
        have h3 : 2 ≤ μ s + 1 := by omega
        have h4 : 2 * ((S s + μ s + 2) ^ d + 3) ≤
            (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := Nat.mul_le_mul_right _ h3
        omega
      · have e3 : (StackProg.loop t p).Exec (g s) (G (g s)) 1 := by
          rw [hstop (g s) hgs ht2']; exact StackProg.Exec.loopFalse ht2'
        rw [hG]
        exact StackProg.Exec.loopTrue ht e1 e3
  · have ht' : t (hd s) = false := by simpa using ht
    refine ⟨1, ?_, ?_⟩
    · have : 1 ≤ (S s + m + 2) ^ d + 3 := by omega
      nlinarith [Nat.zero_le m]
    · rw [hstop s hs ht']; exact StackProg.Exec.loopFalse ht'

lemma PSp.loopJ2 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨2 * d + 3, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ2 t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + μ s + 2 ≤ X ^ 2 := by nlinarith
  have a2 : (S s + μ s + 2) ^ d ≤ X ^ (2 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ (2 * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X := by omega
  calc n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := hn
    _ ≤ X * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ (2 * d + 3) := by rw [hZ]; ring

end PSJ
end Stk

end Sec_Ver57

section Sec_Ver58
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma S_QSt (q : Q) : S (QSt q) = q.w.length + q.t.length + q.pv.length + q.s1.length + q.s2.length +
    q.mb.length + q.kb.length + q.ra.length + q.rb.length + (if q.hh then 1 else 0) := by
  unfold S
  simp [Finset.univ, Fintype.elems, QSt, Finset.sum_insert]
  split_ifs <;> simp <;> omega

lemma addBits_len (xs ys : List Bool) : (addBits xs ys).length ≤ xs.length + ys.length + 1 := by
  unfold addBits
  rw [List.length_append, abits_len]
  split_ifs <;> simp <;> omega

end Stk

end Sec_Ver58

section Sec_Ver59
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def ltT : (Reg → Option Al) → Bool := fun h => (h Reg.W).isSome && (h Reg.BAD).isNone
def lmu (s : St) : ℕ := if s Reg.BAD = [] then (s Reg.W).length else 0
def JInv (s : St) : Prop := Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ d, s = LSt d)
def LG : St → St := lrun ltT bodyG.g lmu
def loopP : Prog := .loop ltT bodyG.p

lemma ltT_iff (s : St) : ltT (hd s) = true ↔ s Reg.W ≠ [] ∧ s Reg.BAD = [] := by
  unfold ltT hd
  cases h1 : s Reg.W <;> cases h2 : s Reg.BAD <;> simp

lemma Gi_LSt (d : LD) : Gi (LSt d) := ⟨rfl, rfl⟩
lemma BAD_LSt (d : LD) : LSt d Reg.BAD = [] := rfl
lemma W_LSt (d : LD) : LSt d Reg.W = d.w.map tk := rfl

lemma JInv_true (s : St) (h : JInv s) (ht : ltT (hd s) = true) : ∃ d, s = LSt d ∧ d.w ≠ [] := by
  rw [ltT_iff] at ht
  rcases h.2 with h2 | ⟨d, rfl⟩
  · exact absurd ht.2 h2
  · refine ⟨d, rfl, fun hw => ht.1 ?_⟩
    rw [W_LSt, hw]; rfl

lemma body_g (d : LD) : bodyG.g (LSt d) Reg.BAD ≠ [] ∨ ∃ d', StepR d d' ∧ bodyG.g (LSt d) = LSt d' := by
  have h := bodyG.h.2.2.2 (LSt d) (Gi_LSt d) (bodyG_pre _) (BAD_LSt d)
  by_cases hb : bodyG.g (LSt d) Reg.BAD = []
  · right
    have ho := h.1.1 hb
    obtain ⟨d', hs⟩ := body_dec d ho
    refine ⟨d', hs, ?_⟩
    rw [h.2 ho]; exact (body_step d d' hs).2
  · left; exact hb

lemma stepR_w (d d' : LD) (h : StepR d d') : ∃ a b, d.w = encB a ++ encB b ++ d'.w := by
  obtain ⟨a, b, w', c, t', hw, ht, ca, cb, hpa, hab, rfl⟩ := h
  exact ⟨a, b, hw⟩

lemma lmu_LSt (d : LD) : lmu (LSt d) = d.w.length := by
  simp [lmu, BAD_LSt, W_LSt]

lemma S_LSt (d : LD) : S (LSt d) = d.w.length + d.t.length + d.pv.length + d.s1.length + d.s2.length := by
  simp [LSt, LQ, S_QSt]

lemma loop_hdec (s : St) (h : JInv s) (ht : ltT (hd s) = true) : lmu (bodyG.g s) < lmu s := by
  obtain ⟨d, rfl, hw⟩ := JInv_true s h ht
  rw [lmu_LSt]
  rcases body_g d with hb | ⟨d', hs, he⟩
  · simp only [lmu, if_neg hb]
    have : 0 < d.w.length := List.length_pos_iff.2 hw
    simpa [lmu_LSt] using this
  · rw [he, lmu_LSt]
    obtain ⟨a, b, hw'⟩ := stepR_w d d' hs
    rw [hw']; simp [encB]; omega

lemma loop_hgrow (s : St) (h : JInv s) (ht : ltT (hd s) = true) (ht2 : ltT (hd (bodyG.g s)) = true) :
    S (bodyG.g s) + lmu (bodyG.g s) ≤ S s + lmu s := by
  obtain ⟨d, rfl, hw⟩ := JInv_true s h ht
  rcases body_g d with hb | ⟨d', hs, he⟩
  · rw [ltT_iff] at ht2; exact absurd ht2.2 hb
  · rw [he, S_LSt, S_LSt, lmu_LSt, lmu_LSt]
    obtain ⟨a, b, w', c, t', hw', ht', ca, cb, hpa, hab, rfl⟩ := hs
    have h1 := addBits_len d.s1 b
    have h2 := addBits_len d.s1 a
    have h3 := addBits_len d.s2 b
    have h4 := addBits_len d.s2 a
    simp only [hw', ht', encB, List.length_append, List.length_map, List.length_cons, List.length_nil]
    cases c <;> simp <;> omega

lemma loop_hinv (s : St) (h : JInv s) (ht : ltT (hd s) = true) : JInv (bodyG.g s) := by
  refine ⟨bodyG.h.1.2 s h.1, ?_⟩
  obtain ⟨d, rfl, hw⟩ := JInv_true s h ht
  rcases body_g d with hb | ⟨d', hs, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨d', he⟩

lemma lrun_step (s : St) (h : JInv s) (ht : ltT (hd s) = true) : LG s = LG (bodyG.g s) :=
  lrun_true JInv ltT bodyG.g lmu loop_hinv loop_hdec s h ht

lemma loop_PSp : PSp JInv loopP LG :=
  PSp.loopJ2 ltT LG lmu (PSp.weaken bodyG.h.1.1 (fun s hs => hs.1))
    (fun s => by unfold lmu; split_ifs
                 · exact len_le_S s Reg.W
                 · exact Nat.zero_le _)
    loop_hinv loop_hgrow
    (fun s _ ht => lrun_false ltT bodyG.g lmu s ht)
    (fun s hs ht => ⟨loop_hdec s hs ht, lrun_step s hs ht⟩)

end Stk

end Sec_Ver59

section Sec_Ver60
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

inductive Run : LD → LD → Prop
  | stop (d : LD) : d.w = [] → Run d d
  | step (d d' d'' : LD) : StepR d d' → Run d' d'' → Run d d''

lemma JInv_LSt (d : LD) : JInv (LSt d) := ⟨Gi_LSt d, Or.inr ⟨d, rfl⟩⟩

lemma LG_Gi (s : St) (h : JInv s) : Gi s → Gi (LG s) := by
  have := lrun_rel JInv ltT bodyG.g lmu loop_hinv loop_hdec (fun s s' => Gi s → Gi s')
    (fun s _ _ h => h) (fun s _ _ ih hg => ih (bodyG.h.1.2 s hg)) s h
  exact this

lemma LG_ltT_false (d : LD) (hw : d.w = []) : ltT (hd (LSt d)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [ltT_iff] at h
  exact h.1 (by rw [W_LSt, hw]; rfl)

lemma LG_run (d d' : LD) (h : Run d d') : LG (LSt d) = LSt d' := by
  induction h with
  | stop d hw => exact lrun_false ltT bodyG.g lmu _ (LG_ltT_false d hw)
  | step d d' d'' hs _ ih =>
    have ht : ltT (hd (LSt d)) = true := by
      rw [ltT_iff]
      obtain ⟨a, b, hw⟩ := stepR_w d d' hs
      refine ⟨?_, BAD_LSt d⟩
      rw [W_LSt, hw]; simp [encB]
    rw [lrun_step _ (JInv_LSt d) ht]
    have hb := bodyG.h.2.2.2 (LSt d) (Gi_LSt d) (bodyG_pre _) (BAD_LSt d)
    have ho := (body_step d d' hs).1
    rw [hb.2 ho, (body_step d d' hs).2]
    exact ih

lemma LG_dec (d : LD) (hb : LG (LSt d) Reg.BAD = []) : ∃ d', Run d d' ∧ LG (LSt d) = LSt d' := by
  have key := lrun_rel JInv ltT bodyG.g lmu loop_hinv loop_hdec
    (fun s s' => ∀ d, s = LSt d → s' Reg.BAD = [] → ∃ d', Run d d' ∧ s' = LSt d')
    (fun s hs ht d hd0 _ => by
      subst hd0
      refine ⟨d, Run.stop d ?_, rfl⟩
      by_contra hne
      have : ltT (hd (LSt d)) = true := by
        rw [ltT_iff]; exact ⟨by rw [W_LSt]; simpa using hne, BAD_LSt d⟩
      rw [ht] at this; exact absurd this (by simp))
    (fun s hs ht ih d hd0 hb1 => by
      subst hd0
      rcases body_g d with hb2 | ⟨d', hst, he⟩
      · exfalso
        have hf : ltT (hd (bodyG.g (LSt d))) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [ltT_iff] at h; exact hb2 h.2
        rw [lrun_false ltT bodyG.g lmu _ hf] at hb1
        exact hb2 hb1
      · rw [he] at ih hb1 ⊢
        obtain ⟨d2, hr, he2⟩ := ih d' rfl hb1
        exact ⟨d2, Run.step d d' d2 hst hr, he2⟩) (LSt d) (JInv_LSt d)
  exact key d rfl hb

end Stk

end Sec_Ver60

section Sec_Ver61
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma gCopy_K2_MB (q : Q) : gCopy Reg.K2 Reg.MB (QSt q) = QSt { q with mb := q.s1 ++ q.mb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_T2_KB (q : Q) : gCopy Reg.T2 Reg.KB (QSt q) = QSt { q with kb := q.s2 ++ q.kb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_T2_MB (q : Q) : gCopy Reg.T2 Reg.MB (QSt q) = QSt { q with mb := q.s2 ++ q.mb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]
lemma gCopy_K2_KB (q : Q) : gCopy Reg.K2 Reg.KB (QSt q) = QSt { q with kb := q.s1 ++ q.kb } := by
  funext r; cases r <;> first | rfl | simp [QSt, gCopy, upd_apply]

def eqB : GB := (bCopy Reg.K2 Reg.MB).seq <| (bCopy Reg.T2 Reg.KB).seq <| (cmpL true).seq <|
  (bBad (isNoneT Reg.H)).seq <| (bClear Reg.H).seq <| (bCopy Reg.T2 Reg.MB).seq <|
  (bCopy Reg.K2 Reg.KB).seq <| (cmpL true).seq <| bBad (isNoneT Reg.H)

lemma H_QSt_none (q : Q) : isNoneT Reg.H (hd (QSt q)) = false ↔ q.hh = true := by
  cases h : q.hh <;> simp [isNoneT, hd, QSt, h]

lemma eqB_spec (q : Q) (hmb : q.mb = []) (hkb : q.kb = []) :
    eqB.ok (QSt q) ↔ val q.s1 = val q.s2 := by
  let q1 : Q := { q with mb := q.s1, kb := q.s2 }
  have e1 := cmpL_Q true q1
  let q2 : Q := { q with mb := q.s2, kb := q.s1, hh := false }
  have e2 := cmpL_Q true q2
  have c1 : gCopy Reg.T2 Reg.KB (gCopy Reg.K2 Reg.MB (QSt q)) = QSt q1 := by
    rw [gCopy_K2_MB, gCopy_T2_KB]; simp [q1, hmb, hkb]
  have c2 : gCopy Reg.K2 Reg.KB (gCopy Reg.T2 Reg.MB (gClear Reg.H ((cmpL true).T (QSt q1)))) = QSt q2 := by
    rw [e1, gClear_H, gCopy_T2_MB, gCopy_K2_KB]; simp [q1, q2]
  simp only [eqB, seq_ok, seq_T, bCopy_ok, bCopy_T, cmpL_ok, bBad_ok, bBad_T, bClear_ok, bClear_T, true_and]
  rw [c1, c2]
  rw [e1, e2, H_QSt_none, H_QSt_none]
  simp only [q1, q2, decide_eq_true_eq, true_and]
  simp only [and_true]
  omega

def sfB : GB := (bBad (topS Reg.T)).seq <| (bBad (isNoneT Reg.NB)).seq eqB

lemma eqB_pre : ∀ s, eqB.pre s := by
  have hc : ∀ (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : b ≠ Reg.BAD) (s : St),
      (bCopy a b h1 h2 h3 h4).pre s := fun _ _ _ _ _ _ _ => trivial
  unfold eqB
  exact seq_pre_all (hc _ _ _ _ _ _) (seq_pre_all (hc _ _ _ _ _ _) (seq_pre_all (cmpL_pre true)
    (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (seq_pre_all (hc _ _ _ _ _ _)
    (seq_pre_all (hc _ _ _ _ _ _) (seq_pre_all (cmpL_pre true) (fun _ => trivial))))))))

lemma sfB_pre : ∀ s, sfB.pre s := by
  unfold sfB
  exact seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) eqB_pre)

lemma sfB_spec (d : LD) :
    sfB.ok (LSt d) ↔ d.t = [] ∧ d.pv ≠ [] ∧ val d.s1 = val d.s2 := by
  have h := eqB_spec (LQ d) rfl rfl
  simp only [sfB, seq_ok, seq_T, bBad_ok, bBad_T]
  have e1 : topS Reg.T (hd (LSt d)) = false ↔ d.t = [] := by
    cases ht : d.t <;> simp [topS, hd, LSt, LQ, QSt, ht]
  have e2 : isNoneT Reg.NB (hd (LSt d)) = false ↔ d.pv ≠ [] := by
    cases ht : d.pv <;> simp [isNoneT, hd, LSt, LQ, QSt, ht]
  rw [e1, e2]
  have h' : eqB.ok (LSt d) ↔ val d.s1 = val d.s2 := h
  rw [h']

end Stk

end Sec_Ver61

section Sec_Ver62
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def b2B : GB := (bBad (topS Reg.N)).seq (bBad (topS Reg.K))

lemma b2B_pre : ∀ s, b2B.pre s := seq_pre_all (fun _ => trivial) (fun _ => trivial)

def Inv0 (s : St) : Prop := ∃ x, s = init x
def Inv1 (s : St) : Prop := Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ w a b t, s = stateA w a b t)

lemma stateA_Gi (w : List BSym) (a b : ℕ) (t : List Bool) : Gi (stateA w a b t) := ⟨rfl, rfl⟩
lemma stateA_BAD (w : List BSym) (a b : ℕ) (t : List Bool) : stateA w a b t Reg.BAD = [] := rfl

lemma stateA_zero (w : List BSym) (t : List Bool) : stateA w 0 0 t = LSt ⟨w, t, [], [], []⟩ := by
  funext r; cases r <;> first | rfl | simp [stateA, LSt, LQ, QSt]

lemma b2B_ok (w : List BSym) (a b : ℕ) (t : List Bool) :
    b2B.ok (stateA w a b t) ↔ a = 0 ∧ b = 0 := by
  simp only [b2B, seq_ok, seq_T, bBad_ok, bBad_T]
  have e1 : topS Reg.N (hd (stateA w a b t)) = false ↔ a = 0 := by
    cases a <;> simp [topS, hd, stateA]
  have e2 : topS Reg.K (hd (stateA w a b t)) = false ↔ b = 0 := by
    cases b <;> simp [topS, hd, stateA]
  rw [e1, e2]

lemma b2B_inv (s : St) (h : Inv1 s) : JInv (b2B.g s) := by
  refine ⟨b2B.h.1.2 s h.1, ?_⟩
  rcases h.2 with hb | ⟨w, a, b, t, rfl⟩
  · exact Or.inl (b2B.h.2.1 s hb)
  · have hh := b2B.h.2.2.2 (stateA w a b t) h.1 (b2B_pre _) (stateA_BAD w a b t)
    by_cases hb : b2B.g (stateA w a b t) Reg.BAD = []
    · right
      have ho := hh.1.1 hb
      rw [b2B_ok] at ho
      obtain ⟨rfl, rfl⟩ := ho
      refine ⟨⟨w, t, [], [], []⟩, ?_⟩
      rw [hh.2 ((b2B_ok _ _ _ _).2 ⟨rfl, rfl⟩)]
      exact stateA_zero w t
    · exact Or.inl hb

lemma gA_inv1 (x : List Al) : Inv1 (gA (init x)) := by
  refine ⟨gs_stA.1.2 _ (Gi_init x), ?_⟩
  have hh := gs_stA.2.2.2 (init x) (Gi_init x) (by simp [init])
  by_cases hb : gA (init x) Reg.BAD = []
  · right
    have ho := hh.1.1 hb
    obtain ⟨w, a, b, t, hx⟩ := stA_dec x ho
    subst hx
    refine ⟨w, a, b, t, ?_⟩
    rw [hh.2 ho]; exact (stA_eval w a b t).2
  · exact Or.inl hb

def tailB : GB := sfB.seq bOut

def progE : Prog := .seq stA (.seq b2B.p (.seq loopP tailB.p))
def gE (s : St) : St := tailB.g (LG (b2B.g (gA s)))

lemma progE_PSp : PSp Inv0 progE gE := by
  have R1 : PSp JInv (.seq loopP tailB.p) (fun s => tailB.g (LG s)) :=
    PSp.seq2 (I1 := JInv) (I2 := Gi) (g := LG) (h := tailB.g) loop_PSp tailB.h.1.1 (fun s hs => LG_Gi s hs hs.1)
  have R2 : PSp Inv1 (.seq b2B.p (.seq loopP tailB.p)) (fun s => tailB.g (LG (b2B.g s))) :=
    PSp.seq2 (I1 := Inv1) (I2 := JInv) (g := b2B.g) (h := fun s => tailB.g (LG s))
      (PSp.weaken (Inv' := Inv1) b2B.h.1.1 (fun s hs => hs.1)) R1 b2B_inv
  have hA : PSp Inv0 stA gA :=
    PSp.weaken (Inv' := Inv0) gs_stA.1.1 (fun s ⟨x, hx⟩ => by subst hx; exact Gi_init x)
  have hi : ∀ s, Inv0 s → Inv1 (gA s) := by
    rintro s ⟨x, rfl⟩; exact gA_inv1 x
  have R3 := PSp.seq2 hA R2 hi
  exact R3

end Stk

end Sec_Ver62

section Sec_Ver63
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def d0 (w : List BSym) (t : List Bool) : LD := ⟨w, t, [], [], []⟩

def EV (w : List BSym) (t : List Bool) : Prop :=
  ∃ d', Run (d0 w t) d' ∧ sfB.ok (LSt d')

lemma gA_Fm (w : List BSym) (a b : ℕ) (t : List Bool) : gA (init (Fm w a b t)) = stateA w a b t := by
  obtain ⟨h1, h2⟩ := stA_eval w a b t
  have hh := gs_stA.2.2.2 (init (Fm w a b t)) (Gi_init _) (by simp [init])
  rw [hh.2 h1, h2]

lemma LG_sticky (s : St) (h : JInv s) (hb : s Reg.BAD ≠ []) : LG s Reg.BAD ≠ [] := by
  have : ltT (hd s) = false := by
    rw [Bool.eq_false_iff]; intro ht; rw [ltT_iff] at ht; exact hb ht.2
  rw [LG, lrun_false ltT bodyG.g lmu s this]; exact hb

lemma gE_OUT (s : St) : gE s Reg.OUT ≠ [] ↔
    sfB.g (LG (b2B.g (gA s))) Reg.BAD = [] := by
  have e : gE s Reg.OUT = outG (sfB.g (LG (b2B.g (gA s)))) Reg.OUT := by
    simp only [gE, tailB, GB.seq, bOut, GB.ofGs]
  rw [e, outG_OUT]
  by_cases h : sfB.g (LG (b2B.g (gA s))) Reg.BAD = [] <;> simp [h]

lemma E_BAD (x : List Al) :
    sfB.g (LG (b2B.g (gA (init x)))) Reg.BAD = [] ↔ ∃ w t, x = Fm w 0 0 t ∧ EV w t := by
  constructor
  · intro hv
    have hJ : JInv (b2B.g (gA (init x))) := b2B_inv _ (gA_inv1 x)
    have h3 : LG (b2B.g (gA (init x))) Reg.BAD = [] := by
      by_contra hc; exact sfB.h.2.1 _ hc hv
    have h2 : b2B.g (gA (init x)) Reg.BAD = [] := by
      by_contra hc; exact LG_sticky _ hJ hc h3
    have h1 : gA (init x) Reg.BAD = [] := by
      by_contra hc; exact b2B.h.2.1 _ hc h2
    have hh := gs_stA.2.2.2 (init x) (Gi_init x) (by simp [init])
    obtain ⟨w, a, b, t, hx⟩ := stA_dec x (hh.1.1 h1)
    subst hx
    rw [gA_Fm] at h2 h3 hv
    have hg := b2B.h.2.2.2 (stateA w a b t) (stateA_Gi w a b t) (b2B_pre _) (stateA_BAD w a b t)
    have hab := (b2B_ok w a b t).1 (hg.1.1 h2)
    obtain ⟨rfl, rfl⟩ := hab
    have hT : b2B.g (stateA w 0 0 t) = stateA w 0 0 t := by
      rw [hg.2 ((b2B_ok w 0 0 t).2 ⟨rfl, rfl⟩)]; rfl
    rw [hT, stateA_zero w t] at h3 hv
    change LG (LSt (d0 w t)) Reg.BAD = [] at h3
    change sfB.g (LG (LSt (d0 w t))) Reg.BAD = [] at hv
    obtain ⟨d', hr, he⟩ := LG_dec (d0 w t) h3
    rw [he] at hv
    have hs := sfB.h.2.2.2 (LSt d') (Gi_LSt d') (sfB_pre _) (BAD_LSt d')
    exact ⟨w, t, rfl, d', hr, hs.1.1 hv⟩
  · rintro ⟨w, t, rfl, d', hr, ho⟩
    rw [gA_Fm]
    have hg := b2B.h.2.2.2 (stateA w 0 0 t) (stateA_Gi w 0 0 t) (b2B_pre _) (stateA_BAD w 0 0 t)
    have hT : b2B.g (stateA w 0 0 t) = stateA w 0 0 t := by
      rw [hg.2 ((b2B_ok w 0 0 t).2 ⟨rfl, rfl⟩)]; rfl
    rw [hT, stateA_zero w t]
    show sfB.g (LG (LSt (d0 w t))) Reg.BAD = []
    rw [LG_run _ _ hr]
    have hs := sfB.h.2.2.2 (LSt d') (Gi_LSt d') (sfB_pre _) (BAD_LSt d')
    exact hs.1.2 ho

lemma E_iff (x : List Al) : gE (init x) Reg.OUT ≠ [] ↔ ∃ w t, x = Fm w 0 0 t ∧ EV w t := by
  rw [gE_OUT, E_BAD]

end Stk

end Sec_Ver63

section Sec_Ver64
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma poly_of_prog : ∃ k, ∀ x : List Al, ∃ s n, n ≤ x.length ^ k + k ∧
      progE.Exec (fun j => if j = Reg.IN then x else []) s n ∧ s = gE (init x) := by
  obtain ⟨d, hd⟩ := progE_PSp
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ d) d 0
  refine ⟨k, fun x => ?_⟩
  obtain ⟨n, hn, ex⟩ := hd (init x) ⟨x, rfl⟩
  refine ⟨gE (init x), n, ?_, ex, rfl⟩
  rw [S_init] at hn
  have h1 := hk x.length
  have h2 : (x.length + 2) ^ d ≤ 2 ^ d * (x.length + 1) ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  omega

theorem mem_P_of_prog (L : Lang Al) (hL : ∀ x, x ∈ L ↔ gE (init x) Reg.OUT ≠ []) : L ∈ P Al := by
  have hpoly : PolyTimeComputable (fun x : List Al => gE (init x) Reg.OUT) := by
    obtain ⟨k, hk⟩ := poly_of_prog
    refine stack_program_polytime progE Reg.IN Reg.OUT _ k (fun x => ?_)
    obtain ⟨s, n, hn, ex, hs⟩ := hk x
    exact ⟨s, n, hn, ex, by rw [hs]⟩
  refine mem_P_of_polyReducible L {w : List Al | w ≠ []} ⟨_, hpoly, fun x => ?_⟩ (neLang_mem_P Al)
  rw [hL]; rfl

def RelE (w : List BSym) (y : List BSym) : Prop :=
  ∃ t, y = t.map bsb ∧ EV w t

lemma checkLangE_iff (x : List Al) :
    x ∈ checkLang RelE ↔ ∃ w t, x = Fm w 0 0 t ∧ EV w t := by
  constructor
  · rintro ⟨w, y, ⟨t, hy, hok⟩, hx⟩
    refine ⟨w, t, ?_, hok⟩
    rw [hx, hy, fm_eq]; simp
  · rintro ⟨w, t, hx, hok⟩
    refine ⟨w, _, ⟨t, rfl, hok⟩, ?_⟩
    rw [hx, fm_eq]; simp

theorem checkLangE_mem_P : checkLang RelE ∈ P Al := by
  refine mem_P_of_prog _ (fun x => ?_)
  rw [E_iff, checkLangE_iff]

end Stk

end Sec_Ver64

section Sec_Ver65
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma canon_bits (n : ℕ) (hn : 0 < n) : canon (Nat.bits n) := by
  unfold canon
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have e : n = Nat.bit (n.bodd) (n.div2) := (Nat.bit_bodd_div2 n).symm
    have hd : n.div2 < n := by
      have := Nat.div2_val n; omega
    have h0 : n.div2 = 0 → n.bodd = true := by
      intro h; by_contra hb
      have : n.bodd = false := by simpa using hb
      have : n = 0 := by rw [e, h, this]; simp
      omega
    have hb := Nat.bits_append_bit n.div2 n.bodd h0
    rw [← e] at hb
    rw [hb]
    by_cases hz : n.div2 = 0
    · rw [hz]; simp [h0 hz]
    · have := ih _ hd (by omega)
      cases hl : Nat.bits n.div2 with
      | nil => rw [hl] at this; simp at this
      | cons x r => rw [hl] at this; simpa [List.getLast?_cons_cons] using this

lemma encB_inj (a a' : List Bool) (r r' : List BSym) (h : encB a ++ r = encB a' ++ r') :
    a = a' ∧ r = r' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa [encB] using h
    | cons y l => simp [encB, bsb] at h; split_ifs at h <;> simp at h
  | cons x l ih =>
    cases a' with
    | nil => simp [encB, bsb] at h; split_ifs at h <;> simp at h
    | cons y l' =>
      simp only [encB, List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hxy : x = y := by
        cases x <;> cases y <;> simp [bsb] at h1 <;> rfl
      subst hxy
      have := ih l' (by simpa [encB] using h2)
      exact ⟨by rw [this.1], this.2⟩

lemma encB_ne (a : List Bool) : encB a ++ ([] : List BSym) ≠ [] := by simp [encB]

def Chain : ℕ → List ℕ → List Bool → ℕ → ℕ → Prop
  | _, [], [], A, B => A = B
  | pv, a :: b :: x', c :: t', A, B =>
      pv < a ∧ a < b ∧ Chain b x' t' (A + if c then b else a) (B + if c then a else b)
  | _, _, _, _, _ => False

lemma Run_nil (d d' : LD) (h : Run d d') (hw : d.w = []) : d' = d := by
  cases h with
  | stop _ _ => rfl
  | step _ d1 _ hs _ =>
    obtain ⟨a, b, w', c, t', hw', -⟩ := hs
    rw [hw] at hw'
    simp [encB] at hw'

lemma canon_ne (a : List Bool) (h : canon a) : a ≠ [] := by
  rintro rfl; simp [canon] at h

lemma run_to_chain (d d' : LD) (hr : Run d d') : d'.t = [] → val d'.s1 = val d'.s2 →
    ∃ x : List ℕ, (∀ v ∈ x, 0 < v) ∧ d.w = encNats x ∧ Chain (val d.pv) x d.t (val d.s1) (val d.s2) := by
  induction hr with
  | stop d hw =>
    intro ht he
    refine ⟨[], by simp, by simp [encNats, hw], ?_⟩
    rw [ht]; simpa [Chain] using he
  | step d d1 d2 hs hr ih =>
    intro ht he
    obtain ⟨x', hx', hw', hc⟩ := ih ht he
    obtain ⟨a, b, w', c, t', hw, htt, ca, cb, hpa, hab, rfl⟩ := hs
    refine ⟨val a :: val b :: x', ?_, ?_, ?_⟩
    · intro v hv
      simp only [List.mem_cons] at hv
      rcases hv with rfl | rfl | hv
      · omega
      · omega
      · exact hx' v hv
    · simp only at hw'
      rw [hw, hw']
      simp [encNats, encNat_eq, bits_val_of_canon a (Or.inl ca), bits_val_of_canon b (Or.inl cb)]
    · rw [htt]
      simp only at hc
      refine ⟨hpa, hab, ?_⟩
      cases c <;> simpa [val_addBits] using hc

lemma chain_to_run : ∀ (t : List Bool) (x : List ℕ) (d : LD), (∀ v ∈ x, 0 < v) → d.w = encNats x →
    d.t = t → Chain (val d.pv) x t (val d.s1) (val d.s2) →
    ∃ d', Run d d' ∧ d'.t = [] ∧ val d'.s1 = val d'.s2 ∧ ((x = [] ∧ d' = d) ∨ d'.pv ≠ []) := by
  intro t
  induction t with
  | nil =>
    intro x d hx hw ht hc
    cases x with
    | nil =>
      refine ⟨d, Run.stop d (by simpa [encNats] using hw), ht, ?_, Or.inl ⟨rfl, rfl⟩⟩
      simpa [Chain] using hc
    | cons a r => cases r <;> simp [Chain] at hc
  | cons c t' ih =>
    intro x d hx hw ht hc
    cases x with
    | nil => simp [Chain] at hc
    | cons a r =>
      cases r with
      | nil => simp [Chain] at hc
      | cons b x' =>
        simp only [Chain] at hc
        obtain ⟨hpa, hab, hc'⟩ := hc
        have ha0 : 0 < a := by simpa using hx a (by simp)
        have hb0 : 0 < b := by simpa using hx b (by simp)
        have hx' : ∀ v ∈ x', 0 < v := fun v hv => hx v (by simp [hv])
        let d1 : LD := ⟨encNats x', t', Nat.bits b,
          (if c then addBits d.s1 (Nat.bits b) else addBits d.s1 (Nat.bits a)),
          (if c then addBits d.s2 (Nat.bits a) else addBits d.s2 (Nat.bits b))⟩
        have hs : StepR d d1 := by
          refine ⟨Nat.bits a, Nat.bits b, encNats x', c, t', ?_, ht.symm ▸ rfl, canon_bits a ha0,
            canon_bits b hb0, ?_, ?_, rfl⟩
          · rw [hw]; simp [encNats, encNat_eq]
          · rw [val_bits]; exact hpa
          · rw [val_bits, val_bits]; exact hab
        have h1 : Chain (val d1.pv) x' t' (val d1.s1) (val d1.s2) := by
          simp only [d1, val_bits]
          cases c <;> simpa [val_addBits, val_bits] using hc'
        obtain ⟨d2, hr, ht2, he2, hcase⟩ := ih x' d1 hx' rfl rfl h1
        refine ⟨d2, Run.step d d1 d2 hs hr, ht2, he2, Or.inr ?_⟩
        rcases hcase with ⟨hx0, rfl⟩ | h
        · exact canon_ne _ (canon_bits b hb0)
        · exact h

end Stk

end Sec_Ver65

section Sec_Ver66
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def selB (t : List Bool) (i : ℕ) : Bool := (decide (i % 2 = 1)) == (t.getD (i / 2) false)

def sumSel (t : List Bool) (x : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range x.length, if selB t i then x.getD i 0 else 0

def sumUn (t : List Bool) (x : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range x.length, if selB t i then 0 else x.getD i 0

lemma selB_shift (c : Bool) (t : List Bool) (i : ℕ) : selB (c :: t) (i + 2) = selB t i := by
  unfold selB
  have h1 : (i + 2) / 2 = i / 2 + 1 := by omega
  have h2 : (i + 2) % 2 = i % 2 := by omega
  rw [h1, h2]; simp

lemma selB_0 (c : Bool) (t : List Bool) : selB (c :: t) 0 = !c := by
  unfold selB; cases c <;> simp

lemma selB_1 (c : Bool) (t : List Bool) : selB (c :: t) 1 = c := by
  unfold selB; cases c <;> simp

lemma sumSel_cons (c : Bool) (t : List Bool) (a b : ℕ) (x : List ℕ) :
    sumSel (c :: t) (a :: b :: x) = sumSel t x + (if c then b else a) := by
  unfold sumSel
  have : (a :: b :: x).length = x.length + 2 := by simp
  rw [this, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [selB_shift, selB_0, selB_1, List.getD_cons_succ, List.getD_cons_zero, zero_add]
  cases c <;> simp [add_comm, add_left_comm]

lemma sumUn_cons (c : Bool) (t : List Bool) (a b : ℕ) (x : List ℕ) :
    sumUn (c :: t) (a :: b :: x) = sumUn t x + (if c then a else b) := by
  unfold sumUn
  have : (a :: b :: x).length = x.length + 2 := by simp
  rw [this, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [selB_shift, selB_0, selB_1, List.getD_cons_succ, List.getD_cons_zero, zero_add]
  cases c <;> simp [add_comm, add_left_comm]

lemma pw_cons3 (pv a b : ℕ) (x : List ℕ) :
    (pv :: a :: b :: x).Pairwise (· < ·) ↔ pv < a ∧ a < b ∧ (b :: x).Pairwise (· < ·) := by
  constructor
  · intro h
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.pairwise_cons] at h2
    obtain ⟨h3, h4⟩ := h2
    rw [List.pairwise_cons] at h4
    exact ⟨h1 a (by simp), h3 b (by simp), List.pairwise_cons.2 h4⟩
  · rintro ⟨h1, h2, h4⟩
    have h4' := List.pairwise_cons.1 h4
    refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, h4⟩⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact h1
      · omega
      · have := h4'.1 y hy; omega
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact h2
      · have := h4'.1 y hy; omega

lemma chain_iff : ∀ (t : List Bool) (pv : ℕ) (x : List ℕ) (A B : ℕ),
    Chain pv x t A B ↔ x.length = 2 * t.length ∧ (pv :: x).Pairwise (· < ·) ∧
      A + sumSel t x = B + sumUn t x := by
  intro t
  induction t with
  | nil =>
    intro pv x A B
    cases x with
    | nil => simp [Chain, sumUn, sumSel]
    | cons a r => cases r <;> simp [Chain]
  | cons c t ih =>
    intro pv x A B
    cases x with
    | nil => simp [Chain]
    | cons a r =>
      cases r with
      | nil => simp [Chain]; intro h; omega
      | cons b x' =>
        simp only [Chain, ih, pw_cons3, sumSel_cons, sumUn_cons, List.length_cons]
        constructor
        · rintro ⟨h1, h2, h3, h4, h5⟩
          refine ⟨by omega, ⟨h1, h2, h4⟩, ?_⟩
          cases c <;> simp only [Bool.false_eq_true, if_false, if_true] at h5 ⊢ <;> omega
        · rintro ⟨h1, ⟨h2, h3, h4⟩, h5⟩
          refine ⟨h2, h3, by omega, h4, ?_⟩
          cases c <;> simp only [Bool.false_eq_true, if_false, if_true] at h5 ⊢ <;> omega

end Stk

end Sec_Ver66

section Sec_Ver67
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC
namespace Stk

lemma fin_sum (x : List ℕ) (f : ℕ → Bool) :
    ∑ p ∈ (Finset.univ.filter (fun p : Fin x.length => f p.val = true)), x.get p =
      ∑ i ∈ Finset.range x.length, if f i then x.getD i 0 else 0 := by
  rw [Finset.sum_filter]
  have := Fin.sum_univ_eq_sum_range (fun i => if f i then x.getD i 0 else 0) x.length
  rw [← this]
  apply Finset.sum_congr rfl
  intro p _
  simp [List.getD_eq_getElem?_getD]

lemma eo_sums (x : List ℕ) (t : List Bool) :
    ∑ p ∈ (Finset.univ.filter (fun p : Fin x.length => selB t p.val = true)), x.get p = sumSel t x ∧
    ∑ p ∈ (Finset.univ.filter (fun p : Fin x.length => selB t p.val = true))ᶜ, x.get p = sumUn t x := by
  constructor
  · exact fin_sum x (selB t)
  · have e : (Finset.univ.filter (fun p : Fin x.length => selB t p.val = true))ᶜ =
        Finset.univ.filter (fun p : Fin x.length => (!selB t p.val) = true) := by
      ext p; simp
    rw [e, fin_sum x (fun i => !selB t i)]
    unfold sumUn
    apply Finset.sum_congr rfl
    intro i _
    cases selB t i <;> simp

lemma eo_of_chain (x : List ℕ) (hx : x ≠ []) (t : List Bool) (hc : Chain 0 x t 0 0) :
    EOInstance x ∧ EOYes x := by
  rw [chain_iff] at hc
  obtain ⟨hl, hp, hs⟩ := hc
  have hp' := List.pairwise_cons.1 hp
  refine ⟨⟨⟨t.length, by omega⟩, List.length_pos_of_ne_nil hx, fun v hv => hp'.1 v hv, hp'.2⟩, ?_⟩
  refine ⟨Finset.univ.filter (fun p : Fin x.length => selB t p.val = true), ?_, ?_⟩
  · intro p q hpq hdiv
    have hpq' : p.val ≠ q.val := fun h => hpq (Fin.ext h)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold selB
    have : p.val % 2 ≠ q.val % 2 := by omega
    have hd : p.val / 2 = q.val / 2 := hdiv
    rw [hd]
    cases ht : t.getD (q.val / 2) false <;> simp <;> omega
  · obtain ⟨h1, h2⟩ := eo_sums x t
    rw [h1, h2]; omega

lemma chain_of_eo (x : List ℕ) (h : EOInstance x) (hy : EOYes x) : ∃ t, Chain 0 x t 0 0 := by
  obtain ⟨⟨m, hm⟩, hlen, hpos, hpw⟩ := h
  obtain ⟨X, hX, hsum⟩ := hy
  classical
  let t : List Bool := (List.range (x.length / 2)).map (fun i =>
    if h : 2 * i + 1 < x.length then decide ((⟨2 * i + 1, h⟩ : Fin x.length) ∈ X) else false)
  have htl : t.length = x.length / 2 := by simp [t]
  have ht : ∀ i, i < x.length / 2 → t.getD i false =
      (if h : 2 * i + 1 < x.length then decide ((⟨2 * i + 1, h⟩ : Fin x.length) ∈ X) else false) := by
    intro i hi
    simp [t, List.getD_eq_getElem?_getD, hi]
  have hsel : ∀ p : Fin x.length, selB t p.val = true ↔ p ∈ X := by
    intro p
    have hp := p.isLt
    have hi : p.val / 2 < x.length / 2 := by omega
    have h2 : 2 * (p.val / 2) + 1 < x.length := by omega
    unfold selB
    rw [ht _ hi, dif_pos h2]
    by_cases hodd : p.val % 2 = 1
    · have : p = ⟨2 * (p.val / 2) + 1, h2⟩ := Fin.ext (by simp; omega)
      rw [← this]
      simp [hodd]
    · have hne : p ≠ ⟨2 * (p.val / 2) + 1, h2⟩ := fun h => by
        have := congrArg Fin.val h; simp at this; omega
      have := hX p ⟨2 * (p.val / 2) + 1, h2⟩ hne (by simp; omega)
      simp [hodd]
      tauto
  refine ⟨t, ?_⟩
  rw [chain_iff]
  refine ⟨by omega, ?_, ?_⟩
  · exact List.pairwise_cons.2 ⟨fun v hv => hpos v hv, hpw⟩
  · have e : (Finset.univ.filter (fun p : Fin x.length => selB t p.val = true)) = X := by
      ext p; simp [hsel]
    obtain ⟨h1, h2⟩ := eo_sums x t
    rw [e] at h1 h2
    rw [← h1, ← h2, hsum]

lemma eo_iff (x : List ℕ) :
    (EOInstance x ∧ EOYes x) ↔ (x ≠ [] ∧ ∃ t, Chain 0 x t 0 0) := by
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨fun hn => by have := h.2.1; simp [hn] at this, chain_of_eo x h hy⟩
  · rintro ⟨hx, t, hc⟩
    exact eo_of_chain x hx t hc

end Stk

end Sec_Ver67

section Sec_Ver68
set_option autoImplicit false
set_option linter.unusedSectionVars false
open CookPvsNP ProjSchedTW.Complexity GTWSched.NPC
namespace Stk

lemma len_encNats (x : List ℕ) : x.length ≤ (encNats x).length := by
  induction x with
  | nil => simp
  | cons a r ih =>
    simp only [encNats, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have : 1 ≤ (encNat a).length := by simp [encNat]
    omega

lemma sfB_ok_iff (d : LD) : sfB.ok (LSt d) ↔ d.t = [] ∧ d.pv ≠ [] ∧ val d.s1 = val d.s2 := sfB_spec d

theorem eo_fwd (w : List BSym) (h : w ∈ evenOddLang) : ∃ y, y.length ≤ w.length ^ 1 ∧ RelE w y := by
  obtain ⟨x, hi, hy, rfl⟩ := h
  obtain ⟨hx, t, hc⟩ := (eo_iff x).1 ⟨hi, hy⟩
  have hc' := (chain_iff t 0 x 0 0).1 hc
  have hpos := hi.2.2.1
  obtain ⟨d', hr, ht, he, hcase⟩ := chain_to_run t x (d0 (encNats x) t) hpos rfl rfl
    (by simpa [d0, val] using hc)
  have hpv : d'.pv ≠ [] := by
    rcases hcase with ⟨h1, _⟩ | h1
    · exact absurd h1 hx
    · exact h1
  refine ⟨t.map bsb, ?_, t, rfl, d', hr, (sfB_ok_iff d').2 ⟨ht, hpv, he⟩⟩
  have := len_encNats x
  simp only [List.length_map, pow_one]
  omega

theorem eo_bwd (w y : List BSym) (h : RelE w y) : w ∈ evenOddLang := by
  obtain ⟨t, -, d', hr, hok⟩ := h
  obtain ⟨ht, hpv, he⟩ := (sfB_ok_iff d').1 hok
  obtain ⟨x, hpos, hw, hc⟩ := run_to_chain (d0 w t) d' hr ht he
  have hx : x ≠ [] := by
    rintro rfl
    have hw0 : (d0 w t).w = [] := by rw [hw]; rfl
    have := Run_nil _ _ hr hw0
    rw [this] at hpv
    exact hpv rfl
  have hc0 : Chain 0 x t 0 0 := by simpa [d0, val] using hc
  obtain ⟨h1, h2⟩ := (eo_iff x).2 ⟨hx, t, hc0⟩
  exact ⟨x, h1, h2, hw⟩

end Stk


end Sec_Ver68

section Sec_Ap1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def stBlk (R X : Reg) : Prog :=
  sq (mvP R Reg.TMP isBitW) <| sq (popIf R (isA (tk BSym.sep))) <| mvA Reg.TMP X

def PB1 (R : Reg) (s : St) : St := gMvP R Reg.TMP isBitW s
def PB2 (R : Reg) (s : St) : St := gPop R (PB1 R s)
def PB3 (R X : Reg) (s : St) : St := gMvA Reg.TMP X (PB2 R s)
def okBlk (R : Reg) (s : St) : Prop := topP R (isA (tk BSym.sep)) (hd (PB1 R s)) = true

lemma gs_stBlk (R X : Reg) (hR : safe R := by decide) (hRB : R ≠ Reg.BAD := by decide)
    (hRT : R ≠ Reg.TMP := by decide) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : Gs (stBlk R X) (fun s => gMvA Reg.TMP X (gPopIf R
      (isA (tk BSym.sep)) (gMvP R Reg.TMP isBitW s))) (PB3 R X) (okBlk R) := by
  have h := Gs.seq (gs_mvP R Reg.TMP isBitW hRT hR (by decide) hRB (by decide)) <|
    Gs.seq (gs_popIf R (isA (tk BSym.sep)) hR hRB) <|
      gs_mvA Reg.TMP X hX2 (by decide) hX (by decide) hX'
  refine Gs.congr (p := stBlk R X) h (fun s _ => rfl) (fun s _ => ?_) (fun s => ?_)
  · simp [okBlk, PB1]
  · simp [PB3, PB2, PB1, gMvA, gMvP, gPop, upd_apply, hX'.symm, hRB.symm]

def bPopBlk (R X : Reg) (hR : safe R := by decide) (hRB : R ≠ Reg.BAD := by decide)
    (hRT : R ≠ Reg.TMP := by decide) (hX : safe X := by decide) (hX' : X ≠ Reg.BAD := by decide)
    (hX2 : Reg.TMP ≠ X := by decide) : GB := GB.ofGs (gs_stBlk R X hR hRB hRT hX hX' hX2)

lemma popBlk_calc (R X : Reg) (s : St) (bl : List Bool) (rest : List Al)
    (hW : s R = bl.map tkb ++ tk BSym.sep :: rest) (hT : s Reg.TMP = [])
    (hXW : X ≠ R) (hXT : X ≠ Reg.TMP) (hRT : R ≠ Reg.TMP) :
    okBlk R s ∧ ∀ r, PB3 R X s r = if r = X then bl.map tkb ++ s X else if r = R then rest
      else if r = Reg.TMP then [] else s r := by
  have hc := tw_calc bl rest
  have hB1 : PB1 R s = upd (upd s R (tk BSym.sep :: rest)) Reg.TMP (bl.map tkb).reverse := by
    unfold PB1 gMvP
    rw [hW, hc.1, hc.2]; simp [hT]
  constructor
  · unfold okBlk; rw [hB1]; simp [topP, hd, upd_apply, isA, hRT]
  · intro r
    unfold PB3 PB2 gMvA gPop
    rw [hB1]
    by_cases h1 : r = X <;> by_cases h2 : r = R <;> by_cases h3 : r = Reg.TMP <;>
      simp [upd_apply, h1, h2, h3, hXW, hXT, hXW.symm, hXT.symm, hRT, hRT.symm]

end Stk

end Sec_Ap1

section Sec_Ap2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

@[simp] lemma bPush_ok (a : Reg) (x : Al) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPush a x h1 h2).ok s = True := rfl
@[simp] lemma bPush_T (a : Reg) (x : Al) (h1 : safe a) (h2 : a ≠ Reg.BAD) (s : St) :
    (bPush a x h1 h2).T s = gPush a x s := rfl
@[simp] lemma bMvA_ok (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : a ≠ Reg.BAD)
    (h5 : b ≠ Reg.BAD) (s : St) : (bMvA a b h1 h2 h3 h4 h5).ok s = True := rfl
@[simp] lemma bMvA_T (a b : Reg) (h1 : a ≠ b) (h2 : safe a) (h3 : safe b) (h4 : a ≠ Reg.BAD)
    (h5 : b ≠ Reg.BAD) (s : St) : (bMvA a b h1 h2 h3 h4 h5).T s = gMvA a b s := rfl
@[simp] lemma skipB_ok (s : St) : skipB.ok s = True := rfl
@[simp] lemma skipB_T (s : St) : skipB.T s = s := rfl
@[simp] lemma bPopBlk_ok_def (R X : Reg) (h1 : safe R) (h2 : R ≠ Reg.BAD) (h3 : R ≠ Reg.TMP) (h4 : safe X)
    (h5 : X ≠ Reg.BAD) (h6 : Reg.TMP ≠ X) (s : St) : (bPopBlk R X h1 h2 h3 h4 h5 h6).ok s = okBlk R s := rfl
@[simp] lemma bPopBlk_T_def (R X : Reg) (h1 : safe R) (h2 : R ≠ Reg.BAD) (h3 : R ≠ Reg.TMP) (h4 : safe X)
    (h5 : X ≠ Reg.BAD) (h6 : Reg.TMP ≠ X) (s : St) : (bPopBlk R X h1 h2 h3 h4 h5 h6).T s = PB3 R X s := rfl

structure Z where
  kr : List Bool
  t : List Bool
  nm : ℕ
  nr : ℕ
  tc : List Bool
  ct : List (List Bool × List Bool)
  cd : List (List Bool × List Bool)
  a1 : List Bool
  a2 : List Bool
  one : List Bool

def encP (p : List Bool × List Bool) : List Al := p.1.map tkb ++ tk BSym.sep :: (p.2.map tkb ++ [tk BSym.sep])
def encPs (ps : List (List Bool × List Bool)) : List Al := ps.flatMap encP

@[simp] lemma encPs_nil : encPs [] = [] := rfl

lemma encPs_append (a b : List (List Bool × List Bool)) : encPs (a ++ b) = encPs a ++ encPs b := by
  simp [encPs]

def ZSt (base : St) (z : Z) : St := fun r =>
  match r with
  | Reg.KR => z.kr.map tyb
  | Reg.T => z.t.map tyb
  | Reg.N => List.replicate z.nm (ty BSym.sep)
  | Reg.NC => List.replicate z.nr (ty BSym.sep)
  | Reg.TC => z.tc.map tyb
  | Reg.TM => encPs z.ct
  | Reg.NC2 => (encPs z.cd).reverse
  | Reg.K2 => z.a1.map tkb
  | Reg.T2 => z.a2.map tkb
  | Reg.KP => z.one.map tkb
  | Reg.TMP => []
  | Reg.LT => []
  | Reg.FP => []
  | Reg.BAD => []
  | Reg.C => []
  | Reg.RC => []
  | r => base r

lemma ZSt_Gi (base : St) (z : Z) : Gi (ZSt base z) := ⟨rfl, rfl⟩
lemma ZSt_BAD (base : St) (z : Z) : ZSt base z Reg.BAD = [] := rfl

-- row-loop pieces
def dStart : GB :=
  (bBad (isNoneT Reg.T)).seq <| (bClear Reg.TC).seq <|
  (GB.branch (topP Reg.T (isA (ty BSym.one))) (bPush Reg.TC (tyb true)) (bPush Reg.TC (tyb false))).seq <|
  (bPop Reg.T).seq <| (bMvA Reg.NC2 Reg.TM).seq <| bCopy Reg.N Reg.NC

def pushPair : GB :=
  (bMvA Reg.K2 Reg.NC2).seq <| (bPush Reg.NC2 (tk BSym.sep)).seq <|
  (bMvA Reg.T2 Reg.NC2).seq <| bPush Reg.NC2 (tk BSym.sep)

def pop2B : GB := (bPopBlk Reg.TM Reg.K2).seq (bPopBlk Reg.TM Reg.T2)

def dMid : GB :=
  (GB.branch (topP Reg.KR (isA (ty BSym.one)))
    (GB.branch (topP Reg.TC (isA (ty BSym.one)))
      ((bPush Reg.KP (tkb true)).seq (addG Reg.K2 Reg.KP))
      ((bPush Reg.KP (tkb true)).seq (addG Reg.T2 Reg.KP)))
    skipB)

def dEnt : GB :=
  (bBad (isNoneT Reg.NC)).seq <| (bPop Reg.NC).seq <| pop2B.seq <| dMid.seq <|
  (bPop Reg.KR).seq pushPair

def dBody : GB := (GB.branch (topS Reg.NC) skipB dStart).seq dEnt

end Stk

end Sec_Ap2

section Sec_Ap3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section ops
variable (base : St) (z : Z)

lemma gClear_TC_Z : gClear Reg.TC (ZSt base z) = ZSt base {z with tc := []} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gClear, upd_apply]
lemma gPush_TC_Z (b : Bool) : gPush Reg.TC (tyb b) (ZSt base z) = ZSt base {z with tc := b :: z.tc} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gPush, upd_apply]
lemma gPop_T_Z : gPop Reg.T (ZSt base z) = ZSt base {z with t := z.t.tail} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gPop, upd_apply]
lemma gPop_KR_Z : gPop Reg.KR (ZSt base z) = ZSt base {z with kr := z.kr.tail} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gPop, upd_apply]
lemma gPop_NC_Z : gPop Reg.NC (ZSt base z) = ZSt base {z with nr := z.nr - 1} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gPop, upd_apply, List.tail_replicate]
lemma gMvA_cd_Z : gMvA Reg.NC2 Reg.TM (ZSt base z) = ZSt base {z with cd := [], ct := z.cd ++ z.ct} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gMvA, upd_apply, encPs_append]
lemma gCopy_N_Z : gCopy Reg.N Reg.NC (ZSt base z) = ZSt base {z with nr := z.nm + z.nr} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gCopy, upd_apply, List.replicate_append_replicate]
lemma gPush_KP_Z : gPush Reg.KP (tkb true) (ZSt base z) = ZSt base {z with one := true :: z.one} := by
  funext r; cases r <;> first | rfl | simp [ZSt, gPush, upd_apply]

lemma addK2_Z (h : z.one = [true]) : (addG Reg.K2 Reg.KP).T (ZSt base z) =
    ZSt base {z with a1 := addBits z.a1 [true], one := []} := by
  rw [addG_T _ _ _ _ z.a1 [true] rfl (by simp [ZSt, h])]
  funext r; cases r <;> first | rfl | simp [ZSt, upd_apply]
lemma addT2_Z (h : z.one = [true]) : (addG Reg.T2 Reg.KP).T (ZSt base z) =
    ZSt base {z with a2 := addBits z.a2 [true], one := []} := by
  rw [addG_T _ _ _ _ z.a2 [true] rfl (by simp [ZSt, h])]
  funext r; cases r <;> first | rfl | simp [ZSt, upd_apply]

lemma pushPair_spec : pushPair.ok (ZSt base z) ∧ pushPair.T (ZSt base z) =
    ZSt base {z with cd := z.cd ++ [(z.a1, z.a2)], a1 := [], a2 := []} := by
  refine ⟨by simp [pushPair], ?_⟩
  simp only [pushPair, seq_T, bMvA_T, bPush_T]
  funext r; cases r <;> first | rfl | simp [ZSt, gMvA, gPush, upd_apply, encPs_append, encPs, encP, List.map_reverse]

lemma pop2_spec (a b : List Bool) (ct' : List (List Bool × List Bool)) (h : z.ct = (a, b) :: ct') :
    pop2B.ok (ZSt base z) ∧
    pop2B.T (ZSt base z) =
      ZSt base {z with ct := ct', a1 := a ++ z.a1, a2 := b ++ z.a2} := by
  simp only [pop2B]
  have hW : ZSt base z Reg.TM = a.map tkb ++ tk BSym.sep :: ((b.map tkb ++ [tk BSym.sep]) ++ encPs ct') := by
    simp [ZSt, h, encPs, encP]
  obtain ⟨o1, c1⟩ := popBlk_calc Reg.TM Reg.K2 (ZSt base z) a _ hW rfl (by decide) (by decide) (by decide)
  have e1 : PB3 Reg.TM Reg.K2 (ZSt base z) = ZSt base {z with ct := (b, [])::[], a1 := a ++ z.a1} ∨ True := Or.inr trivial
  have hW2 : PB3 Reg.TM Reg.K2 (ZSt base z) Reg.TM = b.map tkb ++ tk BSym.sep :: encPs ct' := by
    rw [c1]; simp
  have hT2 : PB3 Reg.TM Reg.K2 (ZSt base z) Reg.TMP = [] := by rw [c1]; simp
  obtain ⟨o2, c2⟩ := popBlk_calc Reg.TM Reg.T2 (PB3 Reg.TM Reg.K2 (ZSt base z)) b _ hW2 hT2 (by decide) (by decide) (by decide)
  refine ⟨⟨o1, o2⟩, ?_⟩
  simp only [seq_T, bPopBlk_T_def]
  funext r
  rw [c2]
  cases r <;> simp [c1, ZSt]

end ops
end Stk

end Sec_Ap3

section Sec_Ap4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma topKR_Z (base : St) (z : Z) (bit : Bool) (kr' : List Bool) (h : z.kr = bit :: kr') :
    topP Reg.KR (isA (ty BSym.one)) (hd (ZSt base z)) = bit := by
  cases bit <;> simp [topP, hd, ZSt, h, isA, tyb, ty]
lemma topT_Z (base : St) (z : Z) (bit : Bool) (kr' : List Bool) (h : z.t = bit :: kr') :
    topP Reg.T (isA (ty BSym.one)) (hd (ZSt base z)) = bit := by
  cases bit <;> simp [topP, hd, ZSt, h, isA, tyb, ty]
lemma topTC_Z (base : St) (z : Z) : topP Reg.TC (isA (ty BSym.one)) (hd (ZSt base z)) =
    decide (z.tc.head? = some true) := by
  cases h : z.tc with
  | nil => simp [topP, hd, ZSt, h]
  | cons b l => cases b <;> simp [topP, hd, ZSt, h, isA, tyb, ty]
lemma topNC_Z (base : St) (z : Z) : topS Reg.NC (hd (ZSt base z)) = decide (z.nr ≠ 0) := by
  cases h : z.nr <;> simp [topS, hd, ZSt, h, List.replicate_succ]

def tcv (z : Z) : Bool := decide (z.tc.head? = some true)

def dNext (z : Z) (bit : Bool) (a b : List Bool) : List Bool × List Bool :=
  if bit then (if tcv z then (addBits a [true], b) else (a, addBits b [true])) else (a, b)

def dA (z : Z) (bit : Bool) : Z :=
  {z with a1 := (if bit && tcv z then addBits z.a1 [true] else z.a1),
          a2 := (if bit && !tcv z then addBits z.a2 [true] else z.a2)}

lemma dMid_spec (base : St) (z : Z) (bit : Bool) (kr' : List Bool) (hk : z.kr = bit :: kr')
    (h3 : z.one = []) : dMid.ok (ZSt base z) ∧ dMid.T (ZSt base z) = ZSt base (dA z bit) := by
  have tk1 := topKR_Z base z bit kr' hk
  have tk2 : topP Reg.TC (isA (ty BSym.one)) (hd (ZSt base z)) = tcv z := topTC_Z base z
  have hone : ({z with one := true :: z.one} : Z).one = [true] := by simp [h3]
  have a1 := addK2_Z base {z with one := true :: z.one} hone
  have a2 := addT2_Z base {z with one := true :: z.one} hone
  have ac1 := addG_ok Reg.K2 Reg.KP (by decide) (ZSt base {z with one := true :: z.one})
  have ac2 := addG_ok Reg.T2 Reg.KP (by decide) (ZSt base {z with one := true :: z.one})
  cases bit <;> cases hc : tcv z <;>
  · simp only [dMid, GB.branch, tk1, tk2, hc, seq_ok, seq_T, bPush_ok, bPush_T, gPush_KP_Z, a1, a2, ac1, ac2,
      skipB_ok, skipB_T, dA, hc, Bool.false_eq_true, if_false, if_true, true_and, Bool.false_and, Bool.and_false,
      Bool.true_and, Bool.not_true, Bool.not_false, and_self]
    try (refine ⟨trivial, ?_⟩)
    try (rw [h3])

lemma dEnt_spec (base : St) (z : Z) (r : ℕ) (bit : Bool) (kr' : List Bool) (a b : List Bool)
    (ct' : List (List Bool × List Bool)) (hn : z.nr = r + 1) (hk : z.kr = bit :: kr')
    (hc : z.ct = (a, b) :: ct') (h1 : z.a1 = []) (h2 : z.a2 = []) (h3 : z.one = []) :
    dEnt.ok (ZSt base z) ∧ dEnt.T (ZSt base z) =
      ZSt base {z with nr := r, kr := kr', ct := ct', cd := z.cd ++ [dNext z bit a b]} := by
  have hz1 : ({z with nr := r} : Z).ct = (a, b) :: ct' := hc
  obtain ⟨po, pT⟩ := pop2_spec base {z with nr := r} a b ct' hz1
  obtain ⟨mo, mT⟩ := dMid_spec base {z with nr := r, ct := ct', a1 := a ++ z.a1, a2 := b ++ z.a2} bit kr' hk h3
  have e0 : isNoneT Reg.NC (hd (ZSt base z)) = false := by
    simp [isNoneT, hd, ZSt, hn, List.replicate_succ]
  have e1 : gPop Reg.NC (ZSt base z) = ZSt base {z with nr := r} := by
    rw [gPop_NC_Z, hn]; simp
  have hpk := gPop_KR_Z base (dA {z with nr := r, ct := ct', a1 := a ++ z.a1, a2 := b ++ z.a2} bit)
  obtain ⟨qo, qT⟩ := pushPair_spec base {dA {z with nr := r, ct := ct', a1 := a ++ z.a1, a2 := b ++ z.a2} bit with kr := (dA {z with nr := r, ct := ct', a1 := a ++ z.a1, a2 := b ++ z.a2} bit).kr.tail}
  simp only [dEnt, seq_ok, seq_T, bBad_T, bPop_T, bBad_ok, e1, e0, true_and, bPop_ok, pT, mT, hpk, qT, po, mo, qo]
  cases bit <;> by_cases ht : z.tc.head? = some true <;> simp [dA, dNext, tcv, h1, h2, hk, ht]

end Stk

end Sec_Ap4

section Sec_Ap5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def clean (z : Z) : Prop := z.a1 = [] ∧ z.a2 = [] ∧ z.one = []

lemma dStart_spec (base : St) (z : Z) (t0 : Bool) (t' : List Bool) (h : z.t = t0 :: t') (hz0 : z.nr = 0) :
    dStart.ok (ZSt base z) ∧ dStart.T (ZSt base z) =
      ZSt base {z with tc := [t0], t := t', cd := [], ct := z.cd ++ z.ct, nr := z.nm} := by
  have tt := topT_Z base z t0 t' h
  have e0 : isNoneT Reg.T (hd (ZSt base z)) = false := by simp [isNoneT, hd, ZSt, h]
  have hc : gClear Reg.TC (ZSt base z) = ZSt base {z with tc := []} := gClear_TC_Z base z
  have tt2 : topP Reg.T (isA (ty BSym.one)) (hd (ZSt base {z with tc := []})) = t0 :=
    topT_Z base {z with tc := []} t0 t' h
  simp only [dStart, seq_ok, seq_T, bBad_T, bBad_ok, bClear_ok, bClear_T, hc, e0, true_and, GB.branch, tt2,
    bPop_ok, bPop_T, bMvA_ok, bMvA_T, bCopy_ok, bCopy_T]
  cases t0 <;>
  · simp only [Bool.false_eq_true, if_false, if_true, bPush_ok, bPush_T, gPush_TC_Z, true_and]
    simp only [gPop_T_Z, gMvA_cd_Z, gCopy_N_Z]
    simp [h, hz0]

lemma dStart_dec (base : St) (z : Z) (h : dStart.ok (ZSt base z)) : ∃ t0 t', z.t = t0 :: t' := by
  simp only [dStart, seq_ok, bBad_ok] at h
  cases ht : z.t with
  | nil => simp [isNoneT, hd, ZSt, ht] at h
  | cons t0 t' => exact ⟨t0, t', rfl⟩

lemma dEnt_dec (base : St) (z : Z) (bit : Bool) (kr' : List Bool) (hk : z.kr = bit :: kr')
    (hc : clean z) (h : dEnt.ok (ZSt base z)) :
    ∃ r a b ct', z.nr = r + 1 ∧ z.ct = (a, b) :: ct' := by
  obtain ⟨h1, h2, h3⟩ := hc
  simp only [dEnt, seq_ok, bBad_ok] at h
  obtain ⟨h0, -, h4, -⟩ := h
  cases hn : z.nr with
  | zero => simp [isNoneT, hd, ZSt, hn] at h0
  | succ r =>
    refine ⟨r, ?_⟩
    cases hct : z.ct with
    | nil =>
      exfalso
      have e1 : gPop Reg.NC (ZSt base z) = ZSt base {z with nr := r} := by rw [gPop_NC_Z, hn]; simp
      simp only [bBad_T, bPop_T, e1, pop2B, seq_ok, bPopBlk_ok_def] at h4
      have := h4.1
      simp [okBlk, PB1, gMvP, hd, topP, ZSt, hct] at this
    | cons p ct' => exact ⟨p.1, p.2, ct', rfl, rfl⟩

def StartR (z z1 : Z) : Prop := (z.nr ≠ 0 ∧ z1 = z) ∨ (z.nr = 0 ∧ ∃ t0 t', z.t = t0 :: t' ∧
  z1 = {z with tc := [t0], t := t', cd := [], ct := z.cd ++ z.ct, nr := z.nm})

def EntR (z1 z' : Z) : Prop := ∃ (r : ℕ) (bit : Bool) (kr' a b : List Bool) (ct' : List (List Bool × List Bool)),
  z1.nr = r + 1 ∧ z1.kr = bit :: kr' ∧ z1.ct = (a, b) :: ct' ∧
  z' = {z1 with nr := r, kr := kr', ct := ct', cd := z1.cd ++ [dNext z1 bit a b]}

def StepD (z z' : Z) : Prop := ∃ z1, StartR z z1 ∧ EntR z1 z'

lemma clean_start (z z1 : Z) (h : StartR z z1) (hc : clean z) : clean z1 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩ <;> exact hc

lemma clean_ent (z1 z' : Z) (h : EntR z1 z') (hc : clean z1) : clean z' := by
  obtain ⟨r, bit, kr', a, b, ct', -, -, -, rfl⟩ := h; exact hc

lemma dBody_step (base : St) (z z' : Z) (hc : clean z) (h : StepD z z') :
    dBody.ok (ZSt base z) ∧ dBody.T (ZSt base z) = ZSt base z' := by
  obtain ⟨z1, hs, he⟩ := h
  have hc1 := clean_start z z1 hs hc
  obtain ⟨r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩ := he
  obtain ⟨eo, eT⟩ := dEnt_spec base z1 r bit kr' a b ct' hn hk hct hc1.1 hc1.2.1 hc1.2.2
  have tn := topNC_Z base z
  rcases hs with ⟨hnz, rfl⟩ | ⟨hz0, t0, t', ht, rfl⟩
  · simp only [dBody, seq_ok, seq_T, GB.branch, tn, hnz, decide_true, if_true, ne_eq, not_false_eq_true,
      skipB_ok, skipB_T, true_and]
    exact ⟨eo, eT⟩
  · obtain ⟨so, sT⟩ := dStart_spec base z t0 t' ht hz0
    simp only [dBody, seq_ok, seq_T, GB.branch, tn, hz0, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, if_false, so, sT, true_and]
    exact ⟨eo, eT⟩

lemma dBody_dec (base : St) (z : Z) (bit : Bool) (kr' : List Bool) (hk : z.kr = bit :: kr') (hc : clean z)
    (h : dBody.ok (ZSt base z)) : ∃ z', StepD z z' := by
  have tn := topNC_Z base z
  simp only [dBody, seq_ok, seq_T, GB.branch, tn] at h
  by_cases hnz : z.nr ≠ 0
  · have hd1 : decide (z.nr ≠ 0) = true := decide_eq_true hnz
    simp only [hd1, if_true, skipB_ok, skipB_T, true_and] at h
    obtain ⟨r, a, b, ct', hn, hct⟩ := dEnt_dec base z bit kr' hk hc h
    exact ⟨_, z, Or.inl ⟨hnz, rfl⟩, r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩
  · have hz0 : z.nr = 0 := by simpa using hnz
    have hd1 : decide (z.nr ≠ 0) = false := decide_eq_false hnz
    simp only [hd1, Bool.false_eq_true, if_false] at h
    obtain ⟨so, h2⟩ := h
    obtain ⟨t0, t', ht⟩ := dStart_dec base z so
    obtain ⟨-, sT⟩ := dStart_spec base z t0 t' ht hz0
    rw [sT] at h2
    have hc1 : clean ({z with tc := [t0], t := t', cd := [], ct := z.cd ++ z.ct, nr := z.nm} : Z) := hc
    obtain ⟨r, a, b, ct', hn, hct⟩ := dEnt_dec base ({z with tc := [t0], t := t', cd := [], ct := z.cd ++ z.ct, nr := z.nm} : Z) bit kr' hk hc1 h2
    exact ⟨_, _, Or.inr ⟨hz0, t0, t', ht, rfl⟩, r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩

end Stk

end Sec_Ap5

section Sec_Ap6
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma bPopBlk_pre_all (R X : Reg) (h1 : safe R) (h2 : R ≠ Reg.BAD) (h3 : R ≠ Reg.TMP) (h4 : safe X)
    (h5 : X ≠ Reg.BAD) (h6 : Reg.TMP ≠ X) : ∀ s, (bPopBlk R X h1 h2 h3 h4 h5 h6).pre s := fun _ => trivial

lemma dBody_pre : ∀ s, dBody.pre s := by
  have hp : ∀ s, (bPush Reg.KP (tkb true)).pre s := fun _ => trivial
  have hm : ∀ s, dMid.pre s := by
    intro s
    unfold dMid
    exact branch_pre_all _ (branch_pre_all _ (seq_pre_all hp (addG_pre _ _ _))
      (seq_pre_all hp (addG_pre _ _ _))) (fun _ => trivial) s
  have hpair : ∀ s, pushPair.pre s := fun _ => seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
    (seq_pre_all (fun _ => trivial) (fun _ => trivial))) _
  have he : ∀ s, dEnt.pre s := by
    unfold dEnt pop2B
    exact seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
      (seq_pre_all (seq_pre_all (fun _ => trivial) (fun _ => trivial))
        (seq_pre_all hm (seq_pre_all (fun _ => trivial) hpair))))
  have hs : ∀ s, dStart.pre s := by
    unfold dStart
    exact seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
      (seq_pre_all (branch_pre_all _ (fun _ => trivial) (fun _ => trivial))
        (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (fun _ => trivial)))))
  unfold dBody
  exact seq_pre_all (branch_pre_all _ (fun _ => trivial) hs) he

def Bc (base : St) : ℕ := (base Reg.IN).length + (base Reg.WR).length + (base Reg.W).length +
  (base Reg.K).length + (base Reg.TR).length + (base Reg.MB).length + (base Reg.NB).length +
  (base Reg.KB).length + (base Reg.U).length + (base Reg.F).length + (base Reg.HU).length +
  (base Reg.OUT).length + (base Reg.PP).length + (base Reg.TT).length + (base Reg.H).length +
  (base Reg.MR).length

def szP (ps : List (List Bool × List Bool)) : ℕ := (ps.map fun p => p.1.length + p.2.length + 2).sum

lemma encPs_len (ps : List (List Bool × List Bool)) : (encPs ps).length = szP ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [encPs, encP, szP] at ih ⊢; omega

lemma szP_append (a b : List (List Bool × List Bool)) : szP (a ++ b) = szP a + szP b := by
  simp [szP]

@[simp] lemma ZR_IN (base : St) (z : Z) : ZSt base z Reg.IN = base Reg.IN := rfl
@[simp] lemma ZR_WR (base : St) (z : Z) : ZSt base z Reg.WR = base Reg.WR := rfl
@[simp] lemma ZR_W (base : St) (z : Z) : ZSt base z Reg.W = base Reg.W := rfl
@[simp] lemma ZR_N (base : St) (z : Z) : ZSt base z Reg.N = List.replicate z.nm (ty BSym.sep) := rfl
@[simp] lemma ZR_K (base : St) (z : Z) : ZSt base z Reg.K = base Reg.K := rfl
@[simp] lemma ZR_TR (base : St) (z : Z) : ZSt base z Reg.TR = base Reg.TR := rfl
@[simp] lemma ZR_T (base : St) (z : Z) : ZSt base z Reg.T = z.t.map tyb := rfl
@[simp] lemma ZR_TMP (base : St) (z : Z) : ZSt base z Reg.TMP = [] := rfl
@[simp] lemma ZR_MB (base : St) (z : Z) : ZSt base z Reg.MB = base Reg.MB := rfl
@[simp] lemma ZR_NB (base : St) (z : Z) : ZSt base z Reg.NB = base Reg.NB := rfl
@[simp] lemma ZR_KB (base : St) (z : Z) : ZSt base z Reg.KB = base Reg.KB := rfl
@[simp] lemma ZR_U (base : St) (z : Z) : ZSt base z Reg.U = base Reg.U := rfl
@[simp] lemma ZR_F (base : St) (z : Z) : ZSt base z Reg.F = base Reg.F := rfl
@[simp] lemma ZR_HU (base : St) (z : Z) : ZSt base z Reg.HU = base Reg.HU := rfl
@[simp] lemma ZR_C (base : St) (z : Z) : ZSt base z Reg.C = [] := rfl
@[simp] lemma ZR_RC (base : St) (z : Z) : ZSt base z Reg.RC = [] := rfl
@[simp] lemma ZR_BAD (base : St) (z : Z) : ZSt base z Reg.BAD = [] := rfl
@[simp] lemma ZR_OUT (base : St) (z : Z) : ZSt base z Reg.OUT = base Reg.OUT := rfl
@[simp] lemma ZR_KP (base : St) (z : Z) : ZSt base z Reg.KP = z.one.map tkb := rfl
@[simp] lemma ZR_NC (base : St) (z : Z) : ZSt base z Reg.NC = List.replicate z.nr (ty BSym.sep) := rfl
@[simp] lemma ZR_PP (base : St) (z : Z) : ZSt base z Reg.PP = base Reg.PP := rfl
@[simp] lemma ZR_TC (base : St) (z : Z) : ZSt base z Reg.TC = z.tc.map tyb := rfl
@[simp] lemma ZR_T2 (base : St) (z : Z) : ZSt base z Reg.T2 = z.a2.map tkb := rfl
@[simp] lemma ZR_K2 (base : St) (z : Z) : ZSt base z Reg.K2 = z.a1.map tkb := rfl
@[simp] lemma ZR_TM (base : St) (z : Z) : ZSt base z Reg.TM = encPs z.ct := rfl
@[simp] lemma ZR_NC2 (base : St) (z : Z) : ZSt base z Reg.NC2 = (encPs z.cd).reverse := rfl
@[simp] lemma ZR_TT (base : St) (z : Z) : ZSt base z Reg.TT = base Reg.TT := rfl
@[simp] lemma ZR_FP (base : St) (z : Z) : ZSt base z Reg.FP = [] := rfl
@[simp] lemma ZR_H (base : St) (z : Z) : ZSt base z Reg.H = base Reg.H := rfl
@[simp] lemma ZR_MR (base : St) (z : Z) : ZSt base z Reg.MR = base Reg.MR := rfl
@[simp] lemma ZR_KR (base : St) (z : Z) : ZSt base z Reg.KR = z.kr.map tyb := rfl
@[simp] lemma ZR_LT (base : St) (z : Z) : ZSt base z Reg.LT = [] := rfl

lemma S_ZSt (base : St) (z : Z) : S (ZSt base z) = Bc base + z.kr.length + z.t.length + z.nm + z.nr +
    z.tc.length + szP z.ct + szP z.cd + z.a1.length + z.a2.length + z.one.length := by
  have e : (encPs z.cd).reverse.length = szP z.cd := by rw [List.length_reverse, encPs_len]
  have e2 : (encPs z.ct).length = szP z.ct := encPs_len _
  unfold S
  simp only [Finset.univ, Fintype.elems]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [ZR_IN, ZR_WR, ZR_W, ZR_N, ZR_K, ZR_TR, ZR_T, ZR_TMP, ZR_MB, ZR_NB, ZR_KB, ZR_U, ZR_F, ZR_HU,
    ZR_C, ZR_RC, ZR_BAD, ZR_OUT, ZR_KP, ZR_NC, ZR_PP, ZR_TC, ZR_T2, ZR_K2, ZR_TM, ZR_NC2, ZR_TT, ZR_FP,
    ZR_H, ZR_MR, ZR_KR, ZR_LT, List.length_map, List.length_replicate, List.length_nil, e, e2, Bc]
  ac_rfl

end Stk

end Sec_Ap6

section Sec_Ap7
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def ZInv (z : Z) : Prop := clean z ∧ z.nr ≤ z.nm

def muD (s : St) : ℕ := if s Reg.BAD = [] then 2 * (s Reg.KR).length + ((s Reg.N).length - (s Reg.NC).length) else 0

lemma muD_ZSt (base : St) (z : Z) : muD (ZSt base z) = 2 * z.kr.length + (z.nm - z.nr) := by
  simp [muD]

lemma ZInv_start (z z1 : Z) (h : StartR z z1) (hI : ZInv z) : ZInv z1 := by
  rcases h with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩
  · exact hI
  · exact ⟨hI.1, le_refl _⟩

lemma ZInv_ent (z1 z' : Z) (h : EntR z1 z') (hI : ZInv z1) : ZInv z' := by
  obtain ⟨r, bit, kr', a, b, ct', hn, -, -, rfl⟩ := h
  exact ⟨hI.1, by have := hI.2; simp only [hn] at this ⊢; omega⟩

lemma addBits_one_len (a : List Bool) : (addBits a [true]).length ≤ a.length + 1 := by
  cases a with
  | nil => simp [addBits, abits]
  | cons x xs =>
    have := abits_len false (x :: xs) [true]
    unfold addBits
    rw [List.length_append]
    simp only [List.length_cons, List.length_nil] at this ⊢
    split_ifs <;> simp <;> omega

lemma dNext_len (z : Z) (bit : Bool) (a b : List Bool) :
    szP [dNext z bit a b] ≤ szP [(a, b)] + 1 := by
  have h1 := addBits_one_len a
  have h2 := addBits_one_len b
  unfold dNext
  cases bit <;> by_cases ht : tcv z = true <;> simp [szP, ht] <;> omega

lemma szP_cons (p : List Bool × List Bool) (ps : List (List Bool × List Bool)) :
    szP (p :: ps) = p.1.length + p.2.length + 2 + szP ps := by simp [szP]

lemma ent_num (base : St) (z1 z' : Z) (hI1 : ZInv z1) (he : EntR z1 z') :
    S (ZSt base z') + 1 ≤ S (ZSt base z1) ∧ muD (ZSt base z') + 1 = muD (ZSt base z1) := by
  obtain ⟨c1, c2, c3⟩ := hI1.1
  obtain ⟨r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩ := he
  have dl := dNext_len z1 bit a b
  have e1 : szP z1.ct = a.length + b.length + 2 + szP ct' := by rw [hct, szP_cons]
  have e2 : szP [dNext z1 bit a b] ≤ a.length + b.length + 2 + 1 := by
    have := szP_cons (a, b) []
    simp only [szP_cons, szP] at dl this ⊢
    simp at dl this ⊢
    omega
  have hle := hI1.2
  rw [S_ZSt, S_ZSt, muD_ZSt, muD_ZSt]
  simp only [szP_append, c1, c2, c3, List.length_nil, hk, hn, List.length_cons] at hle ⊢
  constructor <;> omega

@[simp] lemma szP_nil : szP [] = 0 := rfl

lemma start_num (base : St) (z z1 : Z) (hI : ZInv z) (hs : StartR z z1) :
    S (ZSt base z1) ≤ S (ZSt base z) + z.nm ∧ muD (ZSt base z1) + z.nm ≤ muD (ZSt base z) + z.nm ∧
      (S (ZSt base z1) + muD (ZSt base z1) ≤ S (ZSt base z) + muD (ZSt base z)) ∧
      muD (ZSt base z1) ≤ muD (ZSt base z) := by
  rcases hs with ⟨-, rfl⟩ | ⟨hz0, t0, t', ht, rfl⟩
  · simp
  · rw [S_ZSt, S_ZSt, muD_ZSt, muD_ZSt]
    simp only [szP_append, szP_nil, ht, List.length_cons, List.length_nil, hz0]
    have : szP z.cd + szP z.ct = szP z.ct + szP z.cd := Nat.add_comm _ _
    omega

lemma step_num (base : St) (z z' : Z) (hI : ZInv z) (h : StepD z z') :
    ZInv z' ∧ S (ZSt base z') + muD (ZSt base z') ≤ S (ZSt base z) + muD (ZSt base z) ∧
      muD (ZSt base z') < muD (ZSt base z) := by
  obtain ⟨z1, hs, he⟩ := h
  have hI1 := ZInv_start z z1 hs hI
  obtain ⟨n1, n2⟩ := ent_num base z1 z' hI1 he
  obtain ⟨s1, -, s3, s4⟩ := start_num base z z1 hI hs
  exact ⟨ZInv_ent z1 z' he hI1, by omega, by omega⟩

end Stk

end Sec_Ap7

section Sec_Ap8
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk
section PSJ3
variable {K A : Type} [Fintype K] [DecidableEq K]

lemma PSp.loopJ3 {Inv : (K → List A) → Prop} {p : StackProg K A}
    {g : (K → List A) → (K → List A)}
    (t : (K → Option A) → Bool) (G : (K → List A) → (K → List A)) (μ : (K → List A) → ℕ)
    (hp : PSp Inv p g) (hμ : ∀ s, μ s ≤ 3 * S s)
    (hinv : ∀ s, Inv s → t (hd s) = true → Inv (g s))
    (hgrow : ∀ s, Inv s → t (hd s) = true → t (hd (g s)) = true → S (g s) + μ (g s) ≤ S s + μ s)
    (hstop : ∀ s, Inv s → t (hd s) = false → G s = s)
    (hstep : ∀ s, Inv s → t (hd s) = true → μ (g s) < μ s ∧ G s = G (g s)) :
    PSp Inv (.loop t p) G := by
  obtain ⟨d, hp⟩ := hp
  refine ⟨2 * d + 4, fun s hs => ?_⟩
  obtain ⟨n, hn, e⟩ := loop_execJ2 t G μ hp hinv hgrow hstop hstep s hs
  refine ⟨n, ?_, e⟩
  set X := S s + 2 with hX
  have hX2 : 2 ≤ X := by omega
  have hm := hμ s
  have a1 : S s + μ s + 2 ≤ X ^ 2 := by nlinarith
  have a2 : (S s + μ s + 2) ^ d ≤ X ^ (2 * d) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left a1 d
  set Z := X ^ (2 * d) with hZ
  have hZ1 : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have a3 : (S s + μ s + 2) ^ d + 3 ≤ X ^ 2 * Z := by
    have : 4 ≤ X ^ 2 := by nlinarith
    nlinarith
  have a4 : μ s + 1 ≤ X ^ 2 := by nlinarith
  calc n ≤ (μ s + 1) * ((S s + μ s + 2) ^ d + 3) := hn
    _ ≤ X ^ 2 * (X ^ 2 * Z) := Nat.mul_le_mul a4 a3
    _ = X ^ (2 * d + 4) := by rw [hZ]; ring

end PSJ3

def ltK : (Reg → Option Al) → Bool := fun h => (h Reg.KR).isSome && (h Reg.BAD).isNone

def JD (base : St) (s : St) : Prop := Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ z, ZInv z ∧ s = ZSt base z)

def LGD : St → St := lrun ltK dBody.g muD
def loopD : Prog := .loop ltK dBody.p

lemma ltK_iff (s : St) : ltK (hd s) = true ↔ s Reg.KR ≠ [] ∧ s Reg.BAD = [] := by
  unfold ltK hd
  cases h1 : s Reg.KR <;> cases h2 : s Reg.BAD <;> simp

lemma JD_true (base : St) (s : St) (h : JD base s) (ht : ltK (hd s) = true) :
    ∃ z, ZInv z ∧ s = ZSt base z ∧ z.kr ≠ [] := by
  rw [ltK_iff] at ht
  rcases h.2 with h2 | ⟨z, hz, rfl⟩
  · exact absurd ht.2 h2
  · refine ⟨z, hz, rfl, fun hw => ht.1 ?_⟩
    simp [hw]

lemma bodyD_g (base : St) (z : Z) (hz : ZInv z) (hk : z.kr ≠ []) :
    dBody.g (ZSt base z) Reg.BAD ≠ [] ∨ ∃ z', StepD z z' ∧ dBody.g (ZSt base z) = ZSt base z' := by
  have h := dBody.h.2.2.2 (ZSt base z) (ZSt_Gi base z) (dBody_pre _) (ZSt_BAD base z)
  by_cases hb : dBody.g (ZSt base z) Reg.BAD = []
  · right
    have ho := h.1.1 hb
    obtain ⟨bit, kr', hkr⟩ := List.exists_cons_of_ne_nil hk
    obtain ⟨z', hs⟩ := dBody_dec base z bit kr' hkr hz.1 ho
    refine ⟨z', hs, ?_⟩
    rw [h.2 ho]; exact (dBody_step base z z' hz.1 hs).2
  · left; exact hb

lemma loopD_hinv (base : St) (s : St) (h : JD base s) (ht : ltK (hd s) = true) : JD base (dBody.g s) := by
  refine ⟨dBody.h.1.2 s h.1, ?_⟩
  obtain ⟨z, hz, rfl, hk⟩ := JD_true base s h ht
  rcases bodyD_g base z hz hk with hb | ⟨z', hs, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨z', (step_num base z z' hz hs).1, he⟩

lemma loopD_hdec (base : St) (s : St) (h : JD base s) (ht : ltK (hd s) = true) : muD (dBody.g s) < muD s := by
  obtain ⟨z, hz, rfl, hk⟩ := JD_true base s h ht
  rw [muD_ZSt]
  rcases bodyD_g base z hz hk with hb | ⟨z', hs, he⟩
  · simp only [muD, if_neg hb]
    obtain ⟨bit, kr', hkr⟩ := List.exists_cons_of_ne_nil hk
    simp [hkr]
  · rw [he, muD_ZSt]; have := (step_num base z z' hz hs).2.2; rw [muD_ZSt, muD_ZSt] at this; exact this

lemma loopD_hgrow (base : St) (s : St) (h : JD base s) (ht : ltK (hd s) = true)
    (ht2 : ltK (hd (dBody.g s)) = true) : S (dBody.g s) + muD (dBody.g s) ≤ S s + muD s := by
  obtain ⟨z, hz, rfl, hk⟩ := JD_true base s h ht
  rcases bodyD_g base z hz hk with hb | ⟨z', hs, he⟩
  · rw [ltK_iff] at ht2; exact absurd ht2.2 hb
  · rw [he]; exact (step_num base z z' hz hs).2.1

lemma lrunD_step (base : St) (s : St) (h : JD base s) (ht : ltK (hd s) = true) : LGD s = LGD (dBody.g s) :=
  lrun_true (JD base) ltK dBody.g muD (loopD_hinv base) (loopD_hdec base) s h ht

lemma muD_le (s : St) : muD s ≤ 3 * S s := by
  unfold muD; split_ifs
  · have h1 := len_le_S s Reg.KR
    have h2 := len_le_S s Reg.N
    have : (s Reg.N).length - (s Reg.NC).length ≤ (s Reg.N).length := Nat.sub_le _ _
    omega
  · exact Nat.zero_le _

lemma loopD_PSp (base : St) : PSp (JD base) loopD LGD :=
  PSp.loopJ3 ltK LGD muD (PSp.weaken dBody.h.1.1 (fun s hs => hs.1)) muD_le
    (loopD_hinv base) (loopD_hgrow base)
    (fun s _ ht => lrun_false ltK dBody.g muD s ht)
    (fun s hs ht => ⟨loopD_hdec base s hs ht, lrunD_step base s hs ht⟩)

inductive RT : Z → Z → Prop
  | refl (z : Z) : RT z z
  | step (z z' z'' : Z) : StepD z z' → RT z' z'' → RT z z''

lemma step_kr (z z' : Z) (h : StepD z z') : z.kr.length = z'.kr.length + 1 := by
  obtain ⟨z1, hs, r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩ := h
  have : z1.kr = z.kr := by rcases hs with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩ <;> rfl
  rw [← this, hk]; simp

lemma LGD_char (base : St) : ∀ (n : ℕ) (z : Z), z.kr.length = n → ZInv z →
    LGD (ZSt base z) Reg.BAD ≠ [] ∨ ∃ z', RT z z' ∧ z'.kr = [] ∧ LGD (ZSt base z) = ZSt base z' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hz
    by_cases hk : z.kr = []
    · right
      refine ⟨z, RT.refl z, hk, ?_⟩
      apply lrun_false
      rw [← Bool.not_eq_true, ltK_iff]; simp [hk]
    · have hj : JD base (ZSt base z) := ⟨ZSt_Gi base z, Or.inr ⟨z, hz, rfl⟩⟩
      have ht : ltK (hd (ZSt base z)) = true := by
        rw [ltK_iff]; exact ⟨by simpa using hk, rfl⟩
      rw [lrunD_step base _ hj ht]
      rcases bodyD_g base z hz hk with hb | ⟨z', hs, he⟩
      · left
        have hf : ltK (hd (dBody.g (ZSt base z))) = false := by
          rw [← Bool.not_eq_true, ltK_iff]; simp [hb]
        unfold LGD; rw [lrun_false _ _ _ _ hf]; exact hb
      · rw [he]
        have hl := step_kr z z' hs
        rcases ih z'.kr.length (by omega) z' rfl (step_num base z z' hz hs).1 with h1 | ⟨z'', hr, hk2, he2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨z'', RT.step z z' z'' hs hr, hk2, he2⟩

end Stk

end Sec_Ap8

section Sec_Ap9
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section Fold
variable {Y : Type}

def Efold (E0 : Y → St) (y : Y) (l : List (List Bool × List Bool)) : St := upd (E0 y) Reg.TM (encPs l)

def ltM : (Reg → Option Al) → Bool := fun h => (h Reg.TM).isSome && (h Reg.BAD).isNone

def muM (s : St) : ℕ := if s Reg.BAD = [] then 3 * (s Reg.TM).length else 0

def JF (E0 : Y → St) (s : St) : Prop := Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ y l, s = Efold E0 y l)

lemma ltM_iff (s : St) : ltM (hd s) = true ↔ s Reg.TM ≠ [] ∧ s Reg.BAD = [] := by
  unfold ltM hd
  cases h1 : s Reg.TM <;> cases h2 : s Reg.BAD <;> simp

lemma muM_le (s : St) : muM s ≤ 3 * S s := by
  unfold muM; split_ifs
  · have := len_le_S s Reg.TM; omega
  · exact Nat.zero_le _

structure FoldHyp (body : GB) (E0 : Y → St) (f : Y → List Bool × List Bool → Y) : Prop where
  gi : ∀ y, Gi (E0 y)
  bad : ∀ y, E0 y Reg.BAD = []
  tm : ∀ y, E0 y Reg.TM = []
  pre : ∀ s, body.pre s
  step : ∀ y p l, body.ok (Efold E0 y (p :: l)) ∧ body.T (Efold E0 y (p :: l)) = Efold E0 (f y p) l
  sz : ∀ y p, S (E0 (f y p)) ≤ S (E0 y) + 4 * (p.1.length + p.2.length + 2)

lemma Efold_TM (E0 : Y → St) (y : Y) (l : List (List Bool × List Bool)) : Efold E0 y l Reg.TM = encPs l := by
  simp [Efold]

lemma Efold_BAD {body : GB} {E0 : Y → St} {f : Y → List Bool × List Bool → Y} (h : FoldHyp body E0 f)
    (y : Y) (l : List (List Bool × List Bool)) : Efold E0 y l Reg.BAD = [] := by
  simp [Efold, upd_apply, h.bad y]

lemma Efold_Gi {body : GB} {E0 : Y → St} {f : Y → List Bool × List Bool → Y} (h : FoldHyp body E0 f)
    (y : Y) (l : List (List Bool × List Bool)) : Gi (Efold E0 y l) := by
  have := h.gi y
  refine ⟨?_, ?_⟩ <;> simp [Efold, upd_apply, this.1, this.2]

lemma S_Efold {body : GB} {E0 : Y → St} {f : Y → List Bool × List Bool → Y} (h : FoldHyp body E0 f)
    (y : Y) (l : List (List Bool × List Bool)) : S (Efold E0 y l) = S (E0 y) + szP l := by
  have := S_upd (E0 y) Reg.TM (encPs l)
  rw [h.tm y] at this
  simp only [List.length_nil, encPs_len] at this
  unfold Efold; omega

lemma szP_cons' (p : List Bool × List Bool) (l : List (List Bool × List Bool)) :
    szP (p :: l) = p.1.length + p.2.length + 2 + szP l := by simp [szP]

variable {body : GB} {E0 : Y → St} {f : Y → List Bool × List Bool → Y}

lemma JF_true (h : FoldHyp body E0 f) (s : St) (hs : JF E0 s) (ht : ltM (hd s) = true) :
    ∃ y p l, s = Efold E0 y (p :: l) := by
  rw [ltM_iff] at ht
  rcases hs.2 with h2 | ⟨y, l, rfl⟩
  · exact absurd ht.2 h2
  · cases l with
    | nil => exact absurd (by simp [Efold_TM]) ht.1
    | cons p l => exact ⟨y, p, l, rfl⟩

lemma foldbody_g (h : FoldHyp body E0 f) (y : Y) (p : List Bool × List Bool) (l : List (List Bool × List Bool)) :
    body.g (Efold E0 y (p :: l)) = Efold E0 (f y p) l := by
  have hh := body.h.2.2.2 (Efold E0 y (p :: l)) (Efold_Gi h _ _) (h.pre _) (Efold_BAD h _ _)
  have ho := (h.step y p l).1
  rw [hh.2 ho]; exact (h.step y p l).2

lemma fold_hinv (h : FoldHyp body E0 f) (s : St) (hs : JF E0 s) (ht : ltM (hd s) = true) : JF E0 (body.g s) := by
  refine ⟨body.h.1.2 s hs.1, ?_⟩
  obtain ⟨y, p, l, rfl⟩ := JF_true h s hs ht
  rw [foldbody_g h]; exact Or.inr ⟨_, _, rfl⟩

lemma fold_hdec (h : FoldHyp body E0 f) (s : St) (hs : JF E0 s) (ht : ltM (hd s) = true) :
    muM (body.g s) < muM s := by
  obtain ⟨y, p, l, rfl⟩ := JF_true h s hs ht
  rw [foldbody_g h]
  have e1 := Efold_BAD h y (p :: l)
  have e2 := Efold_BAD h (f y p) l
  simp only [muM, e1, e2, if_true, Efold_TM, encPs_len, szP_cons']
  omega

lemma fold_hgrow (h : FoldHyp body E0 f) (s : St) (hs : JF E0 s) (ht : ltM (hd s) = true)
    (_ : ltM (hd (body.g s)) = true) : S (body.g s) + muM (body.g s) ≤ S s + muM s := by
  obtain ⟨y, p, l, rfl⟩ := JF_true h s hs ht
  rw [foldbody_g h]
  have e1 := Efold_BAD h y (p :: l)
  have e2 := Efold_BAD h (f y p) l
  have := h.sz y p
  simp only [muM, e1, e2, if_true, Efold_TM, encPs_len, szP_cons', S_Efold h]
  omega

lemma fold_PSp (h : FoldHyp body E0 f) : PSp (JF E0) (.loop ltM body.p) (lrun ltM body.g muM) :=
  PSp.loopJ3 ltM (lrun ltM body.g muM) muM (PSp.weaken body.h.1.1 (fun s hs => hs.1)) muM_le
    (fold_hinv h) (fold_hgrow h)
    (fun s _ ht => lrun_false ltM body.g muM s ht)
    (fun s hs ht => ⟨fold_hdec h s hs ht, lrun_true (JF E0) ltM body.g muM (fold_hinv h) (fold_hdec h) s hs ht⟩)

lemma fold_char (h : FoldHyp body E0 f) :
    ∀ (l : List (List Bool × List Bool)) (y : Y),
      lrun ltM body.g muM (Efold E0 y l) = Efold E0 (l.foldl f y) [] := by
  intro l
  induction l with
  | nil =>
    intro y
    apply lrun_false
    rw [← Bool.not_eq_true, ltM_iff]; simp [Efold_TM]
  | cons p l ih =>
    intro y
    have hj : JF E0 (Efold E0 y (p :: l)) := ⟨Efold_Gi h _ _, Or.inr ⟨y, p :: l, rfl⟩⟩
    have ht : ltM (hd (Efold E0 y (p :: l))) = true := by
      rw [ltM_iff]; exact ⟨by simp [Efold_TM, encPs, encP], Efold_BAD h _ _⟩
    rw [lrun_true (JF E0) ltM body.g muM (fold_hinv h) (fold_hdec h) _ hj ht, foldbody_g h, ih]
    rfl

end Fold
end Stk

end Sec_Ap9

section Sec_Ap10
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

structure Y where
  cd : List (List Bool × List Bool)
  a1 : List Bool
  a2 : List Bool
  m1 : List Bool
  m2 : List Bool
  k1 : ℕ
  k2 : ℕ
  kc : ℕ
  nf : ℕ
  ac : List Bool
  bc : List Bool
  o1 : Bool
  o2 : Bool
  cnt : ℕ
  hh : Bool

def flag (b : Bool) : List Al := if b then [mk] else []

def YS (base : St) (y : Y) : St := fun r =>
  match r with
  | Reg.TM => []
  | Reg.NC2 => (encPs y.cd).reverse
  | Reg.K2 => y.a1.map tkb
  | Reg.T2 => y.a2.map tkb
  | Reg.PP => y.m1.map tkb
  | Reg.TT => y.m2.map tkb
  | Reg.NC => List.replicate y.k1 mk
  | Reg.TC => List.replicate y.k2 mk
  | Reg.K => List.replicate y.kc (ty BSym.minus)
  | Reg.IN => List.replicate y.nf mk
  | Reg.W => y.ac.map tkb
  | Reg.WR => y.bc.map tkb
  | Reg.KR => flag y.o1
  | Reg.T => flag y.o2
  | Reg.NB => List.replicate y.cnt mk
  | Reg.H => flag y.hh
  | Reg.MB => []
  | Reg.KB => []
  | Reg.TMP => []
  | Reg.LT => []
  | Reg.FP => []
  | Reg.BAD => []
  | Reg.C => []
  | Reg.RC => []
  | r => base r

def YSt (base : St) (y : Y) (l : List (List Bool × List Bool)) : St := Efold (YS base) y l

lemma YSt_TM (base : St) (y : Y) (l : List (List Bool × List Bool)) : YSt base y l Reg.TM = encPs l := by
  simp [YSt, Efold]

lemma YSt_eq (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    YSt base y l = fun r => if r = Reg.TM then encPs l else YS base y r := by
  funext r; simp [YSt, Efold, upd_apply]

end Stk

end Sec_Ap10

section Sec_Ap11
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma cmpL_gen (g : Bool) (s : St) (mb kb : List Bool) (hmb : s Reg.MB = mb.map tkb)
    (hkb : s Reg.KB = kb.map tkb) :
    (cmpL g).T s = upd (upd (upd s Reg.MB []) Reg.KB []) Reg.H
      (flag (decide (val kb < val mb ∨ (val mb = val kb ∧ g = true)))) := by
  have hg : ∀ s' : St, s' Reg.MB = mb.map tkb → s' Reg.KB = kb.map tkb →
      (upd (cmpF s') Reg.BAD (s' Reg.BAD)) = upd (upd (upd s' Reg.MB []) Reg.KB []) Reg.H
      (flag (decide (val kb < val mb ∨ (val mb = val kb ∧ (decide (s' Reg.H ≠ [])) = true)))) := by
    intro s' h1 h2
    unfold cmpF
    rw [h1, h2, cf_val]
    funext r
    by_cases hr : r = Reg.BAD
    · subst hr; simp [upd_apply]
    · simp [upd_apply, hr, flag]
  have hH : ∀ (s' : St) (x : List Al), upd (upd (upd (upd s' Reg.H []) Reg.MB []) Reg.KB []) Reg.H x = upd (upd (upd s' Reg.MB []) Reg.KB []) Reg.H x := by
    intro s' x; funext r; by_cases hr : r = Reg.H <;> simp [upd_apply, hr]
  cases g
  · have := hg (upd s Reg.H []) (by simp [upd_apply, hmb]) (by simp [upd_apply, hkb])
    simp only [cmpL, GB.seq, bClear, skipB, GB.ofGs, bCmp, gClear, Bool.false_eq_true, if_false, id] at this ⊢
    rw [this]
    simp [hH, upd_apply]
  · have := hg (upd (upd s Reg.H []) Reg.H (mk :: upd s Reg.H [] Reg.H)) (by simp [upd_apply, hmb]) (by simp [upd_apply, hkb])
    simp only [cmpL, GB.seq, bClear, bPush, GB.ofGs, bCmp, gClear, gPush, if_true, id] at this ⊢
    rw [this]
    funext r
    by_cases hr : r = Reg.H <;> by_cases hb : r = Reg.MB <;> by_cases hk : r = Reg.KB <;> simp [upd_apply, hr, hb, hk]

end Stk

end Sec_Ap11

section Sec_Ap12
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section ops2
variable (base : St) (y : Y) (l : List (List Bool × List Bool))

lemma YSt_BAD (base : St) (y : Y) (l : List (List Bool × List Bool)) : YSt base y l Reg.BAD = [] := by
  simp [YSt_eq, YS]
lemma YSt_Gi (base : St) (y : Y) (l : List (List Bool × List Bool)) : Gi (YSt base y l) := by
  constructor <;> simp [YSt_eq, YS]

lemma c_K2 : gClear Reg.K2 (YSt base y l) = YSt base {y with a1 := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_T2 : gClear Reg.T2 (YSt base y l) = YSt base {y with a2 := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_PP : gClear Reg.PP (YSt base y l) = YSt base {y with m1 := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_TT : gClear Reg.TT (YSt base y l) = YSt base {y with m2 := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_NC : gClear Reg.NC (YSt base y l) = YSt base {y with k1 := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_TC : gClear Reg.TC (YSt base y l) = YSt base {y with k2 := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_W : gClear Reg.W (YSt base y l) = YSt base {y with ac := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_WR : gClear Reg.WR (YSt base y l) = YSt base {y with bc := []} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_H : gClear Reg.H (YSt base y l) = YSt base {y with hh := false} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply, flag]
lemma p_NC : gPush Reg.NC mk (YSt base y l) = YSt base {y with k1 := y.k1 + 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, List.replicate_succ]
lemma p_TC : gPush Reg.TC mk (YSt base y l) = YSt base {y with k2 := y.k2 + 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, List.replicate_succ]
lemma p_IN : gPush Reg.IN mk (YSt base y l) = YSt base {y with nf := y.nf + 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, List.replicate_succ]
lemma pop_K : gPop Reg.K (YSt base y l) = YSt base {y with kc := y.kc - 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPop, upd_apply, List.tail_replicate]
lemma cp_K2_PP : gCopy Reg.K2 Reg.PP (YSt base y l) = YSt base {y with m1 := y.a1 ++ y.m1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gCopy, upd_apply]
lemma cp_T2_TT : gCopy Reg.T2 Reg.TT (YSt base y l) = YSt base {y with m2 := y.a2 ++ y.m2} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gCopy, upd_apply]
lemma cp_K2_W : gCopy Reg.K2 Reg.W (YSt base y l) = YSt base {y with ac := y.a1 ++ y.ac} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gCopy, upd_apply]
lemma cp_T2_WR : gCopy Reg.T2 Reg.WR (YSt base y l) = YSt base {y with bc := y.a2 ++ y.bc} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gCopy, upd_apply]
lemma upd_H_YSt (b : Bool) : upd (YSt base y l) Reg.H (flag b) = YSt base {y with hh := b} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, upd_apply]

end ops2
end Stk

end Sec_Ap12

section Sec_Ap13
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def LtH (X Y : Reg) : Prop := X ≠ Reg.KB ∧ X ≠ Reg.MB ∧ Y ≠ Reg.KB ∧ Y ≠ Reg.MB ∧ safe X ∧ safe Y

instance (X Y : Reg) : Decidable (LtH X Y) := by unfold LtH; infer_instance

def cmpLt (X Y : Reg) (h : LtH X Y := by decide) : GB :=
  ((bCopy X Reg.KB h.1 h.2.2.2.2.1 (by decide) (by decide)).seq
    (bCopy Y Reg.MB h.2.2.2.1 h.2.2.2.2.2 (by decide) (by decide))).seq (cmpL false)

lemma cmpLt_pre (X Y : Reg) (h : LtH X Y) (s : St) : (cmpLt X Y h).pre s := by
  refine seq_pre_all (seq_pre_all (fun _ => trivial) (fun _ => trivial)) (fun s' => cmpL_pre false s') s

lemma cmpLt_spec (X Y : Reg) (h : LtH X Y) (s : St) (xs ys : List Bool)
    (hX : s X = xs.map tkb) (hY : s Y = ys.map tkb) (hM : s Reg.MB = []) (hK : s Reg.KB = []) :
    (cmpLt X Y h).ok s ∧ (cmpLt X Y h).T s = upd s Reg.H (flag (decide (val xs < val ys))) := by
  refine ⟨by simp [cmpLt], ?_⟩
  have hXK : X ≠ Reg.KB := h.1
  have hYK : Y ≠ Reg.KB := h.2.2.1
  have hYM : Y ≠ Reg.MB := h.2.2.2.1
  have e0 : (cmpLt X Y h).T s = (cmpL false).T (gCopy Y Reg.MB (gCopy X Reg.KB s)) := rfl
  have e1 : (gCopy Y Reg.MB (gCopy X Reg.KB s)) Reg.KB = xs.map tkb := by
    simp [gCopy, upd_apply, hX, hK]
  have e2 : (gCopy Y Reg.MB (gCopy X Reg.KB s)) Reg.MB = ys.map tkb := by
    simp [gCopy, upd_apply, hY, hM, hYK]
  rw [e0, cmpL_gen false _ ys xs e2 e1]
  have e3 : decide (val xs < val ys ∨ val ys = val xs ∧ false = true) = decide (val xs < val ys) := by simp
  rw [e3]
  funext r
  by_cases hH : r = Reg.H
  · subst hH; simp [upd_apply]
  by_cases hm : r = Reg.MB
  · subst hm; simp [upd_apply, hM]
  by_cases hk : r = Reg.KB
  · subst hk; simp [upd_apply, hK]
  simp [upd_apply, gCopy, hH, hm, hk]

end Stk

end Sec_Ap13

section Sec_Ap14
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma cmpLt_YSt (P Q : Reg) (h : LtH P Q) (base : St) (y : Y) (l : List (List Bool × List Bool))
    (xs ys : List Bool) (hX : YSt base y l P = xs.map tkb) (hY : YSt base y l Q = ys.map tkb) :
    (cmpLt P Q h).ok (YSt base y l) ∧
    (cmpLt P Q h).T (YSt base y l) = YSt base {y with hh := decide (val xs < val ys)} l := by
  obtain ⟨o, t⟩ := cmpLt_spec P Q h (YSt base y l) xs ys hX hY (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  exact ⟨o, by rw [t, upd_H_YSt]⟩

def maxB1 : GB :=
  (cmpLt Reg.PP Reg.K2).seq <|
  (GB.branch (isNoneT Reg.H)
    ((cmpLt Reg.K2 Reg.PP).seq (GB.branch (isNoneT Reg.H) (bPush Reg.NC mk) skipB))
    ((bClear Reg.PP).seq <| (bCopy Reg.K2 Reg.PP).seq <| (bClear Reg.NC).seq (bPush Reg.NC mk))).seq
  (bClear Reg.H)

lemma maxB1_pre (s : St) : maxB1.pre s := by
  refine seq_pre_all (cmpLt_pre _ _ _) (seq_pre_all (branch_pre_all _ (seq_pre_all (cmpLt_pre _ _ _)
    (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)))
    (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (fun _ => trivial))))) (fun _ => trivial)) s

lemma maxB1_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    maxB1.ok (YSt base y l) ∧ maxB1.T (YSt base y l) = YSt base
      {y with m1 := if val y.m1 < val y.a1 then y.a1 else y.m1,
              k1 := if val y.m1 < val y.a1 then 1 else if val y.a1 < val y.m1 then y.k1 else y.k1 + 1,
              hh := false} l := by
  obtain ⟨o1, t1⟩ := cmpLt_YSt Reg.PP Reg.K2 (by decide) base y l y.m1 y.a1 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  by_cases h1 : val y.m1 < val y.a1
  · have hd1 : isNoneT Reg.H (hd (YSt base {y with hh := true} l)) = false := by
      simp [isNoneT, hd, YSt_eq, YS, flag]
    simp only [maxB1, seq_ok, seq_T, o1, t1, true_and, decide_eq_true h1, GB.branch, hd1, Bool.false_eq_true,
      if_false, bClear_ok, bClear_T, bCopy_ok, bCopy_T, bPush_ok, bPush_T, c_PP, cp_K2_PP, c_NC, p_NC, c_H, and_true]
    simp [h1]
  · have hd1 : isNoneT Reg.H (hd (YSt base {y with hh := false} l)) = true := by
      simp [isNoneT, hd, YSt_eq, YS, flag]
    obtain ⟨o2, t2⟩ := cmpLt_YSt Reg.K2 Reg.PP (by decide) base {y with hh := false} l y.a1 y.m1 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
    by_cases h2 : val y.a1 < val y.m1
    · have hd2 : isNoneT Reg.H (hd (YSt base {y with hh := true} l)) = false := by
        simp [isNoneT, hd, YSt_eq, YS, flag]
      simp only [maxB1, seq_ok, seq_T, o1, t1, true_and, decide_eq_false h1, GB.branch, hd1, if_true,
        o2, t2, decide_eq_true h2, hd2, Bool.false_eq_true, if_false, skipB_ok, skipB_T, bClear_ok, bClear_T, c_H, and_true]
      simp [h1, h2]
    · have hd2 : isNoneT Reg.H (hd (YSt base {y with hh := false} l)) = true := by
        simp [isNoneT, hd, YSt_eq, YS, flag]
      simp only [maxB1, seq_ok, seq_T, o1, t1, true_and, decide_eq_false h1, GB.branch, hd1, if_true,
        o2, t2, decide_eq_false h2, hd2, bClear_ok, bClear_T, bPush_ok, bPush_T, p_NC, c_H]
      simp [h1, h2]

def maxB2 : GB :=
  (cmpLt Reg.TT Reg.T2).seq <|
  (GB.branch (isNoneT Reg.H)
    ((cmpLt Reg.T2 Reg.TT).seq (GB.branch (isNoneT Reg.H) (bPush Reg.TC mk) skipB))
    ((bClear Reg.TT).seq <| (bCopy Reg.T2 Reg.TT).seq <| (bClear Reg.TC).seq (bPush Reg.TC mk))).seq
  (bClear Reg.H)

lemma maxB2_pre (s : St) : maxB2.pre s := by
  refine seq_pre_all (cmpLt_pre _ _ _) (seq_pre_all (branch_pre_all _ (seq_pre_all (cmpLt_pre _ _ _)
    (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)))
    (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (fun _ => trivial))))) (fun _ => trivial)) s

lemma maxB2_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    maxB2.ok (YSt base y l) ∧ maxB2.T (YSt base y l) = YSt base
      {y with m2 := if val y.m2 < val y.a2 then y.a2 else y.m2,
              k2 := if val y.m2 < val y.a2 then 1 else if val y.a2 < val y.m2 then y.k2 else y.k2 + 1,
              hh := false} l := by
  obtain ⟨o1, t1⟩ := cmpLt_YSt Reg.TT Reg.T2 (by decide) base y l y.m2 y.a2 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  by_cases h1 : val y.m2 < val y.a2
  · have hd1 : isNoneT Reg.H (hd (YSt base {y with hh := true} l)) = false := by
      simp [isNoneT, hd, YSt_eq, YS, flag]
    simp only [maxB2, seq_ok, seq_T, o1, t1, true_and, decide_eq_true h1, GB.branch, hd1, Bool.false_eq_true,
      if_false, bClear_ok, bClear_T, bCopy_ok, bCopy_T, bPush_ok, bPush_T, c_TT, cp_T2_TT, c_TC, p_TC, c_H, and_true]
    simp [h1]
  · have hd1 : isNoneT Reg.H (hd (YSt base {y with hh := false} l)) = true := by
      simp [isNoneT, hd, YSt_eq, YS, flag]
    obtain ⟨o2, t2⟩ := cmpLt_YSt Reg.T2 Reg.TT (by decide) base {y with hh := false} l y.a2 y.m2 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
    by_cases h2 : val y.a2 < val y.m2
    · have hd2 : isNoneT Reg.H (hd (YSt base {y with hh := true} l)) = false := by
        simp [isNoneT, hd, YSt_eq, YS, flag]
      simp only [maxB2, seq_ok, seq_T, o1, t1, true_and, decide_eq_false h1, GB.branch, hd1, if_true,
        o2, t2, decide_eq_true h2, hd2, Bool.false_eq_true, if_false, skipB_ok, skipB_T, bClear_ok, bClear_T, c_H, and_true]
      simp [h1, h2]
    · have hd2 : isNoneT Reg.H (hd (YSt base {y with hh := false} l)) = true := by
        simp [isNoneT, hd, YSt_eq, YS, flag]
      simp only [maxB2, seq_ok, seq_T, o1, t1, true_and, decide_eq_false h1, GB.branch, hd1, if_true,
        o2, t2, decide_eq_false h2, hd2, bClear_ok, bClear_T, bPush_ok, bPush_T, p_TC, c_H]
      simp [h1, h2]


end Stk

end Sec_Ap14

section Sec_Ap15
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma pushPair_YSt (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    pushPair.ok (YSt base y l) ∧ pushPair.T (YSt base y l) =
      YSt base {y with cd := y.cd ++ [(y.a1, y.a2)], a1 := [], a2 := []} l := by
  refine ⟨by simp [pushPair], ?_⟩
  simp only [pushPair, seq_T, bMvA_T, bPush_T]
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gMvA, gPush, upd_apply, encPs_append, encPs, encP, List.map_reverse]

lemma pop2_YSt (base : St) (y : Y) (a b : List Bool) (l : List (List Bool × List Bool)) :
    pop2B.ok (YSt base y ((a, b) :: l)) ∧
    pop2B.T (YSt base y ((a, b) :: l)) = YSt base {y with a1 := a ++ y.a1, a2 := b ++ y.a2} l := by
  simp only [pop2B]
  have hW : YSt base y ((a, b) :: l) Reg.TM = a.map tkb ++ tk BSym.sep :: ((b.map tkb ++ [tk BSym.sep]) ++ encPs l) := by
    simp [YSt_eq, encPs, encP]
  have hT0 : YSt base y ((a, b) :: l) Reg.TMP = [] := by simp [YSt_eq, YS]
  obtain ⟨o1, c1⟩ := popBlk_calc Reg.TM Reg.K2 (YSt base y ((a, b) :: l)) a _ hW hT0 (by decide) (by decide) (by decide)
  have hW2 : PB3 Reg.TM Reg.K2 (YSt base y ((a, b) :: l)) Reg.TM = b.map tkb ++ tk BSym.sep :: encPs l := by
    rw [c1]; simp
  have hT2 : PB3 Reg.TM Reg.K2 (YSt base y ((a, b) :: l)) Reg.TMP = [] := by rw [c1]; simp
  obtain ⟨o2, c2⟩ := popBlk_calc Reg.TM Reg.T2 (PB3 Reg.TM Reg.K2 (YSt base y ((a, b) :: l))) b _ hW2 hT2 (by decide) (by decide) (by decide)
  refine ⟨⟨o1, o2⟩, ?_⟩
  simp only [seq_T, bPopBlk_T_def]
  funext r
  rw [c2]
  cases r <;> simp only [c1] <;> simp [YSt_eq, YS]

def captureB : GB :=
  GB.branch (topS Reg.K) (bPop Reg.K)
    (GB.branch (isNoneT Reg.IN)
      ((bPush Reg.IN mk).seq <| (bClear Reg.W).seq <| (bCopy Reg.K2 Reg.W).seq <|
        (bClear Reg.WR).seq (bCopy Reg.T2 Reg.WR))
      skipB)

lemma captureB_pre (s : St) : captureB.pre s :=
  branch_pre_all _ (fun _ => trivial) (branch_pre_all _
    (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
      (seq_pre_all (fun _ => trivial) (fun _ => trivial))))) (fun _ => trivial)) s

lemma captureB_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    captureB.ok (YSt base y l) ∧ captureB.T (YSt base y l) = YSt base
      (if 0 < y.kc then {y with kc := y.kc - 1}
       else if y.nf = 0 then {y with nf := 1, ac := y.a1, bc := y.a2} else y) l := by
  by_cases hk : 0 < y.kc
  · have hd1 : topS Reg.K (hd (YSt base y l)) = true := by
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
      simp [topS, hd, YSt_eq, YS, hn, List.replicate_succ]
    simp only [captureB, GB.branch, hd1, if_true, bPop_ok, bPop_T, pop_K, hk, true_and]
  · have hk0 : y.kc = 0 := by omega
    have hd1 : topS Reg.K (hd (YSt base y l)) = false := by
      simp [topS, hd, YSt_eq, YS, hk0]
    by_cases hn : y.nf = 0
    · have hd2 : isNoneT Reg.IN (hd (YSt base y l)) = true := by
        simp [isNoneT, hd, YSt_eq, YS, hn]
      simp only [captureB, GB.branch, hd1, hd2, Bool.false_eq_true, if_false, if_true, seq_ok, seq_T, bPush_ok,
        bPush_T, bClear_ok, bClear_T, bCopy_ok, bCopy_T, p_IN, c_W, cp_K2_W, c_WR, cp_T2_WR, hk, hn, true_and]
      simp
    · have hd2 : isNoneT Reg.IN (hd (YSt base y l)) = false := by
        obtain ⟨n, hn'⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp [isNoneT, hd, YSt_eq, YS, hn', List.replicate_succ]
      simp only [captureB, GB.branch, hd1, hd2, Bool.false_eq_true, if_false, skipB_ok, skipB_T, hk, hn]
      simp

end Stk

end Sec_Ap15

section Sec_Ap16
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

@[simp] lemma YR_IN (base : St) (y : Y) : YS base y Reg.IN = List.replicate y.nf mk := rfl
@[simp] lemma YR_WR (base : St) (y : Y) : YS base y Reg.WR = y.bc.map tkb := rfl
@[simp] lemma YR_W (base : St) (y : Y) : YS base y Reg.W = y.ac.map tkb := rfl
@[simp] lemma YR_N (base : St) (y : Y) : YS base y Reg.N = base Reg.N := rfl
@[simp] lemma YR_K (base : St) (y : Y) : YS base y Reg.K = List.replicate y.kc (ty BSym.minus) := rfl
@[simp] lemma YR_TR (base : St) (y : Y) : YS base y Reg.TR = base Reg.TR := rfl
@[simp] lemma YR_T (base : St) (y : Y) : YS base y Reg.T = flag y.o2 := rfl
@[simp] lemma YR_TMP (base : St) (y : Y) : YS base y Reg.TMP = [] := rfl
@[simp] lemma YR_MB (base : St) (y : Y) : YS base y Reg.MB = [] := rfl
@[simp] lemma YR_NB (base : St) (y : Y) : YS base y Reg.NB = List.replicate y.cnt mk := rfl
@[simp] lemma YR_KB (base : St) (y : Y) : YS base y Reg.KB = [] := rfl
@[simp] lemma YR_U (base : St) (y : Y) : YS base y Reg.U = base Reg.U := rfl
@[simp] lemma YR_F (base : St) (y : Y) : YS base y Reg.F = base Reg.F := rfl
@[simp] lemma YR_HU (base : St) (y : Y) : YS base y Reg.HU = base Reg.HU := rfl
@[simp] lemma YR_C (base : St) (y : Y) : YS base y Reg.C = [] := rfl
@[simp] lemma YR_RC (base : St) (y : Y) : YS base y Reg.RC = [] := rfl
@[simp] lemma YR_BAD (base : St) (y : Y) : YS base y Reg.BAD = [] := rfl
@[simp] lemma YR_OUT (base : St) (y : Y) : YS base y Reg.OUT = base Reg.OUT := rfl
@[simp] lemma YR_KP (base : St) (y : Y) : YS base y Reg.KP = base Reg.KP := rfl
@[simp] lemma YR_NC (base : St) (y : Y) : YS base y Reg.NC = List.replicate y.k1 mk := rfl
@[simp] lemma YR_PP (base : St) (y : Y) : YS base y Reg.PP = y.m1.map tkb := rfl
@[simp] lemma YR_TC (base : St) (y : Y) : YS base y Reg.TC = List.replicate y.k2 mk := rfl
@[simp] lemma YR_T2 (base : St) (y : Y) : YS base y Reg.T2 = y.a2.map tkb := rfl
@[simp] lemma YR_K2 (base : St) (y : Y) : YS base y Reg.K2 = y.a1.map tkb := rfl
@[simp] lemma YR_TM (base : St) (y : Y) : YS base y Reg.TM = [] := rfl
@[simp] lemma YR_NC2 (base : St) (y : Y) : YS base y Reg.NC2 = (encPs y.cd).reverse := rfl
@[simp] lemma YR_TT (base : St) (y : Y) : YS base y Reg.TT = y.m2.map tkb := rfl
@[simp] lemma YR_FP (base : St) (y : Y) : YS base y Reg.FP = [] := rfl
@[simp] lemma YR_H (base : St) (y : Y) : YS base y Reg.H = flag y.hh := rfl
@[simp] lemma YR_MR (base : St) (y : Y) : YS base y Reg.MR = base Reg.MR := rfl
@[simp] lemma YR_KR (base : St) (y : Y) : YS base y Reg.KR = flag y.o1 := rfl
@[simp] lemma YR_LT (base : St) (y : Y) : YS base y Reg.LT = [] := rfl

def Bd (base : St) : ℕ := (base Reg.N).length + (base Reg.TR).length +
  (base Reg.U).length + (base Reg.F).length + (base Reg.HU).length + (base Reg.OUT).length +
  (base Reg.KP).length + (base Reg.MR).length

lemma S_YS (base : St) (y : Y) : S (YS base y) = Bd base + szP y.cd + y.a1.length + y.a2.length +
    y.m1.length + y.m2.length + y.k1 + y.k2 + y.kc + y.nf + y.ac.length + y.bc.length +
    (flag y.o1).length + (flag y.o2).length + y.cnt + (flag y.hh).length := by
  have e : (encPs y.cd).reverse.length = szP y.cd := by rw [List.length_reverse, encPs_len]
  unfold S
  simp only [Finset.univ, Fintype.elems]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [YR_IN, YR_WR, YR_W, YR_N, YR_K, YR_TR, YR_T, YR_TMP, YR_MB, YR_NB, YR_KB, YR_U, YR_F, YR_HU,
    YR_C, YR_RC, YR_BAD, YR_OUT, YR_KP, YR_NC, YR_PP, YR_TC, YR_T2, YR_K2, YR_TM, YR_NC2, YR_TT, YR_FP,
    YR_H, YR_MR, YR_KR, YR_LT, List.length_map, List.length_replicate, List.length_nil, e, Bd]
  ac_rfl

end Stk

end Sec_Ap16

section Sec_Ap17
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def maxY1 (y : Y) : Y :=
  {y with m1 := if val y.m1 < val y.a1 then y.a1 else y.m1,
          k1 := if val y.m1 < val y.a1 then 1 else if val y.a1 < val y.m1 then y.k1 else y.k1 + 1,
          hh := false}
def maxY2 (y : Y) : Y :=
  {y with m2 := if val y.m2 < val y.a2 then y.a2 else y.m2,
          k2 := if val y.m2 < val y.a2 then 1 else if val y.a2 < val y.m2 then y.k2 else y.k2 + 1,
          hh := false}
def capY (y : Y) : Y :=
  if 0 < y.kc then {y with kc := y.kc - 1}
  else if y.nf = 0 then {y with nf := 1, ac := y.a1, bc := y.a2} else y

def fA (y : Y) (p : List Bool × List Bool) : Y :=
  let y3 := capY (maxY2 (maxY1 {y with a1 := p.1 ++ ([] : List Bool), a2 := p.2 ++ ([] : List Bool)}))
  {y3 with cd := y3.cd ++ [(y3.a1, y3.a2)], a1 := [], a2 := []}

def bodyA : GB :=
  (bClear Reg.K2).seq <| (bClear Reg.T2).seq <| pop2B.seq <| maxB1.seq <| maxB2.seq <|
    captureB.seq pushPair

lemma pushPair_pre (s : St) : pushPair.pre s := seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
    (seq_pre_all (fun _ => trivial) (fun _ => trivial))) s

lemma pop2_pre (s : St) : pop2B.pre s := by
  unfold pop2B; exact seq_pre_all (fun _ => trivial) (fun _ => trivial) s

lemma bodyA_pre (s : St) : bodyA.pre s :=
  seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial) (seq_pre_all pop2_pre
    (seq_pre_all maxB1_pre (seq_pre_all maxB2_pre (seq_pre_all captureB_pre pushPair_pre))))) s

lemma maxB1_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : maxB1.ok (YSt base y l) :=
  (maxB1_spec base y l).1
lemma maxB1_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    maxB1.T (YSt base y l) = YSt base (maxY1 y) l := (maxB1_spec base y l).2
lemma maxB2_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : maxB2.ok (YSt base y l) :=
  (maxB2_spec base y l).1
lemma maxB2_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    maxB2.T (YSt base y l) = YSt base (maxY2 y) l := (maxB2_spec base y l).2
lemma cap_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : captureB.ok (YSt base y l) :=
  (captureB_spec base y l).1
lemma cap_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    captureB.T (YSt base y l) = YSt base (capY y) l := (captureB_spec base y l).2
lemma pp_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : pushPair.ok (YSt base y l) :=
  (pushPair_YSt base y l).1
lemma pp_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    pushPair.T (YSt base y l) = YSt base {y with cd := y.cd ++ [(y.a1, y.a2)], a1 := [], a2 := []} l :=
  (pushPair_YSt base y l).2
lemma p2_ok' (base : St) (y : Y) (a b : List Bool) (l : List (List Bool × List Bool)) :
    pop2B.ok (YSt base y ((a, b) :: l)) := (pop2_YSt base y a b l).1
lemma p2_T' (base : St) (y : Y) (a b : List Bool) (l : List (List Bool × List Bool)) :
    pop2B.T (YSt base y ((a, b) :: l)) = YSt base {y with a1 := a ++ y.a1, a2 := b ++ y.a2} l :=
  (pop2_YSt base y a b l).2

lemma bodyA_step (base : St) (y : Y) (p : List Bool × List Bool) (l : List (List Bool × List Bool)) :
    bodyA.ok (Efold (YS base) y (p :: l)) ∧ bodyA.T (Efold (YS base) y (p :: l)) = Efold (YS base) (fA y p) l := by
  obtain ⟨a, b⟩ := p
  show bodyA.ok (YSt base y ((a, b) :: l)) ∧ bodyA.T (YSt base y ((a, b) :: l)) = YSt base (fA y (a, b)) l
  simp only [bodyA, seq_ok, seq_T, bClear_ok, bClear_T, c_K2, c_T2, p2_ok', p2_T', maxB1_ok', maxB1_T',
    maxB2_ok', maxB2_T', cap_ok', cap_T', pp_ok', pp_T', and_self, true_and]
  rfl

lemma szP_one (a b : List Bool) : szP [(a, b)] = a.length + b.length + 2 := by simp [szP]

lemma flag_len (b : Bool) : (flag b).length ≤ 1 := by cases b <;> simp [flag]

lemma fA_sz (base : St) (y : Y) (p : List Bool × List Bool) :
    S (YS base (fA y p)) ≤ S (YS base y) + 4 * (p.1.length + p.2.length + 2) := by
  obtain ⟨a, b⟩ := p
  rw [S_YS, S_YS]
  have h1 := flag_len y.o1
  have h2 := flag_len y.o2
  have h3 := flag_len y.hh
  have h4 : (flag false).length = 0 := by simp [flag]
  simp only [fA, capY, maxY1, maxY2, szP_append, szP_one, List.append_nil, List.length_nil, h4]
  split_ifs <;> simp [flag] <;> omega

lemma foldA_hyp (base : St) : FoldHyp bodyA (YS base) fA where
  gi := fun y => ⟨by simp, by simp⟩
  bad := fun y => by simp
  tm := fun y => by simp
  pre := bodyA_pre
  step := fun y p l => bodyA_step base y p l
  sz := fun y p => fA_sz base y p

end Stk

end Sec_Ap17

section Sec_Ap18
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section tests
variable (base : St) (y : Y) (l : List (List Bool × List Bool))

lemma rep_isSome (n : ℕ) (a : Al) : (List.replicate n a).head?.isSome = decide (n ≠ 0) := by
  cases n <;> simp [List.replicate_succ]

@[simp] lemma tS_H : topS Reg.H (hd (YSt base y l)) = y.hh := by
  simp only [topS, hd, YSt_eq, YS]; cases y.hh <;> simp [flag]
@[simp] lemma tS_KR : topS Reg.KR (hd (YSt base y l)) = y.o1 := by
  simp only [topS, hd, YSt_eq, YS]; cases y.o1 <;> simp [flag]
@[simp] lemma tS_T : topS Reg.T (hd (YSt base y l)) = y.o2 := by
  simp only [topS, hd, YSt_eq, YS]; cases y.o2 <;> simp [flag]
@[simp] lemma tS_IN : topS Reg.IN (hd (YSt base y l)) = decide (y.nf ≠ 0) := by
  simp only [topS, hd, YSt_eq, YS]; simp [rep_isSome]
@[simp] lemma tS_NB : topS Reg.NB (hd (YSt base y l)) = decide (y.cnt ≠ 0) := by
  simp only [topS, hd, YSt_eq, YS]; simp [rep_isSome]
@[simp] lemma tS_K : topS Reg.K (hd (YSt base y l)) = decide (y.kc ≠ 0) := by
  simp only [topS, hd, YSt_eq, YS]; simp [rep_isSome]
@[simp] lemma tS_NC : topS Reg.NC (hd (YSt base y l)) = decide (y.k1 ≠ 0) := by
  simp only [topS, hd, YSt_eq, YS]; simp [rep_isSome]
@[simp] lemma tS_TC : topS Reg.TC (hd (YSt base y l)) = decide (y.k2 ≠ 0) := by
  simp only [topS, hd, YSt_eq, YS]; simp [rep_isSome]
@[simp] lemma nT_H : isNoneT Reg.H (hd (YSt base y l)) = !y.hh := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases y.hh <;> simp [flag]
@[simp] lemma nT_IN : isNoneT Reg.IN (hd (YSt base y l)) = decide (y.nf = 0) := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases h : y.nf <;> simp [List.replicate_succ]
@[simp] lemma nT_NB : isNoneT Reg.NB (hd (YSt base y l)) = decide (y.cnt = 0) := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases h : y.cnt <;> simp [List.replicate_succ]
@[simp] lemma nT_NC : isNoneT Reg.NC (hd (YSt base y l)) = decide (y.k1 = 0) := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases h : y.k1 <;> simp [List.replicate_succ]
@[simp] lemma nT_TC : isNoneT Reg.TC (hd (YSt base y l)) = decide (y.k2 = 0) := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases h : y.k2 <;> simp [List.replicate_succ]
@[simp] lemma nT_K : isNoneT Reg.K (hd (YSt base y l)) = decide (y.kc = 0) := by
  simp only [isNoneT, hd, YSt_eq, YS]; cases h : y.kc <;> simp [List.replicate_succ]

end tests

def eqFl (X Z : Reg) (h1 : LtH X Z := by decide) (h2 : LtH Z X := by decide) : GB :=
  (cmpLt X Z h1).seq <|
    GB.branch (isNoneT Reg.H)
      ((cmpLt Z X h2).seq (GB.branch (isNoneT Reg.H) (bPush Reg.H mk) (bClear Reg.H)))
      (bClear Reg.H)

lemma YSt_hh (base : St) (y : Y) (l : List (List Bool × List Bool)) (b : Bool) (r : Reg) (hr : r ≠ Reg.H) :
    YSt base {y with hh := b} l r = YSt base y l r := by
  cases r <;> simp_all [YSt_eq, YS]

lemma p_H (base : St) (y : Y) (l : List (List Bool × List Bool)) (hy : y.hh = false) :
    gPush Reg.H mk (YSt base y l) = YSt base {y with hh := true} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, hy, flag]

lemma eqFl_pre (X Z : Reg) (h1 : LtH X Z) (h2 : LtH Z X) (s : St) : (eqFl X Z h1 h2).pre s :=
  seq_pre_all (cmpLt_pre _ _ _) (branch_pre_all _ (seq_pre_all (cmpLt_pre _ _ _)
    (branch_pre_all _ (fun _ => trivial) (fun _ => trivial))) (fun _ => trivial)) s

lemma eqFl_spec (X Z : Reg) (h1 : LtH X Z) (h2 : LtH Z X) (hXH : X ≠ Reg.H) (hZH : Z ≠ Reg.H)
    (base : St) (y : Y)
    (l : List (List Bool × List Bool)) (xs zs : List Bool)
    (hX : YSt base y l X = xs.map tkb) (hZ : YSt base y l Z = zs.map tkb) :
    (eqFl X Z h1 h2).ok (YSt base y l) ∧
    (eqFl X Z h1 h2).T (YSt base y l) = YSt base {y with hh := decide (val xs = val zs)} l := by
  obtain ⟨o1, t1⟩ := cmpLt_YSt X Z h1 base y l xs zs hX hZ
  have hX' : ∀ b, YSt base {y with hh := b} l X = xs.map tkb := fun b => by rw [YSt_hh _ _ _ _ _ hXH, hX]
  have hZ' : ∀ b, YSt base {y with hh := b} l Z = zs.map tkb := fun b => by rw [YSt_hh _ _ _ _ _ hZH, hZ]
  by_cases hlt : val xs < val zs
  · simp only [eqFl, seq_ok, seq_T, o1, t1, true_and, decide_eq_true hlt, GB.branch, nT_H, Bool.not_true,
      Bool.false_eq_true, if_false, bClear_ok, bClear_T, c_H]
    have : ¬ val xs = val zs := by omega
    simp [this]
  · obtain ⟨o2, t2⟩ := cmpLt_YSt Z X h2 base {y with hh := false} l zs xs (hZ' false) (hX' false)
    by_cases hlt2 : val zs < val xs
    · simp only [eqFl, seq_ok, seq_T, o1, t1, true_and, decide_eq_false hlt, GB.branch, nT_H, Bool.not_false,
        if_true, o2, t2, decide_eq_true hlt2, Bool.not_true, Bool.false_eq_true, if_false, bClear_ok, bClear_T, c_H]
      have : ¬ val xs = val zs := by omega
      simp [this]
    · simp only [eqFl, seq_ok, seq_T, o1, t1, true_and, decide_eq_false hlt, GB.branch, nT_H, Bool.not_false,
        if_true, o2, t2, decide_eq_false hlt2, Bool.not_false, bPush_ok, bPush_T]
      have : val xs = val zs := by omega
      simp [this, p_H]

end Stk

end Sec_Ap18

section Sec_Ap19
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma c_IN (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    gClear Reg.IN (YSt base y l) = YSt base {y with nf := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]

def nomB1 : GB :=
  GB.branch (topS Reg.KR) ((eqFl Reg.K2 Reg.PP).seq (GB.branch (topS Reg.H) (bPush Reg.IN mk) skipB)) skipB

lemma nomB1_pre (s : St) : (nomB1).pre s :=
  branch_pre_all _ (seq_pre_all (eqFl_pre _ _ _ _) (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)))
    (fun _ => trivial) s

def nomY1 (y : Y) : Y :=
  if y.o1 then (if val y.a1 = val y.m1 then {y with hh := true, nf := y.nf + 1} else {y with hh := false}) else y

lemma nomB1_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (nomB1).ok (YSt base y l) ∧ (nomB1).T (YSt base y l) = YSt base (nomY1 y) l := by
  obtain ⟨o1, t1⟩ := eqFl_spec Reg.K2 Reg.PP (by decide) (by decide) (by decide) (by decide) base y l y.a1 y.m1
    (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  by_cases ho : y.o1 = true
  · by_cases he : val y.a1 = val y.m1
    · simp only [nomB1, GB.branch, tS_KR, ho, if_true, seq_ok, seq_T, o1, t1, true_and, nomY1, decide_eq_true he,
        tS_H, bPush_ok, bPush_T, p_IN]
      simp [he]
    · simp only [nomB1, GB.branch, tS_KR, ho, if_true, seq_ok, seq_T, o1, t1, true_and, nomY1, decide_eq_false he,
        tS_H, Bool.false_eq_true, if_false, skipB_ok, skipB_T]
      simp [he]
  · have ho' : y.o1 = false := by simpa using ho
    simp [nomB1, GB.branch, tS_KR, ho', nomY1, skipB_ok, skipB_T]

def nomB2 : GB :=
  GB.branch (topS Reg.T) ((eqFl Reg.T2 Reg.TT).seq (GB.branch (topS Reg.H) (bPush Reg.IN mk) skipB)) skipB

lemma nomB2_pre (s : St) : (nomB2).pre s :=
  branch_pre_all _ (seq_pre_all (eqFl_pre _ _ _ _) (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)))
    (fun _ => trivial) s

def nomY2 (y : Y) : Y :=
  if y.o2 then (if val y.a2 = val y.m2 then {y with hh := true, nf := y.nf + 1} else {y with hh := false}) else y

lemma nomB2_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (nomB2).ok (YSt base y l) ∧ (nomB2).T (YSt base y l) = YSt base (nomY2 y) l := by
  obtain ⟨o1, t1⟩ := eqFl_spec Reg.T2 Reg.TT (by decide) (by decide) (by decide) (by decide) base y l y.a2 y.m2
    (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  by_cases ho : y.o2 = true
  · by_cases he : val y.a2 = val y.m2
    · simp only [nomB2, GB.branch, tS_T, ho, if_true, seq_ok, seq_T, o1, t1, true_and, nomY2, decide_eq_true he,
        tS_H, bPush_ok, bPush_T, p_IN]
      simp [he]
    · simp only [nomB2, GB.branch, tS_T, ho, if_true, seq_ok, seq_T, o1, t1, true_and, nomY2, decide_eq_false he,
        tS_H, Bool.false_eq_true, if_false, skipB_ok, skipB_T]
      simp [he]
  · have ho' : y.o2 = false := by simpa using ho
    simp [nomB2, GB.branch, tS_T, ho', nomY2, skipB_ok, skipB_T]

end Stk

end Sec_Ap19

section Sec_Ap20
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma addK2T2_YSt (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (addG Reg.K2 Reg.T2).ok (YSt base y l) ∧ (addG Reg.K2 Reg.T2).T (YSt base y l) =
      YSt base {y with a1 := addBits y.a1 y.a2, a2 := []} l := by
  refine ⟨addG_ok _ _ _ _, ?_⟩
  rw [addG_T _ _ _ _ y.a1 y.a2 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])]
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, upd_apply]

lemma addWWR_YSt (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (addG Reg.W Reg.WR).ok (YSt base y l) ∧ (addG Reg.W Reg.WR).T (YSt base y l) =
      YSt base {y with ac := addBits y.ac y.bc, bc := []} l := by
  refine ⟨addG_ok _ _ _ _, ?_⟩
  rw [addG_T _ _ _ _ y.ac y.bc (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])]
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, upd_apply]

def cntB : GB :=
  GB.branch (topS Reg.IN) (GB.branch (isNoneT Reg.H) (bPush Reg.NB mk) skipB) skipB

lemma cntB_pre (s : St) : cntB.pre s :=
  branch_pre_all _ (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)) (fun _ => trivial) s

def cntY (y : Y) : Y := if y.nf ≠ 0 ∧ y.hh = false then {y with cnt := y.cnt + 1} else y

lemma p_NB (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    gPush Reg.NB mk (YSt base y l) = YSt base {y with cnt := y.cnt + 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, List.replicate_succ]

lemma cntB_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    cntB.ok (YSt base y l) ∧ cntB.T (YSt base y l) = YSt base (cntY y) l := by
  by_cases h1 : y.nf ≠ 0
  · by_cases h2 : y.hh = false
    · simp [cntB, GB.branch, h1, h2, cntY, bPush_ok, bPush_T, p_NB]
    · have h2' : y.hh = true := by simpa using h2
      simp [cntB, GB.branch, h1, h2', cntY, skipB_ok, skipB_T]
  · simp [cntB, GB.branch, h1, cntY, skipB_ok, skipB_T]

def nomY12 (y : Y) : Y := nomY2 (nomY1 y)

def fB (y : Y) (p : List Bool × List Bool) : Y :=
  let y2 : Y := {y with a1 := p.1 ++ ([] : List Bool), a2 := p.2 ++ ([] : List Bool)}
  let y5 := nomY2 (nomY1 {y2 with nf := 0})
  let y6 : Y := {y5 with a1 := addBits y5.a1 y5.a2, a2 := []}
  let y8 := cntY {y6 with hh := decide (val y6.a1 < val y6.ac)}
  {y8 with hh := false, nf := 0, a1 := []}

def bodyB : GB :=
  (bClear Reg.K2).seq <| (bClear Reg.T2).seq <| pop2B.seq <| (bClear Reg.IN).seq <|
  nomB1.seq <| nomB2.seq <| (addG Reg.K2 Reg.T2).seq <| (cmpLt Reg.K2 Reg.W).seq <|
  cntB.seq <| (bClear Reg.H).seq <| (bClear Reg.IN).seq <| bClear Reg.K2

lemma bodyB_pre (s : St) : bodyB.pre s := by
  unfold bodyB
  refine seq_pre_all (fun _ => trivial) ?_ s
  refine seq_pre_all (fun _ => trivial) ?_
  refine seq_pre_all pop2_pre ?_
  refine seq_pre_all (fun _ => trivial) ?_
  refine seq_pre_all nomB1_pre ?_
  refine seq_pre_all nomB2_pre ?_
  refine seq_pre_all (addG_pre _ _ _) ?_
  refine seq_pre_all (cmpLt_pre _ _ _) ?_
  refine seq_pre_all cntB_pre ?_
  refine seq_pre_all (fun _ => trivial) ?_
  exact seq_pre_all (fun _ => trivial) (fun _ => trivial)

lemma nom1_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : nomB1.ok (YSt base y l) := (nomB1_spec base y l).1
lemma nom1_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) : nomB1.T (YSt base y l) = YSt base (nomY1 y) l := (nomB1_spec base y l).2
lemma nom2_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : nomB2.ok (YSt base y l) := (nomB2_spec base y l).1
lemma nom2_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) : nomB2.T (YSt base y l) = YSt base (nomY2 y) l := (nomB2_spec base y l).2
lemma add_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : (addG Reg.K2 Reg.T2).ok (YSt base y l) := (addK2T2_YSt base y l).1
lemma add_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) : (addG Reg.K2 Reg.T2).T (YSt base y l) = YSt base {y with a1 := addBits y.a1 y.a2, a2 := []} l := (addK2T2_YSt base y l).2
lemma cnt_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : cntB.ok (YSt base y l) := (cntB_spec base y l).1
lemma cnt_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) : cntB.T (YSt base y l) = YSt base (cntY y) l := (cntB_spec base y l).2
lemma lt_ok' (base : St) (y : Y) (l : List (List Bool × List Bool)) : (cmpLt Reg.K2 Reg.W (by decide)).ok (YSt base y l) :=
  (cmpLt_YSt Reg.K2 Reg.W (by decide) base y l y.a1 y.ac (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])).1
lemma lt_T' (base : St) (y : Y) (l : List (List Bool × List Bool)) : (cmpLt Reg.K2 Reg.W (by decide)).T (YSt base y l) =
    YSt base {y with hh := decide (val y.a1 < val y.ac)} l :=
  (cmpLt_YSt Reg.K2 Reg.W (by decide) base y l y.a1 y.ac (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])).2

lemma bodyB_step (base : St) (y : Y) (p : List Bool × List Bool) (l : List (List Bool × List Bool)) :
    bodyB.ok (Efold (YS base) y (p :: l)) ∧ bodyB.T (Efold (YS base) y (p :: l)) = Efold (YS base) (fB y p) l := by
  obtain ⟨a, b⟩ := p
  show bodyB.ok (YSt base y ((a, b) :: l)) ∧ bodyB.T (YSt base y ((a, b) :: l)) = YSt base (fB y (a, b)) l
  simp only [bodyB, seq_ok, seq_T, bClear_ok, bClear_T, c_K2, c_T2, p2_ok', p2_T', c_IN, nom1_ok', nom1_T',
    nom2_ok', nom2_T', add_ok', add_T', lt_ok', lt_T', cnt_ok', cnt_T', c_H, and_self, true_and]
  rfl

lemma fB_sz (base : St) (y : Y) (p : List Bool × List Bool) :
    S (YS base (fB y p)) ≤ S (YS base y) + 4 * (p.1.length + p.2.length + 2) := by
  obtain ⟨a, b⟩ := p
  rw [S_YS, S_YS]
  have h4 : (flag false).length = 0 := by simp [flag]
  simp only [fB, cntY, nomY1, nomY2, List.length_nil, h4]
  split_ifs <;> simp [flag] <;> omega

lemma foldB_hyp (base : St) : FoldHyp bodyB (YS base) fB where
  gi := fun y => ⟨by simp, by simp⟩
  bad := fun y => by simp
  tm := fun y => by simp
  pre := bodyB_pre
  step := fun y p l => bodyB_step base y p l
  sz := fun y p => fB_sz base y p

end Stk

end Sec_Ap20

section Sec_Ap21
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section ops3
variable (base : St) (y : Y) (l : List (List Bool × List Bool))

lemma c_KR : gClear Reg.KR (YSt base y l) = YSt base {y with o1 := false} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply, flag]
lemma c_T : gClear Reg.T (YSt base y l) = YSt base {y with o2 := false} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply, flag]
lemma c_K : gClear Reg.K (YSt base y l) = YSt base {y with kc := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_NB : gClear Reg.NB (YSt base y l) = YSt base {y with cnt := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma c_TC' : gClear Reg.TC (YSt base y l) = YSt base {y with k2 := 0} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gClear, upd_apply]
lemma p_KR (hy : y.o1 = false) : gPush Reg.KR mk (YSt base y l) = YSt base {y with o1 := true} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, hy, flag]
lemma p_T (hy : y.o2 = false) : gPush Reg.T mk (YSt base y l) = YSt base {y with o2 := true} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, hy, flag]
lemma p_K : gPush Reg.K (ty BSym.minus) (YSt base y l) = YSt base {y with kc := y.kc + 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPush, upd_apply, List.replicate_succ]
lemma pop_NC : gPop Reg.NC (YSt base y l) = YSt base {y with k1 := y.k1 - 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPop, upd_apply, List.tail_replicate]
lemma pop_TC : gPop Reg.TC (YSt base y l) = YSt base {y with k2 := y.k2 - 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPop, upd_apply, List.tail_replicate]
lemma p_NC1 : gClear Reg.NC (YSt base y l) = YSt base {y with k1 := 0} l := c_NC base y l
lemma mv_NC2_TM (y : Y) (base : St) : gMvA Reg.NC2 Reg.TM (YSt base y []) = YSt base {y with cd := []} y.cd := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gMvA, upd_apply, encPs_append]
lemma c_IN' : gClear Reg.IN (YSt base y l) = YSt base {y with nf := 0} l := c_IN base y l

end ops3

def flg1 : GB := (bClear Reg.KR).seq (GB.branch (topS Reg.NC) ((bPop Reg.NC).seq
  (GB.branch (isNoneT Reg.NC) (bPush Reg.KR mk) skipB)) skipB)
def flg2 : GB := (bClear Reg.T).seq (GB.branch (topS Reg.TC) ((bPop Reg.TC).seq
  (GB.branch (isNoneT Reg.TC) (bPush Reg.T mk) skipB)) skipB)

lemma flg1_pre (s : St) : flg1.pre s :=
  seq_pre_all (fun _ => trivial) (branch_pre_all _ (seq_pre_all (fun _ => trivial)
    (branch_pre_all _ (fun _ => trivial) (fun _ => trivial))) (fun _ => trivial)) s
lemma flg2_pre (s : St) : flg2.pre s :=
  seq_pre_all (fun _ => trivial) (branch_pre_all _ (seq_pre_all (fun _ => trivial)
    (branch_pre_all _ (fun _ => trivial) (fun _ => trivial))) (fun _ => trivial)) s

def flgY1 (y : Y) : Y := {y with o1 := decide (y.k1 = 1), k1 := y.k1 - 1}
def flgY2 (y : Y) : Y := {y with o2 := decide (y.k2 = 1), k2 := y.k2 - 1}

lemma flg1_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    flg1.ok (YSt base y l) ∧ flg1.T (YSt base y l) = YSt base (flgY1 y) l := by
  by_cases h0 : y.k1 = 0
  · simp [flg1, GB.branch, c_KR, h0, flgY1, skipB_ok, skipB_T]
  · by_cases h1 : y.k1 = 1
    · simp [flg1, GB.branch, c_KR, h0, h1, pop_NC, p_KR, flgY1, skipB_ok, skipB_T]
    · have : y.k1 - 1 ≠ 0 := by omega
      simp [flg1, GB.branch, c_KR, h0, h1, pop_NC, this, flgY1, skipB_ok, skipB_T]

lemma flg2_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    flg2.ok (YSt base y l) ∧ flg2.T (YSt base y l) = YSt base (flgY2 y) l := by
  by_cases h0 : y.k2 = 0
  · simp [flg2, GB.branch, c_T, h0, flgY2, skipB_ok, skipB_T]
  · by_cases h1 : y.k2 = 1
    · simp [flg2, GB.branch, c_T, h0, h1, pop_TC, p_T, flgY2, skipB_ok, skipB_T]
    · have : y.k2 - 1 ≠ 0 := by omega
      simp [flg2, GB.branch, c_T, h0, h1, pop_TC, this, flgY2, skipB_ok, skipB_T]

def tpB1 (tp : Bool) : GB := if tp then (bClear Reg.NC).seq (bPush Reg.NC mk) else skipB
def tpB2 (tp : Bool) : GB := if tp then (bClear Reg.TC).seq (bPush Reg.TC mk) else skipB
def tpY (tp : Bool) (y : Y) : Y := if tp then {y with k1 := 1, k2 := 1} else y

lemma tpB1_spec (tp : Bool) (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (tpB1 tp).ok (YSt base y l) ∧ (tpB1 tp).T (YSt base y l) = YSt base {y with k1 := if tp then 1 else y.k1} l := by
  cases tp <;> simp [tpB1, c_NC, p_NC, skipB_ok, skipB_T]
lemma tpB2_spec (tp : Bool) (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    (tpB2 tp).ok (YSt base y l) ∧ (tpB2 tp).T (YSt base y l) = YSt base {y with k2 := if tp then 1 else y.k2} l := by
  cases tp <;> simp [tpB2, c_TC', p_TC, skipB_ok, skipB_T]
lemma tpB1_pre (tp : Bool) (s : St) : (tpB1 tp).pre s := by
  cases tp <;> simp only [tpB1, if_true, Bool.false_eq_true, if_false]
  · exact (fun _ => trivial) s
  · exact seq_pre_all (fun _ => trivial) (fun _ => trivial) s
lemma tpB2_pre (tp : Bool) (s : St) : (tpB2 tp).pre s := by
  cases tp <;> simp only [tpB2, if_true, Bool.false_eq_true, if_false]
  · exact (fun _ => trivial) s
  · exact seq_pre_all (fun _ => trivial) (fun _ => trivial) s

def nc1 (y : Y) : Y := {y with kc := 0, hh := decide (val y.ac = val y.m1)}
def nc2 (y : Y) : Y := if y.hh = true ∧ y.o1 = true then {y with kc := y.kc + 1} else y
def nc3 (y : Y) : Y := {y with hh := decide (val y.bc = val y.m2)}
def nc4 (y : Y) : Y := if y.hh = true ∧ y.o2 = true then {y with kc := y.kc + 1} else y
def nomCY (y : Y) : Y := nc4 (nc3 (nc2 (nc1 y)))

def br1 : GB := GB.branch (topS Reg.H) (GB.branch (topS Reg.KR) (bPush Reg.K (ty BSym.minus)) skipB) skipB
def br2 : GB := GB.branch (topS Reg.H) (GB.branch (topS Reg.T) (bPush Reg.K (ty BSym.minus)) skipB) skipB

lemma br1_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    br1.ok (YSt base y l) ∧ br1.T (YSt base y l) = YSt base (nc2 y) l := by
  by_cases ha : y.hh = true <;> by_cases ho : y.o1 = true <;>
    simp [br1, GB.branch, ha, ho, nc2, p_K, skipB_ok, skipB_T]
lemma br2_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    br2.ok (YSt base y l) ∧ br2.T (YSt base y l) = YSt base (nc4 y) l := by
  by_cases ha : y.hh = true <;> by_cases ho : y.o2 = true <;>
    simp [br2, GB.branch, ha, ho, nc4, p_K, skipB_ok, skipB_T]

def nomCB : GB :=
  (bClear Reg.K).seq <| (eqFl Reg.W Reg.PP).seq <| br1.seq <| (eqFl Reg.WR Reg.TT).seq br2

lemma nomCB_pre (s : St) : nomCB.pre s :=
  seq_pre_all (fun _ => trivial) (seq_pre_all (eqFl_pre _ _ _ _) (seq_pre_all
    (branch_pre_all _ (branch_pre_all _ (fun _ => trivial) (fun _ => trivial)) (fun _ => trivial))
    (seq_pre_all (eqFl_pre _ _ _ _) (branch_pre_all _ (branch_pre_all _ (fun _ => trivial) (fun _ => trivial))
      (fun _ => trivial))))) s

lemma nomCB_spec (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    nomCB.ok (YSt base y l) ∧ nomCB.T (YSt base y l) = YSt base (nomCY y) l := by
  obtain ⟨o1, t1⟩ := eqFl_spec Reg.W Reg.PP (by decide) (by decide) (by decide) (by decide) base {y with kc := 0} l
    y.ac y.m1 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  obtain ⟨o2, t2⟩ := eqFl_spec Reg.WR Reg.TT (by decide) (by decide) (by decide) (by decide) base (nc2 (nc1 y)) l
    (nc2 (nc1 y)).bc (nc2 (nc1 y)).m2 (by simp [YSt_eq, YS]) (by simp [YSt_eq, YS])
  have e1 : ({ {y with kc := 0} with hh := decide (val y.ac = val y.m1)} : Y) = nc1 y := rfl
  have e2 : ({ nc2 (nc1 y) with hh := decide (val (nc2 (nc1 y)).bc = val (nc2 (nc1 y)).m2)} : Y) = nc3 (nc2 (nc1 y)) := rfl
  rw [e1] at t1
  rw [e2] at t2
  have b1 := br1_spec base (nc1 y) l
  have b2 := br2_spec base (nc3 (nc2 (nc1 y))) l
  simp only [nomCB, seq_ok, seq_T, bClear_ok, bClear_T, c_K, o1, t1, true_and, b1.1, b1.2, o2, t2, b2.1, b2.2]
  simp [nomCY]

end Stk

end Sec_Ap21

section Sec_Ap22
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

section
variable (base : St) (y : Y) (l : List (List Bool × List Bool))

lemma tpB1_ok' (tp : Bool) : (tpB1 tp).ok (YSt base y l) := (tpB1_spec tp base y l).1
lemma tpB1_T' (tp : Bool) : (tpB1 tp).T (YSt base y l) = YSt base {y with k1 := if tp then 1 else y.k1} l := (tpB1_spec tp base y l).2
lemma tpB2_ok' (tp : Bool) : (tpB2 tp).ok (YSt base y l) := (tpB2_spec tp base y l).1
lemma tpB2_T' (tp : Bool) : (tpB2 tp).T (YSt base y l) = YSt base {y with k2 := if tp then 1 else y.k2} l := (tpB2_spec tp base y l).2
lemma flg1_ok' : flg1.ok (YSt base y l) := (flg1_spec base y l).1
lemma flg1_T' : flg1.T (YSt base y l) = YSt base (flgY1 y) l := (flg1_spec base y l).2
lemma flg2_ok' : flg2.ok (YSt base y l) := (flg2_spec base y l).1
lemma flg2_T' : flg2.T (YSt base y l) = YSt base (flgY2 y) l := (flg2_spec base y l).2
lemma nomCB_ok' : nomCB.ok (YSt base y l) := (nomCB_spec base y l).1
lemma nomCB_T' : nomCB.T (YSt base y l) = YSt base (nomCY y) l := (nomCB_spec base y l).2
lemma addWWR_ok' : (addG Reg.W Reg.WR).ok (YSt base y l) := (addWWR_YSt base y l).1
lemma addWWR_T' : (addG Reg.W Reg.WR).T (YSt base y l) = YSt base {y with ac := addBits y.ac y.bc, bc := []} l := (addWWR_YSt base y l).2
end

def midB (tp : Bool) : GB :=
  (bMvA Reg.NC2 Reg.TM).seq <| (tpB1 tp).seq <| (tpB2 tp).seq <| flg1.seq <| flg2.seq <|
  (bClear Reg.NC).seq <| (bClear Reg.TC).seq <| nomCB.seq <| (addG Reg.W Reg.WR).seq <|
  (bClear Reg.H).seq <| (bClear Reg.IN).seq (bClear Reg.NB)

def midY (tp : Bool) (y : Y) : Y :=
  let y1 : Y := {y with cd := []}
  let y2 : Y := {y1 with k1 := if tp then 1 else y1.k1}
  let y3 : Y := {y2 with k2 := if tp then 1 else y2.k2}
  let y4 : Y := flgY2 (flgY1 y3)
  let y5 : Y := {y4 with k1 := 0}
  let y6 : Y := {y5 with k2 := 0}
  let y7 : Y := nomCY y6
  let y8 : Y := {y7 with ac := addBits y7.ac y7.bc, bc := []}
  let y9 : Y := {y8 with hh := false}
  let y10 : Y := {y9 with nf := 0}
  {y10 with cnt := 0}

lemma midB_pre (tp : Bool) (s : St) : (midB tp).pre s := by
  unfold midB
  refine seq_pre_all (fun _ => trivial) ?_ s; intro s
  refine seq_pre_all (fun s => tpB1_pre tp s) ?_ s; intro s
  refine seq_pre_all (fun s => tpB2_pre tp s) ?_ s; intro s
  refine seq_pre_all (fun s => flg1_pre s) ?_ s; intro s
  refine seq_pre_all (fun s => flg2_pre s) ?_ s; intro s
  refine seq_pre_all (fun _ => trivial) ?_ s; intro s
  refine seq_pre_all (fun _ => trivial) ?_ s; intro s
  refine seq_pre_all (fun s => nomCB_pre s) ?_ s; intro s
  refine seq_pre_all (fun s => addG_pre _ _ _ s) ?_ s; intro s
  refine seq_pre_all (fun _ => trivial) ?_ s; intro s
  exact seq_pre_all (fun _ => trivial) (fun _ => trivial) s

lemma midB_spec (tp : Bool) (base : St) (y : Y) :
    (midB tp).ok (YSt base y []) ∧ (midB tp).T (YSt base y []) = YSt base (midY tp y) y.cd := by
  simp only [midB, seq_ok, seq_T, bMvA_ok, bMvA_T, mv_NC2_TM, tpB1_ok', tpB1_T', tpB2_ok', tpB2_T', flg1_ok', flg1_T',
    flg2_ok', flg2_T', bClear_ok, bClear_T, c_NC, c_TC, nomCB_ok', nomCB_T', addWWR_ok', addWWR_T', c_H, c_IN', c_NB,
    true_and]
  rfl

lemma pop_NBY (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    gPop Reg.NB (YSt base y l) = YSt base {y with cnt := y.cnt - 1} l := by
  funext r; cases r <;> first | rfl | simp [YSt_eq, YS, gPop, upd_apply, List.tail_replicate]

def finB : GB := (bBad (isNoneT Reg.K)).seq <| (bBad (isNoneT Reg.NB)).seq <|
  (bPop Reg.NB).seq (bBad (topS Reg.NB))

lemma finB_pre (s : St) : finB.pre s :=
  seq_pre_all (fun _ => trivial) (seq_pre_all (fun _ => trivial)
    (seq_pre_all (fun _ => trivial) (fun _ => trivial))) s

lemma finB_ok (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    finB.ok (YSt base y l) ↔ y.kc ≠ 0 ∧ y.cnt = 1 := by
  simp only [finB, seq_ok, seq_T, bBad_ok, bBad_T, bPop_ok, bPop_T, pop_NBY, nT_K, nT_NB, tS_NB, true_and]
  by_cases h1 : y.kc = 0 <;> by_cases h2 : y.cnt = 0 <;> simp [h1, h2]
  omega

end Stk

end Sec_Ap22

section Sec_Ap23
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def hdrB : GB :=
  (bEq Reg.MB Reg.N).seq <| (bEq Reg.KB Reg.K).seq <|
  (bCopy Reg.T Reg.TC).seq <| (bFill Reg.TC Reg.T2 mk).seq <| (bEq Reg.NB Reg.T2).seq <|
    (bClear Reg.T2).seq <|
  bParse.seq <| (bMvA Reg.MR Reg.KR).seq <| (bBad (topS Reg.FP)).seq <|
  (bCopy Reg.N Reg.NC).seq <| (bFill Reg.NC Reg.TM (tk BSym.sep)).seq <|
  (bCopy Reg.N Reg.NC).seq <| (bFill Reg.NC Reg.TM (tk BSym.sep))

lemma hdrB_pre (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    hdrB.pre (sQ3 bl1 bl2 bl3 rest a b t) := by
  simp only [hdrB, GB.seq, bEq, bBad, bCopy, bFill, bClear, bParse, bMvA, GB.ofGs]
  simp only [eqT, gCopy, flF, upd_apply, sQ3, reduceCtorEq, ↓reduceIte, id, Gi]
  simp [hd, topS, PInv, paF, gMvA, gClear, sQ3]


def base0 (c m : ℕ) : St := fun r =>
  if r = Reg.K then List.replicate c (ty BSym.minus)
  else if r = Reg.N then List.replicate m (ty BSym.sep) else []

def z0 (a : ℕ) (t bs : List Bool) : Z :=
  ⟨bs, t, a, 0, [], List.replicate a ([], []), [], [], [], []⟩

def HdrCl (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) : Prop :=
  List.map tkb bl1 = List.map tkb a.bits ∧ List.map tkb bl3 = List.map tkb b.bits ∧
  List.map tkb bl2 = List.map tkb t.length.bits ∧
  (List.foldl ps (false, [], 0) (List.map tk rest)).2.2 = 0 ∧
  (List.foldl ps (false, [], 0) (List.map tk rest)).1 = false

lemma hdrB_ok_cl (bl1 bl2 bl3 : List Bool) (rest : List BSym) (a b : ℕ) (t : List Bool) :
    hdrB.ok (sQ3 bl1 bl2 bl3 rest a b t) ↔ HdrCl bl1 bl2 bl3 rest a b t := by
  simp only [hdrB, GB.seq, bEq, bBad, bCopy, bFill, bClear, bParse, bMvA, GB.ofGs]
  simp only [eqT, gCopy, flF, upd_apply, sQ3, reduceCtorEq, ↓reduceIte, id]
  simp [hd, topS, paNB, gMvA, gClear, paF, upd_apply, HdrCl, sQ3]


lemma encPs_rep : ∀ a : ℕ, List.flatMap encP (List.replicate a ([], [])) =
    List.replicate (a + a) (tk BSym.sep)
  | 0 => rfl
  | a + 1 => by
    rw [List.replicate_succ, List.flatMap_cons, encPs_rep a]
    have : a + 1 + (a + 1) = (a + a) + 1 + 1 := by omega
    rw [this, List.replicate_succ, List.replicate_succ]
    simp only [encP, List.map_nil, List.nil_append, List.cons_append, List.append_nil, List.cons_append]

lemma hdrB_T (a b : ℕ) (t bs : List Bool) :
    hdrB.T (sQ3 a.bits t.length.bits b.bits (encBits bs) a b t) = ZSt (base0 b a) (z0 a t bs) := by
  have hp : (List.foldl ps (false, [], 0) (List.map tk (encBits bs))) = (false, bs.reverse.map tyb, 0) :=
    (parse_iff (encBits bs) false [] 0 _).2 ⟨rfl, bs, by simp, by simp⟩
  simp only [hdrB, GB.seq, bEq, bBad, bCopy, bFill, bClear, bParse, bMvA, GB.ofGs]
  simp only [eqT, gCopy, flF, upd_apply, sQ3, reduceCtorEq, ↓reduceIte, id]
  funext r
  cases r <;> simp [topS, gMvA, gClear, paF, upd_apply, sQ3, ZSt, base0, z0, hp, encPs]
  exact (encPs_rep a).symm


def y0 (c : ℕ) : Y := ⟨[], [], [], [], [], 0, 0, c, 0, [], [], false, false, 0, false⟩

def postB : GB :=
  (bBad (topS Reg.T)).seq <| (bBad (topS Reg.NC)).seq <| (bMvA Reg.NC2 Reg.TM).seq (bClear Reg.TC)

lemma postB_pre (base : St) (z : Z) : postB.pre (ZSt base z) := by
  simp only [postB, GB.seq, bBad, bMvA, bClear, GB.ofGs]
  simp

lemma postB_ok (base : St) (z : Z) : postB.ok (ZSt base z) ↔ z.t = [] ∧ z.nr = 0 := by
  simp only [postB, GB.seq, bBad, bMvA, bClear, GB.ofGs]
  simp only [id]
  have h1 : topS Reg.T (hd (ZSt base z)) = false ↔ z.t = [] := by
    cases h : z.t <;> simp [topS, hd, ZSt, h, tyb]
  have h2 : topS Reg.NC (hd (ZSt base z)) = false ↔ z.nr = 0 := by
    cases h : z.nr <;> simp [topS, hd, ZSt, h, List.replicate_succ]
  rw [h1, h2]; simp


lemma postB_T (c m : ℕ) (z : Z) (hkr : z.kr = []) (ht : z.t = []) (hnr : z.nr = 0) (hnm : z.nm = m)
    (h1 : z.a1 = []) (h2 : z.a2 = []) (h3 : z.one = []) :
    postB.T (ZSt (base0 c m) z) = YSt (base0 c m) (y0 c) (z.cd ++ z.ct) := by
  simp only [postB, GB.seq, bBad, bMvA, bClear, GB.ofGs]
  simp only [id]
  funext r
  cases r <;> simp [gMvA, gClear, upd_apply, ZSt, YSt, Efold, YS, y0, base0, hkr, ht, hnr, hnm, h1, h2, h3, flag, encPs, List.flatMap_append]

end Stk

end Sec_Ap23

section Sec_Ap24
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

def hd1 : GB := (bStNum Reg.MB).seq <| (bStNum Reg.NB).seq <| (bStNum Reg.KB).seq hdrB

lemma hd1_pre (w : List BSym) (a b : ℕ) (t : List Bool) : hd1.pre (stateA w a b t) := by
  simp only [hd1, GB.seq, bStNum, GB.ofGs]
  refine ⟨trivial, fun _ _ o1 => ⟨trivial, fun _ _ o2 => ⟨trivial, fun _ _ o3 => ?_⟩⟩⟩
  obtain ⟨bl1, bl2, bl3, rest, hw⟩ := top_dec w a b t _ rfl o1 o2 o3
  subst hw
  have hc := (top_calc bl1 bl2 bl3 rest a b t).2
  try simp only at hc
  rw [hc]
  exact hdrB_pre _ _ _ _ _ _ _

lemma hd1_ok (w : List BSym) (a b : ℕ) (t : List Bool) :
    hd1.ok (stateA w a b t) ↔
      ∃ bs, w = encB a.bits ++ encB t.length.bits ++ encB b.bits ++ encBits bs := by
  simp only [hd1, GB.seq, bStNum, GB.ofGs]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨bl1, bl2, bl3, rest, hw⟩ := top_dec w a b t _ rfl h1 h2 h3
    subst hw
    have hc := (top_calc bl1 bl2 bl3 rest a b t).2
    try simp only at hc
    rw [hc, hdrB_ok_cl] at h4
    obtain ⟨e1, e3, e2, hp2, hp1⟩ := h4
    rw [map_tkb_eq] at e1 e2 e3
    subst e1 e2 e3
    have hp : List.foldl ps (false, [], 0) (List.map tk rest) =
        (false, (List.foldl ps (false, [], 0) (List.map tk rest)).2.1, 0) := by
      ext <;> simp [hp1, hp2]
    obtain ⟨-, bs, hbs, -⟩ := (parse_iff rest false [] 0 _).1 hp
    exact ⟨bs, by simpa using hbs ▸ rfl⟩
  · rintro ⟨bs, hw⟩
    subst hw
    have hc := (top_calc a.bits t.length.bits b.bits (encBits bs) a b t)
    try simp only at hc
    obtain ⟨⟨o1, o2, o3⟩, hc⟩ := hc
    refine ⟨o1, o2, o3, ?_⟩
    rw [hc, hdrB_ok_cl]
    have hp : (List.foldl ps (false, [], 0) (List.map tk (encBits bs))) = (false, bs.reverse.map tyb, 0) :=
      (parse_iff (encBits bs) false [] 0 _).2 ⟨rfl, bs, by simp, by simp⟩
    simp [HdrCl, hp]

lemma hd1_T (a b : ℕ) (t bs : List Bool) :
    hd1.T (stateA (encB a.bits ++ encB t.length.bits ++ encB b.bits ++ encBits bs) a b t) =
      ZSt (base0 b a) (z0 a t bs) := by
  simp only [hd1, GB.seq, bStNum, GB.ofGs]
  have hc := (top_calc a.bits t.length.bits b.bits (encBits bs) a b t).2
  try simp only at hc
  rw [hc, hdrB_T]

end Stk

end Sec_Ap24

section Sec_Ap25
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma EntR_kr (z1 z' : Z) (h : EntR z1 z') : z1.kr ≠ [] := by
  obtain ⟨r, bit, kr', a, b, ct', -, hk, -⟩ := h
  simp [hk]

lemma StartR_kr (z z1 : Z) (h : StartR z z1) : z1.kr = z.kr := by
  rcases h with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩ <;> rfl

lemma StepD_kr_ne (z z' : Z) (h : StepD z z') : z.kr ≠ [] := by
  obtain ⟨z1, hs, he⟩ := h
  have := EntR_kr z1 z' he
  rwa [StartR_kr z z1 hs] at this

lemma RT_kr_nil (z z' : Z) (hk : z.kr = []) (h : RT z z') : z' = z := by
  cases h with
  | refl => rfl
  | step _ z1 _ hs _ => exact absurd hk (StepD_kr_ne _ _ hs)

lemma StartR_det (z z1 z2 : Z) (h1 : StartR z z1) (h2 : StartR z z2) : z1 = z2 := by
  rcases h1 with ⟨g1, rfl⟩ | ⟨h0, t0, t', ht, rfl⟩ <;> rcases h2 with ⟨g2, rfl⟩ | ⟨h0', t1, t1', ht', rfl⟩
  · rfl
  · exact absurd h0' g1
  · exact absurd h0 g2
  · rw [ht] at ht'; cases ht'; rfl

lemma EntR_det (z1 z' z'' : Z) (h1 : EntR z1 z') (h2 : EntR z1 z'') : z' = z'' := by
  obtain ⟨r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩ := h1
  obtain ⟨r2, bit2, kr2, a2, b2, ct2, hn2, hk2, hct2, rfl⟩ := h2
  have e1 : r = r2 := by omega
  rw [hk] at hk2; cases hk2
  rw [hct] at hct2; cases hct2
  subst e1; rfl

lemma StepD_det (z z' z'' : Z) (h1 : StepD z z') (h2 : StepD z z'') : z' = z'' := by
  obtain ⟨z1, hs, he⟩ := h1
  obtain ⟨z2, hs2, he2⟩ := h2
  have := StartR_det z z1 z2 hs hs2
  subst this
  exact EntR_det _ _ _ he he2

lemma RT_trans {z p q : Z} (h1 : RT z p) (h2 : RT p q) : RT z q := by
  induction h1 with
  | refl => exact h2
  | step z z' z'' hs _ ih => exact RT.step z z' q hs (ih h2)

lemma RT_cmp {z p q : Z} (h1 : RT z p) (h2 : RT z q) : RT p q ∨ RT q p := by
  induction h1 generalizing q with
  | refl => exact Or.inl h2
  | step z z' z'' hs _ ih =>
    cases h2 with
    | refl => exact Or.inr (RT.step _ z' z'' hs ‹_›)
    | step _ z3 _ hs2 h3 =>
      have := StepD_det _ _ _ hs hs2
      subst this
      exact ih h3

def nxt (f bit : Bool) (p : List Bool × List Bool) : List Bool × List Bool :=
  if bit then (if f then (addBits p.1 [true], p.2) else (p.1, addBits p.2 [true])) else p

lemma dNext_eq (z : Z) (bit : Bool) (a b : List Bool) : dNext z bit a b = nxt (tcv z) bit (a, b) := by
  simp [dNext, nxt]

def stepRow (L : List (List Bool × List Bool)) (r : Bool × List Bool) : List (List Bool × List Bool) :=
  List.zipWith (nxt r.1) r.2 L

lemma rowRun0 : ∀ (row : List Bool) (z : Z) (k : List Bool), z.nr = row.length → z.kr = row ++ k →
    z.ct.length = row.length →
    ∃ z2, RT z z2 ∧ z2 = {z with kr := k, nr := 0, ct := [], cd := z.cd ++ List.zipWith (nxt (tcv z)) row z.ct} := by
  intro row
  induction row with
  | nil =>
    intro z k hn hk hc
    refine ⟨z, RT.refl z, ?_⟩
    have : z.ct = [] := List.length_eq_zero_iff.1 (by simpa using hc)
    simp at hn hk
    cases z; simp_all
  | cons bit row' ih =>
    intro z k hn hk hc
    obtain ⟨p, ct', hct⟩ : ∃ p ct', z.ct = p :: ct' := by
      cases h : z.ct with
      | nil => simp [h] at hc
      | cons p ct' => exact ⟨p, ct', rfl⟩
    have hn' : z.nr = row'.length + 1 := by simpa using hn
    let z' : Z := {z with nr := row'.length, kr := row' ++ k, ct := ct', cd := z.cd ++ [dNext z bit p.1 p.2]}
    have hs : StepD z z' :=
      ⟨z, Or.inl ⟨by omega, rfl⟩, row'.length, bit, row' ++ k, p.1, p.2, ct', hn', by simpa using hk, by simpa using hct, rfl⟩
    obtain ⟨z2, hr, he⟩ := ih z' k rfl rfl (by
      have : (p :: ct').length = row'.length + 1 := by rw [← hct]; simpa using hc
      simpa using this)
    refine ⟨z2, RT.step z z' z2 hs hr, ?_⟩
    rw [he]
    simp [z', hct, tcv, dNext_eq, List.zipWith_cons_cons]

lemma rowB (z : Z) (f : Bool) (t' row k : List Bool) (hnr : z.nr = 0) (ht : z.t = f :: t')
    (hkr : z.kr = row ++ k) (hlen : row.length = z.nm) (hct : (z.cd ++ z.ct).length = z.nm)
    (hpos : 0 < z.nm) :
    ∃ z2, RT z z2 ∧ z2 = {z with tc := [f], t := t', kr := k, nr := 0, cd := List.zipWith (nxt f) row (z.cd ++ z.ct), ct := []} := by
  obtain ⟨bit, row', hrow⟩ : ∃ bit row', row = bit :: row' := by
    cases row with
    | nil => simp at hlen; omega
    | cons b r => exact ⟨b, r, rfl⟩
  subst hrow
  obtain ⟨p, ct', hct'⟩ : ∃ p ct', z.cd ++ z.ct = p :: ct' := by
    cases h : z.cd ++ z.ct with
    | nil => simp [h] at hct; omega
    | cons p ct' => exact ⟨p, ct', rfl⟩
  let z1 : Z := {z with tc := [f], t := t', cd := [], ct := z.cd ++ z.ct, nr := z.nm}
  have hn1 : z1.nr = row'.length + 1 := by simp [z1]; simpa using hlen.symm
  let z' : Z := {z1 with nr := row'.length, kr := row' ++ k, ct := ct', cd := [] ++ [dNext z1 bit p.1 p.2]}
  have hs : StepD z z' :=
    ⟨z1, Or.inr ⟨hnr, f, t', ht, rfl⟩, row'.length, bit, row' ++ k, p.1, p.2, ct', hn1,
      by simpa [z1] using hkr, by simpa [z1] using hct', rfl⟩
  obtain ⟨z2, hr, he⟩ := rowRun0 row' z' k rfl rfl (by
    have : (p :: ct').length = row'.length + 1 := by
      rw [← hct']; simp at hlen hct ⊢; omega
    simpa [z'] using this)
  refine ⟨z2, RT.step z z' z2 hs hr, ?_⟩
  rw [he]
  have htc : tcv z' = f := by simp [tcv, z', z1]
  simp [z', z1, hct', dNext_eq, List.zipWith_cons_cons, tcv]

end Stk

end Sec_Ap25

section Sec_Ap26
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma RT_pres {z z' : Z} (h : RT z z') :
    z'.nm = z.nm ∧ z'.a1 = z.a1 ∧ z'.a2 = z.a2 ∧ z'.one = z.one := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl⟩
  | step z z1 z2 hs _ ih =>
    obtain ⟨z0, hS, hE⟩ := hs
    obtain ⟨r, bit, kr', a, b, ct', -, -, -, rfl⟩ := hE
    have : z0.nm = z.nm ∧ z0.a1 = z.a1 ∧ z0.a2 = z.a2 ∧ z0.one = z.one := by
      rcases hS with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := ih
    exact ⟨by simp_all, by simp_all, by simp_all, by simp_all⟩

lemma rowsRun : ∀ (rows : List (Bool × List Bool)) (z : Z) (t' k : List Bool), z.nr = 0 →
    (∀ r ∈ rows, r.2.length = z.nm) → 0 < z.nm → (z.cd ++ z.ct).length = z.nm →
    z.t = rows.map Prod.fst ++ t' → z.kr = rows.flatMap Prod.snd ++ k →
    ∃ z2, RT z z2 ∧ z2.nr = 0 ∧ z2.t = t' ∧ z2.kr = k ∧
      z2.cd ++ z2.ct = rows.foldl stepRow (z.cd ++ z.ct) := by
  intro rows
  induction rows with
  | nil =>
    intro z t' k hn _ _ _ ht hk
    exact ⟨z, RT.refl z, hn, by simpa using ht, by simpa using hk, rfl⟩
  | cons r rows ih =>
    intro z t' k hn hl hpos hlen ht hk
    simp only [List.map_cons, List.cons_append, List.flatMap_cons] at ht hk
    rw [List.append_assoc] at hk
    obtain ⟨z1, hr1, he1⟩ := rowB z r.1 (rows.map Prod.fst ++ t') r.2 (rows.flatMap Prod.snd ++ k) hn ht hk
      (hl r (List.mem_cons_self ..)) hlen hpos
    subst he1
    obtain ⟨z2, hr2, h1, h2, h3, h4⟩ := ih {z with tc := [r.1], t := rows.map Prod.fst ++ t', kr := rows.flatMap Prod.snd ++ k, nr := 0, cd := List.zipWith (nxt r.1) r.2 (z.cd ++ z.ct), ct := []} t' k rfl
      (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) hpos
      (by
        have := hl r (List.mem_cons_self ..)
        simp [this, hlen]) rfl rfl
    refine ⟨z2, RT_trans hr1 hr2, h1, h2, h3, ?_⟩
    rw [h4]
    simp [List.foldl_cons, stepRow]

lemma short (z' : Z) (hk : z'.kr = []) (hn : z'.nr = 0) :
    ∀ (j : ℕ) (z1 : Z), z1.nr = j → 0 < j → RT z1 z' → j ≤ z1.kr.length := by
  intro j
  induction j with
  | zero => intro z1 _ h; omega
  | succ j ih =>
    intro z1 hj _ hr
    cases hr with
    | refl => simp [hn] at hj
    | step _ z1n _ hs hr =>
      obtain ⟨z0, hS, hE⟩ := hs
      have hz0 : z0 = z1 := by
        rcases hS with ⟨-, rfl⟩ | ⟨h0, -⟩
        · rfl
        · omega
      subst hz0
      obtain ⟨r, bit, kr', a, b, ct', hn1, hk1, hct, rfl⟩ := hE
      have hr' : r = j := by omega
      subst hr'
      by_cases h0 : r = 0
      · simp [hk1]; omega
      · have := ih _ rfl (by omega) hr
        simp [hk1]; exact this

lemma rowsConv (z' : Z) (hk' : z'.kr = []) (ht' : z'.t = []) (hn' : z'.nr = 0) :
    ∀ n (z : Z), z.kr.length = n → z.nr = 0 → 0 < z.nm → (z.cd ++ z.ct).length = z.nm → RT z z' →
    ∃ rows : List (Bool × List Bool), (∀ r ∈ rows, r.2.length = z.nm) ∧ z.t = rows.map Prod.fst ∧
      z.kr = rows.flatMap Prod.snd ∧ z'.cd ++ z'.ct = rows.foldl stepRow (z.cd ++ z.ct) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro z hn hnr hpos hlen hr
    by_cases hk : z.kr = []
    · have := RT_kr_nil z z' hk hr
      subst this
      exact ⟨[], by simp, by simpa using ht', by simpa using hk, rfl⟩
    · cases hr with
      | refl => exact absurd hk' hk
      | step _ zn _ hs hr2 =>
        obtain ⟨z1, hS, hE⟩ := hs
        obtain ⟨f, t'', ht⟩ : ∃ f t'', z.t = f :: t'' := by
          rcases hS with ⟨h0, -⟩ | ⟨-, t0, t'', ht, -⟩
          · omega
          · exact ⟨t0, t'', ht⟩
        have hz1 : z1 = {z with tc := [f], t := t'', cd := [], ct := z.cd ++ z.ct, nr := z.nm} := by
          rcases hS with ⟨h0, -⟩ | ⟨-, t0, t2, ht2, rfl⟩
          · omega
          · rw [ht] at ht2; cases ht2; rfl
        have hrr : RT z1 z' := RT.step z1 zn z' ⟨z1, Or.inl ⟨by simp [hz1]; omega, rfl⟩, hE⟩ hr2
        have hsh := short z' hk' hn' z.nm z1 (by simp [hz1]) hpos hrr
        have hkr1 : z1.kr = z.kr := StartR_kr z z1 hS
        have hnm : z.nm ≤ z.kr.length := by rw [← hkr1]; exact hsh
        obtain ⟨z2, hrz, he⟩ := rowB z f t'' (z.kr.take z.nm) (z.kr.drop z.nm) hnr ht
          (by rw [List.take_append_drop]) (by simp; omega) hlen hpos
        have hr3 : RT z2 z' := by
          rcases RT_cmp hrz (RT.step z zn z' ⟨z1, hS, hE⟩ hr2) with h | h
          · exact h
          · have := RT_kr_nil z' z2 hk' h
            rw [this]; exact RT.refl _
        subst he
        obtain ⟨rows', hl', ht2, hk2, hf⟩ := ih (z.kr.drop z.nm).length (by simp; omega)
          {z with tc := [f], t := t'', kr := z.kr.drop z.nm, nr := 0, cd := List.zipWith (nxt f) (z.kr.take z.nm) (z.cd ++ z.ct), ct := []}
          rfl rfl hpos (by simp [hlen]; omega) hr3
        refine ⟨(f, z.kr.take z.nm) :: rows', ?_, ?_, ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.1 hr with rfl | hr
          · simp; omega
          · exact hl' r hr
        · simp only [ht, List.map_cons]; simp only at ht2; rw [ht2]
        · simp only [List.flatMap_cons, List.map_cons]
          simp only at hk2
          rw [← hk2, List.take_append_drop]
        · rw [hf]; simp [List.foldl_cons, stepRow]


lemma rowLoop_iff (a : ℕ) (ha : 0 < a) (t bs : List Bool) (L : List (List Bool × List Bool)) :
    (∃ z', RT (z0 a t bs) z' ∧ z'.kr = [] ∧ z'.t = [] ∧ z'.nr = 0 ∧ L = z'.cd ++ z'.ct) ↔
    ∃ rows : List (Bool × List Bool), (∀ r ∈ rows, r.2.length = a) ∧ t = rows.map Prod.fst ∧
      bs = rows.flatMap Prod.snd ∧ L = rows.foldl stepRow (List.replicate a ([], [])) := by
  constructor
  · rintro ⟨z', hr, hk, ht, hn, rfl⟩
    obtain ⟨rows, h1, h2, h3, h4⟩ := rowsConv z' hk ht hn _ (z0 a t bs) rfl rfl ha (by simp [z0]) hr
    exact ⟨rows, h1, h2, h3, by simpa [z0] using h4⟩
  · rintro ⟨rows, h1, h2, h3, rfl⟩
    obtain ⟨z2, hr, hn, ht, hk, he⟩ := rowsRun rows (z0 a t bs) [] [] rfl h1 ha (by simp [z0])
      (by simpa [z0] using h2) (by simpa [z0] using h3)
    exact ⟨z2, hr, hk, ht, hn, by simpa [z0] using he.symm⟩

end Stk

end Sec_Ap26

section Sec_Ap27
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

/-- a generic "state of the form F a with side condition P a, or BAD" invariant -/
def InvF {α : Type} (F : α → St) (P : α → Prop) (s : St) : Prop :=
  Gi s ∧ (s Reg.BAD ≠ [] ∨ ∃ a, P a ∧ s = F a)

lemma step_inv {α β : Type} (b : GB) (F : α → St) (P : α → Prop) (F2 : β → St) (Q : β → Prop)
    (hF : ∀ a, Gi (F a)) (hB : ∀ a, F a Reg.BAD = []) (hpre : ∀ a, P a → b.pre (F a))
    (hnext : ∀ a, P a → b.ok (F a) → ∃ c, Q c ∧ b.T (F a) = F2 c) (s : St) (h : InvF F P s) :
    InvF F2 Q (b.g s) := by
  refine ⟨b.h.1.2 s h.1, ?_⟩
  rcases h.2 with hb | ⟨a, ha, rfl⟩
  · exact Or.inl (b.h.2.1 _ hb)
  · have hh := b.h.2.2.2 (F a) (hF a) (hpre a ha) (hB a)
    by_cases hb : b.g (F a) Reg.BAD = []
    · right
      have ho := hh.1.1 hb
      obtain ⟨c, hc, he⟩ := hnext a ha ho
      exact ⟨c, hc, by rw [hh.2 ho]; exact he⟩
    · exact Or.inl hb

lemma lrun_Gi (t : (Reg → Option Al) → Bool) (g : St → St) (μ : St → ℕ)
    (hinv : ∀ s, Gi s → t (hd s) = true → Gi (g s))
    (hdec : ∀ s, Gi s → t (hd s) = true → μ (g s) < μ s) (s : St) (h : Gi s) :
    Gi (lrun t g μ s) :=
  lrun_rel Gi t g μ hinv hdec (fun _ s' => Gi s') (fun s hs _ => hs) (fun s _ _ h => h) s h

def chkNf : GB := bBad (isNoneT Reg.IN)

lemma chkNf_pre (s : St) : chkNf.pre s := trivial

lemma chkNf_ok (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    chkNf.ok (YSt base y l) ↔ y.nf ≠ 0 := by
  simp [chkNf, nT_IN]

lemma chkNf_T (base : St) (y : Y) (l : List (List Bool × List Bool)) :
    chkNf.T (YSt base y l) = YSt base y l := rfl

/-- fold loop PSp uniform in the base -/
lemma fold_PSp_ex {body : GB} {E0 : ℕ × ℕ → Y → St} {f : Y → List Bool × List Bool → Y}
    (h : ∀ b, FoldHyp body (E0 b) f) :
    PSp (fun s => ∃ b, JF (E0 b) s) (.loop ltM body.p) (lrun ltM body.g muM) :=
  PSp.loopJ3 ltM (lrun ltM body.g muM) muM (PSp.weaken body.h.1.1 (fun s ⟨_, hs⟩ => hs.1)) muM_le
    (fun s ⟨b, hs⟩ ht => ⟨b, fold_hinv (h b) s hs ht⟩)
    (fun s ⟨b, hs⟩ ht ht2 => fold_hgrow (h b) s hs ht ht2)
    (fun s _ ht => lrun_false ltM body.g muM s ht)
    (fun s ⟨b, hs⟩ ht => ⟨fold_hdec (h b) s hs ht,
      lrun_true (JF (E0 b)) ltM body.g muM (fold_hinv (h b)) (fold_hdec (h b)) s hs ht⟩)

lemma loopD_PSp_ex : PSp (fun s => ∃ b, JD b s) loopD LGD :=
  PSp.loopJ3 ltK LGD muD (PSp.weaken dBody.h.1.1 (fun s ⟨_, hs⟩ => hs.1)) muD_le
    (fun s ⟨b, hs⟩ ht => ⟨b, loopD_hinv b s hs ht⟩)
    (fun s ⟨b, hs⟩ ht ht2 => loopD_hgrow b s hs ht ht2)
    (fun s _ ht => lrun_false ltK dBody.g muD s ht)
    (fun s ⟨b, hs⟩ ht => ⟨loopD_hdec b s hs ht, lrunD_step b s hs ht⟩)


def loopA : Prog := .loop ltM bodyA.p
def loopB : Prog := .loop ltM bodyB.p
def LGA : St → St := lrun ltM bodyA.g muM
def LGB : St → St := lrun ltM bodyB.g muM

def tailC : GB := finB.seq bOut

def progC (tp : Bool) : Prog :=
  .seq stA (.seq hd1.p (.seq loopD (.seq postB.p (.seq loopA (.seq chkNf.p
    (.seq (midB tp).p (.seq loopB tailC.p)))))))

def gC (tp : Bool) (s : St) : St :=
  tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD (hd1.g (gA s))))))))

-- stage state families
def F2 (a : ℕ × ℕ × Z) : St := ZSt (base0 a.2.1 a.1) a.2.2
def P2 (a : ℕ × ℕ × Z) : Prop := a.2.2.nm = a.1 ∧ ZInv a.2.2
def F4 (a : ℕ × ℕ × Y × List (List Bool × List Bool)) : St := YSt (base0 a.2.1 a.1) a.2.2.1 a.2.2.2

lemma F2_Gi (a : ℕ × ℕ × Z) : Gi (F2 a) := ZSt_Gi _ _
lemma F2_BAD (a : ℕ × ℕ × Z) : F2 a Reg.BAD = [] := ZSt_BAD _ _
lemma F4_Gi (a : ℕ × ℕ × Y × List (List Bool × List Bool)) : Gi (F4 a) := Efold_Gi (foldA_hyp (base0 a.2.1 a.1)) a.2.2.1 a.2.2.2
lemma F4_BAD (a : ℕ × ℕ × Y × List (List Bool × List Bool)) : F4 a Reg.BAD = [] := Efold_BAD (foldA_hyp (base0 a.2.1 a.1)) a.2.2.1 a.2.2.2

def Fs (a : ℕ × ℕ × List Bool × List Bool) : St :=
  stateA (encB a.1.bits ++ encB a.2.2.1.length.bits ++ encB a.2.1.bits ++ encBits a.2.2.2) a.1 a.2.1 a.2.2.1

end Stk

end Sec_Ap27

section Sec_Ap28
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

abbrev QL := List (List Bool × List Bool)

def F1 (a : List BSym × ℕ × ℕ × List Bool) : St := stateA a.1 a.2.1 a.2.2.1 a.2.2.2

lemma InvF1 (s : St) : Inv1 s → InvF F1 (fun _ => True) s := by
  rintro ⟨hg, h | ⟨w, a, b, t, rfl⟩⟩
  · exact ⟨hg, Or.inl h⟩
  · exact ⟨hg, Or.inr ⟨(w, a, b, t), trivial, rfl⟩⟩

lemma hd1_inv (s : St) (h : InvF F1 (fun _ => True) s) : InvF F2 P2 (hd1.g s) :=
  step_inv hd1 F1 (fun _ => True) F2 P2 (fun a => stateA_Gi _ _ _ _) (fun a => stateA_BAD _ _ _ _)
    (fun a _ => hd1_pre _ _ _ _)
    (fun a _ ho => by
      obtain ⟨w, a1, b, t⟩ := a
      obtain ⟨bs, hw⟩ := (hd1_ok w a1 b t).1 ho
      subst hw
      refine ⟨(a1, b, z0 a1 t bs), ⟨rfl, ⟨rfl, rfl, rfl⟩, Nat.zero_le _⟩, ?_⟩
      exact hd1_T a1 b t bs) s h

def P3 (a : ℕ × ℕ × Z) : Prop := a.2.2.nm = a.1 ∧ clean a.2.2 ∧ a.2.2.kr = []

lemma F2_JD (s : St) (h : InvF F2 P2 s) : ∃ b, JD b s := by
  rcases h.2 with hb | ⟨a, ha, rfl⟩
  · exact ⟨base0 0 0, h.1, Or.inl hb⟩
  · exact ⟨_, h.1, Or.inr ⟨a.2.2, ha.2, rfl⟩⟩

lemma LGD_Gi (b : St) (s : St) (h : JD b s) : Gi (LGD s) :=
  lrun_rel (JD b) ltK dBody.g muD (loopD_hinv b) (loopD_hdec b) (fun _ s' => Gi s')
    (fun s hs _ => hs.1) (fun s _ _ h => h) s h

lemma LGD_inv (s : St) (h : InvF F2 P2 s) : InvF F2 P3 (LGD s) := by
  rcases h.2 with hb | ⟨a, ha, rfl⟩
  · have hn : ltK (hd s) = false := by
      rw [Bool.eq_false_iff]; intro ht; rw [ltK_iff] at ht; exact hb ht.2
    rw [LGD, lrun_false _ _ _ _ hn]; exact ⟨h.1, Or.inl hb⟩
  · obtain ⟨m, c, z⟩ := a
    have hJ : JD (base0 c m) (F2 (m, c, z)) := ⟨ZSt_Gi _ _, Or.inr ⟨z, ha.2, rfl⟩⟩
    refine ⟨LGD_Gi _ _ hJ, ?_⟩
    rcases LGD_char (base0 c m) z.kr.length z rfl ha.2 with hb | ⟨z', hr, hk, he⟩
    · exact Or.inl hb
    · right
      obtain ⟨e1, e2, e3, e4⟩ := RT_pres hr
      have hnm : z.nm = m := ha.1
      obtain ⟨c1, c2, c3⟩ : z.a1 = [] ∧ z.a2 = [] ∧ z.one = [] := ha.2.1
      refine ⟨(m, c, z'), ⟨by rw [e1]; exact hnm, ⟨by rw [e2]; exact c1, by rw [e3]; exact c2, by rw [e4]; exact c3⟩, hk⟩, ?_⟩
      exact he

def Q4 (a : ℕ × ℕ × Y × QL) : Prop := True

lemma postB_inv (s : St) (h : InvF F2 P3 s) :
    InvF F4 (fun _ => True) (postB.g s) :=
  step_inv postB F2 P3 F4 (fun _ => True) F2_Gi F2_BAD (fun a _ => postB_pre _ _)
    (fun a ha ho => by
      obtain ⟨m, c, z⟩ := a
      obtain ⟨ht, hnr⟩ := (postB_ok _ _).1 ho
      obtain ⟨hnm, ⟨h1, h2, h3⟩, hk⟩ := ha
      refine ⟨(m, c, y0 c, z.cd ++ z.ct), trivial, ?_⟩
      have := postB_T c m z hk ht hnr hnm h1 h2 h3
      exact this) s h

lemma lrun_fold_inv {body : GB} {f : Y → List Bool × List Bool → Y}
    (h : ∀ base, FoldHyp body (YS base) f) (P : ℕ × ℕ × Y × QL → Prop) (s : St) (hs : InvF F4 P s) :
    InvF F4 (fun a => a.2.2.2 = []) (lrun ltM body.g muM s) := by
  rcases hs.2 with hb | ⟨a, ha, rfl⟩
  · have hn : ltM (hd s) = false := by
      rw [Bool.eq_false_iff]; intro ht; rw [ltM_iff] at ht; exact hb ht.2
    rw [lrun_false _ _ _ _ hn]; exact ⟨hs.1, Or.inl hb⟩
  · obtain ⟨m, c, y, l⟩ := a
    have := fold_char (h (base0 c m)) l y
    refine ⟨?_, Or.inr ⟨(m, c, l.foldl f y, []), rfl, ?_⟩⟩
    · rw [show F4 (m, c, y, l) = Efold (YS (base0 c m)) y l from rfl, this]
      exact Efold_Gi (h _) _ _
    · exact this

lemma LGA_inv (P : ℕ × ℕ × Y × QL → Prop) (s : St) (hs : InvF F4 P s) :
    InvF F4 (fun a => a.2.2.2 = []) (LGA s) := lrun_fold_inv foldA_hyp P s hs

lemma LGB_inv (P : ℕ × ℕ × Y × QL → Prop) (s : St) (hs : InvF F4 P s) :
    InvF F4 (fun a => a.2.2.2 = []) (LGB s) := lrun_fold_inv foldB_hyp P s hs

lemma chk_inv (P : ℕ × ℕ × Y × QL → Prop) (s : St) (hs : InvF F4 P s) : InvF F4 P (chkNf.g s) :=
  step_inv chkNf F4 P F4 P F4_Gi F4_BAD (fun a _ => chkNf_pre _)
    (fun a ha _ => ⟨a, ha, rfl⟩) s hs

lemma mid_inv (tp : Bool) (s : St) (hs : InvF F4 (fun a => a.2.2.2 = []) s) :
    InvF F4 (fun _ => True) ((midB tp).g s) :=
  step_inv (midB tp) F4 _ F4 (fun _ => True) F4_Gi F4_BAD (fun a _ => midB_pre _ _)
    (fun a ha _ => by
      obtain ⟨m, c, y, l⟩ := a
      simp only at ha; subst ha
      exact ⟨(m, c, midY tp y, y.cd), trivial, (midB_spec tp _ y).2⟩) s hs

lemma F4_JF (P : ℕ × ℕ × Y × QL → Prop) (s : St) (hs : InvF F4 P s) :
    ∃ b : ℕ × ℕ, JF (fun y => YS (base0 b.2 b.1) y) s := by
  rcases hs.2 with hb | ⟨a, ha, rfl⟩
  · exact ⟨(0, 0), hs.1, Or.inl hb⟩
  · exact ⟨(a.1, a.2.1), hs.1, Or.inr ⟨a.2.2.1, a.2.2.2, rfl⟩⟩

end Stk

end Sec_Ap28

section Sec_Ap29
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma Lb_PSp (P : ℕ × ℕ × Y × QL → Prop) : PSp (InvF F4 P) loopB LGB :=
  PSp.weaken (fold_PSp_ex (E0 := fun b => YS (base0 b.2 b.1)) (fun b => foldB_hyp (base0 b.2 b.1)))
    (fun s hs => F4_JF P s hs)

lemma La_PSp (P : ℕ × ℕ × Y × QL → Prop) : PSp (InvF F4 P) loopA LGA :=
  PSp.weaken (fold_PSp_ex (E0 := fun b => YS (base0 b.2 b.1)) (fun b => foldA_hyp (base0 b.2 b.1)))
    (fun s hs => F4_JF P s hs)

set_option maxHeartbeats 1000000 in
lemma progC_PSp (tp : Bool) : PSp Inv0 (progC tp) (gC tp) := by
  have C1 : PSp (InvF F4 (fun _ => True)) (.seq loopB tailC.p) (fun s => tailC.g (LGB s)) :=
    PSp.seq2 (I1 := InvF F4 (fun _ => True)) (I2 := Gi) (g := LGB) (h := tailC.g)
      (Lb_PSp _) tailC.h.1.1 (fun s hs => (LGB_inv _ s hs).1)
  have C2 : PSp (InvF F4 (fun a => a.2.2.2 = [])) (.seq (midB tp).p (.seq loopB tailC.p))
      (fun s => tailC.g (LGB ((midB tp).g s))) :=
    PSp.seq2 (I1 := InvF F4 (fun a => a.2.2.2 = [])) (I2 := InvF F4 (fun _ => True))
      (g := (midB tp).g) (h := fun s => tailC.g (LGB s))
      (PSp.weaken (midB tp).h.1.1 (fun s hs => hs.1)) C1 (mid_inv tp)
  have C3 : PSp (InvF F4 (fun a => a.2.2.2 = [])) (.seq chkNf.p (.seq (midB tp).p (.seq loopB tailC.p)))
      (fun s => tailC.g (LGB ((midB tp).g (chkNf.g s)))) :=
    PSp.seq2 (I1 := InvF F4 (fun a => a.2.2.2 = [])) (I2 := InvF F4 (fun a => a.2.2.2 = []))
      (g := chkNf.g) (h := fun s => tailC.g (LGB ((midB tp).g s)))
      (PSp.weaken chkNf.h.1.1 (fun s hs => hs.1)) C2 (chk_inv _)
  have C4 : PSp (InvF F4 (fun _ => True))
      (.seq loopA (.seq chkNf.p (.seq (midB tp).p (.seq loopB tailC.p))))
      (fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA s))))) :=
    PSp.seq2 (I1 := InvF F4 (fun _ => True)) (I2 := InvF F4 (fun a => a.2.2.2 = []))
      (g := LGA) (h := fun s => tailC.g (LGB ((midB tp).g (chkNf.g s))))
      (La_PSp _) C3 (LGA_inv _)
  have C5 : PSp (InvF F2 P3)
      (.seq postB.p (.seq loopA (.seq chkNf.p (.seq (midB tp).p (.seq loopB tailC.p)))))
      (fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g s)))))) :=
    PSp.seq2 (I1 := InvF F2 P3) (I2 := InvF F4 (fun _ => True))
      (g := postB.g) (h := fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA s)))))
      (PSp.weaken postB.h.1.1 (fun s hs => hs.1)) C4 postB_inv
  have C6 : PSp (InvF F2 P2)
      (.seq loopD (.seq postB.p (.seq loopA (.seq chkNf.p (.seq (midB tp).p (.seq loopB tailC.p))))))
      (fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD s))))))) :=
    PSp.seq2 (I1 := InvF F2 P2) (I2 := InvF F2 P3)
      (g := LGD) (h := fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g s))))))
      (PSp.weaken loopD_PSp_ex (fun s hs => F2_JD s hs)) C5 LGD_inv
  have C7 : PSp (InvF F1 (fun _ => True))
      (.seq hd1.p (.seq loopD (.seq postB.p (.seq loopA (.seq chkNf.p (.seq (midB tp).p (.seq loopB tailC.p)))))))
      (fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD (hd1.g s)))))))) :=
    PSp.seq2 (I1 := InvF F1 (fun _ => True)) (I2 := InvF F2 P2)
      (g := hd1.g) (h := fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD s)))))))
      (PSp.weaken hd1.h.1.1 (fun s hs => hs.1)) C6 hd1_inv
  have hA : PSp Inv0 stA gA :=
    PSp.weaken (Inv' := Inv0) gs_stA.1.1 (fun s ⟨x, hx⟩ => by subst hx; exact Gi_init x)
  exact PSp.seq2 (I1 := Inv0) (I2 := InvF F1 (fun _ => True)) (g := gA)
    (h := fun s => tailC.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD (hd1.g s))))))))
    hA C7 (fun s hs => by
    obtain ⟨x, rfl⟩ := hs; exact InvF1 _ (gA_inv1 x))

end Stk

end Sec_Ap29

section Sec_Ap30
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

-- sticky lemmas
lemma LGA_sticky (s : St) (h : s Reg.BAD ≠ []) : LGA s Reg.BAD ≠ [] := by
  have : ltM (hd s) = false := by
    rw [Bool.eq_false_iff]; intro ht; rw [ltM_iff] at ht; exact h ht.2
  rw [LGA, lrun_false _ _ _ _ this]; exact h
lemma LGB_sticky (s : St) (h : s Reg.BAD ≠ []) : LGB s Reg.BAD ≠ [] := by
  have : ltM (hd s) = false := by
    rw [Bool.eq_false_iff]; intro ht; rw [ltM_iff] at ht; exact h ht.2
  rw [LGB, lrun_false _ _ _ _ this]; exact h
lemma LGD_sticky (s : St) (h : s Reg.BAD ≠ []) : LGD s Reg.BAD ≠ [] := by
  have : ltK (hd s) = false := by
    rw [Bool.eq_false_iff]; intro ht; rw [ltK_iff] at ht; exact h ht.2
  rw [LGD, lrun_false _ _ _ _ this]; exact h

-- backward predicates
def Rb (s : St) : Prop := finB.g (LGB s) Reg.BAD = []
def Rm (tp : Bool) (s : St) : Prop := Rb ((midB tp).g s)
def Rc (tp : Bool) (s : St) : Prop := Rm tp (chkNf.g s)
def Ra (tp : Bool) (s : St) : Prop := Rc tp (LGA s)
def Rp (tp : Bool) (s : St) : Prop := Ra tp (postB.g s)
def Rd (tp : Bool) (s : St) : Prop := Rp tp (LGD s)
def Rh (tp : Bool) (s : St) : Prop := Rd tp (hd1.g s)
def R0 (tp : Bool) (s : St) : Prop := Rh tp (gA s)

lemma bad_of (g : St → St) (hs : ∀ s, s Reg.BAD ≠ [] → g s Reg.BAD ≠ []) (R : St → Prop)
    (hR : ∀ s, R s → s Reg.BAD = []) : ∀ s, R (g s) → s Reg.BAD = [] := by
  intro s h; by_contra hc; exact hs s hc (hR _ h)

lemma Rb_bad (s : St) (h : Rb s) : s Reg.BAD = [] := by
  by_contra hc; exact finB.h.2.1 _ (LGB_sticky _ hc) h
lemma Rm_bad (tp : Bool) : ∀ s, Rm tp s → s Reg.BAD = [] :=
  bad_of (midB tp).g (fun s hc => (midB tp).h.2.1 s hc) Rb (fun s h => Rb_bad s h)
lemma Rc_bad (tp : Bool) : ∀ s, Rc tp s → s Reg.BAD = [] :=
  bad_of chkNf.g (fun s hc => chkNf.h.2.1 s hc) (Rm tp) (Rm_bad tp)
lemma Ra_bad (tp : Bool) : ∀ s, Ra tp s → s Reg.BAD = [] :=
  bad_of LGA LGA_sticky (Rc tp) (Rc_bad tp)
lemma Rp_bad (tp : Bool) : ∀ s, Rp tp s → s Reg.BAD = [] :=
  bad_of postB.g (fun s hc => postB.h.2.1 s hc) (Ra tp) (Ra_bad tp)
lemma Rd_bad (tp : Bool) : ∀ s, Rd tp s → s Reg.BAD = [] :=
  bad_of LGD LGD_sticky (Rp tp) (Rp_bad tp)
lemma Rh_bad (tp : Bool) : ∀ s, Rh tp s → s Reg.BAD = [] :=
  bad_of hd1.g (fun s hc => hd1.h.2.1 s hc) (Rd tp) (Rd_bad tp)

lemma gb_eval (b : GB) (s : St) (hG : Gi s) (hp : b.pre s) (hB : s Reg.BAD = []) (R : St → Prop)
    (hR : ∀ s, R s → s Reg.BAD = []) : R (b.g s) ↔ b.ok s ∧ R (b.T s) := by
  have hh := b.h.2.2.2 s hG hp hB
  by_cases ho : b.ok s
  · rw [hh.2 ho]; simp [ho]
  · constructor
    · intro h; exact absurd (hh.1.1 (hR _ h)) ho
    · intro h; exact absurd h.1 ho

lemma Rb_YSt (base : St) (y : Y) (l : QL) :
    Rb (YSt base y l) ↔ (l.foldl fB y).kc ≠ 0 ∧ (l.foldl fB y).cnt = 1 := by
  have e : LGB (YSt base y l) = YSt base (l.foldl fB y) [] := fold_char (foldB_hyp base) l y
  unfold Rb
  rw [e]
  have hh := finB.h.2.2.2 (YSt base (l.foldl fB y) []) (YSt_Gi _ _ _) (finB_pre _) (YSt_BAD _ _ _)
  rw [hh.1, finB_ok]

lemma Rm_YSt (tp : Bool) (base : St) (y : Y) :
    Rm tp (YSt base y []) ↔ (y.cd.foldl fB (midY tp y)).kc ≠ 0 ∧ (y.cd.foldl fB (midY tp y)).cnt = 1 := by
  unfold Rm
  rw [gb_eval (midB tp) _ (YSt_Gi _ _ _) (midB_pre _ _) (YSt_BAD _ _ _) _ (fun s h => Rb_bad s h),
    (midB_spec tp base y).2, Rb_YSt]
  simp [(midB_spec tp base y).1]

lemma Rc_YSt (tp : Bool) (base : St) (y : Y) :
    Rc tp (YSt base y []) ↔ y.nf ≠ 0 ∧ Rm tp (YSt base y []) := by
  unfold Rc
  rw [gb_eval chkNf _ (YSt_Gi _ _ _) (chkNf_pre _) (YSt_BAD _ _ _) _ (Rm_bad tp), chkNf_ok, chkNf_T]

lemma Ra_YSt (tp : Bool) (base : St) (y : Y) (l : QL) :
    Ra tp (YSt base y l) ↔ Rc tp (YSt base (l.foldl fA y) []) := by
  have e : LGA (YSt base y l) = YSt base (l.foldl fA y) [] := fold_char (foldA_hyp base) l y
  unfold Ra
  rw [e]

lemma Ra_iff (tp : Bool) (base : St) (y : Y) (l : QL) :
    Ra tp (YSt base y l) ↔ (l.foldl fA y).nf ≠ 0 ∧
      ((l.foldl fA y).cd.foldl fB (midY tp (l.foldl fA y))).kc ≠ 0 ∧
      ((l.foldl fA y).cd.foldl fB (midY tp (l.foldl fA y))).cnt = 1 := by
  rw [Ra_YSt, Rc_YSt, Rm_YSt]

lemma Rp_ZSt (tp : Bool) (c m : ℕ) (z : Z) (hkr : z.kr = []) (hnm : z.nm = m)
    (h1 : z.a1 = []) (h2 : z.a2 = []) (h3 : z.one = []) :
    Rp tp (ZSt (base0 c m) z) ↔ z.t = [] ∧ z.nr = 0 ∧ Ra tp (YSt (base0 c m) (y0 c) (z.cd ++ z.ct)) := by
  unfold Rp
  rw [gb_eval postB _ (ZSt_Gi _ _) (postB_pre _ _) (ZSt_BAD _ _) _ (Ra_bad tp), postB_ok]
  by_cases ho : z.t = [] ∧ z.nr = 0
  · rw [postB_T c m z hkr ho.1 ho.2 hnm h1 h2 h3]; simp [ho]
  · constructor
    · intro h; exact absurd h.1 ho
    · rintro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ ho

lemma LGD_conv (base : St) : ∀ z z' : Z, RT z z' → ZInv z → z'.kr = [] → LGD (ZSt base z) = ZSt base z' := by
  intro z z' hr
  induction hr with
  | refl z =>
    intro _ hk
    apply lrun_false
    rw [← Bool.not_eq_true, ltK_iff]; simp [hk]
  | step z z1 z2 hs hr ih =>
    intro hz hk2
    have hk : z.kr ≠ [] := StepD_kr_ne _ _ hs
    have hj : JD base (ZSt base z) := ⟨ZSt_Gi base z, Or.inr ⟨z, hz, rfl⟩⟩
    have ht : ltK (hd (ZSt base z)) = true := by
      rw [ltK_iff]; exact ⟨by simpa using hk, rfl⟩
    rw [lrunD_step base _ hj ht]
    have hd := dBody_step base z z1 hz.1 hs
    have hh := dBody.h.2.2.2 (ZSt base z) (ZSt_Gi base z) (dBody_pre _) (ZSt_BAD base z)
    rw [hh.2 hd.1, hd.2]
    exact ih (step_num base z z1 hz hs).1 hk2

lemma Rd_ZSt (tp : Bool) (base : St) (z : Z) (hz : ZInv z) :
    Rd tp (ZSt base z) ↔ ∃ z', RT z z' ∧ z'.kr = [] ∧ Rp tp (ZSt base z') := by
  rcases LGD_char base _ z rfl hz with hb | ⟨z', hr, hk, he⟩
  · constructor
    · intro h; exact absurd (Rp_bad tp _ h) hb
    · rintro ⟨z2, hr2, hk2, _⟩
      rw [LGD_conv base z z2 hr2 hz hk2] at hb
      exact absurd (ZSt_BAD _ _) hb
  · unfold Rd; rw [he]
    constructor
    · intro h; exact ⟨z', hr, hk, h⟩
    · rintro ⟨z2, hr2, hk2, h2⟩
      rcases RT_cmp hr hr2 with h | h
      · obtain rfl := RT_kr_nil z' z2 hk h; exact h2
      · obtain rfl := RT_kr_nil z2 z' hk2 h; exact h2

lemma Rh_stateA (tp : Bool) (w : List BSym) (a b : ℕ) (t : List Bool) :
    Rh tp (stateA w a b t) ↔ ∃ bs, w = encB a.bits ++ encB t.length.bits ++ encB b.bits ++ encBits bs ∧
      Rd tp (ZSt (base0 b a) (z0 a t bs)) := by
  unfold Rh
  rw [gb_eval hd1 _ (stateA_Gi _ _ _ _) (hd1_pre _ _ _ _) (stateA_BAD _ _ _ _) _ (Rd_bad tp), hd1_ok]
  constructor
  · rintro ⟨⟨bs, hw⟩, h⟩
    refine ⟨bs, hw, ?_⟩
    subst hw; rw [hd1_T] at h; exact h
  · rintro ⟨bs, hw, h⟩
    refine ⟨⟨bs, hw⟩, ?_⟩
    subst hw; rw [hd1_T]; exact h

def AccY (tp : Bool) (b : ℕ) (L : QL) : Prop :=
  (L.foldl fA (y0 b)).nf ≠ 0 ∧
    ((L.foldl fA (y0 b)).cd.foldl fB (midY tp (L.foldl fA (y0 b)))).kc ≠ 0 ∧
    ((L.foldl fA (y0 b)).cd.foldl fB (midY tp (L.foldl fA (y0 b)))).cnt = 1

def AccC (tp : Bool) (w : List BSym) (a b : ℕ) (t : List Bool) : Prop :=
  ∃ (bs : List Bool) (z' : Z), w = encB a.bits ++ encB t.length.bits ++ encB b.bits ++ encBits bs ∧
    RT (z0 a t bs) z' ∧ z'.kr = [] ∧ z'.t = [] ∧ z'.nr = 0 ∧ AccY tp b (z'.cd ++ z'.ct)

lemma Rh_iff (tp : Bool) (w : List BSym) (a b : ℕ) (t : List Bool) :
    Rh tp (stateA w a b t) ↔ AccC tp w a b t := by
  rw [Rh_stateA]
  constructor
  · rintro ⟨bs, hw, h⟩
    rw [Rd_ZSt tp _ _ ⟨⟨rfl, rfl, rfl⟩, Nat.zero_le _⟩] at h
    obtain ⟨z', hr, hk, h⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := RT_pres hr
    rw [Rp_ZSt tp b a z' hk e1 e2 e3 e4, Ra_iff] at h
    exact ⟨bs, z', hw, hr, hk, h.1, h.2.1, h.2.2⟩
  · rintro ⟨bs, z', hw, hr, hk, ht, hn, h⟩
    refine ⟨bs, hw, ?_⟩
    rw [Rd_ZSt tp _ _ ⟨⟨rfl, rfl, rfl⟩, Nat.zero_le _⟩]
    obtain ⟨e1, e2, e3, e4⟩ := RT_pres hr
    refine ⟨z', hr, hk, ?_⟩
    rw [Rp_ZSt tp b a z' hk e1 e2 e3 e4, Ra_iff]
    exact ⟨ht, hn, h⟩

lemma R0_iff (tp : Bool) (x : List Al) :
    R0 tp (init x) ↔ ∃ w a b t, x = Fm w a b t ∧ AccC tp w a b t := by
  constructor
  · intro h
    have h1 : gA (init x) Reg.BAD = [] := Rh_bad tp _ h
    have hh := gs_stA.2.2.2 (init x) (Gi_init x) (by simp [init])
    obtain ⟨w, a, b, t, hx⟩ := stA_dec x (hh.1.1 h1)
    subst hx
    unfold R0 at h
    rw [gA_Fm, Rh_iff] at h
    exact ⟨w, a, b, t, rfl, h⟩
  · rintro ⟨w, a, b, t, rfl, h⟩
    unfold R0
    rw [gA_Fm, Rh_iff]; exact h

lemma gC_OUT (tp : Bool) (s : St) : gC tp s Reg.OUT ≠ [] ↔ R0 tp s := by
  have e : gC tp s Reg.OUT = outG (finB.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD (hd1.g (gA s))))))))) Reg.OUT := by
    simp only [gC, tailC, GB.seq, bOut, GB.ofGs]
  rw [e, outG_OUT]
  unfold R0 Rh Rd Rp Ra Rc Rm Rb
  by_cases h : finB.g (LGB ((midB tp).g (chkNf.g (LGA (postB.g (LGD (hd1.g (gA s)))))))) Reg.BAD = [] <;> simp [h]

end Stk

end Sec_Ap30

section Sec_Ap31
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

abbrev PP := List Bool × List Bool

def v1 (p : PP) : ℕ := val p.1
def v2 (p : PP) : ℕ := val p.2

def mxv (v : PP → ℕ) (L : List PP) : ℕ := L.foldl (fun a p => max a (v p)) 0
def ctv (v : PP → ℕ) (L : List PP) : ℕ := (L.filter fun p => decide (v p = mxv v L)).length

lemma foldl_max_aux (v : PP → ℕ) (L : List PP) : ∀ a : ℕ,
    a ≤ L.foldl (fun a p => max a (v p)) a ∧ ∀ q ∈ L, v q ≤ L.foldl (fun a p => max a (v p)) a := by
  induction L with
  | nil => intro a; simp
  | cons p L ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (max a (v p))
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro q hq
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact le_trans (le_max_right _ _) h1
    · exact h2 q hq

lemma le_mxv (v : PP → ℕ) (L : List PP) (q : PP) (h : q ∈ L) : v q ≤ mxv v L :=
  (foldl_max_aux v L 0).2 q h

lemma mxv_snoc (v : PP → ℕ) (L : List PP) (p : PP) : mxv v (L ++ [p]) = max (mxv v L) (v p) := by
  simp [mxv, List.foldl_append]

lemma ctv_snoc (v : PP → ℕ) (L : List PP) (p : PP) :
    ctv v (L ++ [p]) = if mxv v L < v p then 1 else if v p < mxv v L then ctv v L else ctv v L + 1 := by
  unfold ctv
  rw [mxv_snoc, List.filter_append]
  by_cases h1 : mxv v L < v p
  · have e : max (mxv v L) (v p) = v p := max_eq_right h1.le
    rw [e, if_pos h1]
    have : List.filter (fun q => decide (v q = v p)) L = [] := by
      rw [List.filter_eq_nil_iff]
      intro q hq
      have := le_mxv v L q hq
      simp; omega
    simp [this]
  · by_cases h2 : v p < mxv v L
    · have e : max (mxv v L) (v p) = mxv v L := max_eq_left h2.le
      rw [e, if_neg h1, if_pos h2]
      simp; omega
    · have e : v p = mxv v L := by omega
      have e2 : max (mxv v L) (v p) = mxv v L := by omega
      rw [e2, if_neg h1, if_neg h2]
      simp [e]

def InvA (c : ℕ) (L : List PP) (y : Y) : Prop :=
  y.cd = L ∧ val y.m1 = mxv v1 L ∧ y.k1 = ctv v1 L ∧ val y.m2 = mxv v2 L ∧ y.k2 = ctv v2 L ∧
  y.kc = c - L.length ∧ (y.nf ≠ 0 ↔ c < L.length) ∧
  (∀ p, L[c]? = some p → val y.ac = val p.1 ∧ val y.bc = val p.2) ∧ y.a1 = [] ∧ y.a2 = []

lemma InvA_nil (c : ℕ) : InvA c [] (y0 c) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩ <;> simp [y0, mxv, ctv, val]

lemma fA_cd (y : Y) (p : PP) : (fA y p).cd = y.cd ++ [p] := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp

lemma fA_m1 (y : Y) (p : PP) : val (fA y p).m1 = max (val y.m1) (val p.1) := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp <;> omega

lemma fA_k1 (y : Y) (p : PP) : (fA y p).k1 = if val y.m1 < val p.1 then 1 else if val p.1 < val y.m1 then y.k1 else y.k1 + 1 := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_m2 (y : Y) (p : PP) : val (fA y p).m2 = max (val y.m2) (val p.2) := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp <;> omega

lemma fA_k2 (y : Y) (p : PP) : (fA y p).k2 = if val y.m2 < val p.2 then 1 else if val p.2 < val y.m2 then y.k2 else y.k2 + 1 := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_kc (y : Y) (p : PP) : (fA y p).kc = if 0 < y.kc then y.kc - 1 else y.kc := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_nf (y : Y) (p : PP) : (fA y p).nf = if 0 < y.kc then y.nf else if y.nf = 0 then 1 else y.nf := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_ac (y : Y) (p : PP) : (fA y p).ac = if 0 < y.kc then y.ac else if y.nf = 0 then p.1 else y.ac := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_bc (y : Y) (p : PP) : (fA y p).bc = if 0 < y.kc then y.bc else if y.nf = 0 then p.2 else y.bc := by
  simp only [fA, capY, maxY1, maxY2, List.append_nil]; split_ifs <;> simp_all

lemma fA_a (y : Y) (p : PP) : (fA y p).a1 = [] ∧ (fA y p).a2 = [] := by
  simp only [fA]; simp

lemma InvA_step (c : ℕ) (L : List PP) (p : PP) (y : Y) (h : InvA c L y) : InvA c (L ++ [p]) (fA y p) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (fA_a y p).1, (fA_a y p).2⟩
  · rw [fA_cd, h1]
  · rw [fA_m1, mxv_snoc, h2]; rfl
  · rw [fA_k1, ctv_snoc, h2, h3]; rfl
  · rw [fA_m2, mxv_snoc, h4]; rfl
  · rw [fA_k2, ctv_snoc, h4, h5]; rfl
  · rw [fA_kc, h6]; simp only [List.length_append, List.length_singleton]; split_ifs <;> omega
  · rw [fA_nf, h6]; simp only [List.length_append, List.length_singleton]
    have := h7
    split_ifs <;> simp_all <;> omega
  · intro q hq
    have hl : c < L.length + 1 ∨ L.length + 1 ≤ c := by omega
    by_cases hc : c < L.length
    · rw [List.getElem?_append_left hc] at hq
      obtain ⟨e1, e2⟩ := h8 q hq
      have hnf : y.nf ≠ 0 := h7.2 hc
      rw [fA_ac, fA_bc, h6]
      have : ¬ (0 < c - L.length) := by omega
      simp [this, hnf, e1, e2]
    · by_cases hc2 : c = L.length
      · subst hc2
        rw [List.getElem?_append_right (le_refl _)] at hq
        simp at hq
        subst hq
        have hnf : y.nf = 0 := by
          by_contra hn; exact absurd (h7.1 hn) (lt_irrefl _)
        rw [fA_ac, fA_bc, h6]
        simp [hnf]
      · rw [List.getElem?_append_right (by omega)] at hq
        obtain ⟨k, hk⟩ : ∃ k, c - L.length = k + 1 := ⟨c - L.length - 1, by omega⟩
        rw [hk] at hq
        simp at hq

lemma InvA_fold (c : ℕ) : ∀ L : List PP, InvA c L (L.foldl fA (y0 c)) := by
  intro L
  induction L using List.reverseRecOn with
  | nil => exact InvA_nil c
  | append_singleton L p ih =>
    rw [List.foldl_append]
    exact InvA_step c L p _ ih

end Stk

end Sec_Ap31

section Sec_Ap32
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma midY_o1 (tp : Bool) (y : Y) : (midY tp y).o1 = decide ((if tp then 1 else y.k1) = 1) := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all

lemma midY_o2 (tp : Bool) (y : Y) : (midY tp y).o2 = decide ((if tp then 1 else y.k2) = 1) := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all

lemma midY_m1 (tp : Bool) (y : Y) : (midY tp y).m1 = y.m1 := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all

lemma midY_m2 (tp : Bool) (y : Y) : (midY tp y).m2 = y.m2 := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all

lemma midY_ac (tp : Bool) (y : Y) : val (midY tp y).ac = val y.ac + val y.bc := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all [val_addBits]

lemma midY_cnt (tp : Bool) (y : Y) : (midY tp y).cnt = 0 := by
  simp only [midY]

lemma midY_kc (tp : Bool) (y : Y) : (midY tp y).kc =
    (if val y.ac = val y.m1 ∧ decide ((if tp then 1 else y.k1) = 1) = true then 1 else 0) +
    (if val y.bc = val y.m2 ∧ decide ((if tp then 1 else y.k2) = 1) = true then 1 else 0) := by
  simp only [midY, flgY1, flgY2, nomCY, nc1, nc2, nc3, nc4]
  split_ifs <;> simp_all

lemma fB_fields (y : Y) (p : PP) : (fB y p).m1 = y.m1 ∧ (fB y p).m2 = y.m2 ∧ (fB y p).o1 = y.o1 ∧
    (fB y p).o2 = y.o2 ∧ (fB y p).ac = y.ac ∧ (fB y p).kc = y.kc := by
  simp only [fB, nomY1, nomY2, cntY]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
lemma fB_m1 (y : Y) (p : PP) : (fB y p).m1 = y.m1 := (fB_fields y p).1
lemma fB_m2 (y : Y) (p : PP) : (fB y p).m2 = y.m2 := (fB_fields y p).2.1
lemma fB_o1 (y : Y) (p : PP) : (fB y p).o1 = y.o1 := (fB_fields y p).2.2.1
lemma fB_o2 (y : Y) (p : PP) : (fB y p).o2 = y.o2 := (fB_fields y p).2.2.2.1
lemma fB_ac (y : Y) (p : PP) : (fB y p).ac = y.ac := (fB_fields y p).2.2.2.2.1
lemma fB_kc (y : Y) (p : PP) : (fB y p).kc = y.kc := (fB_fields y p).2.2.2.2.2

lemma fB_cnt (y : Y) (p : PP) : (fB y p).cnt = y.cnt +
    if ((y.o1 = true ∧ v1 p = val y.m1) ∨ (y.o2 = true ∧ v2 p = val y.m2)) ∧ ¬ (v1 p + v2 p < val y.ac) then 1 else 0 := by
  simp only [fB, nomY1, nomY2, cntY, v1, v2, val_addBits, List.append_nil]
  split_ifs <;> simp_all <;> omega

lemma foldB (L : List PP) : ∀ y : Y,
    (L.foldl fB y).m1 = y.m1 ∧ (L.foldl fB y).m2 = y.m2 ∧ (L.foldl fB y).o1 = y.o1 ∧
    (L.foldl fB y).o2 = y.o2 ∧ (L.foldl fB y).ac = y.ac ∧ (L.foldl fB y).kc = y.kc ∧
    (L.foldl fB y).cnt = y.cnt + (L.filter fun q => decide (((y.o1 = true ∧ v1 q = val y.m1) ∨
      (y.o2 = true ∧ v2 q = val y.m2)) ∧ ¬ (v1 q + v2 q < val y.ac))).length := by
  induction L with
  | nil => intro y; simp
  | cons p L ih =>
    intro y
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (fB y p)
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, fB_m1], by rw [h2, fB_m2], by rw [h3, fB_o1], by rw [h4, fB_o2],
      by rw [h5, fB_ac], by rw [h6, fB_kc], ?_⟩
    rw [h7, fB_cnt, fB_m1, fB_m2, fB_o1, fB_o2, fB_ac]
    rw [List.filter_cons]
    by_cases hq : ((y.o1 = true ∧ v1 p = val y.m1) ∨ (y.o2 = true ∧ v2 p = val y.m2)) ∧ ¬ (v1 p + v2 p < val y.ac)
    · rw [if_pos hq, if_pos (decide_eq_true hq)]; simp; omega
    · rw [if_neg hq, if_neg (by simpa only [decide_eq_true_eq] using hq)]; omega

def nomP (tp : Bool) (L : List PP) (q : PP) : Prop :=
  ((tp = true ∨ ctv v1 L = 1) ∧ v1 q = mxv v1 L) ∨ ((tp = true ∨ ctv v2 L = 1) ∧ v2 q = mxv v2 L)

instance (tp : Bool) (L : List PP) (q : PP) : Decidable (nomP tp L q) := by unfold nomP; infer_instance

def SemY (tp : Bool) (c : ℕ) (L : List PP) : Prop :=
  ∃ p, L[c]? = some p ∧ nomP tp L p ∧
    (L.filter fun q => decide (nomP tp L q ∧ ¬ (v1 q + v2 q < v1 p + v2 p))).length = 1

lemma core (tp : Bool) (c : ℕ) (L : List PP) (y : Y) (p : PP) (hA : InvA c L y) (hp : L[c]? = some p) :
    ((L.foldl fB (midY tp y)).kc ≠ 0 ↔ nomP tp L p) ∧
    (L.foldl fB (midY tp y)).cnt =
      (L.filter fun q => decide (nomP tp L q ∧ ¬ (v1 q + v2 q < v1 p + v2 p))).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hA
  obtain ⟨e1, e2⟩ := h8 p hp
  have O1 : (midY tp y).o1 = true ↔ (tp = true ∨ ctv v1 L = 1) := by
    rw [midY_o1]; cases tp <;> simp [h3]
  have O2 : (midY tp y).o2 = true ↔ (tp = true ∨ ctv v2 L = 1) := by
    rw [midY_o2]; cases tp <;> simp [h5]
  constructor
  · have hkc := (foldB L (midY tp y)).2.2.2.2.2.1
    rw [hkc, midY_kc]
    unfold nomP
    have a1 : val y.ac = v1 p := e1
    have a2 : val y.bc = v2 p := e2
    rw [a1, a2, h2, h4]
    cases tp <;> simp only [h3, h5, Bool.false_eq_true, false_or, if_false, if_true, decide_eq_true_eq, true_or, true_and, and_true] <;>
      split_ifs <;> simp_all <;> exact ⟨fun a b => ‹val p.1 = mxv v1 L → ¬ctv v1 L = 1› b a, fun a b => ‹val p.2 = mxv v2 L → ¬ctv v2 L = 1› b a⟩
  · have hcnt := (foldB L (midY tp y)).2.2.2.2.2.2
    rw [hcnt, midY_cnt, zero_add]
    congr 1
    apply List.filter_congr
    intro q _
    simp only [decide_eq_decide]
    rw [midY_m1, midY_m2, midY_ac, h2, h4, O1, O2]
    have a1 : val y.ac = v1 p := e1
    have a2 : val y.bc = v2 p := e2
    rw [a1, a2]
    unfold nomP
    rfl

lemma AccY_iff (tp : Bool) (c : ℕ) (L : List PP) : AccY tp c L ↔ SemY tp c L := by
  have hA := InvA_fold c L
  unfold AccY SemY
  generalize L.foldl fA (y0 c) = y at *
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hA
  rw [h1]
  constructor
  · rintro ⟨hnf, hk, hc⟩
    have hl : c < L.length := h7.1 hnf
    obtain ⟨p, hp⟩ : ∃ p, L[c]? = some p := ⟨L[c], List.getElem?_eq_getElem hl⟩
    obtain ⟨c1, c2⟩ := core tp c L y p ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hp
    exact ⟨p, hp, c1.1 hk, by rw [← c2]; exact hc⟩
  · rintro ⟨p, hp, hn, hf⟩
    have hl : c < L.length := (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨c1, c2⟩ := core tp c L y p ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hp
    exact ⟨h7.2 hl, c1.2 hn, by rw [c2]; exact hf⟩

end Stk

end Sec_Ap32

section Sec_Ap33
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity
namespace Stk

lemma RT_len {z z' : Z} (h : RT z z') (hl : (z.cd ++ z.ct).length = z.nm) :
    (z'.cd ++ z'.ct).length = z'.nm := by
  induction h with
  | refl => exact hl
  | step z z1 z2 hs _ ih =>
    apply ih
    obtain ⟨z0, hS, hE⟩ := hs
    obtain ⟨r, bit, kr', a, b, ct', hn, hk, hct, rfl⟩ := hE
    have : z0.nm = z.nm ∧ (z0.cd ++ z0.ct).length = (z.cd ++ z.ct).length := by
      rcases hS with ⟨-, rfl⟩ | ⟨-, t0, t', -, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, by simp⟩
    obtain ⟨h1, h2⟩ := this
    have key : (z0.cd ++ z0.ct).length = z0.nm := by rw [h2, h1]; exact hl
    rw [hct] at key
    simp only [List.length_append, List.length_cons, List.length_nil] at key ⊢
    omega

lemma stepRow_len (L : QL) (r : Bool × List Bool) (h : r.2.length = L.length) :
    (stepRow L r).length = L.length := by
  simp [stepRow, h]

lemma stepRow_get (L : QL) (r : Bool × List Bool) (h : r.2.length = L.length) (j : ℕ) (hj : j < L.length)
    (p0 : PP) (hp : L[j]? = some p0) :
    ∃ p, (stepRow L r)[j]? = some p ∧
      v1 p = v1 p0 + (if r.1 = true ∧ r.2.getD j false = true then 1 else 0) ∧
      v2 p = v2 p0 + (if r.1 = false ∧ r.2.getD j false = true then 1 else 0) := by
  have hj2 : j < r.2.length := by omega
  have e : (stepRow L r)[j]? = some (nxt r.1 (r.2[j]) p0) := by
    simp only [stepRow]
    rw [List.getElem?_zipWith]
    simp [hj2, hp]
  refine ⟨_, e, ?_, ?_⟩
  · have : r.2.getD j false = r.2[j] := by simp [List.getD_eq_getElem?_getD, hj2]
    rw [this]
    unfold nxt v1
    cases r.1 <;> cases r.2[j] <;> simp [val_addBits, val]
  · have : r.2.getD j false = r.2[j] := by simp [List.getD_eq_getElem?_getD, hj2]
    rw [this]
    unfold nxt v2
    cases r.1 <;> cases r.2[j] <;> simp [val_addBits, val]

lemma scoreRows (rows : List (Bool × List Bool)) : ∀ (L0 : QL), (∀ r ∈ rows, r.2.length = L0.length) →
    (rows.foldl stepRow L0).length = L0.length ∧
    ∀ j (hj : j < L0.length) (p0 : PP), L0[j]? = some p0 →
      ∃ p, (rows.foldl stepRow L0)[j]? = some p ∧
        v1 p = v1 p0 + (rows.filter fun r => decide (r.1 = true ∧ r.2.getD j false = true)).length ∧
        v2 p = v2 p0 + (rows.filter fun r => decide (r.1 = false ∧ r.2.getD j false = true)).length := by
  induction rows with
  | nil => intro L0 _; exact ⟨rfl, fun j hj p0 hp => ⟨p0, hp, by simp, by simp⟩⟩
  | cons r rows ih =>
    intro L0 hr
    have hr0 : r.2.length = L0.length := hr r (List.mem_cons_self ..)
    have hl1 := stepRow_len L0 r hr0
    obtain ⟨i1, i2⟩ := ih (stepRow L0 r) (by
      intro r' hr'; rw [hl1]; exact hr r' (List.mem_cons_of_mem _ hr'))
    refine ⟨by simp only [List.foldl_cons]; rw [i1, hl1], ?_⟩
    intro j hj p0 hp
    obtain ⟨p1, hp1, e1, e2⟩ := stepRow_get L0 r hr0 j hj p0 hp
    obtain ⟨p, hp', f1, f2⟩ := i2 j (by omega) p1 hp1
    refine ⟨p, by simpa only [List.foldl_cons] using hp', ?_, ?_⟩
    · rw [f1, e1, List.filter_cons]
      by_cases hq : r.1 = true ∧ r.2.getD j false = true
      · rw [if_pos hq, if_pos (decide_eq_true hq)]; simp; omega
      · rw [if_neg hq, if_neg (by simpa only [decide_eq_true_eq] using hq)]; omega
    · rw [f2, e2, List.filter_cons]
      by_cases hq : r.1 = false ∧ r.2.getD j false = true
      · rw [if_pos hq, if_pos (decide_eq_true hq)]; simp; omega
      · rw [if_neg hq, if_neg (by simpa only [decide_eq_true_eq] using hq)]; omega

end Stk

end Sec_Ap33

section Sec_Ap34
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma filter_ofFn_len {α : Type} (k : ℕ) (f : Fin k → α) (p : α → Bool) :
    ((List.ofFn f).filter p).length = (Finset.univ.filter fun i => p (f i) = true).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.filter_cons, Finset.card_filter, Fin.sum_univ_succ]
    rw [← Finset.card_filter]
    have := ih (fun i => f i.succ)
    rw [← this]
    by_cases h : p (f 0) = true
    · simp [h]; omega
    · simp [h]

lemma exists_foldl_max (v : PP → ℕ) (L : List PP) : ∀ a : ℕ,
    L.foldl (fun a p => max a (v p)) a = a ∨ ∃ q ∈ L, v q = L.foldl (fun a p => max a (v p)) a := by
  induction L with
  | nil => intro a; simp
  | cons p L ih =>
    intro a
    simp only [List.foldl_cons]
    rcases ih (max a (v p)) with h | ⟨q, hq, h⟩
    · rw [h]
      rcases max_choice a (v p) with e | e
      · left; exact e
      · right; exact ⟨p, List.mem_cons_self .., by rw [e]⟩
    · right; exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

lemma exists_mxv (v : PP → ℕ) (L : List PP) (hL : L ≠ []) : ∃ q ∈ L, v q = mxv v L := by
  unfold mxv
  rcases exists_foldl_max v L 0 with h | h
  · obtain ⟨q, hq⟩ : ∃ q, q ∈ L := List.exists_mem_of_ne_nil L hL
    refine ⟨q, hq, ?_⟩
    have := le_mxv v L q hq
    unfold mxv at this
    omega
  · exact h

lemma win_iff (v : PP → ℕ) (L : List PP) (s : Fin L.length → ℕ) (hs : ∀ j : Fin L.length, v L[j] = s j)
    (x : Fin L.length) : (∀ y, s y ≤ s x) ↔ s x = mxv v L := by
  constructor
  · intro h
    have hle : s x ≤ mxv v L := by
      rw [← hs]; exact le_mxv v L _ (List.getElem_mem _)
    obtain ⟨q, hq, e⟩ := exists_mxv v L (List.ne_nil_of_length_pos x.pos)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hq
    have h' := h ⟨i, hi⟩
    have h'' : v L[i] = s ⟨i, hi⟩ := hs ⟨i, hi⟩
    omega
  · intro h y
    rw [h, ← hs]
    exact le_mxv v L _ (List.getElem_mem _)

lemma ctv_card (v : PP → ℕ) (L : List PP) (s : Fin L.length → ℕ) (hs : ∀ j : Fin L.length, v L[j] = s j) :
    ctv v L = (Finset.univ.filter fun x : Fin L.length => s x = mxv v L).card := by
  unfold ctv
  generalize mxv v L = mx
  conv_lhs => rw [← List.ofFn_getElem (xs := L)]
  rw [filter_ofFn_len]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  have e : v L[(x : ℕ)] = s x := hs x
  rw [e]

end Stk

end Sec_Ap34

section Sec_Ap35
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma tot_eq {m n : ℕ} (P : Fin n → Finset (Fin m)) (V : Finset (Fin n)) (x : Fin m) :
    approvalScore P Finset.univ x = approvalScore P V x + approvalScore P Vᶜ x := by
  unfold approvalScore
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  exact (Finset.sum_add_sum_compl V _).symm

lemma win_mem (L : List PP) {n : ℕ} (v : PP → ℕ) (P : Fin n → approval.Ballot L.length) (V : Finset (Fin n))
    (hs : ∀ j : Fin L.length, v L[j] = approvalScore P V j) (x : Fin L.length) :
    x ∈ approval.winners L.length n P Finset.univ V ↔ approvalScore P V x = mxv v L := by
  show x ∈ Finset.univ.filter (fun x => ∀ y ∈ (Finset.univ : Finset (Fin L.length)),
    approvalScore P V y ≤ approvalScore P V x) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, forall_const]
  exact win_iff v L (fun j => approvalScore P V j) hs x

lemma win_card (L : List PP) {n : ℕ} (v : PP → ℕ) (P : Fin n → approval.Ballot L.length) (V : Finset (Fin n))
    (hs : ∀ j : Fin L.length, v L[j] = approvalScore P V j) :
    (approval.winners L.length n P Finset.univ V).card = ctv v L := by
  rw [ctv_card v L (fun j => approvalScore P V j) hs]
  congr 1
  ext x
  rw [win_mem L v P V hs x]
  simp

lemma nom_iff (rule : TieRule) (L : List PP) {n : ℕ} (v : PP → ℕ) (P : Fin n → approval.Ballot L.length)
    (V : Finset (Fin n)) (hs : ∀ j : Fin L.length, v L[j] = approvalScore P V j) (j : Fin L.length) :
    j ∈ nominees rule approval P V ↔ ((rule = TieRule.TP ∨ ctv v L = 1) ∧ v L[j] = mxv v L) := by
  have hw := win_mem L v P V hs j
  have hc := win_card L v P V hs
  have e : v L[j] = approvalScore P V j := hs j
  rw [e]
  cases rule
  · -- TE
    simp only [nominees]
    by_cases h : (approval.winners L.length n P Finset.univ V).card = 1
    · rw [if_pos h]
      have : ctv v L = 1 := by rw [← hc]; exact h
      simp [hw, this]
    · rw [if_neg h]
      have : ¬ ctv v L = 1 := by rw [← hc]; exact h
      simp [this]
  · simp only [nominees]
    simp [hw]

lemma filter_len_card (L : List PP) (pr : PP → Bool) :
    (L.filter pr).length = (Finset.univ.filter fun j : Fin L.length => pr L[j] = true).card := by
  conv_lhs => rw [← List.ofFn_getElem (xs := L)]
  rw [filter_ofFn_len]
  rfl

lemma A1x {k : ℕ} (t : Fin k → ℕ) (nm : Fin k → Prop) (c : Fin k) :
    (∀ x, (nm x ∧ ∀ y, nm y → t y ≤ t x) ↔ x = c) ↔ (nm c ∧ ∀ j, nm j → ¬ t j < t c → j = c) := by
  constructor
  · intro h
    have hc := (h c).2 rfl
    refine ⟨hc.1, fun j hj hlt => ?_⟩
    rw [← h]
    exact ⟨hj, fun y hy => by have := hc.2 y hy; omega⟩
  · rintro ⟨hc, h⟩ x
    constructor
    · rintro ⟨hx, hmax⟩
      exact h x hx (by have := hmax c hc; omega)
    · rintro rfl
      refine ⟨hc, fun y hy => ?_⟩
      by_contra hcon
      have := h y hy (by omega)
      subst this
      omega

lemma twoStage_iff (rule : TieRule) (L : List PP) {n : ℕ} (P : Fin n → approval.Ballot L.length)
    (V₁ : Finset (Fin n)) (c : Fin L.length)
    (h1 : ∀ j : Fin L.length, v1 L[j] = approvalScore P V₁ j)
    (h2 : ∀ j : Fin L.length, v2 L[j] = approvalScore P V₁ᶜ j) :
    twoStage rule approval P V₁ = {c} ↔ SemY (decide (rule = TieRule.TP)) c.1 L := by
  have hT : ∀ j : Fin L.length, approvalScore P Finset.univ j = v1 L[j] + v2 L[j] := by
    intro j
    have e1 : v1 L[j] = approvalScore P V₁ j := h1 j
    have e2 : v2 L[j] = approvalScore P V₁ᶜ j := h2 j
    rw [tot_eq P V₁ j, e1, e2]
  have hD : ∀ j : Fin L.length, j ∈ nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ ↔
      nomP (decide (rule = TieRule.TP)) L L[j] := by
    intro j
    rw [Finset.mem_union, nom_iff rule L v1 P V₁ h1 j, nom_iff rule L v2 P V₁ᶜ h2 j]
    unfold nomP
    simp only [decide_eq_true_eq]
  have hmem : ∀ x : Fin L.length, x ∈ twoStage rule approval P V₁ ↔
      nomP (decide (rule = TieRule.TP)) L L[x] ∧ ∀ y : Fin L.length,
        nomP (decide (rule = TieRule.TP)) L L[y] → v1 L[y] + v2 L[y] ≤ v1 L[x] + v2 L[x] := by
    intro x
    show x ∈ (nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ).filter (fun x =>
      ∀ y ∈ (nominees rule approval P V₁ ∪ nominees rule approval P V₁ᶜ),
        approvalScore P Finset.univ y ≤ approvalScore P Finset.univ x) ↔ _
    simp only [Finset.mem_filter, hD, hT]
  rw [Finset.ext_iff]
  simp only [hmem, Finset.mem_singleton]
  have key := A1x (fun j : Fin L.length => v1 L[j] + v2 L[j])
    (fun j => nomP (decide (rule = TieRule.TP)) L L[j]) c
  refine Iff.trans key ?_
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨L[c], List.getElem?_eq_getElem c.2, hn, ?_⟩
    rw [filter_len_card, Finset.card_eq_one]
    refine ⟨c, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_singleton]
    exact ⟨fun ⟨hj, hlt⟩ => h j hj hlt, by rintro rfl; exact ⟨hn, lt_irrefl _⟩⟩
  · rintro ⟨p, hp, hn, hf⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hp
    rw [filter_len_card, Finset.card_eq_one] at hf
    obtain ⟨a, ha⟩ := hf
    have hj := Finset.ext_iff.1 ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_singleton] at hj
    have hca : c = a := (hj c).1 ⟨hn, lt_irrefl _⟩
    refine ⟨hn, fun j hj' hlt' => ?_⟩
    rw [(hj j).1 ⟨hj', hlt'⟩, hca]

end Stk

end Sec_Ap35

section Sec_Ap36
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

def Pf {m n : ℕ} (P : Fin n → approval.Ballot m) (v : Fin n) : Finset (Fin m) := P v

def mkRows (m n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)) : List (Bool × List Bool) :=
  List.ofFn fun v : Fin n => (decide (v ∈ V₁), List.ofFn fun j : Fin m => decide (j ∈ Pf P v))

lemma mkRows_len (m n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)) :
    ∀ r ∈ mkRows m n P V₁, r.2.length = m := by
  intro r hr
  unfold mkRows at hr
  rw [List.mem_ofFn] at hr
  obtain ⟨i, rfl⟩ := hr
  simp

lemma rows_exists (m : ℕ) (rows : List (Bool × List Bool)) (hr : ∀ r ∈ rows, r.2.length = m) :
    ∃ (n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)), rows = mkRows m n P V₁ := by
  refine ⟨rows.length, fun v => (Finset.univ.filter fun j : Fin m => rows[v].2.getD j false = true),
    Finset.univ.filter fun v : Fin rows.length => rows[v].1 = true, ?_⟩
  apply List.ext_getElem
  · simp [mkRows]
  · intro i h1 h2
    have hl : rows[i].2.length = m := hr _ (List.getElem_mem h1)
    simp only [mkRows, List.getElem_ofFn]
    refine Prod.ext (by simp) ?_
    apply List.ext_getElem
    · simp [hl]
    · intro j hj1 hj2
      simp [Pf, List.getD_eq_getElem?_getD, hl, hj1]

lemma getD_ofFn_dec {m : ℕ} (g : Fin m → Bool) (j : Fin m) : (List.ofFn g).getD j false = g j := by
  simp [List.getD_eq_getElem?_getD]

def foldL (m n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)) : QL :=
  (mkRows m n P V₁).foldl stepRow (List.replicate m ([], []))

lemma scores_mkRows (m n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)) :
    (foldL m n P V₁).length = m ∧ ∀ j : Fin m, ∃ p, (foldL m n P V₁)[j.1]? = some p ∧
      v1 p = approvalScore P V₁ j ∧ v2 p = approvalScore P V₁ᶜ j := by
  obtain ⟨hl, hs⟩ := scoreRows (mkRows m n P V₁) (List.replicate m ([], []))
    (by intro r hr; rw [List.length_replicate]; exact mkRows_len m n P V₁ r hr)
  refine ⟨by simpa [foldL] using hl, fun j => ?_⟩
  obtain ⟨p, hp, e1, e2⟩ := hs j.1 (by simp) ([], []) (by simp)
  refine ⟨p, hp, ?_, ?_⟩
  · rw [e1]
    simp only [v1, val, zero_add]
    unfold mkRows
    rw [filter_ofFn_len]
    unfold approvalScore
    congr 1
    ext v
    simp [Pf, getD_ofFn_dec]
    intro _
    exact (decide_eq_true_iff (p := j ∈ Pf P v))
  · rw [e2]
    simp only [v2, val, zero_add]
    unfold mkRows
    rw [filter_ofFn_len]
    unfold approvalScore
    congr 1
    ext v
    simp [Pf, getD_ofFn_dec]
    intro _
    exact (decide_eq_true_iff (p := j ∈ Pf P v))

lemma twoStage_iff2 (rule : TieRule) (m n : ℕ) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n))
    (c : Fin m) :
    twoStage rule approval P V₁ = {c} ↔ SemY (decide (rule = TieRule.TP)) c.1 (foldL m n P V₁) := by
  obtain ⟨hl, hs⟩ := scores_mkRows m n P V₁
  generalize foldL m n P V₁ = L at *
  subst hl
  have key : ∀ j : Fin L.length, v1 L[j] = approvalScore P V₁ j ∧ v2 L[j] = approvalScore P V₁ᶜ j := by
    intro j
    obtain ⟨p, hp, e1, e2⟩ := hs j
    rw [List.getElem?_eq_getElem j.2] at hp
    have : L[j.1] = p := Option.some.inj hp
    have h' : L[j] = p := this
    rw [h']
    exact ⟨e1, e2⟩
  exact twoStage_iff rule L P V₁ c (fun j => (key j).1) (fun j => (key j).2)

end Stk

end Sec_Ap36

section Sec_Ap37
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma poly_of_prog' (p : Prog) (g : St → St) (hp : PSp Inv0 p g) :
    ∃ k, ∀ x : List Al, ∃ s n, n ≤ x.length ^ k + k ∧
      p.Exec (fun j => if j = Reg.IN then x else []) s n ∧ s = g (init x) := by
  obtain ⟨d, hd⟩ := hp
  obtain ⟨k, hk⟩ := polynomial_absorb (2 ^ d) d 0
  refine ⟨k, fun x => ?_⟩
  obtain ⟨n, hn, ex⟩ := hd (init x) ⟨x, rfl⟩
  refine ⟨g (init x), n, ?_, ex, rfl⟩
  rw [S_init] at hn
  have h1 := hk x.length
  have h2 : (x.length + 2) ^ d ≤ 2 ^ d * (x.length + 1) ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d
  omega

theorem mem_P_of_prog' (p : Prog) (g : St → St) (hp : PSp Inv0 p g) (L : Lang Al)
    (hL : ∀ x, x ∈ L ↔ g (init x) Reg.OUT ≠ []) : L ∈ P Al := by
  have hpoly : PolyTimeComputable (fun x : List Al => g (init x) Reg.OUT) := by
    obtain ⟨k, hk⟩ := poly_of_prog' p g hp
    refine stack_program_polytime p Reg.IN Reg.OUT _ k (fun x => ?_)
    obtain ⟨s, n, hn, ex, hs⟩ := hk x
    exact ⟨s, n, hn, ex, by rw [hs]⟩
  refine mem_P_of_polyReducible L {w : List Al | w ≠ []} ⟨_, hpoly, fun x => ?_⟩ (neLang_mem_P Al)
  rw [hL]; rfl

def RelC (tp : Bool) (w : List BSym) (y : List BSym) : Prop :=
  ∃ a b t, y = List.replicate a BSym.sep ++ List.replicate b BSym.minus ++ t.map bsb ∧ AccC tp w a b t

lemma checkLangC_iff (tp : Bool) (x : List Al) :
    x ∈ checkLang (RelC tp) ↔ R0 tp (init x) := by
  rw [R0_iff]
  constructor
  · rintro ⟨w, y, ⟨a, b, t, hy, hok⟩, hx⟩
    refine ⟨w, a, b, t, ?_, hok⟩
    rw [hx, hy, fm_eq]
  · rintro ⟨w, a, b, t, hx, hok⟩
    refine ⟨w, _, ⟨a, b, t, rfl, hok⟩, ?_⟩
    rw [hx, fm_eq]

theorem checkLangC_mem_P (tp : Bool) : checkLang (RelC tp) ∈ P Al := by
  refine mem_P_of_prog' (progC tp) (gC tp) (progC_PSp tp) _ (fun x => ?_)
  rw [gC_OUT, checkLangC_iff]

end Stk

end Sec_Ap37

section Sec_Ap38
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

lemma encB_len (l : List Bool) : (encB l).length = l.length + 1 := by simp [encB]

lemma encBits_len_ge : ∀ bs : List Bool, bs.length ≤ (encBits bs).length
  | [] => by simp
  | b :: bs => by
    have ih := encBits_len_ge bs
    rw [encBits_cons]
    cases b <;> simp <;> omega

lemma flatMap_snd_len (m : ℕ) : ∀ rows : List (Bool × List Bool), (∀ r ∈ rows, r.2.length = m) →
    (rows.flatMap Prod.snd).length = rows.length * m
  | [], _ => by simp
  | r :: rows, h => by
    have h1 : r.2.length = m := h r (List.mem_cons_self ..)
    have ih := flatMap_snd_len m rows (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih, h1]
    ring

lemma code_eq (m n : ℕ) (c : Fin m) (P : Fin n → approval.Ballot m) (V₁ : Finset (Fin n)) :
    electionCode approval c P = encB m.bits ++ encB n.bits ++ encB c.1.bits ++
      encBits ((mkRows m n P V₁).flatMap Prod.snd) := by
  unfold electionCode
  rw [encNats, List.flatMap_append]
  have h1 : List.flatMap encNat [m, n, c.1] = encB m.bits ++ encB n.bits ++ encB c.1.bits := by
    simp [encNat_eq]
  rw [h1]
  congr 1
  rw [← encNats_bits]
  unfold encNats
  congr 1
  unfold mkRows
  rw [List.flatMap_def, List.map_ofFn, List.map_flatten, List.map_ofFn]
  congr 2
  funext v
  simp [approval, approvalCode, Pf, List.map_ofFn]
  funext x
  show (if x ∈ Pf P v then 1 else 0) = if decide (x ∈ Pf P v) = true then 1 else 0
  simp

end Stk

end Sec_Ap38

section Sec_Ap39
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

theorem acc_bwd (rule : TieRule) (w : List BSym) (a b : ℕ) (t : List Bool)
    (h : AccC (decide (rule = TieRule.TP)) w a b t) : w ∈ ccLang rule approval := by
  obtain ⟨bs, z', hw, hr, hk, ht, hn, hacc⟩ := h
  have hsem := (AccY_iff _ _ _).1 hacc
  obtain ⟨p, hp, -⟩ := hsem
  have hL : (z'.cd ++ z'.ct).length = a := by
    have h1 := RT_len hr (by simp [z0])
    rw [h1]
    exact (RT_pres hr).1
  have hb : b < a := by
    have := (List.getElem?_eq_some_iff.1 hp).1
    omega
  have ha : 0 < a := by omega
  obtain ⟨rows, hrl, ht', hbs, hLr⟩ := (rowLoop_iff a ha t bs _).1 ⟨z', hr, hk, ht, hn, rfl⟩
  obtain ⟨n, P, V₁, hrows⟩ := rows_exists a rows hrl
  subst hrows
  have hsem' : SemY (decide (rule = TieRule.TP)) b (foldL a n P V₁) := by
    have h2 := hacc
    rw [hLr] at h2
    exact (AccY_iff _ _ _).1 h2
  refine ⟨a, n, ⟨b, hb⟩, P, ⟨V₁, (twoStage_iff2 rule a n P V₁ ⟨b, hb⟩).2 hsem'⟩, ?_⟩
  rw [code_eq a n ⟨b, hb⟩ P V₁, hw, ht', hbs]
  simp [mkRows]

lemma n0_m1 (rule : TieRule) (m : ℕ) (c : Fin m) (P : Fin 0 → approval.Ballot m) (V₁ : Finset (Fin 0))
    (hV : twoStage rule approval P V₁ = {c}) : m = 1 := by
  have hs : ∀ (U : Finset (Fin 0)) (x : Fin m), approvalScore P U x = 0 := by
    intro U x
    have : U = ∅ := Finset.eq_empty_of_isEmpty U
    subst this
    simp [approvalScore]
  have hw : ∀ (D : Finset (Fin m)) (U : Finset (Fin 0)), approval.winners m 0 P D U = D := by
    intro D U
    show D.filter (fun x => ∀ y ∈ D, approvalScore P U y ≤ approvalScore P U x) = D
    apply Finset.filter_true_of_mem
    intro x _ y _
    rw [hs U x, hs U y]
  unfold twoStage nominees at hV
  rw [hw] at hV
  cases rule
  · simp only [hw] at hV
    by_contra hm
    simp [hm] at hV
  · simp only [hw] at hV
    have := congrArg Finset.card hV
    simpa using this

end Stk

end Sec_Ap39

section Sec_Ap40
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV
namespace Stk

theorem acc_fwd (rule : TieRule) (w : List BSym) (h : w ∈ ccLang rule approval) :
    ∃ y, y.length ≤ w.length ^ 2 ∧ RelC (decide (rule = TieRule.TP)) w y := by
  obtain ⟨m, n, c, P, ⟨V₁, hV⟩, hw⟩ := h
  have hm : 0 < m := c.pos
  have hsem := (twoStage_iff2 rule m n P V₁ c).1 hV
  obtain ⟨z', hr, hk, ht, hn, hL⟩ := (rowLoop_iff m hm ((mkRows m n P V₁).map Prod.fst)
    ((mkRows m n P V₁).flatMap Prod.snd) (foldL m n P V₁)).2
    ⟨mkRows m n P V₁, mkRows_len m n P V₁, rfl, rfl, rfl⟩
  have htl : ((mkRows m n P V₁).map Prod.fst).length = n := by simp [mkRows]
  have hbl : ((mkRows m n P V₁).flatMap Prod.snd).length = n * m := by
    rw [flatMap_snd_len m _ (mkRows_len m n P V₁)]
    simp [mkRows]
  have hwe : w = encB m.bits ++ encB ((mkRows m n P V₁).map Prod.fst).length.bits ++ encB c.1.bits ++
      encBits ((mkRows m n P V₁).flatMap Prod.snd) := by
    rw [hw, code_eq m n c P V₁, htl]
  have hacc : AccC (decide (rule = TieRule.TP)) w m c.1 ((mkRows m n P V₁).map Prod.fst) :=
    ⟨_, z', hwe, hr, hk, ht, hn, (AccY_iff _ _ _).2 (by rw [← hL]; exact hsem)⟩
  refine ⟨_, ?_, ⟨m, c.1, _, rfl, hacc⟩⟩
  simp only [List.length_append, List.length_replicate, List.length_map]
  have hW : w.length = (m.bits.length + 1) + (n.bits.length + 1) + (c.1.bits.length + 1) +
      (encBits ((mkRows m n P V₁).flatMap Prod.snd)).length := by
    rw [hwe]; simp only [List.length_append, encB_len, htl]
  have hge := encBits_len_ge ((mkRows m n P V₁).flatMap Prod.snd)
  rw [hbl] at hge
  have hcm : c.1 < m := c.2
  have hlen : (mkRows m n P V₁).length = n := by simp [mkRows]
  rw [hlen]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    have h1 := n0_m1 rule m c P V₁ hV
    subst h1
    have : c.1 = 0 := by omega
    rw [this]
    have h3 : 3 ≤ w.length := by omega
    nlinarith
  · have h1 : m ≤ n * m := Nat.le_mul_of_pos_left m hn0
    have h2 : n ≤ n * m := Nat.le_mul_of_pos_right n hm
    have h3 : 3 ≤ w.length := by omega
    nlinarith

end Stk

end Sec_Ap40

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity HHRControl.PV

theorem solution (rule : TieRule) : ccLang rule approval ∈ NP BSym := by
  refine ⟨BSym, inferInstance, ⟨BSym.zero⟩, Stk.RelC (decide (rule = TieRule.TP)), 2,
    Stk.checkLangC_mem_P _, fun w => ⟨fun h => Stk.acc_fwd rule w h, fun ⟨y, _, hy⟩ => ?_⟩⟩
  obtain ⟨a, b, t, -, hacc⟩ := hy
  exact Stk.acc_bwd rule w a b t hacc
