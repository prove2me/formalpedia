-- Prove2me | solution 1 for IntConeFPT.lemma_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-26T09:38:29.814618+00:00
-- url     : https://prove2.me/submissions/c30ab5d1-269f-44a3-8281-38b1bf77d9e8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation
import Theorems.Thm_IntConeFPT_lemma_5
import Theorems.Thm_IntConeFPT_runsWithin_chain
import Theorems.Thm_IntConeFPT_runsWithin_thread
import Theorems.Thm_IntConeFPT_lemma_6_prep_writer
import Theorems.Thm_IntConeFPT_lemma_6_round_writer

set_option autoImplicit false

open Turing OnlineCRS.Combine IntConeFPT Function

/- Stack volume accounting and QueryVM adapted from Prove2Me submission
   70c7eb16-aa64-45fc-9619-d6fd621972a7 / Sol_IntConeFPT_threshold_bisection_machine.lean (Apache-2.0). -/
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
  Turing.FinTM2.kDecidableEq

namespace IntConeFPT.Lemma6Proof

/-! ### 1. Output length bound for arbitrary `FinTM2` and `QueryVM` -/

section TM2Infrastructure

private def pushes {K : Type*} {Γ : K → Type*} {Λ σ : Type*} :
    TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

private def volume {K : Type*} {Γ : K → Type*} [Fintype K] (s : (k : K) → List (Γ k)) : ℕ :=
  ∑ k, (s k).length

private lemma length_update {K : Type*} {Γ : K → Type*} [DecidableEq K]
    (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

private lemma volume_update {K : Type*} {Γ : K → Type*} [Fintype K] [DecidableEq K]
    (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

private lemma stepAux_volume {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    [Fintype K] [DecidableEq K] (q : TM2.Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek _ _ q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load _ q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto _ => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

private noncomputable def tmGrowth (tm : FinTM2) : ℕ := ∑ l, pushes (tm.m l)

private lemma step_volume (tm : FinTM2) {a b : tm.Cfg} (h : tm.step a = some b) :
    volume b.stk ≤ volume a.stk + tmGrowth tm := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, tmGrowth]
      refine (stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

private lemma iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      volume b.stk ≤ volume a.stk + m * tmGrowth tm
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none =>
          rw [hprev] at h
          dsimp [flip] at h
          contradiction
      | some c =>
          rw [hprev] at h
          change tm.step c = some b at h
          have ih := iterate_volume tm m a c hprev
          have hs := step_volume tm h
          have hmul : (m + 1) * tmGrowth tm = m * tmGrowth tm + tmGrowth tm := Nat.succ_mul _ _
          rw [hmul]
          omega

private lemma volume_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    volume (initList tm s).stk = s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk; simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma volume_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    volume (haltList tm s).stk = s.length := by
  classical
  unfold volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk; simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma tm2_output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tmGrowth tm := by
  have hvol := iterate_volume tm h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [volume_initList, volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end TM2Infrastructure

namespace QueryVM
noncomputable section
abbrev Key (M : Machine) (R : Type) := M.tm.K ⊕ R
abbrev G (M : Machine) (R : Type) : Key M R → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Sym
abbrev Lab (M : Machine) (R : Type) (PC : Type) := PC ⊕ (PC × (M.tm.Λ ⊕ Unit))
abbrev St (M : Machine) := M.tm.σ × Option Sym
variable {R PC : Type} [DecidableEq R]
abbrev Code (M : Machine) (R PC : Type) := TM2.Stmt (G M R) (Lab M R PC) (St M)

def pack (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) :
    ∀ k, List (G M R k)
  | .inl k => s k
  | .inr r => b r

lemma upd (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) (k : M.tm.K)
    (v : List (M.tm.Γ k)) :
    update (pack M s b) (.inl k) v = pack M (update s k v) b := by
  funext i; cases i with
  | inr _ => simp [pack]
  | inl i =>
      by_cases h : i = k
      · subst i; simp [pack]
      · simp [pack, update, h]

lemma tmp (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) (i : R) (v : List Sym) :
    update (pack M s b) (.inr i) v = pack M s (update b i v) := by
  funext j; cases j with
  | inl _ => simp [pack]
  | inr j =>
      by_cases h : j = i
      · subst j; simp [pack]
      · simp [pack, update, h]

def tr (M : Machine) (ret : PC) : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → Code M R PC
  | .push k f q => .push (.inl k) (fun s => f s.1) (tr M ret q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (tr M ret q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (tr M ret q)
  | .load f q => .load (fun s => (f s.1, s.2)) (tr M ret q)
  | .branch f q r => .branch (fun s => f s.1) (tr M ret q) (tr M ret r)
  | .goto f => .goto (fun s => .inr (ret, .inl (f s.1)))
  | .halt => .goto (fun _ => .inr (ret, .inr ()))

def loc (M : Machine) (ret : PC) : Option M.tm.Λ → Option (Lab M R PC)
  | none => some (.inr (ret, .inr ()))
  | some l => some (.inr (ret, .inl l))

def liftCfg (M : Machine) (ret : PC) (c : M.tm.Cfg) (b : R → List Sym) :
    TM2.Cfg (G M R) (Lab M R PC) (St M) :=
  ⟨loc M ret c.l, (c.var, none), pack M c.stk b⟩

lemma trStep (M : Machine) (ret : PC) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ)
    (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) :
    TM2.stepAux (tr M ret q) (v, none) (pack M s b) =
      liftCfg M ret (TM2.stepAux q v s) b := by
  induction q generalizing v s with
  | push _ _ _ ih => simpa only [tr, TM2.stepAux, upd, pack] using ih _ _
  | peek _ _ _ ih => exact ih _ _
  | pop _ _ _ ih => simp only [tr, TM2.stepAux, upd]; exact ih _ _
  | load _ _ ih => exact ih _ _
  | branch f _ _ ih jh => cases h : f v <;> simp [tr, TM2.stepAux, h, ih, jh]
  | goto _ => rfl
  | halt => rfl

abbrev Word := List OnlineCRS.Combine.Sym
abbrev Mem (R : Type) := R → Word

inductive Cmd (R : Type)
  | put (r : R) (w : Word)
  | drop (r : R)
  | drain (r : R) (f : R → Sym → Word)
  | call
  | seq (a b : Cmd R)
  | cond (r : R) (p : Option Sym → Bool) (a b : Cmd R)
  | loop (r : R) (p : Option Sym → Bool) (a : Cmd R)

def drained (s : Mem R) (r : R) (f : R → Sym → Word) : Mem R :=
  fun j => if j = r then [] else (s r).reverse.flatMap (f j) ++ s j

inductive Eval (M : Machine) (port : R) : Cmd R → Mem R → Mem R → ℕ → Prop
  | put (s r w) : Eval M port (.put r w) s (update s r (w ++ s r)) 1
  | drop (s r) : Eval M port (.drop r) s (update s r (s r).tail) 1
  | drain (s r f) : Eval M port (.drain r f) s (drained s r f) ((s r).length + 1)
  | call (s : Mem R) (x y : Word) (n : ℕ) (hx : s port = x.reverse)
      (hr : Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some (y.map M.outputAlphabet.invFun)) n)) :
      Eval M port .call s (update s port y.reverse) (x.length + n + y.length + 2)
  | seq {a b s t u h k} : Eval M port a s t h → Eval M port b t u k →
      Eval M port (.seq a b) s u (h + k)
  | yes {r p a b s t h} : p (s r).head? = true → Eval M port a s t h →
      Eval M port (.cond r p a b) s t (1 + h)
  | no {r p a b s t h} : p (s r).head? = false → Eval M port b s t h →
      Eval M port (.cond r p a b) s t (1 + h)
  | stop {r p a s} : p (s r).head? = false → Eval M port (.loop r p a) s s 1
  | more {r p a s t u h k} : p (s r).head? = true → Eval M port a s t h →
      Eval M port (.loop r p a) t u k → Eval M port (.loop r p a) s u (1 + h + k)
  | mono {a s t h k} : Eval M port a s t h → h ≤ k → Eval M port a s t k

def Pos : Cmd R → Type
  | .seq a b => Pos a ⊕ Pos b
  | .cond _ _ a b => Option (Pos a ⊕ Pos b)
  | .loop _ _ a => Option (Pos a)
  | _ => Unit

instance posFin (c : Cmd R) : Fintype (Pos c) := by
  induction c <;> dsimp [Pos] <;> infer_instance

def entry : (c : Cmd R) → Pos c
  | .seq a _ => .inl (entry a)
  | .loop .. | .cond .. => none
  | .put .. | .drop .. | .drain .. | .call => ()

inductive Ins (R Q : Type) where
  | put (r : R) (w : Word) (k : Q)
  | drop (r : R) (k : Q)
  | drain (r : R) (f : R → Sym → Word) (k : Q)
  | branch (r : R) (f : Option Sym → Q)
  | call (k : Q)
  | halt

def asm : (c : Cmd R) → (Pos c → PC) → PC → Pos c → Ins R PC
  | .put r w, _, k, _ => .put r w k
  | .drop r, _, k, _ => .drop r k
  | .drain r f, _, k, _ => .drain r f k
  | .call, _, k, _ => .call k
  | .seq a b, g, k, .inl j => asm a (g ∘ Sum.inl) (g (.inr (entry b))) j
  | .seq a b, g, k, .inr j => asm b (g ∘ Sum.inr) k j
  | .cond r p a b, g, _, none =>
      .branch r (fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
  | .cond _ _ a _, g, k, some (.inl i) => asm a (fun i => g (some (.inl i))) k i
  | .cond _ _ _ b, g, k, some (.inr i) => asm b (fun i => g (some (.inr i))) k i
  | .loop r p a, g, k, none => .branch r (fun o => if p o then g (some (entry a)) else k)
  | .loop _ _ a, g, _, some i => asm a (g ∘ some) (g none) i

def pushWord {M : Machine} (k : R) (w : Word) (q : Code M R PC) : Code M R PC :=
  w.reverse.foldr (fun s q => .push (.inr k) (fun _ => s) q) q

lemma pushWord_aux {M : Machine} (k : R) (w : Word) (q : Code M R PC) v h s :
    TM2.stepAux (pushWord k w q) v (pack M h s) =
      TM2.stepAux q v (pack M h (update s k (w ++ s k))) := by
  have aux (xs : Word) (s : Mem R) :
      TM2.stepAux (xs.foldr (fun a q => TM2.Stmt.push (.inr k) (fun _ => a) q) q) v
        (pack M h s) =
        TM2.stepAux q v (pack M h (update s k (xs.reverse ++ s k))) := by
    induction xs generalizing s with
    | nil => simp
    | cons a xs ih =>
        simp only [List.foldr_cons, TM2.stepAux, tmp, pack, ih, update_self, update_idem]
        simp
  simpa [pushWord] using aux w.reverse s

def pushAll {M : Machine} (ks : List R) (f : R → Word) (q : Code M R PC) :=
  ks.foldr (fun k q => pushWord k (f k) q) q

lemma pushAll_aux {M : Machine} (ks : List R) (f : R → Word) (q : Code M R PC) v h s
    (hn : ks.Nodup) :
    TM2.stepAux (pushAll ks f q) v (pack M h s) =
      TM2.stepAux q v (pack M h fun i => if i ∈ ks then f i ++ s i else s i) := by
  induction ks generalizing s with
  | nil => simp [pushAll]
  | cons k ks ih =>
      rw [show pushAll (k :: ks) f q = pushWord k (f k) (pushAll ks f q) from rfl, pushWord_aux,
        ih _ (List.nodup_cons.mp hn).2]
      congr 2; funext i
      by_cases he : i = k
      · subst i; simp [(List.nodup_cons.mp hn).1]
      · simp [he, update_of_ne he]

def stopAt {M : Machine} (k : PC) : Code M R PC :=
  .load (fun _ => (M.tm.initialState, none)) (.goto (fun _ => .inl k))

def onSym {M : Machine} (f : Sym → Code M R PC) : Code M R PC :=
  .branch (fun v => decide (v.2 = some 0)) (f 0)
    (.branch (fun v => decide (v.2 = some 1)) (f 1)
      (.branch (fun v => decide (v.2 = some 2)) (f 2) (f 3)))

lemma onSym_aux {M : Machine} (f : Sym → Code M R PC) (sym : Sym) s :
    TM2.stepAux (onSym f) (M.tm.initialState, some sym) s =
      TM2.stepAux (f sym) (M.tm.initialState, some sym) s := by fin_cases sym <;> rfl

variable [Fintype R]

noncomputable def program (M : Machine) (port : R) (pg : PC → Ins R PC) :
    Lab M R PC → Code M R PC
  | .inr (ret, .inl l) => tr M ret (M.tm.m l)
  | .inr (ret, .inr ()) =>
      .pop (.inl M.tm.k₁) (fun _ o => (M.tm.initialState, o.map M.outputAlphabet))
        (.branch (fun v => v.2.isSome)
          (.push (.inr port) (fun v => v.2.getD 0)
            (.load (fun _ => (M.tm.initialState, none)) (.goto (fun _ => .inr (ret, .inr ())))))
          (stopAt ret))
  | .inl i =>
      match pg i with
      | .halt => .halt
      | .put r w k => pushWord r w (stopAt k)
      | .drop r k => .pop (.inr r) (fun s _ => s) (stopAt k)
      | .branch r f => .peek (.inr r) (fun s o => (s.1, o)) (.goto (fun v => .inl (f v.2)))
      | .drain r f k =>
          .pop (.inr r) (fun s o => (s.1, o)) (.branch (fun v => v.2.isSome)
            (onSym (fun a => pushAll Finset.univ.toList (fun j => if j = r then [] else f j a)
              (stopAt i)))
            (stopAt k))
      | .call k =>
          .pop (.inr port) (fun s o => (s.1, o)) (.branch (fun v => v.2.isSome)
            (.push (.inl M.tm.k₀) (fun v => M.inputAlphabet.symm (v.2.getD 0)) (stopAt i))
            (.load (fun _ => (M.tm.initialState, none))
              (.goto (fun _ => .inr (k, .inl M.tm.main)))))

noncomputable def code (M : Machine) (port : R) (pg : PC → Ins R PC) : Lab M R PC → Code M R PC
  | .inl i =>
      match pg i with
      | .branch r f => .peek (.inr r) (fun s o => (s.1, o))
          (.branch (fun v => v.2.isSome) (onSym fun a => stopAt (f (some a))) (stopAt (f none)))
      | _ => program M port pg (.inl i)
  | .inr k => program M port pg (.inr k)

abbrev Cfg (M : Machine) (R PC : Type) := TM2.Cfg (G M R) (Lab M R PC) (St M)

def cfg (M : Machine) (i : PC) (s : Mem R) : Cfg M R PC :=
  ⟨some (.inl i), (M.tm.initialState, none), pack M (fun _ => []) s⟩

def Reach {α : Type} (f : α → Option α) (n : ℕ) (u v : α) :=
  ∃ k ≤ n, (flip Option.bind f)^[k] (some u) = some v

namespace Reach
variable {α : Type} {f : α → Option α} {a b c : α} {h k : ℕ}
theorem refl : Reach f 0 a a := ⟨0, le_rfl, rfl⟩
theorem one (he : f a = some b) : Reach f 1 a b := ⟨1, le_rfl, he⟩
theorem trans (x : Reach f h a b) (y : Reach f k b c) : Reach f (h + k) a c := by
  obtain ⟨h', hl, he⟩ := x; obtain ⟨k', kl, ke⟩ := y
  exact ⟨k' + h', by omega, by rw [Function.iterate_add_apply, he, ke]⟩
theorem mono (x : Reach f h a b) (hl : h ≤ k) : Reach f k a b := by
  obtain ⟨t, ht, he⟩ := x; exact ⟨t, ht.trans hl, he⟩
end Reach

abbrev step (M : Machine) (port : R) (pg : PC → Ins R PC) := TM2.step (code M port pg)

private lemma br {M : Machine} {port : R} {pg : PC → Ins R PC} {i k f}
    (he : pg i = .branch k f) (s : Mem R) :
    Reach (step M port pg) 1 (cfg M i s) (cfg M (f (s k).head?) s) := by
  apply Reach.one
  cases h : (s k).head? with
  | none => simp [cfg, step, code, he, TM2.step, TM2.stepAux, pack, h, stopAt]
  | some a => simp [cfg, step, code, he, TM2.step, TM2.stepAux, pack, h, onSym_aux, stopAt]

private lemma bulk {M : Machine} {port : R} {pg : PC → Ins R PC} {i r f k}
    (he : pg i = .drain r f k) (s : Mem R) :
    Reach (step M port pg) ((s r).length + 1) (cfg M i s) (cfg M k (drained s r f)) := by
  generalize hx : s r = xs
  induction xs generalizing s with
  | nil =>
      apply Reach.one
      have eq : update s r [] = drained s r f := by funext j; simp [drained, hx, update_apply]
      simp [cfg, code, step, program, he, TM2.step, TM2.stepAux, pack, hx, tmp, stopAt, eq]
  | cons a xs ih =>
      let t := fun j => if j = r then xs else f j a ++ s j
      have h1 : step M port pg (cfg M i s) = some (cfg M i t) := by
        simp only [cfg, step, TM2.step, code, he, program, TM2.stepAux, pack, hx, List.head?_cons,
          List.tail_cons, Option.isSome_some, Bool.cond_true, tmp, onSym_aux,
          pushAll_aux _ _ _ _ _ _ Finset.univ.nodup_toList, Finset.mem_toList, Finset.mem_univ,
          if_true, stopAt]
        congr 3; funext j; by_cases h : j = r <;> simp_all [t, update]
      have h2 := ih t (by simp [t])
      have eq : drained t r f = drained s r f := by
        funext j; by_cases h : j = r <;>
          simp [drained, t, h, hx, List.flatMap_append, List.append_assoc]
      rw [eq] at h2
      exact ((Reach.one h1).trans h2).mono (by simp; omega)

private abbrev io (M : Machine) (k : M.tm.K) (w : List (M.tm.Γ k)) : ∀ j, List (M.tm.Γ j) :=
  update (fun _ => []) k w

private lemma io_init (M : Machine) w : (initList M.tm w).stk = io M M.tm.k₀ w := by
  funext k; by_cases h : k = M.tm.k₀
  · subst k; simp [initList, io]
  · simp [h, initList, io, update]

private lemma io_halt (M : Machine) w : (haltList M.tm w).stk = io M M.tm.k₁ w := by
  funext k; by_cases h : k = M.tm.k₁
  · subst k; simp [haltList, io]
  · simp [h, haltList, io, update]

private def cc (M : Machine) (l : Lab M R PC) (s : Mem R) (j : M.tm.K) (w : List (M.tm.Γ j)) :
    Cfg M R PC := ⟨some l, (M.tm.initialState, none), pack M (io M j w) s⟩

private lemma load_call (M : Machine) (port : R) (pg : PC → Ins R PC) {i k} (he : pg i = .call k)
    (s : Mem R) (x w : Word) :
    Reach (step M port pg) (x.length + 1)
      (cc M (.inl i) (update s port x) M.tm.k₀ (w.map M.inputAlphabet.symm))
      (liftCfg M k (initList M.tm ((x.reverse ++ w).map M.inputAlphabet.symm)) (update s port [])) := by
  induction x generalizing w with
  | nil =>
      apply Reach.one
      simp [cc, step, code, program, he, TM2.step, TM2.stepAux, pack, tmp, update_idem, stopAt,
        liftCfg, loc, io_init] <;> exact ⟨rfl, rfl⟩
  | cons a x ih =>
      have h1 : step M port pg (cc M (.inl i) (update s port (a :: x)) M.tm.k₀
          (w.map M.inputAlphabet.symm)) =
          some (cc M (.inl i) (update s port x) M.tm.k₀ ((a :: w).map M.inputAlphabet.symm)) := by
        simp [cc, step, code, program, he, TM2.step, TM2.stepAux, pack, tmp, upd, io, update_idem,
          stopAt] <;> rfl
      have hh := (Reach.one h1).trans (ih (a :: w))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hh

private lemma unload (M : Machine) (port : R) (pg : PC → Ins R PC) (k) (s : Mem R) (y w : Word) :
    Reach (step M port pg) (y.length + 1)
      (cc M (.inr (k, .inr ())) (update s port w) M.tm.k₁ (y.map M.outputAlphabet.symm))
      (cfg M k (update s port (y.reverse ++ w))) := by
  induction y generalizing w with
  | nil =>
      apply Reach.one
      have hh : io M M.tm.k₁ [] = fun _ => [] := by
        funext j; by_cases h : j = M.tm.k₁ <;> simp_all [io]
      simp [cc, step, code, program, TM2.step, TM2.stepAux, pack, upd, io, update_idem, stopAt,
        cfg, hh] <;> rfl
  | cons a y ih =>
      have h1 : step M port pg (cc M (.inr (k, .inr ())) (update s port w) M.tm.k₁
          ((a :: y).map M.outputAlphabet.symm)) =
          some (cc M (.inr (k, .inr ())) (update s port (a :: w)) M.tm.k₁
            (y.map M.outputAlphabet.symm)) := by
        simp [cc, step, code, program, TM2.step, TM2.stepAux, pack, upd, tmp, io,
          update_idem] <;> rfl
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using (Reach.one h1).trans (ih (a :: w))

private lemma sim_oracle (M : Machine) (port : R) (pg : PC → Ins R PC) (k : PC) (s : Mem R)
    (n : ℕ) (c d : M.tm.Cfg) (hr : (flip Option.bind M.tm.step)^[n] (some c) = some d) :
    Reach (step M port pg) n (liftCfg M k c s) (liftCfg M k d s) := by
  induction n generalizing c with
  | zero => have he : c = d := Option.some.inj hr; subst c; exact Reach.refl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hr
      rcases c with ⟨l, v, os⟩
      cases l with
      | none =>
          have hh : ∀ n, (flip Option.bind M.tm.step)^[n] none = none := by
            intro n; induction n with
            | zero => rfl
            | succ n ih => rw [Function.iterate_succ_apply]; exact ih
          change (flip Option.bind M.tm.step)^[n] none = some d at hr
          rw [hh] at hr; contradiction
      | some l =>
          let t := TM2.stepAux (M.tm.m l) v os
          have hstep : step M port pg (liftCfg M k ⟨some l, v, os⟩ s) =
              some (liftCfg M k t s) :=
            congrArg some (trStep M k _ v os s)
          exact ((Reach.one hstep).trans (ih t hr)).mono (by omega)

private lemma invoke {M : Machine} {port : R} {pg : PC → Ins R PC} {i k} (he : pg i = .call k)
    (s : Mem R) (x y : Word) n (hx : s port = x.reverse)
    (hr : TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
      (some (y.map M.outputAlphabet.invFun)) n) :
    Reach (step M port pg) (x.length + n + y.length + 2) (cfg M i s)
      (cfg M k (update s port y.reverse)) := by
  have l := load_call M port pg he s x.reverse []
  have o := sim_oracle M port pg k (update s port []) hr.steps _ _ hr.evals_in_steps
  have u := unload M port pg k s y []
  have h1 : cfg M i s = cc M (.inl i) (update s port x.reverse) M.tm.k₀ [] := by
    rw [← hx, update_eq_self]
    have he : io M M.tm.k₀ [] = fun _ => [] := by
      funext j; by_cases h : j = M.tm.k₀ <;> simp_all [io]
    simp [cfg, cc, he]
  have h2 : liftCfg M k (haltList M.tm (y.map M.outputAlphabet.invFun)) (update s port []) =
      cc M (.inr (k, .inr ())) (update s port []) M.tm.k₁ (y.map M.outputAlphabet.symm) := by
    simp [liftCfg, cc, io_halt, loc]; exact ⟨rfl, rfl⟩
  rw [h1]
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, List.map_nil] at l u
  rw [← h2] at u
  exact ((l.trans (o.mono hr.steps_le_m)).trans u).mono (by omega)

theorem sound {M : Machine} {port : R} {c : Cmd R} {s t n} (h : Eval M port c s t n)
    (pg : PC → Ins R PC) (g : Pos c → PC) (k : PC) (sub : ∀ j, pg (g j) = asm c g k j) :
    Reach (step M port pg) n (cfg M (g (entry c)) s) (cfg M k t) := by
  induction h generalizing k with
  | put s r w =>
      apply Reach.one
      change some (TM2.stepAux (code M port pg (.inl (g ()))) _ _) = _
      have h : pg (g ()) = .put r w k := sub ()
      simp [code, program, h, pushWord_aux, stopAt, TM2.stepAux, cfg]
  | drop s r =>
      apply Reach.one
      change some (TM2.stepAux (code M port pg (.inl (g ()))) _ _) = _
      have h : pg (g ()) = .drop r k := sub ()
      simp [code, program, h, tmp, pack, stopAt, TM2.stepAux, cfg]
  | drain _ _ _ => exact bulk (sub ()) _
  | call _ _ _ _ hx hr => exact invoke (sub ()) _ _ _ _ hx hr.some
  | seq _ _ ih jh =>
      exact (ih (g ∘ Sum.inl) _ (fun j => sub (.inl j))).trans
        (jh (g ∘ Sum.inr) k (fun j => sub (.inr j)))
  | @yes r p a b s t n hp _ ih =>
      have branch := br (M := M) (port := port) (pg := pg) (i := g none) (k := r)
        (f := fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
        (sub none) s
      simp only [hp, if_true] at branch
      exact branch.trans (ih (fun j => g (some (.inl j))) k (fun j => sub (some (.inl j))))
  | @no r p a b s t n hp _ ih =>
      have branch := br (M := M) (port := port) (pg := pg) (i := g none) (k := r)
        (f := fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
        (sub none) s
      simp only [hp, Bool.false_eq_true, if_false] at branch
      exact branch.trans (ih (fun j => g (some (.inr j))) k (fun j => sub (some (.inr j))))
  | @stop r p a s hn =>
      have branch := br (M := M) (port := port) (pg := pg) (i := g none) (k := r)
        (f := fun o => if p o then g (some (entry a)) else k) (sub none) s
      simp only [hn, Bool.false_eq_true, if_false] at branch; exact branch
  | @more r p a s t u h j hp _ _ ih jh =>
      have branch := br (M := M) (port := port) (pg := pg) (i := g none) (k := r)
        (f := fun o => if p o then g (some (entry a)) else k) (sub none) s
      simp only [hp, if_true] at branch
      exact (branch.trans (ih (g ∘ some) (g none) (fun j => sub (some j)))).trans (jh g k sub)
  | mono _ hl ih => exact (ih g k sub).mono hl

def pgm (c : Cmd R) : Option (Pos c) → Ins R (Option (Pos c))
  | none => .halt
  | some j => asm c some none j

noncomputable abbrev compiled (M : Machine) (port input output : R) (c : Cmd R) : Machine where
  tm :=
    { K := Key M R, k₀ := .inr input, k₁ := .inr output, Γ := G M R,
      Λ := Lab M R (Option (Pos c)), main := .inl (some (entry c)), σ := St M,
      initialState := (M.tm.initialState, none), m := code M port (pgm c) }
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

def singleWord (i : R) (x : Word) : Mem R := update (fun _ => []) i x

theorem compile_run {M : Machine} {port i o : R} {c : Cmd R} {x y n}
    (h : Eval M port c (singleWord i x) (singleWord o y) n) :
    RunsWithin (compiled M port i o c) x y ((n + 1 : ℕ) : ℝ) := by
  let W := compiled M port i o c
  have hinit : initList W.tm (x.map W.inputAlphabet.invFun) =
      cfg M (PC := Option (Pos c)) (some (entry c)) (singleWord i x) := by
    apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, funext fun j => ?_⟩
    rcases j with _ | b
    · simp [initList, W, compiled, pack]
    · by_cases he : b = i
      · subst b; simp [initList, W, compiled, pack, singleWord, Equiv.refl]
      · simp [initList, W, compiled, pack, singleWord, update, he]
  have hstop : W.tm.step (cfg M (PC := Option (Pos c)) none (singleWord o y)) =
      some (haltList W.tm (y.map W.outputAlphabet.invFun)) := by
    change some (TM2.stepAux (code M port (pgm c) (.inl none)) _ _) = _
    apply congrArg some; apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl, rfl, funext fun j => ?_⟩
    rcases j with _ | b
    · simp [haltList, W, compiled, pack, code, pgm, program, TM2.stepAux]
    · by_cases he : b = o
      · subst b; simp [haltList, W, compiled, pack, code, pgm, program, TM2.stepAux, singleWord,
          Equiv.refl]
      · simp [haltList, W, compiled, pack, code, pgm, program, TM2.stepAux, singleWord, update, he]
  have hrun := sound h (pgm c) some none (fun _ => rfl)
  obtain ⟨k, hk, hr⟩ := hrun.trans (Reach.one hstop)
  exact ⟨n + 1, le_rfl, ⟨⟨⟨k, hinit ▸ hr⟩, hk⟩⟩⟩

end
end QueryVM

/-! ### 2. Zero-vs-positive branching wrapper on `n` -/

section BranchZero

private lemma encNat_zero : encNat 0 = [] := by rfl

private lemma encNat_mem_bit {n : ℕ} {s : Sym} (hs : s ∈ encNat n) : s = 0 ∨ s = 1 := by
  simp only [encNat, List.mem_map] at hs
  rcases hs with ⟨b, _, rfl⟩
  cases b <;> decide

private lemma encNat_ne_nil_of_pos {n : ℕ} (hn : 1 ≤ n) : encNat n ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m : Num, (m : ℕ) = n := ⟨n, Num.to_of_nat n⟩
  simp only [encNat, Computability.encodeNat, Num.of_to_nat]
  cases m with
  | zero => simp at hn
  | pos p => cases p <;> simp [Computability.encodeNum, Computability.encodePosNum]

private lemma list_ends_three_append {l₁ l₂ : List Sym}
    (h : l₂.reverse.head? = some 3) :
    (l₁ ++ l₂).reverse.head? = some 3 := by
  rw [List.reverse_append]
  cases hrev : l₂.reverse with
  | nil => simp [hrev] at h
  | cons a tl => simp [hrev] at h; subst h; simp

private lemma encVec_ends_three {k : ℕ} (hk : 1 ≤ k) (w : Fin k → ℚ) :
    (encVec w).reverse.head? = some 3 := by
  unfold encVec
  have hne : (List.finRange k) ≠ [] := by
    cases k with
    | zero => omega
    | succ k' => simp [List.finRange]
  have hsplit : ∃ l₀ last, List.finRange k = l₀ ++ [last] :=
    ⟨(List.finRange k).dropLast, (List.finRange k).getLast hne,
      (List.dropLast_append_getLast hne).symm⟩
  rcases hsplit with ⟨l₀, last, hfl⟩
  rw [hfl, List.flatMap_append]
  refine list_ends_three_append ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.head?_cons]

private lemma encIntVec_ends_three {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℤ) :
    (encIntVec z).reverse.head? = some 3 := by
  unfold encIntVec
  have hne : (List.finRange d) ≠ [] := by
    cases d with
    | zero => omega
    | succ d' => simp [List.finRange]
  have hsplit : ∃ l₀ last, List.finRange d = l₀ ++ [last] :=
    ⟨(List.finRange d).dropLast, (List.finRange d).getLast hne,
      (List.dropLast_append_getLast hne).symm⟩
  rcases hsplit with ⟨l₀, last, hfl⟩
  rw [hfl, List.flatMap_append]
  refine list_ends_three_append ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.head?_cons]

private lemma lemma6_prefix_ends_three (I : Instance) (hI : I.Valid)
    (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) :
    (encLocal I t r ++ encIntVec z ++ encVec w).reverse.head? = some 3 := by
  by_cases hk : I.k = 0
  · have hfr : List.finRange I.k = [] := List.length_eq_zero_iff.mp (by simp [hk])
    have hw : encVec w = [] := by simp [encVec, hfr]
    rw [hw, List.append_nil]
    exact list_ends_three_append (encIntVec_ends_three hI.one_le_d z)
  · have hk1 : 1 ≤ I.k := Nat.pos_of_ne_zero hk
    exact list_ends_three_append (encVec_ends_three hk1 w)

open QueryVM in
private noncomputable def branchProg : Cmd (Fin 2) :=
  .seq (.drain 0 (fun j a => if j = (1 : Fin 2) then [a] else []))
    (.seq (.drop 1)
      (.cond 1 (fun o => decide (o = some (3 : Sym)))
        (.seq (.drain 1 (fun _ _ => [])) (.put 0 [3]))
        (.seq (.put 1 [3])
          (.seq .call (.drain 1 (fun j a => if j = (0 : Fin 2) then [a] else []))))))

open QueryVM in
private noncomputable def branchZeroMachine (M : Machine) : Machine :=
  compiled M (1 : Fin 2) 0 0 branchProg

open QueryVM in
private lemma branchZeroMachine_zero (M : Machine) (p : List Sym)
    (hp : p.reverse.head? = some 3) :
    RunsWithin (branchZeroMachine M) (p ++ [3]) (encCert (d := 0) (k := 0) [])
      ((2 * (p ++ [3]).length + 10 : ℕ) : ℝ) := by
  have hcert : encCert (d := 0) (k := 0) [] = [3] := by
    simp [encCert, encNat_zero]
  rw [hcert]
  let inp := p ++ [3]
  let s₀ := singleWord (0 : Fin 2) inp
  let s₁ : Mem (Fin 2) := ![ [], inp.reverse ]
  let s₂ : Mem (Fin 2) := ![ [], p.reverse ]
  let s₃ : Mem (Fin 2) := ![ [], [] ]
  let s₄ : Mem (Fin 2) := ![ [3], [] ]
  have hs₁ : drained s₀ (0 : Fin 2) (fun j a => if j = (1 : Fin 2) then [a] else []) = s₁ := by
    funext j; fin_cases j <;> simp [drained, s₀, s₁, singleWord, update, List.flatMap_singleton] <;> rfl
  have hs₂ : update s₁ (1 : Fin 2) (s₁ 1).tail = s₂ := by
    funext j; fin_cases j
    · simp [s₁, s₂, update]
    · simp [s₁, s₂, inp, update]
  have hs₃ : drained s₂ (1 : Fin 2) (fun _ _ => []) = s₃ := by
    funext j; fin_cases j <;> simp [drained, s₂, s₃]
  have hs₄ : update s₃ (0 : Fin 2) ([3] ++ s₃ 0) = s₄ := by
    funext j; fin_cases j <;> simp [s₃, s₄, update]
  have hs₄' : s₄ = singleWord (0 : Fin 2) [3] := by
    funext j; fin_cases j <;> simp [s₄, singleWord, update]
  have e₁ : Eval M 1 (.drain 0 (fun j a => if j = (1 : Fin 2) then [a] else [])) s₀ s₁ (inp.length + 1) := by
    rw [← hs₁]; exact Eval.drain s₀ 0 _
  have e₂ : Eval M 1 (.drop 1) s₁ s₂ 1 := by
    rw [← hs₂]; exact Eval.drop s₁ 1
  have e₃ : Eval M 1 (.drain 1 (fun _ _ => [])) s₂ s₃ (p.reverse.length + 1) := by
    rw [← hs₃]; exact Eval.drain s₂ 1 _
  have e₄ : Eval M 1 (.put 0 [3]) s₃ s₄ 1 := by
    rw [← hs₄]; exact Eval.put s₃ 0 [3]
  have e₃₄ := Eval.seq e₃ e₄
  have hcond := Eval.yes (r := (1 : Fin 2)) (p := fun o => decide (o = some (3 : Sym)))
    (a := .seq (.drain 1 (fun _ _ => [])) (.put 0 [3]))
    (b := .seq (.put 1 [3]) (.seq .call (.drain 1 (fun j a => if j = (0 : Fin 2) then [a] else []))))
    (by simp [s₂, hp]) e₃₄
  have eall := Eval.seq e₁ (Eval.seq e₂ hcond)
  rw [hs₄'] at eall
  refine compile_run (Eval.mono eall ?_)
  simp [inp, List.length_reverse]
  omega

open QueryVM in
private lemma branchZeroMachine_pos (M : Machine) (p : List Sym) {n : ℕ} (hn : 1 ≤ n)
    (out : List Sym) {T : ℝ}
    (hM : RunsWithin M (p ++ encNat n ++ [3]) out T) :
    ∃ m : ℕ, (m : ℝ) ≤ 2 * (p ++ encNat n ++ [3]).length + T + 2 * out.length + 10 ∧
      Nonempty (TM2OutputsInTime (branchZeroMachine M).tm
        ((p ++ encNat n ++ [3]).map (branchZeroMachine M).inputAlphabet.invFun)
        (some (out.map (branchZeroMachine M).outputAlphabet.invFun)) m) := by
  obtain ⟨m_M, hm_M, ⟨hmrun⟩⟩ := hM
  let inp := p ++ encNat n ++ [3]
  let q := p ++ encNat n
  have hq_rev : ∃ a tl, q.reverse = a :: tl ∧ a ≠ 3 := by
    have hne := encNat_ne_nil_of_pos hn
    cases hrev : (encNat n).reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
    | cons a tl =>
        have ha_mem : a ∈ encNat n := List.mem_reverse.mp (hrev ▸ List.mem_cons_self)
        have ha_ne : a ≠ 3 := by
          rcases encNat_mem_bit ha_mem with rfl | rfl <;> decide
        refine ⟨a, tl ++ p.reverse, ?_, ha_ne⟩
        simp [q, List.reverse_append, hrev]
  rcases hq_rev with ⟨a, tl, hqrev, ha_ne⟩
  let s₀ := singleWord (0 : Fin 2) inp
  let s₁ : Mem (Fin 2) := ![ [], inp.reverse ]
  let s₂ : Mem (Fin 2) := ![ [], q.reverse ]
  let s₃ : Mem (Fin 2) := ![ [], inp.reverse ]
  let s₄ : Mem (Fin 2) := ![ [], out.reverse ]
  let s₅ : Mem (Fin 2) := ![ out, [] ]
  have hs₁ : drained s₀ (0 : Fin 2) (fun j a => if j = (1 : Fin 2) then [a] else []) = s₁ := by
    funext j; fin_cases j <;> simp [drained, s₀, s₁, singleWord, update, List.flatMap_singleton] <;> rfl
  have hs₂ : update s₁ (1 : Fin 2) (s₁ 1).tail = s₂ := by
    funext j; fin_cases j
    · simp [s₁, s₂, update]
    · simp [s₁, s₂, inp, q, update]
  have hs₃ : update s₂ (1 : Fin 2) ([3] ++ s₂ 1) = s₃ := by
    funext j; fin_cases j
    · simp [s₂, s₃, update]
    · simp [s₂, s₃, inp, q, update]
  have hs₄ : update s₃ (1 : Fin 2) out.reverse = s₄ := by
    funext j; fin_cases j <;> simp [s₃, s₄, update]
  have hs₅ : drained s₄ (1 : Fin 2) (fun j a => if j = (0 : Fin 2) then [a] else []) = s₅ := by
    funext j; fin_cases j <;> simp [drained, s₄, s₅, List.flatMap_singleton]
  have hs₅' : s₅ = singleWord (0 : Fin 2) out := by
    funext j; fin_cases j <;> simp [s₅, singleWord, update]
  have e₁ : Eval M 1 (.drain 0 (fun j a => if j = (1 : Fin 2) then [a] else [])) s₀ s₁ (inp.length + 1) := by
    rw [← hs₁]; exact Eval.drain s₀ 0 _
  have e₂ : Eval M 1 (.drop 1) s₁ s₂ 1 := by
    rw [← hs₂]; exact Eval.drop s₁ 1
  have e₃ : Eval M 1 (.put 1 [3]) s₂ s₃ 1 := by
    rw [← hs₃]; exact Eval.put s₂ 1 [3]
  have e₄ : Eval M 1 .call s₃ s₄ (inp.length + m_M + out.length + 2) := by
    rw [← hs₄]
    exact Eval.call s₃ inp out m_M (by simp [s₃]) ⟨hmrun⟩
  have e₅ : Eval M 1 (.drain 1 (fun j a => if j = (0 : Fin 2) then [a] else [])) s₄ s₅ (out.reverse.length + 1) := by
    rw [← hs₅]; exact Eval.drain s₄ 1 _
  have e₃₄₅ := Eval.seq e₃ (Eval.seq e₄ e₅)
  have hcond := Eval.no (r := (1 : Fin 2)) (p := fun o => decide (o = some (3 : Sym)))
    (a := .seq (.drain 1 (fun _ _ => [])) (.put 0 [3]))
    (b := .seq (.put 1 [3]) (.seq .call (.drain 1 (fun j a => if j = (0 : Fin 2) then [a] else []))))
    (by simp [s₂, hqrev, ha_ne]) e₃₄₅
  have eall := Eval.seq e₁ (Eval.seq e₂ hcond)
  rw [hs₅'] at eall
  have hrun := compile_run eall
  obtain ⟨m, hm, ⟨hres⟩⟩ := hrun
  refine ⟨m, ?_, ⟨hres⟩⟩
  have hm' : (m : ℝ) ≤ (inp.length + 1 + (1 + (1 + (1 + (inp.length + m_M + out.length + 2 +
      (out.reverse.length + 1))))) + 1 : ℕ) := hm
  push_cast at hm'
  simp only [List.length_reverse] at hm'
  linarith [hm_M]

end BranchZero

/-! ### 3. List, merge/deduplication, and convexity helpers -/

section MathHelpers

private lemma list_count_sum_fin {M : Type*} [AddCommMonoid M] {m : ℕ}
    (l : List (Fin m)) (F : Fin m → M) :
    (l.map F).sum = ∑ idx : Fin m, (l.count idx) • F idx := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have hcnt : ∀ idx : Fin m, (a :: tl).count idx = tl.count idx + (if idx = a then 1 else 0) :=
        fun idx => by
          rw [List.count_cons]
          by_cases ha : a = idx
          · subst ha; simp
          · simp [beq_false_of_ne ha, Ne.symm ha]
      calc F a + ∑ idx : Fin m, tl.count idx • F idx
        _ = (∑ idx : Fin m, (if idx = a then (1 : ℕ) else 0) • F idx) +
              ∑ idx : Fin m, tl.count idx • F idx := by
            congr 1
            have hite : (∑ idx : Fin m, if idx = a then F idx else 0) = F a := by
              rw [Finset.sum_ite_eq' Finset.univ a F, if_pos (Finset.mem_univ a)]
            rw [← hite]
            refine Finset.sum_congr rfl fun idx _ => by split_ifs <;> simp
        _ = ∑ idx : Fin m, ((if idx = a then (1 : ℕ) else 0) + tl.count idx) • F idx := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun idx _ => (add_smul _ _ _).symm
        _ = ∑ idx : Fin m, (a :: tl).count idx • F idx := by
            refine Finset.sum_congr rfl fun idx _ => ?_
            rw [hcnt idx, add_comm]

private lemma list_map_sum_finRange {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Fin m → M) :
    ((List.finRange m).map f).sum = ∑ j : Fin m, f j := by
  have hnodup : (List.finRange m).Nodup := List.nodup_finRange m
  rw [list_count_sum_fin]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [List.count_eq_one_of_mem hnodup (List.mem_finRange idx), one_smul]

private lemma flatMap_drop_take {α : Type*} (l : List α) (m b : ℕ)
    (hl : l.length = m * b) :
    ((List.finRange m).flatMap fun j => (l.drop (j.1 * b)).take b) = l := by
  induction m generalizing l with
  | zero =>
      simp only [zero_mul, List.length_eq_zero_iff] at hl
      simp [hl]
  | succ m ih =>
      rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
      simp only [Function.comp_def, Fin.val_zero, Fin.val_succ, zero_mul, List.drop_zero]
      have hdrop : (l.drop b).length = m * b := by
        rw [List.length_drop, hl, Nat.succ_mul]; omega
      have hstep : ∀ j : Fin m, ((l.drop ((j.1 + 1) * b)).take b) =
          (((l.drop b).drop (j.1 * b)).take b) := fun j => by
        rw [List.drop_drop, Nat.add_mul, one_mul, Nat.add_comm]
      simp_rw [hstep]
      rw [ih (l.drop b) hdrop, List.take_append_drop]

private lemma list_sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_ratCast_real {α : Type*} (l : List α) (g : α → ℚ) :
    (l.map fun x => (g x : ℝ)).sum = ((l.map g).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_intCast_rat {α : Type*} (l : List α) (g : α → ℤ) :
    (l.map fun x => (g x : ℚ)).sum = ((l.map g).sum : ℚ) := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_intCast_real {α : Type*} (l : List α) (g : α → ℤ) :
    (l.map fun x => (g x : ℝ)).sum = ((l.map g).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_natCast_rat {α : Type*} (l : List α) (g : α → ℕ) :
    (l.map fun x => (g x : ℚ)).sum = ((l.map g).sum : ℚ) := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_get_fin {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    (∑ idx : Fin l.length, g (l.get idx)) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      simp only [List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem, List.getElem_cons_zero,
        List.getElem_cons_succ, List.map_cons, List.sum_cons]
      exact congrArg (g a + ·) ih

private lemma list_prod_fst_sum {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (l : List (A × B)) : l.sum.1 = (l.map Prod.fst).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_prod_snd_sum {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (l : List (A × B)) : l.sum.2 = (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_pi_sum_apply {ι A : Type*} [AddCommMonoid A]
    (l : List (ι → A)) (i : ι) : l.sum i = (l.map fun f => f i).sum := by
  induction l with
  | nil => simp
  | cons a tl ih => simp [ih]

private lemma list_sum_le_of_forall {α : Type*} (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a List.mem_cons_self)
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private lemma list_sum_lt_of_forall_lt {α : Type*} (l : List α) (hne : l ≠ [])
    (f : α → ℚ) (c : ℚ) (h : ∀ x ∈ l, f x < c) : (l.map f).sum < (l.length : ℚ) * c := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have ha := h a List.mem_cons_self
      cases tl with
      | nil => simpa using ha
      | cons b tl' =>
          have htl := ih (List.cons_ne_nil b tl') (fun x hx => h x (List.mem_cons_of_mem _ hx))
          linarith

private lemma list_sum_nonneg_of_forall {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (h0 a List.mem_cons_self)
        (ih (fun x hx => h0 x (List.mem_cons_of_mem _ hx)))

private lemma list_sum_nonneg_eq_zero {α : Type*} (l : List α) (f : α → ℚ)
    (h0 : ∀ x ∈ l, 0 ≤ f x) (hs : (l.map f).sum = 0) : ∀ x ∈ l, f x = 0 := by
  induction l with
  | nil => intro _ hx; simp at hx
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons] at hs
      have ha0 := h0 a List.mem_cons_self
      have htl0 : 0 ≤ (tl.map f).sum :=
        list_sum_nonneg_of_forall tl f (fun x hx => h0 x (List.mem_cons_of_mem _ hx))
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · linarith
      · exact ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (by linarith) x hx'

private lemma list_sum_div_const_rat {α : Type*} (l : List α) (g : α → ℚ) (c : ℚ) :
    (l.map fun x => g x / c).sum = (l.map g).sum / c := by
  induction l with
  | nil => simp
  | cons a tl ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma list_sum_div_const_real {α : Type*} (l : List α) (g : α → ℝ) (c : ℝ) :
    (l.map fun x => g x / c).sum = (l.map g).sum / c := by
  induction l with
  | nil => simp
  | cons a tl ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma mergeStep_props {d k : ℕ}
    (P : (Fin d → ℤ) × (Fin k → ℚ) → Prop) (f : (Fin d → ℝ) → ℝ)
    (e : (Fin d → ℤ) × (Fin k → ℚ) × ℕ) (acc : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ))
    (hnd : (acc.map fun h => (h.1, h.2.1)).Nodup)
    (he_pos : 1 ≤ e.2.2) (he_P : P (e.1, e.2.1))
    (hacc_pos : ∀ h ∈ acc, 1 ≤ h.2.2) (hacc_P : ∀ h ∈ acc, P (h.1, h.2.1)) :
    let step := if acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) then
      acc.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then (h.1, h.2.1, h.2.2 + e.2.2) else h)
      else e :: acc
    step.length ≤ acc.length + 1 ∧
    (step.map fun h => (h.1, h.2.1)).Nodup ∧
    (∀ h ∈ step, 1 ≤ h.2.2) ∧
    (∀ h ∈ step, P (h.1, h.2.1)) ∧
    (step.map fun h => (h.2.2 : ℝ) • (certGen h).toReal).sum =
      (e.2.2 : ℝ) • (certGen e).toReal + (acc.map fun h => (h.2.2 : ℝ) • (certGen h).toReal).sum ∧
    (step.map fun h => h.2.2).sum = e.2.2 + (acc.map fun h => h.2.2).sum ∧
    (step.map fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ))).sum =
      (e.2.2 : ℝ) * f (fun i => (e.1 i : ℝ)) +
        (acc.map fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ))).sum := by
  classical
  dsimp only
  split_ifs with hany
  · obtain ⟨h₀, hh₀_mem, hh₀_eq⟩ := List.any_iff_exists_prop.mp hany
    have hkey : (h₀.1, h₀.2.1) = (e.1, e.2.1) := by simpa using hh₀_eq
    have hmap_key : (acc.map fun h => if (h.1, h.2.1) = (e.1, e.2.1) then
        (h.1, h.2.1, h.2.2 + e.2.2) else h).map (fun h => (h.1, h.2.1)) =
        acc.map (fun h => (h.1, h.2.1)) := by
      rw [List.map_map]
      refine List.map_congr_left fun h _ => ?_
      dsimp only [Function.comp_def]
      split_ifs <;> rfl
    have hind : ∀ xs : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ),
        (xs.map fun h => (h.1, h.2.1)).Nodup →
        (∃ h ∈ xs, (h.1, h.2.1) = (e.1, e.2.1)) →
        ((xs.map fun h => if (h.1, h.2.1) = (e.1, e.2.1) then
            (h.1, h.2.1, h.2.2 + e.2.2) else h).map
            (fun h => (h.2.2 : ℝ) • (certGen h).toReal)).sum =
          (e.2.2 : ℝ) • (certGen e).toReal +
            (xs.map fun h => (h.2.2 : ℝ) • (certGen h).toReal).sum ∧
        ((xs.map fun h => if (h.1, h.2.1) = (e.1, e.2.1) then
            (h.1, h.2.1, h.2.2 + e.2.2) else h).map (fun h => h.2.2)).sum =
          e.2.2 + (xs.map fun h => h.2.2).sum ∧
        ((xs.map fun h => if (h.1, h.2.1) = (e.1, e.2.1) then
            (h.1, h.2.1, h.2.2 + e.2.2) else h).map
            (fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ)))).sum =
          (e.2.2 : ℝ) * f (fun i => (e.1 i : ℝ)) +
            (xs.map fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ))).sum := by
      intro xs hxs_nd hxs_ex
      induction xs with
      | nil => rcases hxs_ex with ⟨_, h, _⟩; simp at h
      | cons a tl ih =>
          rw [List.map_cons, List.nodup_cons] at hxs_nd
          by_cases ha : (a.1, a.2.1) = (e.1, e.2.1)
          · have hnone : ∀ h ∈ tl, ¬((h.1, h.2.1) = (e.1, e.2.1)) := fun h hh hhe =>
              hxs_nd.1 (ha ▸ hhe ▸ List.mem_map_of_mem hh)
            have htl_eq : tl.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then
                (h.1, h.2.1, h.2.2 + e.2.2) else h) = tl :=
              (List.map_congr_left fun h hh => if_neg (hnone h hh)).trans (List.map_id _)
            have h1_eq : a.1 = e.1 := (Prod.mk.inj ha).1
            have h2_eq : a.2.1 = e.2.1 := (Prod.mk.inj ha).2
            simp only [List.map_cons, if_pos ha, htl_eq, List.sum_cons]
            refine ⟨?_, ?_, ?_⟩
            · ext i
              · simp [certGen, Gen.toReal, Nat.cast_add, h1_eq]; ring
              · simp [certGen, Gen.toReal, Nat.cast_add, h2_eq]; ring
            · omega
            · simp [Nat.cast_add, add_mul, h1_eq]; ring
          · have htl_ex : ∃ h ∈ tl, (h.1, h.2.1) = (e.1, e.2.1) := by
              rcases hxs_ex with ⟨h, hh, hhe⟩
              rcases List.mem_cons.mp hh with rfl | hh'
              · exact absurd hhe ha
              · exact ⟨h, hh', hhe⟩
            obtain ⟨ih1, ih2, ih3⟩ := ih hxs_nd.2 htl_ex
            simp only [List.map_cons, if_neg ha, List.sum_cons, ih1, ih2, ih3]
            refine ⟨by abel, by omega, by ring⟩
    obtain ⟨hsum1, hsum2, hsum3⟩ := hind acc hnd ⟨h₀, hh₀_mem, hkey⟩
    refine ⟨by simp, ?_, ?_, ?_, hsum1, hsum2, hsum3⟩
    · rwa [hmap_key]
    · intro h hh
      rw [List.mem_map] at hh
      rcases hh with ⟨a, ha, rfl⟩
      split_ifs
      · exact Nat.le_trans (hacc_pos a ha) (Nat.le_add_right _ _)
      · exact hacc_pos a ha
    · intro h hh
      rw [List.mem_map] at hh
      rcases hh with ⟨a, ha, rfl⟩
      split_ifs
      · exact hacc_P a ha
      · exact hacc_P a ha
  · have hnot : (e.1, e.2.1) ∉ acc.map (fun h => (h.1, h.2.1)) := by
      intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨h, hh, hhe⟩
      have ha : acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) = true :=
        List.any_iff_exists_prop.mpr ⟨h, hh, by simpa using hhe⟩
      exact hany ha
    refine ⟨by simp, ?_, ?_, ?_, by simp, by simp, by simp⟩
    · rw [List.map_cons, List.nodup_cons]; exact ⟨hnot, hnd⟩
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact he_pos
      · exact hacc_pos h hh'
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh'
      · exact he_P
      · exact hacc_P h hh'

private lemma mergeCert_props {d k : ℕ}
    (P : (Fin d → ℤ) × (Fin k → ℚ) → Prop) (f : (Fin d → ℝ) → ℝ)
    (raw : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ))
    (hraw_pos : ∀ e ∈ raw, 1 ≤ e.2.2) (hraw_P : ∀ e ∈ raw, P (e.1, e.2.1)) :
    let out := raw.foldr (fun e acc =>
      if acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) then
        acc.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then (h.1, h.2.1, h.2.2 + e.2.2) else h)
      else e :: acc) []
    out.length ≤ raw.length ∧
    (out.map fun h => (h.1, h.2.1)).Nodup ∧
    (∀ h ∈ out, 1 ≤ h.2.2) ∧
    (∀ h ∈ out, P (h.1, h.2.1)) ∧
    (out.map fun h => (h.2.2 : ℝ) • (certGen h).toReal).sum =
      (raw.map fun h => (h.2.2 : ℝ) • (certGen h).toReal).sum ∧
    (out.map fun h => h.2.2).sum = (raw.map fun h => h.2.2).sum ∧
    (out.map fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ))).sum =
      (raw.map fun h => (h.2.2 : ℝ) * f (fun i => (h.1 i : ℝ))).sum := by
  induction raw with
  | nil => simp
  | cons e tl ih =>
      obtain ⟨hl, hnd, hpos, hP, hs1, hs2, hs3⟩ := ih
        (fun h hh => hraw_pos h (List.mem_cons_of_mem e hh))
        (fun h hh => hraw_P h (List.mem_cons_of_mem e hh))
      have hm := mergeStep_props P f e _ hnd
        (hraw_pos e List.mem_cons_self) (hraw_P e List.mem_cons_self) hpos hP
      simp only [List.foldr_cons, List.length_cons, List.map_cons, List.sum_cons]
      refine ⟨hm.1.trans (Nat.add_le_add_right hl 1), hm.2.1, hm.2.2.1, hm.2.2.2.1, ?_, ?_, ?_⟩
      · rw [hm.2.2.2.2.1, hs1]
      · rw [hm.2.2.2.2.2.1, hs2]
      · rw [hm.2.2.2.2.2.2, hs3]

private lemma convex_P (I : Instance) (t : Fin I.τ) : Convex ℝ (I.P t) := by
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab i
  have h1 := hp₁ i
  have h2 := hp₂ i
  have hcomb :
      (∑ j, (I.Aloc t i j : ℝ) * (a • p₁ + b • p₂).1 j) +
        (∑ j, (I.Bloc t i j : ℝ) * (a • p₁ + b • p₂).2 j) =
      a * ((∑ j, (I.Aloc t i j : ℝ) * p₁.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₁.2 j)) +
        b * ((∑ j, (I.Aloc t i j : ℝ) * p₂.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₂.2 j)) := by
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have ha1 : (∑ j, (I.Aloc t i j : ℝ) * (a * p₁.1 j)) =
        a * ∑ j, (I.Aloc t i j : ℝ) * p₁.1 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have hb1 : (∑ j, (I.Aloc t i j : ℝ) * (b * p₂.1 j)) =
        b * ∑ j, (I.Aloc t i j : ℝ) * p₂.1 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have ha2 : (∑ j, (I.Bloc t i j : ℝ) * (a * p₁.2 j)) =
        a * ∑ j, (I.Bloc t i j : ℝ) * p₁.2 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have hb2 : (∑ j, (I.Bloc t i j : ℝ) * (b * p₂.2 j)) =
        b * ∑ j, (I.Bloc t i j : ℝ) * p₂.2 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    rw [ha1, hb1, ha2, hb2]
    ring
  rw [hcomb]
  calc a * ((∑ j, (I.Aloc t i j : ℝ) * p₁.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₁.2 j)) +
        b * ((∑ j, (I.Aloc t i j : ℝ) * p₂.1 j) + (∑ j, (I.Bloc t i j : ℝ) * p₂.2 j))
    _ ≤ a * (I.bloc t i : ℝ) + b * (I.bloc t i : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = (a + b) * (I.bloc t i : ℝ) := by ring
    _ = (I.bloc t i : ℝ) := by rw [hab, one_mul]

private lemma Pr_subset_P (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    I.Pr t r ⊆ I.P t :=
  convexHull_min (fun _ ⟨g, hg, hge⟩ => hge ▸ hg.1) (convex_P I t)

private lemma Phi_zero (I : Instance) (t : Fin I.τ) (r : Residue I.d) :
    I.Phi t r 0 = 0 := by
  unfold Instance.Phi
  refine le_antisymm ?_ ?_
  · refine iInf₂_le_of_le (0 : Gen I.d I.k →₀ ℝ) ?_ (by simp [fracCost])
    refine ⟨by simp, fun _ => le_rfl, ?_, by simp⟩
    ext <;> simp
  · refine le_iInf₂ fun θ hθ => ?_
    have hθ0 : ∀ g, θ g = 0 := fun g => by
      by_contra hne
      have hg : g ∈ θ.support := Finsupp.mem_support_iff.mpr hne
      have hpos : 0 < θ g := lt_of_le_of_ne (hθ.2.1 g) (Ne.symm hne)
      have hle : θ g ≤ ∑ x ∈ θ.support, θ x :=
        Finset.single_le_sum (fun x _ => hθ.2.1 x) hg
      have hsum : (∑ x ∈ θ.support, θ x) = 0 := hθ.2.2.2
      linarith
    have hcost0 : fracCost (I.f t) θ = 0 := by simp [fracCost, Finsupp.sum, hθ0]
    rw [hcost0]
    exact le_rfl

private lemma nonempty_Sr_of_Cr_pos (I : Instance) (t : Fin I.τ) (r : Residue I.d)
    {z : Fin I.d → ℝ} {w : Fin I.k → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hCr : (z, w, (n : ℝ)) ∈ I.Cr t r) :
    (I.Sr t r).Nonempty := by
  have hPr : ((n : ℝ)⁻¹ • z, (n : ℝ)⁻¹ • w) ∈ I.Pr t r := by
    rcases hCr with h0 | hpos
    · exfalso
      have h2 := congr_arg (fun p : Pt I.d I.k => p.2.2) h0
      simp only at h2
      have : (n : ℝ) = 0 := h2
      have : n = 0 := Nat.cast_eq_zero.mp this
      omega
    · exact hpos.2
  by_contra hSr
  rw [Set.not_nonempty_iff_eq_empty] at hSr
  have hPre : I.Pr t r = ∅ := by simp [Instance.Pr, hSr]
  rw [hPre] at hPr
  exact Set.notMem_empty _ hPr

end MathHelpers

/-! ### 4. Constructive rounding correctness -/

section RoundingCorrectness

private lemma round_correct (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ) (hn : 1 ≤ n)
    (o : ℚ × ((Fin I.d → ℚ) × (Fin I.k → ℚ)) × ℚ × List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ))
    (ho_phi : ((o.1 : ℝ) : EReal) = I.Phi t r ((ratPair (fun i => (z i : ℚ)) w).1,
      (ratPair (fun i => (z i : ℚ)) w).2, (n : ℝ)))
    (ho_len : o.2.2.2.length ≤ min (2 ^ I.d) (I.d + I.k + 1))
    (ho_Sr : ∀ e ∈ o.2.2.2, ratGen e.1 e.2.1 ∈ I.Sr t r ∧ 0 < e.2.2)
    (ho_aggr : (o.2.2.2.map fun e => (e.2.2 : ℝ) • (ratGen e.1 e.2.1).toReal).sum =
      ratPair (fun i => (z i : ℚ)) w)
    (ho_sum : (o.2.2.2.map fun e => (e.2.2 : ℝ)).sum = (n : ℚ))
    (ho_cost : (o.2.2.2.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum = o.1) :
    let rep := o.2.2.2
    let q := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => ⌊e.2.2⌋₊
    let δ := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => e.2.2 - (q e : ℚ)
    let ρ := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => ⌊((2 ^ I.d : ℕ) : ℚ) * δ e⌋₊
    let ℓ := n - (rep.map q).sum
    let poolIdx := (List.finRange rep.length).flatMap fun idx => List.replicate (ρ (rep.get idx)) idx
    let usedIdx := poolIdx.take (2 ^ I.d * (ℓ - 1))
    let chunk := fun j : Fin (ℓ - 1) => (usedIdx.drop (j.1 * 2 ^ I.d)).take (2 ^ I.d)
    let xAvg := fun (j : Fin (ℓ - 1)) (i : Fin I.d) =>
      ((r i : ℕ) : ℤ) + ((chunk j).map fun idx => ((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ)).sum
    let uAvg := fun (j : Fin (ℓ - 1)) (i : Fin I.k) =>
      ((chunk j).map fun idx => (rep.get idx).2.1 i).sum / ((2 ^ I.d : ℕ) : ℚ)
    let β := fun idx : Fin rep.length => δ (rep.get idx) - (usedIdx.count idx : ℚ) / ((2 ^ I.d : ℕ) : ℚ)
    let xFinal := fun i : Fin I.d =>
      z i - (rep.map fun e => (q e : ℤ) * e.1 i).sum - ((List.finRange (ℓ - 1)).map fun j => xAvg j i).sum
    let uFinal := fun i : Fin I.k =>
      ((List.finRange rep.length).map fun idx => β idx * (rep.get idx).2.1 i).sum
    let raw : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) :=
      if ℓ = 0 then rep.map fun e => (e.1, e.2.1, q e)
      else (rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)) ++
           ((List.finRange (ℓ - 1)).map fun j => (xAvg j, uAvg j, 1)) ++
           [(xFinal, uFinal, 1)]
    let out : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) :=
      raw.foldr (fun e acc =>
        if acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) then
          acc.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then (h.1, h.2.1, h.2.2 + e.2.2) else h)
        else e :: acc) []
    out.length ≤ 2 ^ (I.d + 1) - 1 ∧
    (out.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ out, 1 ≤ e.2.2 ∧ (certGen e).toReal ∈ I.Pr t r ∧ certGen e ∈ I.S t) ∧
    (out.map fun e => (e.2.2 : ℝ) • (certGen e).toReal).sum =
      ((fun i => (z i : ℝ)), fun j => (w j : ℝ)) ∧
    (out.map fun e => e.2.2).sum = n ∧
    (((out.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum : ℝ) : EReal) ≤
      I.Phi t r ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) := by
  intro rep q δ ρ ℓ poolIdx usedIdx chunk xAvg uAvg β xFinal uFinal raw out
  have hrep_len : rep.length ≤ 2 ^ I.d := ho_len.trans (min_le_left _ _)
  have hrep_pos : ∀ e ∈ rep, 0 < e.2.2 := fun e he => (ho_Sr e he).2
  have hrep_Sr : ∀ e ∈ rep, ratGen e.1 e.2.1 ∈ I.Sr t r := fun e he => (ho_Sr e he).1
  have hrep_sumQ : (rep.map fun e => e.2.2).sum = (n : ℚ) := by
    rw [list_sum_ratCast_real rep (fun e => e.2.2)] at ho_sum
    exact Rat.cast_injective ho_sum
  have hrep_ne : rep ≠ [] := by
    intro h
    simp [rep, h] at hrep_sumQ
    have : (n : ℚ) = 0 := hrep_sumQ.symm
    have : n = 0 := Nat.cast_eq_zero.mp this
    omega
  have hδ_nonneg : ∀ e ∈ rep, (0 : ℚ) ≤ δ e := fun e he => by
    have h0 := (hrep_pos e he).le
    exact sub_nonneg.mpr (Nat.floor_le h0)
  have hδ_lt_one : ∀ e ∈ rep, δ e < 1 := fun e he => by
    have hlt := Nat.lt_floor_add_one e.2.2
    dsimp only [δ, q]
    linarith
  have hq_sum_le : (rep.map q).sum ≤ n := by
    have hle : ((rep.map q).sum : ℚ) ≤ (n : ℚ) := by
      calc ((rep.map q).sum : ℚ)
        _ = (rep.map fun e => (q e : ℚ)).sum := (list_sum_natCast_rat rep q).symm
        _ ≤ (rep.map fun e => e.2.2).sum :=
            list_sum_le_of_forall rep (fun e => (q e : ℚ)) (fun e => e.2.2)
              (fun e he => Nat.floor_le (hrep_pos e he).le)
        _ = (n : ℚ) := hrep_sumQ
    exact_mod_cast hle
  have hℓ_eqQ : (ℓ : ℚ) = (rep.map δ).sum := by
    have h1 : (rep.map fun e => e.2.2).sum = (rep.map fun e => (q e : ℚ)).sum + (rep.map δ).sum := by
      dsimp only [δ]
      clear * -
      induction rep with
      | nil => simp
      | cons a tl ih =>
          simp only [List.map_cons, List.sum_cons] at ih ⊢
          linarith
    have hcast : ((ℓ : ℕ) : ℚ) = (n : ℚ) - ((rep.map q).sum : ℚ) := Nat.cast_sub hq_sum_le
    rw [hcast, ← hrep_sumQ, ← list_sum_natCast_rat rep q]
    linarith
  have hℓ_lt_rep : ℓ < rep.length := by
    have hltQ : (ℓ : ℚ) < (rep.length : ℚ) := by
      rw [hℓ_eqQ]
      simpa only [mul_one] using list_sum_lt_of_forall_lt rep hrep_ne δ 1 hδ_lt_one
    exact_mod_cast hltQ
  have hℓ_le : ℓ ≤ 2 ^ I.d - 1 := by omega
  have h2d_posZ : (0 : ℤ) < (2 ^ I.d : ℤ) := by positivity
  have h2d_posQ : (0 : ℚ) < ((2 ^ I.d : ℕ) : ℚ) := by positivity
  have h2d_posR : (0 : ℝ) < (2 ^ I.d : ℝ) := by positivity
  have hcongr_Sr : ∀ e ∈ rep, ∀ i : Fin I.d,
      e.1 i ≡ ((r i : ℕ) : ℤ) [ZMOD (2 ^ I.d : ℤ)] := fun e he i =>
    (hrep_Sr e he).2 i
  have hPr_subset : I.Pr t r ⊆ I.P t := Pr_subset_P I t r
  have hinPr_of_rep : ∀ e ∈ rep, (ratGen e.1 e.2.1).toReal ∈ I.Pr t r := fun e he =>
    subset_convexHull ℝ _ ⟨ratGen e.1 e.2.1, hrep_Sr e he, rfl⟩
  have hinS_of_inPr : ∀ e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ,
      (certGen e).toReal ∈ I.Pr t r → certGen e ∈ I.S t := fun e he => hPr_subset he
  have haggr_split1 : ∀ i : Fin I.d,
      (rep.map fun e => e.2.2 * (e.1 i : ℚ)).sum = (z i : ℚ) := fun i => by
    have h1 := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 i) ho_aggr
    rw [list_prod_fst_sum, list_pi_sum_apply, List.map_map] at h1
    have h2 : (((rep.map fun e => e.2.2 * (e.1 i : ℚ)).sum : ℚ) : ℝ) = ((z i : ℚ) : ℝ) := by
      rw [← list_sum_ratCast_real]
      simpa [Function.comp_def, ratPair, ratGen, Gen.toReal] using h1
    exact Rat.cast_injective h2
  have haggr_split2 : ∀ j : Fin I.k,
      (rep.map fun e => e.2.2 * e.2.1 j).sum = w j := fun j => by
    have h1 := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.2 j) ho_aggr
    rw [list_prod_snd_sum, list_pi_sum_apply, List.map_map] at h1
    have h2 : (((rep.map fun e => e.2.2 * e.2.1 j).sum : ℚ) : ℝ) = (w j : ℝ) := by
      rw [← list_sum_ratCast_real]
      simpa [Function.comp_def, ratPair, ratGen, Gen.toReal] using h1
    exact Rat.cast_injective h2
  have hcr_eq : ((ratPair (fun i => (z i : ℚ)) w).1, (ratPair (fun i => (z i : ℚ)) w).2, (n : ℝ)) =
      ((fun i => (z i : ℝ)), fun j => (w j : ℝ), (n : ℝ)) := by simp [ratPair]
  -- Establish all properties on `raw`, then transfer through `mergeCert_props`.
  suffices hraw : raw.length ≤ 2 ^ (I.d + 1) - 1 ∧
      (∀ e ∈ raw, 1 ≤ e.2.2) ∧
      (∀ e ∈ raw, (certGen e).toReal ∈ I.Pr t r ∧ certGen e ∈ I.S t) ∧
      (raw.map fun e => (e.2.2 : ℝ) • (certGen e).toReal).sum =
        ((fun i => (z i : ℝ)), fun j => (w j : ℝ)) ∧
      (raw.map fun e => e.2.2).sum = n ∧
      (((raw.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum : ℝ) : EReal) ≤
        I.Phi t r ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) by
    have hm := mergeCert_props (fun p => (ratGen p.1 p.2).toReal ∈ I.Pr t r ∧ ratGen p.1 p.2 ∈ I.S t)
      (I.f t) raw hraw.2.1 (fun e he => hraw.2.2.1 e he)
    refine ⟨hm.1.trans hraw.1, hm.2.1, fun e he => ⟨hm.2.2.1 e he, hm.2.2.2.1 e he⟩, ?_, ?_, ?_⟩
    · rw [hm.2.2.2.2.1, hraw.2.2.2.1]
    · rw [hm.2.2.2.2.2.1, hraw.2.2.2.2.1]
    · rw [hm.2.2.2.2.2.2]; exact hraw.2.2.2.2.2
  by_cases hℓ0 : ℓ = 0
  · -- Case ℓ = 0: every δ e = 0, so e.2.2 = q e ≥ 1
    have hδ0 : ∀ e ∈ rep, δ e = 0 :=
      list_sum_nonneg_eq_zero rep δ hδ_nonneg (by rw [← hℓ_eqQ, hℓ0, Nat.cast_zero])
    have hqe_eq : ∀ e ∈ rep, (q e : ℚ) = e.2.2 := fun e he => by
      have := hδ0 e he
      dsimp only [δ] at this
      linarith
    have hraw_eq : raw = rep.map fun e => (e.1, e.2.1, q e) := by simp [raw, hℓ0]
    rw [hraw_eq]
    have h1n : 1 ≤ 2 ^ I.d := Nat.one_le_two_pow
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_map]
      calc rep.length ≤ 2 ^ I.d := hrep_len
        _ ≤ 2 ^ (I.d + 1) - 1 := by rw [Nat.pow_succ]; omega
    · intro e he
      rw [List.mem_map] at he
      rcases he with ⟨a, ha, rfl⟩
      have hqpos : (0 : ℚ) < (q a : ℚ) := by rw [hqe_eq a ha]; exact hrep_pos a ha
      exact_mod_cast hqpos
    · intro e he
      rw [List.mem_map] at he
      rcases he with ⟨a, ha, rfl⟩
      have hp : (certGen (a.1, a.2.1, q a)).toReal ∈ I.Pr t r := hinPr_of_rep a ha
      exact ⟨hp, hPr_subset hp⟩
    · rw [List.map_map]
      calc (rep.map fun x => ((q x : ℕ) : ℝ) • (certGen (x.1, x.2.1, q x)).toReal).sum
        _ = (rep.map fun x => (x.2.2 : ℝ) • (ratGen x.1 x.2.1).toReal).sum := by
            congr 1; refine List.map_congr_left fun a ha => ?_
            have hqa : ((q a : ℕ) : ℝ) = (a.2.2 : ℝ) := by exact_mod_cast hqe_eq a ha
            simp [certGen, ratGen, Gen.toReal, hqa]
        _ = ((fun i => (z i : ℝ)), fun j => (w j : ℝ)) := by simpa [ratPair] using ho_aggr
    · rw [List.map_map]
      have hqsum : (rep.map fun x => q x).sum = n := by
        have h1 : ((rep.map q).sum : ℚ) = (n : ℚ) := by
          rw [← list_sum_natCast_rat rep q]
          calc (rep.map fun x => (q x : ℚ)).sum = (rep.map fun x => x.2.2).sum :=
                congrArg List.sum (List.map_congr_left fun a ha => hqe_eq a ha)
            _ = (n : ℚ) := hrep_sumQ
        exact_mod_cast h1
      simpa [Function.comp_def] using hqsum
    · rw [← hcr_eq, ← ho_phi, EReal.coe_le_coe_iff, List.map_map, ← ho_cost]
      refine le_of_eq (congrArg List.sum (List.map_congr_left fun a ha => ?_))
      have hqa : ((q a : ℕ) : ℝ) = (a.2.2 : ℝ) := by exact_mod_cast hqe_eq a ha
      simp [hqa]
  · -- Case ℓ ≥ 1
    have hℓ_pos : 1 ≤ ℓ := Nat.pos_of_ne_zero hℓ0
    have hraw_eq : raw = (rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)) ++
        ((List.finRange (ℓ - 1)).map fun j => (xAvg j, uAvg j, 1)) ++ [(xFinal, uFinal, 1)] := by
      simp [raw, hℓ0]
    -- Pool length bound: ∑ ρ ≥ 2^d * (ℓ - 1)
    have hrem_lt : (rep.map fun e => δ e - (ρ e : ℚ) / ((2 ^ I.d : ℕ) : ℚ)).sum < 1 := by
      have hterm_lt : ∀ e ∈ rep, δ e - (ρ e : ℚ) / ((2 ^ I.d : ℕ) : ℚ) < 1 / ((2 ^ I.d : ℕ) : ℚ) := by
        intro e _
        have hlt := Nat.lt_floor_add_one (((2 ^ I.d : ℕ) : ℚ) * δ e)
        dsimp only [ρ]
        have hlt' : δ e < ((⌊((2 ^ I.d : ℕ) : ℚ) * δ e⌋₊ : ℚ) + 1) / ((2 ^ I.d : ℕ) : ℚ) :=
          (lt_div_iff₀ h2d_posQ).mpr (by linarith)
        rw [add_div] at hlt'
        linarith
      have hsum_lt : (rep.map fun e => δ e - (ρ e : ℚ) / ((2 ^ I.d : ℕ) : ℚ)).sum <
          (rep.length : ℚ) * (1 / ((2 ^ I.d : ℕ) : ℚ)) :=
        list_sum_lt_of_forall_lt rep hrep_ne _ (1 / ((2 ^ I.d : ℕ) : ℚ)) hterm_lt
      have hlen_div : (rep.length : ℚ) * (1 / ((2 ^ I.d : ℕ) : ℚ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one h2d_posQ).mpr (by exact_mod_cast hrep_len)
      exact hsum_lt.trans_le hlen_div
    have hρ_sum_ge : 2 ^ I.d * (ℓ - 1) ≤ ((List.finRange rep.length).map fun idx => ρ (rep.get idx)).sum := by
      have hmap_sum : ((List.finRange rep.length).map fun idx => ρ (rep.get idx)).sum = (rep.map ρ).sum := by
        rw [list_map_sum_finRange, list_sum_get_fin rep ρ]
      rw [hmap_sum]
      have hltQ : ((ℓ : ℚ) - 1) < ((rep.map ρ).sum : ℚ) / ((2 ^ I.d : ℕ) : ℚ) := by
        have hdiff : (ℓ : ℚ) - ((rep.map ρ).sum : ℚ) / ((2 ^ I.d : ℕ) : ℚ) =
            (rep.map fun e => δ e - (ρ e : ℚ) / ((2 ^ I.d : ℕ) : ℚ)).sum := by
          rw [hℓ_eqQ, ← list_sum_natCast_rat rep ρ]
          clear * -
          induction rep with
          | nil => simp
          | cons a tl ih =>
              simp only [List.map_cons, List.sum_cons] at ih ⊢
              rw [add_div, ← ih]
              ring
        linarith
      have hlt_sub : 2 ^ I.d * (ℓ - 1) < (rep.map ρ).sum + 1 := by
        have h1 : (((2 ^ I.d : ℕ) : ℚ) * ((ℓ - 1 : ℕ) : ℚ)) < ((rep.map ρ).sum : ℚ) + 1 := by
          have hc : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := Nat.cast_sub hℓ_pos
          rw [hc]
          have hmul := (lt_div_iff₀' h2d_posQ).mp hltQ
          linarith
        exact_mod_cast h1
      omega
    have hpool_len : poolIdx.length = ((List.finRange rep.length).map fun idx => ρ (rep.get idx)).sum := by
      simp [poolIdx, List.length_flatMap, List.length_replicate]
    have hused_len : usedIdx.length = 2 ^ I.d * (ℓ - 1) := by
      simp only [usedIdx, List.length_take, hpool_len]
      exact min_eq_left hρ_sum_ge
    have hpool_count : ∀ idx : Fin rep.length, poolIdx.count idx = ρ (rep.get idx) := fun idx => by
      dsimp only [poolIdx]
      simp only [List.count_flatMap, List.map_map, Function.comp_def]
      have hmap : ((List.finRange rep.length).map fun x =>
          (List.replicate (ρ (rep.get x)) x).count idx) =
          (List.finRange rep.length).map fun x => if x = idx then ρ (rep.get x) else 0 := by
        refine List.map_congr_left fun a _ => ?_
        by_cases ha : a = idx
        · subst ha; simp
        · simp [List.count_replicate, beq_false_of_ne (Ne.symm ha), Ne.symm ha]
      rw [hmap, list_map_sum_finRange, Finset.sum_ite_eq' Finset.univ idx]
      simp
    have hused_count : ∀ idx : Fin rep.length, usedIdx.count idx ≤ ρ (rep.get idx) := fun idx =>
      (List.take_sublist _ _).count_le idx |>.trans (hpool_count idx).le
    have hused_count_sum : (∑ idx : Fin rep.length, usedIdx.count idx) = 2 ^ I.d * (ℓ - 1) := by
      have h1 := list_count_sum_fin usedIdx (fun _ => (1 : ℕ))
      simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, hused_len] at h1
      exact h1.symm
    have hused_flat : ((List.finRange (ℓ - 1)).flatMap chunk) = usedIdx :=
      flatMap_drop_take usedIdx (ℓ - 1) (2 ^ I.d) (by rw [hused_len, mul_comm])
    have hchunk_len : ∀ j : Fin (ℓ - 1), (chunk j).length = 2 ^ I.d := fun j => by
      dsimp only [chunk]
      rw [List.length_take, List.length_drop, hused_len]
      have h1 : j.1 + 1 ≤ ℓ - 1 := j.2
      have h2 : j.1 * 2 ^ I.d + 2 ^ I.d ≤ 2 ^ I.d * (ℓ - 1) := by
        rw [mul_comm (2 ^ I.d) (ℓ - 1), ← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ h1
      omega
    have hchunk_sum : ∀ {M : Type} [AddCommMonoid M] (F : Fin rep.length → M),
        ∑ j : Fin (ℓ - 1), ((chunk j).map F).sum =
          ∑ idx : Fin rep.length, (usedIdx.count idx) • F idx := fun F => by
      rw [← list_count_sum_fin usedIdx F, ← hused_flat, List.map_flatMap, list_sum_flatMap,
        list_map_sum_finRange]
    have hx_avg_Z : ∀ (j : Fin (ℓ - 1)) (i : Fin I.d),
        (2 ^ I.d : ℤ) * xAvg j i = ((chunk j).map fun idx => (rep.get idx).1 i).sum := fun j i => by
      have hid : ∀ idx : Fin rep.length,
          ((rep.get idx).1 i : ℤ) = ((r i : ℕ) : ℤ) +
            (2 ^ I.d : ℤ) * (((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ)) := fun idx => by
        have hmod := (hcongr_Sr (rep.get idx) (List.get_mem _ _) i).symm
        have hdvd := Int.modEq_iff_dvd.mp hmod
        have hm := Int.mul_ediv_cancel' hdvd
        linarith
      have hconst : ((chunk j).map fun _ => ((r i : ℕ) : ℤ)).sum =
          (2 ^ I.d : ℤ) * ((r i : ℕ) : ℤ) := by
        rw [List.map_const', List.sum_replicate, hchunk_len j, nsmul_eq_mul, Int.natCast_pow, Nat.cast_ofNat]
      have hsum_id : ((chunk j).map fun idx => (rep.get idx).1 i).sum =
          ((chunk j).map fun _ => ((r i : ℕ) : ℤ)).sum +
          (2 ^ I.d : ℤ) * ((chunk j).map fun idx =>
            ((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ)).sum := by
        have h1 : (chunk j).map (fun idx => (rep.get idx).1 i) =
            (chunk j).map (fun idx => ((r i : ℕ) : ℤ) +
              (2 ^ I.d : ℤ) * (((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ))) :=
          List.map_congr_left fun idx _ => hid idx
        rw [h1]
        clear * -
        induction (chunk j) with
        | nil => simp
        | cons a tl ih =>
            simp only [List.map_cons, List.sum_cons, ih]
            ring
      dsimp only [xAvg]
      rw [mul_add, ← hconst, ← hsum_id]
    have hchunk_map_fin : ∀ {M : Type} [AddCommMonoid M] (j : Fin (ℓ - 1))
        (F : Fin rep.length → M),
        ((chunk j).map F).sum =
          ∑ m : Fin (2 ^ I.d), F ((chunk j).get (m.cast (hchunk_len j).symm)) := fun j F => by
      have heq : (chunk j).map F =
          List.ofFn (fun m : Fin (2 ^ I.d) => F ((chunk j).get (m.cast (hchunk_len j).symm))) := by
        refine List.ext_get (by simp [hchunk_len j]) fun idx h1 h2 => ?_
        simp
      rw [heq, List.sum_ofFn]
    have hxAvg_Pr_f : ∀ j : Fin (ℓ - 1),
        (certGen (xAvg j, uAvg j, 1)).toReal ∈ I.Pr t r ∧
        I.f t (fun i => (xAvg j i : ℝ)) ≤
          ((2 ^ I.d : ℕ) : ℝ)⁻¹ *
            ((chunk j).map fun idx => I.f t (fun i => ((rep.get idx).1 i : ℝ))).sum := fun j => by
      let idx_j : Fin (2 ^ I.d) → Fin rep.length := fun m =>
        (chunk j).get (m.cast (hchunk_len j).symm)
      let pts_j : Fin (2 ^ I.d) → (Fin I.d → ℝ) × (Fin I.k → ℝ) := fun m =>
        (ratGen (rep.get (idx_j m)).1 (rep.get (idx_j m)).2.1).toReal
      let xs_j : Fin (2 ^ I.d) → Fin I.d → ℝ := fun m i => ((rep.get (idx_j m)).1 i : ℝ)
      let wts_j : Fin (2 ^ I.d) → ℝ := fun _ => ((2 ^ I.d : ℕ) : ℝ)⁻¹
      have hw0 : ∀ m ∈ (Finset.univ : Finset (Fin (2 ^ I.d))), 0 ≤ wts_j m := fun _ _ => by positivity
      have hw1 : ∑ m : Fin (2 ^ I.d), wts_j m = 1 := by
        simp [wts_j, div_self h2d_posR.ne']
      have hpts_mem : ∀ m ∈ (Finset.univ : Finset (Fin (2 ^ I.d))), pts_j m ∈ I.Pr t r := fun m _ =>
        hinPr_of_rep (rep.get (idx_j m)) (List.get_mem _ _)
      have hcm_eq : (Finset.univ : Finset (Fin (2 ^ I.d))).centerMass wts_j pts_j =
          (certGen (xAvg j, uAvg j, 1)).toReal := by
        simp only [Finset.centerMass, hw1, inv_one, one_smul]
        ext i
        · have hZi : (((2 ^ I.d : ℤ) * xAvg j i : ℤ) : ℝ) =
              (((chunk j).map fun idx => (rep.get idx).1 i).sum : ℝ) := by
            exact_mod_cast hx_avg_Z j i
          have hRi : ((2 ^ I.d : ℕ) : ℝ) * (xAvg j i : ℝ) =
              ((chunk j).map fun idx => ((rep.get idx).1 i : ℝ)).sum := by
            rw [← list_sum_intCast_real (chunk j) (fun idx => (rep.get idx).1 i)] at hZi
            simpa [Int.cast_mul, Int.cast_pow] using hZi
          rw [hchunk_map_fin j (fun idx => ((rep.get idx).1 i : ℝ))] at hRi
          have hdiv : (xAvg j i : ℝ) = ((2 ^ I.d : ℕ) : ℝ)⁻¹ *
              ∑ m : Fin (2 ^ I.d), ((rep.get (idx_j m)).1 i : ℝ) :=
            (eq_inv_mul_iff_mul_eq₀ (by positivity)).mpr hRi
          simpa [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            wts_j, pts_j, certGen, ratGen, Gen.toReal, ← Finset.mul_sum] using hdiv.symm
        · have hUi : (((chunk j).map fun idx => (rep.get idx).2.1 i).sum : ℝ) =
              ((chunk j).map fun idx => ((rep.get idx).2.1 i : ℝ)).sum :=
            (list_sum_ratCast_real (chunk j) (fun idx => (rep.get idx).2.1 i)).symm
          have hUi' : (uAvg j i : ℝ) = ((2 ^ I.d : ℕ) : ℝ)⁻¹ *
              ∑ m : Fin (2 ^ I.d), ((rep.get (idx_j m)).2.1 i : ℝ) := by
            dsimp only [uAvg]
            rw [Rat.cast_div, Rat.cast_natCast, hUi, hchunk_map_fin j (fun idx => ((rep.get idx).2.1 i : ℝ)),
              div_eq_inv_mul]
          simpa [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            wts_j, pts_j, certGen, ratGen, Gen.toReal, ← Finset.mul_sum] using hUi'.symm
      have hPr_mem : (certGen (xAvg j, uAvg j, 1)).toReal ∈ I.Pr t r := by
        rw [← hcm_eq]
        exact (convex_convexHull ℝ _).centerMass_mem hw0 (by rw [hw1]; exact zero_lt_one) hpts_mem
      have hxs_Px : ∀ m ∈ (Finset.univ : Finset (Fin (2 ^ I.d))), xs_j m ∈ I.Px t := fun m _ =>
        ⟨pts_j m, hPr_subset (hpts_mem m (Finset.mem_univ m)), rfl⟩
      have hconv := (hI.convex t).map_sum_le hw0 hw1 hxs_Px
      have hx_sum : ∑ m : Fin (2 ^ I.d), wts_j m • xs_j m = fun i => (xAvg j i : ℝ) := by
        ext i
        have hi := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 i) hcm_eq
        simpa [Finset.centerMass, hw1, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, certGen, ratGen, Gen.toReal, pts_j, xs_j] using hi
      rw [hx_sum] at hconv
      refine ⟨hPr_mem, ?_⟩
      have hsum_f : ((chunk j).map fun idx => I.f t (fun i => ((rep.get idx).1 i : ℝ))).sum =
          ∑ m : Fin (2 ^ I.d), I.f t (xs_j m) :=
        hchunk_map_fin j (fun idx => I.f t (fun i => ((rep.get idx).1 i : ℝ)))
      rw [hsum_f]
      simpa only [wts_j, smul_eq_mul, ← Finset.mul_sum] using hconv
    -- Residual fraction β, xFinal, uFinal
    have hβ_nonneg : ∀ idx : Fin rep.length, (0 : ℚ) ≤ β idx := fun idx => by
      dsimp only [β]
      have h1 : (usedIdx.count idx : ℚ) ≤ (ρ (rep.get idx) : ℚ) := by
        exact_mod_cast hused_count idx
      have h2 : (ρ (rep.get idx) : ℚ) ≤ ((2 ^ I.d : ℕ) : ℚ) * δ (rep.get idx) :=
        Nat.floor_le (mul_nonneg h2d_posQ.le (hδ_nonneg _ (List.get_mem _ _)))
      have h3 : (usedIdx.count idx : ℚ) / ((2 ^ I.d : ℕ) : ℚ) ≤ δ (rep.get idx) :=
        (div_le_iff₀ h2d_posQ).mpr (by linarith)
      linarith
    have hβ_sum1 : ((List.finRange rep.length).map β).sum = 1 := by
      rw [list_map_sum_finRange]
      have h1 : ∑ idx : Fin rep.length, β idx =
          (∑ idx : Fin rep.length, δ (rep.get idx)) -
            (∑ idx : Fin rep.length, (usedIdx.count idx : ℚ)) / ((2 ^ I.d : ℕ) : ℚ) := by
        simp only [β, Finset.sum_sub_distrib, Finset.sum_div]
      have hδ_sum : ∑ idx : Fin rep.length, δ (rep.get idx) = (ℓ : ℚ) := by
        rw [list_sum_get_fin rep δ]
        exact hℓ_eqQ.symm
      have hcnt_sum : (∑ idx : Fin rep.length, (usedIdx.count idx : ℚ)) =
          ((2 ^ I.d : ℕ) : ℚ) * ((ℓ - 1 : ℕ) : ℚ) := by
        exact_mod_cast hused_count_sum
      have hℓ_sub : ((ℓ - 1 : ℕ) : ℚ) = (ℓ : ℚ) - 1 := Nat.cast_sub hℓ_pos
      rw [h1, hδ_sum, hcnt_sum, mul_div_cancel_left₀ _ h2d_posQ.ne', hℓ_sub]
      ring
    have hxFinal_Q : ∀ i : Fin I.d,
        (xFinal i : ℚ) = ((List.finRange rep.length).map fun idx => β idx * ((rep.get idx).1 i : ℚ)).sum :=
      fun i => by
        rw [list_map_sum_finRange]
        have hq_split : (rep.map fun e => e.2.2 * (e.1 i : ℚ)).sum =
            (rep.map fun e => (q e : ℚ) * (e.1 i : ℚ)).sum +
            (rep.map fun e => δ e * (e.1 i : ℚ)).sum := by
          clear * -
          induction rep with
          | nil => simp
          | cons a tl ih =>
              simp only [List.map_cons, List.sum_cons, ih, δ]
              ring
        have hδ_split : ∑ idx : Fin rep.length, δ (rep.get idx) * ((rep.get idx).1 i : ℚ) =
            (z i : ℚ) - ((rep.map fun e => (q e : ℤ) * e.1 i).sum : ℚ) := by
          have h1 : (∑ idx : Fin rep.length, δ (rep.get idx) * ((rep.get idx).1 i : ℚ)) =
              (rep.map fun e => δ e * (e.1 i : ℚ)).sum :=
            list_sum_get_fin rep (fun e => δ e * (e.1 i : ℚ))
          have h2 : ((rep.map fun e => (q e : ℤ) * e.1 i).sum : ℚ) =
              (rep.map fun e => (q e : ℚ) * (e.1 i : ℚ)).sum := by
            rw [← list_sum_intCast_rat]
            simp
          rw [h1, h2]
          linarith [haggr_split1 i, hq_split]
        have havg_sum_Q : (((List.finRange (ℓ - 1)).map fun j => xAvg j i).sum : ℚ) =
            ∑ idx : Fin rep.length, ((usedIdx.count idx : ℚ) / ((2 ^ I.d : ℕ) : ℚ)) *
              ((rep.get idx).1 i : ℚ) := by
          have hstep : ∀ j : Fin (ℓ - 1), (xAvg j i : ℚ) =
              ((chunk j).map fun idx => ((rep.get idx).1 i : ℚ) / ((2 ^ I.d : ℕ) : ℚ)).sum :=
            fun j => by
              have hZ : (((2 ^ I.d : ℕ) : ℚ) * (xAvg j i : ℚ)) =
                  ((chunk j).map fun idx => ((rep.get idx).1 i : ℚ)).sum := by
                have hZi : (((2 ^ I.d : ℤ) * xAvg j i : ℤ) : ℚ) =
                    (((chunk j).map fun idx => (rep.get idx).1 i).sum : ℚ) := by
                  exact_mod_cast hx_avg_Z j i
                rw [← list_sum_intCast_rat (chunk j) (fun idx => (rep.get idx).1 i)] at hZi
                simpa using hZi
              have hdiv_sum : ((chunk j).map fun idx => ((rep.get idx).1 i : ℚ) / ((2 ^ I.d : ℕ) : ℚ)).sum =
                  ((chunk j).map fun idx => ((rep.get idx).1 i : ℚ)).sum / ((2 ^ I.d : ℕ) : ℚ) :=
                list_sum_div_const_rat (chunk j) (fun idx => ((rep.get idx).1 i : ℚ)) ((2 ^ I.d : ℕ) : ℚ)
              rw [hdiv_sum]
              exact (eq_div_iff h2d_posQ.ne').mpr (by linarith)
          rw [← list_sum_intCast_rat (List.finRange (ℓ - 1)) (fun j => xAvg j i),
            list_map_sum_finRange]
          simp_rw [hstep]
          have hcs := hchunk_sum (fun idx => ((rep.get idx).1 i : ℚ) / ((2 ^ I.d : ℕ) : ℚ))
          simp only [nsmul_eq_mul] at hcs
          rw [hcs]
          refine Finset.sum_congr rfl fun idx _ => by ring
        dsimp only [xFinal]
        rw [Int.cast_sub, Int.cast_sub, ← hδ_split, havg_sum_Q, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun idx _ => by dsimp only [β]; ring
    have hxFinal_Pr_f :
        (certGen (xFinal, uFinal, 1)).toReal ∈ I.Pr t r ∧
        I.f t (fun i => (xFinal i : ℝ)) ≤
          ∑ idx : Fin rep.length, (β idx : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ)) := by
      let pts_f : Fin rep.length → (Fin I.d → ℝ) × (Fin I.k → ℝ) := fun idx =>
        (ratGen (rep.get idx).1 (rep.get idx).2.1).toReal
      let xs_f : Fin rep.length → Fin I.d → ℝ := fun idx i => ((rep.get idx).1 i : ℝ)
      let wts_f : Fin rep.length → ℝ := fun idx => (β idx : ℝ)
      have hw0 : ∀ idx ∈ (Finset.univ : Finset (Fin rep.length)), 0 ≤ wts_f idx := fun idx _ => by
        dsimp only [wts_f]
        exact_mod_cast hβ_nonneg idx
      have hw1 : ∑ idx : Fin rep.length, wts_f idx = 1 := by
        have h1 : ((List.finRange rep.length).map β).sum = ∑ idx : Fin rep.length, β idx :=
          list_map_sum_finRange _ _
        have h2 : (∑ idx : Fin rep.length, β idx) = 1 := h1.symm.trans hβ_sum1
        dsimp only [wts_f]
        exact_mod_cast h2
      have hpts_mem : ∀ idx ∈ (Finset.univ : Finset (Fin rep.length)), pts_f idx ∈ I.Pr t r :=
        fun idx _ => hinPr_of_rep (rep.get idx) (List.get_mem _ _)
      have hcm_eq : (Finset.univ : Finset (Fin rep.length)).centerMass wts_f pts_f =
          (certGen (xFinal, uFinal, 1)).toReal := by
        simp only [Finset.centerMass, hw1, inv_one, one_smul]
        ext i
        · have hRi : (xFinal i : ℝ) =
              ((List.finRange rep.length).map fun idx => (β idx : ℝ) * ((rep.get idx).1 i : ℝ)).sum := by
            have hQ := congr_arg (Rat.cast (K := ℝ)) (hxFinal_Q i)
            rw [← list_sum_ratCast_real (List.finRange rep.length) (fun idx => β idx * ((rep.get idx).1 i : ℚ))] at hQ
            simpa using hQ
          rw [list_map_sum_finRange] at hRi
          simpa [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            wts_f, pts_f, certGen, ratGen, Gen.toReal] using hRi.symm
        · have hUi : (uFinal i : ℝ) =
              ∑ idx : Fin rep.length, (β idx : ℝ) * ((rep.get idx).2.1 i : ℝ) := by
            dsimp only [uFinal]
            rw [← list_sum_ratCast_real (List.finRange rep.length) (fun idx => β idx * (rep.get idx).2.1 i),
              list_map_sum_finRange]
            simp
          simpa [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            wts_f, pts_f, certGen, ratGen, Gen.toReal] using hUi.symm
      have hPr_mem : (certGen (xFinal, uFinal, 1)).toReal ∈ I.Pr t r := by
        rw [← hcm_eq]
        exact (convex_convexHull ℝ _).centerMass_mem hw0 (by rw [hw1]; exact zero_lt_one) hpts_mem
      have hxs_Px : ∀ idx ∈ (Finset.univ : Finset (Fin rep.length)), xs_f idx ∈ I.Px t :=
        fun idx _ => ⟨pts_f idx, hPr_subset (hpts_mem idx (Finset.mem_univ idx)), rfl⟩
      have hconv := (hI.convex t).map_sum_le hw0 hw1 hxs_Px
      have hx_sum : ∑ idx : Fin rep.length, wts_f idx • xs_f idx = fun i => (xFinal i : ℝ) := by
        ext i
        have hi := congr_arg (fun p : (Fin I.d → ℝ) × (Fin I.k → ℝ) => p.1 i) hcm_eq
        simpa [Finset.centerMass, hw1, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, certGen, ratGen, Gen.toReal, pts_f, xs_f] using hi
      rw [hx_sum] at hconv
      exact ⟨hPr_mem, by simpa only [wts_f, xs_f, smul_eq_mul] using hconv⟩
    -- Helper to replace filterMap (drops zeros) with full map on rep
    have hfilter_sum : ∀ {M : Type} [AddCommMonoid M]
        (F : (Fin I.d → ℤ) → (Fin I.k → ℚ) → ℕ → M)
        (hF0 : ∀ x u, F x u 0 = 0),
        ((rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)).map
            fun h => F h.1 h.2.1 h.2.2).sum =
          (rep.map fun e => F e.1 e.2.1 (q e)).sum := by
      intro M _ F hF0
      clear * - hF0
      induction rep with
      | nil => simp
      | cons a tl ih =>
          simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
          split_ifs with hq
          · simp [hq, hF0, ih]
          · simp [ih]
    rw [hraw_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_finRange, List.length_cons,
        List.length_nil]
      have hfl : (rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)).length ≤
          rep.length := List.length_filterMap_le _ _
      rw [Nat.pow_succ]
      omega
    · intro e he
      simp only [List.mem_append, List.mem_filterMap, List.mem_map, List.mem_finRange,
        List.mem_singleton] at he
      rcases he with (⟨a, _, ha⟩ | ⟨j, _, rfl⟩) | rfl
      · rcases eq_or_ne (q a) 0 with hq | hq
        · simp [hq] at ha
        · simp only [hq, ite_false, Option.some.injEq] at ha
          rw [← ha]
          exact Nat.pos_of_ne_zero hq
      · exact le_rfl
      · exact le_rfl
    · intro e he
      simp only [List.mem_append, List.mem_filterMap, List.mem_map, List.mem_finRange,
        List.mem_singleton] at he
      rcases he with (⟨a, ha_mem, ha⟩ | ⟨j, _, rfl⟩) | rfl
      · rcases eq_or_ne (q a) 0 with hq | hq
        · simp [hq] at ha
        · simp only [hq, ite_false, Option.some.injEq] at ha
          rw [← ha]
          have hp : (certGen (a.1, a.2.1, q a)).toReal ∈ I.Pr t r := hinPr_of_rep a ha_mem
          exact ⟨hp, hPr_subset hp⟩
      · exact ⟨(hxAvg_Pr_f j).1, hPr_subset (hxAvg_Pr_f j).1⟩
      · exact ⟨hxFinal_Pr_f.1, hPr_subset hxFinal_Pr_f.1⟩
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
      have hf1 := hfilter_sum (M := (Fin I.d → ℝ) × (Fin I.k → ℝ))
        (fun x u c => (c : ℝ) • (certGen (x, u, c)).toReal)
        (fun x u => by simp)
      rw [hf1]
      ext i
      · simp only [Prod.fst_add, Pi.add_apply, list_prod_fst_sum, list_pi_sum_apply, List.map_map,
          Function.comp_def, Nat.cast_one, one_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
          certGen, Gen.toReal]
        have hq_fst : (rep.map fun x => (q x : ℝ) * (x.1 i : ℝ)).sum =
            (((rep.map fun e => (q e : ℤ) * e.1 i).sum : ℤ) : ℝ) := by
          rw [← list_sum_intCast_real rep (fun e => (q e : ℤ) * e.1 i)]
          simp only [Int.cast_mul, Int.cast_natCast]
        rw [hq_fst, list_sum_intCast_real (List.finRange (ℓ - 1)) (fun j => xAvg j i)]
        dsimp only [xFinal]
        push_cast
        ring
      · simp only [Prod.snd_add, Pi.add_apply, list_prod_snd_sum, list_pi_sum_apply, List.map_map,
          Function.comp_def, Nat.cast_one, one_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          certGen, Gen.toReal]
        have havg_snd : ((List.finRange (ℓ - 1)).map fun j => (uAvg j i : ℝ)).sum =
            ∑ idx : Fin rep.length, ((usedIdx.count idx : ℝ) / ((2 ^ I.d : ℕ) : ℝ)) *
              ((rep.get idx).2.1 i : ℝ) := by
          have hstep : ∀ j : Fin (ℓ - 1), (uAvg j i : ℝ) =
              ((chunk j).map fun idx => ((rep.get idx).2.1 i : ℝ) / ((2 ^ I.d : ℕ) : ℝ)).sum :=
            fun j => by
              dsimp only [uAvg]
              rw [Rat.cast_div, Rat.cast_natCast,
                ← list_sum_ratCast_real (chunk j) (fun idx => (rep.get idx).2.1 i)]
              exact (list_sum_div_const_real (chunk j) (fun idx => ((rep.get idx).2.1 i : ℝ))
                ((2 ^ I.d : ℕ) : ℝ)).symm
          rw [list_map_sum_finRange]
          simp_rw [hstep]
          have hcs := hchunk_sum (fun idx => ((rep.get idx).2.1 i : ℝ) / ((2 ^ I.d : ℕ) : ℝ))
          simp only [nsmul_eq_mul] at hcs
          rw [hcs]
          refine Finset.sum_congr rfl fun idx _ => by ring
        have hu_sum : (uFinal i : ℝ) =
            ∑ idx : Fin rep.length, (β idx : ℝ) * ((rep.get idx).2.1 i : ℝ) := by
          dsimp only [uFinal]
          rw [← list_sum_ratCast_real (List.finRange rep.length) (fun idx => β idx * (rep.get idx).2.1 i),
            list_map_sum_finRange]
          simp
        have hq_sum : (rep.map fun x => (q x : ℝ) * (x.2.1 i : ℝ)).sum =
            ∑ idx : Fin rep.length, (q (rep.get idx) : ℝ) * ((rep.get idx).2.1 i : ℝ) :=
          (list_sum_get_fin rep (fun e => (q e : ℝ) * (e.2.1 i : ℝ))).symm
        have hw_i : (w i : ℝ) =
            ∑ idx : Fin rep.length, ((rep.get idx).2.2 : ℝ) * ((rep.get idx).2.1 i : ℝ) := by
          rw [← haggr_split2 i, ← list_sum_ratCast_real rep (fun e => e.2.2 * e.2.1 i)]
          simp_rw [Rat.cast_mul]
          exact (list_sum_get_fin rep (fun e => (e.2.2 : ℝ) * (e.2.1 i : ℝ))).symm
        rw [hq_sum, havg_snd, hu_sum, hw_i, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun idx _ => ?_
        dsimp only [β, δ]
        push_cast
        ring
    · simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hones : ((List.finRange (ℓ - 1)).map fun _ : Fin (ℓ - 1) => 1).sum = ℓ - 1 := by
        rw [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul, mul_one]
      have hf2 := hfilter_sum (M := ℕ) (fun _ _ c => c) (fun _ _ => rfl)
      have hq_eta : (rep.map fun e => q e).sum = (rep.map q).sum := rfl
      rw [hones, hf2, hq_eta]
      dsimp only [ℓ] at hℓ_pos ⊢
      omega
    · rw [← hcr_eq, ← ho_phi, EReal.coe_le_coe_iff, ← ho_cost]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero, Nat.cast_one, one_mul]
      have hf3 := hfilter_sum (M := ℝ) (fun x _ c => (c : ℝ) * I.f t (fun i => (x i : ℝ)))
        (fun _ _ => by simp)
      rw [hf3]
      simp only [List.map_map, Function.comp_def, Nat.cast_one, one_mul]
      have havg_f : ((List.finRange (ℓ - 1)).map fun j =>
          I.f t (fun i => (xAvg j i : ℝ))).sum ≤
          ∑ idx : Fin rep.length, ((usedIdx.count idx : ℝ) / ((2 ^ I.d : ℕ) : ℝ)) *
            I.f t (fun i => ((rep.get idx).1 i : ℝ)) := by
        rw [list_map_sum_finRange]
        refine le_trans (Finset.sum_le_sum fun j _ => (hxAvg_Pr_f j).2) ?_
        rw [← Finset.mul_sum]
        have hcs := hchunk_sum (fun idx => I.f t (fun i => ((rep.get idx).1 i : ℝ)))
        simp only [nsmul_eq_mul] at hcs
        rw [hcs, Finset.mul_sum]
        exact le_of_eq (Finset.sum_congr rfl fun idx _ => by ring)
      have hq_f : (rep.map fun x => (q x : ℝ) * I.f t (fun i => (x.1 i : ℝ))).sum =
          ∑ idx : Fin rep.length, (q (rep.get idx) : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ)) :=
        (list_sum_get_fin rep (fun e => (q e : ℝ) * I.f t (fun i => (e.1 i : ℝ)))).symm
      have ho_f : (rep.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum =
          ∑ idx : Fin rep.length, ((rep.get idx).2.2 : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ)) :=
        (list_sum_get_fin rep (fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ)))).symm
      have htotal_eq :
          (∑ idx : Fin rep.length, (q (rep.get idx) : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ))) +
          (∑ idx : Fin rep.length, ((usedIdx.count idx : ℝ) / ((2 ^ I.d : ℕ) : ℝ)) *
            I.f t (fun i => ((rep.get idx).1 i : ℝ))) +
          (∑ idx : Fin rep.length, (β idx : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ))) =
          ∑ idx : Fin rep.length, ((rep.get idx).2.2 : ℝ) * I.f t (fun i => ((rep.get idx).1 i : ℝ)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun idx _ => ?_
        dsimp only [β, δ]
        push_cast
        ring
      have hf_final := hxFinal_Pr_f.2
      rw [hq_f, ho_f]
      linarith

end RoundingCorrectness

/-! ### 5. Encoding length bounds and assembly -/

section Assembly

private lemma encNat_length_pos (n : ℕ) : 0 ≤ (encNat n).length := Nat.zero_le _

private lemma encInt_length_pos (z : ℤ) : 1 ≤ (encInt z).length := by
  simp [encInt]

private lemma encNat_one : encNat 1 = [1] := by
  simp [encNat, Computability.encodeNat, Computability.encodeNum, Computability.encodePosNum, bit]

private lemma encRat_int_length (a : ℤ) :
    (encRat (a : ℚ)).length ≤ 3 * (encInt a).length := by
  simp only [encRat, Rat.num_intCast, Rat.den_intCast, encNat_one, List.length_append,
    List.length_cons, List.length_nil]
  have h := encInt_length_pos a
  omega

private lemma encVec_int_length {d : ℕ} (z : Fin d → ℤ) :
    (encVec (fun i => (z i : ℚ))).length ≤ 3 * (encIntVec z).length := by
  have aux : ∀ xs : List (Fin d),
      (xs.flatMap fun j => encRat (z j : ℚ) ++ [3]).length ≤
        3 * (xs.flatMap fun i => encInt (z i) ++ [3]).length := fun xs => by
    induction xs with
    | nil => simp
    | cons a tl ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
        have ha := encRat_int_length (z a)
        omega
  exact aux (List.finRange d)

private lemma encRat_nat_length (n : ℕ) :
    (encRat (n : ℚ)).length + 1 ≤ 4 * ((encNat n).length + 1) := by
  simp only [encRat, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast, encNat_one,
    List.length_append, List.length_cons, List.length_nil, encInt]
  omega

private lemma ctx_length_le_inp (I : Instance) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ) :
    (encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encResidue r ++ encIntVec z ++ encNat n ++ [3]).length ≤
      (encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]).length := by
  simp only [encLocal, encInstance, List.length_append, List.length_cons, List.length_nil]
  omega

private lemma inp5_length_le (I : Instance) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ) :
    (encLocal I t r ++ encVec (fun i => (z i : ℚ)) ++ encVec w ++ encRat (n : ℚ) ++ [3]).length ≤
      4 * (encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]).length := by
  simp only [List.length_append, List.length_cons, List.length_nil]
  have hz := encVec_int_length z
  have hn := encRat_nat_length n
  omega

private lemma inp_length_ge_four (I : Instance) (hI : I.Valid) (t : Fin I.τ) (r : Residue I.d)
    (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ) :
    4 ≤ (encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]).length := by
  have h1 : 1 ≤ (encIntVec z).length := by
    have he := encIntVec_ends_three hI.one_le_d z
    cases hrev : (encIntVec z).reverse with
    | nil => simp [hrev] at he
    | cons a tl =>
        have hlen := List.length_reverse (as := encIntVec z)
        rw [hrev] at hlen
        simp at hlen
        omega
  simp only [encLocal, encInstance, List.length_append, List.length_cons, List.length_nil]
  omega

private lemma pow_d_le_expBase (d : ℕ) (hd : 1 ≤ d) :
    (2 : ℝ) ^ d ≤ (2 : ℝ) ^ ((d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : (1 : ℝ) ≤ Real.logb 2 ((d : ℝ) + 1) := by
    have h1 : (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)).symm
    rw [h1]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hexp : (d : ℝ) ≤ (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1) := by
    calc (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
      _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left hdR (by positivity)
      _ = (d : ℝ) ^ 2 := (sq _).symm
      _ = (d : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1) := mul_le_mul_of_nonneg_left hlog (by positivity)
  calc (2 : ℝ) ^ d = (2 : ℝ) ^ (d : ℝ) := (Real.rpow_natCast 2 d).symm
    _ ≤ (2 : ℝ) ^ ((d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

private lemma oracleBound_eq_pow (C d L : ℕ) :
    oracleBound C d L = ((2 : ℝ) ^ ((d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1))) ^ C * (L : ℝ) ^ C := by
  unfold oracleBound
  congr 1
  rw [← Real.rpow_natCast _ C, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

private lemma bound_zero_branch (L B_exp m : ℝ) (C : ℕ)
    (hL4 : 4 ≤ L) (hB1 : 1 ≤ B_exp) (hC3 : 3 ≤ C) (hm : m ≤ 2 * L + 10) :
    m ≤ B_exp ^ C * L ^ C := by
  have h1 : 2 * L + 10 ≤ 5 * L := by linarith only [hL4]
  have h2 : (5 : ℝ) ≤ L ^ 2 := by nlinarith only [hL4]
  have h3 : 5 * L ≤ L ^ 3 := by nlinarith only [hL4, h2]
  have h4 : L ^ 3 ≤ L ^ C := pow_le_pow_right₀ (by linarith only [hL4]) hC3
  have hL_le : m ≤ L ^ C := hm.trans (h1.trans (h3.trans h4))
  calc m ≤ L ^ C := hL_le
    _ = 1 * L ^ C := (one_mul _).symm
    _ ≤ B_exp ^ C * L ^ C := mul_le_mul_of_nonneg_right (one_le_pow₀ hB1) (by positivity)

private lemma bound_pos_branch
    (L L5 Lctx Lenc B_exp pow2d ob5 m_pos m_tot out_len : ℝ)
    (C₅ C_prep C_rnd g_grow E_max C : ℕ)
    (hL4 : 4 ≤ L) (hB1 : 1 ≤ B_exp)
    (hpow2d_nn : 0 ≤ pow2d) (hpow2d_le : pow2d ≤ B_exp)
    (hL5_nn : 0 ≤ L5) (hL5 : L5 ≤ 4 * L)
    (hLctx_nn : 0 ≤ Lctx) (hLctx : Lctx ≤ L)
    (hLenc_nn : 0 ≤ Lenc) (hLenc : Lenc ≤ L5 ^ C₅)
    (hob5 : ob5 ≤ B_exp ^ C₅ * L5 ^ C₅)
    (hE1 : C₅ ≤ E_max) (hE2 : C_rnd ≤ E_max)
    (hC_E : E_max ≤ C)
    (hC_P : (2 * C_prep + 3 * C₅ + C_rnd * (3 * C₅ + 3) + 3) + g_grow + 5 ≤ C)
    (hm_pos : m_pos ≤
      ((L + 2) ^ C_prep + (ob5 + 2 * Lctx + 3) + 2 * ((2 * Lctx + 1 + L5) + 1)) +
        (Lctx + Lenc + pow2d + 2) ^ C_rnd + 2 * ((2 * Lctx + 1 + Lenc) + 1))
    (hout : out_len ≤ L + m_pos * (g_grow : ℝ))
    (hm_tot : m_tot ≤ 2 * L + m_pos + 2 * out_len + 10)
    (hm_pos_nn : 0 ≤ m_pos) :
    m_tot ≤ B_exp ^ C * L ^ C := by
  have h1_le_L : (1 : ℝ) ≤ L := by linarith only [hL4]
  have hL_pos : (0 : ℝ) < L := by linarith only [hL4]
  have h4_le_L2 : (4 : ℝ) ≤ L ^ 2 := by nlinarith only [hL4]
  have hL5_pow : L5 ^ C₅ ≤ L ^ (3 * C₅) := by
    have h1 : L5 ^ C₅ ≤ (4 * L) ^ C₅ := pow_le_pow_left₀ hL5_nn hL5 C₅
    have h2 : (4 * L) ^ C₅ ≤ L ^ (3 * C₅) := by
      rw [mul_pow, show (3 * C₅ : ℕ) = 2 * C₅ + C₅ by omega, pow_add, pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) h4_le_L2 C₅) (by positivity)
    exact h1.trans h2
  have hLenc_le : Lenc ≤ L ^ (3 * C₅) := hLenc.trans hL5_pow
  have hTprep : (L + 2) ^ C_prep ≤ L ^ (2 * C_prep) := by
    have h1 : L + 2 ≤ L ^ 2 := by nlinarith only [hL4]
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) h1 C_prep
  have hT5 : ob5 ≤ B_exp ^ C₅ * L ^ (3 * C₅) :=
    hob5.trans (mul_le_mul_of_nonneg_left hL5_pow (by positivity))
  have hTrnd : (Lctx + Lenc + pow2d + 2) ^ C_rnd ≤ B_exp ^ C_rnd * L ^ (C_rnd * (3 * C₅ + 3)) := by
    have hsum_le : Lctx + Lenc + pow2d + 2 ≤ B_exp * L ^ (3 * C₅ + 3) := by
      have h1 : Lctx + 2 ≤ L ^ 2 := by nlinarith only [hL4, hLctx]
      have hL2 : L ^ 2 ≤ L ^ (3 * C₅ + 2) := pow_le_pow_right₀ h1_le_L (by omega)
      have ho_le : Lenc ≤ L ^ (3 * C₅ + 2) := hLenc_le.trans (pow_le_pow_right₀ h1_le_L (by omega))
      have hLpow1 : (1 : ℝ) ≤ L ^ (3 * C₅ + 2) := one_le_pow₀ h1_le_L
      have hsum1 : Lctx + Lenc + pow2d + 2 ≤ B_exp * (3 * L ^ (3 * C₅ + 2)) := by
        have hctx2 : Lctx + 2 ≤ B_exp * L ^ (3 * C₅ + 2) :=
          (h1.trans hL2).trans (le_mul_of_one_le_left (by positivity) hB1)
        have hoB : Lenc ≤ B_exp * L ^ (3 * C₅ + 2) :=
          ho_le.trans (le_mul_of_one_le_left (by positivity) hB1)
        have h2dB : pow2d ≤ B_exp * L ^ (3 * C₅ + 2) :=
          hpow2d_le.trans (le_mul_of_one_le_right (by positivity) hLpow1)
        linarith only [hctx2, hoB, h2dB]
      have h3L : 3 * L ^ (3 * C₅ + 2) ≤ L ^ (3 * C₅ + 3) := by
        calc 3 * L ^ (3 * C₅ + 2) ≤ L * L ^ (3 * C₅ + 2) :=
            mul_le_mul_of_nonneg_right (by linarith only [hL4]) (by positivity)
          _ = L ^ (3 * C₅ + 3) := by rw [← pow_succ']
      exact hsum1.trans (mul_le_mul_of_nonneg_left h3L (by positivity))
    calc (Lctx + Lenc + pow2d + 2) ^ C_rnd
      _ ≤ (B_exp * L ^ (3 * C₅ + 3)) ^ C_rnd := pow_le_pow_left₀ (by positivity) hsum_le C_rnd
      _ = B_exp ^ C_rnd * L ^ (C_rnd * (3 * C₅ + 3)) := by
          rw [mul_pow, ← pow_mul, mul_comm (3 * C₅ + 3) C_rnd]
  let P₀ : ℕ := 2 * C_prep + 3 * C₅ + C_rnd * (3 * C₅ + 3) + 3
  have hpow_B : ∀ e ≤ E_max, B_exp ^ e ≤ B_exp ^ E_max := fun e he => pow_le_pow_right₀ hB1 he
  have hpow_L : ∀ p ≤ P₀, L ^ p ≤ L ^ P₀ := fun p hp => pow_le_pow_right₀ h1_le_L hp
  have hterm_prep : (L + 2) ^ C_prep ≤ B_exp ^ E_max * L ^ P₀ :=
    hTprep.trans ((hpow_L _ (by omega)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hB1)))
  have hterm_5 : ob5 ≤ B_exp ^ E_max * L ^ P₀ :=
    hT5.trans (mul_le_mul (hpow_B _ hE1) (hpow_L _ (by omega)) (by positivity) (by positivity))
  have hterm_rnd : (Lctx + Lenc + pow2d + 2) ^ C_rnd ≤ B_exp ^ E_max * L ^ P₀ :=
    hTrnd.trans (mul_le_mul (hpow_B _ hE2) (hpow_L _ (by omega)) (by positivity) (by positivity))
  have hterm_thr_overhead : 2 * Lctx + 3 ≤ B_exp ^ E_max * L ^ P₀ := by
    have h1 : 2 * Lctx + 3 ≤ L ^ 2 := by nlinarith only [hL4, hLctx]
    exact h1.trans ((hpow_L 2 (by omega)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hB1)))
  have hframe1 : 2 * ((2 * Lctx + 1 + L5) + 1) ≤ B_exp ^ E_max * L ^ P₀ := by
    have h1 : 2 * ((2 * Lctx + 1 + L5) + 1) ≤ 12 * L + 4 := by linarith only [hLctx, hL5]
    have h2 : 12 * L + 4 ≤ L ^ 3 := by
      have hL3 : L ^ 3 = L ^ 2 * L := by ring
      nlinarith only [hL4, h4_le_L2, hL3]
    exact (h1.trans h2).trans ((hpow_L 3 (by omega)).trans
      (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hB1)))
  have hframe2 : 2 * ((2 * Lctx + 1 + Lenc) + 1) ≤ 3 * (B_exp ^ E_max * L ^ P₀) := by
    have h1 : 2 * ((2 * Lctx + 1 + Lenc) + 1) ≤ 4 * L + 4 + 2 * L ^ (3 * C₅) := by
      linarith only [hLctx, hLenc_le]
    have h4L4 : 4 * L + 4 ≤ L ^ 3 := by
      have hL3 : L ^ 3 = L ^ 2 * L := by ring
      nlinarith only [hL4, h4_le_L2, hL3]
    have hp1 : L ^ 3 ≤ L ^ P₀ := hpow_L 3 (by omega)
    have hp2 : L ^ (3 * C₅) ≤ L ^ P₀ := hpow_L (3 * C₅) (by omega)
    have h3 : 4 * L + 4 + 2 * L ^ (3 * C₅) ≤ 3 * L ^ P₀ := by linarith only [h4L4, hp1, hp2]
    have h4 : 3 * L ^ P₀ ≤ 3 * (B_exp ^ E_max * L ^ P₀) := by
      calc 3 * L ^ P₀ = 3 * (1 * L ^ P₀) := by ring
        _ ≤ 3 * (B_exp ^ E_max * L ^ P₀) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (one_le_pow₀ hB1) (by positivity)) (by norm_num)
    exact h1.trans (h3.trans h4)
  have hm_pos_le : m_pos ≤ B_exp ^ E_max * L ^ (P₀ + 2) := by
    have hsum8 : m_pos ≤ 8 * (B_exp ^ E_max * L ^ P₀) := by
      linarith only [hm_pos, hterm_prep, hterm_5, hterm_thr_overhead, hframe1, hterm_rnd, hframe2]
    have h8 : (8 : ℝ) ≤ L ^ 2 := by nlinarith only [hL4]
    calc m_pos ≤ 8 * (B_exp ^ E_max * L ^ P₀) := hsum8
      _ ≤ L ^ 2 * (B_exp ^ E_max * L ^ P₀) := mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = B_exp ^ E_max * L ^ (P₀ + 2) := by rw [pow_add]; ring
  have hgrow_le : 1 + 2 * (g_grow : ℝ) ≤ L ^ (g_grow + 1) := by
    have aux : ∀ k : ℕ, (1 + 2 * (k : ℝ)) ≤ (4 : ℝ) ^ (k + 1) := fun k => by
      induction k with
      | zero => norm_num
      | succ k ih =>
          push_cast
          rw [pow_succ']
          have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
          linarith only [ih, h1]
    exact (aux g_grow).trans (pow_le_pow_left₀ (by norm_num) hL4 (g_grow + 1))
  have hm_tot_le : m_tot ≤ B_exp ^ E_max * L ^ (P₀ + g_grow + 5) := by
    have htot1 : m_tot ≤ (4 * L + 10) + (1 + 2 * (g_grow : ℝ)) * m_pos := by
      linarith only [hm_tot, hout]
    have h410 : 4 * L + 10 ≤ L ^ 3 := by
      have hL3 : L ^ 3 = L ^ 2 * L := by ring
      nlinarith only [hL4, h4_le_L2, hL3]
    have h1 : 4 * L + 10 ≤ B_exp ^ E_max * L ^ (P₀ + g_grow + 3) :=
      h410.trans ((pow_le_pow_right₀ h1_le_L (by omega)).trans
        (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hB1)))
    have h2 : (1 + 2 * (g_grow : ℝ)) * m_pos ≤ B_exp ^ E_max * L ^ (P₀ + g_grow + 3) := by
      calc (1 + 2 * (g_grow : ℝ)) * m_pos
        _ ≤ L ^ (g_grow + 1) * (B_exp ^ E_max * L ^ (P₀ + 2)) :=
            mul_le_mul hgrow_le hm_pos_le hm_pos_nn (by positivity)
        _ = B_exp ^ E_max * L ^ (P₀ + g_grow + 3) := by
            rw [show P₀ + g_grow + 3 = (g_grow + 1) + (P₀ + 2) by omega, pow_add]; ring
    have hsum2 : m_tot ≤ 2 * (B_exp ^ E_max * L ^ (P₀ + g_grow + 3)) := by
      linarith only [htot1, h1, h2]
    have h2_le_L2 : (2 : ℝ) ≤ L ^ 2 := by nlinarith only [hL4]
    calc m_tot ≤ 2 * (B_exp ^ E_max * L ^ (P₀ + g_grow + 3)) := hsum2
      _ ≤ L ^ 2 * (B_exp ^ E_max * L ^ (P₀ + g_grow + 3)) :=
          mul_le_mul_of_nonneg_right h2_le_L2 (by positivity)
      _ = B_exp ^ E_max * L ^ (P₀ + g_grow + 5) := by rw [pow_add]; ring
  calc m_tot ≤ B_exp ^ E_max * L ^ (P₀ + g_grow + 5) := hm_tot_le
    _ ≤ B_exp ^ C * L ^ C :=
        mul_le_mul (pow_le_pow_right₀ hB1 hC_E)
          (pow_le_pow_right₀ h1_le_L (by exact hC_P)) (by positivity) (by positivity)

end Assembly

end IntConeFPT.Lemma6Proof

open IntConeFPT.Lemma6Proof

theorem solution :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid →
      ∀ (t : Fin I.τ) (r : Residue I.d) (z : Fin I.d → ℤ) (w : Fin I.k → ℚ) (n : ℕ),
        ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) ∈ I.Cr t r →
        let inp := encLocal I t r ++ encIntVec z ++ encVec w ++ encNat n ++ [3]
        ∃ out : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ),
          out.length ≤ 2 ^ (I.d + 1) - 1 ∧
          (out.map fun e => (e.1, e.2.1)).Nodup ∧
          (∀ e ∈ out, 1 ≤ e.2.2 ∧ (certGen e).toReal ∈ I.Pr t r ∧ certGen e ∈ I.S t) ∧
          (out.map fun e => (e.2.2 : ℝ) • (certGen e).toReal).sum =
            ((fun i => (z i : ℝ)), fun j => (w j : ℝ)) ∧
          (out.map fun e => e.2.2).sum = n ∧
          (((out.map fun e => (e.2.2 : ℝ) * I.f t (fun i => (e.1 i : ℝ))).sum : ℝ) : EReal) ≤
            I.Phi t r ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), (n : ℝ)) ∧
          RunsWithin M inp (encCert out) (oracleBound C I.d inp.length) := by
  obtain ⟨C₅, M₅, hM₅⟩ := IntConeFPT.lemma_5
  obtain ⟨C_prep, P_prep, hPrep⟩ := IntConeFPT.lemma_6_prep_writer
  obtain ⟨C_rnd, P_rnd, hRnd⟩ := IntConeFPT.lemma_6_round_writer
  obtain ⟨M₅_thr, hThr⟩ := IntConeFPT.runsWithin_thread M₅
  obtain ⟨W₁, hW₁⟩ := IntConeFPT.runsWithin_chain P_prep M₅_thr
  obtain ⟨M_pos, hW₂⟩ := IntConeFPT.runsWithin_chain W₁ P_rnd
  obtain ⟨g_grow, hg_grow⟩ : ∃ g : ℕ, tmGrowth M_pos.tm = g := ⟨tmGrowth M_pos.tm, rfl⟩
  obtain ⟨E_max, hE_eq⟩ : ∃ e : ℕ, e = max C₅ C_rnd := ⟨_, rfl⟩
  obtain ⟨P_max, hP_eq⟩ : ∃ p : ℕ,
      p = 2 * C_prep + 3 * C₅ + C_rnd * (3 * C₅ + 3) + g_grow + 10 := ⟨_, rfl⟩
  obtain ⟨C, hC_eq⟩ : ∃ c : ℕ, c = max E_max P_max + 2 := ⟨_, rfl⟩
  have hE1 : C₅ ≤ E_max := by rw [hE_eq]; exact le_max_left _ _
  have hE2 : C_rnd ≤ E_max := by rw [hE_eq]; exact le_max_right _ _
  have hC_E : E_max ≤ C := by omega
  have hC_P : (2 * C_prep + 3 * C₅ + C_rnd * (3 * C₅ + 3) + 3) + g_grow + 5 ≤ C := by omega
  have hC3 : 3 ≤ C := by omega
  refine ⟨C, branchZeroMachine M_pos, fun I hI t r z w n hCr => ?_⟩
  intro inp
  have hL_ge4 : 4 ≤ inp.length := inp_length_ge_four I hI t r z w n
  have hL_ge2 : (2 : ℝ) ≤ (inp.length : ℝ) := by exact_mod_cast (by omega : 2 ≤ inp.length)
  have hL_pos : (0 : ℝ) < (inp.length : ℝ) := by linarith
  have h1_le_B : (1 : ℝ) ≤ (2 : ℝ) ^ ((I.d : ℝ) ^ 2 * Real.logb 2 ((I.d : ℝ) + 1)) := by
    have h := pow_d_le_expBase I.d hI.one_le_d
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ I.d := by exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ I.d)
    exact h1.trans h
  by_cases hn0 : n = 0
  · subst hn0
    have hzero : ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), ((0 : ℕ) : ℝ)) = 0 := by
      rcases hCr with h0 | hpos
      · simpa using Set.mem_singleton_iff.mp h0
      · exfalso; have hlt := hpos.1; simp at hlt
    have hz0 : ∀ i, z i = 0 := fun i => by
      have hi := congr_arg (fun p : Pt I.d I.k => p.1 i) hzero
      simp at hi
      exact_mod_cast hi
    have hw0 : ∀ j, w j = 0 := fun j => by
      have hj := congr_arg (fun p : Pt I.d I.k => p.2.1 j) hzero
      simp at hj
      exact_mod_cast hj
    refine ⟨[], by simp, by simp, by simp, ?_, by simp, ?_, ?_⟩
    · ext i <;> simp [hz0, hw0]
    · have hzero' : ((fun i => (z i : ℝ)), (fun j => (w j : ℝ)), ((0 : ℕ) : ℝ)) = 0 := hzero
      rw [hzero', Phi_zero]
      simp
    · have hinp0 : inp = (encLocal I t r ++ encIntVec z ++ encVec w) ++ [3] := by
        simp [inp, encNat_zero]
      obtain ⟨m, hm, hrun⟩ := branchZeroMachine_zero M_pos (encLocal I t r ++ encIntVec z ++ encVec w)
        (lemma6_prefix_ends_three I hI t r z w)
      refine ⟨m, ?_, ?_⟩
      · have hm_le : (m : ℝ) ≤ 2 * (inp.length : ℝ) + 10 := by
          rw [hinp0]
          refine hm.trans_eq ?_
          push_cast
          ring
        have hL4 : (4 : ℝ) ≤ (inp.length : ℝ) := by exact_mod_cast hL_ge4
        rw [oracleBound_eq_pow]
        exact bound_zero_branch (inp.length : ℝ)
          ((2 : ℝ) ^ ((I.d : ℝ) ^ 2 * Real.logb 2 ((I.d : ℝ) + 1))) (m : ℝ) C
          hL4 h1_le_B hC3 hm_le
      · rw [hinp0]
        exact hrun
  · have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hSr_ne : (I.Sr t r).Nonempty := nonempty_Sr_of_Cr_pos I t r hn hCr
    have hCr5 : ((ratPair (fun i => (z i : ℚ)) w).1, (ratPair (fun i => (z i : ℚ)) w).2,
        ((n : ℚ) : ℝ)) ∈ I.Cr t r := by simpa [ratPair] using hCr
    obtain ⟨o, ho_phi, _, _, ho_len, _, ho_Sr, ho_aggr, ho_sum, ho_cost, ho_enc, ho_run⟩ :=
      hM₅ I hI t r (fun i => (z i : ℚ)) w (n : ℚ) hSr_ne hCr5
    have hround := round_correct I hI t r z w n hn o ho_phi ho_len ho_Sr ho_aggr ho_sum ho_cost
    have hrep_sumQ : (o.2.2.2.map fun e => e.2.2).sum = (n : ℚ) := by
      have hsumR : (((o.2.2.2.map fun e => e.2.2).sum : ℚ) : ℝ) = ((n : ℚ) : ℝ) := by
        rw [← list_sum_ratCast_real o.2.2.2 (fun e => e.2.2), ho_sum, Rat.cast_natCast]
      exact Rat.cast_injective hsumR
    set rep := o.2.2.2
    set q := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => ⌊e.2.2⌋₊
    set δ := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => e.2.2 - (q e : ℚ)
    set ρ := fun e : (Fin I.d → ℤ) × (Fin I.k → ℚ) × ℚ => ⌊((2 ^ I.d : ℕ) : ℚ) * δ e⌋₊
    set ℓ := n - (rep.map q).sum
    set poolIdx := (List.finRange rep.length).flatMap fun idx => List.replicate (ρ (rep.get idx)) idx
    set usedIdx := poolIdx.take (2 ^ I.d * (ℓ - 1))
    set chunk := fun j : Fin (ℓ - 1) => (usedIdx.drop (j.1 * 2 ^ I.d)).take (2 ^ I.d)
    set xAvg := fun (j : Fin (ℓ - 1)) (i : Fin I.d) =>
      ((r i : ℕ) : ℤ) + ((chunk j).map fun idx => ((rep.get idx).1 i - ((r i : ℕ) : ℤ)) / (2 ^ I.d : ℤ)).sum
    set uAvg := fun (j : Fin (ℓ - 1)) (i : Fin I.k) =>
      ((chunk j).map fun idx => (rep.get idx).2.1 i).sum / ((2 ^ I.d : ℕ) : ℚ)
    set β := fun idx : Fin rep.length => δ (rep.get idx) - (usedIdx.count idx : ℚ) / ((2 ^ I.d : ℕ) : ℚ)
    set xFinal := fun i : Fin I.d =>
      z i - (rep.map fun e => (q e : ℤ) * e.1 i).sum - ((List.finRange (ℓ - 1)).map fun j => xAvg j i).sum
    set uFinal := fun i : Fin I.k =>
      ((List.finRange rep.length).map fun idx => β idx * (rep.get idx).2.1 i).sum
    set raw : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) :=
      if ℓ = 0 then rep.map fun e => (e.1, e.2.1, q e)
      else (rep.filterMap fun e => if q e = 0 then none else some (e.1, e.2.1, q e)) ++
           ((List.finRange (ℓ - 1)).map fun j => (xAvg j, uAvg j, 1)) ++
           [(xFinal, uFinal, 1)]
    set out : List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ) :=
      raw.foldr (fun e acc =>
        if acc.any (fun h => decide ((h.1, h.2.1) = (e.1, e.2.1))) then
          acc.map (fun h => if (h.1, h.2.1) = (e.1, e.2.1) then (h.1, h.2.1, h.2.2 + e.2.2) else h)
        else e :: acc) []
    refine ⟨out, hround.1, hround.2.1, hround.2.2.1, hround.2.2.2.1, hround.2.2.2.2.1,
      hround.2.2.2.2.2, ?_⟩
    -- Machine time bound for M_pos and branchZeroMachine M_pos
    let ctx := encNat I.d ++ [3] ++ encNat I.k ++ [3] ++ encResidue r ++ encIntVec z ++ encNat n ++ [3]
    let inp5 := encLocal I t r ++ encVec (fun i => (z i : ℚ)) ++ encVec w ++ encRat (n : ℚ) ++ [3]
    let frame := fun (x y : List Sym) => x.flatMap (fun s => [(0 : Sym), s]) ++ 1 :: y
    have hrun_prep := hPrep I hI t r z w n hn
    have hrun_thr5 := hThr ctx inp5 (encOracle o) (oracleBound C₅ I.d inp5.length) ho_run
    have hrun_W1 := hW₁ inp (frame ctx inp5) (frame ctx (encOracle o)) _ _ hrun_prep hrun_thr5
    have hrep_len : o.2.2.2.length ≤ 2 ^ I.d := ho_len.trans (min_le_left _ _)
    have hrun_rnd := hRnd I.d I.k hI.one_le_d r z n hn o hrep_len
      (fun e he => (ho_Sr e he).2) hrep_sumQ
    have hrun_pos := hW₂ inp (frame ctx (encOracle o)) (encCert out) _ _ hrun_W1 hrun_rnd
    obtain ⟨m_pos, hm_pos, ⟨hm_pos_run⟩⟩ := hrun_pos
    have hout_len : (encCert out).length ≤ inp.length + m_pos * g_grow := by
      rw [← hg_grow]
      have hlen := tm2_output_length_le hm_pos_run
      simpa only [List.length_map] using hlen
    have hm_br := branchZeroMachine_pos M_pos (encLocal I t r ++ encIntVec z ++ encVec w) hn
      (encCert out) ⟨m_pos, le_rfl, ⟨hm_pos_run⟩⟩
    obtain ⟨m_tot, hm_tot, hrun_tot⟩ := hm_br
    refine ⟨m_tot, ?_, hrun_tot⟩
    -- Asymptotic bound: m_tot ≤ oracleBound C I.d inp.length
    let B_exp : ℝ := (2 : ℝ) ^ ((I.d : ℝ) ^ 2 * Real.logb 2 ((I.d : ℝ) + 1))
    have hL4 : (4 : ℝ) ≤ (inp.length : ℝ) := by exact_mod_cast hL_ge4
    have hL5 : (inp5.length : ℝ) ≤ 4 * (inp.length : ℝ) := by
      exact_mod_cast inp5_length_le I t r z w n
    have hctx : (ctx.length : ℝ) ≤ (inp.length : ℝ) := by
      exact_mod_cast ctx_length_le_inp I t r z w n
    have ho_encR : ((encOracle o).length : ℝ) ≤ (inp5.length : ℝ) ^ C₅ := by
      exact_mod_cast ho_enc
    have hob5 : oracleBound C₅ I.d inp5.length = B_exp ^ C₅ * (inp5.length : ℝ) ^ C₅ :=
      oracleBound_eq_pow C₅ I.d inp5.length
    have hfl1 : ((frame ctx inp5).length : ℝ) =
        2 * (ctx.length : ℝ) + 1 + (inp5.length : ℝ) := by
      have hlen : (frame ctx inp5).length = 2 * ctx.length + 1 + inp5.length := by
        simp [frame, List.length_flatMap]; ring
      exact_mod_cast hlen
    have hfl2 : ((frame ctx (encOracle o)).length : ℝ) =
        2 * (ctx.length : ℝ) + 1 + ((encOracle o).length : ℝ) := by
      have hlen : (frame ctx (encOracle o)).length = 2 * ctx.length + 1 + (encOracle o).length := by
        simp [frame, List.length_flatMap]; ring
      exact_mod_cast hlen
    have hm_pos_cast : (m_pos : ℝ) ≤
        (((inp.length : ℝ) + 2) ^ C_prep + (oracleBound C₅ I.d inp5.length + 2 * (ctx.length : ℝ) + 3) +
          2 * ((2 * (ctx.length : ℝ) + 1 + (inp5.length : ℝ)) + 1)) +
          ((ctx.length : ℝ) + ((encOracle o).length : ℝ) + (2 ^ I.d : ℝ) + 2) ^ C_rnd +
          2 * ((2 * (ctx.length : ℝ) + 1 + ((encOracle o).length : ℝ)) + 1) := by
      rw [← hfl1, ← hfl2]
      exact hm_pos
    have houtR : ((encCert out).length : ℝ) ≤ (inp.length : ℝ) + (m_pos : ℝ) * (g_grow : ℝ) := by
      exact_mod_cast hout_len
    rw [oracleBound_eq_pow]
    exact bound_pos_branch (inp.length : ℝ) (inp5.length : ℝ) (ctx.length : ℝ)
      ((encOracle o).length : ℝ) B_exp (2 ^ I.d : ℝ) (oracleBound C₅ I.d inp5.length)
      (m_pos : ℝ) (m_tot : ℝ) ((encCert out).length : ℝ)
      C₅ C_prep C_rnd g_grow E_max C
      hL4 h1_le_B (by norm_num) (pow_d_le_expBase I.d hI.one_le_d)
      (Nat.cast_nonneg _) hL5 (Nat.cast_nonneg _) hctx (Nat.cast_nonneg _) ho_encR
      (le_of_eq hob5) hE1 hE2 hC_E hC_P hm_pos_cast houtR hm_tot (Nat.cast_nonneg _)

