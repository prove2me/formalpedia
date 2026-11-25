-- Prove2me | solution 1 for IntConeFPT.threshold_bisection_machine
-- status  : ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T14:08:04.342207+00:00
-- url     : https://prove2.me/submissions/f39aa21f-6c10-4dfb-abc3-a956ed9d147e

import Definitions.Def_IntConeFPT_Machine
import Definitions.Def_OnlineCRS_Combine_encNat

open Turing IntConeFPT OnlineCRS.Combine Function
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/- Stack volume accounting adapted from Prove2Me submission 70c7eb16-aa64-45fc-9619-d6fd621972a7 (Apache-2.0). -/
open Turing
/-! ### Growth and size bounds (from the swarm's `Growth.lean`) -/

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing

namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing

namespace IntConeFPT.QueryVM
noncomputable section
abbrev Key (M : Machine) (R : Type) := M.tm.K ⊕ R
abbrev G (M : Machine) (R : Type) : Key M R → Type
  | .inl k => M.tm.Γ k
  | .inr _ => Sym
-- Each invocation returns to a controller label after emptying the oracle output stack.
abbrev Lab (M : Machine) (R : Type) (PC : Type) := PC ⊕ (PC × (M.tm.Λ ⊕ Unit))
abbrev St (M : Machine) := M.tm.σ × Option Sym
variable {R PC : Type} [DecidableEq R]
abbrev Code (M : Machine) (R PC : Type) := TM2.Stmt (G M R) (Lab M R PC) (St M)
def pack (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) :
    ∀ k, List (G M R k)
  | .inl k => s k
  | .inr r => b r

lemma upd (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) (k : M.tm.K) (v : List (M.tm.Γ k)) :
    update (pack M s b) (.inl k) v = pack M (update s k v) b := by
  funext i; cases i with
  | inr u => simp [pack]
  | inl i =>
    by_cases h : i=k
    · subst i; simp [pack]
    · simp [pack,update,h]

lemma tmp (M : Machine) (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) (i : R) (v : List Sym) :
    update (pack M s b) (.inr i) v = pack M s (update b i v) := by
  funext j; cases j with
  | inl => simp [pack]
  | inr j =>
    by_cases h : j=i
    · subst j; simp [pack]
    · simp [pack,update,h]

def tr (M : Machine) (ret : PC) : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ → Code M R PC
  | .push k f q => .push (.inl k) (fun s => f s.1) (tr M ret q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o,s.2)) (tr M ret q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o,s.2)) (tr M ret q)
  | .load f q => .load (fun s => (f s.1,s.2)) (tr M ret q)
  | .branch f q r => .branch (fun s => f s.1) (tr M ret q) (tr M ret r)
  | .goto f => .goto (fun s => .inr (ret,.inl (f s.1)))
  | .halt => .goto (fun _ => .inr (ret,.inr ()))

def loc (M : Machine) (ret : PC) : Option M.tm.Λ → Option (Lab M R PC)
  | none => some (.inr (ret,.inr ()))
  | some l => some (.inr (ret,.inl l))

def liftCfg (M : Machine) (ret : PC) (c : M.tm.Cfg) (b : R → List Sym) : TM2.Cfg (G M R) (Lab M R PC) (St M) :=
  ⟨loc M ret c.l,(c.var,none),pack M c.stk b⟩

lemma trStep (M : Machine) (ret : PC) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) (v : M.tm.σ)
    (s : ∀ k, List (M.tm.Γ k)) (b : R → List Sym) :
    TM2.stepAux (tr M ret q) (v,none) (pack M s b) = liftCfg M ret (TM2.stepAux q v s) b := by
  induction q generalizing v s with
  | push k f q ih => simpa only [tr,TM2.stepAux,upd,pack] using ih (v:=v) (s:=update s k (f v :: s k))
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [tr,TM2.stepAux,upd]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ih jh => cases h : f v <;> simp [tr,TM2.stepAux,h,ih,jh]
  | goto f => rfl
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

def cleared (s : Mem R) (r : R) := update s r []
def drained (s : Mem R) (r : R) (f : R → Sym → Word) : Mem R :=
  fun j => if j=r then [] else (s r).reverse.flatMap (f j) ++ s j

-- A bounded trace for a word-register command. The oracle port is reversed on
-- both sides of a call, so the two stack transfers require no extra buffer.
inductive Eval (M : Machine) (port : R) : Cmd R → Mem R → Mem R → ℕ → Prop
  | put (s r w) : Eval M port (.put r w) s (update s r (w ++ s r)) 1
  | drop (s r) : Eval M port (.drop r) s (update s r (s r).tail) 1
  | drain (s r f) : Eval M port (.drain r f) s (drained s r f) ((s r).length+1)
  | call (s : Mem R) (x y : Word) (n : ℕ) (hx : s port = x.reverse)
      (hr : Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun)
        (some (y.map M.outputAlphabet.invFun)) n)) :
      Eval M port .call s (update s port y.reverse) (x.length+n+y.length+2)
  | seq {a b s t u h k} : Eval M port a s t h → Eval M port b t u k → Eval M port (.seq a b) s u (h+k)
  | yes {r p a b s t h} : p (s r).head? = true → Eval M port a s t h → Eval M port (.cond r p a b) s t (1+h)
  | no {r p a b s t h} : p (s r).head? = false → Eval M port b s t h → Eval M port (.cond r p a b) s t (1+h)
  | stop {r p a s} : p (s r).head? = false → Eval M port (.loop r p a) s s 1
  | more {r p a s t u h k} : p (s r).head? = true → Eval M port a s t h →
      Eval M port (.loop r p a) t u k → Eval M port (.loop r p a) s u (1+h+k)
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
  | .cond r p a b,g,_,none => .branch r (fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
  | .cond _ _ a _,g,k,some (.inl i) => asm a (fun i => g (some (.inl i))) k i
  | .cond _ _ _ b,g,k,some (.inr i) => asm b (fun i => g (some (.inr i))) k i
  | .loop r p a,g,k,none => .branch r (fun o => if p o then g (some (entry a)) else k)
  | .loop _ _ a,g,_,some i => asm a (g ∘ some) (g none) i

def pushWord {M : Machine} (k : R) (w : Word) (q : Code M R PC) : Code M R PC :=
  w.reverse.foldr (fun s q => .push (.inr k) (fun _ => s) q) q

lemma pushWord_aux {M : Machine} (k : R) (w : Word) (q : Code M R PC) v h s :
    TM2.stepAux (pushWord k w q) v (pack M h s) =
      TM2.stepAux q v (pack M h (update s k (w ++ s k))) := by
  have aux (xs : Word) (s : Mem R) :
      TM2.stepAux (xs.foldr (fun a q => TM2.Stmt.push (.inr k) (fun _ => a) q) q) v (pack M h s) =
        TM2.stepAux q v (pack M h (update s k (xs.reverse ++ s k))) := by
    induction xs generalizing s with
    | nil => simp
    | cons a xs ih =>
      simp only [List.foldr_cons,TM2.stepAux,tmp,pack,ih,update_self,update_idem]
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
    rw [show pushAll (k::ks) f q = pushWord k (f k) (pushAll ks f q) from rfl,pushWord_aux,
      ih _ (List.nodup_cons.mp hn).2]
    congr 2; funext i
    by_cases he : i=k
    · subst i; simp [(List.nodup_cons.mp hn).1]
    · simp [he,update_of_ne he]

def stopAt {M : Machine} (k : PC) : Code M R PC :=
  .load (fun _ => (M.tm.initialState,none)) (.goto (fun _ => .inl k))

def onSym {M : Machine} (f : Sym → Code M R PC) : Code M R PC :=
  .branch (fun v => decide (v.2 = some 0)) (f 0)
    (.branch (fun v => decide (v.2 = some 1)) (f 1)
      (.branch (fun v => decide (v.2 = some 2)) (f 2) (f 3)))
lemma onSym_aux {M : Machine} (f : Sym → Code M R PC) (sym : Sym) s :
    TM2.stepAux (onSym f) (M.tm.initialState,some sym) s =
      TM2.stepAux (f sym) (M.tm.initialState,some sym) s := by fin_cases sym <;> rfl

variable [Fintype R]
noncomputable def program (M : Machine) (port : R) (pg : PC → Ins R PC) : Lab M R PC → Code M R PC
  | .inr (ret,.inl l) => tr M ret (M.tm.m l)
  | .inr (ret,.inr ()) =>
    .pop (.inl M.tm.k₁) (fun _ o => (M.tm.initialState,o.map M.outputAlphabet))
      (.branch (fun v => v.2.isSome)
        (.push (.inr port) (fun v => v.2.getD 0)
          (.load (fun _ => (M.tm.initialState,none)) (.goto (fun _ => .inr (ret,.inr ())))))
        (stopAt ret))
  | .inl i =>
    match pg i with
    | .halt => .halt
    | .put r w k => pushWord r w (stopAt k)
    | .drop r k => .pop (.inr r) (fun s _ => s) (stopAt k)
    | .branch r f => .peek (.inr r) (fun s o => (s.1,o)) (.goto (fun v => .inl (f v.2)))
    | .drain r f k =>
      .pop (.inr r) (fun s o => (s.1,o)) (.branch (fun v => v.2.isSome)
        (onSym (fun a => pushAll Finset.univ.toList (fun j => if j=r then [] else f j a) (stopAt i)))
        (stopAt k))
    | .call k =>
      .pop (.inr port) (fun s o => (s.1,o)) (.branch (fun v => v.2.isSome)
        (.push (.inl M.tm.k₀) (fun v => M.inputAlphabet.symm (v.2.getD 0)) (stopAt i))
        (.load (fun _ => (M.tm.initialState,none)) (.goto (fun _ => .inr (k,.inl M.tm.main)))))

-- Branch must leave the finite buffer clear. A further branch on the five
-- possible peek values allows the continuation to be hardwired before reset.
noncomputable def code (M : Machine) (port : R) (pg : PC → Ins R PC) : Lab M R PC → Code M R PC
  | .inl i =>
    match pg i with
    | .branch r f => .peek (.inr r) (fun s o => (s.1,o))
        (.branch (fun v => v.2.isSome) (onSym fun a => stopAt (f (some a))) (stopAt (f none)))
    | _ => program M port pg (.inl i)
  | .inr k => program M port pg (.inr k)

abbrev Cfg (M : Machine) (R PC : Type) := TM2.Cfg (G M R) (Lab M R PC) (St M)
def cfg (M : Machine) (i : PC) (s : Mem R) : Cfg M R PC :=
  ⟨some (.inl i),(M.tm.initialState,none),pack M (fun _ => []) s⟩

def Reach {α : Type} (f : α → Option α) (n : ℕ) (u v : α) :=
  ∃ k ≤ n, (flip Option.bind f)^[k] (some u) = some v
namespace Reach
variable {α : Type} {f : α → Option α} {a b c : α} {h k : ℕ}
theorem refl : Reach f 0 a a := ⟨0,le_rfl,rfl⟩
theorem one (he : f a = some b) : Reach f 1 a b := ⟨1,le_rfl,he⟩
theorem trans (x : Reach f h a b) (y : Reach f k b c) : Reach f (h+k) a c := by
  obtain ⟨h',hl,he⟩ := x; obtain ⟨k',kl,ke⟩ := y
  exact ⟨k'+h',by omega,by rw [Function.iterate_add_apply,he,ke]⟩
theorem mono (x : Reach f h a b) (hl : h ≤ k) : Reach f k a b := by
  obtain ⟨t,ht,he⟩ := x; exact ⟨t,ht.trans hl,he⟩
end Reach

abbrev step (M : Machine) (port : R) (pg : PC → Ins R PC) := TM2.step (code M port pg)

private lemma br {M : Machine} {port : R} {pg : PC → Ins R PC} {i k f}
    (he : pg i = .branch k f) (s : Mem R) :
    Reach (step M port pg) 1 (cfg M i s) (cfg M (f (s k).head?) s) := by
  apply Reach.one
  cases h : (s k).head? with
  | none => simp [cfg,step,code,he,TM2.step,TM2.stepAux,pack,h,stopAt]
  | some a => simp [cfg,step,code,he,TM2.step,TM2.stepAux,pack,h,onSym_aux,stopAt]

private lemma bulk {M : Machine} {port : R} {pg : PC → Ins R PC} {i r f k}
    (he : pg i = .drain r f k) (s : Mem R) :
    Reach (step M port pg) ((s r).length+1) (cfg M i s) (cfg M k (drained s r f)) := by
  generalize hx : s r = xs
  induction xs generalizing s with
  | nil =>
    apply Reach.one
    have eq : update s r [] = drained s r f := by funext j; simp [drained,hx,update_apply]
    simp [cfg,code,step,program,he,TM2.step,TM2.stepAux,pack,hx,tmp,stopAt,eq]
  | cons a xs ih =>
    let t := fun j => if j=r then xs else f j a ++ s j
    have h1 : step M port pg (cfg M i s) = some (cfg M i t) := by
      simp only [cfg,step,TM2.step,code,he,program,TM2.stepAux,pack,hx,List.head?_cons,List.tail_cons,
        Option.isSome_some,Bool.cond_true,tmp,onSym_aux,pushAll_aux _ _ _ _ _ _ Finset.univ.nodup_toList,
        Finset.mem_toList,Finset.mem_univ,if_true,stopAt]
      congr 3; funext j; by_cases h : j=r <;> simp_all [t,update]
    have h2 := ih t (by simp [t])
    have eq : drained t r f = drained s r f := by
      funext j; by_cases h : j=r <;> simp [drained,t,h,hx,List.flatMap_append,List.append_assoc]
    rw [eq] at h2
    exact ((Reach.one h1).trans h2).mono (by simp; omega)

private abbrev io (M : Machine) (k : M.tm.K) (w : List (M.tm.Γ k)) : ∀ j, List (M.tm.Γ j) :=
  update (fun _ => []) k w
private lemma io_init (M : Machine) w : (initList M.tm w).stk = io M M.tm.k₀ w := by
  funext k; by_cases h : k=M.tm.k₀
  · subst k; simp [initList,io]
  · simp [h,initList,io,update]
private lemma io_halt (M : Machine) w : (haltList M.tm w).stk = io M M.tm.k₁ w := by
  funext k; by_cases h : k=M.tm.k₁
  · subst k; simp [haltList,io]
  · simp [h,haltList,io,update]
private def cc (M : Machine) (l : Lab M R PC) (s : Mem R) (j : M.tm.K) (w : List (M.tm.Γ j)) :
    Cfg M R PC := ⟨some l,(M.tm.initialState,none),pack M (io M j w) s⟩

private lemma load_call (M : Machine) (port : R) (pg : PC → Ins R PC) {i k} (he : pg i = .call k)
    (s : Mem R) (x w : Word) :
    Reach (step M port pg) (x.length+1)
      (cc M (.inl i) (update s port x) M.tm.k₀ (w.map M.inputAlphabet.symm))
      (liftCfg M k (initList M.tm ((x.reverse ++ w).map M.inputAlphabet.symm)) (update s port [])) := by
  induction x generalizing w with
  | nil =>
    apply Reach.one
    simp [cc,step,code,program,he,TM2.step,TM2.stepAux,pack,tmp,update_idem,stopAt,liftCfg,loc,io_init] <;> exact ⟨rfl,rfl⟩
  | cons a x ih =>
    have h1 : step M port pg (cc M (.inl i) (update s port (a::x)) M.tm.k₀ (w.map M.inputAlphabet.symm)) =
        some (cc M (.inl i) (update s port x) M.tm.k₀ ((a::w).map M.inputAlphabet.symm)) := by
      simp [cc,step,code,program,he,TM2.step,TM2.stepAux,pack,tmp,upd,io,update_idem,stopAt] <;> rfl
    have hh := (Reach.one h1).trans (ih (a::w))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using hh

private lemma unload (M : Machine) (port : R) (pg : PC → Ins R PC) (k) (s : Mem R) (y w : Word) :
    Reach (step M port pg) (y.length+1)
      (cc M (.inr (k,.inr ())) (update s port w) M.tm.k₁ (y.map M.outputAlphabet.symm))
      (cfg M k (update s port (y.reverse ++ w))) := by
  induction y generalizing w with
  | nil =>
    apply Reach.one
    have hh : io M M.tm.k₁ [] = fun _ => [] := by funext j; by_cases h : j=M.tm.k₁ <;> simp_all [io]
    simp [cc,step,code,program,TM2.step,TM2.stepAux,pack,upd,io,update_idem,stopAt,cfg,hh] <;> rfl
  | cons a y ih =>
    have h1 : step M port pg (cc M (.inr (k,.inr ())) (update s port w) M.tm.k₁ ((a::y).map M.outputAlphabet.symm)) =
        some (cc M (.inr (k,.inr ())) (update s port (a::w)) M.tm.k₁ (y.map M.outputAlphabet.symm)) := by
      simp [cc,step,code,program,TM2.step,TM2.stepAux,pack,upd,tmp,io,update_idem] <;> rfl
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using (Reach.one h1).trans (ih (a::w))

private lemma sim_oracle (M : Machine) (port : R) (pg : PC → Ins R PC) (k : PC) (s : Mem R)
    (n : ℕ) (c d : M.tm.Cfg) (hr : (flip Option.bind M.tm.step)^[n] (some c) = some d) :
    Reach (step M port pg) n (liftCfg M k c s) (liftCfg M k d s) := by
  induction n generalizing c with
  | zero => have he : c=d := Option.some.inj hr; subst c; exact Reach.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr
    rcases c with ⟨l,v,os⟩
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
      have hstep : step M port pg (liftCfg M k ⟨some l,v,os⟩ s) = some (liftCfg M k t s) :=
        congrArg some (trStep M k _ v os s)
      exact ((Reach.one hstep).trans (ih t hr)).mono (by omega)

private lemma invoke {M : Machine} {port : R} {pg : PC → Ins R PC} {i k} (he : pg i = .call k)
    (s : Mem R) (x y : Word) n (hx : s port = x.reverse)
    (hr : TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some (y.map M.outputAlphabet.invFun)) n) :
    Reach (step M port pg) (x.length+n+y.length+2) (cfg M i s) (cfg M k (update s port y.reverse)) := by
  have l := load_call M port pg he s x.reverse []
  have o := sim_oracle M port pg k (update s port []) hr.steps _ _ hr.evals_in_steps
  have u := unload M port pg k s y []
  have h1 : cfg M i s = cc M (.inl i) (update s port x.reverse) M.tm.k₀ [] := by
    rw [←hx,update_eq_self]
    have he : io M M.tm.k₀ [] = fun _ => [] := by
      funext j; by_cases h : j=M.tm.k₀ <;> simp_all [io]
    simp [cfg,cc,he]
  have h2 : liftCfg M k (haltList M.tm (y.map M.outputAlphabet.invFun)) (update s port []) =
      cc M (.inr (k,.inr ())) (update s port []) M.tm.k₁ (y.map M.outputAlphabet.symm) := by
    simp [liftCfg,cc,io_halt,loc]; exact ⟨rfl,rfl⟩
  rw [h1]
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,List.map_nil] at l u
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
    simp [code,program,h,pushWord_aux,stopAt,TM2.stepAux,cfg]
  | drop s r =>
    apply Reach.one
    change some (TM2.stepAux (code M port pg (.inl (g ()))) _ _) = _
    have h : pg (g ()) = .drop r k := sub ()
    simp [code,program,h,tmp,pack,stopAt,TM2.stepAux,cfg]
  | drain s r f => exact bulk (sub ()) s
  | call s x y n hx hr => exact invoke (sub ()) _ _ _ _ hx hr.some
  | seq _ _ ih jh =>
    exact (ih (g ∘ Sum.inl) _ (fun j => sub (.inl j))).trans
      (jh (g ∘ Sum.inr) k (fun j => sub (.inr j)))
  | @yes r p a b s t n hp h ih =>
    have branch := br (M:=M) (port:=port) (pg:=pg) (i:=g none) (k:=r)
      (f:=fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
      (sub none) s
    simp only [hp,if_true] at branch
    exact branch.trans (ih (fun j => g (some (.inl j))) k (fun j => sub (some (.inl j))))
  | @no r p a b s t n hp h ih =>
    have branch := br (M:=M) (port:=port) (pg:=pg) (i:=g none) (k:=r)
      (f:=fun o => if p o then g (some (.inl (entry a))) else g (some (.inr (entry b))))
      (sub none) s
    simp only [hp,Bool.false_eq_true,if_false] at branch
    exact branch.trans (ih (fun j => g (some (.inr j))) k (fun j => sub (some (.inr j))))
  | @stop r p a s hn =>
    have branch := br (M:=M) (port:=port) (pg:=pg) (i:=g none) (k:=r)
      (f:=fun o => if p o then g (some (entry a)) else k) (sub none) s
    simp only [hn,Bool.false_eq_true,if_false] at branch; exact branch
  | @more r p a s t u h j hp _ _ ih jh =>
    have branch := br (M:=M) (port:=port) (pg:=pg) (i:=g none) (k:=r)
      (f:=fun o => if p o then g (some (entry a)) else k) (sub none) s
    simp only [hp,if_true] at branch
    exact (branch.trans (ih (g ∘ some) (g none) (fun j => sub (some j)))).trans (jh g k sub)
  | mono _ hl ih => exact (ih g k sub).mono hl

def pgm (c : Cmd R) : Option (Pos c) → Ins R (Option (Pos c))
  | none => .halt
  | some j => asm c some none j

noncomputable abbrev compiled (M : Machine) (port input output : R) (c : Cmd R) : Machine where
  tm := { K := Key M R, k₀ := .inr input, k₁ := .inr output, Γ := G M R,
          Λ := Lab M R (Option (Pos c)), main := .inl (some (entry c)), σ := St M,
          initialState := (M.tm.initialState,none), m := code M port (pgm c) }
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _

def singleWord (i : R) (x : Word) : Mem R := update (fun _ => []) i x
theorem compile_run {M : Machine} {port i o : R} {c : Cmd R} {x y n}
    (h : Eval M port c (singleWord i x) (singleWord o y) n) :
    RunsWithin (compiled M port i o c) x y ((n+1 : ℕ) : ℝ) := by
  let W := compiled M port i o c
  have hinit : initList W.tm (x.map W.inputAlphabet.invFun) = cfg M (PC:=Option (Pos c)) (some (entry c)) (singleWord i x) := by
    apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl,rfl,funext fun j => ?_⟩
    rcases j with a|b
    · simp [initList,W,compiled,pack]
    · by_cases he : b=i
      · subst b; simp [initList,W,compiled,pack,singleWord,Equiv.refl]
      · simp [initList,W,compiled,pack,singleWord,update,he]
  have hstop : W.tm.step (cfg M (PC:=Option (Pos c)) none (singleWord o y)) =
      some (haltList W.tm (y.map W.outputAlphabet.invFun)) := by
    change some (TM2.stepAux (code M port (pgm c) (.inl none)) _ _) = _
    apply congrArg some; apply TM2.Cfg.mk.injEq .. |>.mpr
    refine ⟨rfl,rfl,funext fun j => ?_⟩
    rcases j with a|b
    · simp [haltList,W,compiled,pack,code,pgm,program,TM2.stepAux]
    · by_cases he : b=o
      · subst b; simp [haltList,W,compiled,pack,code,pgm,program,TM2.stepAux,singleWord,Equiv.refl]
      · simp [haltList,W,compiled,pack,code,pgm,program,TM2.stepAux,singleWord,update,he]
  have hrun := sound h (pgm c) some none (fun _ => rfl)
  obtain ⟨k,hk,hr⟩ := hrun.trans (Reach.one hstop)
  exact ⟨n+1,le_rfl,⟨⟨⟨k,hinit ▸ hr⟩,hk⟩⟩⟩

end
end IntConeFPT.QueryVM

namespace IntConeFPT.SearchMachine
open IntConeFPT.QueryVM
noncomputable section
private abbrev R := Fin 7
private abbrev C := Cmd R
private abbrev ev (M : Machine) := Eval M (1:R)
local infixr:58 " ;; " => Cmd.seq
private def mem (x a l h f t c : Word) : Mem R := ![x,a,l,h,f,t,c]
private abbrev rep (e : ℕ) : Word := List.replicate e 0
private def clear (r : R) : C := .drain r (fun _ _ => [])
private def move (r j : R) : C := .drain r (fun i a => if i=j then [a] else [])
private def clone (r : R) (j : R) : C := .drain r (fun i a => if i=j ∨ i=5 then [a] else []) ;; move 5 r
private def init : C := .drain 0 (fun i a => if i=5 then [a] else if i=6 then [0] else []) ;; move 5 0 ;;
  .loop 6 Option.isSome (.drop 6 ;; .drain 0 (fun i a => if i=4 then [0] else if i=5 then [a] else []) ;; move 5 0 ;; .put 4 [0,0,0,0]) ;;
  .put 4 [0] ;; .put 3 [1]

private def probe : C := clone 0 1 ;; clone 4 1 ;; .put 1 [1] ;; clone 2 1 ;; .put 1 [3] ;; .call
private def leaf (r : R) : C := clone 0 1 ;; clone r 1 ;; .put 1 [3] ;; .call
private def ifNo (n y : C) : C := .cond 1 (fun o => decide (o=some 0))
  (.drop 1 ;; .cond 1 Option.isSome (.put 1 [0] ;; y) (.put 1 [0] ;; n)) y
private def doubleLow : C := .cond 2 Option.isSome (.put 2 [0]) (.put 2 [])
private def lowHalf : C := clear 1 ;; clear 3 ;; move 2 5 ;;
  .drain 5 (fun i a => if i=2 ∨ i=3 then [a] else []) ;; .put 3 [1] ;; doubleLow
private def highHalf : C := clear 1 ;; .put 2 [1] ;; .put 3 [0]
private def searchLoop : C := .loop 4 Option.isSome (.drop 4 ;; probe ;; ifNo highHalf lowHalf)
private def done : C := clear 0 ;; clear 2 ;; clear 3 ;; move 1 0
private def search : C := init ;; searchLoop ;; leaf 2 ;; ifNo (clear 1 ;; leaf 3) (.put 1 []) ;; done

private lemma onebits (n : ℕ) : encNat (2*n+1) = 1::encNat n := by
  obtain ⟨m,hm⟩ : ∃ m : Num, (m:ℕ)=n := ⟨n,Num.to_of_nat n⟩
  subst n; rw [← Num.cast_bit1]; simp only [encNat,Computability.encodeNat,Num.of_to_nat]
  cases m <;> rfl
private lemma zerobits (n : ℕ) (hn : n≠0) : encNat (2*n) = 0::encNat n := by
  obtain ⟨m,hm⟩ : ∃ m : Num, (m:ℕ)=n := ⟨n,Num.to_of_nat n⟩
  subst n; rw [← Num.cast_bit0]; simp only [encNat,Computability.encodeNat,Num.of_to_nat]
  cases m with
  | zero => exact (hn rfl).elim
  | pos p => rfl
private lemma nzbits (n : ℕ) (hn : n≠0) : encNat n ≠ [] := by
  obtain ⟨m,hm⟩ : ∃ m : Num, (m:ℕ)=n := ⟨n,Num.to_of_nat n⟩
  subst n; simp only [encNat,Computability.encodeNat,Num.of_to_nat]
  cases m with
  | zero => exact (hn rfl).elim
  | pos p => cases p <;> simp [Computability.encodeNum,Computability.encodePosNum]
private lemma midbits (p e : ℕ) : encNat ((2*p+1)*2^e) = rep e ++ 1::encNat p := by
  induction e with
  | zero => simpa using onebits p
  | succ e ih =>
    rw [show (2*p+1)*2^(e+1) = 2*((2*p+1)*2^e) by ring,zerobits _ (by positivity),ih]
    simp [rep,List.replicate_succ]

private lemma ifNo_run {M : Machine} {s t : Mem R} {n y : C} {q : ℕ} (h : ev M (if s 1 = [0] then n else y) s t q) :
    ev M (ifNo n y) s t (q+5) := by
  cases hh : s 1 with
  | nil =>
    simp [hh] at h
    exact (Eval.no (by simp [hh]) h).mono (by omega)
  | cons a l =>
    by_cases ha : a=0
    · subst a
      let u := update s (1:R) l
      have hd : ev M (.drop 1) s u 1 := by simpa [u,hh] using (Eval.drop (M:=M) (port:=(1:R)) s (1:R))
      have hp : ev M (.put 1 [0]) u s 1 := by simpa [u,update_idem,←hh] using
        (Eval.put (M:=M) (port:=(1:R)) u (1:R) [0])
      cases l with
      | nil =>
        simp only [hh,if_pos rfl] at h
        exact (Eval.yes (by simp [hh]) (hd.seq (Eval.no (by simp [u]) (hp.seq h)))).mono (by omega)
      | cons b l =>
        simp only [hh,List.cons.injEq,List.cons_ne_nil,and_false,if_false] at h
        exact (Eval.yes (by simp [hh]) (hd.seq (Eval.yes (by simp [u]) (hp.seq h)))).mono (by omega)
    · simp [hh,ha] at h
      exact (Eval.no (by simp [hh,ha]) h).mono (by omega)

private lemma constZeros (w : Word) : w.flatMap (fun _ => [(0:Sym)]) = rep w.length := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih,rep,List.replicate_succ]

private lemma clear0 (M : Machine) (x a l h f t c : Word) :
    ev M (clear 0) (mem x a l h f t c) (mem [] a l h f t c) (x.length+1) := by
  have he : drained (mem x a l h f t c) (0:R) (fun _ _ => []) = (mem [] a l h f t c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (0:R) (fun _ _ => [])
  rw [he] at hh; exact hh

private lemma clear1 (M : Machine) (x a l h f t c : Word) :
    ev M (clear 1) (mem x a l h f t c) (mem x [] l h f t c) (a.length+1) := by
  have he : drained (mem x a l h f t c) (1:R) (fun _ _ => []) = (mem x [] l h f t c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (1:R) (fun _ _ => [])
  rw [he] at hh; exact hh

private lemma clear2 (M : Machine) (x a l h f t c : Word) :
    ev M (clear 2) (mem x a l h f t c) (mem x a [] h f t c) (l.length+1) := by
  have he : drained (mem x a l h f t c) (2:R) (fun _ _ => []) = (mem x a [] h f t c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (2:R) (fun _ _ => [])
  rw [he] at hh; exact hh

private lemma clear3 (M : Machine) (x a l h f t c : Word) :
    ev M (clear 3) (mem x a l h f t c) (mem x a l [] f t c) (h.length+1) := by
  have he : drained (mem x a l h f t c) (3:R) (fun _ _ => []) = (mem x a l [] f t c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (3:R) (fun _ _ => [])
  rw [he] at hh; exact hh

private lemma move50 (M : Machine) (x a l h f t c : Word) :
    ev M (move 5 0) (mem x a l h f t c) (mem (t.reverse ++ x) a l h f [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=0 then [a] else []) = (mem (t.reverse ++ x) a l h f [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=0 then [a] else [])
  rw [he] at hh; exact hh

private lemma move51 (M : Machine) (x a l h f t c : Word) :
    ev M (move 5 1) (mem x a l h f t c) (mem x (t.reverse ++ a) l h f [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=1 then [a] else []) = (mem x (t.reverse ++ a) l h f [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=1 then [a] else [])
  rw [he] at hh; exact hh

private lemma move52 (M : Machine) (x a l h f t c : Word) :
    ev M (move 5 2) (mem x a l h f t c) (mem x a (t.reverse ++ l) h f [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=2 then [a] else []) = (mem x a (t.reverse ++ l) h f [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=2 then [a] else [])
  rw [he] at hh; exact hh

private lemma move53 (M : Machine) (x a l h f t c : Word) :
    ev M (move 5 3) (mem x a l h f t c) (mem x a l (t.reverse ++ h) f [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=3 then [a] else []) = (mem x a l (t.reverse ++ h) f [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=3 then [a] else [])
  rw [he] at hh; exact hh

private lemma move54 (M : Machine) (x a l h f t c : Word) :
    ev M (move 5 4) (mem x a l h f t c) (mem x a l h (t.reverse ++ f) [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=4 then [a] else []) = (mem x a l h (t.reverse ++ f) [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=4 then [a] else [])
  rw [he] at hh; exact hh

private lemma move10 (M : Machine) (x a l h f t c : Word) :
    ev M (move 1 0) (mem x a l h f t c) (mem (a.reverse ++ x) [] l h f t c) (a.length+1) := by
  have he : drained (mem x a l h f t c) (1:R) (fun i a => if i=0 then [a] else []) = (mem (a.reverse ++ x) [] l h f t c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (1:R) (fun i a => if i=0 then [a] else [])
  rw [he] at hh; exact hh

private lemma move25 (M : Machine) (x a l h f t c : Word) :
    ev M (move 2 5) (mem x a l h f t c) (mem x a [] h f (l.reverse ++ t) c) (l.length+1) := by
  have he : drained (mem x a l h f t c) (2:R) (fun i a => if i=5 then [a] else []) = (mem x a [] h f (l.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (2:R) (fun i a => if i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma clone0a (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 0 (fun i a => if i=1 ∨ i=5 then [a] else [])) (mem x a l h f t c) (mem [] (x.reverse ++ a) l h f (x.reverse ++ t) c) (x.length+1) := by
  have he : drained (mem x a l h f t c) (0:R) (fun i a => if i=1 ∨ i=5 then [a] else []) = (mem [] (x.reverse ++ a) l h f (x.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (0:R) (fun i a => if i=1 ∨ i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma clone2a (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 2 (fun i a => if i=1 ∨ i=5 then [a] else [])) (mem x a l h f t c) (mem x (l.reverse ++ a) [] h f (l.reverse ++ t) c) (l.length+1) := by
  have he : drained (mem x a l h f t c) (2:R) (fun i a => if i=1 ∨ i=5 then [a] else []) = (mem x (l.reverse ++ a) [] h f (l.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (2:R) (fun i a => if i=1 ∨ i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma clone3a (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 3 (fun i a => if i=1 ∨ i=5 then [a] else [])) (mem x a l h f t c) (mem x (h.reverse ++ a) l [] f (h.reverse ++ t) c) (h.length+1) := by
  have he : drained (mem x a l h f t c) (3:R) (fun i a => if i=1 ∨ i=5 then [a] else []) = (mem x (h.reverse ++ a) l [] f (h.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (3:R) (fun i a => if i=1 ∨ i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma clone4a (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 4 (fun i a => if i=1 ∨ i=5 then [a] else [])) (mem x a l h f t c) (mem x (f.reverse ++ a) l h [] (f.reverse ++ t) c) (f.length+1) := by
  have he : drained (mem x a l h f t c) (4:R) (fun i a => if i=1 ∨ i=5 then [a] else []) = (mem x (f.reverse ++ a) l h [] (f.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (4:R) (fun i a => if i=1 ∨ i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma copy0 (M : Machine) (x a l h f c : Word) : ev M (clone 0 1) (mem x a l h f [] c)
    (mem x (x.reverse ++ a) l h f [] c) (2*x.length+2) := by
  have hh := (clone0a M x a l h f [] c).seq (move50 M _ _ _ _ _ _ _)
  simpa only [ev,clone,List.append_nil,List.reverse_reverse,List.length_reverse,show 2*x.length+2=x.length+1+(x.length+1) by omega] using hh
private lemma copy2 (M : Machine) (x a l h f c : Word) : ev M (clone 2 1) (mem x a l h f [] c)
    (mem x (l.reverse ++ a) l h f [] c) (2*l.length+2) := by
  have hh := (clone2a M x a l h f [] c).seq (move52 M _ _ _ _ _ _ _)
  simpa only [ev,clone,List.append_nil,List.reverse_reverse,List.length_reverse,show 2*l.length+2=l.length+1+(l.length+1) by omega] using hh
private lemma copy3 (M : Machine) (x a l h f c : Word) : ev M (clone 3 1) (mem x a l h f [] c)
    (mem x (h.reverse ++ a) l h f [] c) (2*h.length+2) := by
  have hh := (clone3a M x a l h f [] c).seq (move53 M _ _ _ _ _ _ _)
  simpa only [ev,clone,List.append_nil,List.reverse_reverse,List.length_reverse,show 2*h.length+2=h.length+1+(h.length+1) by omega] using hh
private lemma copy4 (M : Machine) (x a l h f c : Word) : ev M (clone 4 1) (mem x a l h f [] c)
    (mem x (f.reverse ++ a) l h f [] c) (2*f.length+2) := by
  have hh := (clone4a M x a l h f [] c).seq (move54 M _ _ _ _ _ _ _)
  simpa only [ev,clone,List.append_nil,List.reverse_reverse,List.length_reverse,show 2*f.length+2=f.length+1+(f.length+1) by omega] using hh

private lemma initA (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 0 (fun i a => if i=5 then [a] else if i=6 then [0] else [])) (mem x a l h f t c) (mem [] a l h f (x.reverse ++ t) (rep x.length ++ c)) (x.length+1) := by
  have he : drained (mem x a l h f t c) (0:R) (fun i a => if i=5 then [a] else if i=6 then [0] else []) = (mem [] a l h f (x.reverse ++ t) (rep x.length ++ c)) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (0:R) (fun i a => if i=5 then [a] else if i=6 then [0] else [])
  rw [he] at hh; exact hh

private lemma initB (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 0 (fun i a => if i=4 then [0] else if i=5 then [a] else [])) (mem x a l h f t c) (mem [] a l h (rep x.length ++ f) (x.reverse ++ t) c) (x.length+1) := by
  have he : drained (mem x a l h f t c) (0:R) (fun i a => if i=4 then [0] else if i=5 then [a] else []) = (mem [] a l h (rep x.length ++ f) (x.reverse ++ t) c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (0:R) (fun i a => if i=4 then [0] else if i=5 then [a] else [])
  rw [he] at hh; exact hh

private lemma setBoth (M : Machine) (x a l h f t c : Word) :
    ev M (.drain 5 (fun i a => if i=2 ∨ i=3 then [a] else [])) (mem x a l h f t c) (mem x a (t.reverse ++ l) (t.reverse ++ h) f [] c) (t.length+1) := by
  have he : drained (mem x a l h f t c) (5:R) (fun i a => if i=2 ∨ i=3 then [a] else []) = (mem x a (t.reverse ++ l) (t.reverse ++ h) f [] c) := by
    funext j; fin_cases j <;> simp [drained,mem,constZeros,List.flatMap_singleton] <;> rfl
  have hh := Eval.drain (M:=M) (port:=(1:R)) (mem x a l h f t c) (5:R) (fun i a => if i=2 ∨ i=3 then [a] else [])
  rw [he] at hh; exact hh
private lemma put1 (M : Machine) (w x a l h f t c : Word) : ev M (.put 1 w) (mem x a l h f t c) (mem x (w ++ a) l h f t c) 1 := by
  have he : update (mem x a l h f t c) (1:R) (w ++ a) = (mem x (w ++ a) l h f t c) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.put (M:=M) (port:=(1:R)) (mem x a l h f t c) (1:R) w)
private lemma put2 (M : Machine) (w x a l h f t c : Word) : ev M (.put 2 w) (mem x a l h f t c) (mem x a (w ++ l) h f t c) 1 := by
  have he : update (mem x a l h f t c) (2:R) (w ++ l) = (mem x a (w ++ l) h f t c) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.put (M:=M) (port:=(1:R)) (mem x a l h f t c) (2:R) w)
private lemma put3 (M : Machine) (w x a l h f t c : Word) : ev M (.put 3 w) (mem x a l h f t c) (mem x a l (w ++ h) f t c) 1 := by
  have he : update (mem x a l h f t c) (3:R) (w ++ h) = (mem x a l (w ++ h) f t c) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.put (M:=M) (port:=(1:R)) (mem x a l h f t c) (3:R) w)
private lemma put4 (M : Machine) (w x a l h f t c : Word) : ev M (.put 4 w) (mem x a l h f t c) (mem x a l h (w ++ f) t c) 1 := by
  have he : update (mem x a l h f t c) (4:R) (w ++ f) = (mem x a l h (w ++ f) t c) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.put (M:=M) (port:=(1:R)) (mem x a l h f t c) (4:R) w)
private lemma drop4 (M : Machine) (x a l h f t c : Word) : ev M (.drop 4) (mem x a l h f t c) (mem x a l h f.tail t c) 1 := by
  have he : update (mem x a l h f t c) (4:R) f.tail = (mem x a l h f.tail t c) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.drop (M:=M) (port:=(1:R)) (mem x a l h f t c) (4:R))
private lemma drop6 (M : Machine) (x a l h f t c : Word) : ev M (.drop 6) (mem x a l h f t c) (mem x a l h f t c.tail) 1 := by
  have he : update (mem x a l h f t c) (6:R) c.tail = (mem x a l h f t c.tail) := by funext j; fin_cases j <;> rfl
  exact he ▸ (Eval.drop (M:=M) (port:=(1:R)) (mem x a l h f t c) (6:R))

private lemma init_run (M : Machine) (x : Word) :
    ev M init (mem x [] [] [] [] [] [])
      (mem x [] [] [1] (rep (x.length^2+4*x.length+1)) [] []) (4*(x.length+2)^2) := by
  let body : C := .drop 6 ;; .drain 0 (fun i a => if i=4 then [0] else if i=5 then [a] else []) ;;
    move 5 0 ;; .put 4 [0,0,0,0]
  have iter (n u : ℕ) : ev M (.loop 6 Option.isSome body) (mem x [] [] [] (rep u) [] (rep n))
      (mem x [] [] [] (rep (u+n*(x.length+4))) [] []) (n*(2*x.length+5)+1) := by
    induction n generalizing u with
    | zero =>
      simpa using (Eval.stop (M:=M) (port:=(1:R)) (r:=(6:R)) (p:=Option.isSome) (a:=body)
        (s:=mem x [] [] [] (rep u) [] []) rfl)
    | succ n ih =>
      have hb := (drop6 M x [] [] [] (rep u) [] (rep (n+1))).seq
        ((initB M _ _ _ _ _ _ _).seq ((move50 M _ _ _ _ _ _ _).seq (put4 M [0,0,0,0] _ _ _ _ _ _ _)))
      have hb' : ev M body (mem x [] [] [] (rep u) [] (rep (n+1)))
          (mem x [] [] [] (rep (4+(x.length+u))) [] (rep n)) (2*x.length+4) := by
        have h4 : ([0,0,0,0] : Word) = rep 4 := rfl
        simpa only [body,ev,h4,rep,List.tail_replicate,Nat.add_sub_cancel,List.append_nil,
          List.reverse_reverse,List.length_reverse,←List.replicate_add,show 1+(x.length+1+(x.length+1+1))=2*x.length+4 by omega] using hb
      have h := Eval.more (p:=Option.isSome) (r:=(6:R)) (by change (rep (n+1)).head?.isSome = true; simp [rep])
        hb' (ih (4+(x.length+u)))
      rw [show u+(n+1)*(x.length+4)=4+(x.length+u)+n*(x.length+4) by ring,
        show (n+1)*(2*x.length+5)+1=1+(2*x.length+4)+(n*(2*x.length+5)+1) by ring]
      exact h
  have ii := iter x.length 0
  have before := move50 M [] [] [] [] [] x.reverse (rep x.length)
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at before
  have aa := initA M x [] [] [] [] [] []
  simp only [List.append_nil] at aa
  have h := aa.seq (before.seq (ii.seq ((put4 M [0] _ _ _ _ _ _ _).seq (put3 M [1] _ _ _ _ _ _ _))))
  simp only [rep,List.append_nil,List.reverse_reverse,List.length_reverse,Nat.zero_add] at h
  apply Eval.mono (h:=x.length+1+(x.length+1+(x.length*(2*x.length+5)+1+(1+1))))
  · rw [show x.length^2+4*x.length+1=x.length*(x.length+4)+1 by ring]
    simpa only [init,body,ev,rep,List.replicate_succ,List.cons_append,List.nil_append] using h
  · nlinarith

private lemma ask {M : Machine} (x a l h f : Word) {q ans : Word} {t : ℕ}
    (he : a=q.reverse) (hr : Nonempty (TM2OutputsInTime M.tm (q.map M.inputAlphabet.invFun)
        (some (ans.map M.outputAlphabet.invFun)) t)) :
    ev M .call (mem x a l h f [] []) (mem x ans.reverse l h f [] []) (q.length+t+ans.length+2) := by
  have hu : update (mem x a l h f [] []) (1:R) ans.reverse = mem x ans.reverse l h f [] [] := by
    funext j; fin_cases j <;> rfl
  exact hu ▸ Eval.call (M:=M) (port:=(1:R)) _ _ _ _ he hr

private abbrev query (x : Word) (k : ℕ) := x ++ encNat k ++ [3]
private abbrev state (x a : Word) (p e : ℕ) := mem x a (encNat p) (encNat (p+1)) (rep e) [] []
private abbrev mid (p e : ℕ) := (2*p+1)*2^e
private abbrev Raw (M : Machine) (q ans : Word) (t : ℕ) :=
  Nonempty (TM2OutputsInTime M.tm (q.map M.inputAlphabet.invFun) (some (ans.map M.outputAlphabet.invFun)) t)

private lemma probe_run (M : Machine) (x ans : Word) (p e t : ℕ)
    (hr : Raw M (query x (mid p e)) ans t) :
    ev M probe (state x [] p e) (state x ans.reverse p e)
      (3*(x.length + (encNat p).length + e) + t + ans.length + 12) := by
  have he : 3 :: ((encNat p).reverse ++ 1::((rep e).reverse ++ x.reverse)) =
      (query x (mid p e)).reverse := by simp [query,mid,midbits,List.reverse_append,List.append_assoc]
  have ca := ask x _ (encNat p) (encNat (p+1)) (rep e) he hr
  have first := copy0 M x [] (encNat p) (encNat (p+1)) (rep e) []
  simp only [List.append_nil] at first
  have h := first.seq
    ((copy4 M _ _ _ _ _ _).seq ((put1 M [1] _ _ _ _ _ _ _).seq
    ((copy2 M _ _ _ _ _ _).seq ((put1 M [3] _ _ _ _ _ _ _).seq ca))))
  apply h.mono
  simp only [mid,midbits,query,List.length_append,List.length_reverse,rep,List.length_replicate,
    List.length_cons,List.length_nil]; omega

private lemma left_run (M : Machine) (x a : Word) (p e : ℕ) :
    ev M lowHalf (state x a p e) (state x [] (2*p) e)
      (a.length+(encNat (p+1)).length+2*(encNat p).length+8) := by
  have hd : ev M doubleLow (mem x [] (encNat p) (1::encNat p) (rep e) [] [])
      (state x [] (2*p) e) 2 := by
    by_cases hp : p=0
    · subst p; exact Eval.no rfl (put2 M [] _ _ _ _ _ _ _)
    · have hb := nzbits p hp
      have ht : (encNat p).head?.isSome = true := by cases he : encNat p <;> simp_all
      simp only [state,zerobits p hp,onebits]
      exact Eval.yes (p:=Option.isSome) (r:=(2:R)) (s:=mem x [] (encNat p) (1::encNat p) (rep e) [] [])
        (by exact ht) (put2 M [0] _ _ _ _ _ _ _)
  have mv := move25 M x [] (encNat p) [] (rep e) [] []
  have both := setBoth M x [] [] [] (rep e) (encNat p).reverse []
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at mv both
  have hh := (clear1 M x a (encNat p) (encNat (p+1)) (rep e) [] []).seq
    ((clear3 M _ _ _ _ _ _ _).seq (mv.seq
      (both.seq ((put3 M [1] _ _ _ _ _ _ _).seq hd))))
  apply hh.mono; simp; omega

private lemma right_run (M : Machine) (x a : Word) (p e : ℕ) :
    ev M highHalf (state x a p e) (state x [] (2*p+1) e) (a.length+3) := by
  have h := (clear1 M x a (encNat p) (encNat (p+1)) (rep e) [] []).seq
    ((put2 M [1] _ _ _ _ _ _ _).seq (put3 M [0] _ _ _ _ _ _ _))
  have hh : 2*p+1+1=2*(p+1) := by omega
  simpa only [state,highHalf,ev,onebits,hh,zerobits (p+1) (Nat.succ_ne_zero _),
    List.cons_append,List.nil_append,Nat.add_assoc] using h

private lemma enc_len (k : ℕ) : (encNat k).length = k.size := by
  obtain ⟨m,rfl⟩ : ∃ m : Num, (m:ℕ)=k := ⟨k,Num.to_of_nat k⟩
  simp only [encNat,Computability.encodeNat,Num.of_to_nat,List.length_map]
  cases m with
  | zero => rfl
  | pos p =>
    change (Computability.encodePosNum p).length = Nat.size (p:ℕ)
    rw [← PosNum.natSize_to_nat]; induction p <;> simp_all [Computability.encodePosNum,PosNum.natSize]

private lemma leaf_run (M : Machine) (x ans : Word) (p t : ℕ) (hi : Bool)
    (hr : Raw M (query x (if hi then p+1 else p)) ans t) :
    ev M (leaf (if hi then 3 else 2)) (state x [] p 0) (state x ans.reverse p 0)
      (3*(x.length + (encNat (if hi then p+1 else p)).length) + t + ans.length + 9) := by
  have he (k) : 3 :: ((encNat k).reverse ++ x.reverse) = (query x k).reverse := by simp [query,List.reverse_append]
  have first := copy0 M x [] (encNat p) (encNat (p+1)) [] []
  simp only [List.append_nil] at first
  cases hi
  · have ca := ask x _ (encNat p) (encNat (p+1)) [] (he p) hr
    have hh := first.seq ((copy2 M _ _ _ _ _ _).seq ((put1 M [3] _ _ _ _ _ _ _).seq ca))
    apply hh.mono; simp [query]; omega
  · have ca := ask x _ (encNat p) (encNat (p+1)) [] (he (p+1)) hr
    have hh := first.seq ((copy3 M _ _ _ _ _ _).seq ((put1 M [3] _ _ _ _ _ _ _).seq ca))
    apply hh.mono; simp [query]; omega

private lemma finish_run (M : Machine) (x a : Word) (p : ℕ) : ev M done (state x a.reverse p 0)
    (mem a [] [] [] [] [] []) (x.length+(encNat p).length+(encNat (p+1)).length+a.length+4) := by
  have h := (clear0 M x a.reverse (encNat p) (encNat (p+1)) [] [] []).seq ((clear2 M _ _ _ _ _ _ _).seq
    ((clear3 M _ _ _ _ _ _ _).seq (move10 M _ _ _ _ _ _ _)))
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at h
  apply h.mono; omega

private lemma locate (U : ℕ) (a : ℕ → Word)
    (mon : ∀ i j, i ≤ j → j ≤ U → a i ≠ [0] → a j ≠ [0]) :
    ∃ k ≤ U, (∀ j < k, a j = [0]) ∧ (∀ j < U, k ≤ j → a j ≠ [0]) ∧
        (a k = [0] → ∀ j ≤ U, a j = [0]) := by
  classical
  by_cases he : ∃ j, j ≤ U ∧ a j ≠ [0]
  · let k := Nat.find he
    have h := Nat.find_spec he
    exact ⟨k,h.1,fun j hj => by by_contra hh; have hl := Nat.find_min' he (show j≤U ∧ _ from ⟨by omega,hh⟩); omega,
      fun j hj hkj => mon k j hkj hj.le h.2,fun hn => (h.2 hn).elim⟩
  · have ha (j) (hj : j≤U) : a j = [0] := by by_contra hn; exact he ⟨j,hj,hn⟩
    exact ⟨U,le_rfl,fun j hj => ha j hj.le,fun _ hj h => (Nat.not_lt_of_ge h hj).elim,fun _ => ha⟩

private lemma loop_run (M : Machine) (x : Word) (a : ℕ → Word) (D t V k : ℕ)
    (oracle : ∀ i ≤ 2^D, Raw M (query x i) (a i) t)
    (volume : ∀ i ≤ 2^D, (a i).length ≤ V)
    (leftNo : ∀ j < k, a j = [0]) (rightYes : ∀ j < 2^D, k ≤ j → a j ≠ [0])
    (e p : ℕ) (he : e ≤ D) (hcap : (p+1)*2^e ≤ 2^D)
    (hl : p*2^e ≤ k) (hu : k ≤ (p+1)*2^e) :
    ∃ p', p' ≤ k ∧ k ≤ p'+1 ∧ p'+1 ≤ 2^D ∧
      ev M searchLoop (state x [] p e) (state x [] p' 0)
        (e*(10*(x.length+D+t+V+10))+1) := by
  have len (j : ℕ) (hj : j ≤ 2^D) : (encNat j).length ≤ D+1 := by
    rw [enc_len,Nat.size_le,pow_succ]; have := Nat.two_pow_pos D; omega
  induction e generalizing p with
  | zero =>
    refine ⟨p,by simpa using hl,by simpa using hu,by simpa using hcap,?_⟩
    simp only [Nat.zero_mul,Nat.zero_add]
    exact Eval.stop rfl
  | succ e ih =>
    let m := mid p e
    have base : p*2^(e+1) = (2*p)*2^e := by ring
    have cap : (p+1)*2^(e+1) = (2*p+2)*2^e := by ring
    have mp : m < (p+1)*2^(e+1) := by dsimp [m,mid]; rw [cap]; nlinarith [Nat.two_pow_pos e]
    have mU := mp.trans_le hcap
    have pU : p+1 ≤ 2^D := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans hcap
    have hpr := probe_run M x (a m) p e t (oracle m mU.le)
    have dp := drop4 M x [] (encNat p) (encNat (p+1)) (rep (e+1)) [] []
    simp only [rep,List.tail_replicate,Nat.add_sub_cancel] at dp
    have lp := len p (Nat.le_trans (Nat.le_succ _) pU)
    have ls := len (p+1) pU
    have la := volume m mU.le
    by_cases hn : a m = [0]
    · have cmp : m ≤ k := by by_contra! hh; exact rightYes m mU hh.le hn
      have hr := right_run M x (a m).reverse p e
      have htest := ifNo_run (M:=M) (n:=highHalf) (y:=lowHalf) (s:=state x (a m).reverse p e) (by
        rw [if_pos (show (state x (a m).reverse p e 1)=[0] by simp [state,mem,hn])]; exact hr)
      obtain ⟨p',h1,h2,h3,h4⟩ := ih (2*p+1) (by omega) (by rw [cap] at hcap; exact hcap) cmp (by rw [cap] at hu; exact hu)
      refine ⟨p',h1,h2,h3,?_⟩
      have hstep := dp.seq (hpr.seq htest)
      apply (Eval.more (p:=Option.isSome) (r:=(4:R)) (by change (rep (e+1)).head?.isSome=true; simp [rep]) hstep h4).mono
      simp only [List.length_reverse]; simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul]; dsimp only [m] at la ⊢; omega
    · have cmp : k ≤ m := by by_contra! hh; exact hn (leftNo m hh)
      have hr := left_run M x (a m).reverse p e
      have hn' : state x (a m).reverse p e 1 ≠ [0] := by
        intro h; change (a m).reverse = [0] at h; exact hn (by simpa using congrArg List.reverse h)
      have htest := ifNo_run (M:=M) (n:=highHalf) (y:=lowHalf) (s:=state x (a m).reverse p e) (by rw [if_neg hn']; exact hr)
      obtain ⟨p',h1,h2,h3,h4⟩ := ih (2*p) (by omega) mU.le (base ▸ hl) cmp
      refine ⟨p',h1,h2,h3,?_⟩
      apply (Eval.more (p:=Option.isSome) (r:=(4:R)) (by change (rep (e+1)).head?.isSome=true; simp [rep])
        (dp.seq (hpr.seq htest)) h4).mono
      simp only [List.length_reverse]; simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul]; dsimp only [m] at la ⊢; omega

private lemma endpoints (M : Machine) (x : Word) (a : ℕ → Word) (D t V k p : ℕ)
    (oracle : ∀ i ≤ 2^D, Raw M (query x i) (a i) t)
    (volume : ∀ i ≤ 2^D, (a i).length ≤ V)
    (leftNo : ∀ j < k, a j = [0]) (rightYes : ∀ j < 2^D, k ≤ j → a j ≠ [0])
    (hl : p ≤ k) (hu : k ≤ p+1) (hcap : p+1 ≤ 2^D) :
    ev M (leaf 2 ;; ifNo (clear 1 ;; leaf 3) (.put 1 []) ;; done) (state x [] p 0)
      (mem (a k) [] [] [] [] [] []) (20*(x.length+D+t+V+10)) := by
  have hpu := (Nat.le_succ p).trans hcap
  have first := leaf_run M x (a p) p t false (oracle p hpu)
  have lp : (encNat p).length ≤ D+1 := by rw [enc_len,Nat.size_le,pow_succ]; have := Nat.two_pow_pos D; omega
  have ls : (encNat (p+1)).length ≤ D+1 := by rw [enc_len,Nat.size_le,pow_succ]; have := Nat.two_pow_pos D; omega
  have hpv := volume p hpu
  have hsv := volume (p+1) hcap
  by_cases hn : a p = [0]
  · have hk : k=p+1 := by by_contra! h; exact rightYes p (by omega) (by omega) hn
    subst k
    have hh := leaf_run M x (a (p+1)) p t true (oracle (p+1) hcap)
    have cl := clear1 M x (a p).reverse (encNat p) (encNat (p+1)) [] [] []
    have test := ifNo_run (M:=M) (s:=state x (a p).reverse p 0) (n:=clear 1 ;; leaf 3) (y:=.put 1 []) (by
      rw [if_pos (show state x (a p).reverse p 0 1=[0] by simp [state,mem,hn])]; exact cl.seq hh)
    apply (first.seq (test.seq (finish_run M x (a (p+1)) p))).mono
    simp only [List.length_reverse,Bool.false_eq_true,if_true,if_false]; omega
  · have hk : k=p := by by_contra! hh; exact hn (leftNo p (by omega))
    subst k
    have hn' : state x (a p).reverse p 0 1 ≠ [0] := by
      intro hh; change (a p).reverse = [0] at hh; exact hn (by simpa using congrArg List.reverse hh)
    have test := ifNo_run (M:=M) (s:=state x (a p).reverse p 0) (n:=clear 1 ;; leaf 3) (y:=.put 1 []) (by
      rw [if_neg hn']; exact put1 M [] _ _ _ _ _ _ _)
    apply (first.seq (test.seq (finish_run M x (a p) p))).mono
    simp only [List.length_reverse,Bool.false_eq_true,if_false]; omega

private lemma oneAt0 (x : Word) : singleWord (0:R) x = mem x [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

end
end IntConeFPT.SearchMachine
open IntConeFPT.QueryVM IntConeFPT.SearchMachine

theorem solution (A : Machine) :
    ∃ d : ℕ, ∃ W : Machine, ∀ (x : List Sym) (a : ℕ → List Sym) (T : ℝ),
      let B := 2^(x.length^2+4*x.length)
      (∀ k ≤ 2*B, RunsWithin A (x ++ encNat k ++ [3]) (a k) T) →
      (∀ i j, i ≤ j → j ≤ 2*B → a i ≠ [0] → a j ≠ [0]) →
      ∃ k : ℕ, k ≤ 2*B ∧
        (a k = [0] → ∀ j ≤ 2*B, a j = [0]) ∧
        (a k ≠ [0] → ∀ j < k, a j = [0]) ∧
        RunsWithin W x (a k) ((x.length + T + 2 : ℝ)^d) := by
  classical
  let G := A.tm.growth
  let C := 100*(G+30)
  refine ⟨C+4,compiled A 1 0 0 search,?_⟩
  intro x a T B hr hm
  let L := x.length
  let D := L^2+4*L+1
  let t := ⌊T⌋₊
  let V := L+D+2+t*G
  have hB : 2^D = 2*B := by simp [D,L,B,pow_succ,mul_comm]
  have oracle (i : ℕ) (hi : i ≤ 2^D) : Raw A (query x i) (a i) t := by
    obtain ⟨m,hb,⟨h⟩⟩ := hr i (hB ▸ hi)
    exact ⟨⟨h.toEvalsTo, h.steps_le_m.trans (Nat.le_floor hb)⟩⟩
  have volume (i : ℕ) (hi : i ≤ 2^D) : (a i).length ≤ V := by
    have h := (oracle i hi).some.output_length_le
    simp only [query,List.length_map,List.length_append,List.length_singleton] at h
    have hl : (encNat i).length ≤ D+1 := by rw [enc_len,Nat.size_le,pow_succ]; have := Nat.two_pow_pos D; omega
    dsimp only [V,G,L]; omega
  obtain ⟨k,hk,hn,hy,hno⟩ := locate (2*B) a hm
  have hy' : ∀ j < 2^D, k ≤ j → a j ≠ [0] := hB.symm ▸ hy
  obtain ⟨p,hp,hpk,hcap,hh⟩ := loop_run A x a D t V k oracle volume hn hy' D 0 le_rfl
    (by simp) (by simp) (by simpa [hB] using hk)
  have tail := endpoints A x a D t V k p oracle volume hn hy' hp hpk hcap
  have exec := (init_run A x).seq (hh.seq tail)
  let steps := 4*(L+2)^2 + (D*(10*(L+D+t+V+10))+1 + 20*(L+D+t+V+10))
  have proof : Eval A (1:R) search (singleWord 0 x) (singleWord 0 (a k)) steps := by
    rw [oneAt0,oneAt0]; exact exec
  obtain ⟨m,hm',hout⟩ := compile_run proof
  refine ⟨k,hk,hno,fun _ => hn, m,hm'.trans ?_,hout⟩
  obtain ⟨m0,hm0,_⟩ := hr 0 (Nat.zero_le _)
  have ht : 0 ≤ T := (Nat.cast_nonneg _).trans hm0
  let S := L+t+2
  have hs : 2 ≤ S := by dsimp [S]; omega
  have hl : L+2 ≤ S := by dsimp [S]; omega
  have hsq : L^2 ≤ S^2 := Nat.pow_le_pow_left (by omega) 2
  have hss : S ≤ S^2 := by nlinarith
  have hd : D ≤ 6*S^2 := by dsimp only [D]; omega
  have ht' : t ≤ S := by dsimp [S]; omega
  have hg : t*G ≤ S^2*G := Nat.mul_le_mul_right G (ht'.trans hss)
  have hv : V ≤ (G+9)*S^2 := by dsimp only [V]; nlinarith
  have hu : L+D+t+V+10 ≤ (G+30)*S^2 := by nlinarith
  have hs4 : S^2 ≤ S^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have hmax : steps+1 ≤ (100*(G+30))*S^4 := by
    have h1 := Nat.pow_le_pow_left hl 2
    have h2 := Nat.mul_le_mul hd (Nat.mul_le_mul_left 10 hu)
    have h3 := Nat.mul_le_mul_left (20*(G+30)) hs4
    have h4 := Nat.mul_le_mul_left 20 hu
    have h24 : D*(10*(L+D+t+V+10)) ≤ 60*(G+30)*S^4 := by
      refine h2.trans_eq ?_; ring
    have h44 : 20*(L+D+t+V+10) ≤ 20*(G+30)*S^4 := h4.trans (by simpa [Nat.mul_assoc] using h3)
    have h14 := h1.trans hs4
    have hlarge : S^4 ≤ (G+30)*S^4 := Nat.le_mul_of_pos_left _ (by omega)
    have hpow : 1 ≤ S^4 := Nat.one_le_pow _ _ (by omega)
    dsimp only [steps]; linarith only [h14,h24,h44,hlarge,hpow]
  have coeff : 100*(G+30) ≤ S^C := (Nat.lt_two_pow_self (n:=C)).le.trans (Nat.pow_le_pow_left hs C)
  have htotal : steps+1 ≤ S^(C+4) := by rw [pow_add]; exact hmax.trans (Nat.mul_le_mul_right _ coeff)
  refine (Nat.cast_le.mpr htotal).trans ?_
  rw [Nat.cast_pow]; apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  dsimp only [S,L,t]; push_cast; linarith [Nat.floor_le ht]
