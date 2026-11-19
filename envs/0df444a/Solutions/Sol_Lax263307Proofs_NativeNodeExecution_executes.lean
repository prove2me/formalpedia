-- Prove2me | solution 1 for Lax263307Proofs.NativeNodeExecution.executes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:05:35.928202+00:00
-- url     : https://prove2.me/submissions/ab824cfd-c10c-4118-843c-79cbc6c69507

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces
import Theorems.Thm_Lax263307Proofs_NativeNodeExecution_large_segment

section

namespace Lax808846Proofs.Imp

@[simp] theorem Bop.apply_add (m n:ℕ):Bop.add.apply m n=m + n:=rfl
@[simp] theorem Bop.apply_sub (m n:ℕ):Bop.sub.apply m n=m - n:=rfl
@[simp] theorem Bop.apply_mul (m n:ℕ):Bop.mul.apply m n=m * n:=rfl
@[simp] theorem Bop.apply_div (m n:ℕ):Bop.div.apply m n=m / n:=rfl
@[simp] theorem Bop.apply_and (m n:ℕ):Bop.and.apply m n=Nat.land m n:=rfl
@[simp] theorem Bop.apply_or (m n:ℕ):Bop.or.apply m n=Nat.lor m n:=rfl
@[simp] theorem Bop.apply_xor (m n:ℕ):Bop.xor.apply m n=Nat.xor m n:=rfl
@[simp] theorem Bop.apply_shiftl (m n:ℕ):Bop.shiftl.apply m n=m * 2 ^ n:=rfl
@[simp] theorem Bop.apply_shiftr (m n:ℕ):Bop.shiftr.apply m n=m / 2 ^ n:=rfl

@[simp] theorem Expr.add_def (e f:Expr):Expr.add e f=.bin .add e f:=rfl
@[simp] theorem Expr.sub_def (e f:Expr):Expr.sub e f=.bin .sub e f:=rfl
@[simp] theorem Expr.mul_def (e f:Expr):Expr.mul e f=.bin .mul e f:=rfl
@[simp] theorem Expr.div_def (e f:Expr):Expr.div e f=.bin .div e f:=rfl
@[simp] theorem Expr.and_def (e f:Expr):Expr.and e f=.bin .and e f:=rfl
@[simp] theorem Expr.or_def (e f:Expr):Expr.or e f=.bin .or e f:=rfl
@[simp] theorem Expr.xor_def (e f:Expr):Expr.xor e f=.bin .xor e f:=rfl
@[simp] theorem Expr.shiftl_def (e f:Expr):Expr.shiftl e f=.bin .shiftl e f:=rfl
@[simp] theorem Expr.shiftr_def (e f:Expr):Expr.shiftr e f=.bin .shiftr e f:=rfl

def Expr.eval:Expr→ Env→ Option ℕ
  | lit n,_ => some n
  | var x,σ => some (σ.vars x)
  | get a i,σ => (i.eval σ).bind fun k => (σ.arrs a)[k]?
  | bin op e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => op.apply m n

def Cond.eval:Cond→ Env→ Option Bool
  | eq e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n
  | lt e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n)

inductive BigStep:Com→ Env→ Env→ ℕ→ Prop

  | skip {σ:Env}:BigStep .skip σ σ 1

  | assign {σ:Env} {x:String} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.assign x e) σ (σ.setVar x v) (1 + e.size)

  | store {σ:Env} {a:String} {i e:Expr} {k v:ℕ}
      (hi:i.eval σ=some k) (he:e.eval σ=some v)
      (hk:k < (σ.arrs a).length):
      BigStep (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)

  | seq {c d:Com} {σ σ' σ'':Env} {k k':ℕ}:
      BigStep c σ σ' k→ BigStep d σ' σ'' k'→
      BigStep (.seq c d) σ σ'' (k + k')

  | ite_true {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | ite_false {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some false) (hd:BigStep d σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | while_true {b:Cond} {c:Com} {σ σ' σ'':Env} {k k':ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k)
      (hw:BigStep (.while b c) σ' σ'' k'):
      BigStep (.while b c) σ σ'' (1 + b.size + k + k')

  | while_false {b:Cond} {c:Com} {σ:Env} (hb:b.eval σ=some false):
      BigStep (.while b c) σ σ (1 + b.size)

  | read {σ:Env} {x:String} {v:ℕ} {rest:List ℕ} (h:σ.inp=v::rest):
      BigStep (.read x) σ { σ.setVar x v with inp:=rest } 1

  | write {σ:Env} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Imp

theorem fit_eq_some {B v u:ℕ}:fit B v=some u↔ u=v∧ v < B:=by
  constructor
  · intro h
    by_cases hv:v < B
    · rw [fit,if_pos hv] at h
      exact ⟨(Option.some.inj h).symm,hv⟩
    · rw [fit,if_neg hv] at h; exact absurd h (by simp)
  · rintro ⟨rfl,h⟩; rw [fit,if_pos h]

theorem fit_self {B v:ℕ} (h:v < B):fit B v=some v:=by rw [fit,if_pos h]

theorem Expr.eval_and_lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v∧ v < B:=by
  induction e generalizing v with
  | lit n =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | var x =>
      rw [Expr.evalB,fit_eq_some] at h
      obtain ⟨rfl,hn⟩:=h
      exact ⟨rfl,hn⟩
  | get a i ih =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨k,hk,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨u,hu,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ih hk).1]; exact hu,hlt⟩
  | bin op e f ihe ihf =>
      rw [Expr.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨n,hn,h⟩:=h
      rw [fit_eq_some] at h
      obtain ⟨rfl,hlt⟩:=h
      exact ⟨by rw [Expr.eval, (ihe hm).1, (ihf hn).1]; rfl,hlt⟩

theorem Expr.eval_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):e.eval σ=some v:=(eval_and_lt_of_evalB h).1

theorem Expr.lt_of_evalB {B:ℕ} {σ:Env} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):v < B:=(eval_and_lt_of_evalB h).2

theorem Cond.eval_of_evalB {B:ℕ} {σ:Env} {b:Cond} {r:Bool}
    (h:b.evalB B σ=some r):b.eval σ=some r:=by
  cases b with
  | eq e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl
  | lt e f =>
      rw [Cond.evalB,Option.bind_eq_some_iff] at h
      obtain ⟨m,hm,h⟩:=h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨n,hn,rfl⟩:=h
      rw [Cond.eval,Expr.eval_of_evalB hm,Expr.eval_of_evalB hn]; rfl

theorem BigStepB.bigStep {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStepB B c σ σ' k):BigStep c σ σ' k:=by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (Expr.eval_of_evalB h)
  | store hi he hk => exact .store (Expr.eval_of_evalB hi) (Expr.eval_of_evalB he) hk
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (Cond.eval_of_evalB hb) ih
  | ite_false hb _ ih => exact .ite_false (Cond.eval_of_evalB hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (Cond.eval_of_evalB hb) ih ih'
  | while_false hb => exact .while_false (Cond.eval_of_evalB hb)
  | read h => exact .read h
  | write h => exact .write (Expr.eval_of_evalB h)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

@[simp] theorem vars_setVar (σ:Env) (x:String) (v:ℕ) (y:String):
    (σ.setVar x v).vars y=if y=x then v else σ.vars y:=rfl

@[simp] theorem arrs_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).arrs=σ.arrs:=rfl

@[simp] theorem inp_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).inp=σ.inp:=rfl

@[simp] theorem out_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).out=σ.out:=rfl

@[simp] theorem vars_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).vars=σ.vars:=rfl

@[simp] theorem arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    (σ.setArr a i v).arrs b=if b=a then (σ.arrs a).set i v else σ.arrs b:=rfl

@[simp] theorem inp_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).inp=σ.inp:=rfl

@[simp] theorem out_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).out=σ.out:=rfl

@[simp] theorem length_arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    ((σ.setArr a i v).arrs b).length=(σ.arrs b).length:=by
  rw [arrs_setArr]; split
  · subst_vars; exact List.length_set ..
  · rfl

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_condEq_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.eq e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=(m == n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

@[simp] theorem evalB_condLt_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.lt e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=decide (m < n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_get {B:ℕ} {a:String} {i:Expr} {σ:Env} {k v:ℕ}
    (hi:i.evalB B σ=some k) (hk:(σ.arrs a)[k]?=some v) (hv:v < B):
    (Expr.get a i).evalB B σ=some v:=by
  rw [Expr.evalB,hi,Option.bind_some,hk,Option.bind_some,fit_self hv]

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

theorem evalB_condEq {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.eq e f).evalB B σ=some (m == n):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

theorem evalB_condLt {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.lt e f).evalB B σ=some (decide (m < n)):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

theorem evalB_condLt_vars {B:ℕ} {x y:String} {σ:Env}
    (hx:σ.vars x < B) (hy:σ.vars y < B):
    ∃ v, (Cond.lt (.var x) (.var y)).evalB B σ=some v:=
  ⟨_,evalB_condLt (evalB_var hx) (evalB_var hy)⟩

@[simp] theorem size_lit (n:ℕ):(Expr.lit n).size=1:=rfl
@[simp] theorem size_var (x:String):(Expr.var x).size=1:=rfl
@[simp] theorem size_get (a:String) (i:Expr):(Expr.get a i).size=i.size + 1:=rfl
@[simp] theorem size_bin (op:Bop) (e f:Expr):
    (Expr.bin op e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_add (e f:Expr):(Expr.add e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_sub (e f:Expr):(Expr.sub e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_mul (e f:Expr):(Expr.mul e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_div (e f:Expr):(Expr.div e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_and (e f:Expr):(Expr.and e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_or (e f:Expr):(Expr.or e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_xor (e f:Expr):(Expr.xor e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftl (e f:Expr):(Expr.shiftl e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftr (e f:Expr):(Expr.shiftr e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condEq (e f:Expr):(Cond.eq e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condLt (e f:Expr):(Cond.lt e f).size=e.size + f.size + 1:=rfl

theorem Run.of_bigStepB {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ} (h:BigStepB B c σ σ' k):
    Run B c σ σ' k:= ⟨k,le_rfl,h⟩

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.skip {B:ℕ} {σ:Env}:Run B .skip σ σ 1:=.of_bigStepB .skip

theorem Run.assign {B:ℕ} {σ:Env} {x:String} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=.of_bigStepB (.assign h)

theorem Run.store {B:ℕ} {σ:Env} {a:String} {i e:Expr} {idx v:ℕ}
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=
  .of_bigStepB (.store hi he hidx)

theorem Run.read {B:ℕ} {σ:Env} {x:String} {v:ℕ} {rest:List ℕ}
    (h:σ.inp=v::rest):
    Run B (.read x) σ { σ.setVar x v with inp:=rest } 1:=.of_bigStepB (.read h)

theorem Run.write {B:ℕ} {σ:Env} {e:Expr} {v:ℕ} (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=.of_bigStepB (.write h)

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

theorem Run.ite_true {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_true hb hbs⟩

theorem Run.ite_false {B:ℕ} {b:Cond} {c d:Com} {σ σ':Env} {K:ℕ}
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=by
  obtain ⟨k,hk,hbs⟩:=h
  exact ⟨1 + b.size + k,by omega, .ite_false hb hbs⟩

theorem Run.while_false {B:ℕ} {b:Cond} {c:Com} {σ:Env}
    (hb:b.evalB B σ=some false):Run B (.while b c) σ σ (1 + b.size):=
  .of_bigStepB (.while_false hb)

theorem Run.while_potential {B:ℕ} {b:Cond} {c:Com} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    {σ:Env} (hI:I σ):
    ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
      K + Φ σ'≤ Φ σ + 1 + b.size:=by
  suffices H:∀ n σ,I σ→ Φ σ≤ n→
      ∃ σ' K,Run B (.while b c) σ σ' K∧ I σ'∧ b.evalB B σ'=some false∧
        K + Φ σ'≤ Φ σ + 1 + b.size from H (Φ σ) σ hI le_rfl
  clear hI σ
  intro n
  induction n with
  | zero =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,_,hpay⟩:=hstep σ hI hv
          omega
  | succ n ih =>
      intro σ hI hΦ
      obtain ⟨v,hv⟩:=hdef σ hI
      cases v with
      | false => exact ⟨σ,_,Run.while_false hv,hI,hv,by omega⟩
      | true =>
          obtain ⟨σ₁,K,hrun,hI₁,hpay⟩:=hstep σ hI hv
          obtain ⟨σ',K',hrun',hI',hfalse,hpay'⟩:=ih σ₁ hI₁ (by omega)
          obtain ⟨k,hk,hbs⟩:=hrun
          obtain ⟨k',hk',hbs'⟩:=hrun'
          exact ⟨σ',1 + b.size + k + k', ⟨1 + b.size + k + k',le_rfl,
            .while_true hv hbs hbs'⟩,hI',hfalse,by omega⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

end

section

namespace Lax808846Proofs.Imp

@[simp] theorem Com.wvars_skip:Com.skip.wvars=[]:=by simp [Com.wvars]

end Lax808846Proofs.Imp

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

theorem _root_.Lax808846Proofs.Imp.BigStep.vars_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {y:String} (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  induction h with
  | skip => rfl
  | assign _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.wvars,List.mem_append,not_or] at hy
      rw [ih' hy.2,ih hy.1]
  | ite_true _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.1
  | ite_false _ _ ih => simp only [Com.wvars,List.mem_append,not_or] at hy; exact ih hy.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.wvars] at hy
      rw [ih' (by simpa [Com.wvars] using hy),ih hy]
  | while_false _ => rfl
  | read _ => simp only [Com.wvars,List.mem_singleton] at hy; simp [Env.setVar,hy]
  | write _ => rfl

theorem _root_.Lax808846Proofs.Imp.BigStep.arrs_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) {a:String} (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [Com.warrs,List.mem_singleton] at ha; simp [Env.setArr,ha]
  | seq _ _ ih ih' =>
      simp only [Com.warrs,List.mem_append,not_or] at ha
      rw [ih' ha.2,ih ha.1]
  | ite_true _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.1
  | ite_false _ _ ih => simp only [Com.warrs,List.mem_append,not_or] at ha; exact ih ha.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.warrs] at ha
      rw [ih' (by simpa [Com.warrs] using ha),ih ha]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

theorem Spec.run (h:Spec B P c Q K) {σ:Env} (hσ:P σ):
    ∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

theorem Spec.mono (h:Spec B P c Q K) (hK:K≤ K'):Spec B P c Q K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr.mono hK,hq⟩

theorem Spec.conseq (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ)
    (hQ:∀ σ σ',P' σ→ Q σ σ'→ Q' σ σ') (hK:K≤ K'):Spec B P' c Q' K':=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ (hP σ hσ)
  exact ⟨σ',hr.mono hK,hQ σ σ' hσ hq⟩

theorem Spec.post (h:Spec B P c Q K) (hQ:∀ σ σ',P σ→ Q σ σ'→ Q' σ σ'):
    Spec B P c Q' K:=
  h.conseq (fun _ hσ => hσ) hQ le_rfl

theorem Spec.assign {x:String} {e:Expr} {f:Env→ ℕ}
    (h:∀ σ,P σ→ e.evalB B σ=some (f σ)):
    Spec B P (.assign x e) (fun σ σ' => σ'=σ.setVar x (f σ)) (1 + e.size):=
  fun σ hσ => ⟨_,Run.assign (h σ hσ),rfl⟩

theorem Spec.seq (h:Spec B P c Q K) (h':Spec B P' d Q' K')
    (hmid:∀ σ σ',P σ→ Q σ σ'→ P' σ')
    (hpost:∀ σ σ' σ'',P σ→ Q σ σ'→ Q' σ' σ''→ R σ σ''):
    Spec B P (.seq c d) R (K + K'):=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  obtain ⟨σ'',hr',hq'⟩:=h' σ' (hmid σ σ' hσ hq)
  exact ⟨σ'',hr.seq hr',hpost σ σ' σ'' hσ hq hq'⟩

theorem Spec.while_potential {b:Cond} (I:Env→ Prop) (Φ:Env→ ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hstep:∀ σ,I σ→ b.evalB B σ=some true→
      ∃ σ' K,Run B c σ σ' K∧ I σ'∧ 1 + b.size + K + Φ σ'≤ Φ σ)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ Φ σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  intro σ hσ
  obtain ⟨σ',K₀,hr,hI,hfalse,hpay⟩:=Run.while_potential I Φ hdef hstep (hPI σ hσ)
  exact ⟨σ',hr.mono (by have:=hK σ hσ; omega),hI,hfalse⟩

theorem Spec.while_count {b:Cond} (I:Env→ Prop) (V:Env→ ℕ) (Kb:ℕ)
    (hdef:∀ σ,I σ→ ∃ v,b.evalB B σ=some v)
    (hbody:Spec B (fun σ => I σ∧ b.evalB B σ=some true) c
      (fun σ σ' => I σ'∧ V σ' < V σ) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (1 + b.size + Kb) * V σ + 1 + b.size≤ K):
    Spec B P (.while b c) (fun _ σ' => I σ'∧ b.evalB B σ'=some false) K:=by
  refine Spec.while_potential I (fun σ => (1 + b.size + Kb) * V σ) hdef ?_ hPI hK
  intro σ hI hv
  obtain ⟨σ',hr,hI',hV⟩:=hbody σ ⟨hI,hv⟩
  refine ⟨σ',Kb,hr,hI', ?_⟩
  calc 1 + b.size + Kb + (1 + b.size + Kb) * V σ'
     =(1 + b.size + Kb) * (V σ' + 1):=by ring
    _≤ (1 + b.size + Kb) * V σ:=Nat.mul_le_mul_left _ hV

theorem lt_of_condLt_true {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some true):ρ.vars x < ρ.vars y:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  simpa using hr.symm

theorem le_of_condLt_false {B:ℕ} {x y:String} {ρ:Env}
    (h:(Cond.lt (.var x) (.var y)).evalB B ρ=some false):ρ.vars y≤ ρ.vars x:=by
  simp only [evalB_condLt_iff,evalB_var_iff] at h
  obtain ⟨a,b, ⟨rfl, -⟩, ⟨rfl, -⟩,hr⟩:=h
  have:=hr.symm
  simp only [decide_eq_false_iff_not,not_lt] at this
  exact this

theorem Spec.forRange (x m:String) (I:Env→ Prop) (N Kb K:ℕ)
    (hxB:∀ σ,I σ→ σ.vars x < B) (hmB:∀ σ,I σ→ σ.vars m < B)
    (hm:∀ σ,I σ→ σ.vars m=N) (hxN:∀ σ,I σ→ σ.vars x≤ N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb)
    (hPI:∀ σ,P σ→ I σ) (hK:∀ σ,P σ→ (Kb + 4) * (N - σ.vars x) + 4≤ K):
    Spec B P (.while (.lt (.var x) (.var m)) c) (fun _ σ' => I σ'∧ σ'.vars x=N) K:=by
  have hsize:(Cond.lt (Expr.var x) (Expr.var m)).size=3:=by simp
  refine ((Spec.while_potential (b:=.lt (.var x) (.var m)) (c:=c) I
    (fun σ => (Kb + 4) * (N - σ.vars x))
    (fun σ hI => evalB_condLt_vars (hxB σ hI) (hmB σ hI)) ?_ hPI ?_).post ?_)
  · intro σ hI hv
    have hlt:σ.vars x < N:=by
      have:=lt_of_condLt_true hv
      rw [hm σ hI] at this
      exact this
    obtain ⟨σ',hr,hI',hx'⟩:=hbody σ ⟨hI,hlt⟩
    refine ⟨σ',Kb,hr,hI', ?_⟩
    show 1 + 3 + Kb + (Kb + 4) * (N - σ'.vars x)≤ (Kb + 4) * (N - σ.vars x)
    have hdrop:N - σ'.vars x + 1=N - σ.vars x:=by rw [hx']; omega
    exact le_of_eq (by rw [← hdrop]; ring)
  · intro σ hσ
    show (Kb + 4) * (N - σ.vars x) + 1 + 3≤ K
    have h:=hK σ hσ
    have hre:(Kb + 4) * (N - σ.vars x) + 1 + 3=(Kb + 4) * (N - σ.vars x) + 4:=by ring
    rw [hre]
    exact h
  · intro σ σ' _ hq
    refine ⟨hq.1, ?_⟩
    have:=le_of_condLt_false hq.2
    have h₁:=hm σ' hq.1
    have h₂:=hxN σ' hq.1
    omega

theorem Spec.forRangeZero (x m:String) (I:Env→ Prop) (N Kb:ℕ) (hNB:N < B)
    (hxN:∀ σ,I σ→ σ.vars x≤ N) (hm:∀ σ,I σ→ σ.vars m=N)
    (hbody:Spec B (fun σ => I σ∧ σ.vars x < N) c
      (fun σ σ' => I σ'∧ σ'.vars x=σ.vars x + 1) Kb):
    Spec B (fun σ => I (σ.setVar x 0))
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c))
      (fun _ σ' => I σ'∧ σ'.vars x=N) ((Kb + 4) * N + 6):=by
  intro σ hσ
  obtain ⟨σ',hrun,hI',hxN'⟩:=
    (Spec.forRange x m I N Kb ((Kb + 4) * N + 4)
      (fun _ hτ => lt_of_le_of_lt (hxN _ hτ) hNB) (fun _ hτ => hm _ hτ ▸ hNB) hm hxN hbody
      (fun _ h => h)
      (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)).run hσ
  exact ⟨σ', (Run.seq (Run.assign (v:=0) (by simp; omega)) hrun).mono (by simp; omega),
    hI',hxN'⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

namespace RunStep

theorem eval_lit (B n:ℕ) (σ:Env) (h:n < B):
    (Expr.lit n).evalB B σ=some n:=evalB_lit h

theorem eval_var (B:ℕ) (σ:Env) (x:String) (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=evalB_var h

theorem eval_get (B:ℕ) (σ:Env) (a:String) (i:Expr) (k:ℕ)
    (hi:i.evalB B σ=some k) (hk:k < (σ.arrs a).length)
    (h:(σ.arrs a).getD k 0 < B):
    (Expr.get a i).evalB B σ=some ((σ.arrs a).getD k 0):=by
  refine evalB_get hi ?_ h
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  rfl

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_sub (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m - n < B):
    (Expr.bin .sub e f).evalB B σ=some (m - n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

theorem cond_eq_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m=n):
    (Cond.eq e f).evalB B σ=some true:=by
  rw [evalB_condEq he hf,h]; simp

theorem cond_eq_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m=n):
    (Cond.eq e f).evalB B σ=some false:=by
  rw [evalB_condEq he hf]; simp [h]

theorem cond_lt_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m < n):
    (Cond.lt e f).evalB B σ=some true:=by
  rw [evalB_condLt he hf]; simp [h]

theorem cond_lt_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m < n):
    (Cond.lt e f).evalB B σ=some false:=by
  rw [evalB_condLt he hf]; simp [h]

theorem skip (B:ℕ) (σ:Env):Run B .skip σ σ 1:=Run.skip

theorem assign (B:ℕ) (σ:Env) (x:String) (e:Expr) (v:ℕ)
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=Run.assign h

theorem store (B:ℕ) (σ:Env) (a:String) (i e:Expr) (idx v:ℕ)
    (hi:i.evalB B σ=some idx) (he:e.evalB B σ=some v)
    (hidx:idx < (σ.arrs a).length):
    Run B (.store a i e) σ (σ.setArr a idx v) (1 + i.size + e.size):=Run.store hi he hidx

theorem read (B:ℕ) (σ:Env) (x:String) (h:σ.inp ≠ []):
    Run B (.read x) σ { σ.setVar x (σ.inp.headD 0) with inp:=σ.inp.tail } 1:=by
  refine Run.read (v:=σ.inp.headD 0) (rest:=σ.inp.tail) ?_
  cases hl:σ.inp with
  | nil => exact absurd hl h
  | cons v rest => simp

theorem write (B:ℕ) (σ:Env) (e:Expr) (v:ℕ) (h:e.evalB B σ=some v):
    Run B (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size):=Run.write h

theorem seq (B:ℕ) (c d:Com) (σ σ' σ'':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):
    Run B (.seq c d) σ σ'' (K + K'):=h.seq h'

inductive SeqSplit:Com→ Com→ Com→ Prop

  | one (a r:Com):SeqSplit a r (.seq a r)

  | cons (a p r w:Com) (h:SeqSplit p r w):SeqSplit (.seq a p) r (.seq a w)

theorem ite_true (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_true hb h

theorem ite_false (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_false hb h

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax455465Proofs.RamFrames

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem array_length {c:Com} {σ τ:Env} {k:ℕ} (h:BigStep c σ τ k) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [length_arrs_setArr]
  | seq _ _ ih ih' => rw [ih',ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih',ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_array_length {B K:ℕ} {c:Com} {σ τ:Env} (h:Run B c σ τ K) (a:String):
    (τ.arrs a).length=(σ.arrs a).length:=by
  obtain ⟨_,_,hs⟩:=h.bigStep
  exact array_length hs a

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamWordBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

private theorem prefix_set (words buffer:List ℕ) (value:ℕ)
    (h:∀ i (hi:i < words.length),buffer[i]?=some words[i])
    (hroom:words.length < buffer.length):
    ∀ i (hi:i < (words ++ [value]).length),
      (buffer.set words.length value)[i]?=some (words ++ [value])[i]:=by
  intro i hi
  by_cases hlt:i < words.length
  · rw [← List.getElem_append_left' hlt,List.getElem?_set_ne (by omega:words.length ≠ i)]
    exact h i hlt
  · have he:i=words.length:=by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i
    simp [List.getElem?_set_self hroom]

theorem append_spec (B:ℕ) (array cursor:String) (words:List ℕ) (value:ℕ) (e:Expr)
    (h1:1 < B) (hlen:words.length + 1 < B):
    Spec B (fun σ => Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length < (σ.arrs array).length∧ e.evalB B σ=some value) (append array cursor e)
      (fun _ τ => Prefix (words ++ [value]) array τ∧ τ.vars cursor=words.length + 1)
      (e.size + 6):=by
  rintro σ ⟨hprefix,hcursor,hroom,he⟩
  have hindex:(Expr.var cursor).evalB B σ=some words.length:=by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm,hcursor ▸ (by omega:words.length < B)⟩
  have hstore:=Run.store hindex he hroom
  let ν:=σ.setArr array words.length value
  have hcounter:(Expr.add (.var cursor) (.lit 1)).evalB B ν=some (words.length + 1):=by
    apply evalB_bin (op:=.add) _ (evalB_lit h1) hlen
    rw [evalB_var_iff]
    exact ⟨by simpa [ν] using hcursor.symm,by simp [ν,hcursor]; omega⟩
  have hnext:=Run.assign (x:=cursor) hcounter
  refine ⟨ν.setVar cursor (words.length + 1), (hstore.seq hnext).mono (by simp [Expr.size]; omega), ?_⟩
  constructor
  · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_true] using
      prefix_set words (σ.arrs array) value hprefix hroom
  · simp

end Lax455465Proofs.RamWordBuffer

end

section

namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem word_spec (B v:ℕ) (h2:2 < B) (hv:v < B):
    Spec B (fun σ => σ.vars "size.value"=v) word
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 6):=by
  let I:=fun σ:Env => σ.vars "size.value" ≤ v∧
    σ.vars "size.count" + (σ.vars "size.value").size=v.size
  have hs:v.size≤ v:=Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hlo:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => I τ∧ (Cond.lt (.lit 0) (.var "size.value")).evalB B τ=some false)
      (12 * v.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "size.value").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))⟩
    · rintro σ ⟨hI,hcond⟩
      have hval:=hI.1.trans_lt hv
      have hp:0 < σ.vars "size.value" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hval)] at hcond
        simpa using hcond
      have hhalf:=WordSize.size_half (σ.vars "size.value") hp
      have hcounter:σ.vars "size.count" + 1 < B:=by
        have hsz:=Nat.size_pos.mpr hp
        have heq:=hI.2
        omega
      have hdiv:=(Nat.div_le_self (σ.vars "size.value") 2).trans_lt hval
      have hle:=(Nat.div_le_self (σ.vars "size.value") 2).trans hI.1
      (expose_names;
        (refine let c0:Env→ Prop:=(fun (σ_1 σ':Env) => And (I σ') (Nat.lt (Nat.size (Env.vars σ' "size.value")) (Nat.size (Env.vars σ_1 "size.value")))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "size.value") ((2:Nat)); let c2:Env:=Env.setVar σ "size.value" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=Env.vars c2 "size.count"; let c5:Nat:=c3 c4 ((1:Nat)); let c6:Env:=Env.setVar c2 "size.count" c5; let c7:Nat→ Nat:=c3 ((1:Nat)); let c8:Expr:=Expr.div (Expr.var "size.value") (Expr.lit ((2:Nat))); let c9:Nat:=c7 (Expr.size c8); let c10:Expr:=Expr.add (Expr.var "size.count") (Expr.lit ((1:Nat))); let c11:Nat:=c7 (Expr.size c10); @Exists.intro Env (fun (σ':Env) => And (Run B wordStep σ σ' ((8:Nat))) (c0 σ')) c6 (@And.intro (Run B wordStep σ c6 ((8:Nat))) (c0 c6) (RunStep.mono B wordStep σ c6 (c3 c9 c11) ((8:Nat)) (RunStep.seq B (Com.assign "size.value" c8) (Com.assign "size.count" c10) σ c2 c6 c9 c11 (RunStep.assign B σ "size.value" c8 c1 (RunStep.eval_div B σ (Expr.var "size.value") (Expr.lit ((2:Nat))) (Env.vars σ "size.value") ((2:Nat)) (RunStep.eval_var B σ "size.value" hval) (RunStep.eval_lit B ((2:Nat)) σ h2) hdiv)) (RunStep.assign B c2 "size.count" c10 c5 (RunStep.eval_add B c2 (Expr.var "size.count") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c2 "size.count" (?nAX_g6023_0_0_0)) (RunStep.eval_lit B ((1:Nat)) c2 (?nAX_g6023_0_0_1)) (?nAX_g6023_0_0_2)))) (?nAX_g6023_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [I]
      all_goals omega
    · rintro σ ⟨hvalue,hcount⟩
      simp [I,hvalue,hcount]
    · rintro σ ⟨hvalue,hcount⟩
      simp [hvalue]
  have hfinish:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 4):=hlo.post (by
    rintro σ τ _ ⟨hI,hcond⟩
    have hzero:τ.vars "size.value"=0:=by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))] at hcond
      simpa using hcond
    exact ⟨hzero,by simpa only [hzero,Nat.size_zero,Nat.add_zero] using hI.2⟩)
  rintro σ hvalue
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "size.count" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B wordLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size v)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "size.value") ((0:Nat))) (@Eq Nat (Env.vars σ' "size.count") (Nat.size v))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x τ:Env) => And (@Eq Nat (Env.vars τ "size.value") ((0:Nat))) (@Eq Nat (Env.vars τ "size.count") (Nat.size v)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B word σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "size.value") v) (@Eq Nat (Env.vars σ_1 "size.count") ((0:Nat)))) wordLoop c7 c4 hfinish c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B word σ w c6) (c8 w) (RunStep.mono B word σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "size.count" (Expr.lit ((0:Nat)))) wordLoop σ c0 w c12 c4 (RunStep.assign B σ "size.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6023_1_0_0))) left) (?nAX_g6023_1_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

open RamVirtualState Lax759944.BinaryWordEncoding

end Lax455465Proofs.RamBitSize

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.NativeLogarithms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open Lax455465Proofs

theorem size_eq (n:ℕ) (hn:0< n):n.size=Nat.log2 n+1:=by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  · have hp:2^Nat.log2 n≤ n:=by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hs:=Nat.lt_size.mpr hp
    omega

theorem small_spec (B n:ℕ) (hn:0< n) (hB:n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) small
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1) (12*n.size+10):=by
  intro σ hs
  let ν:=σ.setVar "size.value" n
  have r1:Run B (.assign "size.value" (.var "graph.n")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩)
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B n (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.log" n.size
  have hsize:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.log" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change n.size=Nat.log2 n+1; exact size_eq n hn⟩

theorem large_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) large
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.logarithm"=logarithm n) (12*(2*n).size+12):=by
  intro σ hs
  let ν:=σ.setVar "size.value" (2*n)
  have r1:Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩) (by change 2*n< B; omega))
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.logarithm" (2*n).size
  have hsize:(2*n).size≤2*n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.logarithm" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change (2*n).size=Nat.log2 (2*n)+1; exact size_eq (2*n) (by omega)⟩

theorem command_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1∧
        τ.vars "node.logarithm"=logarithm n) (12*n.size+12*(2*n).size+22):=by
  intro σ hs
  obtain ⟨ν,r1,p1⟩:=small_spec B n hn (by omega) σ hs
  obtain ⟨τ,r2,p2⟩:=large_spec B n hn hB ν p1.1
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1,
    (r2.frame_var "node.log" (by decide)).trans p1.2,p2.2⟩

end Lax263307Proofs.NativeLogarithms

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem adjacency_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:
    (adjacency G).length=n*n:=by
  simp [adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const]

open Lax109476Proofs

end Lax263307Proofs.NativeWeightReduction

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

theorem flattened_coordinate {α:Type*} (xs:List (List α)) (i:ℕ) (hi:i< xs.length)
    (j:ℕ) (hj:j< xs[i].length):
    xs.flatten[((xs.take i).map List.length).sum+j]?=some xs[i][j]:=by
  have he:xs=xs.take i++xs[i]::xs.drop (i+1):=by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hf:xs.flatten=(xs.take i).flatten++xs[i]++(xs.drop (i+1)).flatten:=by
    conv_lhs => rw [he]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
  rw [hf,List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_flatten]; omega)]
  rw [List.length_flatten]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

def matrix {n:ℕ} (f:Fin n→ Fin n→ ℕ):List ℕ:=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem matrix_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (i j:Fin n):
    (matrix f)[i.val*n+j.val]?=some (f i j):=by
  let xs:=List.ofFn fun i => List.ofFn (f i)
  have hi:i.val< xs.length:=by simpa only [xs,List.length_ofFn] using i.isLt
  have hj:j.val< xs[i.val].length:=by simpa only [xs,List.getElem_ofFn,List.length_ofFn] using j.isLt
  have hx:=flattened_coordinate xs i.val hi j.val hj
  have hp:((xs.take i.val).map List.length).sum=i.val*n:=by
    rw [List.map_take]
    have hm:xs.map List.length=List.replicate n n:=by
      dsimp only [xs]
      rw [List.map_ofFn,←List.ofFn_const]
      congr 1
      funext v
      exact List.length_ofFn
    rw [hm]
    simp [List.take_replicate,List.sum_replicate]
  simpa only [hp,matrix,xs,List.getElem_ofFn] using hx

def row {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val/n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact (Nat.div_lt_iff_lt_mul hn).mpr q.isLt⟩

def col {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val%n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact Nat.mod_lt _ hn⟩

theorem matrix_flat_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (q:Fin (n*n)):
    (matrix f)[q.val]?=some (f (row q) (col q)):=by
  have hx:=matrix_coordinate f (row q) (col q)
  have he:(row q).val*n+(col q).val=q.val:=by
    simpa only [row,col,Nat.mul_comm] using Nat.div_add_mod q.val n
  rwa [he] at hx

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def select {α:Type*}:ℕ→ List α→ ℕ→ List α
  | 0,_,_ => []
  | _+1, [],_ => []
  | k+1,a::xs,q =>
      if q< xs.length.choose (k+1) then select (k+1) xs q
      else a::select k xs (q-xs.length.choose (k+1))

theorem select_correct {α:Type*} (xs:List α) (k q:ℕ)
    (hq:q< xs.length.choose k):(xs.sublistsLen k)[q]?=some (select k xs q):=by
  induction xs generalizing k q with
  | nil =>
    cases k with
    | zero =>
      have:q=0:=by simpa using hq
      subst q
      simp [select]
    | succ k => simp at hq
  | cons a xs ih =>
    cases k with
    | zero =>
      have:q=0:=by simpa using hq
      subst q
      simp [select]
    | succ k =>
      rw [List.sublistsLen_succ_cons]
      by_cases hh:q< xs.length.choose (k+1)
      · rw [List.getElem?_append_left (by rwa [List.length_sublistsLen])]
        simpa only [select,if_pos hh] using ih (k+1) q hh
      · rw [List.getElem?_append_right (by rw [List.length_sublistsLen]; omega)]
        rw [List.length_sublistsLen,List.getElem?_map]
        have hrem:q-xs.length.choose (k+1)< xs.length.choose k:=by
          simp only [List.length_cons,Nat.choose_succ_succ,Nat.succ_eq_add_one] at hq
          omega
        rw [ih k _ hrem]
        simp only [Option.map_some,select,if_neg hh]

def table (n k:ℕ):List ℕ:=
  (List.ofFn fun i:Fin (n+1) => List.ofFn fun j:Fin (k+1) => i.val.choose j.val).flatten

theorem table_length (n k:ℕ):(table n k).length=(n+1)*(k+1):=by
  simp [table,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]
  ring

theorem table_coordinate (n k i j:ℕ) (hi:i≤ n) (hj:j≤ k):
    (table n k)[i*(k+1)+j]?=some (i.choose j):=by
  let xs:=List.ofFn fun i:Fin (n+1) => List.ofFn fun j:Fin (k+1) => i.val.choose j.val
  have hi':i< xs.length:=by simp only [xs,List.length_ofFn]; omega
  have hj':j< xs[i].length:=by simp only [xs,List.getElem_ofFn,List.length_ofFn]; omega
  have hh:=NativeBlowUp.flattened_coordinate xs i hi' j hj'
  have hm:xs.map List.length=List.replicate (n+1) (k+1):=by
    dsimp only [xs]
    rw [List.map_ofFn,←List.ofFn_const]
    congr 1
    funext i
    exact List.length_ofFn
  have hp:((xs.take i).map List.length).sum=i*(k+1):=by
    rw [List.map_take,hm]
    simp [List.take_replicate,List.sum_replicate,Nat.min_eq_left (by omega:i≤ n+1)]
  simpa only [table,xs,hp,List.getElem_ofFn] using hh

theorem coordinates_spec (B q d:ℕ) (_hd:0< d) (hq:q< B) (hdB:d< B):
    Spec B (fun σ => σ.vars "choose.i"=q∧ σ.vars "choose.cols"=d) coordinates
      (fun _ τ => τ.vars "choose.row"=q/d∧ τ.vars "choose.col"=q%d) 10:=by
  have hquot:q/d< B:=(Nat.div_le_self _ _).trans_lt hq
  have hmul:q/d*d< B:=(Nat.div_mul_le_self _ _).trans_lt hq
  have hrem:q-q/d*d< B:=(Nat.sub_le _ _).trans_lt hq
  rintro σ ⟨hσq,hσd⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 q d; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) q d; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.row") c1) (@Eq Nat (Env.vars τ "choose.col") c2)) σ; let c4:Nat:=c0 (Env.vars σ "choose.i") (Env.vars σ "choose.cols"); let c5:Env:=Env.setVar σ "choose.row" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "choose.i"; let c8:Nat:=c6 "choose.row"; let c9:Nat:=c6 "choose.cols"; let c10:Nat:=Nat.mul c8 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10; let c12:Env:=Env.setVar c5 "choose.col" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols"))); let c16:Expr:=Expr.sub (Expr.var "choose.i") (Expr.mul (Expr.var "choose.row") (Expr.var "choose.cols")); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B coordinates σ σ' ((10:Nat))) (c3 σ')) c12 (@And.intro (Run B coordinates σ c12 ((10:Nat))) (c3 c12) (RunStep.mono B coordinates σ c12 (c13 c15 c17) ((10:Nat)) (RunStep.seq B (Com.assign "choose.row" (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols"))) (Com.assign "choose.col" c16) σ c5 c12 c15 c17 (RunStep.assign B σ "choose.row" (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols")) c4 (RunStep.eval_div B σ (Expr.var "choose.i") (Expr.var "choose.cols") (Env.vars σ "choose.i") (Env.vars σ "choose.cols") (RunStep.eval_var B σ "choose.i" (?nAX_g7913_0_0_0)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7913_0_0_1)) ?_)) (RunStep.assign B c5 "choose.col" c16 c11 (RunStep.eval_sub B c5 (Expr.var "choose.i") (Expr.mul (Expr.var "choose.row") (Expr.var "choose.cols")) c7 c10 (RunStep.eval_var B c5 "choose.i" (?nAX_g7913_0_0_2)) (RunStep.eval_mul B c5 (Expr.var "choose.row") (Expr.var "choose.cols") c8 c9 (RunStep.eval_var B c5 "choose.row" ?_) (RunStep.eval_var B c5 "choose.cols" (?nAX_g7913_0_0_3)) ?_) (?nAX_g7913_0_0_4)))) (?nAX_g7913_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7913_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]

theorem entry_spec (B n k i j:ℕ) (hi:i≤ n) (hj:j≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.row"=i∧ σ.vars "choose.col"=j∧ σ.vars "choose.cols"=k+1∧
      Prefix ((table n k).take (i*(k+1)+j)) "choose.table" σ) entry
      (fun _ τ => τ.vars "choose.value"=i.choose j) 30:=by
  rintro σ ⟨hrow,hcol,hcols,hprefix⟩
  have hzero:0< B:=by omega
  have hone:1< B:=by omega
  have hiB:i< B:=by omega
  have hjB:j< B:=by omega
  have hkB:k+1< B:=by omega
  by_cases hj0:j=0
  · subst j
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i (Env.vars σ "choose.col"))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_0_0_0)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_0_0_2)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_4)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_0_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_0_0_6)) (?nAX_g7914_0_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_0_0_10)) (?nAX_g7914_0_0_11)) (?nAX_g7914_0_0_12) (?nAX_g7914_0_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_15)) (?nAX_g7914_0_0_16)) (?nAX_g7914_0_0_17) (?nAX_g7914_0_0_18)) (?nAX_g7914_0_0_19)))))) (?nAX_g7914_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · by_cases hi0:i=0
    · subst i
      have hchoose:Nat.choose 0 j=0:=Nat.choose_eq_zero_of_lt (by omega)
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose (Env.vars σ "choose.row") j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_1_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_1_0_3)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_1_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_1_0_6)) (?nAX_g7914_1_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_1_0_10)) (?nAX_g7914_1_0_11)) (?nAX_g7914_1_0_12) (?nAX_g7914_1_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_15)) (?nAX_g7914_1_0_16)) (?nAX_g7914_1_0_17) (?nAX_g7914_1_0_18)) (?nAX_g7914_1_0_19)))))) (?nAX_g7914_1_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]
    · have hjp:0< j:=by omega
      have hip:0 < i:=by omega
      have hrec:i.choose j=(i-1).choose (j-1)+(i-1).choose j:=by
        obtain ⟨i',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi0
        obtain ⟨j',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hj0
        simp [Nat.choose_succ_succ]
      have hlast:i*(k+1)+j<(table n k).length:=by rw [table_length]; nlinarith only [hi,hj]
      have hidx0:(i-1)*(k+1)+(j-1)< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        have hsubj:j-1+1=j:=by omega
        nlinarith only [hsubi,hsubj]
      have hidx1:(i-1)*(k+1)+j< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        nlinarith only [hsubi]
      have get (a b:ℕ) (ha:a≤ n) (hb:b≤ k) (hlt:a*(k+1)+b< i*(k+1)+j):
          (σ.arrs "choose.table")[a*(k+1)+b]?=some (a.choose b):=by
        have hp:=hprefix (a*(k+1)+b) (by rw [List.length_take]; omega)
        rw [List.getElem_take] at hp
        have hc:=table_coordinate n k a b ha hb
        rw [List.getElem?_eq_getElem (hlt.trans hlast)] at hc
        exact hp.trans hc
      have hget0:=get (i-1) (j-1) (by omega) (by omega) hidx0
      have hget1:=get (i-1) j (by omega) hj hidx1
      have hroom0:(i-1)*(k+1)+(j-1)<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget0
        contradiction
      have hroom1:(i-1)*(k+1)+j<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget1
        contradiction
      have hc0:=hcoeff (i-1) (by omega) (j-1) (by omega)
      have hc1:=hcoeff (i-1) (by omega) j hj
      have hsum:(i-1).choose (j-1)+(i-1).choose j< B:=hrec ▸ hcoeff i hi j hj
      have hdim:(table n k).length< B:=by rw [table_length]; omega
      have hprev:(i-1)*(k+1)< B:=by omega
      have hb0:(i-1)*(k+1)+(j-1)< B:=(hidx0.trans hlast).trans hdim
      have hb1:(i-1)*(k+1)+j< B:=(hidx1.trans hlast).trans hdim
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:List Nat:=Env.arrs c33 "choose.table"; let c35:Nat→ Nat→ Nat:= @List.getD Nat c34; let c36:String→ Nat:=Env.vars c33; let c37:Nat:=c36 "choose.prev"; let c38:Nat→ Nat:=c5 c37; let c39:Nat:=c36 "choose.col"; let c40:Nat:=c30 c39 ((1:Nat)); let c41:Nat:=c38 c40; let c42:Nat:=c35 c41 ((0:Nat)); let c43:Nat:=c38 c39; let c44:Nat:=c35 c43 ((0:Nat)); let c45:Nat:=c5 c42 c44; let c46:Env:=Env.setVar c33 "choose.value" c45; let c47:Nat:=c6 (Expr.size c14); let c48:Nat:=c6 (Expr.size c20); let c49:Nat:=c5 c47 c48; let c50:Nat:=c27 c49; let c51:Nat→ Prop:=Nat.lt c41; let c52:Nat:= @List.length Nat c34; let c53:Nat→ Prop:=Nat.lt c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_2_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_2_0_4)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c46 (@And.intro (Run B entry σ c46 ((30:Nat))) (c2 c46) (RunStep.mono B entry σ c46 (c8 c50) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c46 c50 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_5)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c46 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_6)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c46 c47 c48 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_7)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_2_0_8)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_2_0_9)) ?_)) (RunStep.assign B c33 "choose.value" c20 c45 (RunStep.eval_add B c33 c18 c19 c42 c44 (RunStep.eval_get B c33 "choose.table" c17 c41 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c37 c40 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c39 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_10)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_2_0_11)) ?_) ?_ ?_) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c43 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c37 c39 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_12)) ?_) ?_ ?_) ?_))))) (?nAX_g7914_2_0_13)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]

def Invariant (n k:ℕ) (σ:Env):Prop:=
  σ.vars "choose.cols"=k+1∧ σ.vars "choose.length"=(table n k).length∧
  σ.vars "choose.i"≤(table n k).length∧ (table n k).length≤(σ.arrs "choose.table").length∧
  Prefix ((table n k).take (σ.vars "choose.i")) "choose.table" σ

theorem step_spec (B n k:ℕ) (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => Invariant n k σ∧ σ.vars "choose.i"<(table n k).length) step
      (fun σ τ => Invariant n k τ∧ τ.vars "choose.i"=σ.vars "choose.i"+1) 50:=by
  rintro σ ⟨⟨hcols,hlen,hle,hroom,hprefix⟩,hlt⟩
  let q:=σ.vars "choose.i"
  let i:=q/(k+1)
  let j:=q%(k+1)
  have hlen':=table_length n k
  have hq:q<(n+1)*(k+1):=by rwa [←hlen']
  have hi:i≤ n:=by
    have:q/(k+1)< n+1:=(Nat.div_lt_iff_lt_mul (by omega)).mpr hq
    omega
  have hj:j≤ k:=by have hh:=Nat.mod_lt q (by omega:0< k+1); omega
  have hqB:q< B:=by omega
  have heq:i*(k+1)+j=q:=by
    dsimp [i,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod q (k+1)
  obtain ⟨ν,r1,p1⟩:=coordinates_spec B q (k+1) (by omega) hqB (by omega) σ ⟨rfl,hcols⟩
  obtain ⟨μ,r2,p2⟩:=entry_spec B n k i j hi hj hB hcoeff ν
    ⟨p1.1,p1.2,(r1.frame_var "choose.cols" (by decide)).trans hcols,
      by rw [heq]; simpa only [Prefix,r1.frame_arr "choose.table" (by decide)] using hprefix⟩
  have r12:=r1.seq r2
  have hqμ:μ.vars "choose.i"=q:=r12.frame_var "choose.i" (by decide)
  have htlen:((table n k).take q).length=q:=by rw [List.length_take]; omega
  have hvalue:(table n k)[q]=i.choose j:=by
    have hc:=table_coordinate n k i j hi hj
    rw [heq,List.getElem?_eq_getElem hlt] at hc
    exact Option.some.inj hc
  obtain ⟨τ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "choose.table" "choose.i"
    ((table n k).take q) (i.choose j) (.var "choose.value") (by omega) (by rw [htlen]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "choose.table" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨p2.symm,p2 ▸ hcoeff i hi j hj⟩⟩
  have ht:τ.vars "choose.i"=q+1:=by simpa only [htlen] using p3.2
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.cols" (by decide)).trans hcols,
    (rr.frame_var "choose.length" (by decide)).trans hlen,by rw [ht]; omega,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hlt,hvalue]
    exact p3.1

theorem command_spec (B n k:ℕ) (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.k"=k∧
      (n+1)*(k+1)≤(σ.arrs "choose.table").length) command
      (fun _ τ => Prefix (table n k) "choose.table" τ∧ τ.vars "choose.cols"=k+1)
      (54*(n+1)*(k+1)+16):=by
  have hl:=table_length n k
  have hloop:=Spec.forRangeZero "choose.i" "choose.length" (Invariant n k)
    (table n k).length 50 (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (step_spec B n k hB hcoeff)
  have hmeta:Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.k"=k) metadata
      (fun _ τ => τ.vars "choose.cols"=k+1∧ τ.vars "choose.length"=(n+1)*(k+1)) 10:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 k ((1:Nat)); let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c2 (c0 n ((1:Nat))) c1; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.cols") c1) (@Eq Nat (Env.vars τ "choose.length") c3)) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B metadata σ σ' ((10:Nat))) (c4 σ'); let c6:Nat:=c0 (Env.vars σ "choose.k") ((1:Nat)); let c7:Env:=Env.setVar σ "choose.cols" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "choose.n"; let c10:Nat:=c0 c9 ((1:Nat)); let c11:Nat:=c8 "choose.cols"; let c12:Nat:=c2 c10 c11; let c13:Env:=Env.setVar c7 "choose.length" c12; let c14:Nat→ Nat:=c0 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "choose.k") (Expr.lit ((1:Nat))); let c16:Nat:=c14 (Expr.size c15); let c17:Expr:=Expr.add (Expr.var "choose.n") (Expr.lit ((1:Nat))); let c18:Expr:=Expr.mul c17 (Expr.var "choose.cols"); let c19:Nat:=c14 (Expr.size c18); let c20:String→ Nat:=Env.vars c13; @And.casesOn (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k) (fun (x:And (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k)) => @Exists Env c5) a fun (left:@Eq Nat (Env.vars σ "choose.n") n) (right:@Eq Nat (Env.vars σ "choose.k") k) => @Exists.intro Env c5 c13 (@And.intro (Run B metadata σ c13 ((10:Nat))) (c4 c13) (RunStep.mono B metadata σ c13 (c0 c16 c19) ((10:Nat)) (RunStep.seq B (Com.assign "choose.cols" c15) (Com.assign "choose.length" c18) σ c7 c13 c16 c19 (RunStep.assign B σ "choose.cols" c15 c6 (RunStep.eval_add B σ (Expr.var "choose.k") (Expr.lit ((1:Nat))) (Env.vars σ "choose.k") ((1:Nat)) (RunStep.eval_var B σ "choose.k" (?nAX_g7919_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7919_0_0_1)) (?nAX_g7919_0_0_2))) (RunStep.assign B c7 "choose.length" c18 c12 (RunStep.eval_mul B c7 c17 (Expr.var "choose.cols") c10 c11 (RunStep.eval_add B c7 (Expr.var "choose.n") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "choose.n" (?nAX_g7919_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c7 (?nAX_g7919_0_0_4)) (?nAX_g7919_0_0_5)) (RunStep.eval_var B c7 "choose.cols" (?nAX_g7919_0_0_6)) ?_))) (?nAX_g7919_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7919_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
    all_goals omega
  rintro σ ⟨hn,hk,hroom⟩
  obtain ⟨ν,r1,p1⟩:=hmeta σ ⟨hn,hk⟩
  have hi:Invariant n k (ν.setVar "choose.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using p1.1
    · simpa only [vars_setVar,String.reduceEq,if_false,hl] using p1.2
    · rw [arrs_setVar,Lax455465Proofs.RamFrames.run_array_length r1,hl]
      exact hroom
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by rw [hl]; nlinarith),?_,p2.1.1⟩
  simpa only [p2.2,List.take_length] using p2.1.2.2.2.2

def bits:ℕ→ ℕ→ ℕ→ List ℕ
  | 0,_,_ => []
  | n+1,0,q => 0::bits n 0 q
  | n+1,k+1,q => if q< n.choose (k+1) then 0::bits n (k+1) q
      else 1::bits n k (q-n.choose (k+1))

theorem bits_length (n k q:ℕ):(bits n k q).length=n:=by
  induction n generalizing k q with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => simp [bits,ih]
    | succ k => simp only [bits]; split_ifs <;> simp [ih]

def decode {α:Type*} (xs:List α) (bs:List ℕ):List α:=
  (xs.zip bs).filterMap fun p => if p.2=1 then some p.1 else none

theorem decode_bits {α:Type*} (xs:List α) (k q:ℕ):
    decode xs (bits xs.length k q)=select k xs q:=by
  induction xs generalizing k q with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => simpa [decode,bits,select] using ih 0 q
    | succ k =>
      by_cases hq:q< xs.length.choose (k+1)
      · simpa [decode,bits,select,hq] using ih (k+1) q
      · simpa [decode,bits,select,hq] using congrArg (List.cons a) (ih k (q-xs.length.choose (k+1)))

def advance (remaining need rank:ℕ):ℕ × ℕ × ℕ:=
  if need=0 then (0,need,rank)
  else if rank<(remaining-1).choose need then (0,need,rank)
  else (1,need-1,rank-(remaining-1).choose need)

theorem bits_step (remaining need rank:ℕ) (h:0< remaining):
    bits remaining need rank=(advance remaining need rank).1::
      bits (remaining-1) (advance remaining need rank).2.1 (advance remaining need rank).2.2:=by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  cases need <;> simp [bits,advance]
  split_ifs <;> rfl

theorem advance_bounds (remaining need rank:ℕ):
    (advance remaining need rank).1≤1∧ (advance remaining need rank).2.1≤ need∧
      (advance remaining need rank).2.2≤ rank:=by
  unfold advance
  split_ifs <;> simp

theorem subset_entry_spec (B n k i need rank:ℕ) (hi:i< n) (hneed:need≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
      σ.vars "subset.i"=i∧ σ.vars "subset.need"=need∧ σ.vars "subset.rank"=rank∧
      Prefix (table n k) "choose.table" σ) subsetEntry
      (fun _ τ => τ.vars "subset.bit"=(advance (n-i) need rank).1∧
        τ.vars "subset.need"=(advance (n-i) need rank).2.1∧
        τ.vars "subset.rank"=(advance (n-i) need rank).2.2) 40:=by
  rintro σ ⟨hn,hcols,hiσ,hneedσ,hrankσ,hprefix⟩
  have hrow:n-i-1≤ n:=by omega
  have hidx:(n-i-1)*(k+1)+need<(table n k).length:=by
    rw [table_length]
    nlinarith only [hrow,hneed]
  have hc:=table_coordinate n k (n-i-1) need hrow hneed
  have hp:=hprefix ((n-i-1)*(k+1)+need) hidx
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget:=hp.trans hc
  have hroom:(n-i-1)*(k+1)+need<(σ.arrs "choose.table").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    contradiction
  have htableB:(table n k).length< B:=by rw [table_length]; omega
  have hidxB:=hidx.trans htableB
  have hmul:(n-i-1)*(k+1)< B:=by omega
  have hcB:=hcoeff (n-i-1) hrow need hneed
  by_cases hneed0:need=0
  · subst need
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Prod Nat (Prod Nat Nat):=advance (c2 n i) (Env.vars σ "subset.need") rank; let c4:Nat:= @Prod.fst Nat (Prod Nat Nat) c3; let c5:Prod Nat Nat:= @Prod.snd Nat (Prod Nat Nat) c3; let c6:Nat:= @Prod.fst Nat Nat c5; let c7:Nat:= @Prod.snd Nat Nat c5; let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "subset.bit") c4) (And (@Eq Nat (Env.vars τ "subset.need") c6) (@Eq Nat (Env.vars τ "subset.rank") c7))) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (c8 σ'); let c10:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c17:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c18:Expr:=Expr.mul c17 (Expr.var "choose.cols"); let c19:Expr:=Expr.add c18 (Expr.var "subset.need"); let c20:Expr:=Expr.get "choose.table" c19; let c21:Com:=Com.assign "subset.count" c20; let c22:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c24:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c25:Com:=Com.assign "subset.need" c24; let c26:Com:=Com.seq c23 c25; let c27:Com:=Com.seq c22 c26; let c28:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27; let c29:Com:=Com.seq c21 c28; let c30:String→ Nat:=Env.vars c10; let c31:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c32:Nat:=c2 c31 ((1:Nat)); let c33:Nat:=Nat.mul c32 (Env.vars σ "choose.cols"); let c34:Nat:=c11 c33 (Env.vars σ "subset.need"); let c35:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c34 ((0:Nat)); let c36:Env:=Env.setVar σ "subset.count" c35; let c37:String→ Nat:=Env.vars c36; let c38:Nat:=c37 "subset.rank"; let c39:Nat:=c37 "subset.count"; let c40:Prop:=Nat.lt c38 c39; let c41:Prop:=Not c40; let c42:Nat→ Env:=Env.setVar c36 "subset.bit"; let c43:Env:=c42 ((0:Nat)); let c44:Nat:=c12 (Expr.size c20); let c45:Nat→ Nat:=c11 c44; let c46:Nat→ Nat:=c11 (c12 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c47:Nat:=c46 c15; let c48:Nat:=c45 c47; let c49:String→ Nat:=Env.vars c43; let c50:Env:=c42 ((1:Nat)); let c51:String→ Nat:=Env.vars c50; let c52:Nat:=c51 "subset.rank"; let c53:Nat:=c51 "subset.count"; let c54:Nat:=c2 c52 c53; let c55:Env:=Env.setVar c50 "subset.rank" c54; let c56:Nat:=Env.vars c55 "subset.need"; let c57:Nat:=c2 c56 ((1:Nat)); let c58:Env:=Env.setVar c55 "subset.need" c57; let c59:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c60:Nat:=c12 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c61:Nat:=c12 (Expr.size c24); let c62:Nat:=c11 c60 c61; let c63:Nat:=c11 c59 c62; let c64:Nat:=c46 c63; let c65:Nat:=c45 c64; let c66:String→ Nat:=Env.vars c58; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c9) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c9 c10 (@And.intro (Run B subsetEntry σ c10 ((40:Nat))) (c8 c10) (RunStep.mono B subsetEntry σ c10 (c14 c15) ((40:Nat)) (RunStep.ite_true B c13 c16 c29 σ c10 c15 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_2)))) (?nAX_g7928_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c40 c41 (fun (x:Or c40 c41) => @Exists Env c9) (Classical.em c40) (fun (hcase_1:c40) => @Exists.intro Env c9 c43 (@And.intro (Run B subsetEntry σ c43 ((40:Nat))) (c8 c43) (RunStep.mono B subsetEntry σ c43 (c14 c48) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c43 c48 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_5)) hcase) (RunStep.seq B c21 c28 σ c36 c43 c44 c47 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_7)) (?nAX_g7928_0_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_9)) (?nAX_g7928_0_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_11)) (?nAX_g7928_0_0_12)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_13)) (?nAX_g7928_0_0_14)) (?nAX_g7928_0_0_15) (?nAX_g7928_0_0_16))) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c43 c15 (RunStep.cond_lt_true B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_17)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_18)) hcase_1) (RunStep.assign B c36 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c36 (?nAX_g7928_0_0_19)))))) (?nAX_g7928_0_0_20)) ?_)) fun (hcase_1:c41) => @Exists.intro Env c9 c58 (@And.intro (Run B subsetEntry σ c58 ((40:Nat))) (c8 c58) (RunStep.mono B subsetEntry σ c58 (c14 c65) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c58 c65 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_21)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_22)) hcase) (RunStep.seq B c21 c28 σ c36 c58 c44 c64 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_23)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_24)) (?nAX_g7928_0_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_26)) (?nAX_g7928_0_0_27)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_28)) (?nAX_g7928_0_0_29)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_30)) (?nAX_g7928_0_0_31)) (?nAX_g7928_0_0_32) (?nAX_g7928_0_0_33))) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c58 c63 (RunStep.cond_lt_false B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_34)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_35)) hcase_1) (RunStep.seq B c22 c26 c36 c50 c58 c59 c62 (RunStep.assign B c36 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c36 (?nAX_g7928_0_0_36))) (RunStep.seq B c23 c25 c50 c55 c58 c60 c61 (RunStep.assign B c50 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c54 (RunStep.eval_sub B c50 (Expr.var "subset.rank") (Expr.var "subset.count") c52 c53 (RunStep.eval_var B c50 "subset.rank" (?nAX_g7928_0_0_37)) (RunStep.eval_var B c50 "subset.count" (?nAX_g7928_0_0_38)) (?nAX_g7928_0_0_39))) (RunStep.assign B c55 "subset.need" c24 c57 (RunStep.eval_sub B c55 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c56 ((1:Nat)) (RunStep.eval_var B c55 "subset.need" (?nAX_g7928_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c55 (?nAX_g7928_0_0_41)) (?nAX_g7928_0_0_42)))))))) (?nAX_g7928_0_0_43)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,advance]
  · by_cases hsmall:rank<(n-i-1).choose need
    · have ha:advance (n-i) need rank=(0,need,rank):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((0:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") need) (@Eq Nat (Env.vars σ' "subset.rank") rank))); let c3:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c4:String→ Nat:=Env.vars c3; let c5:Prop:=And (@Eq Nat (c4 "subset.bit") ((0:Nat))) (And (@Eq Nat (c4 "subset.need") need) (@Eq Nat (c4 "subset.rank") rank)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c12:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c13:Expr:=Expr.mul c12 (Expr.var "choose.cols"); let c14:Expr:=Expr.add c13 (Expr.var "subset.need"); let c15:Expr:=Expr.get "choose.table" c14; let c16:Com:=Com.assign "subset.count" c15; let c17:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c18:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c19:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c20:Com:=Com.assign "subset.need" c19; let c21:Com:=Com.seq c18 c20; let c22:Com:=Com.seq c17 c21; let c23:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22; let c24:Com:=Com.seq c16 c23; let c25:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c26:Nat:=c25 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c27:Nat:=c25 c26 ((1:Nat)); let c28:Nat:=Nat.mul c27 (Env.vars σ "choose.cols"); let c29:Nat:=c6 c28 (Env.vars σ "subset.need"); let c30:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c29 ((0:Nat)); let c31:Env:=Env.setVar σ "subset.count" c30; let c32:String→ Nat:=Env.vars c31; let c33:Nat:=c32 "subset.rank"; let c34:Nat:=c32 "subset.count"; let c35:Prop:=Nat.lt c33 c34; let c36:Prop:=Not c35; let c37:Nat→ Env:=Env.setVar c31 "subset.bit"; let c38:Env:=c37 ((0:Nat)); let c39:String→ Nat:=Env.vars c38; let c40:Prop:=And (@Eq Nat (c39 "subset.bit") ((0:Nat))) (And (@Eq Nat (c39 "subset.need") need) (@Eq Nat (c39 "subset.rank") rank)); let c41:Nat:=c7 (Expr.size c15); let c42:Nat→ Nat:=c6 c41; let c43:Nat→ Nat:=c6 (c7 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c44:Nat:=c43 c10; let c45:Nat:=c42 c44; let c46:Nat→ Prop:=Nat.lt c29; let c47:Env:=c37 ((1:Nat)); let c48:String→ Nat:=Env.vars c47; let c49:Nat:=c48 "subset.rank"; let c50:Nat:=c48 "subset.count"; let c51:Nat:=c25 c49 c50; let c52:Env:=Env.setVar c47 "subset.rank" c51; let c53:Nat:=Env.vars c52 "subset.need"; let c54:Nat:=c25 c53 ((1:Nat)); let c55:Env:=Env.setVar c52 "subset.need" c54; let c56:String→ Nat:=Env.vars c55; let c57:Prop:=And (@Eq Nat (c56 "subset.bit") ((0:Nat))) (And (@Eq Nat (c56 "subset.need") need) (@Eq Nat (c56 "subset.rank") rank)); let c58:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c59:Nat:=c7 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c60:Nat:=c7 (Expr.size c19); let c61:Nat:=c6 c59 c60; let c62:Nat:=c6 c58 c61; let c63:Nat:=c43 c62; let c64:Nat:=c42 c63; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c2) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c2 c3 (@And.intro (Run B subsetEntry σ c3 ((40:Nat))) c5 (RunStep.mono B subsetEntry σ c3 (c9 c10) ((40:Nat)) (RunStep.ite_true B c8 c11 c24 σ c3 c10 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_2)))) (?nAX_g7928_1_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c35 c36 (fun (x:Or c35 c36) => @Exists Env c2) (Classical.em c35) (fun (hcase_1:c35) => @Exists.intro Env c2 c38 (@And.intro (Run B subsetEntry σ c38 ((40:Nat))) c40 (RunStep.mono B subsetEntry σ c38 (c9 c45) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c38 c45 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_5)) hcase) (RunStep.seq B c16 c23 σ c31 c38 c41 c44 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_7)) (?nAX_g7928_1_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_9)) (?nAX_g7928_1_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c38 c10 (RunStep.cond_lt_true B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_13)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.assign B c31 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c31 (?nAX_g7928_1_0_14)))))) (?nAX_g7928_1_0_15)) ?_)) fun (hcase_1:c36) => @Exists.intro Env c2 c55 (@And.intro (Run B subsetEntry σ c55 ((40:Nat))) c57 (RunStep.mono B subsetEntry σ c55 (c9 c64) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c55 c64 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_17)) hcase) (RunStep.seq B c16 c23 σ c31 c55 c41 c63 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_19)) (?nAX_g7928_1_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_21)) (?nAX_g7928_1_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c55 c62 (RunStep.cond_lt_false B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_25)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.seq B c17 c21 c31 c47 c55 c58 c61 (RunStep.assign B c31 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c31 (?nAX_g7928_1_0_26))) (RunStep.seq B c18 c20 c47 c52 c55 c59 c60 (RunStep.assign B c47 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c51 (RunStep.eval_sub B c47 (Expr.var "subset.rank") (Expr.var "subset.count") c49 c50 (RunStep.eval_var B c47 "subset.rank" (?nAX_g7928_1_0_27)) (RunStep.eval_var B c47 "subset.count" ?_) (?nAX_g7928_1_0_28))) (RunStep.assign B c52 "subset.need" c19 c54 (RunStep.eval_sub B c52 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c53 ((1:Nat)) (RunStep.eval_var B c52 "subset.need" (?nAX_g7928_1_0_29)) (RunStep.eval_lit B ((1:Nat)) c52 (?nAX_g7928_1_0_30)) (?nAX_g7928_1_0_31)))))))) (?nAX_g7928_1_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
    · have ha:advance (n-i) need rank=(1,need-1,rank-(n-i-1).choose need):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Nat:=c2 need ((1:Nat)); let c4:Nat:=c2 rank (Nat.choose (c2 (c2 n i) ((1:Nat))) need); let c5:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((1:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") c3) (@Eq Nat (Env.vars σ' "subset.rank") c4))); let c6:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c7:String→ Nat:=Env.vars c6; let c8:Prop:=And (@Eq Nat (c7 "subset.bit") ((1:Nat))) (And (@Eq Nat (c7 "subset.need") c3) (@Eq Nat (c7 "subset.rank") c4)); let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c12:Nat→ Nat:=c9 (c10 (Cond.size c11)); let c13:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c14:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c15:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c16:Expr:=Expr.mul c15 (Expr.var "choose.cols"); let c17:Expr:=Expr.add c16 (Expr.var "subset.need"); let c18:Expr:=Expr.get "choose.table" c17; let c19:Com:=Com.assign "subset.count" c18; let c20:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c21:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c22:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.need" c22; let c24:Com:=Com.seq c21 c23; let c25:Com:=Com.seq c20 c24; let c26:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25; let c27:Com:=Com.seq c19 c26; let c28:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c29:Nat:=c2 c28 ((1:Nat)); let c30:Nat:=Nat.mul c29 (Env.vars σ "choose.cols"); let c31:Nat:=c9 c30 (Env.vars σ "subset.need"); let c32:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c31 ((0:Nat)); let c33:Env:=Env.setVar σ "subset.count" c32; let c34:String→ Nat:=Env.vars c33; let c35:Nat:=c34 "subset.rank"; let c36:Nat:=c34 "subset.count"; let c37:Prop:=Nat.lt c35 c36; let c38:Prop:=Not c37; let c39:Nat→ Env:=Env.setVar c33 "subset.bit"; let c40:Env:=c39 ((0:Nat)); let c41:String→ Nat:=Env.vars c40; let c42:Prop:=And (@Eq Nat (c41 "subset.bit") ((1:Nat))) (And (@Eq Nat (c41 "subset.need") c3) (@Eq Nat (c41 "subset.rank") c4)); let c43:Nat:=c10 (Expr.size c18); let c44:Nat→ Nat:=c9 c43; let c45:Nat→ Nat:=c9 (c10 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c46:Nat:=c45 c13; let c47:Nat:=c44 c46; let c48:Nat→ Prop:=Nat.lt c31; let c49:Env:=c39 ((1:Nat)); let c50:String→ Nat:=Env.vars c49; let c51:Nat:=c50 "subset.rank"; let c52:Nat:=c50 "subset.count"; let c53:Nat:=c2 c51 c52; let c54:Env:=Env.setVar c49 "subset.rank" c53; let c55:Nat:=Env.vars c54 "subset.need"; let c56:Nat:=c2 c55 ((1:Nat)); let c57:Env:=Env.setVar c54 "subset.need" c56; let c58:String→ Nat:=Env.vars c57; let c59:Prop:=And (@Eq Nat (c58 "subset.bit") ((1:Nat))) (And (@Eq Nat (c58 "subset.need") c3) (@Eq Nat (c58 "subset.rank") c4)); let c60:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c61:Nat:=c10 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c62:Nat:=c10 (Expr.size c22); let c63:Nat:=c9 c61 c62; let c64:Nat:=c9 c60 c63; let c65:Nat:=c45 c64; let c66:Nat:=c44 c65; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c5 c6 (@And.intro (Run B subsetEntry σ c6 ((40:Nat))) c8 (RunStep.mono B subsetEntry σ c6 (c12 c13) ((40:Nat)) (RunStep.ite_true B c11 c14 c27 σ c6 c13 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_2)))) (?nAX_g7928_2_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c37 c38 (fun (x:Or c37 c38) => @Exists Env c5) (Classical.em c37) (fun (hcase_1:c37) => @Exists.intro Env c5 c40 (@And.intro (Run B subsetEntry σ c40 ((40:Nat))) c42 (RunStep.mono B subsetEntry σ c40 (c12 c47) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c40 c47 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_5)) hcase) (RunStep.seq B c19 c26 σ c33 c40 c43 c46 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_7)) (?nAX_g7928_2_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_9)) (?nAX_g7928_2_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c40 c13 (RunStep.cond_lt_true B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_13)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.assign B c33 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c33 (?nAX_g7928_2_0_14)))))) (?nAX_g7928_2_0_15)) ?_)) fun (hcase_1:c38) => @Exists.intro Env c5 c57 (@And.intro (Run B subsetEntry σ c57 ((40:Nat))) c59 (RunStep.mono B subsetEntry σ c57 (c12 c66) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c57 c66 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_17)) hcase) (RunStep.seq B c19 c26 σ c33 c57 c43 c65 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_19)) (?nAX_g7928_2_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_21)) (?nAX_g7928_2_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c57 c64 (RunStep.cond_lt_false B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_25)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.seq B c20 c24 c33 c49 c57 c60 c63 (RunStep.assign B c33 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g7928_2_0_26))) (RunStep.seq B c21 c23 c49 c54 c57 c61 c62 (RunStep.assign B c49 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c53 (RunStep.eval_sub B c49 (Expr.var "subset.rank") (Expr.var "subset.count") c51 c52 (RunStep.eval_var B c49 "subset.rank" (?nAX_g7928_2_0_27)) (RunStep.eval_var B c49 "subset.count" ?_) (?nAX_g7928_2_0_28))) (RunStep.assign B c54 "subset.need" c22 c56 (RunStep.eval_sub B c54 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c55 ((1:Nat)) (RunStep.eval_var B c54 "subset.need" (?nAX_g7928_2_0_29)) (RunStep.eval_lit B ((1:Nat)) c54 (?nAX_g7928_2_0_30)) (?nAX_g7928_2_0_31)))))))) (?nAX_g7928_2_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
      all_goals omega

def SubsetInvariant (n k rank:ℕ) (σ:Env):Prop:=
  σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
  Prefix (table n k) "choose.table" σ∧ n≤(σ.arrs "subset.bits").length∧
  σ.vars "subset.i"≤ n∧ σ.vars "subset.need"≤ k∧ σ.vars "subset.rank"≤ rank∧
  Prefix ((bits n k rank).take (σ.vars "subset.i")) "subset.bits" σ∧
  (bits n k rank).drop (σ.vars "subset.i")=
    bits (n-σ.vars "subset.i") (σ.vars "subset.need") (σ.vars "subset.rank")

theorem subset_step_spec (B n k rank:ℕ) (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => SubsetInvariant n k rank σ∧ σ.vars "subset.i"< n) subsetStep
      (fun σ τ => SubsetInvariant n k rank τ∧ τ.vars "subset.i"=σ.vars "subset.i"+1) 50:=by
  rintro σ ⟨⟨hn,hcols,htable,hroom,hle,hneed,hq,hprefix,htail⟩,hlt⟩
  let i:=σ.vars "subset.i"
  let need:=σ.vars "subset.need"
  let q:=σ.vars "subset.rank"
  let a:=advance (n-i) need q
  let xs:=bits n k rank
  have hlen:xs.length=n:=bits_length _ _ _
  have hab:=advance_bounds (n-i) need q
  have htail':xs.drop i=a.1::bits (n-i-1) a.2.1 a.2.2:=by
    rw [htail,bits_step (n-i) need q (by omega)]
  have hval:xs[i]=a.1:=by
    have he:=congrArg (fun ys:List ℕ => ys[0]?) htail'
    simp only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] at he
    rw [List.getElem?_eq_getElem (by omega)] at he
    exact Option.some.inj he
  have hnext:xs.drop (i+1)=bits (n-(i+1)) a.2.1 a.2.2:=by
    rw [←List.drop_drop,htail']
    simp only [List.drop_succ_cons,List.drop_zero,Nat.sub_sub]
  obtain ⟨ν,r1,p1⟩:=subset_entry_spec B n k i need q hlt hneed hB (hq.trans_lt hrank) hcoeff σ
    ⟨hn,hcols,rfl,rfl,rfl,htable⟩
  have hiν:ν.vars "subset.i"=i:=r1.frame_var "subset.i" (by decide)
  have htlen:(xs.take i).length=i:=by rw [List.length_take,hlen]; omega
  have hbit:a.1< B:=hab.1.trans_lt (by omega)
  obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "subset.i"
    (xs.take i) a.1 (.var "subset.bit") (by omega) (by rw [htlen]; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hbit⟩⟩
  have ht:τ.vars "subset.i"=i+1:=by simpa only [htlen] using p2.2
  have htn:τ.vars "subset.need"=a.2.1:=(r2.frame_var "subset.need" (by decide)).trans p1.2.1
  have htq:τ.vars "subset.rank"=a.2.2:=(r2.frame_var "subset.rank" (by decide)).trans p1.2.2
  have rr:=r1.seq r2
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.n" (by decide)).trans hn,
    (rr.frame_var "choose.cols" (by decide)).trans hcols,?_,?_,by rw [ht]; omega,
    by rw [htn]; exact hab.2.1.trans hneed,by rw [htq]; exact hab.2.2.trans hq,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "choose.table" (by decide)] using htable
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem (by rw [bits_length]; exact hlt),hval]
    exact p2.1
  · rw [ht,htn,htq]
    exact hnext

theorem subset_command_spec (B n k rank:ℕ) (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
      σ.vars "subset.need"=k∧ σ.vars "subset.rank"=rank∧
      Prefix (table n k) "choose.table" σ∧ n≤(σ.arrs "subset.bits").length) subsetCommand
      (fun _ τ => Prefix (bits n k rank) "subset.bits" τ) (54*n+6):=by
  have hloop:=Spec.forRangeZero "subset.i" "choose.n" (SubsetInvariant n k rank) n 50
    (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.1) (subset_step_spec B n k rank hB hrank hcoeff)
  rintro σ ⟨hn,hcols,hneed,hq,htable,hroom⟩
  have hi:SubsetInvariant n k rank (σ.setVar "subset.i" 0):=by
    refine ⟨?_,?_,htable,hroom,by simp,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcols
    · simp only [vars_setVar,String.reduceEq,if_false,hneed,le_refl]
    · simp only [vars_setVar,String.reduceEq,if_false,hq,le_refl]
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp only [vars_setVar,String.reduceEq,if_true,if_false,List.drop_zero,Nat.sub_zero,hneed,hq]
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr,?_⟩
  have ht:(bits n k rank).take n=bits n k rank:=List.take_of_length_le (by rw [bits_length])
  simpa only [p.2,ht] using p.1.2.2.2.2.2.2.2.1

theorem bits_binary (n k rank:ℕ):∀ b∈bits n k rank,b=0∨ b=1:=by
  induction n generalizing k rank with
  | zero => simp [bits]
  | succ n ih =>
    intro b hb
    cases k with
    | zero =>
      simp only [bits,List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact ih _ _ b hb
    | succ k =>
      by_cases h:rank< n.choose (k+1)
      · simp only [bits,if_pos h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inl rfl
        · exact ih _ _ b hb
      · simp only [bits,if_neg h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact ih _ _ b hb

theorem decode_get {α:Type*} (xs:List α) (bs:List ℕ) (hnd:xs.Nodup)
    (hlen:bs.length=xs.length) (i:ℕ) (hi:i< xs.length):
    xs[i]∈decode xs bs↔ bs[i]=1:=by
  constructor
  · intro h
    obtain ⟨p,hp,hval⟩:=List.mem_filterMap.mp h
    obtain ⟨j,hj,hpj⟩:=List.mem_iff_getElem.mp hp
    have hjx:j< xs.length:=by simpa only [List.length_zip,hlen,Nat.min_self] using hj
    have hjb:j< bs.length:=by omega
    rw [List.getElem_zip] at hpj
    subst p
    dsimp only at hval
    split_ifs at hval with hb
    · have hx:xs[j]=xs[i]:=Option.some.inj hval
      have he:j=i:=(List.Nodup.getElem_inj_iff hnd).mp hx
      subst j
      exact hb
  · intro hb
    apply List.mem_filterMap.mpr
    refine ⟨(xs[i],bs[i]),?_,?_⟩
    · have hz:i<(xs.zip bs).length:=by simp only [List.length_zip,hlen,Nat.min_self]; exact hi
      have hh:=List.getElem_mem hz
      simpa only [List.getElem_zip] using hh
    · simp [hb]

theorem bits_encoding (n k rank:ℕ):
    bits n k rank=Lax263307.IndependentSetEncoding.encodeOutput
      (decode (List.finRange n) (bits n k rank)).toFinset:=by
  let bs:=bits n k rank
  let I:=(decode (List.finRange n) bs).toFinset
  have hlen:bs.length=n:=bits_length _ _ _
  apply List.ext_getElem
  · simpa [Lax263307.IndependentSetEncoding.encodeOutput] using hlen
  · intro i hi hi'
    have hin:i< n:=by simpa only [bits_length] using hi
    have hxs:i<(List.finRange n).length:=by simpa using hin
    have hd:=decode_get (List.finRange n) bs (List.nodup_finRange n) (by simpa using hlen) i hxs
    simp only [List.getElem_finRange] at hd
    have hget:(Lax263307.IndependentSetEncoding.encodeOutput I)[i]=
        if (⟨i,hin⟩:Fin n)∈I then 1 else 0:=List.getElem_ofFn hi'
    change bs[i]=(Lax263307.IndependentSetEncoding.encodeOutput I)[i]
    rw [hget]
    by_cases hb:bs[i]=1
    · have hm:(⟨i,hin⟩:Fin n)∈I:=List.mem_toFinset.mpr (hd.mpr hb)
      rw [if_pos hm]
      exact hb
    · have hz:bs[i]=0:=(bits_binary n k rank _ (List.getElem_mem hi)).resolve_right hb
      have hm:(⟨i,hin⟩:Fin n)∉I:=fun h => hb (hd.mp (List.mem_toFinset.mp h))
      rw [if_neg hm]
      exact hz

theorem candidate_coordinate (n k rank:ℕ) (hrank:rank< n.choose k):
    (Lax263307.ExhaustiveTargets.candidates n k)[rank]?=
      some (decode (List.finRange n) (bits n k rank)).toFinset:=by
  have hs:=select_correct (List.finRange n) k rank (by simpa using hrank)
  rw [Lax263307.ExhaustiveTargets.candidates,List.getElem?_map,hs]
  simp only [Option.map_some]
  congr 2
  have hd:=decode_bits (List.finRange n) k rank
  simpa only [List.length_finRange] using hd.symm

end Lax263307Proofs.NativeCombinations

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

theorem mask_test_bit {n:ℕ} (I:Finset (Fin n)) (j:ℕ):
    (mask I).testBit j=decide (j∈I.image Fin.val):=by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I)↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_empty (n:ℕ):mask (∅:Finset (Fin n))=0:=by
  simp [mask,Lax263307.NativeCatalog.subsetMask,Finset.equivBitIndices]

theorem mask_bound {n:ℕ} (I:Finset (Fin n)):mask I<2^n:=by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro hjm
  obtain ⟨v,hv,hvj⟩:=Finset.mem_image.mp hjm
  have hvn:=v.isLt
  omega

theorem mask_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    mask (insert v I)=Nat.lor (mask I) (2^v.val):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j=((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he:j=v.val <;> by_cases hm:j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n:ℕ} (I:Finset (Fin n)) (i:ℕ):Finset (Fin n):=
  I.filter fun v => v.val < i

theorem prefix_zero {n:ℕ} (I:Finset (Fin n)):initialSet I 0=∅:=by simp [initialSet]

theorem prefix_full {n:ℕ} (I:Finset (Fin n)):initialSet I n=I:=by simp [initialSet]

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

theorem prefix_step {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    Nat.lor (mask (initialSet I i)) ((if (⟨i,hi⟩:Fin n)∈I then 1 else 0)*2^i)=mask (initialSet I (i+1)):=by
  rw [prefix_succ I i hi]
  by_cases h:(⟨i,hi⟩:Fin n)∈I
  · simp only [if_pos h,one_mul,mask_insert]
  · simp [h]

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

theorem step_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant I σ∧ σ.vars "mask.i"< n) step
      (fun σ τ => Invariant I τ∧ τ.vars "mask.i"=σ.vars "mask.i"+1) 11:=by
  rintro σ ⟨⟨hn,hle,hbits,hmask⟩,hlt⟩
  let i:=σ.vars "mask.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈I then 1 else 0
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbitB:bit< B:=by omega
  have hiB:i< B:=by omega
  have hpow:2^i<2^n:=Nat.pow_lt_pow_right (by omega) hlt
  have hshift:bit*2^i< B:=(by simpa only [one_mul] using Nat.mul_le_mul_right (2^i) hbit:bit*2^i≤2^i).trans_lt (hpow.trans hm)
  have hget:(σ.arrs "subset.bits")[i]?=some bit:=by
    have hh:=hbits i (by simpa [encodeOutput] using hlt)
    simpa [encodeOutput,bit] using hh
  have hprev:mask (initialSet I i)< B:=(mask_bound _).trans hm
  have hnext:mask (initialSet I (i+1))< B:=(mask_bound _).trans hm
  have hval:(Expr.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))).evalB B σ=
      some (mask (initialSet I (i+1))):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
      (evalB_bin (op:=.shiftl) (evalB_get (evalB_var hiB) hget hbitB) (evalB_var hiB) hshift)
      (by change Nat.lor (mask (initialSet I i)) (bit*2^i)< B; rw [prefix_step]; exact hnext)
    simpa only [Bop.apply_or,Bop.apply_shiftl,←show σ.vars "mask.i"=i from rfl,bit,prefix_step] using hh
  let ν:=σ.setVar "mask.value" (mask (initialSet I (i+1)))
  have r1:Run B (.assign "mask.value"
      (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i")))) σ ν 7:=
    Run.assign hval
  have hiν:ν.vars "mask.i"=i:=by simp [ν,i]
  let τ:=ν.setVar "mask.i" (i+1)
  have r2:Run B (.assign "mask.i" (.add (.var "mask.i") (.lit 1))) ν τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1< B; omega))
  have rr:=r1.seq r2
  have ht:τ.vars "mask.i"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,by rw [ht]; omega,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hbits
  · simp [τ,ν]

theorem command_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Prefix (encodeOutput I) "subset.bits" σ) command
      (fun _ τ => τ.vars "mask.value"=mask I) (15*n+8):=by
  have hloop:=Spec.forRangeZero "mask.i" "graph.n" (Invariant I) n 11 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hbits⟩
  let ν:=σ.setVar "mask.value" 0
  have r1:Run B (.assign "mask.value" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant I (ν.setVar "mask.i" 0):=by
    refine ⟨?_,by simp,hbits,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,prefix_zero,mask_empty]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
  simpa only [p2.2,prefix_full] using p2.1.2.2.2

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeZeroScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def prefixOK (xs:List ℕ) (i:ℕ):ℕ:=
  if (xs.take i).all (fun x => x==0) then 1 else 0

theorem prefix_ok_zero (xs:List ℕ):prefixOK xs 0=1:=by simp [prefixOK]

theorem prefix_ok_le (xs:List ℕ) (i:ℕ):prefixOK xs i≤1:=by
  unfold prefixOK
  split_ifs <;> omega

theorem prefix_ok_succ (xs:List ℕ) (i:ℕ) (hi:i< xs.length):
    prefixOK xs (i+1)=if xs[i]=0 then prefixOK xs i else 0:=by
  unfold prefixOK
  rw [List.take_succ_eq_append_getElem hi,List.all_append]
  cases h:(xs.take i).all (fun x => x==0) <;> by_cases hx:xs[i]=0 <;> simp [hx]

theorem prefix_ok_full (xs:List ℕ):prefixOK xs xs.length=1↔ ∀ x∈xs,x=0:=by
  simp [prefixOK,List.all_eq_true]

theorem update_spec (B i bit ok:ℕ) (hi:i+1< B) (hbit:bit< B) (_hok:ok≤1) (h1:1< B):
    Spec B (fun σ => σ.vars "test.i"=i∧ σ.vars "test.bit"=bit∧ σ.vars "test.ok"=ok)
      update (fun _ τ => τ.vars "test.i"=i+1∧ τ.vars "test.ok"=if bit=0 then ok else 0) 10:=by
  by_cases hbit0:bit=0
  · subst bit
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") ((0:Nat))) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c1:Prop:=And c0 (@Eq Nat (Env.vars σ "test.ok") ok); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 i ((1:Nat)); let c4:Nat:= @ite Nat (@Eq Nat ((0:Nat)) ((0:Nat))) (instDecidableEqNat ((0:Nat)) ((0:Nat))) ok ((0:Nat)); let c5:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c3) (@Eq Nat (Env.vars τ "test.ok") c4)) σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:=Not c0; let c9:Nat:=c2 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c2 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c2 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c2 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c1 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c1) => c7) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c1) => @And.casesOn c0 (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c1) => c7) right fun (left_1:c0) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c0 c8 (fun (x:Or c0 c8) => c7) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c6 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c5 c10) (RunStep.mono B update σ c10 (c2 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_0_0_1)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_0_0_2)))) (?nAX_g7963_0_0_3)) ?_)) fun (hcase:c8) => @Exists.intro Env c6 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c5 c22) (RunStep.mono B update σ c22 (c2 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hbit))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_0_0_6)))) (?nAX_g7963_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 i ((1:Nat)); let c3:Nat:= @ite Nat (@Eq Nat bit ((0:Nat))) (instDecidableEqNat bit ((0:Nat))) ok ((0:Nat)); let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c2) (@Eq Nat (Env.vars τ "test.ok") c3)) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c4 σ'); let c6:Prop:= @Exists Env c5; let c7:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c8:Prop:=Not c7; let c9:Nat:=c1 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c1 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c1 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c1 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c0 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c0) => c6) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c0) => c6) right fun (left_1:@Eq Nat (Env.vars σ "test.bit") bit) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c6) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c5 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c4 c10) (RunStep.mono B update σ c10 (c1 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_1)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_1_0_2)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_1_0_3)))) (?nAX_g7963_1_0_4)) ?_)) fun (hcase:c8) => @Exists.intro Env c5 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c4 c22) (RunStep.mono B update σ c22 (c1 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_6)) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_7)))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_1_0_8)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_1_0_9)))) (?nAX_g7963_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]

def Invariant (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "test.limit"=xs.length∧ σ.vars "test.i"≤ xs.length∧
  σ.vars "test.ok"=prefixOK xs (σ.vars "test.i")

theorem command_spec (B:ℕ) (xs:List ℕ) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+2< B) (hwords:∀ x∈xs,x< B)
    (hri:"test.i"∉read.wvars) (hrl:"test.limit"∉read.wvars) (hro:"test.ok"∉read.wvars)
    (hinit:∀ σ,P σ→ P ((σ.setVar "test.ok" 1).setVar "test.i" 0))
    (hupdate:∀ σ τ,Run B update σ τ 10→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "test.i"=i) read
      (fun _ τ => P τ∧ τ.vars "test.bit"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "test.limit"=xs.length) (command read)
      (fun _ τ => P τ∧ τ.vars "test.ok"=prefixOK xs xs.length)
      ((K+14)*xs.length+8):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant P xs σ∧ σ.vars "test.i"< xs.length) (body read)
      (fun σ τ => Invariant P xs τ∧ τ.vars "test.i"=σ.vars "test.i"+1) (K+10):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hok⟩,hlt⟩
    let i:=σ.vars "test.i"
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "test.i"=i:=r1.frame_var "test.i" hri
    have hokν:ν.vars "test.ok"=prefixOK xs i:=(r1.frame_var "test.ok" hro).trans hok
    obtain ⟨τ,r2,p2⟩:=update_spec B i xs[i] (prefixOK xs i) (by dsimp [i]; omega)
      (hwords _ (List.getElem_mem hlt)) (prefix_ok_le xs i) h1 ν ⟨hiν,p1.2,hokν⟩
    have hPτ:P τ:=hupdate ν τ r2 p1.1
    refine ⟨τ,r1.seq r2,⟨hPτ,?_,by rw [p2.1]; omega,?_⟩,p2.1⟩
    · exact (r2.frame_var "test.limit" (by decide)).trans ((r1.frame_var "test.limit" hrl).trans hlen)
    · rw [p2.1,prefix_ok_succ xs i hlt]
      exact p2.2
  have hloop:=Spec.forRangeZero "test.i" "test.limit" (Invariant P xs) xs.length (K+10)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hPσ,hlen⟩
  let ν:=σ.setVar "test.ok" 1
  have r1:Run B (.assign "test.ok" (.lit 1)) σ ν 2:=Run.assign (evalB_lit h1)
  have hi:Invariant P xs (ν.setVar "test.i" 0):=by
    refine ⟨?_,?_,by simp,?_⟩
    · exact hinit σ hPσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hlen
    · simp [ν,prefix_ok_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  simpa only [p2.2] using p2.1.2.2.2

end Lax263307Proofs.NativeZeroScan

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeIndependentTest

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

def pairValue {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):ℕ:=
  (if u∈I then 1 else 0)*(if v∈I then 1 else 0)*(if G.Adj u v then 1 else 0)

theorem pair_value_le {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v≤1:=by
  unfold pairValue
  split_ifs <;> norm_num

theorem pair_value_zero {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v=0↔ (u∈I→ v∈I→ ¬G.Adj u v):=by
  unfold pairValue
  split_ifs <;> simp_all

def values {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):List ℕ:=
  List.ofFn fun q:Fin (n*n) => pairValue G I (NativeBlowUp.row q) (NativeBlowUp.col q)

theorem values_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):(values G I).length=n*n:=List.length_ofFn

theorem values_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):
    NativeZeroScan.prefixOK (values G I) (n*n)=1↔ G.IsIndepSet (I:Set (Fin n)):=by
  rw [←values_length G I,NativeZeroScan.prefix_ok_full]
  constructor
  · intro h u hu v hv huv
    let q:Fin (n*n):= ⟨u.val*n+v.val,by nlinarith only [u.isLt,v.isLt]⟩
    have hn:0< n:=by omega
    have hrow:NativeBlowUp.row q=u:=by
      apply Fin.ext
      dsimp [NativeBlowUp.row,q]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt]
      omega
    have hcol:NativeBlowUp.col q=v:=by
      apply Fin.ext
      simp [NativeBlowUp.col,q,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
    have hh:=h _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
    rw [hrow,hcol,pair_value_zero] at hh
    exact hh hu hv
  · intro h z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    rw [pair_value_zero]
    intro hu hv hadj
    exact h hu hv hadj.ne hadj

theorem read_spec (B n q a b e:ℕ) (graphArray membershipArray:String)
    (hB:n*n+n+3< B) (hq:q< n*n) (ha:a≤1) (hb:b≤1) (he:e≤1):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "test.i"=q∧
      (σ.arrs membershipArray)[q/n]?=some a∧ (σ.arrs membershipArray)[q%n]?=some b∧
      (σ.arrs graphArray)[q]?=some e) (read graphArray membershipArray)
      (fun _ τ => τ.vars "test.bit"=a*b*e) 24:=by
  have hn:0< n:=by nlinarith only [hq]
  have hqn:q/n< n:=(Nat.div_lt_iff_lt_mul hn).mpr hq
  have hmod:q%n< n:=Nat.mod_lt _ hn
  have hqB:q< B:=by omega
  have hdivmul:q/n*n≤ q:=Nat.div_mul_le_self _ _
  have hab:a*b≤1:=by nlinarith only [Nat.mul_le_mul ha hb]
  have habe:a*b*e≤1:=by nlinarith only [Nat.mul_le_mul hab he]
  rintro σ ⟨hnσ,hqσ,haσ,hbσ,heσ⟩
  have hrooma:q/n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at haσ
    contradiction
  have hroomb:q%n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hbσ
    contradiction
  have hroome:q<(σ.arrs graphArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (c0 a b) e; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "test.bit") c1) σ; let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "test.i") (Env.vars σ "graph.n"); let c4:Env:=Env.setVar σ "test.row" c3; let c5:String→ Nat:=Env.vars c4; let c6:Nat:=c5 "test.i"; let c7:Nat:=c5 "test.row"; let c8:Nat:=c5 "graph.n"; let c9:Nat:=c0 c7 c8; let c10:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c6 c9; let c11:Env:=Env.setVar c4 "test.col" c10; let c12:String→ List Nat:=Env.arrs c11; let c13:List Nat:=c12 membershipArray; let c14:Nat→ Nat→ Nat:= @List.getD Nat c13; let c15:String→ Nat:=Env.vars c11; let c16:Nat:=c15 "test.row"; let c17:Nat:=c14 c16 ((0:Nat)); let c18:Nat:=c15 "test.col"; let c19:Nat:=c14 c18 ((0:Nat)); let c20:Nat:=c0 c17 c19; let c21:Nat:=c15 "test.i"; let c22:Nat:= @List.getD Nat (c12 graphArray) c21 ((0:Nat)); let c23:Nat:=c0 c20 c22; let c24:Env:=Env.setVar c11 "test.bit" c23; let c25:Nat→ Nat→ Nat:=Nat.add; let c26:Nat→ Nat:=c25 ((1:Nat)); let c27:Nat:=c26 (Expr.size (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))); let c28:Expr:=Expr.sub (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")); let c29:Nat:=c26 (Expr.size c28); let c30:Expr:=Expr.mul (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")); let c31:Expr:=Expr.mul c30 (Expr.get graphArray (Expr.var "test.i")); let c32:Nat:=c26 (Expr.size c31); let c33:Nat:=c25 c29 c32; let c34:Com:=Com.assign "test.col" c28; let c35:Com:=Com.assign "test.bit" c31; let c36:Nat→ Prop:=Nat.lt c16; let c37:Nat:= @List.length Nat c13; @Exists.intro Env (fun (σ':Env) => And (Run B (read graphArray membershipArray) σ σ' ((24:Nat))) (c2 σ')) c24 (@And.intro (Run B (read graphArray membershipArray) σ c24 ((24:Nat))) (c2 c24) (RunStep.mono B (read graphArray membershipArray) σ c24 (c25 c27 c33) ((24:Nat)) (RunStep.seq B (Com.assign "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))) (Com.seq c34 c35) σ c4 c24 c27 c33 (RunStep.assign B σ "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n")) c3 (RunStep.eval_div B σ (Expr.var "test.i") (Expr.var "graph.n") (Env.vars σ "test.i") (Env.vars σ "graph.n") (RunStep.eval_var B σ "test.i" (?nAX_g7975_0_0_0)) (RunStep.eval_var B σ "graph.n" (?nAX_g7975_0_0_1)) ?_)) (RunStep.seq B c34 c35 c4 c11 c24 c29 c32 (RunStep.assign B c4 "test.col" c28 c10 (RunStep.eval_sub B c4 (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")) c6 c9 (RunStep.eval_var B c4 "test.i" (?nAX_g7975_0_0_2)) (RunStep.eval_mul B c4 (Expr.var "test.row") (Expr.var "graph.n") c7 c8 (RunStep.eval_var B c4 "test.row" ?_) (RunStep.eval_var B c4 "graph.n" (?nAX_g7975_0_0_3)) ?_) (?nAX_g7975_0_0_4))) (RunStep.assign B c11 "test.bit" c31 c23 (RunStep.eval_mul B c11 c30 (Expr.get graphArray (Expr.var "test.i")) c20 c22 (RunStep.eval_mul B c11 (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")) c17 c19 (RunStep.eval_get B c11 membershipArray (Expr.var "test.row") c16 (RunStep.eval_var B c11 "test.row" ?_) ?_ ?_) (RunStep.eval_get B c11 membershipArray (Expr.var "test.col") c18 (RunStep.eval_var B c11 "test.col" (?nAX_g7975_0_0_5)) ?_ ?_) ?_) (RunStep.eval_get B c11 graphArray (Expr.var "test.i") c21 (RunStep.eval_var B c11 "test.i" (?nAX_g7975_0_0_6)) (?nAX_g7975_0_0_7) ?_) ?_)))) (?nAX_g7975_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7975_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def Representation {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) graphArray σ∧
    Prefix (encodeOutput I) membershipArray σ

theorem read_graph_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B)
    (q:ℕ) (hq:q<(values G I).length):
    Spec B (fun σ => Representation G I graphArray membershipArray σ∧ σ.vars "test.i"=q)
      (read graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧ τ.vars "test.bit"=(values G I)[q]) 24:=by
  have hq':q< n*n:=by rwa [values_length] at hq
  let u:=NativeBlowUp.row (⟨q,hq'⟩:Fin (n*n))
  let v:=NativeBlowUp.col (⟨q,hq'⟩:Fin (n*n))
  let a:=if u∈I then 1 else 0
  let b:=if v∈I then 1 else 0
  let e:=if G.Adj u v then 1 else 0
  have ha:a≤1:=by dsimp [a]; split_ifs <;> omega
  have hb:b≤1:=by dsimp [b]; split_ifs <;> omega
  have he:e≤1:=by dsimp [e]; split_ifs <;> omega
  rintro σ ⟨⟨hn,hgraph,hmem⟩,hqi⟩
  have hua:(σ.arrs membershipArray)[q/n]?=some a:=by
    have hh:=hmem u.val (by simp [encodeOutput])
    simpa [encodeOutput,a,u,NativeBlowUp.row] using hh
  have hvb:(σ.arrs membershipArray)[q%n]?=some b:=by
    have hh:=hmem v.val (by simp [encodeOutput])
    simpa [encodeOutput,b,v,NativeBlowUp.col] using hh
  have hge:(σ.arrs graphArray)[q]?=some e:=by
    have hh:=hgraph q (by rwa [NativeWeightReduction.adjacency_length])
    have hc:=NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) (⟨q,hq'⟩:Fin (n*n))
    change (NativeWeightReduction.adjacency G)[q]?=some e at hc
    rw [List.getElem?_eq_getElem (by rwa [NativeWeightReduction.adjacency_length])] at hc
    exact hh.trans hc
  obtain ⟨τ,rr,p⟩:=read_spec B n q a b e graphArray membershipArray hB hq' ha hb he σ
    ⟨hn,hqi,hua,hvb,hge⟩
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by simp [read,Com.wvars])).trans hn,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr graphArray (by simp [read,Com.warrs])] using hgraph
  · simpa only [Prefix,rr.frame_arr membershipArray (by simp [read,Com.warrs])] using hmem
  · simpa [values,pairValue,a,b,e,u,v] using p

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B):
    Spec B (Representation G I graphArray membershipArray) (command graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧
        τ.vars "test.ok"≤1∧ (τ.vars "test.ok"=1↔ G.IsIndepSet (I:Set (Fin n))))
      (38*n*n+12):=by
  have hwords:∀ z∈values G I,z< B:=by
    intro z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    exact (pair_value_le G I _ _).trans_lt (by omega)
  have hs:=NativeZeroScan.command_spec B (values G I) (Representation G I graphArray membershipArray)
    (read graphArray membershipArray) 24 (by rw [values_length]; omega) hwords
    (by simp [read,Com.wvars]) (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by
      rintro σ ⟨hn,hg,hm⟩
      exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hn,hg,hm⟩)
    (by
      rintro σ τ rr ⟨hn,hg,hm⟩
      refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩
      · simpa only [Prefix,rr.frame_arr graphArray (by simp [NativeZeroScan.update,Com.warrs])] using hg
      · simpa only [Prefix,rr.frame_arr membershipArray (by simp [NativeZeroScan.update,Com.warrs])] using hm)
    (read_graph_spec B G I graphArray membershipArray hB)
  intro σ hσ
  let ν:=σ.setVar "test.limit" (n*n)
  have hnB:n< B:=by omega
  have hnnB:n*n< B:=by omega
  have r1:Run B (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩) hnnB)
  have hν:Representation G I graphArray membershipArray ν:=
    ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hσ.1,hσ.2⟩
  obtain ⟨τ,r2,p2⟩:=hs ν ⟨hν,by simp [ν,values_length]⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [values_length]; nlinarith),p2.1,?_,?_⟩
  · rw [p2.2]
    exact NativeZeroScan.prefix_ok_le _ _
  · rw [p2.2,values_length,values_correct]

end Lax263307Proofs.NativeIndependentTest

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeExhaustive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307.ExhaustiveTargets

def Data {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧ σ.vars "target.k"=k∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
  Prefix (NativeCombinations.table n k) "choose.table" σ∧ n≤(σ.arrs "subset.bits").length

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"choose.n"∉c.wvars) (h2:"choose.cols"∉c.wvars)
    (h3:"target.k"∉c.wvars) (h4:"search.graph"∉c.warrs) (h5:"choose.table"∉c.warrs)
    (hσ:Data G k σ):Data G k τ:=by
  rcases hσ with ⟨hn,hcn,hcols,hk,hg,ht,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "choose.n" h1).trans hcn,
    (rr.frame_var "choose.cols" h2).trans hcols,(rr.frame_var "target.k" h3).trans hk,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" h4] using hg
  · simpa only [Prefix,rr.frame_arr "choose.table" h5] using ht
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def candidate (n k rank:ℕ):Finset (Fin n):=
  (NativeCombinations.decode (List.finRange n) (NativeCombinations.bits n k rank)).toFinset

theorem candidate_get (n k rank:ℕ) (hrank:rank< n.choose k):
    (candidates n k)[rank]?=some (candidate n k rank):=
  NativeCombinations.candidate_coordinate n k rank hrank

theorem candidate_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k rank:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+5< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => Data G k σ∧ σ.vars "target.i"=rank) candidateCommand
      (fun _ τ => Data G k τ∧ Prefix (encodeOutput (candidate n k rank)) "subset.bits" τ∧
        τ.vars "target.found"≤1∧ (τ.vars "target.found"=1↔ G.IsIndepSet (candidate n k rank:Set (Fin n))))
      (38*n*n+54*n+24):=by
  have hkB:k< B:=by omega
  have hsetup:Spec B (fun σ => σ.vars "target.k"=k∧ σ.vars "target.i"=rank) prepareCandidate
      (fun _ τ => τ.vars "subset.need"=k∧ τ.vars "subset.rank"=rank) 4:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "target.k") k) (@Eq Nat (Env.vars σ "target.i") rank)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "subset.need") k) (@Eq Nat (Env.vars τ "subset.rank") rank)) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B prepareCandidate σ σ' ((4:Nat))) (c0 σ'); let c2:Nat:=Env.vars (Env.setVar σ "subset.need" (Env.vars σ "target.k")) "target.i"; let c3:Env:=Env.setVar (Env.setVar σ "subset.need" (Env.vars σ "target.k")) "subset.rank" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "target.k")); let c7:Nat:=c5 (Expr.size (Expr.var "target.i")); let c8:String→ Nat:=Env.vars c3; @And.casesOn (@Eq Nat (Env.vars σ "target.k") k) (@Eq Nat (Env.vars σ "target.i") rank) (fun (x:And (@Eq Nat (Env.vars σ "target.k") k) (@Eq Nat (Env.vars σ "target.i") rank)) => @Exists Env c1) a fun (left:@Eq Nat (Env.vars σ "target.k") k) (right:@Eq Nat (Env.vars σ "target.i") rank) => @Exists.intro Env c1 c3 (@And.intro (Run B prepareCandidate σ c3 ((4:Nat))) (c0 c3) (RunStep.mono B prepareCandidate σ c3 (c4 c6 c7) ((4:Nat)) (RunStep.seq B (Com.assign "subset.need" (Expr.var "target.k")) (Com.assign "subset.rank" (Expr.var "target.i")) σ (Env.setVar σ "subset.need" (Env.vars σ "target.k")) c3 c6 c7 (RunStep.assign B σ "subset.need" (Expr.var "target.k") (Env.vars σ "target.k") (RunStep.eval_var B σ "target.k" (?nAX_g7986_0_0_0))) (RunStep.assign B (Env.setVar σ "subset.need" (Env.vars σ "target.k")) "subset.rank" (Expr.var "target.i") c2 (RunStep.eval_var B (Env.setVar σ "subset.need" (Env.vars σ "target.k")) "target.i" (?nAX_g7986_0_0_1)))) (?nAX_g7986_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7986_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7986_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7986_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hdata,hrankσ⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ ⟨hdata.2.2.2.1,hrankσ⟩
  have d1:=data_frame G k r1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdata
  obtain ⟨μ,r2,p2⟩:=NativeCombinations.subset_command_spec B n k rank (by omega) hrank hcoeff ν
    ⟨d1.2.1,d1.2.2.1,p1.1,p1.2,d1.2.2.2.2.2.1,d1.2.2.2.2.2.2⟩
  have d2:=data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d1
  have hbits:Prefix (encodeOutput (candidate n k rank)) "subset.bits" μ:=by
    rw [NativeCombinations.bits_encoding] at p2
    exact p2
  obtain ⟨ξ,r3,p3⟩:=NativeIndependentTest.command_spec B G (candidate n k rank) "search.graph" "subset.bits"
    (by omega) μ ⟨d2.1,d2.2.2.2.2.1,hbits⟩
  have d3:=data_frame G k r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d2
  let τ:=ξ.setVar "target.found" (ξ.vars "test.ok")
  have r4:Run B (.assign "target.found" (.var "test.ok")) ξ τ 2:=
    Run.assign (evalB_var (p3.2.1.trans_lt (by omega)))
  have d4:=data_frame G k r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3
  have rtotal:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by omega),d4,?_,?_,?_⟩
  · simpa only [Prefix,r4.frame_arr "subset.bits" (by decide)] using p3.1.2.2
  · simpa only [τ,vars_setVar,if_true] using p3.2.1
  · simpa only [τ,vars_setVar,if_true] using p3.2.2

def prefixFind {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k i:ℕ):Option (Finset (Fin n)):=
  ((candidates n k).take i).find? fun I => decide (G.IsIndepSet (I:Set (Fin n)))

theorem candidates_length (n k:ℕ):(candidates n k).length=n.choose k:=by
  simp [candidates,List.length_sublistsLen]

theorem prefix_find_zero {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ):
    prefixFind G k 0=none:=by simp [prefixFind]

theorem prefix_find_succ {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k i:ℕ) (hi:i< n.choose k):
    prefixFind G k (i+1)=match prefixFind G k i with
      | some I => some I
      | none => if G.IsIndepSet (candidate n k i:Set (Fin n)) then some (candidate n k i) else none:=by
  have hic:i<(candidates n k).length:=by rwa [candidates_length]
  have hc:=candidate_get n k i hi
  rw [List.getElem?_eq_getElem hic] at hc
  have he:=Option.some.inj hc
  unfold prefixFind
  rw [List.take_succ_eq_append_getElem hic,he,List.find?_append]
  cases h:((candidates n k).take i).find? (fun (I:Finset (Fin n)) => decide (G.IsIndepSet (I:Set (Fin n)))) <;> simp

def Result {n:ℕ} (answer:Option (Finset (Fin n))) (σ:Env):Prop:=
  match answer with
  | none => σ.vars "target.found"=0
  | some I => σ.vars "target.found"=1∧ Prefix (encodeOutput I) "subset.bits" σ

def Invariant {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ) (σ:Env):Prop:=
  Data G k σ∧ σ.vars "target.count"=n.choose k∧ σ.vars "target.i"≤ n.choose k∧
    Result (prefixFind G k (σ.vars "target.i")) σ

theorem step_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+5< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => Invariant G k σ∧ σ.vars "target.i"< n.choose k) step
      (fun σ τ => Invariant G k τ∧ τ.vars "target.i"=σ.vars "target.i"+1)
      (38*n*n+54*n+40):=by
  rintro σ ⟨⟨hdata,hcount,hle,hresult⟩,hlt⟩
  let i:=σ.vars "target.i"
  have hcountB:=hcoeff n le_rfl k le_rfl
  have hiB:i< B:=hlt.trans hcountB
  have hi1B:i+1< B:=by dsimp [i]; omega
  have h0:0< B:=by omega
  have h1:1< B:=by omega
  change Result (prefixFind G k i) σ at hresult
  cases hf:prefixFind G k i with
  | none =>
    have hfound:σ.vars "target.found"=0:=by simpa only [hf,Result] using hresult
    obtain ⟨ν,r1,p1⟩:=candidate_spec B G k i hB hiB hcoeff σ ⟨hdata,rfl⟩
    have hb:(Cond.eq (.var "target.found") (.lit 0)).evalB B σ=some true:=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hfound.symm,hfound ▸ h0⟩) (evalB_lit h0)
    have rb:Run B (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip) σ ν
        (4+(38*n*n+54*n+24)):=Run.ite_true hb r1
    have hiν:ν.vars "target.i"=i:=r1.frame_var "target.i" (by decide)
    let τ:=ν.setVar "target.i" (i+1)
    have r2:Run B (.assign "target.i" (.add (.var "target.i") (.lit 1))) ν τ 4:=
      Run.assign (evalB_bin (op:=.add)
        (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit h1) hi1B)
    have rr:=rb.seq r2
    have ht:τ.vars "target.i"=i+1:=by simp [τ]
    have hd:=data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p1.1
    refine ⟨τ,rr.mono (by omega),⟨hd,?_,by rw [ht]; omega,?_⟩,ht⟩
    · exact (rr.frame_var "target.count" (by decide)).trans hcount
    · rw [ht,prefix_find_succ G k i hlt,hf]
      dsimp only
      by_cases hgood:G.IsIndepSet (candidate n k i:Set (Fin n))
      · rw [if_pos hgood]
        refine ⟨?_,?_⟩
        · exact (r2.frame_var "target.found" (by decide)).trans (p1.2.2.2.mpr hgood)
        · simpa only [Prefix,r2.frame_arr "subset.bits" (by decide)] using p1.2.1
      · rw [if_neg hgood]
        have hnot:ν.vars "target.found"≠1:=mt p1.2.2.2.mp hgood
        have hz:ν.vars "target.found"=0:=by have hh:=p1.2.2.1; omega
        exact (r2.frame_var "target.found" (by decide)).trans hz
  | some I =>
    have hfound:σ.vars "target.found"=1∧ Prefix (encodeOutput I) "subset.bits" σ:=by
      simpa only [hf,Result] using hresult
    have hb:(Cond.eq (.var "target.found") (.lit 0)).evalB B σ=some false:=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hfound.1.symm,hfound.1 ▸ h1⟩) (evalB_lit h0)
    have rb:Run B (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip) σ σ 5:=
      Run.ite_false hb Run.skip
    let τ:=σ.setVar "target.i" (i+1)
    have r2:Run B (.assign "target.i" (.add (.var "target.i") (.lit 1))) σ τ 4:=
      Run.assign (evalB_bin (op:=.add) (evalB_var hiB) (evalB_lit h1) hi1B)
    have rr:=rb.seq r2
    have ht:τ.vars "target.i"=i+1:=by simp [τ]
    have hd:=data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdata
    refine ⟨τ,rr.mono (by omega),⟨hd,?_,by rw [ht]; omega,?_⟩,ht⟩
    · exact (r2.frame_var "target.count" (by decide)).trans hcount
    · rw [ht,prefix_find_succ G k i hlt,hf]
      refine ⟨(r2.frame_var "target.found" (by decide)).trans hfound.1,?_⟩
      simpa only [Prefix,r2.frame_arr "subset.bits" (by decide)] using hfound.2

theorem search_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+5< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => Data G k σ∧ σ.vars "target.count"=n.choose k) search
      (fun _ τ => Data G k τ∧ Result (findIndependentSet G k) τ)
      ((38*n*n+54*n+44)*(n.choose k)+8):=by
  have hloop:=Spec.forRangeZero "target.i" "target.count" (Invariant G k) (n.choose k)
    (38*n*n+54*n+40) (hcoeff n le_rfl k le_rfl)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B G k hB hcoeff)
  rintro σ ⟨hdata,hcount⟩
  let ν:=σ.setVar "target.found" 0
  have r1:Run B (.assign "target.found" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant G k (ν.setVar "target.i" 0):=by
    refine ⟨?_,?_,by simp,?_⟩
    · simpa only [Data,ν,vars_setVar,String.reduceEq,if_false,Prefix,arrs_setVar] using hdata
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcount
    · simp [ν,prefix_find_zero,Result]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  have he:prefixFind G k (n.choose k)=findIndependentSet G k:=by
    unfold prefixFind findIndependentSet
    rw [List.take_of_length_le (by rw [candidates_length])]
  simpa only [p2.2,he] using p2.1.2.2.2

def Input {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "target.k"=k∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
  (n+1)*(k+1)≤(σ.arrs "choose.table").length∧ n≤(σ.arrs "subset.bits").length

theorem prepare_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+5< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (Input G k) prepare (fun _ τ => Data G k τ∧ τ.vars "target.count"=n.choose k)
      (54*(n+1)*(k+1)+27):=by
  have hnB:n< B:=by omega
  have hkB:k< B:=by omega
  have hcolsB:k+1< B:=by omega
  have hsetup:Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "target.k"=k) setup
      (fun _ τ => τ.vars "choose.n"=n∧ τ.vars "choose.k"=k) 4:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "target.k") k)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.n") n) (@Eq Nat (Env.vars τ "choose.k") k)) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B setup σ σ' ((4:Nat))) (c0 σ'); let c2:Nat:=Env.vars (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "target.k"; let c3:Env:=Env.setVar (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "choose.k" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "graph.n")); let c7:Nat:=c5 (Expr.size (Expr.var "target.k")); let c8:String→ Nat:=Env.vars c3; @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "target.k") k) (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "target.k") k)) => @Exists Env c1) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "target.k") k) => @Exists.intro Env c1 c3 (@And.intro (Run B setup σ c3 ((4:Nat))) (c0 c3) (RunStep.mono B setup σ c3 (c4 c6 c7) ((4:Nat)) (RunStep.seq B (Com.assign "choose.n" (Expr.var "graph.n")) (Com.assign "choose.k" (Expr.var "target.k")) σ (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) c3 c6 c7 (RunStep.assign B σ "choose.n" (Expr.var "graph.n") (Env.vars σ "graph.n") (RunStep.eval_var B σ "graph.n" (?nAX_g8001_0_0_0))) (RunStep.assign B (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "choose.k" (Expr.var "target.k") c2 (RunStep.eval_var B (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "target.k" (?nAX_g8001_0_0_1)))) (?nAX_g8001_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8001_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8001_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8001_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hn,hk,hgraph,htableroom,hbitsroom⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ ⟨hn,hk⟩
  obtain ⟨μ,r2,p2⟩:=NativeCombinations.command_spec B n k (by omega) hcoeff ν
    ⟨p1.1,p1.2,by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  have r12:=r1.seq r2
  have d2:Data G k μ:=by
    refine ⟨(r12.frame_var "graph.n" (by decide)).trans hn,
      (r2.frame_var "choose.n" (by decide)).trans p1.1,p2.2,
      (r12.frame_var "target.k" (by decide)).trans hk,?_,p2.1,?_⟩
    · simpa only [Prefix,r12.frame_arr "search.graph" (by decide)] using hgraph
    · rwa [Lax455465Proofs.RamFrames.run_array_length r12]
  have hidx:n*(k+1)+k<(NativeCombinations.table n k).length:=by
    rw [NativeCombinations.table_length]
    nlinarith
  have hc:=NativeCombinations.table_coordinate n k n k le_rfl le_rfl
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget:=(p2.1 (n*(k+1)+k) hidx).trans hc
  have hidxB:n*(k+1)+k< B:=by rw [NativeCombinations.table_length] at hidx; omega
  have hmulB:n*(k+1)< B:=by omega
  have hindex:(Expr.add (.mul (.var "graph.n") (.var "choose.cols")) (.var "target.k")).evalB B μ=
      some (n*(k+1)+k):=evalB_bin (op:=.add)
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨d2.1.symm,d2.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨d2.2.2.1.symm,d2.2.2.1 ▸ hcolsB⟩) hmulB)
    (by rw [evalB_var_iff]; exact ⟨d2.2.2.2.1.symm,d2.2.2.2.1 ▸ hkB⟩) hidxB
  let τ:=μ.setVar "target.count" (n.choose k)
  have r3:Run B readCount μ τ 7:=Run.assign (evalB_get hindex hget (hcoeff n le_rfl k le_rfl))
  have d3:=data_frame G k r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d2
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),d3,?_⟩
  simp [τ]

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+5< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (Input G k) command (fun _ τ => Result (findIndependentSet G k) τ) (cost n k):=by
  intro σ hσ
  obtain ⟨ν,r1,p1⟩:=prepare_spec B G k hB hcoeff σ hσ
  obtain ⟨τ,r2,p2⟩:=search_spec B G k hB hcoeff ν p1
  exact ⟨τ,(r1.seq r2).mono (by dsimp [cost]; omega),p2.2⟩

open Lax109476Proofs

end Lax263307Proofs.NativeExhaustive

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"catalog.count"∉c.wvars)
    (h2:"catalog.mask"∉c.warrs) (h3:"search.graph"∉c.warrs) (hσ:Data G r σ):Data G r τ:=by
  rcases hσ with ⟨hn,hc,hm,hg,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.count" h1).trans hc,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hm
  · simpa only [Prefix,rr.frame_arr "search.graph" h3] using hg
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

end Lax263307Proofs.NativeCatalogMetadata

end

section

namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Context (b e:ℕ) (σ:Env):Prop:=σ.vars "power.base"=b∧ σ.vars "power.exponent"=e

def Invariant (b e:ℕ) (σ:Env):Prop:=
  Context b e σ∧ σ.vars "power.i"≤ e∧ σ.vars "power.value"=b^(σ.vars "power.i")

theorem step_spec (B b e i:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B) (hi:i< e):
    Spec B (fun σ => Context b e σ∧ σ.vars "power.i"=i∧ σ.vars "power.value"=b^i) step
      (fun _ τ => Context b e τ∧ τ.vars "power.i"=i+1∧ τ.vars "power.value"=b^(i+1)) 8:=by
  have hp:b^i< B:=(Nat.pow_le_pow_right hb hi.le).trans_lt (by omega)
  have hnext:b^i*b< B:=by
    rw [←pow_succ]
    exact (Nat.pow_le_pow_right hb hi).trans_lt (by omega)
  (expose_names;
    (refine fun (σ:Env) (a:And (Context b e σ) (And (@Eq Nat (Env.vars σ "power.i") i) (@Eq Nat (Env.vars σ "power.value") (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b i)))) => let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b; let c1:Prop:= @Eq Nat (Env.vars σ "power.value") (c0 i); let c2:Prop:=And (@Eq Nat (Env.vars σ "power.i") i) c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=c3 i ((1:Nat)); let c5:Nat:=c0 c4; let c6:Env→ Prop:=(fun (x τ:Env) => And (Context b e τ) (And (@Eq Nat (Env.vars τ "power.i") c4) (@Eq Nat (Env.vars τ "power.value") c5))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B step σ σ' ((8:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c10:Env:=Env.setVar σ "power.value" c9; let c11:Nat:=Env.vars c10 "power.i"; let c12:Nat:=c3 c11 ((1:Nat)); let c13:Env:=Env.setVar c10 "power.i" c12; let c14:Nat→ Nat:=c3 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c16:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c13; @And.casesOn (Context b e σ) c2 (fun (x:And (Context b e σ) c2) => c8) a fun (left:Context b e σ) (right:c2) => @And.casesOn (@Eq Nat (Env.vars σ "power.i") i) c1 (fun (x:c2) => c8) right fun (left_1:@Eq Nat (Env.vars σ "power.i") i) (right_1:c1) => @Exists.intro Env c7 c13 (@And.intro (Run B step σ c13 ((8:Nat))) (c6 c13) (RunStep.mono B step σ c13 (c3 c15 c17) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c16) σ c10 c13 c15 c17 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c9 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g8253_0_0_0)) (RunStep.eval_var B σ "power.base" ?_) ?_)) (RunStep.assign B c10 "power.i" c16 c12 (RunStep.eval_add B c10 (Expr.var "power.i") (Expr.lit ((1:Nat))) c11 ((1:Nat)) (RunStep.eval_var B c10 "power.i" (?nAX_g8253_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g8253_0_0_2)) (?nAX_g8253_0_0_3)))) (?nAX_g8253_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8253_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,pow_succ]
  all_goals omega

theorem command_spec (B b e:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B):
    Spec B (Context b e) command
      (fun _ τ => Context b e τ∧ τ.vars "power.value"=b^e) (12*e+8):=by
  have hbody:Spec B (fun σ => Invariant b e σ∧ σ.vars "power.i"< e) step
      (fun σ τ => Invariant b e τ∧ τ.vars "power.i"=σ.vars "power.i"+1) 8:=by
    rintro σ ⟨⟨hc,hle,hv⟩,hlt⟩
    obtain ⟨τ,rr,ht⟩:=step_spec B b e (σ.vars "power.i") hb hB hlt σ ⟨hc,rfl,hv⟩
    exact ⟨τ,rr,⟨ht.1,by rw [ht.2.1]; omega,by simpa only [ht.2.1] using ht.2.2⟩,ht.2.1⟩
  have hloop:=Spec.forRangeZero "power.i" "power.exponent" (Invariant b e) e 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν:=σ.setVar "power.value" 1
  have r1:Run B (.assign "power.value" (.lit 1)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant b e (ν.setVar "power.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,ν,vars_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,by simpa only [p2.2] using p2.1.2.2⟩

end Lax263307Proofs.NativeNaturalPower

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.ParameterResources

open Lax263307.AlgorithmParameters Lax263307.ParameterResources

theorem cutoff_eq_level (a K B n D:ℕ):cutoff a K B n D=level a K B n D:=by
  have h:targetThreshold a K B n D≤ level a K B n D:=by
    unfold level sparsity
    have hfactor:1≤ Nat.log2 n + 1:=by omega
    nlinarith
  exact max_eq_right h

end Lax263307Proofs.ParameterResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.AlgorithmParameters

def Context (n D:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.D"=D∧ σ.vars "node.log"=Nat.log2 n+1∧
    σ.vars "node.logarithm"=logarithm n

def Data (a K b n D:ℕ) (σ:Env):Prop:=Context n D σ∧
  σ.vars "node.load"=load b n D∧ σ.vars "node.threshold"=targetThreshold a K b n D∧
  σ.vars "node.sparsity"=sparsity a K b n D∧ σ.vars "moment.r"=level a K b n D∧
  σ.vars "node.cutoff"=cutoff a K b n D∧ σ.vars "node.floorDen"=floorDenominator a K b n D

theorem context_frame {B n D t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hs:Context n D σ) (hn:"graph.n"∉c.wvars) (hD:"node.D"∉c.wvars)
    (hl:"node.log"∉c.wvars) (hL:"node.logarithm"∉c.wvars):Context n D τ:=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,
    (rr.frame_var _ hl).trans hs.2.2.1,(rr.frame_var _ hL).trans hs.2.2.2⟩

theorem floor_eq (a K b n D:ℕ):floorDenominator a K b n D=2*n*level a K b n D:=by
  unfold floorDenominator level
  ring

theorem setup_spec (B a K b n D:ℕ) (hB:guard a K b n D< B):
    Spec B (Context n D) (setup a b)
      (fun _ τ => Context n D τ∧ τ.vars "node.load"=load b n D∧
        NativeNaturalPower.Context (load b n D+1) (4*a+2) τ) 12:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c0 (c1 ((4:Nat)) a) ((2:Nat)); let c3:Env→ Prop:=NativeNaturalPower.Context (c0 (load b n D) ((1:Nat))) c2; let c4:Env→ Prop:=(fun (x τ:Env) => And (Context n D τ) (And (@Eq Nat (Env.vars τ "node.load") (load b n D)) (c3 τ))) σ; let c5:Nat:=c1 ((12:Nat)) b; let c6:Nat:=c1 c5 (Env.vars σ "node.D"); let c7:Nat:=c1 c6 (Env.vars σ "node.logarithm"); let c8:Env:=Env.setVar σ "node.load" c7; let c9:Nat:=Env.vars c8 "node.load"; let c10:Nat:=c0 c9 ((1:Nat)); let c11:Env:=Env.setVar c8 "power.base" c10; let c12:Env:=Env.setVar c11 "power.exponent" c2; let c13:Nat→ Nat:=c0 ((1:Nat)); let c14:Expr:=Expr.lit c5; let c15:Expr:=Expr.mul c14 (Expr.var "node.D"); let c16:Expr:=Expr.mul c15 (Expr.var "node.logarithm"); let c17:Nat:=c13 (Expr.size c16); let c18:Expr:=Expr.add (Expr.var "node.load") (Expr.lit ((1:Nat))); let c19:Nat:=c13 (Expr.size c18); let c20:Expr:=Expr.lit c2; let c21:Nat:=c13 (Expr.size c20); let c22:Nat:=c0 c19 c21; let c23:Com:=Com.assign "power.base" c18; let c24:Com:=Com.assign "power.exponent" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (setup a b) σ σ' ((12:Nat))) (c4 σ')) c12 (@And.intro (Run B (setup a b) σ c12 ((12:Nat))) (c4 c12) (RunStep.mono B (setup a b) σ c12 (c0 c17 c22) ((12:Nat)) (RunStep.seq B (Com.assign "node.load" c16) (Com.seq c23 c24) σ c8 c12 c17 c22 (RunStep.assign B σ "node.load" c16 c7 (RunStep.eval_mul B σ c15 (Expr.var "node.logarithm") c6 (Env.vars σ "node.logarithm") (RunStep.eval_mul B σ c14 (Expr.var "node.D") c5 (Env.vars σ "node.D") (RunStep.eval_lit B c5 σ ?_) (RunStep.eval_var B σ "node.D" ?_) ?_) (RunStep.eval_var B σ "node.logarithm" ?_) ?_)) (RunStep.seq B c23 c24 c8 c11 c12 c19 c21 (RunStep.assign B c8 "power.base" c18 c10 (RunStep.eval_add B c8 (Expr.var "node.load") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c8 "node.load" ?_) (RunStep.eval_lit B ((1:Nat)) c8 ?_) ?_)) (RunStep.assign B c11 "power.exponent" c20 c2 (RunStep.eval_lit B c2 c11 ?_)))) (?nAX_g8271_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8271_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,NativeNaturalPower.Context,Env.setVar,guard,load]
  all_goals omega

theorem finish_spec (B a K b n D:ℕ) (hB:guard a K b n D< B):
    Spec B (fun σ => Context n D σ∧ σ.vars "node.load"=load b n D∧
      σ.vars "power.value"=(load b n D+1)^(4*a+2)) (finish K)
      (fun _ τ => Data a K b n D τ) 22:=by
  have hg:=hB
  dsimp only [guard] at hg
  have hth:K*(load b n D+1)^(4*a+2)=targetThreshold a K b n D:=rfl
  have hsp:2*targetThreshold a K b n D=sparsity a K b n D:=rfl
  have hl:sparsity a K b n D*(Nat.log2 n+1)=level a K b n D:=rfl
  have hf:=floor_eq a K b n D
  rintro σ ⟨hc,hload,hpower⟩
  let ν:=σ.setVar "node.threshold" (targetThreshold a K b n D)
  have r1:Run B (.assign "node.threshold" (.mul (.lit K) (.var "power.value"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show K< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hpower.symm,hpower ▸ (by omega)⟩)
      (by change K*(load b n D+1)^(4*a+2)< B; rw [hth]; omega))
  have hν:ν.vars "node.threshold"=targetThreshold a K b n D:=by rfl
  let μ:=ν.setVar "node.sparsity" (sparsity a K b n D)
  have r2:Run B (.assign "node.sparsity" (.mul (.lit 2) (.var "node.threshold"))) ν μ 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hν.symm,hν ▸ (by omega)⟩)
      (by change 2*targetThreshold a K b n D< B; rw [hsp]; omega))
  have hμ:μ.vars "node.sparsity"=sparsity a K b n D:=by rfl
  have hlog:=((r1.seq r2).frame_var "node.log" (by simp [Com.wvars])).trans hc.2.2.1
  let ρ:=μ.setVar "node.level" (level a K b n D)
  have r3:Run B (.assign "node.level" (.mul (.var "node.sparsity") (.var "node.log"))) μ ρ 4:=Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlog.symm,hlog ▸ (by omega)⟩)
      (by change sparsity a K b n D*(Nat.log2 n+1)< B; rw [hl]; omega))
  have hρ:ρ.vars "node.level"=level a K b n D:=by rfl
  let υ:=ρ.setVar "node.cutoff" (level a K b n D)
  have r4:Run B (.assign "node.cutoff" (.var "node.level")) ρ υ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hρ.symm,hρ ▸ (by omega)⟩)
  have hυ:=(r4.frame_var "node.level" (by simp [Com.wvars])).trans hρ
  let τ:=υ.setVar "moment.r" (level a K b n D)
  have r5:Run B (.assign "moment.r" (.var "node.level")) υ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hυ.symm,hυ ▸ (by omega)⟩)
  have hτ:=(r5.frame_var "node.level" (by simp [Com.wvars])).trans hυ
  have horder:=((r1.seq (r2.seq (r3.seq (r4.seq r5)))).frame_var "graph.n" (by simp [Com.wvars])).trans hc.1
  let κ:=τ.setVar "node.floorDen" (floorDenominator a K b n D)
  have r6:Run B (.assign "node.floorDen" (.mul (.mul (.lit 2) (.var "graph.n")) (.var "node.level"))) τ κ 6:=by
    apply Run.assign
    rw [hf]
    apply evalB_bin (op:=.mul)
    · exact evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
        (by rw [evalB_var_iff]; exact ⟨horder.symm,horder ▸ (by omega)⟩) (by change 2*n< B; omega)
    · rw [evalB_var_iff]; exact ⟨hτ.symm,hτ ▸ (by omega)⟩
    · change 2*n*level a K b n D< B
      rw [←hf]
      omega
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  refine ⟨κ,rr,⟨context_frame rr hc (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]),
    (rr.frame_var "node.load" (by simp [Com.wvars])).trans hload,
    ((r2.seq (r3.seq (r4.seq (r5.seq r6)))).frame_var "node.threshold" (by simp [Com.wvars])).trans hν,
    ((r3.seq (r4.seq (r5.seq r6))).frame_var "node.sparsity" (by simp [Com.wvars])).trans hμ,
    (r6.frame_var "moment.r" (by simp [Com.wvars])).trans (by rfl),?_,by rfl⟩⟩
  rw [Lax263307Proofs.ParameterResources.cutoff_eq_level]
  exact ((r5.seq r6).frame_var "node.cutoff" (by simp [Com.wvars])).trans (by rfl)

theorem command_spec (B a K b n D:ℕ) (hn:0< n) (hB:guard a K b n D< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "node.D"=D) (command a K b)
      (fun _ τ => Data a K b n D τ) (12*n.size+12*(2*n).size+12*(4*a+2)+64):=by
  rintro σ ⟨hnσ,hDσ⟩
  obtain ⟨ν,r1,p1⟩:=NativeLogarithms.command_spec B n hn (by dsimp [guard] at hB; omega) σ hnσ
  have hd1:Context n D ν:= ⟨p1.1,(r1.frame_var "node.D" (by decide)).trans hDσ,p1.2⟩
  obtain ⟨μ,r2,p2⟩:=setup_spec B a K b n D hB ν hd1
  obtain ⟨ρ,r3,p3⟩:=NativeNaturalPower.command_spec B (load b n D+1) (4*a+2) (by omega)
    (by dsimp [guard] at hB; omega) μ p2.2.2
  have hd3:=context_frame r3 p2.1 (by decide) (by decide) (by decide) (by decide)
  have hl3:=(r3.frame_var "node.load" (by decide)).trans p2.2.1
  obtain ⟨τ,r4,p4⟩:=finish_spec B a K b n D hB ρ ⟨hd3,hl3,p3.2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),p4⟩

end Lax263307Proofs.NativeNodeParameters

end

section

namespace Lax263307Proofs.NativeAttemptReply

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

theorem none_spec (B n ret:ℕ) (hB:n+ret+5< B):
    Spec B (fun σ => σ.vars "graph.n"=n) (noneCommand ret)
      (fun _ τ => τ.vars "graph.n"=n∧ NativeTargetDriver.Reply (none:Option (Finset (Fin n))) τ∧
        τ.vars "machine.phase"=ret) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "graph.n") n) (And (@NativeTargetDriver.Reply n (@none (Finset (Fin n))) τ) (@Eq Nat (Env.vars τ "machine.phase") ret))) σ; let c1:Env:=Env.setVar σ "recursion.return.tag" ((0:Nat)); let c2:Env:=Env.setVar c1 "recursion.return.mask" ((0:Nat)); let c3:Env:=Env.setVar c2 "machine.phase" ret; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ret)); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "recursion.return.mask" (Expr.lit ((0:Nat))); let c11:String→ Nat:=Env.vars c3; @Exists.intro Env (fun (σ':Env) => And (Run B (noneCommand ret) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (noneCommand ret) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (noneCommand ret) σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "recursion.return.tag" (Expr.lit ((0:Nat)))) (Com.seq c10 (Com.assign "machine.phase" (Expr.lit ret))) σ c1 c3 c6 c9 (RunStep.assign B σ "recursion.return.tag" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8286_0_0_0))) (RunStep.seq B c10 (Com.assign "machine.phase" (Expr.lit ret)) c1 c2 c3 c6 c8 (RunStep.assign B c1 "recursion.return.mask" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g8286_0_0_1))) (RunStep.assign B c2 "machine.phase" (Expr.lit ret) ret (RunStep.eval_lit B ret c2 (?nAX_g8286_0_0_2))))) (?nAX_g8286_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8286_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

theorem some_spec (B n ret:ℕ) (I:Finset (Fin n)) (hB:n+ret+5< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Lax455465Proofs.RamVirtualState.Prefix
      (IndependentSetEncoding.encodeOutput I) "subset.bits" σ) (someCommand ret)
      (fun _ τ => τ.vars "graph.n"=n∧ NativeTargetDriver.Reply (some I) τ∧
        τ.vars "machine.phase"=ret) (15*n+14):=by
  rintro σ ⟨hn,hbits⟩
  obtain ⟨ν,r1,p1⟩:=NativeMasks.command_spec B I (by omega) hm σ ⟨hn,hbits⟩
  let μ:=ν.setVar "recursion.return.tag" 1
  have r2:Run B (.assign "recursion.return.tag" (.lit 1)) ν μ 2:=Run.assign (evalB_lit (show 1< B by omega))
  have hmμ:=(r2.frame_var "mask.value" (by decide)).trans p1
  let ρ:=μ.setVar "recursion.return.mask" (mask I)
  have r3:Run B (.assign "recursion.return.mask" (.var "mask.value")) μ ρ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hmμ.symm,hmμ ▸ (mask_bound I).trans hm⟩)
  let τ:=ρ.setVar "machine.phase" ret
  have r4:Run B (.assign "machine.phase" (.lit ret)) ρ τ 2:=Run.assign (evalB_lit (show ret< B by omega))
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),(rr.frame_var "graph.n" (by simp [Com.wvars,NativeMasks.command,NativeMasks.step])).trans hn,
    ⟨((r3.seq r4).frame_var "recursion.return.tag" (by simp [Com.wvars])).trans (by rfl),
      (r4.frame_var "recursion.return.mask" (by simp [Com.wvars])).trans (by rfl)⟩,by rfl⟩

theorem command_spec (B n ret:ℕ) (answer:Option (Finset (Fin n)))
    (hB:n+ret+5< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ NativeExhaustive.Result answer σ) (command ret)
      (fun _ τ => τ.vars "graph.n"=n∧ NativeTargetDriver.Reply answer τ∧ τ.vars "machine.phase"=ret)
      (15*n+18):=by
  rintro σ ⟨hn,hr⟩
  cases answer with
  | none =>
    have hc:(Cond.eq (.var "target.found") (.lit 1)).evalB B σ=some false:=by
      have hh:=evalB_condEq (by rw [evalB_var_iff]; exact ⟨hr.symm,hr ▸ (by omega:0< B)⟩)
        (evalB_lit (show 1< B by omega))
      simpa using hh
    obtain ⟨τ,rr,p⟩:=none_spec B n ret hB σ hn
    exact ⟨τ,(Run.ite_false (c:=someCommand ret) hc rr).mono (by simp [Cond.size,Expr.size] <;> omega),p⟩
  | some I =>
    have hc:(Cond.eq (.var "target.found") (.lit 1)).evalB B σ=some true:=by
      have hh:=evalB_condEq (by rw [evalB_var_iff]; exact ⟨hr.1.symm,hr.1 ▸ (by omega:1< B)⟩)
        (evalB_lit (show 1< B by omega))
      simpa using hh
    obtain ⟨τ,rr,p⟩:=some_spec B n ret I hB hm σ ⟨hn,hr.2⟩
    exact ⟨τ,(Run.ite_true (d:=noneCommand ret) hc rr).mono (by simp [Cond.size,Expr.size] <;> omega),p⟩

end Lax263307Proofs.NativeAttemptReply

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 AlgorithmParameters

inductive Route | exhaustive | reject | search
  deriving DecidableEq

def route (n k threshold fuel:ℕ):Route:=
  if k≤ threshold∨ n≤1 then .exhaustive else if n< k∨ fuel=0 then .reject else .search

def Output (small large ret:ℕ):Route→ Env→ Prop
  | .exhaustive,σ => σ.vars "machine.phase"=small
  | .reject,σ => σ.vars "machine.phase"=ret∧ σ.vars "recursion.return.tag"=0
  | .search,σ => σ.vars "machine.phase"=large

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem select_spec (B n k threshold fuel small large ret:ℕ) (hn:1< n)
    (hB:n+k+threshold+fuel+small+large+ret+10< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "node.k"=k∧ σ.vars "node.cutoff"=threshold∧
      σ.vars "recursion.fuel"=fuel) (select small large ret)
      (fun _ τ => Output small large ret (route n k threshold fuel) τ) 20:=by
  rintro σ ⟨hnσ,hk,ht,hf⟩
  have hsmall:(Cond.lt (.var "node.k") (.add (.var "node.cutoff") (.lit 1))).evalB B σ=
      some (decide (k≤ threshold)):=by
    have hh:=evalB_condLt (value hk (by omega))
      (evalB_bin (op:=.add) (value ht (by omega)) (evalB_lit (show 1< B by omega))
        (by change threshold+1< B; omega))
    simpa only [Bop.apply_add,Nat.lt_succ_iff] using hh
  have hlarge:(Cond.lt (.var "graph.n") (.var "node.k")).evalB B σ=some (decide (n< k)):=
    evalB_condLt (value hnσ (by omega)) (value hk (by omega))
  have hzero:(Cond.eq (.var "recursion.fuel") (.lit 0)).evalB B σ=some (decide (fuel=0)):=by
    simpa only [Bool.beq_eq_decide_eq] using evalB_condEq (value hf (by omega)) (evalB_lit (show 0< B by omega))
  by_cases hs:k≤ threshold
  · let τ:=σ.setVar "machine.phase" small
    have rr:Run B (.assign "machine.phase" (.lit small)) σ τ 2:=Run.assign (evalB_lit (show small< B by omega))
    refine ⟨τ,(Run.ite_true (d:=.ite (.lt (.var "graph.n") (.var "node.k")) (NativeAttemptReply.noneCommand ret)
      (.ite (.eq (.var "recursion.fuel") (.lit 0)) (NativeAttemptReply.noneCommand ret)
        (.assign "machine.phase" (.lit large)))) (by simpa only [hs,decide_true] using hsmall) rr).mono
      (by simp [Cond.size,Expr.size]),?_⟩
    simp [Output,route,hs,τ]
  · have hnot:¬(k≤ threshold∨ n≤1):=by omega
    by_cases hk':n< k
    · obtain ⟨τ,rr,p⟩:=NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
      have r2:=Run.ite_true (d:=.ite (.eq (.var "recursion.fuel") (.lit 0))
        (NativeAttemptReply.noneCommand ret) (.assign "machine.phase" (.lit large)))
        (by simpa only [hk',decide_true] using hlarge) rr
      refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
        (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
      simpa only [route,if_neg hnot,hk',true_or,if_true,Output] using (show τ.vars "machine.phase"=ret∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
    · by_cases hz:fuel=0
      · obtain ⟨τ,rr,p⟩:=NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
        have r3:=Run.ite_true (d:=.assign "machine.phase" (.lit large))
          (by simpa only [hz,decide_true] using hzero) rr
        have r2:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret)
          (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simpa only [route,if_neg hnot,hz,or_true,if_true,Output] using (show τ.vars "machine.phase"=ret∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
      · let τ:=σ.setVar "machine.phase" large
        have rr:Run B (.assign "machine.phase" (.lit large)) σ τ 2:=Run.assign (evalB_lit (show large< B by omega))
        have r3:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hz,decide_false] using hzero) rr
        have r2:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simp [route,hnot,hk',hz,Output,τ]

def Input (n D k fuel:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.D"=D∧ σ.vars "node.k"=k∧ σ.vars "recursion.fuel"=fuel

theorem command_spec (B a K b n D k fuel small large ret:ℕ)
    (hB:NativeNodeParameters.guard a K b n D+n+k+cutoff a K b n D+fuel+small+large+ret+10< B):
    Spec B (Input n D k fuel) (command a K b small large ret)
      (fun _ τ => Input n D k fuel τ∧ Output small large ret (route n k (cutoff a K b n D) fuel) τ∧
        (route n k (cutoff a K b n D) fuel=.search→ NativeNodeParameters.Data a K b n D τ))
      (12*n.size+12*(2*n).size+12*(4*a+2)+88):=by
  rintro σ ⟨hn,hD,hk,hf⟩
  have htest:=evalB_condLt (value hn (show n< B by omega)) (evalB_lit (show 2< B by omega))
  by_cases hs:n<2
  · let τ:=σ.setVar "machine.phase" small
    have rr:Run B (.assign "machine.phase" (.lit small)) σ τ 2:=Run.assign (evalB_lit (show small< B by omega))
    refine ⟨τ,(Run.ite_true (d:=.seq (NativeNodeParameters.command a K b) (select small large ret))
      (by simpa only [hs,decide_true] using htest) rr).mono (by simp [Cond.size,Expr.size] <;> omega),?_,?_,?_⟩
    · simpa [Input,τ] using (show Input n D k fuel σ from ⟨hn,hD,hk,hf⟩)
    · have hsmall:n≤1:=by omega
      simp [route,hsmall,Output,τ]
    · have hsmall:n≤1:=by omega
      simp [route,hsmall]
  · obtain ⟨ν,r1,p1⟩:=NativeNodeParameters.command_spec B a K b n D (by omega) (by omega) σ ⟨hn,hD⟩
    have hk1:ν.vars "node.k"=k:=(r1.frame_var _ (by
      change "node.k"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hk
    have hf1:ν.vars "recursion.fuel"=fuel:=(r1.frame_var _ (by
      change "recursion.fuel"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hf
    obtain ⟨τ,r2,p2⟩:=select_spec B n k (cutoff a K b n D) fuel small large ret (by omega) (by omega) ν
      ⟨p1.1.1,hk1,p1.2.2.2.2.2.1,hf1⟩
    have hn2:=(r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.1
    have hD2:=(r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.2.1
    have hk2:=(r2.frame_var "node.k" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hk1
    have hf2:=(r2.frame_var "recursion.fuel" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hf1
    refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
      (by simpa only [hs,decide_false] using htest) (r1.seq r2)).mono (by simp [Cond.size,Expr.size] <;> omega),
      ⟨hn2,hD2,hk2,hf2⟩,p2,?_⟩
    intro _
    simpa only [NativeNodeParameters.Data,NativeNodeParameters.Context,
      r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.log" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.logarithm" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.load" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.threshold" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.sparsity" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "moment.r" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.cutoff" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.floorDen" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])] using p1

end Lax263307Proofs.NativeNodeDispatch

end

section

namespace Lax263307Proofs.NativeSmallAttempt

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307

def Input {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.k"=k∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
  (n+1)*(k+1)≤(σ.arrs "choose.table").length∧ n≤(σ.arrs "subset.bits").length

theorem command_spec {n:ℕ} (B ret:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k:ℕ) (hB:n*n+(n+1)*(k+1)+n+k+ret+10< B) (hm:2^n< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (Input G k) (command ret)
      (fun _ τ => τ.vars "graph.n"=n∧
        NativeTargetDriver.Reply (ExhaustiveTargets.findIndependentSet G k) τ∧ τ.vars "machine.phase"=ret)
      (NativeExhaustive.cost n k+15*n+20):=by
  rintro σ ⟨hn,hk,hgraph,htable,hbits⟩
  let ν:=σ.setVar "target.k" k
  have r0:Run B (.assign "target.k" (.var "node.k")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hk.symm,hk ▸ (by omega)⟩)
  obtain ⟨μ,r1,p1⟩:=NativeExhaustive.command_spec B G k (by omega) hcoeff ν
    ⟨(r0.frame_var "graph.n" (by decide)).trans hn,by rfl,
      by simpa only [Prefix,r0.frame_arr "search.graph" (by decide)] using hgraph,
      by rw [RamFrames.run_array_length r0]; exact htable,
      by rw [RamFrames.run_array_length r0]; exact hbits⟩
  have hnμ:=((r0.seq r1).frame_var "graph.n" (by decide)).trans hn
  obtain ⟨τ,r2,p2⟩:=NativeAttemptReply.command_spec B n ret (ExhaustiveTargets.findIndependentSet G k)
    (by omega) hm μ ⟨hnμ,p1⟩
  exact ⟨τ,(r0.seq (r1.seq r2)).mono (by omega),p2⟩

end Lax263307Proofs.NativeSmallAttempt

end

section

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target index cursor count:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars count=xs.length
  counter:σ.vars index≤ xs.length
  position:σ.vars cursor=front.length+σ.vars index
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars index)) target σ

end Lax263307Proofs.NativeAppendBuffer

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

end Lax263307Proofs.NativeShoreMasks

end

section

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command:Com:=.ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))

end Lax263307Proofs.NativeChildReturn

end

section

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars "stack.copy.length"=xs.length
  index:σ.vars "stack.i"≤ xs.length
  position:σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars "stack.i")) target σ

end Lax263307Proofs.NativeBlockAppend

end

section

namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem set_var {B:ℕ} {σ:Env} (hd:Bounded B σ) (s:String) (v:ℕ) (hv:v< B):
    Bounded B (σ.setVar s v):=by
  refine ⟨?_,hd.2.1,hd.2.2⟩
  intro t
  simp only [vars_setVar]
  split_ifs <;> first | exact hv | exact hd.1 t

theorem set_arr {B:ℕ} {σ:Env} (hd:Bounded B σ) (a:String) (i v:ℕ) (hv:v< B):
    Bounded B (σ.setArr a i v):=by
  refine ⟨hd.1,?_,hd.2.2⟩
  intro b z hz
  simp only [arrs_setArr] at hz
  split_ifs at hz
  · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hd.2.1 a z hz
    · exact hv
  · exact hd.2.1 b z hz

theorem big_step {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:BigStepB B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hd
  | assign he => exact set_var hd _ _ (Expr.lt_of_evalB he)
  | store hi he hk => exact set_arr hd _ _ _ (Expr.lt_of_evalB he)
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh =>
    rename_i σ0 s v rest
    have hv:=hd.2.2 _ (by rw [hh]; exact List.mem_cons_self)
    have hs:=set_var hd s v hv
    refine ⟨hs.1,hs.2.1,?_⟩
    intro z hz
    exact hd.2.2 z (by rw [hh]; exact List.mem_cons_of_mem _ hz)
  | write he => exact ⟨hd.1,hd.2.1,hd.2.2⟩

theorem run {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:Run B c σ τ K)
    (hd:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,rr⟩:=rr
  exact big_step rr hd

end Lax263307Proofs.NativeStateBounds

end

section

namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem words_length (names:List String) (S:ℕ) (σ:Env)
    (hS:∀ a∈names,(σ.arrs a).length=S):(words names σ).length=S*names.length:=by
  induction names with
  | nil => simp [words]
  | cons a as ih =>
    have hi:=ih (fun b hb => hS b (List.mem_cons_of_mem a hb))
    change (List.flatMap σ.arrs as).length=S*as.length at hi
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons]
    rw [hS a (by simp),hi]
    nlinarith only []

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (names:List String) (s:String) (hs:s≠"stack.words"):s∉(save names).wvars:=by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

end Lax263307Proofs.NativeFrameScalars

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem buffers_variable (names:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):s∉(NativeFrameBuffers.save names).wvars:=by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

end Lax263307Proofs.NativeRecursionFrame

end

section

namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (arrays scalars:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉(NativeRecursionFrame.save arrays scalars).wvars:=by
  have hw:s≠"stack.words" :=fun h => hs (by simp [h])
  simpa only [NativeRecursionFrame.save,Com.wvars,List.mem_append,not_or] using
    And.intro (NativeRecursionFrame.buffers_variable arrays s hs) (NativeFrameScalars.save_variable scalars s hw)

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

theorem append {B s t s' t':ℕ} {cases:List Com} {σ μ τ:Env}
    (a:Segment B cases s t σ μ) (b:Segment B cases s' t' μ τ):
    Segment B cases (s+s') (t+t') σ τ:=by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Segment.step h j hj rr (ih b)

theorem phase {B K:ℕ} {cases:List Com} {σ τ:Env}
    (running:σ.vars "machine.running"=1) (j:Fin cases.length)
    (phase:σ.vars "machine.phase"=j.val) (rr:Run B cases[j.val] σ τ K):
    Segment B cases 1 K σ τ:=by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

end Lax263307Proofs.NativeMachineSegment

end

section

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

theorem array_length {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (a:String):(τ.arrs a).length=(σ.arrs a).length:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (Lax455465Proofs.RamFrames.run_array_length rr a)

theorem single_run {B total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases 1 total σ τ) (j:Fin cases.length)
    (hp:σ.vars "machine.phase"=j.val):Run B cases[j.val] σ τ total:=by
  cases trace with
  | step hr i hi rr rest =>
    cases rest with
    | nil =>
      have he:i=j:=Fin.ext (hi.symm.trans hp)
      subst i
      simpa only [Nat.add_zero] using rr

end Lax263307Proofs.NativeMachineFrame

end

section

namespace Lax263307Proofs.NativeMachineBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning NativeMachineSegment

theorem state {B steps total:ℕ} {phases:List Com} {σ τ:Env}
    (trace:Segment B phases steps total σ τ) (hσ:NativeStateBounds.Bounded B σ):
    NativeStateBounds.Bounded B τ:=by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeStateBounds.run rr hσ)

end Lax263307Proofs.NativeMachineBounds

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem RootData.trans {σ ν τ:Env} (h1:RootData σ ν) (h2:RootData ν τ):RootData σ τ:=
  ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem root_frame {B t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (ht:"root.target"∉c.wvars) (hf:"root.fuel"∉c.wvars):RootData σ τ:=
  ⟨rr.frame_var _ ht,rr.frame_var _ hf⟩

theorem protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

def arrays:List String:= ["catalog.mask","search.graph","catalog.card",
  "catalog.independent","moment.program","recursion.frames"]

theorem frame {n B D k r p b load F fuel S v limit t:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∈scalars):=rr.frame_var s (hv s hs)
  have a (s:String) (hs:s∈arrays):=rr.frame_arr s (ha s hs)
  refine ⟨?_,(v _ (by simp [scalars])).trans hc.target,
    (v _ (by simp [scalars])).trans hc.sparsity,
    (v _ (by simp [scalars])).trans hc.denominator,
    (v _ (by simp [scalars])).trans hc.classB,
    (v _ (by simp [scalars])).trans hc.loadValue,
    (v _ (by simp [scalars])).trans hc.nodeD,
    (v _ (by simp [scalars])).trans hc.floorPower,?_,
    (v _ (by simp [scalars])).trans hc.programLength,
    (v _ (by simp [scalars])).trans hc.roundLimit,
    (v _ (by simp [scalars])).trans hc.roundWidth,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (v _ (by simp [scalars])).trans hc.cursor,
    (v _ (by simp [scalars])).trans hc.stride,
    (v _ (by simp [scalars])).trans hc.depth,
    (v _ (by simp [scalars])).trans hc.frameLength⟩
  · refine ⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by simp [scalars]))
      (hv _ (by simp [scalars])) (ha _ (by simp [arrays])) (ha _ (by simp [arrays])) hc.moments.1,
      ?_,?_,(v _ (by simp [scalars])).trans hc.moments.2.2.2⟩
    · simpa only [Prefix,a "catalog.card" (by simp [arrays])] using hc.moments.2.1
    · simpa only [Prefix,a "catalog.independent" (by simp [arrays])] using hc.moments.2.2.1
  · simpa only [Prefix,a "moment.program" (by simp [arrays])] using hc.program
  · intro s; rw [RamFrames.run_array_length rr]; exact hc.lengths s
  · simpa only [Prefix,a "recursion.frames" (by simp [arrays])] using hc.stack

theorem collection {n B D k r p b load F fuel S v limit steps total:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {base τ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front base)
    (trace:Segment B (phases cfg) steps total base τ)
    (anchor:NativeCollectionAnchor.Anchor base τ)
    (order:τ.vars "graph.n"=n)
    (stack:Prefix front "recursion.frames" τ) (cursor:τ.vars "stack.words"=front.length):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∉NativeCollectionAnchor.workScalars):=anchor.1 s hs
  have a (s:String) (hs:s∉NativeCollectionAnchor.workArrays):=anchor.2 s hs
  refine ⟨?_,(v _ (by decide)).trans hc.target,(v _ (by decide)).trans hc.sparsity,
    (v _ (by decide)).trans hc.denominator,(v _ (by decide)).trans hc.classB,
    (v _ (by decide)).trans hc.loadValue,(v _ (by decide)).trans hc.nodeD,
    (v _ (by decide)).trans hc.floorPower,?_,(v _ (by decide)).trans hc.programLength,
    (v _ (by decide)).trans hc.roundLimit,(v _ (by decide)).trans hc.roundWidth,NativeMachineBounds.state trace hc.bounded,
    ?_,stack,cursor,(v _ (by decide)).trans hc.stride,(v _ (by decide)).trans hc.depth,
    (v _ (by decide)).trans hc.frameLength⟩
  · rcases hc.moments with ⟨⟨hn,hN,hm,hg,hbits⟩,hcard,hind,hr⟩
    refine ⟨⟨order,(v _ (by decide)).trans hN,?_,?_,?_⟩,
      ?_,?_,(v _ (by decide)).trans hr⟩
    · simpa only [Prefix,a "catalog.mask" (by decide)] using hm
    · simpa only [Prefix,a "search.graph" (by decide)] using hg
    · rw [NativeMachineFrame.array_length trace]; exact hbits
    · simpa only [Prefix,a "catalog.card" (by decide)] using hcard
    · simpa only [Prefix,a "catalog.independent" (by decide)] using hind
  · simpa only [Prefix,a "moment.program" (by decide)] using hc.program
  · intro s; rw [NativeMachineFrame.array_length trace]; exact hc.lengths s

end Lax263307Proofs.NativeOracleContext

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters NativeCoreMachine NativeMachineSegment

theorem exhaustive_segment {n:ℕ} (B:ℕ) (cfg:Config) (lp flow:List ℕ→ List ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel:ℕ)
    (hsmall:k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1)
    (hdispatch:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29< B)
    (hsearch:n*n+(n+1)*(k+1)+n+k+24< B) (hm:2^n< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    ∀ σ,NativeNodeDispatch.Input n D k fuel σ→
      NativeSmallAttempt.Input G k σ→ σ.vars "machine.running"=1→ σ.vars "machine.phase"=1→
      ∃ τ,Segment B (phases cfg) 2
        (entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20) σ τ∧
        NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ∧
        τ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" τ∧
        ∃ ν,Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ ν (entryCost cfg.a n)∧
          Run B (NativeSmallAttempt.command 14) ν τ (NativeExhaustive.cost n k+15*n+20):=by
  intro σ hinput hdata hr hp
  obtain ⟨ν,r1,p1⟩:=NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ hinput
  have hrν:ν.vars "machine.running"=1:=(r1.frame_var _ (by
    change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide)).trans hr
  have hpν:ν.vars "machine.phase"=2:=by
    simpa only [NativeNodeDispatch.route,hsmall,if_true,NativeNodeDispatch.Output] using p1.2.1
  have hgν:Prefix (NativeWeightReduction.adjacency G) "search.graph" ν:=by
    rw [Prefix,r1.frame_arr "search.graph" (by
      change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
      decide)]
    exact hdata.2.2.1
  obtain ⟨τ,r2,p2⟩:=NativeSmallAttempt.command_spec B 14 G k hsearch hm hcoeff ν
    ⟨p1.1.1,p1.1.2.2.1,hgν,by rw [RamFrames.run_array_length r1]; exact hdata.2.2.2.1,
      by rw [RamFrames.run_array_length r1]; exact hdata.2.2.2.2⟩
  have s1:Segment B (phases cfg) 1 (entryCost cfg.a n) σ ν:=
    NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp r1
  have s2:Segment B (phases cfg) 1 (NativeExhaustive.cost n k+15*n+20) ν τ:=
    NativeMachineSegment.phase hrν ⟨2,by change 2<16; decide⟩ hpν r2
  refine ⟨τ,?_,?_,p2.1,?_,ν,r1,r2⟩
  · convert NativeMachineSegment.append s1 s2 using 1 <;> simp [Nat.add_assoc]
  · refine ⟨(r2.frame_var _ (by decide)).trans hrν,p2.2.2,?_⟩
    cases fuel <;> simpa only [RecursiveAlgorithm.attempt,hsmall,if_true] using p2.2.1
  · rw [Prefix,r2.frame_arr "search.graph" (by decide)]
    exact hgν

theorem reject_segment {n:ℕ} (B:ℕ) (cfg:Config) (lp flow:List ℕ→ List ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel:ℕ)
    (hsmall:¬(k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1)) (hreject:n< k∨ fuel=0)
    (hdispatch:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29< B):
    ∀ σ,NativeNodeDispatch.Input n D k fuel σ→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=1→
      ∃ τ,Segment B (phases cfg) 1 (entryCost cfg.a n) σ τ∧
        NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ∧
        NativeNodeDispatch.Input n D k fuel τ:=by
  intro σ hi hr hp
  obtain ⟨τ,rr,po⟩:=NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ hi
  have hout:τ.vars "machine.phase"=14∧ τ.vars "recursion.return.tag"=0:=by
    simpa only [NativeNodeDispatch.route,hsmall,if_false,hreject,if_true,NativeNodeDispatch.Output] using po.2.1
  refine ⟨τ,NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp rr,?_,po.1⟩
  refine ⟨(rr.frame_var _ (by
    change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide)).trans hr,hout.1,?_⟩
  have he:RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k=none:=by
    rcases hreject with hk | hf
    · cases fuel <;> simp only [RecursiveAlgorithm.attempt,hsmall,if_false,hk,if_true]
    · subst fuel
      simp only [RecursiveAlgorithm.attempt,hsmall,if_false]
      split <;> rfl
  simpa only [he,NativeTargetDriver.Reply] using hout.2

end Lax263307Proofs.NativeNodeTrace

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

def scalars:List String:= ["stack.words","recursion.stride","frame.length","algorithm.roundWidth","node.D"]

theorem frame {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t) (hc:Protocol B D S v cfg extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:"recursion.frames"∉c.warrs):
    Protocol B D S v cfg extent front τ:=by
  refine ⟨NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.stride,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.frameLength,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.roundWidth,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.accuracy⟩
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" ha] using hc.stack

theorem dispatch_frame {B D S v t:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t)
    (hc:Protocol B D S v cfg extent front σ):Protocol B D S v cfg extent front τ:=by
  apply frame rr hc
  · change ∀ s∈scalars,s∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide
  · change "recursion.frames"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
    decide

theorem dispatch_root {B t:ℕ} (cfg:Config) {σ τ:Env}
    (rr:Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t):RootData σ τ:=by
  apply root_frame rr
  all_goals first
    | change "root.target"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
    | change "root.fuel"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide

theorem child_variable (cfg:Config) (s:String)
    (hg:s∉NativeChildGraph.command.wvars) (hc:s∉NativeChildActivate.command.wvars)
    (he:s∉(NativeChildCall.enter 1).wvars) (hphase:s≠"machine.phase")
    (hstack:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉((phases cfg)[11]'(by change 11<16; decide)).wvars:=by
  have hsave:=NativeChildCall.save_variable (frameArrays cfg) (frameScalars cfg) s hstack
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeChildCall.command,go,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem pushed_length {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {σ saved:Env} {c:Com} (rr:Run B c σ saved t)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S):
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved).length=
      front.length+S*(frameArrays cfg).length+(frameScalars cfg).length:=by
  have h:(NativeFrameBuffers.words (frameArrays cfg) saved).length=S*(frameArrays cfg).length:=
    NativeFrameBuffers.words_length _ S saved (fun a ha => by rw [RamFrames.run_array_length rr,hc.lengths]; exact hext a ha)
  simp only [List.length_append,NativeRecursionFrame.words,NativeFrameScalars.words,List.length_map,h,Nat.add_assoc]

theorem child_entry {B D S v t cost:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ saved entry:Env} {c:Com} (snapshot:Run B c σ saved t)
    (call:Segment B (phases cfg) 1 cost σ entry)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S)
    (hp:σ.vars "machine.phase"=11)
    (hfront:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry)
    (hwords:entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length):
    Protocol B D S v cfg extent
      (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry:=by
  have rr:=NativeMachineFrame.single_run call ⟨11,by change 11<16; decide⟩ hp
  refine ⟨NativeMachineBounds.state call hc.bounded,?_,hfront,?_,?_,?_,?_,?_⟩
  · intro a; rw [NativeMachineFrame.array_length call]; exact hc.lengths a
  · rw [pushed_length snapshot hc hext]; exact hwords
  all_goals apply (rr.frame_var _ (child_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide))).trans
  all_goals first | exact hc.stride | exact hc.frameLength | exact hc.roundWidth | exact hc.accuracy

theorem children {n:ℕ} (B D fuel S v childSteps childTime:ℕ) (cfg:Config)
    (lp flow:List ℕ→ List ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent:String→ ℕ) (front:List ℕ) (eligible:Eligible)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (ih:Executes B D fuel S v childSteps childTime cfg lp flow extent eligible):
    Children B D fuel S v childSteps childTime cfg G extent front eligible
      (fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (ComputedSeparators.restriction G C) t):=by
  intro C target σ hel hp phase saved entry snapshot call hfront hwords hgraph horder hk hf hr he
  have protocolEntry:=child_entry cfg snapshot call hp hext phase hfront hwords
  have hlength:=pushed_length snapshot hp hext
  obtain ⟨τ,s,t,trace,hs,ht,answer,protocolDone,rootDone,graphDone⟩:=ih C.card (ComputedSeparators.restriction G C) target
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry
    (by simpa only [hlength] using hel) ⟨protocolEntry,horder,hgraph,hk,hf⟩ hr he
  exact ⟨τ,s,t,trace,hs,ht,answer,protocolDone.stack,
    by simpa only [hlength] using protocolDone.cursor,protocolDone.frameLength,protocolDone.stride⟩

end Lax263307Proofs.NativeNodeProtocol

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

theorem small_input {n w D k fuel S v:ℕ} {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent:String→ ℕ} {front:List ℕ} {σ:Env}
    (bounds:Bounds w D k fuel n cfg extent) (hi:Input (2^w) D fuel S v cfg G k extent front σ):
    NativeSmallAttempt.Input G k σ:=
  ⟨hi.order,hi.target,hi.graph,by rw [hi.protocol.lengths]; exact bounds.smallTable,
    by rw [hi.protocol.lengths]; exact bounds.bits⟩

theorem small_segment {n:ℕ} (D k fuel S v w:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow:List ℕ→ List ℕ)
    (extent:String→ ℕ) (front:List ℕ) (bounds:Bounds w D k fuel n cfg extent)
    (hsmall:k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1) (σ:Env)
    (hi:Input (2^w) D fuel S v cfg G k extent front σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=1):
    ∃ τ,Segment (2^w) (phases cfg) 2 (NativeNodeTrace.entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20) σ τ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ∧
      Protocol (2^w) D S v cfg extent front τ∧ RootData σ τ∧ GraphData G τ:=by
  obtain ⟨τ,trace,answer,order,graph,ν,r1,r2⟩:=NativeNodeTrace.exhaustive_segment (2^w) cfg lp flow G D k fuel
    hsmall bounds.dispatch bounds.exhaustive bounds.masks bounds.choose σ
    ⟨hi.order,hi.protocol.accuracy,hi.target,hi.depth⟩ (small_input bounds hi) hr hp
  exact ⟨τ,trace,answer,NativeNodeProtocol.frame r2 (dispatch_frame cfg r1 hi.protocol) (by decide) (by decide),
    (dispatch_root cfg r1).trans (root_frame r2 (by decide) (by decide)),order,graph⟩

theorem reject_segment {n:ℕ} (D k fuel S v w:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow:List ℕ→ List ℕ)
    (extent:String→ ℕ) (front:List ℕ) (bounds:Bounds w D k fuel n cfg extent)
    (hsmall:¬(k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1)) (hreject:n< k∨ fuel=0) (σ:Env)
    (hi:Input (2^w) D fuel S v cfg G k extent front σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=1):
    ∃ τ,Segment (2^w) (phases cfg) 1 (NativeNodeTrace.entryCost cfg.a n) σ τ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ∧
      Protocol (2^w) D S v cfg extent front τ∧ RootData σ τ∧ GraphData G τ:=by
  obtain ⟨τ,trace,answer,hinput⟩:=NativeNodeTrace.reject_segment (2^w) cfg lp flow G D k fuel
    hsmall hreject bounds.dispatch σ ⟨hi.order,hi.protocol.accuracy,hi.target,hi.depth⟩ hr hp
  have rr:=NativeMachineFrame.single_run trace ⟨1,by change 1<16; decide⟩ hp
  refine ⟨τ,trace,answer,dispatch_frame cfg rr hi.protocol,dispatch_root cfg rr,hinput.1,?_⟩
  simpa only [Prefix,rr.frame_arr "search.graph" (by
    change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
    decide)] using hi.graph

theorem work_base (localCost branches fuel:ℕ):localCost≤ NativeRecursionBudget.work localCost branches fuel:=by
  cases fuel <;> simp only [NativeRecursionBudget.work] <;> omega

theorem executes (D S v w localSteps localTime branches:ℕ) (cfg:Config)
    (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (eligible:Eligible)
    (resources:Resources D S v w localSteps localTime branches cfg lp flow extent eligible):
    ∀ fuel,Executes (2^w) D fuel S v (NativeRecursionBudget.work localSteps branches fuel)
      (NativeRecursionBudget.work localTime branches fuel) cfg lp flow extent eligible:=by
  intro fuel
  induction fuel with
  | zero =>
    intro n G _ k front σ hel hi hr hp
    have bounds:=resources.entry 0 n G k front.length hel
    by_cases hsmall:k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩:=small_segment D k 0 S v w cfg G lp flow extent front bounds hsmall σ hi hr hp
      have caps:=resources.small 0 n G k front.length hel hsmall
      exact ⟨τ,2,_,trace,caps.1,caps.2,answer,protocolτ,rootτ,graphτ⟩
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩:=reject_segment D k 0 S v w cfg G lp flow extent front bounds hsmall (by simp) σ hi hr hp
      have caps:=resources.entryCost 0 n G k front.length hel
      exact ⟨τ,1,_,trace,caps.1,caps.2,answer,protocolτ,rootτ,graphτ⟩
  | succ fuel ih =>
    intro n G _ k front σ hel hi hr hp
    have bounds:=resources.entry (fuel+1) n G k front.length hel
    by_cases hsmall:k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩:=small_segment D k (fuel+1) S v w cfg G lp flow extent front bounds hsmall σ hi hr hp
      have caps:=resources.small (fuel+1) n G k front.length hel hsmall
      exact ⟨τ,2,_,trace,caps.1.trans (work_base _ _ _),caps.2.trans (work_base _ _ _),answer,protocolτ,rootτ,graphτ⟩
    · by_cases hk:n< k
      · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩:=reject_segment D k (fuel+1) S v w cfg G lp flow extent front bounds hsmall (Or.inl hk) σ hi hr hp
        have caps:=resources.entryCost (fuel+1) n G k front.length hel
        exact ⟨τ,1,_,trace,caps.1.trans (work_base _ _ _),caps.2.trans (work_base _ _ _),answer,protocolτ,rootτ,graphτ⟩
      · have children:=NativeNodeProtocol.children (2^w) D fuel S v
          (NativeRecursionBudget.work localSteps branches fuel) (NativeRecursionBudget.work localTime branches fuel)
          cfg lp flow G extent front eligible resources.frameExtents ih
        exact large_segment D k fuel S v w _ _ localSteps localTime branches cfg G lp flow extent front eligible bounds
          (resources.large fuel n G k front hel hsmall (by omega)) children hsmall (by omega) σ hi hr hp

end Lax263307Proofs.NativeNodeExecution

end

theorem solution:∀ (D S v w localSteps localTime branches:ℕ) (cfg:Lax263307Proofs.NativeCoreMachine.Config)
  (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (eligible:Lax263307Proofs.NativeNodeProtocol.Eligible)
  (resources:
    Lax263307Proofs.NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible)
  (fuel:ℕ),
  Lax263307Proofs.NativeNodeProtocol.Executes (2 ^ w) D fuel S v
    (Lax263307Proofs.NativeRecursionBudget.work localSteps branches fuel)
    (Lax263307Proofs.NativeRecursionBudget.work localTime branches fuel) cfg lp flow extent eligible:= @Lax263307Proofs.NativeNodeExecution.executes
