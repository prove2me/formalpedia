-- Prove2me | solution 1 for Lax263307Proofs.NativeCoreExecution.command_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:46:22.330405+00:00
-- url     : https://prove2.me/submissions/66eae313-d1c7-4f1f-ab46-c19d5599a33d

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces
import Theorems.Thm_Lax263307Proofs_NativeNodeExecution_executes

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

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

theorem evalB_condEq {B:ℕ} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n):
    (Cond.eq e f).evalB B σ=some (m == n):=by
  rw [Cond.evalB,he,Option.bind_some,hf,Option.map_some]

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

end Lax808846Proofs.Reasoning

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

namespace RunStep

theorem eval_lit (B n:ℕ) (σ:Env) (h:n < B):
    (Expr.lit n).evalB B σ=some n:=evalB_lit h

theorem eval_var (B:ℕ) (σ:Env) (x:String) (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=evalB_var h

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_sub (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m - n < B):
    (Expr.bin .sub e f).evalB B σ=some (m - n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem cond_eq_true (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m=n):
    (Cond.eq e f).evalB B σ=some true:=by
  rw [evalB_condEq he hf,h]; simp

theorem cond_eq_false (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:¬ m=n):
    (Cond.eq e f).evalB B σ=some false:=by
  rw [evalB_condEq he hf]; simp [h]

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

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

end Lax263307Proofs.NativeMasks

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

namespace Lax263307Proofs.NativeStackReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem root_spec (B root:ℕ) (arrays scalars:List String) (hB:root+1< B):
    Spec B (fun σ => σ.vars "stack.words"=0) (command arrays scalars root)
      (fun σ τ => τ.vars "machine.phase"=root∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask" ∧ τ=σ.setVar "machine.phase" root) 6:=by
  intro σ hs
  let τ:=σ.setVar "machine.phase" root
  have rr:Run B (.assign "machine.phase" (.lit root)) σ τ 2:=Run.assign (evalB_lit (show root< B by omega))
  have hc:(Cond.eq (.var "stack.words") (.lit 0)).evalB B σ=some true:=by
    have hh:=evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (by omega:0< B)⟩) (evalB_lit (show 0< B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_true (d:=pop arrays scalars) hc rr).mono (by simp [Cond.size,Expr.size]),
    by simp [τ],rr.frame_var _ (by simp [Com.wvars]),rr.frame_var _ (by simp [Com.wvars]),rfl⟩

end Lax263307Proofs.NativeStackReturn

end

section

namespace Lax263307Proofs.NativeMachineTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem while_true_run {B K K':ℕ} {b:Cond} {c:Com} {σ μ τ:Env}
    (hc:b.evalB B σ=some true) (r1:Run B c σ μ K) (r2:Run B (.while b c) μ τ K'):
    Run B (.while b c) σ τ (1+b.size+K+K'):=by
  obtain ⟨k,hk,rr1⟩:=r1
  obtain ⟨k',hk',rr2⟩:=r2
  exact ⟨_,by omega,BigStepB.while_true hc rr1 rr2⟩

inductive Trace (B:ℕ) (cases:List Com):ℕ→ ℕ→ Env→ Env→ Prop
  | stop {σ:Env} (h:σ.vars "machine.running"=0):Trace B cases 0 0 σ σ
  | step {σ μ τ:Env} {steps total cost:ℕ} (h:σ.vars "machine.running"=1)
      (j:Fin cases.length) (hj:σ.vars "machine.phase"=j.val)
      (rr:Run B cases[j.val] σ μ cost) (rest:Trace B cases steps total μ τ):
      Trace B cases (steps+1) (cost+total) σ τ

theorem dispatch_run (B:ℕ) (cases:List Com) (i j K:ℕ) (hj:j< cases.length)
    (hB:i+cases.length+2< B) {σ τ:Env} (hphase:σ.vars "machine.phase"=i+j)
    (rr:Run B cases[j] σ τ K):Run B (dispatch cases i) σ τ (K+4*(j+1)):=by
  induction cases generalizing i j K with
  | nil => simp at hj
  | cons c cs ih =>
    have hphaseB:i+j< B:=by simp only [List.length_cons] at hj hB; omega
    have hc:(Cond.eq (.var "machine.phase") (.lit i)).evalB B σ=some (decide (i+j=i)):=by
      have hh:(Cond.eq (.var "machine.phase") (.lit i)).evalB B σ=some ((i+j)==i):=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hphase.symm,hphase ▸ hphaseB⟩)
        (evalB_lit (show i< B by simp only [List.length_cons] at hB; omega))
      have he:((i+j)==i)=decide (i+j=i):=by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq,decide_eq_true_eq]
      exact hh.trans (congrArg some he)
    cases j with
    | zero =>
      have rb:Run B c σ τ K:=by simpa only [List.getElem_cons_zero] using rr
      exact (Run.ite_true (d:=dispatch cs (i+1)) (by simpa using hc) rb).mono
        (by simp [Cond.size,Expr.size] <;> omega)
    | succ j =>
      have hcs:j< cs.length:=by simp only [List.length_cons] at hj; omega
      have rb:=ih (i+1) j K hcs (by simp only [List.length_cons] at hB; omega)
        (by simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1] using hphase)
        (by simpa only [List.getElem_cons_succ] using rr)
      exact (Run.ite_false (c:=c) (by simpa using hc) rb).mono
        (by simp [Cond.size,Expr.size,Nat.succ_eq_add_one]; omega)

theorem driver_run {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (tr:Trace B cases steps total σ τ) (hB:cases.length+2< B):
    Run B (driver cases) σ τ (total+(4*cases.length+4)*steps+4):=by
  induction tr with
  | stop h =>
    rename_i σ0
    have hc:(Cond.eq (.var "machine.running") (.lit 1)).evalB B σ0=some false:=by
      have hh:=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨h.symm,h ▸ (by omega:0< B)⟩) (evalB_lit (show 1< B by omega))
      simpa using hh
    exact (Run.while_false hc).mono (by simp [Cond.size,Expr.size])
  | step h j hj rr rest ih =>
    rename_i σ0 μ0 τ0 steps0 total0 cost0
    have hc:(Cond.eq (.var "machine.running") (.lit 1)).evalB B σ0=some true:=by
      have hh:=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨h.symm,h ▸ (by omega:1< B)⟩) (evalB_lit (show 1< B by omega))
      simpa using hh
    have rb:=dispatch_run B cases 0 j.val _ j.isLt (by simpa only [Nat.zero_add] using hB)
      (by simpa only [Nat.zero_add] using hj) rr
    have hcost:4*(j.val+1)≤4*cases.length:=Nat.mul_le_mul_left _ j.isLt
    exact (while_true_run hc (rb.mono (Nat.add_le_add_left hcost _)) ih).mono
      (by simp only [Cond.size,Expr.size]; nlinarith only [])

end Lax263307Proofs.NativeMachineTrace

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

theorem attach_trace {B s t s' t':ℕ} {cases:List Com} {σ μ τ:Env}
    (a:Segment B cases s t σ μ) (b:Trace B cases s' t' μ τ):
    Trace B cases (s+s') (t+t') σ τ:=by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Trace.step h j hj rr (ih b)

theorem finish {B s t:ℕ} {cases:List Com} {σ τ:Env}
    (a:Segment B cases s t σ τ) (halt:τ.vars "machine.running"=0):
    Trace B cases s t σ τ:=by
  simpa only [Nat.add_zero] using attach_trace a (Trace.stop halt)

theorem phase {B K:ℕ} {cases:List Com} {σ τ:Env}
    (running:σ.vars "machine.running"=1) (j:Fin cases.length)
    (phase:σ.vars "machine.phase"=j.val) (rr:Run B cases[j.val] σ τ K):
    Segment B cases 1 K σ τ:=by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

theorem driver_run {B s t:ℕ} {cases:List Com} {σ τ:Env}
    (a:Segment B cases s t σ τ) (halt:τ.vars "machine.running"=0)
    (hB:cases.length+2< B):
    Run B (driver cases) σ τ (t+(4*cases.length+4)*s+4):=
  NativeMachineTrace.driver_run (finish a halt) hB

end Lax263307Proofs.NativeMachineSegment

end

section

namespace Lax263307Proofs.NativeCoreMachine

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem phases_length (cfg:Config):(phases cfg).length=16:=rfl

theorem driver_run {B steps total:ℕ} {cfg:Config} {σ τ:Env}
    (trace:NativeMachineSegment.Segment B (phases cfg) steps total σ τ)
    (halt:τ.vars "machine.running"=0) (hB:18< B):
    Run B (NativeMachineTrace.driver (phases cfg)) σ τ (total+68*steps+4):=by
  exact NativeMachineSegment.driver_run trace halt hB

end Lax263307Proofs.NativeCoreMachine

end

section

namespace Lax263307Proofs.NativeReturnTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem reply_transfer {n:ℕ} (answer:Option (Finset (Fin n))) {σ τ:Env}
    (ht:τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag")
    (hm:τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
    (h:NativeTargetDriver.Reply answer σ):NativeTargetDriver.Reply answer τ:=by
  cases answer <;> simp only [NativeTargetDriver.Reply,ht,hm] at * <;> assumption

theorem root_segment {n:ℕ} (B:ℕ) (cfg:Config) (answer:Option (Finset (Fin n)))
    (hB:16< B) (σ:Env) (hs:σ.vars "stack.words"=0) (h:NativeRoundTrace.Stopped answer σ):
    ∃ τ,Segment B (phases cfg) 1 6 σ τ∧ τ=σ.setVar "machine.phase" 15∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=15∧ NativeTargetDriver.Reply answer τ:=by
  obtain ⟨τ,rr,po⟩:=NativeStackReturn.root_spec B 15 (frameArrays cfg) (frameScalars cfg) hB σ hs
  refine ⟨τ,NativeMachineSegment.phase h.1 ⟨14,by change 14<16; decide⟩ h.2.1 rr,
    po.2.2.2,?_,po.1,reply_transfer answer po.2.1 po.2.2.1 h.2.2⟩
  rw [po.2.2.2]
  simpa using h.1

end Lax263307Proofs.NativeReturnTrace

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

namespace Lax263307Proofs.NativeRootTransitions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine Lax263307 NativeMasks

theorem frame_size_spec (B S:ℕ) (cfg:Config)
    (hB:S*(frameArrays cfg).length+(frameScalars cfg).length+S+(frameArrays cfg).length+10< B):
    Spec B (fun σ => σ.vars "recursion.stride"=S) (frameSize cfg)
      (fun _ τ => τ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length) 6:=by
  intro σ hs
  (expose_names;
    (refine let vcgPost0:Nat.lt (Nat.mul (Env.vars σ "recursion.stride") (@List.length String (frameArrays cfg))) B:= ?_; let vcgPost1:Nat.lt (Nat.add (Nat.mul (Env.vars σ "recursion.stride") (@List.length String (frameArrays cfg))) (@List.length String (frameScalars cfg))) B:= ?_; let vcgPost2:@Eq Nat (Env.vars (Env.setVar σ "frame.length" (Nat.add (Nat.mul (Env.vars σ "recursion.stride") (@List.length String (frameArrays cfg))) (@List.length String (frameScalars cfg)))) "frame.length") (Nat.add (Nat.mul S (@List.length String (frameArrays cfg))) (@List.length String (frameScalars cfg))):= ?_; let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "frame.length") (c0 (c1 S (@List.length String (frameArrays cfg))) (@List.length String (frameScalars cfg)))) σ; let c3:Nat:=c1 (Env.vars σ "recursion.stride") (@List.length String (frameArrays cfg)); let c4:Nat:=c0 c3 (@List.length String (frameScalars cfg)); let c5:Env:=Env.setVar σ "frame.length" c4; let c6:Expr:=Expr.mul (Expr.var "recursion.stride") (Expr.lit (@List.length String (frameArrays cfg))); let c7:Expr:=Expr.add c6 (Expr.lit (@List.length String (frameScalars cfg))); @Exists.intro Env (fun (σ':Env) => And (Run B (frameSize cfg) σ σ' ((6:Nat))) (c2 σ')) c5 (@And.intro (Run B (frameSize cfg) σ c5 ((6:Nat))) (c2 c5) (RunStep.mono B (frameSize cfg) σ c5 (c0 ((1:Nat)) (Expr.size c7)) ((6:Nat)) (RunStep.assign B σ "frame.length" c7 c4 (RunStep.eval_add B σ c6 (Expr.lit (@List.length String (frameScalars cfg))) c3 (@List.length String (frameScalars cfg)) (RunStep.eval_mul B σ (Expr.var "recursion.stride") (Expr.lit (@List.length String (frameArrays cfg))) (Env.vars σ "recursion.stride") (@List.length String (frameArrays cfg)) (RunStep.eval_var B σ "recursion.stride" (?nAX_g9573_0_0_0)) (RunStep.eval_lit B (@List.length String (frameArrays cfg)) σ (?nAX_g9573_0_0_1)) vcgPost0) (RunStep.eval_lit B (@List.length String (frameScalars cfg)) σ (?nAX_g9573_0_0_2)) vcgPost1)) (?nAX_g9573_0_0_3)) vcgPost2) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear_value vcgPost2); (all_goals try clear vcgPost2); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9573_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9573_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9573_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9573_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem initialize_spec (B n fuel:ℕ) (hB:n+fuel+2< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "recursion.fuel"=fuel) initializeRoot
      (fun _ τ => τ.vars "root.target"=n∧ τ.vars "root.fuel"=fuel∧ τ.vars "stack.words"=0∧
        τ.vars "machine.running"=1∧ τ.vars "machine.phase"=0) 10:=by
  intro σ hs
  (expose_names;
    (refine let vcgPost0:And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar (Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel")) "stack.words" ((0:Nat))) "machine.running" ((1:Nat))) "machine.phase" ((0:Nat))) "root.target") n) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar (Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel")) "stack.words" ((0:Nat))) "machine.running" ((1:Nat))) "machine.phase" ((0:Nat))) "root.fuel") fuel) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar (Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel")) "stack.words" ((0:Nat))) "machine.running" ((1:Nat))) "machine.phase" ((0:Nat))) "stack.words") ((0:Nat))) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar (Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel")) "stack.words" ((0:Nat))) "machine.running" ((1:Nat))) "machine.phase" ((0:Nat))) "machine.running") ((1:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar (Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel")) "stack.words" ((0:Nat))) "machine.running" ((1:Nat))) "machine.phase" ((0:Nat))) "machine.phase") ((0:Nat)))))):= ?_; let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "root.target") n) (And (@Eq Nat (Env.vars τ "root.fuel") fuel) (And (@Eq Nat (Env.vars τ "stack.words") ((0:Nat))) (And (@Eq Nat (Env.vars τ "machine.running") ((1:Nat))) (@Eq Nat (Env.vars τ "machine.phase") ((0:Nat))))))) σ; let c1:Nat:=Env.vars (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel"; let c2:Env:=Env.setVar (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" c1; let c3:Env:=Env.setVar c2 "stack.words" ((0:Nat)); let c4:Env:=Env.setVar c3 "machine.running" ((1:Nat)); let c5:Env:=Env.setVar c4 "machine.phase" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.var "graph.n")); let c9:Nat:=c7 (Expr.size (Expr.var "recursion.fuel")); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c12:Nat:=c6 c11 c10; let c13:Nat:=c6 c10 c12; let c14:Nat:=c6 c9 c13; let c15:Com:=Com.assign "stack.words" (Expr.lit ((0:Nat))); let c16:Com:=Com.assign "machine.running" (Expr.lit ((1:Nat))); let c17:Com:=Com.seq c16 (go ((0:Nat))); let c18:Com:=Com.seq c15 c17; @Exists.intro Env (fun (σ':Env) => And (Run B initializeRoot σ σ' ((10:Nat))) (c0 σ')) c5 (@And.intro (Run B initializeRoot σ c5 ((10:Nat))) (c0 c5) (RunStep.mono B initializeRoot σ c5 (c6 c8 c14) ((10:Nat)) (RunStep.seq B (Com.assign "root.target" (Expr.var "graph.n")) (Com.seq (Com.assign "root.fuel" (Expr.var "recursion.fuel")) c18) σ (Env.setVar σ "root.target" (Env.vars σ "graph.n")) c5 c8 c14 (RunStep.assign B σ "root.target" (Expr.var "graph.n") (Env.vars σ "graph.n") (RunStep.eval_var B σ "graph.n" (?nAX_g9574_0_0_0))) (RunStep.seq B (Com.assign "root.fuel" (Expr.var "recursion.fuel")) c18 (Env.setVar σ "root.target" (Env.vars σ "graph.n")) c2 c5 c9 c13 (RunStep.assign B (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "root.fuel" (Expr.var "recursion.fuel") c1 (RunStep.eval_var B (Env.setVar σ "root.target" (Env.vars σ "graph.n")) "recursion.fuel" (?nAX_g9574_0_0_1))) (RunStep.seq B c15 c17 c2 c3 c5 c10 c12 (RunStep.assign B c2 "stack.words" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g9574_0_0_2))) (RunStep.seq B c16 (go ((0:Nat))) c3 c4 c5 c11 c10 (RunStep.assign B c3 "machine.running" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 (?nAX_g9574_0_0_3))) (RunStep.assign B c4 "machine.phase" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g9574_0_0_4))))))) (?nAX_g9574_0_0_5)) vcgPost0) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9574_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9574_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9574_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9574_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9574_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9574_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Env.setVar]

theorem target_zero_spec (B:ℕ) (hB:2< B):
    Spec B (fun σ => σ.vars "root.target"=0) rootTarget
      (fun _ τ => τ.vars "root.mask"=0∧ τ.vars "root.value"=0∧ τ.vars "machine.running"=0) 10:=by
  intro σ hs
  (expose_names;
    (refine let vcgPost0:@Eq Nat (Env.vars σ "root.target") ((0:Nat))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "root.mask") ((0:Nat))) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "root.value") ((0:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "machine.running") ((0:Nat)))):= ?_; let vcgPost1:Not (@Eq Nat (Env.vars σ "root.target") ((0:Nat)))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "root.mask") ((0:Nat))) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "root.value") ((0:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "machine.running") ((0:Nat)))):= ?_; let c0:Prop:= @Eq Nat (Env.vars σ "root.target") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "root.mask") ((0:Nat))) (And (@Eq Nat (Env.vars τ "root.value") ((0:Nat))) (@Eq Nat (Env.vars τ "machine.running") ((0:Nat))))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B rootTarget σ σ' ((10:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "root.mask" ((0:Nat)); let c5:Env:=Env.setVar c4 "root.value" ((0:Nat)); let c6:Env:=Env.setVar c5 "machine.running" ((0:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Cond:=Cond.eq (Expr.var "root.target") (Expr.lit ((0:Nat))); let c10:Nat→ Nat:=c7 (c8 (Cond.size c9)); let c11:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c12:Nat→ Nat:=c7 c11; let c13:Nat:=c12 c11; let c14:Nat:=c12 c13; let c15:Com:=Com.seq (Com.assign "recursion.fuel" (Expr.var "root.fuel")) (go ((1:Nat))); let c16:Com:=Com.seq (Com.assign "node.k" (Expr.var "root.target")) c15; let c17:Com:=Com.assign "root.value" (Expr.lit ((0:Nat))); let c18:Com:=Com.assign "machine.running" (Expr.lit ((0:Nat))); let c19:Nat:=Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel"; let c20:Env:=Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" c19; let c21:Env:=Env.setVar c20 "machine.phase" ((1:Nat)); let c22:Nat:=c8 (Expr.size (Expr.var "root.target")); let c23:Nat:=c8 (Expr.size (Expr.var "root.fuel")); let c24:Nat:=c8 (Expr.size (Expr.lit ((1:Nat)))); let c25:Nat:=c7 c23 c24; let c26:Nat:=c7 c22 c25; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c6 (@And.intro (Run B rootTarget σ c6 ((10:Nat))) (c2 c6) (RunStep.mono B rootTarget σ c6 (c10 c14) ((10:Nat)) (RunStep.ite_true B c9 emptyRoot c16 σ c6 c14 (RunStep.cond_eq_true B σ (Expr.var "root.target") (Expr.lit ((0:Nat))) (Env.vars σ "root.target") ((0:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9575_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9575_0_0_1)) hcase) (RunStep.seq B (Com.assign "root.mask" (Expr.lit ((0:Nat)))) (Com.seq c17 c18) σ c4 c6 c11 c13 (RunStep.assign B σ "root.mask" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9575_0_0_2))) (RunStep.seq B c17 c18 c4 c5 c6 c11 c11 (RunStep.assign B c4 "root.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g9575_0_0_3))) (RunStep.assign B c5 "machine.running" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g9575_0_0_4)))))) (?nAX_g9575_0_0_5)) (vcgPost0 hcase))) fun (hcase:c1) => @Exists.intro Env c3 c21 (@And.intro (Run B rootTarget σ c21 ((10:Nat))) (c2 c21) (RunStep.mono B rootTarget σ c21 (c10 c26) ((10:Nat)) (RunStep.ite_false B c9 emptyRoot c16 σ c21 c26 (RunStep.cond_eq_false B σ (Expr.var "root.target") (Expr.lit ((0:Nat))) (Env.vars σ "root.target") ((0:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9575_0_0_6)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9575_0_0_7)) hcase) (RunStep.seq B (Com.assign "node.k" (Expr.var "root.target")) c15 σ (Env.setVar σ "node.k" (Env.vars σ "root.target")) c21 c22 c25 (RunStep.assign B σ "node.k" (Expr.var "root.target") (Env.vars σ "root.target") (RunStep.eval_var B σ "root.target" (?nAX_g9575_0_0_8))) (RunStep.seq B (Com.assign "recursion.fuel" (Expr.var "root.fuel")) (go ((1:Nat))) (Env.setVar σ "node.k" (Env.vars σ "root.target")) c20 c21 c23 c24 (RunStep.assign B (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Expr.var "root.fuel") c19 (RunStep.eval_var B (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel" (?nAX_g9575_0_0_9))) (RunStep.assign B c20 "machine.phase" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c20 (?nAX_g9575_0_0_10)))))) (?nAX_g9575_0_0_11)) (vcgPost1 hcase)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9575_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9575_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Env.setVar]

theorem target_positive_spec (B k fuel:ℕ) (hk:0< k) (hB:k+fuel+2< B):
    Spec B (fun σ => σ.vars "root.target"=k∧ σ.vars "root.fuel"=fuel) rootTarget
      (fun σ τ => τ.vars "node.k"=k∧ τ.vars "recursion.fuel"=fuel∧ τ.vars "machine.phase"=1∧
        τ.vars "machine.running"=σ.vars "machine.running") 10:=by
  intro σ hs
  (expose_names;
    (refine let vcgPost0:@Eq Nat (Env.vars σ "root.target") ((0:Nat))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "node.k") k) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "recursion.fuel") fuel) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "machine.phase") ((1:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" ((0:Nat))) "root.value" ((0:Nat))) "machine.running" ((0:Nat))) "machine.running") (Env.vars σ "machine.running")))):= ?_; let vcgPost1:Not (@Eq Nat (Env.vars σ "root.target") ((0:Nat)))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "node.k") k) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "recursion.fuel") fuel) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "machine.phase") ((1:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel")) "machine.phase" ((1:Nat))) "machine.running") (Env.vars σ "machine.running")))):= ?_; let c0:Prop:= @Eq Nat (Env.vars σ "root.target") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "node.k") k) (And (@Eq Nat (Env.vars τ "recursion.fuel") fuel) (And (@Eq Nat (Env.vars τ "machine.phase") ((1:Nat))) (@Eq Nat (Env.vars τ "machine.running") (Env.vars σ_1 "machine.running"))))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B rootTarget σ σ' ((10:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "root.mask" ((0:Nat)); let c5:Env:=Env.setVar c4 "root.value" ((0:Nat)); let c6:Env:=Env.setVar c5 "machine.running" ((0:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Cond:=Cond.eq (Expr.var "root.target") (Expr.lit ((0:Nat))); let c10:Nat→ Nat:=c7 (c8 (Cond.size c9)); let c11:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c12:Nat→ Nat:=c7 c11; let c13:Nat:=c12 c11; let c14:Nat:=c12 c13; let c15:Com:=Com.seq (Com.assign "recursion.fuel" (Expr.var "root.fuel")) (go ((1:Nat))); let c16:Com:=Com.seq (Com.assign "node.k" (Expr.var "root.target")) c15; let c17:Com:=Com.assign "root.value" (Expr.lit ((0:Nat))); let c18:Com:=Com.assign "machine.running" (Expr.lit ((0:Nat))); let c19:Nat:=Env.vars (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel"; let c20:Env:=Env.setVar (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" c19; let c21:Env:=Env.setVar c20 "machine.phase" ((1:Nat)); let c22:Nat:=c8 (Expr.size (Expr.var "root.target")); let c23:Nat:=c8 (Expr.size (Expr.var "root.fuel")); let c24:Nat:=c8 (Expr.size (Expr.lit ((1:Nat)))); let c25:Nat:=c7 c23 c24; let c26:Nat:=c7 c22 c25; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c6 (@And.intro (Run B rootTarget σ c6 ((10:Nat))) (c2 c6) (RunStep.mono B rootTarget σ c6 (c10 c14) ((10:Nat)) (RunStep.ite_true B c9 emptyRoot c16 σ c6 c14 (RunStep.cond_eq_true B σ (Expr.var "root.target") (Expr.lit ((0:Nat))) (Env.vars σ "root.target") ((0:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9576_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9576_0_0_1)) hcase) (RunStep.seq B (Com.assign "root.mask" (Expr.lit ((0:Nat)))) (Com.seq c17 c18) σ c4 c6 c11 c13 (RunStep.assign B σ "root.mask" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9576_0_0_2))) (RunStep.seq B c17 c18 c4 c5 c6 c11 c11 (RunStep.assign B c4 "root.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g9576_0_0_3))) (RunStep.assign B c5 "machine.running" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g9576_0_0_4)))))) (?nAX_g9576_0_0_5)) (vcgPost0 hcase))) fun (hcase:c1) => @Exists.intro Env c3 c21 (@And.intro (Run B rootTarget σ c21 ((10:Nat))) (c2 c21) (RunStep.mono B rootTarget σ c21 (c10 c26) ((10:Nat)) (RunStep.ite_false B c9 emptyRoot c16 σ c21 c26 (RunStep.cond_eq_false B σ (Expr.var "root.target") (Expr.lit ((0:Nat))) (Env.vars σ "root.target") ((0:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9576_0_0_6)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g9576_0_0_7)) hcase) (RunStep.seq B (Com.assign "node.k" (Expr.var "root.target")) c15 σ (Env.setVar σ "node.k" (Env.vars σ "root.target")) c21 c22 c25 (RunStep.assign B σ "node.k" (Expr.var "root.target") (Env.vars σ "root.target") (RunStep.eval_var B σ "root.target" (?nAX_g9576_0_0_8))) (RunStep.seq B (Com.assign "recursion.fuel" (Expr.var "root.fuel")) (go ((1:Nat))) (Env.setVar σ "node.k" (Env.vars σ "root.target")) c20 c21 c23 c24 (RunStep.assign B (Env.setVar σ "node.k" (Env.vars σ "root.target")) "recursion.fuel" (Expr.var "root.fuel") c19 (RunStep.eval_var B (Env.setVar σ "node.k" (Env.vars σ "root.target")) "root.fuel" (?nAX_g9576_0_0_9))) (RunStep.assign B c20 "machine.phase" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c20 (?nAX_g9576_0_0_10)))))) (?nAX_g9576_0_0_11)) (vcgPost1 hcase)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9576_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9576_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem reply_none_spec (B k:ℕ) (hB:k+2< B):
    Spec B (fun σ => σ.vars "recursion.return.tag"=0∧ σ.vars "root.target"=k+1) rootReply
      (fun σ τ => τ.vars "root.target"=k∧ τ.vars "machine.phase"=0∧
        τ.vars "machine.running"=σ.vars "machine.running") 10:=by
  intro σ hs
  (expose_names;
    (refine let vcgPost0:@Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "root.target") k) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "machine.phase") ((0:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "machine.running") (Env.vars σ "machine.running"))):= ?_; let vcgPost1:Not (@Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat)))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "root.target") k) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "machine.phase") ((0:Nat))) (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "machine.running") (Env.vars σ "machine.running"))):= ?_; let c0:Prop:= @Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "root.target") k) (And (@Eq Nat (Env.vars τ "machine.phase") ((0:Nat))) (@Eq Nat (Env.vars τ "machine.running") (Env.vars σ_1 "machine.running")))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B rootReply σ σ' ((10:Nat))) (c2 σ'); let c4:Nat:=Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target"; let c5:Env:=Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" c4; let c6:Env:=Env.setVar c5 "machine.running" ((0:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Cond:=Cond.eq (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))); let c10:Nat→ Nat:=c7 (c8 (Cond.size c9)); let c11:Nat:=c8 (Expr.size (Expr.var "recursion.return.mask")); let c12:Nat:=c8 (Expr.size (Expr.var "root.target")); let c13:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c14:Nat:=c7 c12 c13; let c15:Nat:=c7 c11 c14; let c16:Com:=Com.assign "machine.running" (Expr.lit ((0:Nat))); let c17:Com:=Com.seq (Com.assign "root.value" (Expr.var "root.target")) c16; let c18:Com:=Com.seq (Com.assign "root.mask" (Expr.var "recursion.return.mask")) c17; let c19:Expr:=Expr.sub (Expr.var "root.target") (Expr.lit ((1:Nat))); let c20:Com:=Com.assign "root.target" c19; let c21:Com:=Com.seq c20 (go ((0:Nat))); let c22:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)); let c23:Env:=Env.setVar σ "root.target" c22; let c24:Env:=Env.setVar c23 "machine.phase" ((0:Nat)); let c25:Nat:=c8 (Expr.size c19); let c26:Nat:=c7 c25 c13; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c6 (@And.intro (Run B rootReply σ c6 ((10:Nat))) (c2 c6) (RunStep.mono B rootReply σ c6 (c10 c15) ((10:Nat)) (RunStep.ite_true B c9 c18 c21 σ c6 c15 (RunStep.cond_eq_true B σ (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))) (Env.vars σ "recursion.return.tag") ((1:Nat)) (RunStep.eval_var B σ "recursion.return.tag" (?nAX_g9577_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9577_0_0_1)) hcase) (RunStep.seq B (Com.assign "root.mask" (Expr.var "recursion.return.mask")) c17 σ (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) c6 c11 c14 (RunStep.assign B σ "root.mask" (Expr.var "recursion.return.mask") (Env.vars σ "recursion.return.mask") (RunStep.eval_var B σ "recursion.return.mask" (?nAX_g9577_0_0_2))) (RunStep.seq B (Com.assign "root.value" (Expr.var "root.target")) c16 (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) c5 c6 c12 c13 (RunStep.assign B (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Expr.var "root.target") c4 (RunStep.eval_var B (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target" (?nAX_g9577_0_0_3))) (RunStep.assign B c5 "machine.running" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g9577_0_0_4)))))) (?nAX_g9577_0_0_5)) (vcgPost0 hcase))) fun (hcase:c1) => @Exists.intro Env c3 c24 (@And.intro (Run B rootReply σ c24 ((10:Nat))) (c2 c24) (RunStep.mono B rootReply σ c24 (c10 c26) ((10:Nat)) (RunStep.ite_false B c9 c18 c21 σ c24 c26 (RunStep.cond_eq_false B σ (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))) (Env.vars σ "recursion.return.tag") ((1:Nat)) (RunStep.eval_var B σ "recursion.return.tag" (?nAX_g9577_0_0_6)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9577_0_0_7)) hcase) (RunStep.seq B c20 (go ((0:Nat))) σ c23 c24 c25 c13 (RunStep.assign B σ "root.target" c19 c22 (RunStep.eval_sub B σ (Expr.var "root.target") (Expr.lit ((1:Nat))) (Env.vars σ "root.target") ((1:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9577_0_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9577_0_0_9)) (?nAX_g9577_0_0_10))) (RunStep.assign B c23 "machine.phase" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c23 (?nAX_g9577_0_0_11))))) (?nAX_g9577_0_0_12)) (vcgPost1 hcase)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9577_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9577_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem reply_some_spec {n:ℕ} (B k:ℕ) (I:Finset (Fin n)) (hB:k+2< B) (hm:2^n< B):
    Spec B (fun σ => NativeTargetDriver.Reply (some I) σ∧ σ.vars "root.target"=k) rootReply
      (fun _ τ => τ.vars "root.mask"=mask I∧ τ.vars "root.value"=k∧ τ.vars "machine.running"=0) 10:=by
  have hmask:mask I< B:=(mask_bound I).trans hm
  intro σ hs
  (expose_names;
    (refine let vcgPost0:Nat.lt (Env.vars σ "recursion.return.tag") B:= ?_; let vcgPost1:@Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat))→ Nat.lt (Env.vars σ "recursion.return.mask") B:= ?_; let vcgPost2:@Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "root.mask") (@mask n I)) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "root.value") k) (@Eq Nat (Env.vars (Env.setVar (Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target")) "machine.running" ((0:Nat))) "machine.running") ((0:Nat)))):= ?_; let vcgPost3:Not (@Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat)))→ And (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "root.mask") (@mask n I)) (And (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "root.value") k) (@Eq Nat (Env.vars (Env.setVar (Env.setVar σ "root.target" (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)))) "machine.phase" ((0:Nat))) "machine.running") ((0:Nat)))):= ?_; let c0:Prop:= @Eq Nat (Env.vars σ "recursion.return.tag") ((1:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "root.mask") (@mask n I)) (And (@Eq Nat (Env.vars τ "root.value") k) (@Eq Nat (Env.vars τ "machine.running") ((0:Nat))))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B rootReply σ σ' ((10:Nat))) (c2 σ'); let c4:Nat:=Env.vars (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target"; let c5:Env:=Env.setVar (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" c4; let c6:Env:=Env.setVar c5 "machine.running" ((0:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Cond:=Cond.eq (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))); let c10:Nat→ Nat:=c7 (c8 (Cond.size c9)); let c11:Nat:=c8 (Expr.size (Expr.var "recursion.return.mask")); let c12:Nat:=c8 (Expr.size (Expr.var "root.target")); let c13:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c14:Nat:=c7 c12 c13; let c15:Nat:=c7 c11 c14; let c16:Com:=Com.assign "machine.running" (Expr.lit ((0:Nat))); let c17:Com:=Com.seq (Com.assign "root.value" (Expr.var "root.target")) c16; let c18:Com:=Com.seq (Com.assign "root.mask" (Expr.var "recursion.return.mask")) c17; let c19:Expr:=Expr.sub (Expr.var "root.target") (Expr.lit ((1:Nat))); let c20:Com:=Com.assign "root.target" c19; let c21:Com:=Com.seq c20 (go ((0:Nat))); let c22:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "root.target") ((1:Nat)); let c23:Env:=Env.setVar σ "root.target" c22; let c24:Env:=Env.setVar c23 "machine.phase" ((0:Nat)); let c25:Nat:=c8 (Expr.size c19); let c26:Nat:=c7 c25 c13; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c6 (@And.intro (Run B rootReply σ c6 ((10:Nat))) (c2 c6) (RunStep.mono B rootReply σ c6 (c10 c15) ((10:Nat)) (RunStep.ite_true B c9 c18 c21 σ c6 c15 (RunStep.cond_eq_true B σ (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))) (Env.vars σ "recursion.return.tag") ((1:Nat)) (RunStep.eval_var B σ "recursion.return.tag" vcgPost0) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9578_0_0_0)) hcase) (RunStep.seq B (Com.assign "root.mask" (Expr.var "recursion.return.mask")) c17 σ (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) c6 c11 c14 (RunStep.assign B σ "root.mask" (Expr.var "recursion.return.mask") (Env.vars σ "recursion.return.mask") (RunStep.eval_var B σ "recursion.return.mask" (vcgPost1 hcase))) (RunStep.seq B (Com.assign "root.value" (Expr.var "root.target")) c16 (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) c5 c6 c12 c13 (RunStep.assign B (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.value" (Expr.var "root.target") c4 (RunStep.eval_var B (Env.setVar σ "root.mask" (Env.vars σ "recursion.return.mask")) "root.target" (?nAX_g9578_0_0_1))) (RunStep.assign B c5 "machine.running" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g9578_0_0_2)))))) (?nAX_g9578_0_0_3)) (vcgPost2 hcase))) fun (hcase:c1) => @Exists.intro Env c3 c24 (@And.intro (Run B rootReply σ c24 ((10:Nat))) (c2 c24) (RunStep.mono B rootReply σ c24 (c10 c26) ((10:Nat)) (RunStep.ite_false B c9 c18 c21 σ c24 c26 (RunStep.cond_eq_false B σ (Expr.var "recursion.return.tag") (Expr.lit ((1:Nat))) (Env.vars σ "recursion.return.tag") ((1:Nat)) (RunStep.eval_var B σ "recursion.return.tag" vcgPost0) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9578_0_0_4)) hcase) (RunStep.seq B c20 (go ((0:Nat))) σ c23 c24 c25 c13 (RunStep.assign B σ "root.target" c19 c22 (RunStep.eval_sub B σ (Expr.var "root.target") (Expr.lit ((1:Nat))) (Env.vars σ "root.target") ((1:Nat)) (RunStep.eval_var B σ "root.target" (?nAX_g9578_0_0_5)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9578_0_0_6)) (?nAX_g9578_0_0_7))) (RunStep.assign B c23 "machine.phase" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c23 (?nAX_g9578_0_0_8))))) (?nAX_g9578_0_0_9)) (vcgPost3 hcase)) <;> try dsimp +zetaDelta at *); (all_goals try clear_value vcgPost0); (all_goals try clear_value vcgPost1); (all_goals try clear_value vcgPost2); (all_goals try clear_value vcgPost3); (all_goals try clear vcgPost3); (all_goals try clear vcgPost2); (all_goals try clear vcgPost1); (all_goals try clear vcgPost0); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9578_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9578_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals intros))
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeRootTransitions

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRootTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

def RootStable (B:ℕ) (Q:Env→ Prop):Prop:=
  ∀ (σ τ:Env) (t:ℕ) (c:Com),c∈[rootTarget,rootReply]→ Run B c σ τ t→ Q σ→ Q τ

def Attempts {n:ℕ} (B:ℕ) (cfg:Config) (Q:Env→ Prop)
    (attempt:ℕ→ Option (Finset (Fin n))) (fuel S K:ℕ):Prop:=
  ∀ k,0< k→ k≤ n→ ∀ σ,Q σ→ σ.vars "node.k"=k→ σ.vars "recursion.fuel"=fuel→
    σ.vars "root.target"=k→ σ.vars "root.fuel"=fuel→
    σ.vars "machine.running"=1→ σ.vars "machine.phase"=1→
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ∧ steps≤ S∧ total≤ K∧ Q τ∧
      τ.vars "root.target"=k∧ τ.vars "root.fuel"=fuel∧ τ.vars "machine.running"=1∧
      τ.vars "machine.phase"=15∧ NativeTargetDriver.Reply (attempt k) τ

theorem search_segment {n:ℕ} (B:ℕ) (cfg:Config) (Q:Env→ Prop)
    (attempt:ℕ→ Option (Finset (Fin n))) (fuel S K:ℕ)
    (hB:n+fuel+20< B) (hm:2^n< B) (hstable:RootStable B Q)
    (hattempt:Attempts B cfg Q attempt fuel S K) (k:ℕ) (hk:k≤ n):
    ∀ σ,Q σ→ σ.vars "root.target"=k→ σ.vars "root.fuel"=fuel→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=0→
      ∃ τ steps total,Segment B (phases cfg) steps total σ τ∧
        steps≤(S+2)*k+1∧ total≤(K+20)*k+10∧ Q τ∧ Answer (TargetSearch.search attempt k) τ:=by
  induction k with
  | zero =>
    intro σ hQ ht hf hr hp
    obtain ⟨τ,rr,p⟩:=NativeRootTransitions.target_zero_spec B (by omega) σ ht
    have trace:Segment B (phases cfg) 1 10 σ τ:=
      phase hr ⟨0,by rw [phases_length]; decide⟩ hp rr
    refine ⟨τ,1,10,trace,by omega,by omega,hstable σ τ 10 rootTarget (by simp) rr hQ,?_⟩
    simpa only [Answer,TargetSearch.search,mask_empty] using p
  | succ k ih =>
    intro σ hQ ht hf hr hp
    obtain ⟨ν,r0,p0⟩:=NativeRootTransitions.target_positive_spec B (k+1) fuel (by omega) (by omega) σ ⟨ht,hf⟩
    have first:Segment B (phases cfg) 1 10 σ ν:=
      phase hr ⟨0,by rw [phases_length]; decide⟩ hp r0
    have hQν:=hstable σ ν 10 rootTarget (by simp) r0 hQ
    have htν:=(r0.frame_var "root.target" (by decide)).trans ht
    have hfν:=(r0.frame_var "root.fuel" (by decide)).trans hf
    have hrν:=p0.2.2.2.trans hr
    obtain ⟨μ,s,t,middle,hs,hcost,hQμ,htμ,hfμ,hrμ,hpμ,hreply⟩:=
      hattempt (k+1) (by omega) hk ν hQν p0.1 p0.2.1 htν hfν hrν p0.2.2.1
    cases ha:attempt (k+1) with
    | none =>
      have htag:μ.vars "recursion.return.tag"=0:=by simpa only [ha,NativeTargetDriver.Reply] using hreply
      obtain ⟨ρ,r1,p1⟩:=NativeRootTransitions.reply_none_spec B k (by omega) μ ⟨htag,htμ⟩
      have reply:Segment B (phases cfg) 1 10 μ ρ:=
        phase hrμ ⟨15,by rw [phases_length]; decide⟩ hpμ r1
      have hQρ:=hstable μ ρ 10 rootReply (by simp) r1 hQμ
      have hfρ:=(r1.frame_var "root.fuel" (by decide)).trans hfμ
      obtain ⟨τ,s',t',rest,hs',ht',hQτ,hanswer⟩:=ih (by omega) ρ hQρ p1.1 hfρ (p1.2.2.trans hrμ) p1.2.1
      have trace:=NativeMachineSegment.append (NativeMachineSegment.append (NativeMachineSegment.append first middle) reply) rest
      refine ⟨τ,1+s+1+s',10+t+10+t',trace,by nlinarith only [hs,hs'],by nlinarith only [hcost,ht'],hQτ,?_⟩
      simpa only [TargetSearch.search,ha] using hanswer
    | some I =>
      have htag:NativeTargetDriver.Reply (some I) μ:=by simpa only [ha] using hreply
      obtain ⟨τ,r1,p1⟩:=NativeRootTransitions.reply_some_spec B (k+1) I (by omega) hm μ ⟨htag,htμ⟩
      have reply:Segment B (phases cfg) 1 10 μ τ:=
        phase hrμ ⟨15,by rw [phases_length]; decide⟩ hpμ r1
      have trace:=NativeMachineSegment.append (NativeMachineSegment.append first middle) reply
      refine ⟨τ,1+s+1,10+t+10,trace,by nlinarith only [hs],by nlinarith only [hcost],
        hstable μ τ 10 rootReply (by simp) r1 hQμ,?_⟩
      simpa only [Answer,TargetSearch.search,ha] using p1

theorem driver_spec {n:ℕ} (B:ℕ) (cfg:Config) (Q:Env→ Prop)
    (attempt:ℕ→ Option (Finset (Fin n))) (fuel S K:ℕ)
    (hB:n+fuel+20< B) (hm:2^n< B) (hstable:RootStable B Q)
    (hattempt:Attempts B cfg Q attempt fuel S K):
    Spec B (fun σ => Q σ∧ σ.vars "root.target"=n∧ σ.vars "root.fuel"=fuel∧
      σ.vars "machine.running"=1∧ σ.vars "machine.phase"=0)
      (NativeMachineTrace.driver (phases cfg))
      (fun _ τ => Q τ∧ Answer (TargetSearch.search attempt n) τ)
      ((K+20+68*(S+2))*n+82):=by
  rintro σ ⟨hQ,ht,hf,hr,hp⟩
  obtain ⟨τ,s,t,trace,hs,hcost,hQτ,answer⟩:=search_segment B cfg Q attempt fuel S K hB hm hstable hattempt n
    (by rfl) σ hQ ht hf hr hp
  have rr:=NativeCoreMachine.driver_run trace answer.2.2 (by omega)
  exact ⟨τ,rr.mono (by nlinarith only [hs,hcost]),hQτ,answer⟩

end Lax263307Proofs.NativeRootTrace

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCoreExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

theorem frame {n B D S v t:ℕ} {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent:String→ ℕ} {σ τ:Env} {c:Com} (rr:Run B c σ τ t)
    (hq:Root B D S v cfg G extent σ)
    (hv:∀ s∈NativeNodeProtocol.scalars,s∉c.wvars)
    (hn:"graph.n"∉c.wvars) (hs:"recursion.frames"∉c.warrs) (hg:"search.graph"∉c.warrs):
    Root B D S v cfg G extent τ:=
  ⟨NativeNodeProtocol.frame rr hq.1 hv hs,(rr.frame_var _ hn).trans hq.2.1,
    by simpa only [Prefix,rr.frame_arr "search.graph" hg] using hq.2.2⟩

theorem stable {n B D S v:ℕ} (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent:String→ ℕ):NativeRootTrace.RootStable B (Root B D S v cfg G extent):=by
  intro σ τ t c hc rr hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl <;> exact frame rr hq (by decide) (by decide) (by decide) (by decide)

theorem attempts {n:ℕ} (D fuel S v w nodeSteps nodeTime:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow:List ℕ→ List ℕ)
    (extent:String→ ℕ) (eligible:Eligible) (hB:16<2^w)
    (hroot:∀ k,0< k→ k≤ n→ eligible fuel n G k 0)
    (execution:Executes (2^w) D fuel S v nodeSteps nodeTime cfg lp flow extent eligible):
    NativeRootTrace.Attempts (2^w) cfg (Root (2^w) D S v cfg G extent)
      (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) fuel (nodeSteps+1) (nodeTime+6):=by
  intro k hk hkn σ hq htarget hdepth hrt hrf hr hp
  obtain ⟨μ,s,t,first,hs,ht,answer,protocolμ,rootμ,graphμ⟩:=execution n G k [] σ (hroot k hk hkn)
    ⟨hq.1,hq.2.1,hq.2.2,htarget,hdepth⟩ hr hp
  obtain ⟨τ,last,eqτ,runningτ,phaseτ,replyτ⟩:=NativeReturnTrace.root_segment (2^w) cfg
    (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) hB μ
    (by simpa using protocolμ.cursor) answer
  have rr:Run (2^w) (go 15) μ τ 2:=by
    rw [eqτ]
    exact Run.assign (evalB_lit (by omega))
  have rootτ:=rootμ.trans (root_frame rr (by decide) (by decide))
  exact ⟨τ,s+1,t+6,NativeMachineSegment.append first last,by omega,by omega,
    frame rr ⟨protocolμ,graphμ⟩ (by decide) (by decide) (by decide) (by decide),
    rootτ.1.trans hrt,rootτ.2.trans hrf,runningτ,phaseτ,replyτ⟩

theorem command_spec {n:ℕ} (D fuel S v w localSteps localTime branches:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow:List ℕ→ List ℕ)
    (extent:String→ ℕ) (eligible:Eligible)
    (resources:NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible)
    (hroot:∀ k,0< k→ k≤ n→ eligible fuel n G k 0)
    (hframe:S*(frameArrays cfg).length+(frameScalars cfg).length+S+(frameArrays cfg).length+10<2^w)
    (hB:n+fuel+20<2^w) (hm:2^n<2^w):
    let NS:=NativeRecursionBudget.work localSteps branches fuel
    let NT:=NativeRecursionBudget.work localTime branches fuel
    Spec (2^w) (Input (2^w) D fuel S v G extent) (NativeCoreMachine.command cfg)
      (fun _ τ => Root (2^w) D S v cfg G extent τ∧
        NativeRootTrace.Answer (TargetSearch.search (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) n) τ)
      ((NT+26+68*(NS+3))*n+98):=by
  dsimp only
  let NS:=NativeRecursionBudget.work localSteps branches fuel
  let NT:=NativeRecursionBudget.work localTime branches fuel
  have runs:=NativeNodeExecution.executes D S v w localSteps localTime branches cfg lp flow extent eligible resources fuel
  have attempts:=attempts D fuel S v w NS NT cfg G lp flow extent eligible (by omega) hroot runs
  have driver:=NativeRootTrace.driver_spec (2^w) cfg (Root (2^w) D S v cfg G extent)
    (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) fuel (NS+1) (NT+6) hB hm (stable cfg G extent) attempts
  intro σ hi
  obtain ⟨ν,r1,frameν⟩:=NativeRootTransitions.frame_size_spec (2^w) S cfg hframe σ hi.stride
  obtain ⟨μ,r2,initμ⟩:=NativeRootTransitions.initialize_spec (2^w) n fuel (by omega) ν
    ⟨(r1.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.graph.1,(r1.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.fuel⟩
  have qμ:Root (2^w) D S v cfg G extent μ:=by
    refine ⟨⟨NativeStateBounds.run (r1.seq r2) hi.bounded,?_,by simp [Prefix],by simpa using initμ.2.2.1,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.stride,(r2.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans frameν,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.width,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.accuracy⟩,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.graph.1,?_⟩
    · intro a; rw [RamFrames.run_array_length (r1.seq r2)]; exact hi.lengths a
    · simpa only [Prefix,(r1.seq r2).frame_arr "search.graph" (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])] using hi.graph.2
  obtain ⟨τ,r3,post⟩:=driver μ ⟨qμ,initμ.1,initμ.2.1,initμ.2.2.2.1,initμ.2.2.2.2⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,post⟩
  dsimp only [NS,NT]
  ring_nf
  omega

end Lax263307Proofs.NativeCoreExecution

end

theorem solution:∀ {n:ℕ} (D fuel S v w localSteps localTime branches:ℕ) (cfg:Lax263307Proofs.NativeCoreMachine.Config)
  (G:SimpleGraph (Fin n)) [inst:DecidableRel G.Adj] (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ)
  (eligible:Lax263307Proofs.NativeNodeProtocol.Eligible)
  (resources:
    Lax263307Proofs.NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible),
  (∀ (k:ℕ),0 < k→ k≤ n→ eligible fuel n G k 0)→
    S * (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length +
                (Lax263307Proofs.NativeCoreMachine.frameScalars cfg).length +
              S +
            (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length +
          10 <
        2 ^ w→
      n + fuel + 20 < 2 ^ w→
        2 ^ n < 2 ^ w→
          have NS:=Lax263307Proofs.NativeRecursionBudget.work localSteps branches fuel;
          have NT:=Lax263307Proofs.NativeRecursionBudget.work localTime branches fuel;
          Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax263307Proofs.NativeCoreExecution.Input (2 ^ w) D fuel S v G extent)
            (Lax263307Proofs.NativeCoreMachine.command cfg)
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeCoreExecution.Root (2 ^ w) D S v cfg G extent τ∧
                Lax263307Proofs.NativeRootTrace.Answer
                  (Lax263307.TargetSearch.search
                    (Lax263307.RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) n)
                  τ)
            ((NT + 26 + 68 * (NS + 3)) * n + 98):= @Lax263307Proofs.NativeCoreExecution.command_spec
