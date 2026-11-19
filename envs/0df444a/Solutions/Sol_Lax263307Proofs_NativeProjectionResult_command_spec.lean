-- Prove2me | solution 1 for Lax263307Proofs.NativeProjectionResult.command_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:08:55.948214+00:00
-- url     : https://prove2.me/submissions/1936e454-7a63-42af-a3f8-88c5432a3a03

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces

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

def _root_.Lax808846Proofs.Imp.Com.NoWrite:Com→ Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite∧ d.NoWrite
  | .ite _ c d => c.NoWrite∧ d.NoWrite
  | .while _ c => c.NoWrite

theorem _root_.Lax808846Proofs.Imp.BigStep.out_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k):c.NoWrite→ σ'.out=σ.out:=by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2,ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc,ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.NoWrite):σ'.out=σ.out:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.out_eq hc

end Lax808846Proofs.Reasoning

end

section

namespace Lax808846Proofs.Imp

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

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

theorem _root_.Lax808846Proofs.Imp.BigStep.inp_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) (hr:¬ c.reads):σ'.inp=σ.inp:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads,not_or] at hr
      rw [ih' hr.2,ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr),ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

theorem Run.frame_inp {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hr:¬ c.reads):σ'.inp=σ.inp:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.inp_eq hr

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

theorem Spec.frame (h:Spec B P c Q K):
    Spec B P c (fun σ σ' => Q σ σ'∧
      (∀ y,y∉ c.wvars→ σ'.vars y=σ.vars y)∧
      (∀ a,a∉ c.warrs→ σ'.arrs a=σ.arrs a)∧
      (¬ c.reads→ σ'.inp=σ.inp)∧
      (c.NoWrite→ σ'.out=σ.out)) K:=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr,hq,fun y hy => hr.frame_var y hy,fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc,fun hc => hr.out_eq hc⟩

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

namespace Lax455465Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem gcdStep_spec (B a b:ℕ) (ha:a < B) (hb:b < B):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdStep
      (fun _ σ' => σ'.vars "gcd.a"=b∧ σ'.vars "gcd.b"=a % b) 12:=by
  rintro σ ⟨hsa,hsb⟩
  have hdiv:a / b < B:=(Nat.div_le_self a b).trans_lt ha
  have hmul:a / b * b < B:=(Nat.div_mul_le_self a b).trans_lt ha
  have hsub:a - a / b * b < B:=(Nat.sub_le _ _).trans_lt ha
  (expose_names;
    (refine let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a b; let c1:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "gcd.a") b) (@Eq Nat (Env.vars σ' "gcd.b") c0)) σ; let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "gcd.a") (Env.vars σ "gcd.b"); let c3:Nat:=Nat.mul c2 (Env.vars σ "gcd.b"); let c4:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "gcd.a") c3; let c5:Env:=Env.setVar σ "gcd.t" c4; let c6:Nat:=Env.vars c5 "gcd.b"; let c7:Env:=Env.setVar c5 "gcd.a" c6; let c8:Nat:=Env.vars c7 "gcd.t"; let c9:Env:=Env.setVar c7 "gcd.b" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.mul (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b"); let c13:Expr:=Expr.sub (Expr.var "gcd.a") c12; let c14:Nat:=c11 (Expr.size c13); let c15:Nat:=c11 (Expr.size (Expr.var "gcd.b")); let c16:Nat:=c11 (Expr.size (Expr.var "gcd.t")); let c17:Nat:=c10 c15 c16; let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B gcdStep σ σ' ((12:Nat))) (c1 σ')) c9 (@And.intro (Run B gcdStep σ c9 ((12:Nat))) (c1 c9) (RunStep.mono B gcdStep σ c9 (c10 c14 c17) ((12:Nat)) (RunStep.seq B (Com.assign "gcd.t" c13) (Com.seq (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t"))) σ c5 c9 c14 c17 (RunStep.assign B σ "gcd.t" c13 c4 (RunStep.eval_sub B σ (Expr.var "gcd.a") c12 (Env.vars σ "gcd.a") c3 (RunStep.eval_var B σ "gcd.a" (?nAX_g5407_0_0_0)) (RunStep.eval_mul B σ (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b") c2 (Env.vars σ "gcd.b") (RunStep.eval_div B σ (Expr.var "gcd.a") (Expr.var "gcd.b") (Env.vars σ "gcd.a") (Env.vars σ "gcd.b") (RunStep.eval_var B σ "gcd.a" (?nAX_g5407_0_0_1)) (RunStep.eval_var B σ "gcd.b" (?nAX_g5407_0_0_2)) ?_) (RunStep.eval_var B σ "gcd.b" (?nAX_g5407_0_0_3)) ?_) (?nAX_g5407_0_0_4))) (RunStep.seq B (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t")) c5 c7 c9 c15 c16 (RunStep.assign B c5 "gcd.a" (Expr.var "gcd.b") c6 (RunStep.eval_var B c5 "gcd.b" (?nAX_g5407_0_0_5))) (RunStep.assign B c7 "gcd.b" (Expr.var "gcd.t") c8 (RunStep.eval_var B c7 "gcd.t" (?nAX_g5407_0_0_6))))) (?nAX_g5407_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5407_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

theorem remainder_half (d r:ℕ) (hr:0 < r) (hrd:r < d):d % r≤ d / 2:=by
  by_cases h:r≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le,Nat.mod_eq_of_lt (by omega)]
    omega

theorem size_half_lt (b:ℕ) (hb:0 < b):(b / 2).size < b.size:=by
  have hs:0 < b.size:=Nat.size_pos.mpr hb
  have hp:b < 2 ^ b.size:=Nat.lt_size_self b
  have he:2 ^ b.size=2 * 2 ^ (b.size - 1):=by
    calc
      _=2 ^ ((b.size - 1) + 1):=congrArg (fun k => 2 ^ k) (by omega)
      _=_:=by rw [pow_succ]; omega
  have hhalf:b / 2 < 2 ^ (b.size - 1):=by omega
  have h:=Nat.size_le.mpr hhalf
  omega

theorem gcd_swap_mod (a b:ℕ):Nat.gcd b (a % b)=Nat.gcd a b:=by
  rw [Nat.gcd_comm b _, ← Nat.gcd_rec,Nat.gcd_comm]

theorem gcdDoubleStep_spec (B M a b:ℕ) (hM:M < B)
    (ha:a≤ M) (hb:b≤ M) (hbpos:0 < b):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdDoubleStep
      (fun _ σ' => σ'.vars "gcd.a" ≤ M∧ σ'.vars "gcd.b" ≤ M∧
        Nat.gcd (σ'.vars "gcd.a") (σ'.vars "gcd.b")=Nat.gcd a b∧
        (σ'.vars "gcd.b").size < b.size) 32:=by
  intro σ hσ
  obtain ⟨τ,hrun,hτa,hτb⟩:=(gcdStep_spec B a b (ha.trans_lt hM) (hb.trans_lt hM)) σ hσ
  have hrlt:a % b < b:=Nat.mod_lt a hbpos
  have hrB:a % b < B:=hrlt.trans (hb.trans_lt hM)
  have h0B:0 < B:=(Nat.zero_le M).trans_lt hM
  by_cases hr0:a % b=0
  · have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some false:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb,hr0]
      rfl
    refine ⟨τ, (hrun.seq (Run.ite_false hc Run.skip)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hτa,hτb]
    refine ⟨hb,hrlt.le.trans hb,gcd_swap_mod a b, ?_⟩
    rw [hr0]
    exact Nat.size_pos.mpr hbpos
  · have hrpos:0 < a % b:=Nat.pos_of_ne_zero hr0
    have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some true:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb]
      simp [hrpos]
    obtain ⟨ν,hrν,hνa,hνb⟩:=
      (gcdStep_spec B b (a % b) (hb.trans_lt hM) hrB) τ ⟨hτa,hτb⟩
    refine ⟨ν, (hrun.seq (Run.ite_true hc hrν)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hνa,hνb]
    refine ⟨hrlt.le.trans hb, (Nat.mod_lt b hrpos).le.trans (hrlt.le.trans hb),
      (gcd_swap_mod b (a % b)).trans (gcd_swap_mod a b), ?_⟩
    exact (Nat.size_le_size (remainder_half b (a % b) hrpos hrlt)).trans_lt
      (size_half_lt b hbpos)

theorem gcdLoop_spec (B M a b:ℕ) (hM:M < B) (ha:a≤ M) (hb:b≤ M):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => σ'.vars "gcd.a"=Nat.gcd a b∧ σ'.vars "gcd.b"=0)
      (36 * b.size + 4):=by
  let I:=fun σ:Env => σ.vars "gcd.a" ≤ M∧ σ.vars "gcd.b" ≤ M∧
    Nat.gcd (σ.vars "gcd.a") (σ.vars "gcd.b")=Nat.gcd a b
  have hloop:Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => I σ'∧
        (Cond.lt (.lit 0) (.var "gcd.b")).evalB B σ'=some false)
      (36 * b.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "gcd.b").size) 32
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
        (evalB_var (hI.2.1.trans_lt hM))⟩
    · rintro σ ⟨hI,hc⟩
      have hbpos:0 < σ.vars "gcd.b" :=by
        rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
          (evalB_var (hI.2.1.trans_lt hM))] at hc
        simpa using hc
      obtain ⟨τ,hr,hτa,hτb,hτg,hτs⟩:=
        gcdDoubleStep_spec B M _ _ hM hI.1 hI.2.1 hbpos σ ⟨rfl,rfl⟩
      exact ⟨τ,hr, ⟨hτa,hτb,hτg.trans hI.2.2⟩,hτs⟩
    · rintro σ ⟨hσa,hσb⟩
      exact ⟨hσa ▸ ha,hσb ▸ hb,by rw [hσa,hσb]⟩
    · rintro σ ⟨_,hσb⟩
      simp [hσb]
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hb0:τ.vars "gcd.b"=0:=by
    rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
      (evalB_var (hI.2.1.trans_lt hM))] at hc
    simpa using hc
  exact ⟨by simpa [hb0] using hI.2.2,hb0⟩

theorem normalizeFraction_spec (B n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d) (36 * d.size + 16):=by
  have hM:max n d < B:=max_lt hn hd
  have hg:Nat.gcd n d < B:=(Nat.gcd_le_right n hdpos).trans_lt hd
  have hnDiv:n / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hn
  have hdDiv:d / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hd
  have hs:=(gcdLoop_spec B (max n d) n d hM (le_max_left _ _) (le_max_right _ _)).frame
  rintro σ ⟨hσn,hσd⟩
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" c0; let c2:Env→ Nat→ Prop:=Run B gcdLoop c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 (Nat.mul ((36:Nat)) (Nat.size d)); let c5:Nat:=c4 ((4:Nat)); let c6:String→ Nat:=Env.vars c1; let c7:List Nat:=Env.inp c1; let c8:List Nat:=Env.out c1; let c9:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') c8))))); let c10:Nat:=c4 ((16:Nat)); let c11:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c12:Nat:=c11 n (Nat.gcd n d); let c13:Nat:=c11 d (Nat.gcd n d); let c14:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "rat.n") c12) (@Eq Nat (Env.vars σ' "rat.d") c13)) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B normalizeFraction σ σ' c10) (c14 σ'); let c16:Prop:= @Exists Env c15; let c17:Nat→ Nat:=c3 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.var "rat.n")); let c19:Nat:=c17 (Expr.size (Expr.var "rat.d")); let c20:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a"))); let c21:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a"))); let c22:Nat:=c3 c20 c21; let c23:Nat:=c3 c5 c22; let c24:Nat:=c3 c19 c23; let c25:Com:=Com.assign "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")); let c26:Com:=Com.assign "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")); let c27:Com:=Com.seq c25 c26; let c28:Com:=Com.seq gcdLoop c27; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c16) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "gcd.a") n) (@Eq Nat (Env.vars σ_1 "gcd.b") d)) gcdLoop (fun (σ_1 σ':Env) => And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (Env.vars σ_1 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs σ_1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') (Env.inp σ_1)) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') (Env.out σ_1)))))) c5 hs c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))); let c1_1:Nat:=c11 (Env.vars w "rat.n") (Env.vars w "gcd.a"); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:String→ Nat:=Env.vars c2_1; let c4_1:Nat:=c3_1 "rat.d"; let c5_1:Nat:=c3_1 "gcd.a"; let c6_1:Nat:=c11 c4_1 c5_1; let c7_1:Env:=Env.setVar c2_1 "rat.d" c6_1; let c8_1:String→ Nat:=Env.vars c7_1; @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c16) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c15 c7_1 (@And.intro (Run B normalizeFraction σ c7_1 c10) (c14 c7_1) (RunStep.mono B normalizeFraction σ c7_1 (c3 c18 c24) c10 (RunStep.seq B (Com.assign "gcd.a" (Expr.var "rat.n")) (Com.seq (Com.assign "gcd.b" (Expr.var "rat.d")) c28) σ (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c7_1 c18 c24 (RunStep.assign B σ "gcd.a" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g5416_0_0_0))) (RunStep.seq B (Com.assign "gcd.b" (Expr.var "rat.d")) c28 (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c1 c7_1 c19 c23 (RunStep.assign B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d" (?nAX_g5416_0_0_1))) (RunStep.seq B gcdLoop c27 c1 w c7_1 c5 c22 left (RunStep.seq B c25 c26 w c2_1 c7_1 c20 c21 (RunStep.assign B w "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")) c1_1 (RunStep.eval_div B w (Expr.var "rat.n") (Expr.var "gcd.a") (Env.vars w "rat.n") (Env.vars w "gcd.a") (RunStep.eval_var B w "rat.n" ?_) (RunStep.eval_var B w "gcd.a" (?nAX_g5416_0_0_2)) ?_)) (RunStep.assign B c2_1 "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")) c6_1 (RunStep.eval_div B c2_1 (Expr.var "rat.d") (Expr.var "gcd.a") c4_1 c5_1 (RunStep.eval_var B c2_1 "rat.d" ?_) (RunStep.eval_var B c2_1 "gcd.a" (?nAX_g5416_0_0_3)) ?_)))))) (?nAX_g5416_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5416_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [gcdLoop,gcdDoubleStep,gcdStep,Com.wvars]

end Lax455465Proofs.RamArithmetic

end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

theorem fractionValue_reduce (s n d:ℕ):
    fractionValue s (n / Nat.gcd n d) (d / Nat.gcd n d)=fractionValue s n d:=by
  have h:((n / Nat.gcd n d:ℕ):ℚ) / ((d / Nat.gcd n d:ℕ):ℚ)=(n:ℚ) / d:=
    Nat.cast_div_div_div_cancel_right (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold fractionValue
  split_ifs
  · simpa only [neg_div] using congrArg Neg.neg h
  · exact h

theorem normalizeFraction_signed_spec (B s n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d∧ σ'.vars "rat.s"=s) (36 * d.size + 16):=by
  rintro σ ⟨hσn,hσd,hσs⟩
  obtain ⟨τ,hr,hτn,hτd⟩:=normalizeFraction_spec B n d hn hd hdpos σ ⟨hσn,hσd⟩
  have hτs:=hr.frame_var "rat.s" (by decide)
  exact ⟨τ,hr,hτn,hτd,hτs.trans hσs⟩

theorem fractionValue_num_den (s n d:ℕ) (hd:0 < d):
    (fractionValue s n d).num.natAbs=n / Nat.gcd n d∧
      (fractionValue s n d).den=d / Nat.gcd n d:=by
  have h:(((n:ℚ) / d).num.natAbs=n / Nat.gcd n d)∧
      ((n:ℚ) / d).den=d / Nat.gcd n d:=by
    have he:(n:ℚ) / d=mkRat (n:ℤ) d:=by simp [Rat.mkRat_eq_div]
    rw [he]
    simp [Rat.num_mkRat,Rat.den_mkRat,ne_of_gt hd,
      Int.natAbs_ediv_of_nonneg (by positivity:(0:ℤ)≤ n),Nat.gcd_comm]
  unfold fractionValue
  split_ifs
  · simpa only [neg_div,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using h
  · exact h

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

theorem normalizeFraction_output_spec (B s n d:ℕ) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => FractionOutput (fractionValue s n d) σ')
      (36 * d.size + 16):=by
  apply (normalizeFraction_signed_spec B s n d hn hd hdpos).post
  rintro σ τ _ ⟨hτn,hτd,hτs⟩
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hτs,hτn,hτd]; exact fractionValue_reduce s n d,
    hτn.trans hnum.symm,hτd.trans hden.symm,hτs ▸ hs⟩

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

def sumNumerator (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then n₁ * d₂ + n₂ * d₁
  else if n₁ * d₂ < n₂ * d₁ then n₂ * d₁ - n₁ * d₂ else n₁ * d₂ - n₂ * d₁

def sumSign (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then s₁ else if n₁ * d₂ < n₂ * d₁ then s₂ else s₁

theorem fractionValue_sum (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    fractionValue (sumSign s₁ n₁ d₁ s₂ n₂ d₂) (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂:=by
  have hd₁q:(d₁:ℚ) ≠ 0:=by positivity
  have hd₂q:(d₂:ℚ) ≠ 0:=by positivity
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
    by_cases h:n₁ * d₂ < n₂ * d₁
  all_goals first
    | (have hu:n₁ * d₂≤ n₂ * d₁:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hu]
       field_simp <;> ring)
    | (have hv:n₂ * d₁≤ n₁ * d₂:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hv]
       field_simp <;> ring)

set_option maxHeartbeats 0 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96):=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have hu:n₁ * d₂≤ M * M:=Nat.mul_le_mul hn₁ hd₂
  have hv:n₂ * d₁≤ M * M:=Nat.mul_le_mul hn₂ hd₁
  have huB:n₁ * d₂ < B:=hu.trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=hv.trans_lt (by nlinarith)
  have huvB:n₁ * d₂ + n₂ * d₁ < B:=by nlinarith
  have hdd:d₁ * d₂ < B:=(Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have hnB:sumNumerator s₁ n₁ d₁ s₂ n₂ d₂ < B:=by
    unfold sumNumerator
    split_ifs <;> omega
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  have hss:sumSign s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by unfold sumSign; split_ifs <;> omega
  have hn:=normalizeFraction_output_spec B (sumSign s₁ n₁ d₁ s₂ n₂ d₂)
    (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) hss hnB hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  have hsum:=fractionValue_sum s₁ n₁ d₁ s₂ n₂ d₂ hs₁ hs₂ hd₁pos hd₂pos
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "sum.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "sum.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.d"; let c10:Nat:=c8 "right.d"; let c11:Nat:=c0 c9 c10; let c12:Env:=Env.setVar c7 "rat.d" c11; let c13:String→ Nat:=Env.vars c12; let c14:Nat:=c13 "left.s"; let c15:Nat:=c13 "right.s"; let c16:Prop:= @Eq Nat c14 c15; let c17:Prop:=Not c16; let c18:Nat→ Nat→ Nat:=Nat.add; let c19:Nat:=c0 d₁ d₂; let c20:Nat→ Nat:=c18 (c0 ((36:Nat)) (Nat.size c19)); let c21:Nat:=c20 ((96:Nat)); let c22:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (fractionValue s₁ n₁ d₁) (fractionValue s₂ n₂ d₂)); let c23:Env→ Prop:=(fun (x σ':Env) => c22 σ') σ; let c24:Env→ Prop:=fun (σ':Env) => And (Run B addFraction σ σ' c21) (c23 σ'); let c25:Prop:= @Exists Env c24; let c26:Nat→ Env:=Env.setVar c12 "rat.n"; let c27:Nat:=c13 "sum.u"; let c28:Nat:=c13 "sum.v"; let c29:Nat:=c18 c27 c28; let c30:Env:=c26 c29; let c31:Nat:=Env.vars c30 "left.s"; let c32:Env:=Env.setVar c30 "rat.s" c31; let c33:Env→ Nat→ Prop:=Run B normalizeFraction c32; let c34:Nat:=c20 ((16:Nat)); let c35:Nat:=sumSign s₁ n₁ d₁ s₂ n₂ d₂; let c36:Nat:=sumNumerator s₁ n₁ d₁ s₂ n₂ d₂; let c37:Env→ Prop:=FractionOutput (fractionValue c35 c36 c19); let c38:Env→ Prop:=fun (σ':Env) => And (c33 σ' c34) (c37 σ'); let c39:String→ Nat:=Env.vars c32; let c40:Nat→ Nat:=c18 ((1:Nat)); let c41:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c42:Nat→ Nat:=c18 c41; let c43:Nat:=c40 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c44:Nat→ Nat:=c18 c43; let c45:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.d") (Expr.var "right.d"))); let c46:Nat→ Nat:=c18 c45; let c47:Nat→ Nat:=c18 (c40 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c48:Nat:=c40 (Expr.size (Expr.add (Expr.var "sum.u") (Expr.var "sum.v"))); let c49:Nat:=c40 (Expr.size (Expr.var "left.s")); let c50:Nat:=c18 c48 c49; let c51:Nat:=c47 c50; let c52:Nat:=c18 c51 c34; let c53:Nat:=c46 c52; let c54:Nat:=c44 c53; let c55:Com:=Com.assign "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c56:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")); let c57:Com:=Com.assign "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")); let c58:Com:=Com.seq c57 (Com.assign "rat.s" (Expr.var "left.s")); let c59:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")); let c60:Com:=Com.seq c59 (Com.assign "rat.s" (Expr.var "right.s")); let c61:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")); let c62:Com:=Com.seq c61 (Com.assign "rat.s" (Expr.var "left.s")); let c63:Com:=Com.ite (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62; let c64:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63; let c65:Com:=Com.seq c64 normalizeFraction; let c66:Com:=Com.seq c56 c65; let c67:Nat→ Prop:=Nat.lt c27; let c68:Prop:=c67 c28; let c69:Prop:=Not c68; let c70:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c71:Nat:=c70 c28 c27; let c72:Env:=c26 c71; let c73:Nat:=Env.vars c72 "right.s"; let c74:Env:=Env.setVar c72 "rat.s" c73; let c75:Env→ Nat→ Prop:=Run B normalizeFraction c74; let c76:Env→ Prop:=fun (σ':Env) => And (c75 σ' c34) (c37 σ'); let c77:String→ Nat:=Env.vars c74; let c78:Nat→ Nat:=c18 (c40 (Cond.size (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")))); let c79:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u"))); let c80:Nat:=c40 (Expr.size (Expr.var "right.s")); let c81:Nat:=c18 c79 c80; let c82:Nat:=c78 c81; let c83:Nat:=c47 c82; let c84:Nat:=c18 c83 c34; let c85:Nat:=c46 c84; let c86:Nat:=c44 c85; let c87:Nat:=c70 c27 c28; let c88:Env:=c26 c87; let c89:Nat:=Env.vars c88 "left.s"; let c90:Env:=Env.setVar c88 "rat.s" c89; let c91:Env→ Nat→ Prop:=Run B normalizeFraction c90; let c92:Env→ Prop:=fun (σ':Env) => And (c91 σ' c34) (c37 σ'); let c93:String→ Nat:=Env.vars c90; let c94:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v"))); let c95:Nat:=c18 c94 c49; let c96:Nat:=c78 c95; let c97:Nat:=c47 c96; let c98:Nat:=c18 c97 c34; let c99:Nat:=c46 c98; let c100:Nat:=c44 c99; @Or.casesOn c16 c17 (fun (x:Or c16 c17) => c25) (Classical.em c16) (fun (hcase:c16) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c32 ?_) fun (w:Env) (h:And (c33 w c34) (c37 w)) => @And.casesOn (c33 w c34) (c37 w) (fun (x:And (c33 w c34) (c37 w)) => c25) h fun (left:c33 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c54) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c54 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5433_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g5433_0_0_1)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c53 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5433_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g5433_0_0_3)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c52 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g5433_0_0_4)) (RunStep.eval_var B c7 "right.d" (?nAX_g5433_0_0_5)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c32 w c51 c34 (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c32 c50 (RunStep.cond_eq_true B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g5433_0_0_6)) (RunStep.eval_var B c12 "right.s" (?nAX_g5433_0_0_7)) hcase) (RunStep.seq B c57 (Com.assign "rat.s" (Expr.var "left.s")) c12 c30 c32 c48 c49 (RunStep.assign B c12 "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")) c29 (RunStep.eval_add B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c30 "rat.s" (Expr.var "left.s") c31 (RunStep.eval_var B c30 "left.s" (?nAX_g5433_0_0_8))))) left)))) (?nAX_g5433_0_0_9)) ?_)) fun (hcase:c17) => @Or.casesOn c68 c69 (fun (x:Or c68 c69) => c25) (Classical.em c68) (fun (hcase_1:c68) => @Exists.casesOn Env c76 (fun (x:@Exists Env c76) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c74 ?_) fun (w:Env) (h:And (c75 w c34) (c37 w)) => @And.casesOn (c75 w c34) (c37 w) (fun (x:And (c75 w c34) (c37 w)) => c25) h fun (left:c75 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c86) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c86 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5433_0_0_10)) (RunStep.eval_var B σ "right.d" (?nAX_g5433_0_0_11)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c85 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5433_0_0_12)) (RunStep.eval_var B c2 "left.d" (?nAX_g5433_0_0_13)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c84 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g5433_0_0_14)) (RunStep.eval_var B c7 "right.d" (?nAX_g5433_0_0_15)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c74 w c83 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c74 c82 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g5433_0_0_16)) (RunStep.eval_var B c12 "right.s" (?nAX_g5433_0_0_17)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c74 c81 (RunStep.cond_lt_true B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c59 (Com.assign "rat.s" (Expr.var "right.s")) c12 c72 c74 c79 c80 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")) c71 (RunStep.eval_sub B c12 (Expr.var "sum.v") (Expr.var "sum.u") c28 c27 (RunStep.eval_var B c12 "sum.v" ?_) (RunStep.eval_var B c12 "sum.u" ?_) ?_)) (RunStep.assign B c72 "rat.s" (Expr.var "right.s") c73 (RunStep.eval_var B c72 "right.s" (?nAX_g5433_0_0_18)))))) left)))) (?nAX_g5433_0_0_19)) ?_)) fun (hcase_1:c69) => @Exists.casesOn Env c92 (fun (x:@Exists Env c92) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c90 ?_) fun (w:Env) (h:And (c91 w c34) (c37 w)) => @And.casesOn (c91 w c34) (c37 w) (fun (x:And (c91 w c34) (c37 w)) => c25) h fun (left:c91 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c100) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c100 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5433_0_0_20)) (RunStep.eval_var B σ "right.d" (?nAX_g5433_0_0_21)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c99 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5433_0_0_22)) (RunStep.eval_var B c2 "left.d" (?nAX_g5433_0_0_23)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c98 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g5433_0_0_24)) (RunStep.eval_var B c7 "right.d" (?nAX_g5433_0_0_25)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c90 w c97 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c90 c96 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g5433_0_0_26)) (RunStep.eval_var B c12 "right.s" (?nAX_g5433_0_0_27)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c90 c95 (RunStep.cond_lt_false B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c61 (Com.assign "rat.s" (Expr.var "left.s")) c12 c88 c90 c94 c49 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")) c87 (RunStep.eval_sub B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c88 "rat.s" (Expr.var "left.s") c89 (RunStep.eval_var B c88 "left.s" (?nAX_g5433_0_0_28)))))) left)))) (?nAX_g5433_0_0_29)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5433_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5433_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [sumNumerator,sumSign]
  all_goals try omega

end Lax455465Proofs.RamRational

end

section

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def leFlag (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then
    if s₁=1 then (if n₁ * d₂ < n₂ * d₁ then 0 else 1)
    else (if n₂ * d₁ < n₁ * d₂ then 0 else 1)
  else if s₁=1 then 1
  else if n₁=0 then (if n₂=0 then 1 else 0) else 0

theorem leFlag_le_one (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):leFlag s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by
  unfold leFlag
  split_ifs <;> omega

theorem leFlag_correct (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    leFlag s₁ n₁ d₁ s₂ n₂ d₂=1↔
      fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂:=by
  have hd₁q:(0:ℚ) < d₁:=by exact_mod_cast hd₁
  have hd₂q:(0:ℚ) < d₂:=by exact_mod_cast hd₂
  have hpos₁:(0:ℚ)≤ (n₁:ℚ) / d₁:=by positivity
  have hpos₂:(0:ℚ)≤ (n₂:ℚ) / d₂:=by positivity
  have hcross:(n₁:ℚ) / d₁≤ (n₂:ℚ) / d₂↔ n₁ * d₂≤ n₂ * d₁:=by
    rw [div_le_div_iff₀ hd₁q hd₂q]
    exact_mod_cast Iff.rfl
  have hcrossRev:(n₂:ℚ) / d₂≤ (n₁:ℚ) / d₁↔ n₂ * d₁≤ n₁ * d₂:=by
    rw [div_le_div_iff₀ hd₂q hd₁q]
    exact_mod_cast Iff.rfl
  have hzero:(n₁:ℚ) / d₁≤ -((n₂:ℚ) / d₂)↔ n₁=0∧ n₂=0:=by
    constructor
    · intro h
      have hz₁:(n₁:ℚ) / d₁=0:=by linarith
      have hz₂:(n₂:ℚ) / d₂=0:=by linarith
      simpa [div_eq_zero_iff,ne_of_gt hd₁q,ne_of_gt hd₂q] using And.intro hz₁ hz₂
    · rintro ⟨rfl,rfl⟩; simp
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl
  · simp [leFlag,fractionValue,hcross]
  · simp [leFlag,fractionValue,neg_div,hzero]
    split_ifs <;> simp_all
  · simp [leFlag,fractionValue,neg_div]
    linarith
  · simp [leFlag,fractionValue,neg_div,hcrossRev]

set_option maxHeartbeats 0 in
theorem compareFraction_flag_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le"=leFlag s₁ n₁ d₁ s₂ n₂ d₂) 40:=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have huB:n₁ * d₂ < B:=(Nat.mul_le_mul hn₁ hd₂).trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=(Nat.mul_le_mul hn₂ hd₁).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "cmp.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "cmp.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat→ Prop:= @Eq Nat c9; let c11:Nat:=c8 "right.s"; let c12:Prop:=c10 c11; let c13:Prop:=Not c12; let c14:Nat:=leFlag s₁ n₁ d₁ s₂ n₂ d₂; let c15:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "cmp.le") c14) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction σ σ' ((40:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Prop:=c10 ((1:Nat)); let c19:Prop:=Not c18; let c20:Nat:=c8 "cmp.u"; let c21:Nat→ Prop:=Nat.lt c20; let c22:Nat:=c8 "cmp.v"; let c23:Prop:=c21 c22; let c24:Prop:=Not c23; let c25:Nat→ Env:=Env.setVar c7 "cmp.le"; let c26:Env:=c25 ((0:Nat)); let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Nat:=c28 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c30:Nat→ Nat:=c27 c29; let c31:Nat:=c28 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c32:Nat→ Nat:=c27 c31; let c33:Nat→ Nat:=c27 (c28 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c34:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c35:Nat→ Nat:=c27 (c28 (Cond.size c34)); let c36:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")))); let c37:Nat:=c28 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat:=c36 c37; let c39:Nat:=c35 c38; let c40:Nat:=c33 c39; let c41:Nat:=c32 c40; let c42:Com:=Com.assign "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c43:Com→ Com→ Com:=Com.ite c34; let c44:Com:=Com.assign "cmp.le" (Expr.lit ((0:Nat))); let c45:Com:=Com.assign "cmp.le" (Expr.lit ((1:Nat))); let c46:Com:=Com.ite (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45; let c47:Com:=Com.ite (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45; let c48:Com:=c43 c46 c47; let c49:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c50:Cond:=Cond.eq (Expr.var "right.n") (Expr.lit ((0:Nat))); let c51:Com:=Com.ite c50 c45 c44; let c52:Com:=Com.ite c49 c51 c44; let c53:Com:=c43 c45 c52; let c54:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53; let c55:Nat→ Prop:=Nat.lt c22; let c56:Env:=c25 ((1:Nat)); let c57:Nat:=c28 (Expr.size (Expr.lit ((1:Nat)))); let c58:Nat:=c36 c57; let c59:Nat:=c35 c58; let c60:Nat:=c33 c59; let c61:Nat:=c32 c60; let c62:Prop:=c55 c20; let c63:Prop:=Not c62; let c64:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")))); let c65:Nat:=c64 c37; let c66:Nat:=c35 c65; let c67:Nat:=c33 c66; let c68:Nat:=c32 c67; let c69:Nat:=c64 c57; let c70:Nat:=c35 c69; let c71:Nat:=c33 c70; let c72:Nat:=c32 c71; let c73:Nat:=c35 c57; let c74:Nat:=c33 c73; let c75:Nat:=c32 c74; let c76:Nat:=c8 "left.n"; let c77:Prop:= @Eq Nat c76 ((0:Nat)); let c78:Prop:=Not c77; let c79:Nat:=c8 "right.n"; let c80:Prop:= @Eq Nat c79 ((0:Nat)); let c81:Prop:=Not c80; let c82:Nat→ Nat:=c27 (c28 (Cond.size c49)); let c83:Nat→ Nat:=c27 (c28 (Cond.size c50)); let c84:Nat:=c83 c57; let c85:Nat:=c82 c84; let c86:Nat:=c35 c85; let c87:Nat:=c33 c86; let c88:Nat:=c32 c87; let c89:Nat:=c83 c37; let c90:Nat:=c82 c89; let c91:Nat:=c35 c90; let c92:Nat:=c33 c91; let c93:Nat:=c32 c92; let c94:Nat:=c82 c37; let c95:Nat:=c35 c94; let c96:Nat:=c33 c95; let c97:Nat:=c32 c96; @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c17) (Classical.em c12) (fun (hcase:c12) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c17) (Classical.em c23) (fun (hcase_2:c23) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c41) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c41 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_1)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c40 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_3)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c39 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_5)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c26 c38 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_7)))))))) (?nAX_g5438_0_0_8)) ?_)) fun (hcase_2:c24) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c61) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c61 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_9)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_10)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c60 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_11)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_12)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c59 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_13)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_14)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c56 c58 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_15)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_16)) ?_)) fun (hcase_1:c19) => @Or.casesOn c62 c63 (fun (x:Or c62 c63) => c17) (Classical.em c62) (fun (hcase_2:c62) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c68) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c68 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_17)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_18)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c67 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_19)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_20)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c66 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_21)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_22)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c26 c65 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_23)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_24)))))))) (?nAX_g5438_0_0_25)) ?_)) fun (hcase_2:c63) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c72) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c72 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_26)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_27)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c71 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_28)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_29)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c70 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_30)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_31)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c56 c69 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_33)) ?_)) fun (hcase:c13) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c75) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c75 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_34)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_35)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c74 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_36)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_37)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c73 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_38)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_39)) hcase) (RunStep.ite_true B c34 c45 c52 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))) (?nAX_g5438_0_0_41)) ?_)) fun (hcase_1:c19) => @Or.casesOn c77 c78 (fun (x:Or c77 c78) => c17) (Classical.em c77) (fun (hcase_2:c77) => @Or.casesOn c80 c81 (fun (x:Or c80 c81) => c17) (Classical.em c80) (fun (hcase_3:c80) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c88) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c88 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_42)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_43)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c87 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_44)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_45)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c86 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_46)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_47)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c56 c85 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_48)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c56 c84 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_49)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_50)) hcase_2) (RunStep.ite_true B c50 c45 c44 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_51)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_52)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))))) (?nAX_g5438_0_0_53)) ?_)) fun (hcase_3:c81) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c93) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c93 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_54)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_55)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c92 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_56)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_57)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c91 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_58)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_59)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c90 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_60)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c26 c89 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_61)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_62)) hcase_2) (RunStep.ite_false B c50 c45 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_63)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_64)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_65))))))))) (?nAX_g5438_0_0_66)) ?_)) fun (hcase_2:c78) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c97) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c97 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_67)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_68)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c96 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_69)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_70)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c95 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_71)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_72)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c94 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_73)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B c49 c51 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_74)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_75)) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_76)))))))) (?nAX_g5438_0_0_77)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5438_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [leFlag]

theorem compareFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" ≤ 1∧
        (σ'.vars "cmp.le"=1↔ fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂)) 40:=by
  apply (compareFraction_flag_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂).post
  intro σ τ _ ht
  rw [ht]
  exact ⟨leFlag_le_one _ _ _ _ _ _,leFlag_correct _ _ _ _ _ _ hs₁ hs₂ hd₁pos hd₂pos⟩

end Lax455465Proofs.RamComparison

end

section

namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational

theorem save_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".s"≠"rat.n" ∧ name++".s"≠"rat.d" ∧ name++".n"≠"rat.d"):
    Spec B (FractionOutput q) (save name) (fun _ τ => Stored name q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars "rat.s"< B:=hs.trans_lt h1
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".s"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.s"); let c4:String:=c1 ".n"; let c5:Nat:=Env.vars c3 "rat.n"; let c6:Env:=Env.setVar c3 c4 c5; let c7:String:=c1 ".d"; let c8:Nat:=Env.vars c6 "rat.d"; let c9:Env:=Env.setVar c6 c7 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "rat.s")); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c4 (Expr.var "rat.n"); let c17:Com:=Com.assign c7 (Expr.var "rat.d"); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((6:Nat))) (c0 σ')) c9 (@And.intro (Run B (save name) σ c9 ((6:Nat))) (c0 c9) (RunStep.mono B (save name) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.s")) (Com.seq c16 c17) σ c3 c9 c12 c15 (RunStep.assign B σ c2 (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B c16 c17 c3 c6 c9 c13 c14 (RunStep.assign B c3 c4 (Expr.var "rat.n") c5 (RunStep.eval_var B c3 "rat.n" ?_)) (RunStep.assign B c6 c7 (Expr.var "rat.d") c8 (RunStep.eval_var B c6 "rat.d" ?_)))) (?nAX_g5443_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5443_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem load_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars (name++".s")< B:=hs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "rat.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "rat.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "rat.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "rat.n" c14; let c20:Com:=Com.assign "rat.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c9 (@And.intro (Run B (load name) σ c9 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c9) (RunStep.mono B (load name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "rat.s" c12 c2 (RunStep.eval_var B σ c1 hsB)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "rat.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "rat.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g5444_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

def Operands (a b:ℚ) (σ:Env):Prop:=Stored "left" a σ∧ Stored "right" b σ

theorem add_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (Operands a b) addFraction (fun _ τ => FractionOutput (a+b) τ)
      (36*(a.den*b.den).size+96):=by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩:=addFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl:fractionValue (σ.vars "left.s") a.num.natAbs a.den=a:=by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr:fractionValue (σ.vars "right.s") b.num.natAbs b.den=b:=by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

theorem compare_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (Operands a b) Lax455465Proofs.RamComparison.compareFraction
      (fun _ τ => τ.vars "cmp.le"=if a≤ b then 1 else 0) 40:=by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩:=Lax455465Proofs.RamComparison.compareFraction_spec B M
    (σ.vars "left.s") a.num.natAbs a.den (σ.vars "right.s") b.num.natAbs b.den
    hB hleft.2.2.2 hright.2.2.2 ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl:fractionValue (σ.vars "left.s") a.num.natAbs a.den=a:=by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr:fractionValue (σ.vars "right.s") b.num.natAbs b.den=b:=by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  rw [hl,hr] at ht
  refine ⟨τ,rr,?_⟩
  split_ifs with h
  · exact ht.2.mpr h
  · have hne:=mt ht.2.mp h
    have hle:=ht.1
    omega

end Lax263307Proofs.NativeSignedArithmetic

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

theorem keep_scalar {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (h:Spec B P c Q K) (x:String) (v:ℕ) (hx:x∉ c.wvars):
    Spec B (fun σ => P σ∧ σ.vars x=v) c (fun σ τ => Q σ τ∧ τ.vars x=v) K:=by
  rintro σ ⟨hp,hv⟩
  obtain ⟨τ,hr,hq⟩:=h σ hp
  exact ⟨τ,hr,hq, (hr.frame_var x hx).trans hv⟩

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem negate_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (FractionOutput q) negate (fun _ τ => FractionOutput (-q) τ) 4:=by
  rintro σ ⟨hvalue,hn,hd,hs⟩
  have hsign:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by omega
  rcases hsign with hs₀ | hs₁
  · (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negate σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negate σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negate σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" (?nAX_g5828_0_0_0)) (?nAX_g5828_0_0_1))) (?nAX_g5828_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5828_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
  · (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negate σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negate σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negate σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" (?nAX_g5828_1_0_0)) (?nAX_g5828_1_0_1))) (?nAX_g5828_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5828_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
    all_goals linarith

end Lax455465Proofs.RamFractionPrimitives

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

namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

theorem canonical_sign (q:ℚ) (σ:Env) (h:FractionOutput q σ):
    (if σ.vars "rat.n"=0 then 0 else σ.vars "rat.s")=if q.num < 0 then 1 else 0:=by
  by_cases hn:σ.vars "rat.n"=0
  · have hnum:q.num=0:=by
      have he:q.num.natAbs=0:=h.2.1.symm.trans hn
      exact Int.natAbs_eq_zero.mp he
    simp [hn,hnum]
  · have hs:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by have:=h.2.2.2; omega
    rcases hs with hs | hs
    · have hnonneg:0≤ q:=by
        rw [← h.1]
        simp only [fractionValue,hs,show ¬(0:ℕ)=1 by decide,if_false]
        positivity
      have hnum:=Rat.num_nonneg.mpr hnonneg
      simp [hn,hs,not_lt.mpr hnum]
    · have hnpos:(0:ℚ) < σ.vars "rat.n" :=by exact_mod_cast (show 0 < σ.vars "rat.n" by omega)
      have hdpos:(0:ℚ) < σ.vars "rat.d" :=by
        rw [h.2.2.1]
        exact_mod_cast q.den_pos
      have hneg:q < 0:=by
        rw [← h.1]
        simp only [fractionValue,hs,if_true]
        exact div_neg_of_neg_of_pos (by linarith) hdpos
      have hnum:q.num < 0:=by
        by_contra hnum
        have hq:=Rat.num_nonneg.mp (show 0≤ q.num by omega)
        linarith
      simp [hn,hs,hnum]

theorem sign_spec (B:ℕ) (q:ℚ) (h1:1 < B) (hn:q.num.natAbs < B):
    Spec B (FractionOutput q) sign
      (fun _ τ => τ.vars "emit.s"=if q.num < 0 then 1 else 0) 6:=by
  intro σ h
  have hvalue:=h.2.1
  have hsign:=h.2.2.2
  have hcanonical:=canonical_sign q σ h
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LT.lt Int Int.instLTInt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Int.decLt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "emit.s") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B sign σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "emit.s" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "emit.s" (Expr.lit ((0:Nat))); let c12:Nat:=c7 (Expr.size (Expr.var "rat.s")); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B sign σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B sign σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_1)) hcase) (RunStep.assign B σ "emit.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_2)))) (?nAX_g5889_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (@And.intro (Run B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) ((6:Nat))) (c3 (Env.setVar σ "emit.s" (Env.vars σ "rat.s"))) (RunStep.mono B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (c9 c12) ((6:Nat)) (RunStep.ite_false B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) c12 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_5)) hcase) (RunStep.assign B σ "emit.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5889_0_0_6)))) (?nAX_g5889_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5889_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem emit_spec (B:ℕ) (q:ℚ) (words:List ℕ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hlen:words.length + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ Prefix words "lp.word" σ∧
      σ.vars "lp.position"=words.length∧ words.length + 2 < (σ.arrs "lp.word").length) emit
      (fun _ τ => Prefix (words ++ Lax109476.RationalEncoding.encodeRational q) "lp.word" τ∧
        τ.vars "lp.position"=words.length + 3) 27:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  let tag:=if q.num < 0 then 1 else 0
  have htag:tag < B:=by dsimp only [tag]; split_ifs <;> omega
  obtain ⟨ν,hsign,htagν⟩:=sign_spec B q h1 hn σ hf
  have hnumν:=(hsign.frame_var "rat.n" (by simp [sign,Com.wvars])).trans hf.2.1
  have hdenν:=(hsign.frame_var "rat.d" (by simp [sign,Com.wvars])).trans hf.2.2.1
  have hposν:=(hsign.frame_var "lp.position" (by simp [sign,Com.wvars])).trans hpos
  have hpν:Prefix words "lp.word" ν:=by
    simpa only [Prefix,hsign.frame_arr "lp.word" (by simp [sign,Com.warrs])] using hp
  have hroomν:words.length + 2 < (ν.arrs "lp.word").length:=by
    rwa [RamFrames.run_array_length hsign "lp.word"]
  have hnum:=RamFrames.keep_scalar (RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" words tag (.var "emit.s") h1 (by omega))
    "rat.n" q.num.natAbs (by simp [RamWordBuffer.append,Com.wvars]))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨μ,hfirst,hfirstPost⟩:=hnum ν ⟨⟨⟨hpν,hposν,by omega,
    by rw [evalB_var_iff]; exact ⟨htagν.symm,htagν ▸ htag⟩⟩,hnumν⟩,hdenν⟩
  have hroomμ:(words ++ [tag]).length + 1 < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hfirst "lp.word",List.length_append,List.length_singleton]
    exact hroomν
  have hden:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" (words ++ [tag]) q.num.natAbs (.var "rat.n") h1
      (by simp only [List.length_append,List.length_singleton]; omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨ρ,hsecond,hsecondPost⟩:=hden μ ⟨⟨hfirstPost.1.1.1,
    by simpa only [List.length_append,List.length_singleton] using hfirstPost.1.1.2,
    by omega,by rw [evalB_var_iff]; exact ⟨hfirstPost.1.2.symm,hfirstPost.1.2 ▸ hn⟩⟩,hfirstPost.2⟩
  have hroomρ:((words ++ [tag]) ++ [q.num.natAbs]).length < (ρ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hsecond "lp.word",List.length_append,List.length_singleton]
    exact hroomμ
  obtain ⟨τ,hthird,hthirdPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position"
    ((words ++ [tag]) ++ [q.num.natAbs]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ρ
    ⟨hsecondPost.1.1,by simpa only [List.length_append,List.length_singleton] using hsecondPost.1.2,
      hroomρ,by rw [evalB_var_iff]; exact ⟨hsecondPost.2.symm,hsecondPost.2 ▸ hd⟩⟩
  refine ⟨τ, (hsign.seq (hfirst.seq (hsecond.seq hthird))).mono (by simp [Expr.size]), ?_⟩
  simpa only [Lax109476.RationalEncoding.encodeRational,tag,List.append_assoc,
    List.cons_append,List.nil_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc]
    using hthirdPost

end Lax455465Proofs.RamFractionEncoding

end

section

namespace Lax455465Proofs.RamVectorEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding

def encode (qs:List ℚ):List ℕ:=qs.flatMap encodeRational

@[simp] theorem length_encode (qs:List ℚ):(encode qs).length=3*qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ) (words:List ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ encode (qs.take (σ.vars index))) "lp.word" σ∧
    σ.vars "lp.position"=words.length+3*σ.vars index∧
    words.length+3*qs.length < (σ.arrs "lp.word").length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+3*qs.length+3 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num.natAbs < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput qs[i] τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:"lp.position" ∉ body.wvars)
    (hbodyArray:"lp.word" ∉ body.warrs)
    (hemitIndex:index∉ RamFractionEncoding.emit.wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B RamFractionEncoding.emit σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ "lp.position"):
    Spec B (fun σ => R σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*qs.length < (σ.arrs "lp.word").length) (command index limit body)
      (fun _ τ => R τ∧ Prefix (words ++ encode qs) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*qs.length) ((K+35)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs words τ∧ τ.vars index=σ.vars index+1)
      (K+31):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ encode (qs.take i)).length=words.length+3*i:=by
      simp only [List.length_append,length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars "lp.position"=words.length+3*i:=
      (hproduce.frame_var "lp.position" hbodyPosition).trans hpos
    have hpν:Prefix (words ++ encode (qs.take i)) "lp.word" ν:=by
      simpa only [Prefix,hproduce.frame_arr "lp.word" hbodyArray] using hp
    have hroomν:words.length+3*qs.length < (ν.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hproduce "lp.word"]
    obtain ⟨μ,hemit,hemitted⟩:=RamFractionEncoding.emit_spec B qs[i] (words ++ encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+3*qs.length < (μ.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hemit "lp.word"]
    have hpμ:Prefix (words ++ encode (qs.take (i+1))) "lp.word" μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars "lp.position"=words.length+3*(i+1):=by rw [hpLen] at hemitted; omega
    have hnext:i+1 < B:=by omega
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) hnext)
    refine ⟨μ.setVar index (i+1),hproduce.seq (hemit.seq hinc),?_,?_⟩
    · refine ⟨hset μ (i+1) hRμ,by simp; omega,?_,?_,?_⟩
      · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hpμ
      · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true] using hposμ
      · simpa only [arrs_setVar] using hroomμ
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words) qs.length (K+31)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def sign (q:ℚ):ℕ:=if q.num < 0 then 1 else 0

theorem value_eq (q:ℚ):fractionValue (sign q) q.num.natAbs q.den=q:=by
  have hnum:(if q.num < 0 then -((q.num.natAbs:ℕ):ℚ) else ((q.num.natAbs:ℕ):ℚ))=(q.num:ℚ):=by
    generalize q.num=z
    cases z <;> simp
  by_cases h:q.num < 0
  · simp only [if_pos h] at hnum
    simpa only [fractionValue,sign,if_pos h,if_true,hnum] using q.num_div_den
  · simp only [if_neg h] at hnum
    simpa only [fractionValue,sign,if_neg h,show ¬(0:ℕ)=1 by decide,if_false,hnum] using q.num_div_den

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

theorem command_spec (B:ℕ) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front ++ (encodeRational q ++ tail)) "vm.output" σ∧
      σ.vars "cert.cursor"=front.length) command
      (fun _ τ => FractionOutput q τ∧ τ.vars "cert.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front ++ (encodeRational q ++ tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs "vm.output").length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "cert.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ "vm.output") (Env.vars σ "cert.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "cert.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 "vm.output") c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "cert.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 "vm.output") c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "cert.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "cert.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get "vm.output" (Expr.var "cert.cursor"))); let c18:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get "vm.output" c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get "vm.output" c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "cert.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B command σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B command σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor")) c3 (RunStep.eval_get B σ "vm.output" (Expr.var "cert.cursor") (Env.vars σ "cert.cursor") (RunStep.eval_var B σ "cert.cursor" (?nAX_g6135_0_0_0)) (?nAX_g6135_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 "vm.output" c18 c6 (RunStep.eval_add B c4 (Expr.var "cert.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "cert.cursor" (?nAX_g6135_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g6135_0_0_3)) (?nAX_g6135_0_0_4)) (?nAX_g6135_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 "vm.output" c21 c10 (RunStep.eval_add B c8 (Expr.var "cert.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "cert.cursor" (?nAX_g6135_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g6135_0_0_7)) (?nAX_g6135_0_0_8)) (?nAX_g6135_0_0_9) ?_)) (RunStep.assign B c12 "cert.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "cert.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "cert.cursor" (?nAX_g6135_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g6135_0_0_11)))))) (?nAX_g6135_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6135_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.NativeRationalBounds

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem negate (M:ℕ) (q:ℚ) (hq:Bounded M q):Bounded M (-q):=by
  simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq

theorem add (M:ℕ) (a b:ℚ) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^2) (a+b):=by
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn:sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*M^2:=by
    have hleft:=Nat.mul_le_mul ha.1 hb.2
    have hright:=Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd:a.den*b.den≤2*M^2:=by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd:=fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

theorem subtract (M:ℕ) (a b:ℚ) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^2) (a-b):=by
  simpa only [sub_eq_add_neg] using add M a (-b) ha (negate M b hb)

theorem vector_words (B M n:ℕ) (x:Fin n→ ℚ) (h1:1< B) (hM:M< B)
    (hx:∀ i,Bounded M (x i)):
    ∀ v∈Lax109476.RationalEncoding.encodeVector x,v< B:=by
  intro v hv
  simp only [Lax109476.RationalEncoding.encodeVector,List.mem_flatMap,List.mem_ofFn] at hv
  obtain ⟨q,⟨i,rfl⟩,hv⟩:=hv
  simp only [Lax109476.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl
  · split_ifs <;> omega
  · exact (hx i).1.trans_lt hM
  · exact (hx i).2.trans_lt hM

end Lax263307Proofs.NativeRationalBounds

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Invariant (array:String) (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "fill.i"≤ xs.length∧
  xs.length≤(σ.arrs array).length∧ Prefix (xs.take (σ.vars "fill.i")) array σ

theorem command_spec (B:ℕ) (xs:List ℕ) (array:String) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+1< B) (hwords:∀ x∈xs,x< B)
    (hri:"fill.i"∉read.wvars) (hrl:"fill.length"∉read.wvars) (hra:array∉read.warrs)
    (hinit:∀ σ,P σ→ P (σ.setVar "fill.i" 0))
    (hwrite:∀ σ τ,Run B (append array) σ τ 7→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ∧ τ.vars "fill.value"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "fill.length"=xs.length∧ xs.length≤(σ.arrs array).length)
      (command array read) (fun _ τ => P τ∧ Prefix xs array τ) ((K+11)*xs.length+6):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant array P xs σ∧ σ.vars "fill.i"< xs.length)
      (.seq read (append array))
      (fun σ τ => Invariant array P xs τ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+7):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hroom,hprefix⟩,hlt⟩
    let i:=σ.vars "fill.i"
    have htlen:(xs.take i).length=i:=by rw [List.length_take,Nat.min_eq_left hle]
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "fill.i"=i:=r1.frame_var "fill.i" hri
    obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B array "fill.i" (xs.take i) xs[i]
      (.var "fill.value") h1 (by rw [htlen]; omega) ν
      ⟨by simpa only [Prefix,r1.frame_arr array hra] using hprefix,by rwa [htlen],
        by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
        by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ hwords _ (List.getElem_mem hlt)⟩⟩
    have r2':Run B (append array) ν τ 7:=r2
    have ht:τ.vars "fill.i"=i+1:=by simpa only [htlen] using p2.2
    have rr:=r1.seq r2'
    refine ⟨τ,rr,⟨hwrite ν τ r2' p1.1,?_,by rw [ht]; omega,?_,?_⟩,ht⟩
    · exact (r2'.frame_var "fill.length" (by simp [append,Lax455465Proofs.RamWordBuffer.append,Com.wvars])).trans
        ((r1.frame_var "fill.length" hrl).trans hlen)
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,List.take_succ_eq_append_getElem hlt]
      exact p2.1
  have hloop:=Spec.forRangeZero "fill.i" "fill.length" (Invariant array P xs) xs.length (K+7)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hroom⟩
  have hi:Invariant array P xs (σ.setVar "fill.i" 0):=by
    refine ⟨hinit σ hP,?_,by simp,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_⟩
  simpa only [p.2,List.take_length] using p.1.2.2.2.2

end Lax263307Proofs.NativeTabulate

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeRationalTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def words (xs:List ℚ):List ℕ:=xs.flatMap encodeRational

theorem words_length (xs:List ℚ):(words xs).length=3*xs.length:=by
  induction xs with
  | nil => simp [words]
  | cons x xs ih => simp only [words,List.flatMap_cons,List.length_append,encodeRational,List.length_cons,List.length_nil] at ih ⊢; omega

end Lax263307Proofs.NativeRationalTabulate

end

section

namespace Lax263307Proofs.NativeRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax455465Proofs.RamLpRationalRead

theorem command_spec (B:ℕ) (array:String) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front++(encodeRational q++tail)) array σ∧ σ.vars "read.cursor"=front.length)
      (command array) (fun _ τ => FractionOutput q τ∧ τ.vars "read.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front++(encodeRational q++tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs array).length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "read.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ array) (Env.vars σ "read.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "read.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 array) c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "read.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 array) c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "read.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "read.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get array (Expr.var "read.cursor"))); let c18:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get array c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "read.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B (command array) σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B (command array) σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B (command array) σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get array (Expr.var "read.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get array (Expr.var "read.cursor")) c3 (RunStep.eval_get B σ array (Expr.var "read.cursor") (Env.vars σ "read.cursor") (RunStep.eval_var B σ "read.cursor" (?nAX_g8234_0_0_0)) (?nAX_g8234_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 array c18 c6 (RunStep.eval_add B c4 (Expr.var "read.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "read.cursor" (?nAX_g8234_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g8234_0_0_3)) (?nAX_g8234_0_0_4)) (?nAX_g8234_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 array c21 c10 (RunStep.eval_add B c8 (Expr.var "read.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "read.cursor" (?nAX_g8234_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g8234_0_0_7)) (?nAX_g8234_0_0_8)) (?nAX_g8234_0_0_9) ?_)) (RunStep.assign B c12 "read.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "read.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "read.cursor" (?nAX_g8234_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g8234_0_0_11)))))) (?nAX_g8234_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8234_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

theorem vector_entry_spec (B:ℕ) (array:String) (front tail:List ℕ) (qs:List ℚ)
    (i:ℕ) (hi:i < qs.length) (h3:3 < B) (hlen:front.length+3*i+3 < B)
    (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Prefix (front++(NativeRationalTabulate.words qs++tail)) array σ∧
      σ.vars "read.cursor"=front.length+3*i) (command array)
      (fun _ τ => FractionOutput qs[i] τ∧ τ.vars "read.cursor"=front.length+3*i+3) 17:=by
  have he:qs=qs.take i++qs[i]::qs.drop (i+1):=by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hlen':(front++NativeRationalTabulate.words (qs.take i)).length=front.length+3*i:=by
    rw [List.length_append,NativeRationalTabulate.words_length,List.length_take,Nat.min_eq_left hi.le]
  have hew:front++(NativeRationalTabulate.words qs++tail)=
      (front++NativeRationalTabulate.words (qs.take i))++
        (encodeRational qs[i]++(NativeRationalTabulate.words (qs.drop (i+1))++tail)):=by
    conv_lhs => rw [he]
    simp only [NativeRationalTabulate.words,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hh:=command_spec B array qs[i] (front++NativeRationalTabulate.words (qs.take i))
    (NativeRationalTabulate.words (qs.drop (i+1))++tail) h3 (by rwa [hlen']) hn hd
  simpa only [hlen',←hew] using hh

end Lax263307Proofs.NativeRationalRead

end

section

namespace Lax263307Proofs.NativeSlice

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def Context (source:String) (front xs tail:List ℕ) (σ:Env):Prop:=
  Prefix (front++(xs++tail)) source σ∧ σ.vars "slice.start"=front.length

theorem read_spec (B:ℕ) (source:String) (front xs tail:List ℕ)
    (i:ℕ) (hi:i< xs.length) (hB:front.length+xs.length+1< B) (hv:xs[i]< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.i"=i) (read source)
      (fun _ τ => Context source front xs tail τ∧ τ.vars "fill.value"=xs[i]) 5:=by
  rintro σ ⟨⟨hp,hstart⟩,hindex⟩
  have hlen:front.length+i<(front++(xs++tail)).length:=by simp; omega
  have hget:(σ.arrs source)[front.length+i]?=some xs[i]:=by
    have hh:=hp (front.length+i) hlen
    simpa only [List.getElem_append_right (by omega:front.length≤ front.length+i),
      Nat.add_sub_cancel_left,List.getElem_append_left hi] using hh
  have hroom:front.length+i<(σ.arrs source).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  (expose_names;
    (refine let c0:Nat:= @getElem (List Nat) Nat Nat (fun (as:List Nat) (i_1:Nat) => Nat.lt i_1 (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) xs i hi; let c1:Env→ Prop:=(fun (x τ:Env) => And (Context source front xs tail τ) (@Eq Nat (Env.vars τ "fill.value") c0)) σ; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 (Env.vars σ "slice.start") (Env.vars σ "fill.i"); let c4:Nat:= @List.getD Nat (Env.arrs σ source) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "fill.value" c4; let c6:Expr:=Expr.get source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")); @Exists.intro Env (fun (σ':Env) => And (Run B (read source) σ σ' ((5:Nat))) (c1 σ')) c5 (@And.intro (Run B (read source) σ c5 ((5:Nat))) (c1 c5) (RunStep.mono B (read source) σ c5 (c2 ((1:Nat)) (Expr.size c6)) ((5:Nat)) (RunStep.assign B σ "fill.value" c6 c4 (RunStep.eval_get B σ source (Expr.add (Expr.var "slice.start") (Expr.var "fill.i")) c3 (RunStep.eval_add B σ (Expr.var "slice.start") (Expr.var "fill.i") (Env.vars σ "slice.start") (Env.vars σ "fill.i") (RunStep.eval_var B σ "slice.start" (?nAX_g8333_0_0_0)) (RunStep.eval_var B σ "fill.i" (?nAX_g8333_0_0_1)) (?nAX_g8333_0_0_2)) (?nAX_g8333_0_0_3) ?_)) (?nAX_g8333_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8333_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8333_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,Prefix]

theorem command_spec (B:ℕ) (source target:String) (front xs tail:List ℕ)
    (hne:source≠target) (hB:front.length+xs.length+1< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Context source front xs tail σ∧ σ.vars "fill.length"=xs.length∧
      xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Context source front xs tail τ∧ Prefix xs target τ) (16*xs.length+6):=by
  have hh:=NativeTabulate.command_spec B xs target (Context source front xs tail) (read source) 5
    (by omega) hv (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by simp [read,Com.warrs])
    (fun σ h => by simpa only [Context,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_false] using h)
    (fun σ τ rr h => by
      simpa only [Context,Prefix,rr.frame_arr source (by simp [NativeTabulate.append,RamWordBuffer.append,Com.warrs,hne]),
        rr.frame_var "slice.start" (by simp [NativeTabulate.append,RamWordBuffer.append,Com.wvars])] using h)
    (fun i hi => read_spec B source front xs tail i hi hB (hv _ (List.getElem_mem hi)))
  exact hh

end Lax263307Proofs.NativeSlice

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeDistanceMetadata

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceData

theorem read_dimensions_spec (B m n:ℕ) (P:Program ℚ m n) (hB:m+n+3 < B):
    Spec B (Prefix (encodeProgram P) "lp.input") readDimensions
      (fun _ τ => τ.vars "projection.m"=m∧ τ.vars "projection.n"=n) 6:=by
  intro σ hp
  have hm:(σ.arrs "lp.input")[0]?=some m:=by
    have hh:=hp 0 (by simp [encodeProgram])
    simpa [encodeProgram] using hh
  have hn:(σ.arrs "lp.input")[1]?=some n:=by
    have hh:=hp 1 (by simp [encodeProgram])
    simpa [encodeProgram] using hh
  let ν:=σ.setVar "projection.m" m
  have r1:Run B (.assign "projection.m" (.get "lp.input" (.lit 0))) σ ν 3:=
    Run.assign (evalB_get (evalB_lit (show 0 < B by omega)) hm (by omega))
  let τ:=ν.setVar "projection.n" n
  have r2:Run B (.assign "projection.n" (.get "lp.input" (.lit 1))) ν τ 3:=
    Run.assign (evalB_get (evalB_lit (show 1 < B by omega)) hn (by omega))
  exact ⟨τ,r1.seq r2,by simp [τ,ν],by simp [τ]⟩

end Lax263307Proofs.NativeDistanceMetadata

end

section

namespace Lax263307Proofs.NativeCertificateRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection

def tagValue {m n:ℕ}:Certificate m n→ ℕ
  | .optimal _ _ => 0
  | .infeasible _ => 1
  | .unbounded _ _ => 2

theorem tag_spec (B:ℕ) {m n:ℕ} (c:Certificate m n) (h3:3< B):
    Spec B (Prefix (encodeCertificate c) "vm.output") tag
      (fun _ τ => τ.vars "projection.tag"=tagValue c) 3:=by
  intro σ hp
  have hget:(σ.arrs "vm.output")[0]?=some (tagValue c):=by
    cases c <;> simpa [encodeCertificate,tagValue] using hp 0 (by simp [encodeCertificate])
  have hv:tagValue c< B:=by cases c <;> dsimp [tagValue] <;> omega
  have hread:(Expr.get "vm.output" (.lit 0)).evalB B σ=some (tagValue c):=by
    exact evalB_get (evalB_lit (show 0< B by omega)) hget hv
  exact ⟨σ.setVar "projection.tag" (tagValue c),Run.assign hread,by simp⟩

theorem primal_spec (B m n:ℕ) (z:Fin (n+1)→ ℚ) (dual:Fin (m+(n+n))→ ℚ)
    (i:Fin (n+1)) (hB:3*n+10< B) (hn:(z i).num.natAbs< B) (hd:(z i).den< B):
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z dual)) "vm.output" σ∧
      σ.vars "certificate.index"=i.val) primal
      (fun _ τ => RamRational.FractionOutput (z i) τ) 23:=by
  rintro σ ⟨hp,hi⟩
  have hpos:Spec B (fun σ => σ.vars "certificate.index"=i.val) primalPosition
      (fun _ τ => τ.vars "read.cursor"=1+3*i.val) 6:=by
    intro μ hh
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 ((1:Nat)); let c2:Nat→ Nat:=Nat.mul ((3:Nat)); let c3:Nat:=c1 (c2 (@Fin.val (c0 n ((1:Nat))) i)); let c4:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "read.cursor") c3) μ; let c5:Nat:=c2 (Env.vars μ "certificate.index"); let c6:Nat:=c1 c5; let c7:Env:=Env.setVar μ "read.cursor" c6; let c8:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "certificate.index"); let c9:Expr:=Expr.add (Expr.lit ((1:Nat))) c8; @Exists.intro Env (fun (σ':Env) => And (Run B primalPosition μ σ' ((6:Nat))) (c4 σ')) c7 (@And.intro (Run B primalPosition μ c7 ((6:Nat))) (c4 c7) (RunStep.mono B primalPosition μ c7 (c1 (Expr.size c9)) ((6:Nat)) (RunStep.assign B μ "read.cursor" c9 c6 (RunStep.eval_add B μ (Expr.lit ((1:Nat))) c8 ((1:Nat)) c5 (RunStep.eval_lit B ((1:Nat)) μ (?nAX_g8534_0_0_0)) (RunStep.eval_mul B μ (Expr.lit ((3:Nat))) (Expr.var "certificate.index") ((3:Nat)) (Env.vars μ "certificate.index") (RunStep.eval_lit B ((3:Nat)) μ (?nAX_g8534_0_0_1)) (RunStep.eval_var B μ "certificate.index" (?nAX_g8534_0_0_2)) (?nAX_g8534_0_0_3)) (?nAX_g8534_0_0_4))) (?nAX_g8534_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8534_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8534_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8534_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8534_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8534_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8534_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  obtain ⟨ν,r1,p1⟩:=hpos σ hi
  have hpν:Prefix ([0]++RamVectorEncoding.encode (List.ofFn z)++encodeVector dual) "vm.output" ν:=by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encodeVector,RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hp
  obtain ⟨τ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "vm.output" [0] (encodeVector dual)
    (List.ofFn z) i.val (by simpa using i.isLt) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using hn) (by simpa only [List.getElem_ofFn] using hd) ν
    ⟨by simpa only [RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hpν,by simpa using p1⟩
  exact ⟨τ,(r1.seq r2),by simpa only [List.getElem_ofFn] using p2.1⟩

theorem dual_spec (B m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (i:Fin (m+(n+n))) (hB:3*m+10*n+20< B)
    (hn:(y i).num.natAbs< B) (hd:(y i).den< B):
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧
      σ.vars "projection.n"=n∧ σ.vars "certificate.index"=i.val) dual
      (fun _ τ => RamRational.FractionOutput (y i) τ) 27:=by
  rintro σ ⟨hp,hN,hi⟩
  have hpos:Spec B (fun σ => σ.vars "projection.n"=n∧ σ.vars "certificate.index"=i.val) dualPosition
      (fun _ τ => τ.vars "read.cursor"=1+3*(n+1+i.val)) 10:=by
    rintro μ ⟨hhN,hhi⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 ((1:Nat)); let c2:Nat→ Nat:=Nat.mul ((3:Nat)); let c3:Nat→ Nat:=c0 n; let c4:Nat:=c1 (c2 (c0 (c3 ((1:Nat))) (@Fin.val (c0 m (c3 n)) i))); let c5:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "read.cursor") c4) μ; let c6:Nat:=c0 (Env.vars μ "projection.n") ((1:Nat)); let c7:Nat:=c0 c6 (Env.vars μ "certificate.index"); let c8:Nat:=c2 c7; let c9:Nat:=c1 c8; let c10:Env:=Env.setVar μ "read.cursor" c9; let c11:Expr:=Expr.add (Expr.var "projection.n") (Expr.lit ((1:Nat))); let c12:Expr:=Expr.add c11 (Expr.var "certificate.index"); let c13:Expr:=Expr.mul (Expr.lit ((3:Nat))) c12; let c14:Expr:=Expr.add (Expr.lit ((1:Nat))) c13; @Exists.intro Env (fun (σ':Env) => And (Run B dualPosition μ σ' ((10:Nat))) (c5 σ')) c10 (@And.intro (Run B dualPosition μ c10 ((10:Nat))) (c5 c10) (RunStep.mono B dualPosition μ c10 (c1 (Expr.size c14)) ((10:Nat)) (RunStep.assign B μ "read.cursor" c14 c9 (RunStep.eval_add B μ (Expr.lit ((1:Nat))) c13 ((1:Nat)) c8 (RunStep.eval_lit B ((1:Nat)) μ (?nAX_g8537_0_0_0)) (RunStep.eval_mul B μ (Expr.lit ((3:Nat))) c12 ((3:Nat)) c7 (RunStep.eval_lit B ((3:Nat)) μ (?nAX_g8537_0_0_1)) (RunStep.eval_add B μ c11 (Expr.var "certificate.index") c6 (Env.vars μ "certificate.index") (RunStep.eval_add B μ (Expr.var "projection.n") (Expr.lit ((1:Nat))) (Env.vars μ "projection.n") ((1:Nat)) (RunStep.eval_var B μ "projection.n" (?nAX_g8537_0_0_2)) (RunStep.eval_lit B ((1:Nat)) μ (?nAX_g8537_0_0_3)) (?nAX_g8537_0_0_4)) (RunStep.eval_var B μ "certificate.index" (?nAX_g8537_0_0_5)) (?nAX_g8537_0_0_6)) (?nAX_g8537_0_0_7)) (?nAX_g8537_0_0_8))) (?nAX_g8537_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8537_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8537_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  obtain ⟨ν,r1,p1⟩:=hpos σ ⟨hN,hi⟩
  let front:= [0]++encodeVector z
  have hfront:front.length=1+3*(n+1):=by
    change ([0]++RamVectorEncoding.encode (List.ofFn z)).length=_
    simp only [List.length_append,List.length_cons,List.length_nil,
      RamVectorEncoding.length_encode,List.length_ofFn]
  have hpν:Prefix (front++RamVectorEncoding.encode (List.ofFn y)++[]) "vm.output" ν:=by
    simpa only [front,Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encodeVector,RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_nil,List.append_assoc] using hp
  obtain ⟨τ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "vm.output" front [] (List.ofFn y)
    i.val (by simpa using i.isLt) (by omega) (by rw [hfront]; omega)
    (by simpa only [List.getElem_ofFn] using hn) (by simpa only [List.getElem_ofFn] using hd) ν
    ⟨by simpa only [RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hpν,by rw [hfront]; omega⟩
  exact ⟨τ,r1.seq r2,by simpa only [List.getElem_ofFn] using p2.1⟩

end Lax263307Proofs.NativeCertificateRead

end

section

namespace Lax263307Proofs.NativeProjectionDecide

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def decision {m n:ℕ} (ρ:ℚ):Certificate (m+(n+n)) (n+1)→ ℕ
  | .optimal z _ => if distance z≤ρ then 0 else 1
  | _ => 2

theorem readDistance_spec (B m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (hs:3*n+10< B) (hn:(distance z).num.natAbs< B) (hd:(distance z).den< B):
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧ σ.vars "projection.n"=n)
      readDistance (fun _ τ => RamRational.FractionOutput (distance z) τ) 25:=by
  rintro σ ⟨hp,hN⟩
  let i:Fin (n+1):=Fin.natAdd n (0:Fin 1)
  have hv:i.val=n:=by simp [i]
  have r1:Run B (.assign "certificate.index" (.var "projection.n")) σ
      (σ.setVar "certificate.index" n) 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ (by omega:n< B)⟩)
  obtain ⟨τ,r2,p2⟩:=NativeCertificateRead.primal_spec B m n z y i hs hn hd
    (σ.setVar "certificate.index" n) ⟨hp,by simp [hv]⟩
  exact ⟨τ,r1.seq r2,p2⟩

theorem record_spec (B:ℕ) (a b:ℚ) (h1:1< B):
    Spec B (fun σ => σ.vars "cmp.le"=if a≤ b then 1 else 0) record
      (fun _ τ => τ.vars "projection.kind"=if a≤ b then 0 else 1) 6:=by
  have hflagB:(if a≤ b then 1 else 0:ℕ)< B:=by split_ifs <;> omega
  by_cases hh:a≤ b
  · (expose_names;
      (refine fun (σ:Env) (a_1:@Eq Nat (Env.vars σ "cmp.le") (@ite Nat (@LE.le Rat Rat.instLE a b) (Rat.instDecidableLe a b) ((1:Nat)) ((0:Nat)))) => let c0:Prop:= @Eq Nat (Env.vars σ "cmp.le") ((1:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LE.le Rat Rat.instLE a b) (Rat.instDecidableLe a b) ((0:Nat)) ((1:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "projection.kind") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B record σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "projection.kind" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "cmp.le") (Expr.lit ((1:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "projection.kind" (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "projection.kind" (Expr.lit ((1:Nat))); let c13:Env:=Env.setVar σ "projection.kind" ((1:Nat)); let c14:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B record σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B record σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 c12 σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "cmp.le") (Expr.lit ((1:Nat))) (Env.vars σ "cmp.le") ((1:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g8545_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase) (RunStep.assign B σ "projection.kind" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8545_0_0_1)))) (?nAX_g8545_0_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c13 (@And.intro (Run B record σ c13 ((6:Nat))) (c3 c13) (RunStep.mono B record σ c13 (c9 c14) ((6:Nat)) (RunStep.ite_false B c8 c11 c12 σ c13 c14 (RunStep.cond_eq_false B σ (Expr.var "cmp.le") (Expr.lit ((1:Nat))) (Env.vars σ "cmp.le") ((1:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g8545_0_0_3)) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase) (RunStep.assign B σ "projection.kind" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1))) (?nAX_g8545_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8545_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  · (expose_names;
      (refine fun (σ:Env) (a_1:@Eq Nat (Env.vars σ "cmp.le") (@ite Nat (@LE.le Rat Rat.instLE a b) (Rat.instDecidableLe a b) ((1:Nat)) ((0:Nat)))) => let c0:Prop:= @Eq Nat (Env.vars σ "cmp.le") ((1:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LE.le Rat Rat.instLE a b) (Rat.instDecidableLe a b) ((0:Nat)) ((1:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "projection.kind") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B record σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "projection.kind" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "cmp.le") (Expr.lit ((1:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "projection.kind" (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "projection.kind" (Expr.lit ((1:Nat))); let c13:Env:=Env.setVar σ "projection.kind" ((1:Nat)); let c14:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B record σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B record σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 c12 σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "cmp.le") (Expr.lit ((1:Nat))) (Env.vars σ "cmp.le") ((1:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g8545_1_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase) (RunStep.assign B σ "projection.kind" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8545_1_0_1)))) (?nAX_g8545_1_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c13 (@And.intro (Run B record σ c13 ((6:Nat))) (c3 c13) (RunStep.mono B record σ c13 (c9 c14) ((6:Nat)) (RunStep.ite_false B c8 c11 c12 σ c13 c14 (RunStep.cond_eq_false B σ (Expr.var "cmp.le") (Expr.lit ((1:Nat))) (Env.vars σ "cmp.le") ((1:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g8545_1_0_3)) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase) (RunStep.assign B σ "projection.kind" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1))) (?nAX_g8545_1_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8545_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8545_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all

theorem optimal_spec (B M m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ) (ρ:ℚ)
    (hB:2*M^2+3< B) (hs:3*n+10< B) (hz:Bounded M (distance z)) (hρ:Bounded M ρ):
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧
      σ.vars "projection.n"=n∧ Stored "projection.tolerance" ρ σ) optimal
      (fun _ τ => τ.vars "projection.kind"=if distance z≤ρ then 0 else 1) 89:=by
  rintro σ ⟨hc,hN,hT⟩
  have h1:1< B:=by nlinarith
  have hM:M< B:=by nlinarith
  obtain ⟨σ1,r1,p1⟩:=readDistance_spec B m n z y hs (hz.1.trans_lt hM) (hz.2.trans_lt hM) σ ⟨hc,hN⟩
  obtain ⟨σ2,r2,p2⟩:=save_spec B "left" (distance z) h1 (hz.1.trans_lt hM) (hz.2.trans_lt hM) (by decide) σ1 p1
  have hT2:Stored "projection.tolerance" ρ σ2:=by
    simpa only [Stored,String.reduceAppend,(r1.seq r2).frame_var "projection.tolerance.s" (by decide),
      (r1.seq r2).frame_var "projection.tolerance.n" (by decide),
      (r1.seq r2).frame_var "projection.tolerance.d" (by decide)] using hT
  obtain ⟨σ3,r3,p3⟩:=load_spec B "projection.tolerance" ρ h1 (hρ.1.trans_lt hM) (hρ.2.trans_lt hM) (by decide) σ2 hT2
  obtain ⟨σ4,r4,p4⟩:=save_spec B "right" ρ h1 (hρ.1.trans_lt hM) (hρ.2.trans_lt hM) (by decide) σ3 p3
  have hL4:Stored "left" (distance z) σ4:=by
    simpa only [Stored,String.reduceAppend,(r3.seq r4).frame_var "left.s" (by decide),
      (r3.seq r4).frame_var "left.n" (by decide),(r3.seq r4).frame_var "left.d" (by decide)] using p2
  obtain ⟨σ5,r5,p5⟩:=compare_spec B M (distance z) ρ hB hz hρ σ4 ⟨hL4,p4⟩
  obtain ⟨τ,r6,p6⟩:=record_spec B (distance z) ρ h1 σ5 p5
  exact ⟨τ,r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))),p6⟩

def DistanceBounded (M:ℕ) {m n:ℕ}:Certificate (m+(n+n)) (n+1)→ Prop
  | .optimal z _ => Bounded M (distance z)
  | _ => True

theorem command_spec (B M m n:ℕ) (c:Certificate (m+(n+n)) (n+1)) (ρ:ℚ)
    (hB:2*M^2+3< B) (hs:3*n+10< B) (hρ:Bounded M ρ)
    (hc:DistanceBounded M c):
    Spec B (fun σ => Prefix (encodeCertificate c) "vm.output" σ∧
      σ.vars "projection.n"=n∧ Stored "projection.tolerance" ρ σ) command
      (fun _ τ => τ.vars "projection.kind"=decision ρ c) 96:=by
  rintro σ ⟨hp,hN,hT⟩
  have h3:3< B:=by omega
  obtain ⟨ν,r1,p1⟩:=NativeCertificateRead.tag_spec B c h3 σ hp
  have hpν:Prefix (encodeCertificate c) "vm.output" ν:=by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide)] using hp
  have hNν:=(r1.frame_var "projection.n" (by decide)).trans hN
  have hTν:Stored "projection.tolerance" ρ ν:=by
    simpa only [Stored,String.reduceAppend,r1.frame_var "projection.tolerance.s" (by decide),
      r1.frame_var "projection.tolerance.n" (by decide),
      r1.frame_var "projection.tolerance.d" (by decide)] using hT
  cases c with
  | optimal z y =>
    obtain ⟨τ,r2,p2⟩:=optimal_spec B M m n z y ρ hB hs hc hρ ν ⟨hpν,hNν,hTν⟩
    have he:(Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some true:=by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega:0< B)⟩)
        (evalB_lit (by omega:0< B))]
      rfl
    exact ⟨τ,(r1.seq (Run.ite_true (d:=reject) he r2)).mono (by decide),p2⟩
  | infeasible y =>
    have he:(Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some false:=by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega:1< B)⟩)
        (evalB_lit (by omega:0< B))]
      rfl
    have r2:Run B reject ν (ν.setVar "projection.kind" 2) 2:=Run.assign (evalB_lit (by omega))
    exact ⟨_,(r1.seq (Run.ite_false (c:=optimal) he r2)).mono (by decide),by simp [decision]⟩
  | unbounded z d =>
    have he:(Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some false:=by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega:2< B)⟩)
        (evalB_lit (by omega:0< B))]
      rfl
    have r2:Run B reject ν (ν.setVar "projection.kind" 2) 2:=Run.assign (evalB_lit (by omega))
    exact ⟨_,(r1.seq (Run.ite_false (c:=optimal) he r2)).mono (by decide),by simp [decision]⟩

end Lax263307Proofs.NativeProjectionDecide

end

section

namespace Lax263307Proofs.NativeProjectionNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def Context {m n:ℕ} (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ) (σ:Env):Prop:=
  Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧
    σ.vars "projection.m"=m∧ σ.vars "projection.n"=n

theorem frame {m n B K:ℕ} {z:Fin (n+1)→ ℚ} {y:Fin (m+(n+n))→ ℚ}
    {σ τ:Env} {c:Com} (rr:Run B c σ τ K) (h:Context z y σ)
    (ha:"vm.output"∉c.warrs) (hm:"projection.m"∉c.wvars) (hn:"projection.n"∉c.wvars):
    Context z y τ:=by
  simpa only [Context,Prefix,rr.frame_arr "vm.output" ha,rr.frame_var "projection.m" hm,
    rr.frame_var "projection.n" hn] using h

theorem plus_spec (B M m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (i:Fin n) (hB:2*M^2+3< B) (hs:3*m+10*n+20< B)
    (hy:∀ j,Bounded M (y j)):
    Spec B (fun σ => Context z y σ∧ σ.vars "projection.entry"=i.val) plus
      (fun _ τ => RamRational.FractionOutput (plusMultipliers y i) τ) 31:=by
  rintro σ ⟨hc,hi⟩
  have hM:M< B:=by nlinarith
  let j:Fin (m+(n+n)):=Fin.natAdd m (Fin.castAdd n i)
  have hj:j.val=m+i.val:=rfl
  have hset:Run B (.assign "certificate.index" (.add (.var "projection.m") (.var "projection.entry"))) σ
      (σ.setVar "certificate.index" j.val) 4:=by
    apply Run.assign
    rw [hj]
    exact evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega:m< B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega:i.val< B)⟩) (by dsimp only [Bop.apply]; omega)
  obtain ⟨τ,rr,ht⟩:=NativeCertificateRead.dual_spec B m n z y j hs
    ((hy j).1.trans_lt hM) ((hy j).2.trans_lt hM) (σ.setVar "certificate.index" j.val)
    ⟨hc.1,hc.2.2,by simp⟩
  exact ⟨τ,hset.seq rr,ht⟩

theorem minus_spec (B M m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (i:Fin n) (hB:2*M^2+3< B) (hs:3*m+10*n+20< B)
    (hy:∀ j,Bounded M (y j)):
    Spec B (fun σ => Context z y σ∧ σ.vars "projection.entry"=i.val) minus
      (fun _ τ => RamRational.FractionOutput (minusMultipliers y i) τ) 33:=by
  rintro σ ⟨hc,hi⟩
  have hM:M< B:=by nlinarith
  let j:Fin (m+(n+n)):=Fin.natAdd m (Fin.natAdd n i)
  have hj:j.val=(m+n)+i.val:=by dsimp [j]; omega
  have hset:Run B (.assign "certificate.index" (.add (.add (.var "projection.m") (.var "projection.n")) (.var "projection.entry"))) σ
      (σ.setVar "certificate.index" j.val) 6:=by
    apply Run.assign
    rw [hj]
    exact evalB_bin (op:=.add)
      (evalB_bin (op:=.add)
        (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega:m< B)⟩)
        (by rw [evalB_var_iff]; exact ⟨hc.2.2.symm,hc.2.2 ▸ (by omega:n< B)⟩) (by dsimp only [Bop.apply]; omega))
      (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega:i.val< B)⟩) (by dsimp only [Bop.apply]; omega)
  obtain ⟨τ,rr,ht⟩:=NativeCertificateRead.dual_spec B m n z y j hs
    ((hy j).1.trans_lt hM) ((hy j).2.trans_lt hM) (σ.setVar "certificate.index" j.val)
    ⟨hc.1,hc.2.2,by simp⟩
  exact ⟨τ,hset.seq rr,ht⟩

theorem command_spec (B M m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (i:Fin n) (hB:2*M^2+3< B) (hs:3*m+10*n+20< B)
    (hy:∀ j,Bounded M (y j)):
    Spec B (fun σ => Context z y σ∧ σ.vars "projection.entry"=i.val) command
      (fun _ τ => Context z y τ∧ RamRational.FractionOutput (normal y i) τ)
      (36*(M^2).size+176):=by
  rintro σ ⟨hc,hi⟩
  have h1:1< B:=by nlinarith
  have hM:M< B:=by nlinarith
  have hp:Bounded M (plusMultipliers y i):=hy _
  have hm:Bounded M (minusMultipliers y i):=hy _
  have hpneg:Bounded M (-plusMultipliers y i):=by
    simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hp
  obtain ⟨σ1,r1,p1⟩:=plus_spec B M m n z y i hB hs hy σ ⟨hc,hi⟩
  obtain ⟨σ2,r2,p2⟩:=RamFractionPrimitives.negate_spec B (plusMultipliers y i) h1 σ1 p1
  obtain ⟨σ3,r3,p3⟩:=save_spec B "left" (-plusMultipliers y i) h1
    (hpneg.1.trans_lt hM) (hpneg.2.trans_lt hM) (by decide) σ2 p2
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩:=minus_spec B M m n z y i hB hs hy σ3
    ⟨frame r123 hc (by decide) (by decide) (by decide),
      (r123.frame_var "projection.entry" (by decide)).trans hi⟩
  obtain ⟨σ5,r5,p5⟩:=save_spec B "right" (minusMultipliers y i) h1
    (hm.1.trans_lt hM) (hm.2.trans_lt hM) (by decide) σ4 p4
  have hleft:Stored "left" (-plusMultipliers y i) σ5:=by
    simpa only [Stored,String.reduceAppend,(r4.seq r5).frame_var "left.s" (by decide),
      (r4.seq r5).frame_var "left.n" (by decide),(r4.seq r5).frame_var "left.d" (by decide)] using p3
  obtain ⟨τ,r6,p6⟩:=add_spec B M (-plusMultipliers y i) (minusMultipliers y i) hB hpneg hm σ5 ⟨hleft,p5⟩
  have hden:((-plusMultipliers y i).den*(minusMultipliers y i).den).size≤(M^2).size:=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul hpneg.2 hm.2])
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  refine ⟨τ,rr.mono (by omega),frame rr hc (by decide) (by decide) (by decide),?_⟩
  simpa only [normal,sub_eq_neg_add] using p6

end Lax263307Proofs.NativeProjectionNormal

end

section

namespace Lax263307Proofs.NativeProjectionVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeSignedArithmetic
open NativeProjectionNormal

theorem normal_spec (B M m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (hB:2*M^2+3< B) (hs:3*m+10*n+20< B) (hy:∀ j,Bounded M (y j)):
    Spec B (fun σ => Context z y σ∧ 3*n<(σ.arrs "lp.word").length) normalCommand
      (fun _ τ => Context z y τ∧ Prefix (encodeVector (normal y)) "lp.word" τ∧
        τ.vars "lp.position"=3*n) ((36*(M^2).size+211)*n+8):=by
  have h1:1< B:=by nlinarith
  have hheight (i:Fin n):Bounded (2*M^2) (normal y i):=
    NativeRationalBounds.subtract M (minusMultipliers y i) (plusMultipliers y i) (hy _) (hy _)
  have hh:=RamVectorEncoding.command_spec B (36*(M^2).size+176) (Context z y)
    "projection.entry" "projection.n" (List.ofFn (normal y)) [] NativeProjectionNormal.command h1
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hheight ⟨i,by simpa using hi⟩).2.trans_lt (by omega))
    (fun σ h => by simpa only [List.length_ofFn] using h.2.2)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using NativeProjectionNormal.command_spec B M m n z y ⟨i,by simpa using hi⟩ hB hs hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hc,hr⟩
  have r1:Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2:=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩:=hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hc (by decide) (by decide) (by decide),by simp [Prefix],by simp,by simpa using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeProjectionVectors

end

section

namespace Lax263307Proofs.NativeProjectionNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection

theorem encode_point_distance {n:ℕ} (z:Fin (n+1)→ ℚ):
    encodeVector z=encodeVector (point z)++encodeRational (distance z):=by
  unfold encodeVector
  rw [List.ofFn_add,List.flatMap_append]
  simp [distance,List.ofFn_succ]
  apply congrArg (fun f:Fin n→ ℚ => (List.ofFn f).flatMap encodeRational)
  funext i
  change z (Fin.castLE _ i)=z (Fin.castAdd 1 i)
  congr 1

theorem command_spec (B m n:ℕ) (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ)
    (hs:3*n+10< B) (hwords:∀ v∈encodeVector (point z),v< B):
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧
      σ.vars "projection.n"=n∧ 3*n≤(σ.arrs "lp.word").length) command
      (fun _ τ => Prefix (encodeVector (point z)) "lp.word" τ∧ τ.vars "lp.position"=3*n)
      (48*n+14):=by
  have hlen:(encodeVector (point z)).length=3*n:=by
    change (RamVectorEncoding.encode (List.ofFn (point z))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup:Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "slice.start"=1∧ τ.vars "fill.length"=3*n∧ τ.vars "lp.position"=3*n) 8:=by
    intro σ hh
    (expose_names;
      (refine let c0:Nat→ Nat:=Nat.mul ((3:Nat)); let c1:Nat:=c0 n; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "slice.start") ((1:Nat))) (And (@Eq Nat (Env.vars τ "fill.length") c1) (@Eq Nat (Env.vars τ "lp.position") c1))) σ; let c3:Env:=Env.setVar σ "slice.start" ((1:Nat)); let c4:Nat:=Env.vars c3 "projection.n"; let c5:Nat:=c0 c4; let c6:Env:=Env.setVar c3 "fill.length" c5; let c7:Nat:=Env.vars c6 "fill.length"; let c8:Env:=Env.setVar c6 "lp.position" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c12:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "projection.n"); let c13:Nat:=c10 (Expr.size c12); let c14:Nat:=c10 (Expr.size (Expr.var "fill.length")); let c15:Nat:=c9 c13 c14; let c16:Com:=Com.assign "fill.length" c12; let c17:String→ Nat:=Env.vars c8; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((8:Nat))) (c2 σ')) c8 (@And.intro (Run B setup σ c8 ((8:Nat))) (c2 c8) (RunStep.mono B setup σ c8 (c9 c11 c15) ((8:Nat)) (RunStep.seq B (Com.assign "slice.start" (Expr.lit ((1:Nat)))) (Com.seq c16 (Com.assign "lp.position" (Expr.var "fill.length"))) σ c3 c8 c11 c15 (RunStep.assign B σ "slice.start" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8562_0_0_0))) (RunStep.seq B c16 (Com.assign "lp.position" (Expr.var "fill.length")) c3 c6 c8 c13 c14 (RunStep.assign B c3 "fill.length" c12 c5 (RunStep.eval_mul B c3 (Expr.lit ((3:Nat))) (Expr.var "projection.n") ((3:Nat)) c4 (RunStep.eval_lit B ((3:Nat)) c3 (?nAX_g8562_0_0_1)) (RunStep.eval_var B c3 "projection.n" (?nAX_g8562_0_0_2)) (?nAX_g8562_0_0_3))) (RunStep.assign B c6 "lp.position" (Expr.var "fill.length") c7 (RunStep.eval_var B c6 "fill.length" (?nAX_g8562_0_0_4))))) (?nAX_g8562_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8562_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8562_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8562_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8562_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8562_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8562_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  rintro σ ⟨hc,hN,hr⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ hN
  have hp:Prefix ([0]++(encodeVector (point z)++(encodeRational (distance z)++encodeVector y))) "vm.output" ν:=by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encode_point_distance,List.append_assoc] using hc
  obtain ⟨τ,r2,p2⟩:=NativeSlice.command_spec B "vm.output" "lp.word" [0]
    (encodeVector (point z)) (encodeRational (distance z)++encodeVector y) (by decide)
    (by simp only [List.length_cons,List.length_nil,hlen]; omega) hwords ν
    ⟨⟨hp,by simpa using p1.1⟩,by simpa only [hlen] using p1.2.1,
      by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2.2,
    (r2.frame_var "lp.position" (by decide)).trans p1.2.2⟩

end Lax263307Proofs.NativeProjectionNear

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeSignedArithmetic

theorem finish_reject_spec (B:ℕ) (h2:2< B):
    Spec B (fun σ => σ.vars "projection.kind"=2) finish
      (fun _ τ => τ.vars "projection.kind"=2) 9:=by
  intro σ hh
  have he0:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false:=by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ h2⟩)
      (evalB_lit (by omega:0< B))]
    rfl
  have he1:(Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some false:=by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ h2⟩)
      (evalB_lit (by omega:1< B))]
    rfl
  exact ⟨σ,Run.ite_false he0 (Run.ite_false he1 Run.skip),hh⟩

theorem finish_optimal_spec (B M m n:ℕ) (P:Program ℚ m n)
    (z:Fin (n+1)→ ℚ) (y:Fin (m+(n+n))→ ℚ) (ρ:ℚ)
    (hB:2*M^2+3< B) (hs:3*m+10*n+20< B)
    (hz:∀ i,Bounded M (z i)) (hy:∀ i,Bounded M (y i)):
    Spec B (fun σ => NativeProjectionNormal.Context z y σ∧
      σ.vars "projection.kind"=NativeProjectionDecide.decision ρ (.optimal z y)∧
      3*n<(σ.arrs "lp.word").length) finish
      (fun _ τ => Output (classify P ρ (.optimal z y)) τ)
      ((36*(M^2).size+300)*(n+1)+20):=by
  rintro σ ⟨hc,hk,hr⟩
  have hM:M< B:=by nlinarith
  have h1:1< B:=by nlinarith
  by_cases hnear:distance z≤ρ
  · have hk0:σ.vars "projection.kind"=0:=by simpa only [NativeProjectionDecide.decision,if_pos hnear] using hk
    obtain ⟨τ,rr,ht⟩:=NativeProjectionNear.command_spec B m n z y (by omega)
      (NativeRationalBounds.vector_words B M n (point z) h1 hM (fun i => hz _)) σ
      ⟨hc.1,hc.2.2,hr.le⟩
    have he:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk0.symm,hk0 ▸ (by omega:0< B)⟩)
        (evalB_lit (by omega:0< B))]
      rfl
    refine ⟨τ,(Run.ite_true (d:=.ite (.eq (.var "projection.kind") (.lit 1)) NativeProjectionVectors.normalCommand .skip) he rr).mono (by dsimp [Cond.size,Expr.size]; nlinarith),?_⟩
    simp only [classify,if_pos hnear,Output]
    exact ⟨(rr.frame_var "projection.kind" (by decide)).trans hk0,ht⟩
  · have hk1:σ.vars "projection.kind"=1:=by simpa only [NativeProjectionDecide.decision,if_neg hnear] using hk
    obtain ⟨τ,rr,ht⟩:=NativeProjectionVectors.normal_spec B M m n z y hB hs hy σ ⟨hc,hr⟩
    have he0:(Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false:=by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk1.symm,hk1 ▸ h1⟩)
        (evalB_lit (by omega:0< B))]
      rfl
    have he1:(Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk1.symm,hk1 ▸ h1⟩) (evalB_lit h1)]
      rfl
    refine ⟨τ,(Run.ite_false (c:=NativeProjectionNear.command) he0 (Run.ite_true (d:=.skip) he1 rr)).mono (by dsimp [Cond.size,Expr.size]; nlinarith),?_⟩
    simp only [classify,if_neg hnear,Output]
    exact ⟨(rr.frame_var "projection.kind" (by decide)).trans hk1,ht.2⟩

theorem command_spec (B M m n:ℕ) (P:Program ℚ m n)
    (c:Certificate (m+(n+n)) (n+1)) (ρ:ℚ)
    (hB:2*M^2+3< B) (hs:3*m+10*n+20< B)
    (hc:CertificateBounded M c) (hρ:Bounded M ρ):
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ∧
      Prefix (encodeCertificate c) "vm.output" σ∧ Stored "projection.tolerance" ρ σ∧
      3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Output (classify P ρ c) τ∧ Prefix (encodeProgram P) "lp.input" τ∧ τ.vars "projection.n"=n)
      (cost M n):=by
  rintro σ ⟨hp,hcert,hT,hr⟩
  obtain ⟨ν,r1,p1⟩:=NativeDistanceMetadata.read_dimensions_spec B m n P (by omega) σ hp
  have hcertν:Prefix (encodeCertificate c) "vm.output" ν:=by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide)] using hcert
  have hTν:Stored "projection.tolerance" ρ ν:=by
    simpa only [Stored,String.reduceAppend,r1.frame_var "projection.tolerance.s" (by decide),
      r1.frame_var "projection.tolerance.n" (by decide),r1.frame_var "projection.tolerance.d" (by decide)] using hT
  have hdist:NativeProjectionDecide.DistanceBounded M c:=by
    cases c with
    | optimal z y => exact hc.1 _
    | infeasible _ => trivial
    | unbounded _ _ => trivial
  obtain ⟨μ,r2,p2⟩:=NativeProjectionDecide.command_spec B M m n c ρ hB (by omega) hρ hdist ν ⟨hcertν,p1.2,hTν⟩
  have hcertμ:Prefix (encodeCertificate c) "vm.output" μ:=by
    simpa only [Prefix,r2.frame_arr "vm.output" (by decide)] using hcertν
  have hm:=(r2.frame_var "projection.m" (by decide)).trans p1.1
  have hn:=(r2.frame_var "projection.n" (by decide)).trans p1.2
  have hroom:3*n<(μ.arrs "lp.word").length:=by rwa [RamFrames.run_array_length (r1.seq r2)]
  cases c with
  | optimal z y =>
    obtain ⟨τ,r3,p3⟩:=finish_optimal_spec B M m n P z y ρ hB hs hc.1 hc.2 μ ⟨⟨hcertμ,hm,hn⟩,p2,hroom⟩
    have rr:=r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp,
      (r3.frame_var "projection.n" (by decide)).trans hn⟩
  | infeasible y =>
    obtain ⟨τ,r3,p3⟩:=finish_reject_spec B (by omega) μ p2
    have rr:=r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp,
      (r3.frame_var "projection.n" (by decide)).trans hn⟩
  | unbounded z d =>
    obtain ⟨τ,r3,p3⟩:=finish_reject_spec B (by omega) μ p2
    have rr:=r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp,
      (r3.frame_var "projection.n" (by decide)).trans hn⟩

end Lax263307Proofs.NativeProjectionResult

end

theorem solution:∀ (B M m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n)
  (c:Lax109476.RationalCertificates.Certificate (m + (n + n)) (n + 1)) (ρ:ℚ),
  2 * M ^ 2 + 3 < B→
    3 * m + 10 * n + 20 < B→
      Lax263307Proofs.NativeProjectionResult.CertificateBounded M c→
        Lax263307Proofs.NativeSignedArithmetic.Bounded M ρ→
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ:Lax808846Proofs.Imp.Env) =>
              Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeProgram P) "lp.input" σ∧
                Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeCertificate c) "vm.output" σ∧
                  Lax263307Proofs.NativeSignedArithmetic.Stored "projection.tolerance" ρ σ∧
                    3 * n < (σ.arrs "lp.word").length)
            Lax263307Proofs.NativeProjectionResult.command
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              Lax263307Proofs.NativeProjectionResult.Output (Lax263307.RationalProjection.classify P ρ c) τ∧
                Lax455465Proofs.RamVirtualState.Prefix (Lax109476.RationalEncoding.encodeProgram P) "lp.input" τ∧
                  τ.vars "projection.n"=n)
            (Lax263307Proofs.NativeProjectionResult.cost M n):= @Lax263307Proofs.NativeProjectionResult.command_spec
