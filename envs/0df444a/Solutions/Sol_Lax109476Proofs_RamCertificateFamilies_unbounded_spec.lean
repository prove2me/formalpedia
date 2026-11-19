-- Prove2me | solution 1 for Lax109476Proofs.RamCertificateFamilies.unbounded_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:43:30.110351+00:00
-- url     : https://prove2.me/submissions/74124871-8743-4b67-8330-e2c928596f70

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces

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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem length_arrOf (n:ℕ) (f:ℕ→ ℕ):(arrOf n f).length=n:=by
  simp [arrOf]

theorem replicate_eq_arrOf (n v:ℕ):List.replicate n v=arrOf n (fun _ => v):=by
  simp [arrOf,List.map_const']

theorem arrOf_congr {n:ℕ} {f g:ℕ→ ℕ} (h:∀ i < n,f i=g i):
    arrOf n f=arrOf n g:=by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf,List.length_map,List.length_range] at h₁
  simp [arrOf,h k h₁]

theorem set_arrOf {n i:ℕ} (f:ℕ→ ℕ) (v:ℕ):
    (arrOf n f).set i v=arrOf n (fun k => if k=i then v else f k):=by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk:k=i
  · subst hk; simp [arrOf]
  · simp [arrOf,hk,Ne.symm hk]

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

theorem Spec.pre (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ):Spec B P' c Q K:=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

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

namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

end Lax109476Proofs.RamRational

end

section

namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding

theorem fractionValue_sign (s n d:ℕ) (hs:s≤ 1) (hd:0 < d):
    (if (fractionValue s n d).num < 0 then 1 else 0:ℕ) =
      if n=0 then 0 else s:=by
  have hscases:s=0∨ s=1:=by omega
  rcases hscases with rfl | rfl
  · have hq:0≤ fractionValue 0 n d:=by change (0:ℚ)≤ (n:ℚ) / d; positivity
    have hnum:=Rat.num_nonneg.mpr hq
    simp [not_lt.mpr hnum]
  · by_cases hz:n=0
    · simp [fractionValue,hz]
    · have hq:fractionValue 1 n d < 0:=by
        change -(n:ℚ) / d < 0
        have hp:(0:ℚ) < (n:ℚ) / d:=by positivity
        rw [neg_div]
        linarith
      have hnum:(fractionValue 1 n d).num < 0:=by
        rw [← not_le,Rat.num_nonneg]
        exact not_le_of_gt hq
      simp [hz,hnum]

end Lax109476Proofs.RamEncoding

end

section

namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem rationalSign_le_one (q:ℚ):rationalSign q≤ 1:=by unfold rationalSign; split_ifs <;> omega

theorem canonical_fractionValue (q:ℚ):
    fractionValue (rationalSign q) q.num.natAbs q.den=q:=by
  calc
    _=(q.num:ℚ) / q.den:=by
      by_cases h:q.num < 0
      · have hq:(q.num:ℚ) < 0:=by exact_mod_cast h
        simp [fractionValue,rationalSign,h,Nat.cast_natAbs,Int.cast_abs,abs_of_neg hq]
      · have hq:(0:ℚ)≤ q.num:=by exact_mod_cast le_of_not_gt h
        simp [fractionValue,rationalSign,h,Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg hq]
    _=q:=q.num_div_den

def LeftOutput (q:ℚ) (σ:Env):Prop:=
  σ.vars "left.s"=rationalSign q∧ σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den

theorem map_getD {α:Type*} (f:α→ ℕ) (xs:List α) (i:ℕ) (hi:i < xs.length):
    (xs.map f).getD i 0=f xs[i]:=by
  simp [List.getD_eq_getElem?_getD,hi]

theorem loadLeft_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadLeft a)
      (fun _ τ => LeftOutput qs[i] τ) 9:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi⟩
  have hsB:=(rationalSign_le_one qs[i]).trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsg:(σ.arrs (a ++ ".s")).getD i 0=rationalSign qs[i]:=by
    rw [hσs]; exact map_getD _ _ _ hi
  have hng:(σ.arrs (a ++ ".n")).getD i 0=qs[i].num.natAbs:=by
    rw [hσn]; exact map_getD _ _ _ hi
  have hdg:(σ.arrs (a ++ ".d")).getD i 0=qs[i].den:=by
    rw [hσd]; exact map_getD _ _ _ hi
  (expose_names;
    refine let c0:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat:= @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat)); let c5:Env:=Env.setVar σ "left.s" c4; let c6:String:=c2 ".n"; let c7:Nat:=Env.vars c5 "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat)); let c9:Env:=Env.setVar c5 "left.n" c8; let c10:String:=c2 ".d"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "left.d" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Expr:=Expr.get c3 (Expr.var "vec.i"); let c17:Nat:=c15 (Expr.size c16); let c18:Expr:=Expr.get c6 (Expr.var "vec.i"); let c19:Nat:=c15 (Expr.size c18); let c20:Expr:=Expr.get c10 (Expr.var "vec.i"); let c21:Nat:=c15 (Expr.size c20); let c22:Nat:=c14 c19 c21; let c23:Com:=Com.assign "left.n" c18; let c24:Com:=Com.assign "left.d" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (loadLeft a) σ σ' ((9:Nat))) (c1 σ')) c13 (@And.intro (Run B (loadLeft a) σ c13 ((9:Nat))) (c1 c13) (RunStep.mono B (loadLeft a) σ c13 (c14 c17 c22) ((9:Nat)) (RunStep.seq B (Com.assign "left.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "left.s" c16 c4 (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3955_0_0_0)) (?nAX_g3955_0_0_1) ?_)) (RunStep.seq B c23 c24 c5 c9 c13 c19 c21 (RunStep.assign B c5 "left.n" c18 c8 (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7 (RunStep.eval_var B c5 "vec.i" (?nAX_g3955_0_0_2)) (?nAX_g3955_0_0_3) ?_)) (RunStep.assign B c9 "left.d" c20 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g3955_0_0_4)) (?nAX_g3955_0_0_5) ?_)))) (?nAX_g3955_0_0_6)) ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case' nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [LeftOutput]

theorem storeReduced_spec (B:ℕ) (a:String) (qs:List ℚ) (q:ℚ) (i:ℕ)
    (hi:i < qs.length) (hB:1 < B) (hiB:i < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i∧ FractionOutput q σ)
      (storeReduced a) (fun _ τ => Represents a (qs.set i q) τ) 13:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi,hv,hratn,hratd,hrats⟩
  have hnB:σ.vars "rat.n" < B:=hratn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hratd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hrats.trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  have hns:=Ne.symm hsn
  have hds:=Ne.symm hsd
  have hdn:=Ne.symm hnd
  have hsign:=RamEncoding.fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hrats (hratd ▸ q.den_pos)
  rw [hv] at hsign
  change rationalSign q=_ at hsign
  (expose_names;
    refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=Represents a (@List.set Rat qs i q); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced a) σ σ' ((13:Nat))) (c3 σ'); let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c6:String:=c5 ".s"; let c7:Nat→ Env:=Env.setArr σ c6 (Env.vars σ "vec.i"); let c8:Env:=c7 ((0:Nat)); let c9:String:=c5 ".n"; let c10:String→ Nat:=Env.vars c8; let c11:Nat:=c10 "vec.i"; let c12:Nat:=c10 "rat.n"; let c13:Env:=Env.setArr c8 c9 c11 c12; let c14:String:=c5 ".d"; let c15:String→ Nat:=Env.vars c13; let c16:Nat:=c15 "vec.i"; let c17:Nat:=c15 "rat.d"; let c18:Env:=Env.setArr c13 c14 c16 c17; let c19:Nat→ Nat→ Nat:=Nat.add; let c20:Nat→ Nat:=c19 ((1:Nat)); let c21:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c22:Nat→ Nat:=c19 (c20 (Cond.size c21)); let c23:Nat→ Nat:=c19 (c20 (Expr.size (Expr.var "vec.i"))); let c24:Nat:=c23 (Expr.size (Expr.lit ((0:Nat)))); let c25:Nat:=c22 c24; let c26:Nat:=c23 (Expr.size (Expr.var "rat.n")); let c27:Nat:=c23 (Expr.size (Expr.var "rat.d")); let c28:Nat:=c19 c26 c27; let c29:Expr→ Com:=Com.store c6 (Expr.var "vec.i"); let c30:Com:=c29 (Expr.lit ((0:Nat))); let c31:Com:=c29 (Expr.var "rat.s"); let c32:Com:=Com.store c9 (Expr.var "vec.i") (Expr.var "rat.n"); let c33:Com:=Com.store c14 (Expr.var "vec.i") (Expr.var "rat.d"); let c34:Env:=c7 (Env.vars σ "rat.s"); let c35:String→ Nat:=Env.vars c34; let c36:Nat:=c35 "vec.i"; let c37:Nat:=c35 "rat.n"; let c38:Env:=Env.setArr c34 c9 c36 c37; let c39:String→ Nat:=Env.vars c38; let c40:Nat:=c39 "vec.i"; let c41:Nat:=c39 "rat.d"; let c42:Env:=Env.setArr c38 c14 c40 c41; let c43:Nat:=c23 (Expr.size (Expr.var "rat.s")); let c44:Nat:=c22 c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c18 (@And.intro (Run B (storeReduced a) σ c18 ((13:Nat))) (c3 c18) (RunStep.mono B (storeReduced a) σ c18 (c19 c25 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c8 c18 c25 c28 (RunStep.ite_true B c21 c30 c31 σ c8 c24 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_0)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.lit ((0:Nat))) (Env.vars σ "vec.i") ((0:Nat)) (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_2)) (?nAX_g3962_0_0_3))) (RunStep.seq B c32 c33 c8 c13 c18 c26 c27 (RunStep.store B c8 c9 (Expr.var "vec.i") (Expr.var "rat.n") c11 c12 (RunStep.eval_var B c8 "vec.i" (?nAX_g3962_0_0_4)) (RunStep.eval_var B c8 "rat.n" (?nAX_g3962_0_0_5)) (?nAX_g3962_0_0_6)) (RunStep.store B c13 c14 (Expr.var "vec.i") (Expr.var "rat.d") c16 c17 (RunStep.eval_var B c13 "vec.i" (?nAX_g3962_0_0_7)) (RunStep.eval_var B c13 "rat.d" (?nAX_g3962_0_0_8)) (?nAX_g3962_0_0_9)))) (?nAX_g3962_0_0_10)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c42 (@And.intro (Run B (storeReduced a) σ c42 ((13:Nat))) (c3 c42) (RunStep.mono B (storeReduced a) σ c42 (c19 c44 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c34 c42 c44 c28 (RunStep.ite_false B c21 c30 c31 σ c34 c43 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_11)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s") (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_12)) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g3962_0_0_13))) (RunStep.seq B c32 c33 c34 c38 c42 c26 c27 (RunStep.store B c34 c9 (Expr.var "vec.i") (Expr.var "rat.n") c36 c37 (RunStep.eval_var B c34 "vec.i" (?nAX_g3962_0_0_14)) (RunStep.eval_var B c34 "rat.n" (?nAX_g3962_0_0_15)) (?nAX_g3962_0_0_16)) (RunStep.store B c38 c14 (Expr.var "vec.i") (Expr.var "rat.d") c40 c41 (RunStep.eval_var B c38 "vec.i" (?nAX_g3962_0_0_17)) (RunStep.eval_var B c38 "rat.d" (?nAX_g3962_0_0_18)) (?nAX_g3962_0_0_19)))) (?nAX_g3962_0_0_20)) ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case' nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g3962_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRounding RationalArithmeticBounds

theorem fractionValue_flip (s n d:ℕ) (hs:s≤ 1):
    fractionValue (1 - s) n d=-fractionValue s n d:=by
  interval_cases s <;> simp [fractionValue,neg_div]

end Lax109476Proofs.RamFractionInterface

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem spec_with_fields {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars) (ha:c.warrs=[]):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  refine ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx), ?_⟩
  funext a
  exact hr.frame_arr a (by simp [ha])

end Lax109476Proofs.RamFrame

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram

def runOut (w:ℕ):ℕ→ Program→ State→ ℕ→ Option (List ℕ × ℕ)
  | 0,p,s,k => if s.pc < p.length then none else some (s.out,k)
  | fuel + 1,p,s,k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out,k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out,k)

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

theorem Fill.arr (h:Fill a x n i g F σ):σ.arrs a=arrOf n g:=h.1

theorem Fill.counter (h:Fill a x n i g F σ):σ.vars x=i:=h.2.1

theorem Fill.le (h:Fill a x n i g F σ):i≤ n:=h.2.2.1

theorem Fill.cell (h:Fill a x n i g F σ) (hj:j < i):g j=F j:=h.2.2.2 j hj

theorem Fill.length (h:Fill a x n i g F σ):(σ.arrs a).length=n:=by
  rw [h.arr,length_arrOf]

@[simp] theorem Fill.setVar_iff (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env)
    (y:String) (v:ℕ) (hy:y ≠ x):
    Fill a x n i g F (σ.setVar y v)↔ Fill a x n i g F σ:=by
  simp [Fill,Ne.symm hy]

theorem Fill.setVar (h:Fill a x n i g F σ) (hy:y ≠ x) (v:ℕ):
    Fill a x n i g F (σ.setVar y v):=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

theorem Fill.setCell (h:Fill a x n i g F σ) (v:ℕ):
    Fill a x n i (upd g i v) F (σ.setArr a i v):=
  ⟨by rw [arrs_setArr,if_pos rfl,h.arr,set_arrOf_eq_upd],by rw [vars_setArr,h.counter],
   h.2.2.1,fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

theorem Fill.bump (h:Fill a x n i g F σ) (hin:i < n) (hgi:g i=F i):
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)):=
  ⟨by rw [arrs_setVar,h.arr],by simp,hin,fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

namespace Fill

def Below (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ:Env):Prop:=
  ∃ g,Fill a x n (σ.vars x) g F σ

theorem Below.le (h:Below a x n F σ):σ.vars x≤ n:=by
  obtain ⟨_,hf⟩:=h; exact hf.le

theorem Below.length (h:Below a x n F σ):(σ.arrs a).length=n:=by
  obtain ⟨_,hf⟩:=h; exact hf.length

theorem below_zero (h:σ.arrs a=arrOf n g) (hx:σ.vars x=0):Below a x n F σ:=
  ⟨g,h,rfl,by omega,fun j hj => absurd hj (by omega)⟩

theorem Below.done (h:Below a x n F σ) (hx:σ.vars x=n):
    ∃ g,σ.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j:=by
  obtain ⟨g,hf⟩:=h
  exact ⟨g,hf.arr,fun j hj => hf.cell (by omega)⟩

theorem Below.step (h:Below a x n F σ) (hlt:σ.vars x < n) (hv:v=F (σ.vars x)):
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)):=by
  obtain ⟨g,hf⟩:=h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x=σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

@[simp] theorem wvars_put (a x:String) (e:Expr):(put a x e).wvars=[x]:=by
  simp [put,Com.wvars]

abbrev PutPost (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ σ':Env):Prop:=
  Below a x n F σ'∧ σ'.vars x=σ.vars x + 1

theorem put_spec (B n:ℕ) (a x:String) (e:Expr) (F:ℕ→ ℕ) (P:Env→ Prop)
    (hP:∀ σ,P σ→ Below a x n F σ∧ σ.vars x < n) (hnB:n < B)
    (he:∀ σ,P σ→ e.evalB B σ=some (F (σ.vars x))):
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size):=by
  intro σ hσ
  obtain ⟨hb,hlt⟩:=hP σ hσ
  obtain ⟨g,hf⟩:=hb
  refine ⟨_, (Run.seq (Run.store (idx:=σ.vars x) (v:=F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v:=σ.vars x + 1) ?_)).mono (by simp; omega), ?_,by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g,hf⟩ hlt rfl

theorem loop_spec (B n:ℕ) (a x m:String) (e:Expr) (F:ℕ→ ℕ)
    (hxm:x ≠ m) (hnB:n < B)
    (he:∀ σ,Below a x n F σ→ σ.vars m=n→ σ.vars x < n→
      e.evalB B σ=some (F (σ.vars x))):
    Spec B (fun σ => (∃ g,σ.arrs a=arrOf n g)∧ σ.vars m=n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g,σ'.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j)∧ σ'.vars x=n)
      ((10 + e.size) * n + 6):=by
  have hbody:Spec B (fun σ => (Below a x n F σ∧ σ.vars m=n)∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ'∧ σ'.vars m=n)∧ σ'.vars x=σ.vars x + 1)
      (6 + e.size):=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1,hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1,by rw [hq.2.1 m (by simp [Ne.symm hxm]),hσ.1.2]⟩,hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ∧ σ.vars m=n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g,harr⟩,hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp),by simp [Ne.symm hxm,hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2,hq.2⟩

namespace Demo

def demo (a x m:String):Com:=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

def demoWatched (a x m:String):Com:=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

def layout:Lax808846Proofs.Compile.Layout:= ⟨["i", "m"], ["ar"],2⟩

def prog:Lax808846.Ram.Program:=
  Lax808846Proofs.Compile.compileProgram layout (demoWatched "ar" "i" "m")

def demoRun:Option (List ℕ × ℕ):=runOut 16 1000 prog (Lax808846.Ram.initState []) 0

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem exists_arrOf (xs:List ℕ) (n:ℕ) (h:xs.length=n):∃ g,xs=arrOf n g:=by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf,List.getD_eq_getElem?_getD,hi]

theorem fillConstant_spec (B n v:ℕ) (a:String) (hnB:n < B) (hvB:v < B):
    Spec B (fun σ => (σ.arrs a).length=n∧ σ.vars "vec.n"=n) (fillConstant a v)
      (fun σ τ => τ.arrs a=List.replicate n v∧ τ.vars "vec.n"=n∧
        ∀ b ≠ a,τ.arrs b=σ.arrs b) (11 * n + 6):=by
  have hfill:=Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ,hr, ⟨g,hτg,hg⟩,_⟩:=hfill σ ⟨exists_arrOf _ _ hσ.1,hσ.2⟩
  refine ⟨τ,hr, ?_, ?_, ?_⟩
  · rw [hτg,replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put,Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put,Com.warrs,hb])

theorem zeroRationalArray_spec (B n:ℕ) (a:String) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ∧ τ.vars "vec.n"=n∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      (33 * n + 18):=by
  have h0:0 < B:=by omega
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  rintro σ ⟨hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτs,hτN,hτa⟩:=fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs,hσN⟩
  have hτn:(τ.arrs (a ++ ".n")).length=n:=by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ,hr₂,hυn,hυN,hυa⟩:=fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn,hτN⟩
  have hυd:(υ.arrs (a ++ ".d")).length=n:=by
    rw [hυa _ hnd.symm,hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ,hr₃,hρd,hρN,hρa⟩:=fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd,hυN⟩
  have hρs:ρ.arrs (a ++ ".s")=List.replicate n 0:=by rw [hρa _ hsd,hυa _ hsn,hτs]
  have hρn:ρ.arrs (a ++ ".n")=List.replicate n 0:=by rw [hρa _ hnd,hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_,hρN, ?_⟩
  · simp [Represents,hρs,hρn,hρd,rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n:ℕ} (v:Fin n→ ℚ):filled v 0=List.replicate n 0:=by simp [filled]

theorem filled_done {n:ℕ} (v:Fin n→ ℚ):filled v n=List.ofFn v:=by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

theorem filled_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    (filled v i.val).set i.val (v i)=filled v (i.val + 1):=by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkn:k < n:=by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki:i.val=k
    · have hfin:i=(⟨k,hkn⟩:Fin n):=Fin.ext hki
      simp [filled,hfin]
    · have hnext:k < i.val + 1↔ k < i.val:=by omega
      simp only [hki, ↓reduceIte,filled,List.getElem_ofFn]
      change (if k < i.val then v ⟨k,hkn⟩ else 0)=(if k < i.val + 1 then v ⟨k,hkn⟩ else 0)
      simp only [hnext]

end Lax109476Proofs.RamCenterUpdate

end

section

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "left.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "left.s")); let c7:Nat:=c5 (Expr.size (Expr.var "left.n")); let c8:Nat:=c5 (Expr.size (Expr.var "left.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B leftToResult σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c3 (@And.intro (Run B leftToResult σ c3 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c3) (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4081_0_0_0))) (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2 (RunStep.eval_var B c1 "left.d" (?nAX_g4081_0_0_1))))) (?nAX_g4081_0_0_2)) ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case' nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

end Lax109476Proofs.RamCopy

end

section

namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars

theorem load_spec (B:ℕ) (a:String) (xs:List ℚ) (i:ℕ) (hi:i < xs.length)
    (h1:1 < B) (hiB:i < B) (hn:xs[i].num.natAbs < B) (hd:xs[i].den < B):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "vec.i"=i) (load a)
      (fun _ τ => FractionOutput xs[i] τ) 15:=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=loadLeft_spec B a xs i hi h1 hiB hn hd σ hσ
  obtain ⟨υ,hr₂,hυ⟩:=RamCopy.leftToResult_spec B xs[i] h1 hn hd τ hτ
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

end Lax109476Proofs.RamArrayResult

end

section

namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

@[simp] theorem flatten_length {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ):
    (flatten A).length=m * n:=by simp [flatten]

theorem row_index_lt {m n:ℕ} (i:Fin m) (j:Fin n):i.val * n + j.val < m * n:=by
  have hmul:=Nat.mul_le_mul_right n i.isLt
  calc
    _ < i.val * n + n:=Nat.add_lt_add_left j.isLt _
    _=(i.val + 1) * n:=by ring
    _≤ _:=hmul

theorem flatten_entry {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (i:Fin m) (j:Fin n):
    (flatten A)[i.val * n + j.val]'(by simp; exact row_index_lt i j)=A i j:=by
  have hk:(⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [flatten,List.getElem_ofFn]
  change A ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).1)
    ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).2)=_
  rw [hk,Equiv.symm_apply_apply]

end Lax109476Proofs.RamMatrixStorage

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamMatrixStorage

theorem array_length_of_bigStep {c:Com} {σ τ:Env} {K:ℕ}
    (hr:BigStep c σ τ K) (b:String):(τ.arrs b).length=(σ.arrs b).length:=by
  induction hr with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem extents_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (b:String) (n:ℕ) (hσ:Extents b n σ):Extents b n τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  intro s hs
  rw [array_length_of_bigStep hstep]
  exact hσ s hs

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars
open RamBisectionCommit

def preserves (B:ℕ) (Q:Env→ Prop) (c:Com):Prop:=
  ∀ {σ τ k},Run B c σ τ k→ Q σ→ Q τ

end Lax109476Proofs.RamBisectionLoop

end

section

namespace Lax109476Proofs.RamCertificateSource

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def fields:List String:= ["source.m", "source.n"]
def arrays:List String:= ["source.A", "source.b", "source.c"]

theorem data_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (hσ:Data P σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):Data P τ:=by
  rcases hσ with ⟨hA,hb,hc,hm,hn⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hc hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn⟩

theorem data_setVar {m n:ℕ} (P:Program ℤ m n) (σ:Env) (v:String) (z:ℕ)
    (hv:v∉ fields) (hσ:Data P σ):Data P (σ.setVar v z):=by
  have hm:v ≠ "source.m" :=by intro h; subst v; simp [fields] at hv
  have hn:v ≠ "source.n" :=by intro h; subst v; simp [fields] at hv
  simpa [Data,Represents,arrs_setVar,vars_setVar,Ne.symm hm,Ne.symm hn] using hσ

end Lax109476Proofs.RamCertificateSource

end

section

namespace Lax109476Proofs.RamCertificateContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

def fields:List String:= ["source.m", "source.n", "system.m", "system.n"]

def Context {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (σ:Env):Prop:=
  RamCertificateSource.Data P σ∧ σ.vars "system.m"=r∧ σ.vars "system.n"=s

theorem context_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (hσ:Context P r s σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ c.warrs):
    Context P r s τ:=by
  exact ⟨RamCertificateSource.data_frame hr P hσ.1
      (fun a h => hf a (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) ha,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.1,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hσ.2.2⟩

theorem context_setVar {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (σ:Env) (v:String) (z:ℕ)
    (hv:v∉ fields) (hσ:Context P r s σ):Context P r s (σ.setVar v z):=by
  have hr:v ≠ "system.m" :=by intro h; subst v; simp [fields] at hv
  have hs:v ≠ "system.n" :=by intro h; subst v; simp [fields] at hv
  exact ⟨RamCertificateSource.data_setVar P σ v z
    (fun h => hv (by simp [RamCertificateSource.fields] at h; rcases h with rfl | rfl <;> simp [fields])) hσ.1,
    by simpa [vars_setVar,Ne.symm hr] using hσ.2.1,
    by simpa [vars_setVar,Ne.symm hs] using hσ.2.2⟩

theorem preserves_context (B:ℕ) {m n:ℕ} (P:Program ℤ m n) (r s:ℕ) (c:Com)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ c.warrs):
    RamBisectionLoop.preserves B (Context P r s) c:=fun hr hσ => context_frame hr P r s hσ hf ha

end Lax109476Proofs.RamCertificateContext

end

section

namespace Lax109476Proofs.RamBuildVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamCenterUpdate RamEllipsoidStep RationalArithmeticBounds

def Invariant {n:ℕ} (a:String) (v:Fin n→ ℚ) (Q:Env→ Prop) (σ:Env):Prop:=
  Q σ∧ Represents a (filled v (σ.vars "build.i")) σ∧
    σ.vars "build.i" ≤ n∧ σ.vars "build.count"=n

set_option maxHeartbeats 800000 in
theorem step_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Invariant a v Q σ∧ σ.vars "build.i" < n) (step a selector)
      (fun σ τ => Invariant a v Q τ∧ τ.vars "build.i"=σ.vars "build.i" + 1)
      (selectorCost + 19):=by
  rintro σ ⟨⟨hσQ,hσa,hσi,hσn⟩,hi⟩
  let i:Fin n:= ⟨σ.vars "build.i",hi⟩
  obtain ⟨τ,hr₁,hτQ,hτv⟩:=hselector i σ ⟨hσQ,rfl,hσn⟩
  have hτi:τ.vars "build.i"=i.val:=hr₁.frame_var _ hiFrame
  have hτa:Represents a (filled v i.val) τ:=RamReadBody.represents_frame _ _ hσa hr₁ haFrame
  have hiB:i.val < B:=i.isLt.trans hnB
  have hr₂:Run B (.assign "vec.i" (.var "build.i")) τ (τ.setVar "vec.i" i.val) 2:=
    Run.assign (by simpa only [hτi] using evalB_var (B:=B) (σ:=τ) (x:= "build.i") (hτi ▸ hiB))
  have hstore:=storeReduced_spec B a (filled v i.val) (v i) i.val
    (by simpa only [filled,List.length_ofFn] using i.isLt) h1 hiB
    ((hv i).1.trans_lt hMB) ((hv i).2.trans_lt hMB)
  obtain ⟨υ,hr₃,hυa⟩:=hstore (τ.setVar "vec.i" i.val)
    ⟨hτa,by simp,by simpa [FractionOutput,vars_setVar] using hτv⟩
  have hυQ:Q υ:=hQstore hr₃ (hQvec τ i.val hτQ)
  have hυi:υ.vars "build.i"=i.val:=
    (hr₃.frame_var _ (by simp [storeReduced,Com.wvars])).trans (by simpa using hτi)
  have hsumB:Bop.add.apply (υ.vars "build.i") 1 < B:=by simpa [hυi] using lt_of_le_of_lt i.isLt hnB
  have hr₄:Run B (.assign "build.i" (.add (.var "build.i") (.lit 1))) υ (υ.setVar "build.i" (i.val + 1)) 4:=
    Run.assign (by simpa only [hυi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "build.i") (hυi ▸ hiB)) (evalB_lit h1) hsumB))
  have hr:=(hr₁.seq (hr₂.seq hr₃)).seq hr₄
  have hfilled:Represents a (filled v (i.val + 1)) υ:=by rw [← filled_step]; exact hυa
  refine ⟨_,hr.mono (by omega), ⟨hQset υ (i.val + 1) hυQ, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change i.val + 1≤ n; exact i.isLt
  · exact (hr.frame_var _ (by simp [Com.wvars,storeReduced,hnFrame])).trans hσn
  · simp [i]

theorem loop_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Q σ∧ Represents a (List.replicate n 0) σ∧ σ.vars "build.count"=n)
      (loop a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 23) * n + 6):=by
  have hlo:=Spec.forRangeZero "build.i" "build.count" (Invariant a v Q) n (selectorCost + 19) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (step_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector hiFrame hnFrame haFrame hQstore hQset hQvec)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσQ,hσa,hσn⟩
    exact ⟨hQset σ 0 hσQ,by simpa only [Represents,arrs_setVar,vars_setVar,ite_true,filled_zero] using hσa,by simp,by simpa using hσn⟩
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨hτ.1,by simpa only [hcounter,filled_done] using hτ.2.1,hτ.2.2.2⟩

theorem build_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQzero:RamBisectionLoop.preserves B Q (RamZeroArray.zeroRationalArray a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t))
    (hQlength:∀ σ t,Q σ→ Q (σ.setVar "vec.n" t)):
    Spec B (fun σ => Q σ∧ Extents a n σ∧ σ.vars "build.count"=n)
      (build a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 56) * n + 26):=by
  rintro σ ⟨hσQ,hσa,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var "build.count")) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:= "build.count") (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτa,hτn,hτframe⟩:=RamZeroArray.zeroRationalArray_spec B n a hnB h1
    (σ.setVar "vec.n" n) ⟨hσa ".s" (by simp),hσa ".n" (by simp),hσa ".d" (by simp),by simp⟩
  have hτQ:=hQzero hr₂ (hQlength σ n hσQ)
  have hτcount:τ.vars "build.count"=n:=
    (hr₂.frame_var _ (by simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Com.wvars,Lib.Fill.put])).trans
      (by simpa using hσn)
  obtain ⟨υ,hr₃,hυ⟩:=loop_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector
    hiFrame hnFrame haFrame hQstore hQset hQvec τ ⟨hτQ,hτa,hτcount⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_,hυ⟩
  simp only [Nat.add_mul]
  omega

end Lax109476Proofs.RamBuildVector

end

section

namespace Lax109476Proofs.RamCertificateMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

def values {r s:ℕ} (F:Program ℤ r s):Fin (r * s)→ ℚ:=
  fun i => F.A i.divNat i.modNat

set_option maxHeartbeats 1000000 in
theorem selectCoordinate_spec (B m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hB:r * s + s + 4 < B)
    (hselector:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ selector.warrs)
    (i:Fin (r * s)):
    Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r * s)
      (selectCoordinate selector) (fun _ τ => Context P r s τ∧ FractionOutput (values F i) τ)
      (selectorCost + 14):=by
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hs:s < B:=by omega
  have hdiv:i.val / s < B:=(Nat.div_le_self _ _).trans_lt hiB
  have hmul:(i.val / s) * s < B:=(Nat.div_mul_le_self _ _).trans_lt hiB
  have hsub:i.val - (i.val / s) * s < B:=(Nat.sub_le _ _).trans_lt hiB
  have hmod:i.val - (i.val / s) * s=i.val % s:=by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x:=i.val) (k:=s)).symm
  have hsel:=hselector i.divNat i.modNat
  have hbase:Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r * s)
      (selectCoordinate selector) (fun _ τ => FractionOutput (values F i) τ) (selectorCost + 14):=by
    rintro σ ⟨⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσr,hσs⟩,hσi,hσcount⟩
    (expose_names;
      refine let c0:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "build.i") (Env.vars σ "system.n"); let c1:Env:=Env.setVar σ "query.row" c0; let c2:String→ Nat:=Env.vars c1; let c3:Nat:=c2 "build.i"; let c4:Nat:=c2 "query.row"; let c5:Nat:=c2 "system.n"; let c6:Nat:=Nat.mul c4 c5; let c7:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c3 c6; let c8:Env:=Env.setVar c1 "query.col" c7; let c9:Env→ Nat→ Prop:=Run B selector c8; let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int r s F (@Fin.divNat r s i) (@Fin.modNat r s i))); let c11:Env→ Prop:=fun (σ':Env) => And (c9 σ' selectorCost) (And (@RamCertificateSource.Data m n P σ') (c10 σ')); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat:=c12 selectorCost ((14:Nat)); let c14:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@values r s F i) τ) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B (selectCoordinate selector) σ σ' c13) (c14 σ'); let c16:Prop:= @Exists Env c15; let c17:String→ Nat:=Env.vars c8; let c18:Nat→ Nat:=c12 ((1:Nat)); let c19:Nat:=c18 (Expr.size (Expr.div (Expr.var "build.i") (Expr.var "system.n"))); let c20:Expr:=Expr.sub (Expr.var "build.i") (Expr.mul (Expr.var "query.row") (Expr.var "system.n")); let c21:Nat:=c18 (Expr.size c20); let c22:Nat:=c12 c21 selectorCost; let c23:Com:=Com.assign "query.col" c20; @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c16) (RunStep.use B (fun (σ:Env) => And (@RamCertificateSource.Data m n P σ) (And (@Eq Nat (Env.vars σ "query.row") (@Fin.val r (@Fin.divNat r s i))) (@Eq Nat (Env.vars σ "query.col") (@Fin.val s (@Fin.modNat r s i))))) selector (fun (x τ:Env) => And (@RamCertificateSource.Data m n P τ) (c10 τ)) selectorCost hsel c8 ?_) fun (w:Env) (h:And (c9 w selectorCost) (And (@RamCertificateSource.Data m n P w) (c10 w))) => let c0_1:Prop:=And (@RamCertificateSource.Data m n P w) (c10 w); @And.casesOn (c9 w selectorCost) c0_1 (fun (x:And (c9 w selectorCost) c0_1) => c16) h fun (left:c9 w selectorCost) (right:c0_1) => @Exists.intro Env c15 w (@And.intro (Run B (selectCoordinate selector) σ w c13) (c14 w) (RunStep.mono B (selectCoordinate selector) σ w (c12 c19 c22) c13 (RunStep.seq B (Com.assign "query.row" (Expr.div (Expr.var "build.i") (Expr.var "system.n"))) (Com.seq c23 selector) σ c1 w c19 c22 (RunStep.assign B σ "query.row" (Expr.div (Expr.var "build.i") (Expr.var "system.n")) c0 (RunStep.eval_div B σ (Expr.var "build.i") (Expr.var "system.n") (Env.vars σ "build.i") (Env.vars σ "system.n") (RunStep.eval_var B σ "build.i" (?nAX_g4423_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g4423_0_0_1)) ?_)) (RunStep.seq B c23 selector c1 c8 w c21 selectorCost (RunStep.assign B c1 "query.col" c20 c7 (RunStep.eval_sub B c1 (Expr.var "build.i") (Expr.mul (Expr.var "query.row") (Expr.var "system.n")) c3 c6 (RunStep.eval_var B c1 "build.i" (?nAX_g4423_0_0_2)) (RunStep.eval_mul B c1 (Expr.var "query.row") (Expr.var "system.n") c4 c5 (RunStep.eval_var B c1 "query.row" ?_) (RunStep.eval_var B c1 "system.n" (?nAX_g4423_0_0_3)) ?_) (?nAX_g4423_0_0_4))) left)) (?nAX_g4423_0_0_5)) ?_) <;> try dsimp +zetaDelta at *
     all_goals try dsimp +zetaDelta at *
     try case' nAX_g4423_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4423_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4423_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4423_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4423_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4423_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
    )
    all_goals clear hsel
    all_goals simp_all [values,Fin.divNat,Fin.modNat,RamCertificateSource.Data,Represents,arrs_setVar]
    all_goals omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,context_frame hr P r s hσ.1 ?_ ?_,hτ⟩
  · intro a ha'
    have haRow:a ≠ "query.row" :=by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    have haCol:a ≠ "query.col" :=by simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide
    simp [selectCoordinate,Com.wvars,haRow,haCol,hf a ha']
  · simpa [selectCoordinate,Com.warrs] using ha

set_option maxHeartbeats 1000000 in
theorem matrix_spec (B M m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hM:1≤ M) (hMB:M < B) (hB:r * s + r + s + 4 < B)
    (hA:∀ i j, (F.A i j).natAbs≤ M)
    (hselector:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (ha:∀ a∈ RamCertificateSource.arrays, ∀ t∈ RamCopy.suffixes,a ++ t∉ selector.warrs)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (htarget:∀ t∈ RamCopy.suffixes, "system.A" ++ t∉ selector.warrs):
    Spec B (fun σ => Context P r s σ∧ Extents "system.A" (r * s) σ) (matrix selector)
      (fun _ τ => Context P r s τ∧ Represents "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) τ)
      ((selectorCost + 70) * (r * s) + 34):=by
  have h1:1 < B:=by omega
  have hNB:r * s < B:=by omega
  have hbuild:=RamBuildVector.build_spec B M (r * s) (selectorCost + 14) "system.A" (values F)
    (selectCoordinate selector) (Context P r s) h1 hNB hMB
    (fun i => ⟨by simpa [values] using hA i.divNat i.modNat,by simpa [values] using hM⟩)
    (selectCoordinate_spec B m n r s selectorCost P F selector (by omega) hselector hf ha)
    (by simpa [selectCoordinate,Com.wvars] using hiFrame)
    (by simpa [selectCoordinate,Com.wvars] using hnFrame)
    (by simpa [selectCoordinate,Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.A")
      (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha' t ht
        simp [RamCertificateSource.arrays] at ha'
        simp [RamCopy.suffixes] at ht
        rcases ha' with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta:Spec B (fun σ => σ.vars "system.m"=r∧ σ.vars "system.n"=s) prepare
      (fun _ τ => τ.vars "build.count"=r * s) 4:=by
    rintro σ ⟨hr,hs⟩
    (expose_names;
      refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 r s; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "build.count") c1) σ; let c3:Nat:=c0 (Env.vars σ "system.m") (Env.vars σ "system.n"); let c4:Env:=Env.setVar σ "build.count" c3; @Exists.intro Env (fun (σ':Env) => And (Run B prepare σ σ' ((4:Nat))) (c2 σ')) c4 (@And.intro (Run B prepare σ c4 ((4:Nat))) (c2 c4) (RunStep.mono B prepare σ c4 (Nat.add ((1:Nat)) (Expr.size (Expr.mul (Expr.var "system.m") (Expr.var "system.n")))) ((4:Nat)) (RunStep.assign B σ "build.count" (Expr.mul (Expr.var "system.m") (Expr.var "system.n")) c3 (RunStep.eval_mul B σ (Expr.var "system.m") (Expr.var "system.n") (Env.vars σ "system.m") (Env.vars σ "system.n") (RunStep.eval_var B σ "system.m" (?nAX_g4426_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g4426_0_0_1)) ?_)) (?nAX_g4426_0_0_2)) ?_) <;> try dsimp +zetaDelta at *
     all_goals try dsimp +zetaDelta at *
     try case' nAX_g4426_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4426_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g4426_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
    )
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hσContext,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ hσContext.2
  have hτContext:=context_frame hr₁ P r s hσContext
    (by intro a ha'; simp [fields] at ha'; rcases ha' with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha' t ht; simp [prepare,Com.warrs])
  obtain ⟨υ,hr₂,hυContext,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσtarget,hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυContext, ?_⟩
  · simp only [Nat.add_assoc,Nat.reduceAdd]; omega
  · exact hυtarget

end Lax109476Proofs.RamCertificateMatrix

end

section

namespace Lax109476Proofs.RamCertificateBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

theorem selectCoordinate_spec (B m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (hrB:r < B)
    (hselector:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars) (i:Fin r):
    Spec B (fun σ => Context P r s σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=r)
      (selectCoordinate selector) (fun _ τ => Context P r s τ∧ FractionOutput (F.b i:ℚ) τ)
      (selectorCost + 2):=by
  rintro σ ⟨hσContext,hσi,hσcount⟩
  have hr₁:Run B (.assign "query.row" (.var "build.i")) σ (σ.setVar "query.row" i.val) 2:=
    Run.assign (by simpa only [hσi] using evalB_var (B:=B) (σ:=σ) (x:= "build.i") (hσi ▸ i.isLt.trans hrB))
  have hτContext:=context_setVar P r s σ "query.row" i.val (by decide) hσContext
  obtain ⟨υ,hr₂,hυData,hυq⟩:=hselector i (σ.setVar "query.row" i.val) ⟨hτContext.1,by simp⟩
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ⟨hυData, ?_, ?_⟩,hυq⟩
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.1
  · exact (hr₂.frame_var _ (hf _ (by simp [fields]))).trans hτContext.2.2

set_option maxHeartbeats 1000000 in
theorem buildBound_spec (B M m n r s selectorCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (selector:Com) (h1:1 < B) (hMB:M < B) (hrB:r < B)
    (hb:∀ i,Height (F.b i:ℚ) M)
    (hselector:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      selector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) selectorCost)
    (hf:∀ a∈ fields,a∉ selector.wvars)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (htarget:∀ t∈ RamCopy.suffixes, "system.b" ++ t∉ selector.warrs):
    Spec B (fun σ => Context P r s σ∧ Extents "system.b" r σ) (buildBound selector)
      (fun _ τ => Context P r s τ∧ Represents "system.b" (List.ofFn (rationalProgram F).b) τ)
      ((selectorCost + 58) * r + 28):=by
  have hbuild:=RamBuildVector.build_spec B M r (selectorCost + 2) "system.b" (rationalProgram F).b
    (selectCoordinate selector) (Context P r s) h1 hrB hMB hb
    (selectCoordinate_spec B m n r s selectorCost P F selector hrB hselector hf)
    (by simpa [selectCoordinate,Com.wvars] using hiFrame)
    (by simpa [selectCoordinate,Com.wvars] using hnFrame)
    (by simpa [selectCoordinate,Com.warrs] using htarget)
    (preserves_context B P r s (storeReduced "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (preserves_context B P r s (RamZeroArray.zeroRationalArray "system.b")
      (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
      (by
        intro a ha t ht
        simp [RamCertificateSource.arrays] at ha
        simp [RamCopy.suffixes] at ht
        rcases ha with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;> decide))
    (fun σ z h => context_setVar P r s σ "build.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.i" z (by decide) h)
    (fun σ z h => context_setVar P r s σ "vec.n" z (by decide) h)
  have hmeta:Spec B (fun σ => σ.vars "system.m"=r) prepare
      (fun _ τ => τ.vars "build.count"=r) 2:=by
    intro σ hr
    refine ⟨σ.setVar "build.count" r, ?_,by simp⟩
    exact Run.assign (by simpa only [hr] using evalB_var (B:=B) (σ:=σ) (x:= "system.m") (hr ▸ hrB))
  rintro σ ⟨hσContext,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ hσContext.2.1
  have hτContext:=context_frame hr₁ P r s hσContext
    (by intro a ha; simp [fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha t ht; simp [prepare,Com.warrs])
  obtain ⟨υ,hr₂,hυContext,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.b" r hσtarget,hτcount⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hυContext,hυtarget⟩

end Lax109476Proofs.RamCertificateBound

end

section

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp [FractionOutput,fractionValue]

end Lax109476Proofs.RamPadSelector

end

section

namespace Lax109476Proofs.RamResultNegation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface

theorem negateResult_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (FractionOutput q) negateResult (fun _ τ => FractionOutput (-q) τ) 4:=by
  rintro σ ⟨hval,hn,hd,hs⟩
  have hsB:σ.vars "rat.s" < B:=hs.trans_lt h1
  have hflip:=fractionValue_flip (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") hs
  rw [hval] at hflip
  (expose_names;
    refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negateResult σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negateResult σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negateResult σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g4454_0_0_0))) (?nAX_g4454_0_0_1)) ?_) <;> try dsimp +zetaDelta at *
   all_goals try dsimp +zetaDelta at *
   try case' nAX_g4454_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
   try case' nAX_g4454_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
  )
  all_goals simp_all [FractionOutput]

end Lax109476Proofs.RamResultNegation

end

section

namespace Lax109476Proofs.RamCertificateBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds IntegerEncoding RamEllipsoidStep
open RamCertificateContext

set_option maxHeartbeats 1000000 in
theorem buildSystem_spec (B M m n r s matrixCost boundCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (matrixSelector boundSelector:Com) (hM:1≤ M) (hMB:M < B)
    (hB:r * s + r + s + 4 < B)
    (hA:∀ i j, (F.A i j).natAbs≤ M) (hb:∀ i, (F.b i).natAbs≤ M)
    (hMatrix:∀ i j,Spec B
      (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      matrixSelector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.A i j:ℚ) τ) matrixCost)
    (hBound:∀ i,Spec B (fun σ => RamCertificateSource.Data P σ∧ σ.vars "query.row"=i.val)
      boundSelector (fun _ τ => RamCertificateSource.Data P τ∧ FractionOutput (F.b i:ℚ) τ) boundCost)
    (hfm:∀ a∈ fields,a∉ matrixSelector.wvars)
    (hfb:∀ a∈ fields,a∉ boundSelector.wvars)
    (him:"build.i" ∉ matrixSelector.wvars) (hnm:"build.count" ∉ matrixSelector.wvars)
    (hib:"build.i" ∉ boundSelector.wvars) (hnb:"build.count" ∉ boundSelector.wvars)
    (ham:matrixSelector.warrs=[]) (hab:boundSelector.warrs=[]):
    Spec B (fun σ => Context P r s σ∧ Extents "system.A" (r * s) σ∧ Extents "system.b" r σ)
      (buildSystem matrixSelector boundSelector)
      (fun _ τ => RamCertificateSource.Data P τ∧ RamEquationData.Data F τ)
      ((matrixCost + 70) * (r * s) + (boundCost + 58) * r + 62):=by
  have h1:1 < B:=by omega
  have hm:=RamCertificateMatrix.matrix_spec B M m n r s matrixCost P F matrixSelector hM hMB hB hA hMatrix hfm
    (by intro a ha t ht; rw [ham]; simp) him hnm (by intro t ht; rw [ham]; simp)
  have hbound:=RamCertificateBound.buildBound_spec B M m n r s boundCost P F boundSelector h1 hMB (by omega)
    (fun i => ⟨by simpa using hb i,by simpa using hM⟩) hBound hfb hib hnb
    (by intro t ht; rw [hab]; simp)
  rintro σ ⟨hσContext,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτContext,hτA⟩:=hm σ ⟨hσContext,hσA⟩
  obtain ⟨υ,hr₂,hυContext,hυb⟩:=hbound τ
    ⟨hτContext,RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  have hυA:=RamReadBody.represents_frame "system.A" (RamMatrixStorage.flatten (rationalProgram F).A) hτA hr₂
    (by
      intro t ht
      simp [RamCopy.suffixes] at ht
      rcases ht with rfl | rfl | rfl
      all_goals simp [RamCertificateBound.buildBound,RamCertificateBound.prepare,RamCertificateBound.selectCoordinate,
        RamBuildVector.build,RamBuildVector.loop,RamBuildVector.step,RamBuildVector.coordinate,
        RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,storeReduced,Com.warrs,hab])
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυContext.1,hυA,hυb,hυContext.2⟩

end Lax109476Proofs.RamCertificateBuilder

end

section

namespace Lax109476Proofs.RamCertificateMetadata

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamCertificateSource RamCertificateContext

theorem unbounded_spec (B m n:ℕ) (P:Program ℤ m n) (hB:2 * m + 2 * n + 4 < B):
    Spec B (Data P) unbounded (fun _ τ => Context P (m + (m + 1)) (n + n) τ) 12:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hm1:m + 1 < B:=by omega
  have hr:m + (m + 1) < B:=by omega
  have hs:n + n < B:=by omega
  have hbase:Spec B (fun σ => σ.vars "source.m"=m∧ σ.vars "source.n"=n) unbounded
      (fun _ τ => τ.vars "system.m"=m + (m + 1)∧ τ.vars "system.n"=n + n) 12:=by
    rintro σ ⟨hσm,hσn⟩
    (expose_names;
      refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 m; let c2:Nat:=c1 (c1 ((1:Nat))); let c3:Nat:=c0 n n; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "system.m") c2) (@Eq Nat (Env.vars τ "system.n") c3)) σ; let c5:Nat→ Nat:=c0 (Env.vars σ "source.m"); let c6:Nat:=c5 ((1:Nat)); let c7:Nat:=c5 c6; let c8:Env:=Env.setVar σ "system.m" c7; let c9:Nat:=Env.vars c8 "source.n"; let c10:Nat:=c0 c9 c9; let c11:Env:=Env.setVar c8 "system.n" c10; let c12:Nat→ Nat:=c0 ((1:Nat)); let c13:Expr:=Expr.add (Expr.var "source.m") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.add (Expr.var "source.m") c13; let c15:Nat:=c12 (Expr.size c14); let c16:Nat:=c12 (Expr.size (Expr.add (Expr.var "source.n") (Expr.var "source.n"))); let c17:String→ Nat:=Env.vars c11; @Exists.intro Env (fun (σ':Env) => And (Run B unbounded σ σ' ((12:Nat))) (c4 σ')) c11 (@And.intro (Run B unbounded σ c11 ((12:Nat))) (c4 c11) (RunStep.mono B unbounded σ c11 (c0 c15 c16) ((12:Nat)) (RunStep.seq B (Com.assign "system.m" c14) (Com.assign "system.n" (Expr.add (Expr.var "source.n") (Expr.var "source.n"))) σ c8 c11 c15 c16 (RunStep.assign B σ "system.m" c14 c7 (RunStep.eval_add B σ (Expr.var "source.m") c13 (Env.vars σ "source.m") c6 (RunStep.eval_var B σ "source.m" (?nAX_g5021_0_0_0)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.lit ((1:Nat))) (Env.vars σ "source.m") ((1:Nat)) (RunStep.eval_var B σ "source.m" (?nAX_g5021_0_0_1)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5021_0_0_2)) (?nAX_g5021_0_0_3))) (RunStep.assign B c8 "system.n" (Expr.add (Expr.var "source.n") (Expr.var "source.n")) c10 (RunStep.eval_add B c8 (Expr.var "source.n") (Expr.var "source.n") c9 c9 (RunStep.eval_var B c8 "source.n" (?nAX_g5021_0_0_4)) (RunStep.eval_var B c8 "source.n" (?nAX_g5021_0_0_5)) (?nAX_g5021_0_0_6)))) (?nAX_g5021_0_0_7)) ?_) <;> try dsimp +zetaDelta at *
     all_goals try dsimp +zetaDelta at *
     try case' nAX_g5021_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5021_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
    )
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ ⟨hσ.2.2.2.1,hσ.2.2.2.2⟩
  refine ⟨τ,hr,data_frame hr P hσ ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t∉ ([]:List String); simp

end Lax109476Proofs.RamCertificateMetadata

end

section

namespace Lax109476Proofs.RamCertificateLoad

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

def loadFields:List String:= ["source.m", "source.n", "query.row", "query.col", "query.a.row", "query.a.col", "certificate.kind"]

set_option maxHeartbeats 800000 in
theorem matrix_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin m) (j:Fin n)
    (hM:1≤ M) (hMB:M < B) (hB:m * n + m + n + 4 < B) (hq:(P.A i j).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val∧ σ.vars "query.a.col"=j.val) matrix
      (fun _ τ => Data P τ∧ FractionOutput (P.A i j:ℚ) τ) 21:=by
  have h1:1 < B:=by omega
  have hi:i.val < B:=i.isLt.trans (by omega)
  have hj:j.val < B:=j.isLt.trans (by omega)
  have hn:n < B:=by omega
  let index:=i.val * n + j.val
  have hindex:index < (RamMatrixStorage.flatten (rationalProgram P).A).length:=by
    simpa [RamMatrixStorage.flatten,index] using RamMatrixStorage.row_index_lt i j
  have hindexB:index < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hindex:index < m * n).trans (by omega)
  have hmul:i.val * n < B:=by dsimp only [index] at hindexB; omega
  have he:(RamMatrixStorage.flatten (rationalProgram P).A)[index]=(P.A i j:ℚ):=
    RamMatrixStorage.flatten_entry (rationalProgram P).A i j
  have hqH:Height (P.A i j:ℚ) M:= ⟨by simpa using hq,by simpa using hM⟩
  have hload:=spec_with_fields loadFields
    (RamArrayResult.load_spec B "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) index hindex h1 hindexB
      (by rw [he]; exact hqH.1.trans_lt hMB) (by rw [he]; exact hqH.2.trans_lt hMB))
    (by intro a ha; simp [loadFields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val∧ σ.vars "query.a.col"=j.val) matrix
      (fun _ τ => FractionOutput (P.A i j:ℚ) τ) 21:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσi,hσj⟩
    (expose_names;
      refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=Nat.mul (Env.vars σ "query.a.row") (Env.vars σ "source.n"); let c2:Nat:=c0 c1 (Env.vars σ "query.a.col"); let c3:Env:=Env.setVar σ "vec.i" c2; let c4:Env→ Nat→ Prop:=Run B (RamArrayResult.load "source.A") c3; let c5:List Rat:= @RamMatrixStorage.flatten m n (@Program.A Rat m n (@rationalProgram m n P)); let c6:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c5 index hindex); let c7:Env→ Prop:=FieldsAgree loadFields c3; let c8:String→ List Nat:=Env.arrs c3; let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((15:Nat))) (And (c6 σ') (And (c7 σ') (@Eq (String→ List Nat) (Env.arrs σ') c8))); let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int m n P i j)); let c11:Env→ Prop:=(fun (x τ:Env) => c10 τ) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B matrix σ σ' ((21:Nat))) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Env→ Prop:=Represents "source.A" c5; let c15:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c16:Nat:=c0 ((1:Nat)) (Expr.size c15); @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c13) (RunStep.use B (fun (σ:Env) => And (c14 σ) (@Eq Nat (Env.vars σ "vec.i") index)) (RamArrayResult.load "source.A") (fun (σ τ:Env) => And (c6 τ) (And (FieldsAgree loadFields σ τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ)))) ((15:Nat)) hload c3 ?_) fun (w:Env) (h:And (c4 w ((15:Nat))) (And (c6 w) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) c8)))) => let c0_1:Prop:=c4 w ((15:Nat)); let c1_1:Prop:=And (c6 w) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) c8)); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c12 w (@And.intro (Run B matrix σ w ((21:Nat))) (c11 w) (RunStep.mono B matrix σ w (c0 c16 ((15:Nat))) ((21:Nat)) (RunStep.seq B (Com.assign "vec.i" c15) (RamArrayResult.load "source.A") σ c3 w c16 ((15:Nat)) (RunStep.assign B σ "vec.i" c15 c2 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c1 (Env.vars σ "query.a.col") (RunStep.eval_mul B σ (Expr.var "query.a.row") (Expr.var "source.n") (Env.vars σ "query.a.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.a.row" (?nAX_g5024_0_0_0)) (RunStep.eval_var B σ "source.n" (?nAX_g5024_0_0_1)) ?_) (RunStep.eval_var B σ "query.a.col" (?nAX_g5024_0_0_2)) ?_)) left) (?nAX_g5024_0_0_3)) ?_) <;> try dsimp +zetaDelta at *
     all_goals try dsimp +zetaDelta at *
     try case' nAX_g5024_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5024_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5024_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5024_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
    )
    all_goals clear hload
    all_goals simp_all [loadFields,FieldsAgree,Represents,index]
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

theorem vector_wvars (a:String):(vector a).wvars=(vector "").wvars:=by rfl

theorem vector_spec (B m n r:ℕ) (P:Program ℤ m n) (a:String) (v:Fin r→ ℚ) (i:Fin r)
    (h1:1 < B) (hi:i.val < B) (hn:(v i).num.natAbs < B) (hd:(v i).den < B):
    Spec B (fun σ => Data P σ∧ Represents a (List.ofFn v) σ∧ σ.vars "query.a.row"=i.val) (vector a)
      (fun _ τ => Data P τ∧ FractionOutput (v i) τ) 17:=by
  have hload:=RamArrayResult.load_spec B a (List.ofFn v) i.val (by simpa using i.isLt) h1 hi
    (by simpa using hn) (by simpa using hd)
  have hbase:Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "query.a.row"=i.val) (vector a)
      (fun _ τ => FractionOutput (v i) τ) 17:=by
    rintro σ ⟨hσa,hσi⟩
    (expose_names;
      refine let c0:Env→ Nat→ Prop:=Run B (RamArrayResult.load a) (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")); let c1:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) (@List.ofFn Rat r v) (@Fin.val r i) (?nAX_g5027_0_0_0)); let c2:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((15:Nat))) (c1 σ'); let c3:Env→ Prop:=(fun (x τ:Env) => FractionOutput (v i) τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (vector a) σ σ' ((17:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 ((1:Nat)) (Expr.size (Expr.var "query.a.row")); @Exists.casesOn Env c2 (fun (x:@Exists Env c2) => c5) (RunStep.use B (fun (σ:Env) => And (Represents a (@List.ofFn Rat r v) σ) (@Eq Nat (Env.vars σ "vec.i") (@Fin.val r i))) (RamArrayResult.load a) (fun (x τ:Env) => c1 τ) ((15:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) ?_) fun (w:Env) (h:And (c0 w ((15:Nat))) (c1 w)) => let c0:Prop:=c0 w ((15:Nat)); @And.casesOn c0 (c1 w) (fun (x:And c0 (c1 w)) => c5) h fun (left:c0) (right:c1 w) => @Exists.intro Env c4 w (@And.intro (Run B (vector a) σ w ((17:Nat))) (c3 w) (RunStep.mono B (vector a) σ w (c6 c7 ((15:Nat))) ((17:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load a) σ (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) w c7 ((15:Nat)) (RunStep.assign B σ "vec.i" (Expr.var "query.a.row") (Env.vars σ "query.a.row") (RunStep.eval_var B σ "query.a.row" (?nAX_g5027_0_0_1))) left) (?nAX_g5027_0_0_2)) ?_) <;> try dsimp +zetaDelta at *
     all_goals try dsimp +zetaDelta at *
     try case' nAX_g5027_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5027_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
     try case' nAX_g5027_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
    )
    all_goals clear hload
    all_goals simp_all [Represents,arrs_setVar]
  rintro σ ⟨hσData,hσa,hσi⟩
  obtain ⟨τ,hr,hτ⟩:=hbase σ ⟨hσa,hσi⟩
  refine ⟨τ,hr,data_frame hr P hσData ?_ ?_,hτ⟩
  · intro f hf; rw [vector_wvars]; simp [RamCertificateSource.fields] at hf; rcases hf with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

theorem bound_spec (B m n:ℕ) (P:Program ℤ m n) (i:Fin m)
    (h1:1 < B) (hi:i.val < B) (hn:(P.b i).natAbs < B):
    Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val) (vector "source.b")
      (fun _ τ => Data P τ∧ FractionOutput (P.b i:ℚ) τ) 17:=by
  exact (vector_spec B m n m P "source.b" (rationalProgram P).b i h1 hi
    (by simpa [rationalProgram] using hn) (by simpa [rationalProgram] using h1)).pre
      (fun _ h => ⟨h.1,h.1.2.1,h.2⟩)

theorem objective_spec (B m n:ℕ) (P:Program ℤ m n) (i:Fin n)
    (h1:1 < B) (hi:i.val < B) (hn:(P.c i).natAbs < B):
    Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val) (vector "source.c")
      (fun _ τ => Data P τ∧ FractionOutput (P.c i:ℚ) τ) 17:=by
  exact (vector_spec B m n n P "source.c" (rationalProgram P).c i h1 hi
    (by simpa [rationalProgram] using hn) (by simpa [rationalProgram] using h1)).pre
      (fun _ h => ⟨h.1,h.1.2.2.1,h.2⟩)

end Lax109476Proofs.RamCertificateLoad

end

section

namespace Lax109476Proofs.CertificateFamilyEntries

open Lax109476.LinearProgram
open CertificateFamilyPrograms IntegerCertificates CertificateSearch IndexedPointRecovery

def rayEntry {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))) (j:Fin (n + n)):ℤ:=
  if hi:i.val < m then
    if hj:j.val < n then P.A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else if hir:i.val < m + m then
    if hj:j.val < n then 0 else P.A ⟨i.val - m,by omega⟩ ⟨j.val - n,by omega⟩
  else if hj:j.val < n then 0 else -P.c ⟨j.val - n,by omega⟩

def rayRhs {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))):ℤ:=
  if hi:i.val < m then P.b ⟨i.val,hi⟩ else if i.val < m + m then 0 else -1

theorem rayEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))) (j:Fin (n + n)):
    rayEntry P i j=(unbounded P).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,i.isLt,j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,i.isLt,j.isLt]
      all_goals omega
    · have hi:i=0:=Subsingleton.elim _ _
      subst i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,unitFin,j.isLt,Nat.add_assoc]
      all_goals omega

theorem rayRhs_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))):
    rayRhs P i=(unbounded P).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [rayRhs,unbounded,reindexProgram,rayRows,rayBound,i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat,rayRhs,unbounded,reindexProgram,rayRows,rayBound,i.isLt]
    · have hi:i=0:=Subsingleton.elim _ _
      subst i
      simp [-Fin.natAdd_eq_addNat,rayRhs,unbounded,reindexProgram,rayRows,rayBound,unitFin]

end Lax109476Proofs.CertificateFamilyEntries

end

section

namespace Lax109476Proofs.RamRaySelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

set_option maxHeartbeats 1200000 in
theorem selectEntry_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + (m + 1))) (j:Fin (n + n))
    (hM:1≤ M) (hMB:M < B) (hB:m * n + 2 * m + 2 * n + 8 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M) (hc:∀ s, (P.c s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.rayEntry P i j:ℚ) τ) 64:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hmm:m + m < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hisub:i.val - m < B:=(Nat.sub_le _ _).trans_lt hiB
  have hjsub:j.val - n < B:=(Nat.sub_le _ _).trans_lt hjB
  have hz:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => FractionOutput (CertificateFamilyEntries.rayEntry P i j:ℚ) τ) 64:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσrow,hσcol⟩
    by_cases hi:i.val < m
    · by_cases hj:j.val < n
      · let ii:Fin m:= ⟨i.val,hi⟩
        let jj:Fin n:= ⟨j.val,hj⟩
        have hload:=RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj)
        (expose_names;
          refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c6:Prop:=Not c5; let c7:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c8:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c7; let c9:Env→ Nat→ Prop:=Run B RamCertificateLoad.matrix c8; let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int m n P ii jj)); let c11:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((21:Nat))) (And (@Data m n P σ') (c10 σ')); let c12:String→ Nat:=Env.vars c8; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c16:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c17:Nat:=c14 (Expr.size (Expr.var "query.row")); let c18:Nat:=c14 (Expr.size (Expr.var "query.col")); let c19:Nat:=c13 c18 ((21:Nat)); let c20:Nat:=c13 c17 c19; let c21:Nat:=c16 c20; let c22:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c23:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))); let c24:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c25:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c26:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c27:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c28:Com:=Com.seq c27 RamCertificateLoad.matrix; let c29:Com:=Com.seq c26 c28; let c30:Com:=c25 c29; let c31:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c32:Com:=Com.seq c31 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c33:Com:=c25 c32; let c34:Com:=Com.ite c24 c30 c33; let c35:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c36:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c37:Env→ Prop:=fun (σ':Env) => And (c35 σ' ((6:Nat))) (c36 σ'); let c38:Nat:=c16 ((6:Nat)); let c39:Nat:=c13 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c40:Prop:=Nat.lt (Env.vars σ "query.row") c39; let c41:Prop:=Not c40; let c42:Nat→ Nat:=c13 (c14 (Cond.size c24)); let c43:Nat:=c42 c38; let c44:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c45:Nat:=c44 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c46:Env:=Env.setVar σ "query.a.row" c45; let c47:String→ Nat:=Env.vars c46; let c48:Nat:=c47 "query.col"; let c49:Nat:=c47 "source.n"; let c50:Nat:=c44 c48 c49; let c51:Env:=Env.setVar c46 "query.a.col" c50; let c52:Env→ Nat→ Prop:=Run B RamCertificateLoad.matrix c51; let c53:Env→ Prop:=fun (σ':Env) => And (c52 σ' ((21:Nat))) (And (@Data m n P σ') (c10 σ')); let c54:String→ Nat:=Env.vars c51; let c55:Nat:=c14 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c56:Nat:=c14 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c57:Nat→ Nat:=c13 c56; let c58:Nat:=c57 ((21:Nat)); let c59:Nat:=c13 c55 c58; let c60:Nat:=c16 c59; let c61:Nat:=c42 c60; let c62:Nat:=c44 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c63:Env:=Env.setVar σ "query.a.row" c62; let c64:Nat:=Env.vars c63 "query.a.row"; let c65:Env:=Env.setVar c63 "vec.i" c64; let c66:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.c"; let c67:String:=c66 ".s"; let c68:Nat:=Env.vars c65 "vec.i"; let c69:Nat:= @List.getD Nat (Env.arrs c65 c67) c68 ((0:Nat)); let c70:Env:=Env.setVar c65 "left.s" c69; let c71:String:=c66 ".n"; let c72:Nat:=Env.vars c70 "vec.i"; let c73:Nat:= @List.getD Nat (Env.arrs c70 c71) c72 ((0:Nat)); let c74:Env:=Env.setVar c70 "left.n" c73; let c75:String:=c66 ".d"; let c76:Nat:=Env.vars c74 "vec.i"; let c77:Nat:= @List.getD Nat (Env.arrs c74 c75) c76 ((0:Nat)); let c78:Env:=Env.setVar c74 "left.d" c77; let c79:Nat:=Env.vars c78 "left.s"; let c80:Env:=Env.setVar c78 "rat.s" c79; let c81:Nat:=Env.vars c80 "left.n"; let c82:Env:=Env.setVar c80 "rat.n" c81; let c83:Nat:=Env.vars c82 "left.d"; let c84:Env:=Env.setVar c82 "rat.d" c83; let c85:Nat:=Env.vars c84 "rat.s"; let c86:Nat:=c44 ((1:Nat)) c85; let c87:Env:=Env.setVar c84 "rat.s" c86; let c88:Nat:=c14 (Expr.size (Expr.var "query.a.row")); let c89:Expr:=Expr.get c67 (Expr.var "vec.i"); let c90:Nat:=c14 (Expr.size c89); let c91:Expr:=Expr.get c71 (Expr.var "vec.i"); let c92:Nat:=c14 (Expr.size c91); let c93:Expr:=Expr.get c75 (Expr.var "vec.i"); let c94:Nat:=c14 (Expr.size c93); let c95:Nat:=c13 c92 c94; let c96:Nat:=c13 c90 c95; let c97:Nat:=c14 (Expr.size (Expr.var "left.s")); let c98:Nat:=c14 (Expr.size (Expr.var "left.n")); let c99:Nat:=c14 (Expr.size (Expr.var "left.d")); let c100:Nat:=c13 c98 c99; let c101:Nat:=c13 c97 c100; let c102:Nat:=c13 c96 c101; let c103:Nat:=c13 c88 c102; let c104:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c105:Nat:=c14 (Expr.size c104); let c106:Nat:=c13 c103 c105; let c107:Nat:=c57 c106; let c108:Nat:=c16 c107; let c109:Nat:=c42 c108; let c110:Com:=Com.assign "left.n" c91; let c111:Com:=Com.assign "left.d" c93; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_1:c5) => @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (And (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val m ii)) (@Eq Nat (Env.vars σ "query.a.col") (@Fin.val n jj)))) RamCertificateLoad.matrix (fun (x τ:Env) => And (@Data m n P τ) (c10 τ)) ((21:Nat)) hload c8 ?_) fun (w:Env) (h:And (c9 w ((21:Nat))) (And (@Data m n P w) (c10 w))) => let c0:Prop:=c9 w ((21:Nat)); let c1:Prop:=And (@Data m n P w) (c10 w); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c21) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c21 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))) σ w c20 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) w c17 c19 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c8 w c18 ((21:Nat)) (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c7 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_0_0_5))) left)))) (?nAX_g5054_0_0_6)) ?_)) fun (hcase_1:c6) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c38) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c38 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_7)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_8)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_9)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_10)) hcase_1) left)) (?nAX_g5054_0_0_11)) ?_)) fun (hcase:c1) => @Or.casesOn c40 c41 (fun (x:Or c40 c41) => @Exists Env c4) (Classical.em c40) (fun (hcase_1:c40) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c43) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c43 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_12)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_13)) hcase) (RunStep.ite_true B c24 c30 c33 σ w c38 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_14)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_15)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_16)) (?nAX_g5054_0_0_17)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c29 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_18)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_19)) hcase_2) left))) (?nAX_g5054_0_0_20)) ?_)) fun (hcase_2:c6) => @Exists.casesOn Env c53 (fun (x:@Exists Env c53) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (And (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val m ii)) (@Eq Nat (Env.vars σ "query.a.col") (@Fin.val n jj)))) RamCertificateLoad.matrix (fun (x τ:Env) => And (@Data m n P τ) (c10 τ)) ((21:Nat)) hload c51 ?_) fun (w:Env) (h:And (c52 w ((21:Nat))) (And (@Data m n P w) (c10 w))) => let c0:Prop:=c52 w ((21:Nat)); let c1:Prop:=And (@Data m n P w) (c10 w); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c61) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c61 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_21)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_22)) hcase) (RunStep.ite_true B c24 c30 c33 σ w c60 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_23)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_25)) (?nAX_g5054_0_0_26)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c29 σ w c59 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_27)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_28)) hcase_2) (RunStep.seq B c26 c28 σ c46 w c55 c58 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c45 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_30)) (?nAX_g5054_0_0_31))) (RunStep.seq B c27 RamCertificateLoad.matrix c46 c51 w c56 ((21:Nat)) (RunStep.assign B c46 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c50 (RunStep.eval_sub B c46 (Expr.var "query.col") (Expr.var "source.n") c48 c49 (RunStep.eval_var B c46 "query.col" (?nAX_g5054_0_0_32)) (RunStep.eval_var B c46 "source.n" (?nAX_g5054_0_0_33)) (?nAX_g5054_0_0_34))) left))))) (?nAX_g5054_0_0_35)) ?_)) fun (hcase_1:c41) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c43) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c43 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_37)) hcase) (RunStep.ite_false B c24 c30 c33 σ w c38 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_38)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_39)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_40)) (?nAX_g5054_0_0_41)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c32 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_42)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_43)) hcase_2) left))) (?nAX_g5054_0_0_44)) ?_)) fun (hcase_2:c6) => @Exists.intro Env c4 c87 (@And.intro (Run B selectEntry σ c87 ((64:Nat))) (c3 c87) (RunStep.mono B selectEntry σ c87 (c15 c109) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ c87 c109 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_45)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_46)) hcase) (RunStep.ite_false B c24 c30 c33 σ c87 c108 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_0_0_47)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_48)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_0_0_49)) (?nAX_g5054_0_0_50)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c32 σ c87 c107 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_51)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_52)) hcase_2) (RunStep.seq B c31 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c63 c87 c56 c106 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c62 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_0_0_53)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_0_0_54)) (?nAX_g5054_0_0_55))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c63 c84 c87 c103 c105 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c63 c65 c84 c88 c102 (RunStep.assign B c63 "vec.i" (Expr.var "query.a.row") c64 (RunStep.eval_var B c63 "query.a.row" (?nAX_g5054_0_0_56))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c65 c78 c84 c96 c101 (RunStep.seq B (Com.assign "left.s" c89) (Com.seq c110 c111) c65 c70 c78 c90 c95 (RunStep.assign B c65 "left.s" c89 c69 (RunStep.eval_get B c65 c67 (Expr.var "vec.i") c68 (RunStep.eval_var B c65 "vec.i" (?nAX_g5054_0_0_57)) (?nAX_g5054_0_0_58) (?nAX_g5054_0_0_59))) (RunStep.seq B c110 c111 c70 c74 c78 c92 c94 (RunStep.assign B c70 "left.n" c91 c73 (RunStep.eval_get B c70 c71 (Expr.var "vec.i") c72 (RunStep.eval_var B c70 "vec.i" (?nAX_g5054_0_0_60)) (?nAX_g5054_0_0_61) (?nAX_g5054_0_0_62))) (RunStep.assign B c74 "left.d" c93 c77 (RunStep.eval_get B c74 c75 (Expr.var "vec.i") c76 (RunStep.eval_var B c74 "vec.i" (?nAX_g5054_0_0_63)) (?nAX_g5054_0_0_64) (?nAX_g5054_0_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c78 c80 c84 c97 c100 (RunStep.assign B c78 "rat.s" (Expr.var "left.s") c79 (RunStep.eval_var B c78 "left.s" (?nAX_g5054_0_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c80 c82 c84 c98 c99 (RunStep.assign B c80 "rat.n" (Expr.var "left.n") c81 (RunStep.eval_var B c80 "left.n" (?nAX_g5054_0_0_67))) (RunStep.assign B c82 "rat.d" (Expr.var "left.d") c83 (RunStep.eval_var B c82 "left.d" (?nAX_g5054_0_0_68))))))) (RunStep.assign B c84 "rat.s" c104 c86 (RunStep.eval_sub B c84 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c85 (RunStep.eval_lit B ((1:Nat)) c84 h1) (RunStep.eval_var B c84 "rat.s" (?nAX_g5054_0_0_69)) (?nAX_g5054_0_0_70)))))))) (?nAX_g5054_0_0_71)) ?_) <;> try dsimp +zetaDelta at *
         all_goals try dsimp +zetaDelta at *
         try case' nAX_g5054_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
        )
        all_goals clear hload hz
        all_goals simp_all [CertificateFamilyEntries.rayEntry,ii,jj,Data,Represents,arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · (expose_names;
          refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c9:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat→ Nat:=Nat.mul; let c12:String→ Nat:=Env.vars c9; let c13:Nat:=c12 "query.a.row"; let c14:Nat:=c12 "source.n"; let c15:Nat:=c11 c13 c14; let c16:Nat:=c12 "query.a.col"; let c17:Nat:=c10 c15 c16; let c18:Env:=Env.setVar c9 "vec.i" c17; let c19:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c20:String→ String:=c19 "source.A"; let c21:String:=c20 ".s"; let c22:Nat:=Env.vars c18 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c18 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c18 "left.s" c23; let c25:String:=c20 ".n"; let c26:Nat:=Env.vars c24 "vec.i"; let c27:Nat:= @List.getD Nat (Env.arrs c24 c25) c26 ((0:Nat)); let c28:Env:=Env.setVar c24 "left.n" c27; let c29:String:=c20 ".d"; let c30:Nat:=Env.vars c28 "vec.i"; let c31:Nat:= @List.getD Nat (Env.arrs c28 c29) c30 ((0:Nat)); let c32:Env:=Env.setVar c28 "left.d" c31; let c33:Nat:=Env.vars c32 "left.s"; let c34:Env:=Env.setVar c32 "rat.s" c33; let c35:Nat:=Env.vars c34 "left.n"; let c36:Env:=Env.setVar c34 "rat.n" c35; let c37:Nat:=Env.vars c36 "left.d"; let c38:Env:=Env.setVar c36 "rat.d" c37; let c39:Nat→ Nat:=c10 ((1:Nat)); let c40:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c41:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c42:Nat:=c39 (Expr.size (Expr.var "query.row")); let c43:Nat:=c39 (Expr.size (Expr.var "query.col")); let c44:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c45:Nat:=c39 (Expr.size c44); let c46:Expr:=Expr.get c21 (Expr.var "vec.i"); let c47:Nat:=c39 (Expr.size c46); let c48:Expr:=Expr.get c25 (Expr.var "vec.i"); let c49:Nat:=c39 (Expr.size c48); let c50:Expr:=Expr.get c29 (Expr.var "vec.i"); let c51:Nat:=c39 (Expr.size c50); let c52:Nat:=c10 c49 c51; let c53:Nat:=c10 c47 c52; let c54:Nat:=c39 (Expr.size (Expr.var "left.s")); let c55:Nat:=c39 (Expr.size (Expr.var "left.n")); let c56:Nat:=c39 (Expr.size (Expr.var "left.d")); let c57:Nat:=c10 c55 c56; let c58:Nat:=c10 c54 c57; let c59:Nat:=c10 c53 c58; let c60:Nat:=c10 c45 c59; let c61:Nat:=c10 c43 c60; let c62:Nat:=c10 c42 c61; let c63:Nat:=c41 c62; let c64:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c65:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))); let c66:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c67:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c68:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c69:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c70:Com:=Com.seq c69 RamCertificateLoad.matrix; let c71:Com:=Com.seq c68 c70; let c72:Com:=c67 c71; let c73:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c74:Com:=Com.seq c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c75:Com:=c67 c74; let c76:Com:=Com.ite c66 c72 c75; let c77:Com:=Com.assign "left.n" c48; let c78:Com:=Com.assign "left.d" c50; let c79:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c80:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c81:Env→ Prop:=fun (σ':Env) => And (c79 σ' ((6:Nat))) (c80 σ'); let c82:Nat:=c41 ((6:Nat)); let c83:Nat:=c10 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c84:Prop:=Nat.lt (Env.vars σ "query.row") c83; let c85:Prop:=Not c84; let c86:Nat→ Nat:=c10 (c39 (Cond.size c66)); let c87:Nat:=c86 c82; let c88:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c89:Nat:=c88 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c90:Env:=Env.setVar σ "query.a.row" c89; let c91:String→ Nat:=Env.vars c90; let c92:Nat:=c91 "query.col"; let c93:Nat:=c91 "source.n"; let c94:Nat:=c88 c92 c93; let c95:Env:=Env.setVar c90 "query.a.col" c94; let c96:String→ Nat:=Env.vars c95; let c97:Nat:=c96 "query.a.row"; let c98:Nat:=c96 "source.n"; let c99:Nat:=c11 c97 c98; let c100:Nat:=c96 "query.a.col"; let c101:Nat:=c10 c99 c100; let c102:Env:=Env.setVar c95 "vec.i" c101; let c103:Nat:=Env.vars c102 "vec.i"; let c104:Nat:= @List.getD Nat (Env.arrs c102 c21) c103 ((0:Nat)); let c105:Env:=Env.setVar c102 "left.s" c104; let c106:Nat:=Env.vars c105 "vec.i"; let c107:Nat:= @List.getD Nat (Env.arrs c105 c25) c106 ((0:Nat)); let c108:Env:=Env.setVar c105 "left.n" c107; let c109:Nat:=Env.vars c108 "vec.i"; let c110:Nat:= @List.getD Nat (Env.arrs c108 c29) c109 ((0:Nat)); let c111:Env:=Env.setVar c108 "left.d" c110; let c112:Nat:=Env.vars c111 "left.s"; let c113:Env:=Env.setVar c111 "rat.s" c112; let c114:Nat:=Env.vars c113 "left.n"; let c115:Env:=Env.setVar c113 "rat.n" c114; let c116:Nat:=Env.vars c115 "left.d"; let c117:Env:=Env.setVar c115 "rat.d" c116; let c118:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c119:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c120:Nat→ Nat:=c10 c119; let c121:Nat:=c120 c60; let c122:Nat:=c10 c118 c121; let c123:Nat:=c41 c122; let c124:Nat:=c86 c123; let c125:Nat:=c88 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c126:Env:=Env.setVar σ "query.a.row" c125; let c127:Nat:=Env.vars c126 "query.a.row"; let c128:Env:=Env.setVar c126 "vec.i" c127; let c129:String→ String:=c19 "source.c"; let c130:String:=c129 ".s"; let c131:Nat:=Env.vars c128 "vec.i"; let c132:Nat:= @List.getD Nat (Env.arrs c128 c130) c131 ((0:Nat)); let c133:Env:=Env.setVar c128 "left.s" c132; let c134:String:=c129 ".n"; let c135:Nat:=Env.vars c133 "vec.i"; let c136:Nat:= @List.getD Nat (Env.arrs c133 c134) c135 ((0:Nat)); let c137:Env:=Env.setVar c133 "left.n" c136; let c138:String:=c129 ".d"; let c139:Nat:=Env.vars c137 "vec.i"; let c140:Nat:= @List.getD Nat (Env.arrs c137 c138) c139 ((0:Nat)); let c141:Env:=Env.setVar c137 "left.d" c140; let c142:Nat:=Env.vars c141 "left.s"; let c143:Env:=Env.setVar c141 "rat.s" c142; let c144:Nat:=Env.vars c143 "left.n"; let c145:Env:=Env.setVar c143 "rat.n" c144; let c146:Nat:=Env.vars c145 "left.d"; let c147:Env:=Env.setVar c145 "rat.d" c146; let c148:Nat:=Env.vars c147 "rat.s"; let c149:Nat:=c88 ((1:Nat)) c148; let c150:Env:=Env.setVar c147 "rat.s" c149; let c151:Nat:=c39 (Expr.size (Expr.var "query.a.row")); let c152:Expr:=Expr.get c130 (Expr.var "vec.i"); let c153:Nat:=c39 (Expr.size c152); let c154:Expr:=Expr.get c134 (Expr.var "vec.i"); let c155:Nat:=c39 (Expr.size c154); let c156:Expr:=Expr.get c138 (Expr.var "vec.i"); let c157:Nat:=c39 (Expr.size c156); let c158:Nat:=c10 c155 c157; let c159:Nat:=c10 c153 c158; let c160:Nat:=c10 c159 c58; let c161:Nat:=c10 c151 c160; let c162:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c163:Nat:=c39 (Expr.size c162); let c164:Nat:=c10 c161 c163; let c165:Nat:=c120 c164; let c166:Nat:=c41 c165; let c167:Nat:=c86 c166; let c168:Com:=Com.assign "left.n" c154; let c169:Com:=Com.assign "left.d" c156; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((64:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c40 c63) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c38 c63 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ c38 c62 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c38 c42 c61 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c9 c38 c43 c60 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c8 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_1_0_5))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c9 c18 c38 c45 c59 (RunStep.assign B c9 "vec.i" c44 c17 (RunStep.eval_add B c9 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c15 c16 (RunStep.eval_mul B c9 (Expr.var "query.a.row") (Expr.var "source.n") c13 c14 (RunStep.eval_var B c9 "query.a.row" (?nAX_g5054_1_0_6)) (RunStep.eval_var B c9 "source.n" (?nAX_g5054_1_0_7)) (?nAX_g5054_1_0_8)) (RunStep.eval_var B c9 "query.a.col" (?nAX_g5054_1_0_9)) (?nAX_g5054_1_0_10))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c18 c32 c38 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c18 c24 c32 c47 c52 (RunStep.assign B c18 "left.s" c46 c23 (RunStep.eval_get B c18 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c18 "vec.i" (?nAX_g5054_1_0_11)) (?nAX_g5054_1_0_12) (?nAX_g5054_1_0_13))) (RunStep.seq B c77 c78 c24 c28 c32 c49 c51 (RunStep.assign B c24 "left.n" c48 c27 (RunStep.eval_get B c24 c25 (Expr.var "vec.i") c26 (RunStep.eval_var B c24 "vec.i" (?nAX_g5054_1_0_14)) (?nAX_g5054_1_0_15) (?nAX_g5054_1_0_16))) (RunStep.assign B c28 "left.d" c50 c31 (RunStep.eval_get B c28 c29 (Expr.var "vec.i") c30 (RunStep.eval_var B c28 "vec.i" (?nAX_g5054_1_0_17)) (?nAX_g5054_1_0_18) (?nAX_g5054_1_0_19))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c32 c34 c38 c54 c57 (RunStep.assign B c32 "rat.s" (Expr.var "left.s") c33 (RunStep.eval_var B c32 "left.s" (?nAX_g5054_1_0_20))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c34 c36 c38 c55 c56 (RunStep.assign B c34 "rat.n" (Expr.var "left.n") c35 (RunStep.eval_var B c34 "left.n" (?nAX_g5054_1_0_21))) (RunStep.assign B c36 "rat.d" (Expr.var "left.d") c37 (RunStep.eval_var B c36 "left.d" (?nAX_g5054_1_0_22))))))))))) (?nAX_g5054_1_0_23)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c82) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_25)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_26)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_27)) hcase_1) left)) (?nAX_g5054_1_0_28)) ?_)) fun (hcase:c1) => @Or.casesOn c84 c85 (fun (x:Or c84 c85) => c5) (Classical.em c84) (fun (hcase_1:c84) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_30)) hcase) (RunStep.ite_true B c66 c72 c75 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_31)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_33)) (?nAX_g5054_1_0_34)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_35)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_36)) hcase_2) left))) (?nAX_g5054_1_0_37)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c117 (@And.intro (Run B selectEntry σ c117 ((64:Nat))) (c3 c117) (RunStep.mono B selectEntry σ c117 (c40 c124) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c117 c124 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_38)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_39)) hcase) (RunStep.ite_true B c66 c72 c75 σ c117 c123 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_40)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_41)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_42)) (?nAX_g5054_1_0_43)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ c117 c122 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_44)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_45)) hcase_2) (RunStep.seq B c68 c70 σ c90 c117 c118 c121 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c89 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_46)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_47)) (?nAX_g5054_1_0_48))) (RunStep.seq B c69 RamCertificateLoad.matrix c90 c95 c117 c119 c60 (RunStep.assign B c90 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c94 (RunStep.eval_sub B c90 (Expr.var "query.col") (Expr.var "source.n") c92 c93 (RunStep.eval_var B c90 "query.col" (?nAX_g5054_1_0_49)) (RunStep.eval_var B c90 "source.n" (?nAX_g5054_1_0_50)) (?nAX_g5054_1_0_51))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c95 c102 c117 c45 c59 (RunStep.assign B c95 "vec.i" c44 c101 (RunStep.eval_add B c95 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c99 c100 (RunStep.eval_mul B c95 (Expr.var "query.a.row") (Expr.var "source.n") c97 c98 (RunStep.eval_var B c95 "query.a.row" (?nAX_g5054_1_0_52)) (RunStep.eval_var B c95 "source.n" (?nAX_g5054_1_0_53)) (?nAX_g5054_1_0_54)) (RunStep.eval_var B c95 "query.a.col" (?nAX_g5054_1_0_55)) (?nAX_g5054_1_0_56))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c102 c111 c117 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c102 c105 c111 c47 c52 (RunStep.assign B c102 "left.s" c46 c104 (RunStep.eval_get B c102 c21 (Expr.var "vec.i") c103 (RunStep.eval_var B c102 "vec.i" (?nAX_g5054_1_0_57)) (?nAX_g5054_1_0_58) (?nAX_g5054_1_0_59))) (RunStep.seq B c77 c78 c105 c108 c111 c49 c51 (RunStep.assign B c105 "left.n" c48 c107 (RunStep.eval_get B c105 c25 (Expr.var "vec.i") c106 (RunStep.eval_var B c105 "vec.i" (?nAX_g5054_1_0_60)) (?nAX_g5054_1_0_61) (?nAX_g5054_1_0_62))) (RunStep.assign B c108 "left.d" c50 c110 (RunStep.eval_get B c108 c29 (Expr.var "vec.i") c109 (RunStep.eval_var B c108 "vec.i" (?nAX_g5054_1_0_63)) (?nAX_g5054_1_0_64) (?nAX_g5054_1_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c111 c113 c117 c54 c57 (RunStep.assign B c111 "rat.s" (Expr.var "left.s") c112 (RunStep.eval_var B c111 "left.s" (?nAX_g5054_1_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c113 c115 c117 c55 c56 (RunStep.assign B c113 "rat.n" (Expr.var "left.n") c114 (RunStep.eval_var B c113 "left.n" (?nAX_g5054_1_0_67))) (RunStep.assign B c115 "rat.d" (Expr.var "left.d") c116 (RunStep.eval_var B c115 "left.d" (?nAX_g5054_1_0_68)))))))))))) (?nAX_g5054_1_0_69)) ?_)) fun (hcase_1:c85) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_70)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_71)) hcase) (RunStep.ite_false B c66 c72 c75 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_72)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_73)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_74)) (?nAX_g5054_1_0_75)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_76)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_77)) hcase_2) left))) (?nAX_g5054_1_0_78)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c150 (@And.intro (Run B selectEntry σ c150 ((64:Nat))) (c3 c150) (RunStep.mono B selectEntry σ c150 (c40 c167) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c150 c167 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_79)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_80)) hcase) (RunStep.ite_false B c66 c72 c75 σ c150 c166 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_1_0_81)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_82)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_1_0_83)) (?nAX_g5054_1_0_84)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ c150 c165 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_85)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_86)) hcase_2) (RunStep.seq B c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c126 c150 c119 c164 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c125 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_1_0_87)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_1_0_88)) (?nAX_g5054_1_0_89))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c126 c147 c150 c161 c163 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c126 c128 c147 c151 c160 (RunStep.assign B c126 "vec.i" (Expr.var "query.a.row") c127 (RunStep.eval_var B c126 "query.a.row" (?nAX_g5054_1_0_90))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c128 c141 c147 c159 c58 (RunStep.seq B (Com.assign "left.s" c152) (Com.seq c168 c169) c128 c133 c141 c153 c158 (RunStep.assign B c128 "left.s" c152 c132 (RunStep.eval_get B c128 c130 (Expr.var "vec.i") c131 (RunStep.eval_var B c128 "vec.i" (?nAX_g5054_1_0_91)) (?nAX_g5054_1_0_92) (?nAX_g5054_1_0_93))) (RunStep.seq B c168 c169 c133 c137 c141 c155 c157 (RunStep.assign B c133 "left.n" c154 c136 (RunStep.eval_get B c133 c134 (Expr.var "vec.i") c135 (RunStep.eval_var B c133 "vec.i" (?nAX_g5054_1_0_94)) (?nAX_g5054_1_0_95) (?nAX_g5054_1_0_96))) (RunStep.assign B c137 "left.d" c156 c140 (RunStep.eval_get B c137 c138 (Expr.var "vec.i") c139 (RunStep.eval_var B c137 "vec.i" (?nAX_g5054_1_0_97)) (?nAX_g5054_1_0_98) (?nAX_g5054_1_0_99))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c141 c143 c147 c54 c57 (RunStep.assign B c141 "rat.s" (Expr.var "left.s") c142 (RunStep.eval_var B c141 "left.s" (?nAX_g5054_1_0_100))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c143 c145 c147 c55 c56 (RunStep.assign B c143 "rat.n" (Expr.var "left.n") c144 (RunStep.eval_var B c143 "left.n" (?nAX_g5054_1_0_101))) (RunStep.assign B c145 "rat.d" (Expr.var "left.d") c146 (RunStep.eval_var B c145 "left.d" (?nAX_g5054_1_0_102))))))) (RunStep.assign B c147 "rat.s" c162 c149 (RunStep.eval_sub B c147 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c148 (RunStep.eval_lit B ((1:Nat)) c147 h1) (RunStep.eval_var B c147 "rat.s" (?nAX_g5054_1_0_103)) (?nAX_g5054_1_0_104)))))))) (?nAX_g5054_1_0_105)) ?_) <;> try dsimp +zetaDelta at *
         all_goals try dsimp +zetaDelta at *
         try case' nAX_g5054_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_91 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_92 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_93 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_94 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_95 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_96 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_97 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_98 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_99 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_100 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_101 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_102 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_103 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_104 => solve | omega | (simp <;> omega) | assumption | simp_all
         try case' nAX_g5054_1_0_105 => solve | omega | (simp <;> omega) | assumption | simp_all
        )
        all_goals clear hz
        all_goals simp_all [CertificateFamilyEntries.rayEntry,Data,Represents,arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hir:i.val < m + m
      · by_cases hj:j.val < n
        · (expose_names;
            refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c9:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat→ Nat:=Nat.mul; let c12:String→ Nat:=Env.vars c9; let c13:Nat:=c12 "query.a.row"; let c14:Nat:=c12 "source.n"; let c15:Nat:=c11 c13 c14; let c16:Nat:=c12 "query.a.col"; let c17:Nat:=c10 c15 c16; let c18:Env:=Env.setVar c9 "vec.i" c17; let c19:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c20:String→ String:=c19 "source.A"; let c21:String:=c20 ".s"; let c22:Nat:=Env.vars c18 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c18 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c18 "left.s" c23; let c25:String:=c20 ".n"; let c26:Nat:=Env.vars c24 "vec.i"; let c27:Nat:= @List.getD Nat (Env.arrs c24 c25) c26 ((0:Nat)); let c28:Env:=Env.setVar c24 "left.n" c27; let c29:String:=c20 ".d"; let c30:Nat:=Env.vars c28 "vec.i"; let c31:Nat:= @List.getD Nat (Env.arrs c28 c29) c30 ((0:Nat)); let c32:Env:=Env.setVar c28 "left.d" c31; let c33:Nat:=Env.vars c32 "left.s"; let c34:Env:=Env.setVar c32 "rat.s" c33; let c35:Nat:=Env.vars c34 "left.n"; let c36:Env:=Env.setVar c34 "rat.n" c35; let c37:Nat:=Env.vars c36 "left.d"; let c38:Env:=Env.setVar c36 "rat.d" c37; let c39:Nat→ Nat:=c10 ((1:Nat)); let c40:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c41:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c42:Nat:=c39 (Expr.size (Expr.var "query.row")); let c43:Nat:=c39 (Expr.size (Expr.var "query.col")); let c44:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c45:Nat:=c39 (Expr.size c44); let c46:Expr:=Expr.get c21 (Expr.var "vec.i"); let c47:Nat:=c39 (Expr.size c46); let c48:Expr:=Expr.get c25 (Expr.var "vec.i"); let c49:Nat:=c39 (Expr.size c48); let c50:Expr:=Expr.get c29 (Expr.var "vec.i"); let c51:Nat:=c39 (Expr.size c50); let c52:Nat:=c10 c49 c51; let c53:Nat:=c10 c47 c52; let c54:Nat:=c39 (Expr.size (Expr.var "left.s")); let c55:Nat:=c39 (Expr.size (Expr.var "left.n")); let c56:Nat:=c39 (Expr.size (Expr.var "left.d")); let c57:Nat:=c10 c55 c56; let c58:Nat:=c10 c54 c57; let c59:Nat:=c10 c53 c58; let c60:Nat:=c10 c45 c59; let c61:Nat:=c10 c43 c60; let c62:Nat:=c10 c42 c61; let c63:Nat:=c41 c62; let c64:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c65:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))); let c66:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c67:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c68:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c69:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c70:Com:=Com.seq c69 RamCertificateLoad.matrix; let c71:Com:=Com.seq c68 c70; let c72:Com:=c67 c71; let c73:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c74:Com:=Com.seq c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c75:Com:=c67 c74; let c76:Com:=Com.ite c66 c72 c75; let c77:Com:=Com.assign "left.n" c48; let c78:Com:=Com.assign "left.d" c50; let c79:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c80:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c81:Env→ Prop:=fun (σ':Env) => And (c79 σ' ((6:Nat))) (c80 σ'); let c82:Nat:=c41 ((6:Nat)); let c83:Nat:=c10 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c84:Prop:=Nat.lt (Env.vars σ "query.row") c83; let c85:Prop:=Not c84; let c86:Nat→ Nat:=c10 (c39 (Cond.size c66)); let c87:Nat:=c86 c82; let c88:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c89:Nat:=c88 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c90:Env:=Env.setVar σ "query.a.row" c89; let c91:String→ Nat:=Env.vars c90; let c92:Nat:=c91 "query.col"; let c93:Nat:=c91 "source.n"; let c94:Nat:=c88 c92 c93; let c95:Env:=Env.setVar c90 "query.a.col" c94; let c96:String→ Nat:=Env.vars c95; let c97:Nat:=c96 "query.a.row"; let c98:Nat:=c96 "source.n"; let c99:Nat:=c11 c97 c98; let c100:Nat:=c96 "query.a.col"; let c101:Nat:=c10 c99 c100; let c102:Env:=Env.setVar c95 "vec.i" c101; let c103:Nat:=Env.vars c102 "vec.i"; let c104:Nat:= @List.getD Nat (Env.arrs c102 c21) c103 ((0:Nat)); let c105:Env:=Env.setVar c102 "left.s" c104; let c106:Nat:=Env.vars c105 "vec.i"; let c107:Nat:= @List.getD Nat (Env.arrs c105 c25) c106 ((0:Nat)); let c108:Env:=Env.setVar c105 "left.n" c107; let c109:Nat:=Env.vars c108 "vec.i"; let c110:Nat:= @List.getD Nat (Env.arrs c108 c29) c109 ((0:Nat)); let c111:Env:=Env.setVar c108 "left.d" c110; let c112:Nat:=Env.vars c111 "left.s"; let c113:Env:=Env.setVar c111 "rat.s" c112; let c114:Nat:=Env.vars c113 "left.n"; let c115:Env:=Env.setVar c113 "rat.n" c114; let c116:Nat:=Env.vars c115 "left.d"; let c117:Env:=Env.setVar c115 "rat.d" c116; let c118:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c119:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c120:Nat→ Nat:=c10 c119; let c121:Nat:=c120 c60; let c122:Nat:=c10 c118 c121; let c123:Nat:=c41 c122; let c124:Nat:=c86 c123; let c125:Nat:=c88 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c126:Env:=Env.setVar σ "query.a.row" c125; let c127:Nat:=Env.vars c126 "query.a.row"; let c128:Env:=Env.setVar c126 "vec.i" c127; let c129:String→ String:=c19 "source.c"; let c130:String:=c129 ".s"; let c131:Nat:=Env.vars c128 "vec.i"; let c132:Nat:= @List.getD Nat (Env.arrs c128 c130) c131 ((0:Nat)); let c133:Env:=Env.setVar c128 "left.s" c132; let c134:String:=c129 ".n"; let c135:Nat:=Env.vars c133 "vec.i"; let c136:Nat:= @List.getD Nat (Env.arrs c133 c134) c135 ((0:Nat)); let c137:Env:=Env.setVar c133 "left.n" c136; let c138:String:=c129 ".d"; let c139:Nat:=Env.vars c137 "vec.i"; let c140:Nat:= @List.getD Nat (Env.arrs c137 c138) c139 ((0:Nat)); let c141:Env:=Env.setVar c137 "left.d" c140; let c142:Nat:=Env.vars c141 "left.s"; let c143:Env:=Env.setVar c141 "rat.s" c142; let c144:Nat:=Env.vars c143 "left.n"; let c145:Env:=Env.setVar c143 "rat.n" c144; let c146:Nat:=Env.vars c145 "left.d"; let c147:Env:=Env.setVar c145 "rat.d" c146; let c148:Nat:=Env.vars c147 "rat.s"; let c149:Nat:=c88 ((1:Nat)) c148; let c150:Env:=Env.setVar c147 "rat.s" c149; let c151:Nat:=c39 (Expr.size (Expr.var "query.a.row")); let c152:Expr:=Expr.get c130 (Expr.var "vec.i"); let c153:Nat:=c39 (Expr.size c152); let c154:Expr:=Expr.get c134 (Expr.var "vec.i"); let c155:Nat:=c39 (Expr.size c154); let c156:Expr:=Expr.get c138 (Expr.var "vec.i"); let c157:Nat:=c39 (Expr.size c156); let c158:Nat:=c10 c155 c157; let c159:Nat:=c10 c153 c158; let c160:Nat:=c10 c159 c58; let c161:Nat:=c10 c151 c160; let c162:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c163:Nat:=c39 (Expr.size c162); let c164:Nat:=c10 c161 c163; let c165:Nat:=c120 c164; let c166:Nat:=c41 c165; let c167:Nat:=c86 c166; let c168:Com:=Com.assign "left.n" c154; let c169:Com:=Com.assign "left.d" c156; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((64:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c40 c63) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c38 c63 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ c38 c62 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c38 c42 c61 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c9 c38 c43 c60 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c8 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_2_0_5))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c9 c18 c38 c45 c59 (RunStep.assign B c9 "vec.i" c44 c17 (RunStep.eval_add B c9 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c15 c16 (RunStep.eval_mul B c9 (Expr.var "query.a.row") (Expr.var "source.n") c13 c14 (RunStep.eval_var B c9 "query.a.row" (?nAX_g5054_2_0_6)) (RunStep.eval_var B c9 "source.n" (?nAX_g5054_2_0_7)) (?nAX_g5054_2_0_8)) (RunStep.eval_var B c9 "query.a.col" (?nAX_g5054_2_0_9)) (?nAX_g5054_2_0_10))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c18 c32 c38 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c18 c24 c32 c47 c52 (RunStep.assign B c18 "left.s" c46 c23 (RunStep.eval_get B c18 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c18 "vec.i" (?nAX_g5054_2_0_11)) (?nAX_g5054_2_0_12) (?nAX_g5054_2_0_13))) (RunStep.seq B c77 c78 c24 c28 c32 c49 c51 (RunStep.assign B c24 "left.n" c48 c27 (RunStep.eval_get B c24 c25 (Expr.var "vec.i") c26 (RunStep.eval_var B c24 "vec.i" (?nAX_g5054_2_0_14)) (?nAX_g5054_2_0_15) (?nAX_g5054_2_0_16))) (RunStep.assign B c28 "left.d" c50 c31 (RunStep.eval_get B c28 c29 (Expr.var "vec.i") c30 (RunStep.eval_var B c28 "vec.i" (?nAX_g5054_2_0_17)) (?nAX_g5054_2_0_18) (?nAX_g5054_2_0_19))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c32 c34 c38 c54 c57 (RunStep.assign B c32 "rat.s" (Expr.var "left.s") c33 (RunStep.eval_var B c32 "left.s" (?nAX_g5054_2_0_20))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c34 c36 c38 c55 c56 (RunStep.assign B c34 "rat.n" (Expr.var "left.n") c35 (RunStep.eval_var B c34 "left.n" (?nAX_g5054_2_0_21))) (RunStep.assign B c36 "rat.d" (Expr.var "left.d") c37 (RunStep.eval_var B c36 "left.d" (?nAX_g5054_2_0_22))))))))))) (?nAX_g5054_2_0_23)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c82) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_25)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_26)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_27)) hcase_1) left)) (?nAX_g5054_2_0_28)) ?_)) fun (hcase:c1) => @Or.casesOn c84 c85 (fun (x:Or c84 c85) => c5) (Classical.em c84) (fun (hcase_1:c84) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_30)) hcase) (RunStep.ite_true B c66 c72 c75 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_31)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_33)) (?nAX_g5054_2_0_34)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_35)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_36)) hcase_2) left))) (?nAX_g5054_2_0_37)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c117 (@And.intro (Run B selectEntry σ c117 ((64:Nat))) (c3 c117) (RunStep.mono B selectEntry σ c117 (c40 c124) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c117 c124 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_38)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_39)) hcase) (RunStep.ite_true B c66 c72 c75 σ c117 c123 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_40)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_41)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_42)) (?nAX_g5054_2_0_43)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ c117 c122 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_44)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_45)) hcase_2) (RunStep.seq B c68 c70 σ c90 c117 c118 c121 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c89 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_46)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_47)) (?nAX_g5054_2_0_48))) (RunStep.seq B c69 RamCertificateLoad.matrix c90 c95 c117 c119 c60 (RunStep.assign B c90 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c94 (RunStep.eval_sub B c90 (Expr.var "query.col") (Expr.var "source.n") c92 c93 (RunStep.eval_var B c90 "query.col" (?nAX_g5054_2_0_49)) (RunStep.eval_var B c90 "source.n" (?nAX_g5054_2_0_50)) (?nAX_g5054_2_0_51))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c95 c102 c117 c45 c59 (RunStep.assign B c95 "vec.i" c44 c101 (RunStep.eval_add B c95 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c99 c100 (RunStep.eval_mul B c95 (Expr.var "query.a.row") (Expr.var "source.n") c97 c98 (RunStep.eval_var B c95 "query.a.row" (?nAX_g5054_2_0_52)) (RunStep.eval_var B c95 "source.n" (?nAX_g5054_2_0_53)) (?nAX_g5054_2_0_54)) (RunStep.eval_var B c95 "query.a.col" (?nAX_g5054_2_0_55)) (?nAX_g5054_2_0_56))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c102 c111 c117 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c102 c105 c111 c47 c52 (RunStep.assign B c102 "left.s" c46 c104 (RunStep.eval_get B c102 c21 (Expr.var "vec.i") c103 (RunStep.eval_var B c102 "vec.i" (?nAX_g5054_2_0_57)) (?nAX_g5054_2_0_58) (?nAX_g5054_2_0_59))) (RunStep.seq B c77 c78 c105 c108 c111 c49 c51 (RunStep.assign B c105 "left.n" c48 c107 (RunStep.eval_get B c105 c25 (Expr.var "vec.i") c106 (RunStep.eval_var B c105 "vec.i" (?nAX_g5054_2_0_60)) (?nAX_g5054_2_0_61) (?nAX_g5054_2_0_62))) (RunStep.assign B c108 "left.d" c50 c110 (RunStep.eval_get B c108 c29 (Expr.var "vec.i") c109 (RunStep.eval_var B c108 "vec.i" (?nAX_g5054_2_0_63)) (?nAX_g5054_2_0_64) (?nAX_g5054_2_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c111 c113 c117 c54 c57 (RunStep.assign B c111 "rat.s" (Expr.var "left.s") c112 (RunStep.eval_var B c111 "left.s" (?nAX_g5054_2_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c113 c115 c117 c55 c56 (RunStep.assign B c113 "rat.n" (Expr.var "left.n") c114 (RunStep.eval_var B c113 "left.n" (?nAX_g5054_2_0_67))) (RunStep.assign B c115 "rat.d" (Expr.var "left.d") c116 (RunStep.eval_var B c115 "left.d" (?nAX_g5054_2_0_68)))))))))))) (?nAX_g5054_2_0_69)) ?_)) fun (hcase_1:c85) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_70)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_71)) hcase) (RunStep.ite_false B c66 c72 c75 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_72)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_73)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_74)) (?nAX_g5054_2_0_75)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_76)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_77)) hcase_2) left))) (?nAX_g5054_2_0_78)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c150 (@And.intro (Run B selectEntry σ c150 ((64:Nat))) (c3 c150) (RunStep.mono B selectEntry σ c150 (c40 c167) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c150 c167 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_79)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_80)) hcase) (RunStep.ite_false B c66 c72 c75 σ c150 c166 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_2_0_81)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_82)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_2_0_83)) (?nAX_g5054_2_0_84)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ c150 c165 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_85)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_86)) hcase_2) (RunStep.seq B c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c126 c150 c119 c164 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c125 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_2_0_87)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_2_0_88)) (?nAX_g5054_2_0_89))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c126 c147 c150 c161 c163 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c126 c128 c147 c151 c160 (RunStep.assign B c126 "vec.i" (Expr.var "query.a.row") c127 (RunStep.eval_var B c126 "query.a.row" (?nAX_g5054_2_0_90))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c128 c141 c147 c159 c58 (RunStep.seq B (Com.assign "left.s" c152) (Com.seq c168 c169) c128 c133 c141 c153 c158 (RunStep.assign B c128 "left.s" c152 c132 (RunStep.eval_get B c128 c130 (Expr.var "vec.i") c131 (RunStep.eval_var B c128 "vec.i" (?nAX_g5054_2_0_91)) (?nAX_g5054_2_0_92) (?nAX_g5054_2_0_93))) (RunStep.seq B c168 c169 c133 c137 c141 c155 c157 (RunStep.assign B c133 "left.n" c154 c136 (RunStep.eval_get B c133 c134 (Expr.var "vec.i") c135 (RunStep.eval_var B c133 "vec.i" (?nAX_g5054_2_0_94)) (?nAX_g5054_2_0_95) (?nAX_g5054_2_0_96))) (RunStep.assign B c137 "left.d" c156 c140 (RunStep.eval_get B c137 c138 (Expr.var "vec.i") c139 (RunStep.eval_var B c137 "vec.i" (?nAX_g5054_2_0_97)) (?nAX_g5054_2_0_98) (?nAX_g5054_2_0_99))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c141 c143 c147 c54 c57 (RunStep.assign B c141 "rat.s" (Expr.var "left.s") c142 (RunStep.eval_var B c141 "left.s" (?nAX_g5054_2_0_100))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c143 c145 c147 c55 c56 (RunStep.assign B c143 "rat.n" (Expr.var "left.n") c144 (RunStep.eval_var B c143 "left.n" (?nAX_g5054_2_0_101))) (RunStep.assign B c145 "rat.d" (Expr.var "left.d") c146 (RunStep.eval_var B c145 "left.d" (?nAX_g5054_2_0_102))))))) (RunStep.assign B c147 "rat.s" c162 c149 (RunStep.eval_sub B c147 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c148 (RunStep.eval_lit B ((1:Nat)) c147 h1) (RunStep.eval_var B c147 "rat.s" (?nAX_g5054_2_0_103)) (?nAX_g5054_2_0_104)))))))) (?nAX_g5054_2_0_105)) ?_) <;> try dsimp +zetaDelta at *
           all_goals try dsimp +zetaDelta at *
           try case' nAX_g5054_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_91 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_92 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_93 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_94 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_95 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_96 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_97 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_98 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_99 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_100 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_101 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_102 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_103 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_104 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_2_0_105 => solve | omega | (simp <;> omega) | assumption | simp_all
          )
          all_goals clear hz
          all_goals simp_all [CertificateFamilyEntries.rayEntry,Data,Represents,arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
        · let ii:Fin m:= ⟨i.val - m,by omega⟩
          let jj:Fin n:= ⟨j.val - n,by omega⟩
          have hload:=RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj)
          (expose_names;
            refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c6:Prop:=Not c5; let c7:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c8:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c7; let c9:Env→ Nat→ Prop:=Run B RamCertificateLoad.matrix c8; let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int m n P ii jj)); let c11:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((21:Nat))) (And (@Data m n P σ') (c10 σ')); let c12:String→ Nat:=Env.vars c8; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c16:Nat→ Nat:=c13 (c14 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c17:Nat:=c14 (Expr.size (Expr.var "query.row")); let c18:Nat:=c14 (Expr.size (Expr.var "query.col")); let c19:Nat:=c13 c18 ((21:Nat)); let c20:Nat:=c13 c17 c19; let c21:Nat:=c16 c20; let c22:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c23:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))); let c24:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c25:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c26:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c27:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c28:Com:=Com.seq c27 RamCertificateLoad.matrix; let c29:Com:=Com.seq c26 c28; let c30:Com:=c25 c29; let c31:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c32:Com:=Com.seq c31 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c33:Com:=c25 c32; let c34:Com:=Com.ite c24 c30 c33; let c35:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c36:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c37:Env→ Prop:=fun (σ':Env) => And (c35 σ' ((6:Nat))) (c36 σ'); let c38:Nat:=c16 ((6:Nat)); let c39:Nat:=c13 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c40:Prop:=Nat.lt (Env.vars σ "query.row") c39; let c41:Prop:=Not c40; let c42:Nat→ Nat:=c13 (c14 (Cond.size c24)); let c43:Nat:=c42 c38; let c44:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c45:Nat:=c44 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c46:Env:=Env.setVar σ "query.a.row" c45; let c47:String→ Nat:=Env.vars c46; let c48:Nat:=c47 "query.col"; let c49:Nat:=c47 "source.n"; let c50:Nat:=c44 c48 c49; let c51:Env:=Env.setVar c46 "query.a.col" c50; let c52:Env→ Nat→ Prop:=Run B RamCertificateLoad.matrix c51; let c53:Env→ Prop:=fun (σ':Env) => And (c52 σ' ((21:Nat))) (And (@Data m n P σ') (c10 σ')); let c54:String→ Nat:=Env.vars c51; let c55:Nat:=c14 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c56:Nat:=c14 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c57:Nat→ Nat:=c13 c56; let c58:Nat:=c57 ((21:Nat)); let c59:Nat:=c13 c55 c58; let c60:Nat:=c16 c59; let c61:Nat:=c42 c60; let c62:Nat:=c44 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c63:Env:=Env.setVar σ "query.a.row" c62; let c64:Nat:=Env.vars c63 "query.a.row"; let c65:Env:=Env.setVar c63 "vec.i" c64; let c66:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.c"; let c67:String:=c66 ".s"; let c68:Nat:=Env.vars c65 "vec.i"; let c69:Nat:= @List.getD Nat (Env.arrs c65 c67) c68 ((0:Nat)); let c70:Env:=Env.setVar c65 "left.s" c69; let c71:String:=c66 ".n"; let c72:Nat:=Env.vars c70 "vec.i"; let c73:Nat:= @List.getD Nat (Env.arrs c70 c71) c72 ((0:Nat)); let c74:Env:=Env.setVar c70 "left.n" c73; let c75:String:=c66 ".d"; let c76:Nat:=Env.vars c74 "vec.i"; let c77:Nat:= @List.getD Nat (Env.arrs c74 c75) c76 ((0:Nat)); let c78:Env:=Env.setVar c74 "left.d" c77; let c79:Nat:=Env.vars c78 "left.s"; let c80:Env:=Env.setVar c78 "rat.s" c79; let c81:Nat:=Env.vars c80 "left.n"; let c82:Env:=Env.setVar c80 "rat.n" c81; let c83:Nat:=Env.vars c82 "left.d"; let c84:Env:=Env.setVar c82 "rat.d" c83; let c85:Nat:=Env.vars c84 "rat.s"; let c86:Nat:=c44 ((1:Nat)) c85; let c87:Env:=Env.setVar c84 "rat.s" c86; let c88:Nat:=c14 (Expr.size (Expr.var "query.a.row")); let c89:Expr:=Expr.get c67 (Expr.var "vec.i"); let c90:Nat:=c14 (Expr.size c89); let c91:Expr:=Expr.get c71 (Expr.var "vec.i"); let c92:Nat:=c14 (Expr.size c91); let c93:Expr:=Expr.get c75 (Expr.var "vec.i"); let c94:Nat:=c14 (Expr.size c93); let c95:Nat:=c13 c92 c94; let c96:Nat:=c13 c90 c95; let c97:Nat:=c14 (Expr.size (Expr.var "left.s")); let c98:Nat:=c14 (Expr.size (Expr.var "left.n")); let c99:Nat:=c14 (Expr.size (Expr.var "left.d")); let c100:Nat:=c13 c98 c99; let c101:Nat:=c13 c97 c100; let c102:Nat:=c13 c96 c101; let c103:Nat:=c13 c88 c102; let c104:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c105:Nat:=c14 (Expr.size c104); let c106:Nat:=c13 c103 c105; let c107:Nat:=c57 c106; let c108:Nat:=c16 c107; let c109:Nat:=c42 c108; let c110:Com:=Com.assign "left.n" c91; let c111:Com:=Com.assign "left.d" c93; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_1:c5) => @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (And (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val m ii)) (@Eq Nat (Env.vars σ "query.a.col") (@Fin.val n jj)))) RamCertificateLoad.matrix (fun (x τ:Env) => And (@Data m n P τ) (c10 τ)) ((21:Nat)) hload c8 ?_) fun (w:Env) (h:And (c9 w ((21:Nat))) (And (@Data m n P w) (c10 w))) => let c0:Prop:=c9 w ((21:Nat)); let c1:Prop:=And (@Data m n P w) (c10 w); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c21) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c21 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))) σ w c20 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) w c17 c19 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c8 w c18 ((21:Nat)) (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c7 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_3_0_5))) left)))) (?nAX_g5054_3_0_6)) ?_)) fun (hcase_1:c6) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c38) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c38 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_7)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_8)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c22 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_9)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_10)) hcase_1) left)) (?nAX_g5054_3_0_11)) ?_)) fun (hcase:c1) => @Or.casesOn c40 c41 (fun (x:Or c40 c41) => @Exists Env c4) (Classical.em c40) (fun (hcase_1:c40) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c43) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c43 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_12)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_13)) hcase) (RunStep.ite_true B c24 c30 c33 σ w c38 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_14)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_15)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_16)) (?nAX_g5054_3_0_17)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c29 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_18)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_19)) hcase_2) left))) (?nAX_g5054_3_0_20)) ?_)) fun (hcase_2:c6) => @Exists.casesOn Env c53 (fun (x:@Exists Env c53) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (And (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val m ii)) (@Eq Nat (Env.vars σ "query.a.col") (@Fin.val n jj)))) RamCertificateLoad.matrix (fun (x τ:Env) => And (@Data m n P τ) (c10 τ)) ((21:Nat)) hload c51 ?_) fun (w:Env) (h:And (c52 w ((21:Nat))) (And (@Data m n P w) (c10 w))) => let c0:Prop:=c52 w ((21:Nat)); let c1:Prop:=And (@Data m n P w) (c10 w); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c61) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c61 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_21)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_22)) hcase) (RunStep.ite_true B c24 c30 c33 σ w c60 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_23)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_25)) (?nAX_g5054_3_0_26)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c29 σ w c59 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_27)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_28)) hcase_2) (RunStep.seq B c26 c28 σ c46 w c55 c58 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c45 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_30)) (?nAX_g5054_3_0_31))) (RunStep.seq B c27 RamCertificateLoad.matrix c46 c51 w c56 ((21:Nat)) (RunStep.assign B c46 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c50 (RunStep.eval_sub B c46 (Expr.var "query.col") (Expr.var "source.n") c48 c49 (RunStep.eval_var B c46 "query.col" (?nAX_g5054_3_0_32)) (RunStep.eval_var B c46 "source.n" (?nAX_g5054_3_0_33)) (?nAX_g5054_3_0_34))) left))))) (?nAX_g5054_3_0_35)) ?_)) fun (hcase_1:c41) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c36 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c35 w ((6:Nat))) (c36 w)) => let c0:Prop:=c35 w ((6:Nat)); @And.casesOn c0 (c36 w) (fun (x:And c0 (c36 w)) => @Exists Env c4) h fun (left:c0) (right:c36 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c15 c43) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ w c43 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_37)) hcase) (RunStep.ite_false B c24 c30 c33 σ w c38 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_38)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_39)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_40)) (?nAX_g5054_3_0_41)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c32 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_42)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_43)) hcase_2) left))) (?nAX_g5054_3_0_44)) ?_)) fun (hcase_2:c6) => @Exists.intro Env c4 c87 (@And.intro (Run B selectEntry σ c87 ((64:Nat))) (c3 c87) (RunStep.mono B selectEntry σ c87 (c15 c109) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c23 c34 σ c87 c109 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_45)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_46)) hcase) (RunStep.ite_false B c24 c30 c33 σ c87 c108 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c39 (RunStep.eval_var B σ "query.row" (?nAX_g5054_3_0_47)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_48)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_3_0_49)) (?nAX_g5054_3_0_50)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c32 σ c87 c107 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_51)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_52)) hcase_2) (RunStep.seq B c31 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c63 c87 c56 c106 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c62 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_3_0_53)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_3_0_54)) (?nAX_g5054_3_0_55))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c63 c84 c87 c103 c105 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c63 c65 c84 c88 c102 (RunStep.assign B c63 "vec.i" (Expr.var "query.a.row") c64 (RunStep.eval_var B c63 "query.a.row" (?nAX_g5054_3_0_56))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c65 c78 c84 c96 c101 (RunStep.seq B (Com.assign "left.s" c89) (Com.seq c110 c111) c65 c70 c78 c90 c95 (RunStep.assign B c65 "left.s" c89 c69 (RunStep.eval_get B c65 c67 (Expr.var "vec.i") c68 (RunStep.eval_var B c65 "vec.i" (?nAX_g5054_3_0_57)) (?nAX_g5054_3_0_58) (?nAX_g5054_3_0_59))) (RunStep.seq B c110 c111 c70 c74 c78 c92 c94 (RunStep.assign B c70 "left.n" c91 c73 (RunStep.eval_get B c70 c71 (Expr.var "vec.i") c72 (RunStep.eval_var B c70 "vec.i" (?nAX_g5054_3_0_60)) (?nAX_g5054_3_0_61) (?nAX_g5054_3_0_62))) (RunStep.assign B c74 "left.d" c93 c77 (RunStep.eval_get B c74 c75 (Expr.var "vec.i") c76 (RunStep.eval_var B c74 "vec.i" (?nAX_g5054_3_0_63)) (?nAX_g5054_3_0_64) (?nAX_g5054_3_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c78 c80 c84 c97 c100 (RunStep.assign B c78 "rat.s" (Expr.var "left.s") c79 (RunStep.eval_var B c78 "left.s" (?nAX_g5054_3_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c80 c82 c84 c98 c99 (RunStep.assign B c80 "rat.n" (Expr.var "left.n") c81 (RunStep.eval_var B c80 "left.n" (?nAX_g5054_3_0_67))) (RunStep.assign B c82 "rat.d" (Expr.var "left.d") c83 (RunStep.eval_var B c82 "left.d" (?nAX_g5054_3_0_68))))))) (RunStep.assign B c84 "rat.s" c104 c86 (RunStep.eval_sub B c84 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c85 (RunStep.eval_lit B ((1:Nat)) c84 h1) (RunStep.eval_var B c84 "rat.s" (?nAX_g5054_3_0_69)) (?nAX_g5054_3_0_70)))))))) (?nAX_g5054_3_0_71)) ?_) <;> try dsimp +zetaDelta at *
           all_goals try dsimp +zetaDelta at *
           try case' nAX_g5054_3_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_3_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
          )
          all_goals clear hload hz
          all_goals simp_all [CertificateFamilyEntries.rayEntry,ii,jj,Data,Represents,arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · by_cases hj:j.val < n
        · (expose_names;
            refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c9:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat→ Nat:=Nat.mul; let c12:String→ Nat:=Env.vars c9; let c13:Nat:=c12 "query.a.row"; let c14:Nat:=c12 "source.n"; let c15:Nat:=c11 c13 c14; let c16:Nat:=c12 "query.a.col"; let c17:Nat:=c10 c15 c16; let c18:Env:=Env.setVar c9 "vec.i" c17; let c19:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c20:String→ String:=c19 "source.A"; let c21:String:=c20 ".s"; let c22:Nat:=Env.vars c18 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c18 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c18 "left.s" c23; let c25:String:=c20 ".n"; let c26:Nat:=Env.vars c24 "vec.i"; let c27:Nat:= @List.getD Nat (Env.arrs c24 c25) c26 ((0:Nat)); let c28:Env:=Env.setVar c24 "left.n" c27; let c29:String:=c20 ".d"; let c30:Nat:=Env.vars c28 "vec.i"; let c31:Nat:= @List.getD Nat (Env.arrs c28 c29) c30 ((0:Nat)); let c32:Env:=Env.setVar c28 "left.d" c31; let c33:Nat:=Env.vars c32 "left.s"; let c34:Env:=Env.setVar c32 "rat.s" c33; let c35:Nat:=Env.vars c34 "left.n"; let c36:Env:=Env.setVar c34 "rat.n" c35; let c37:Nat:=Env.vars c36 "left.d"; let c38:Env:=Env.setVar c36 "rat.d" c37; let c39:Nat→ Nat:=c10 ((1:Nat)); let c40:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c41:Nat→ Nat:=c10 (c39 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c42:Nat:=c39 (Expr.size (Expr.var "query.row")); let c43:Nat:=c39 (Expr.size (Expr.var "query.col")); let c44:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c45:Nat:=c39 (Expr.size c44); let c46:Expr:=Expr.get c21 (Expr.var "vec.i"); let c47:Nat:=c39 (Expr.size c46); let c48:Expr:=Expr.get c25 (Expr.var "vec.i"); let c49:Nat:=c39 (Expr.size c48); let c50:Expr:=Expr.get c29 (Expr.var "vec.i"); let c51:Nat:=c39 (Expr.size c50); let c52:Nat:=c10 c49 c51; let c53:Nat:=c10 c47 c52; let c54:Nat:=c39 (Expr.size (Expr.var "left.s")); let c55:Nat:=c39 (Expr.size (Expr.var "left.n")); let c56:Nat:=c39 (Expr.size (Expr.var "left.d")); let c57:Nat:=c10 c55 c56; let c58:Nat:=c10 c54 c57; let c59:Nat:=c10 c53 c58; let c60:Nat:=c10 c45 c59; let c61:Nat:=c10 c43 c60; let c62:Nat:=c10 c42 c61; let c63:Nat:=c41 c62; let c64:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c65:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))); let c66:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c67:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c68:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c69:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c70:Com:=Com.seq c69 RamCertificateLoad.matrix; let c71:Com:=Com.seq c68 c70; let c72:Com:=c67 c71; let c73:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c74:Com:=Com.seq c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c75:Com:=c67 c74; let c76:Com:=Com.ite c66 c72 c75; let c77:Com:=Com.assign "left.n" c48; let c78:Com:=Com.assign "left.d" c50; let c79:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c80:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c81:Env→ Prop:=fun (σ':Env) => And (c79 σ' ((6:Nat))) (c80 σ'); let c82:Nat:=c41 ((6:Nat)); let c83:Nat:=c10 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c84:Prop:=Nat.lt (Env.vars σ "query.row") c83; let c85:Prop:=Not c84; let c86:Nat→ Nat:=c10 (c39 (Cond.size c66)); let c87:Nat:=c86 c82; let c88:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c89:Nat:=c88 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c90:Env:=Env.setVar σ "query.a.row" c89; let c91:String→ Nat:=Env.vars c90; let c92:Nat:=c91 "query.col"; let c93:Nat:=c91 "source.n"; let c94:Nat:=c88 c92 c93; let c95:Env:=Env.setVar c90 "query.a.col" c94; let c96:String→ Nat:=Env.vars c95; let c97:Nat:=c96 "query.a.row"; let c98:Nat:=c96 "source.n"; let c99:Nat:=c11 c97 c98; let c100:Nat:=c96 "query.a.col"; let c101:Nat:=c10 c99 c100; let c102:Env:=Env.setVar c95 "vec.i" c101; let c103:Nat:=Env.vars c102 "vec.i"; let c104:Nat:= @List.getD Nat (Env.arrs c102 c21) c103 ((0:Nat)); let c105:Env:=Env.setVar c102 "left.s" c104; let c106:Nat:=Env.vars c105 "vec.i"; let c107:Nat:= @List.getD Nat (Env.arrs c105 c25) c106 ((0:Nat)); let c108:Env:=Env.setVar c105 "left.n" c107; let c109:Nat:=Env.vars c108 "vec.i"; let c110:Nat:= @List.getD Nat (Env.arrs c108 c29) c109 ((0:Nat)); let c111:Env:=Env.setVar c108 "left.d" c110; let c112:Nat:=Env.vars c111 "left.s"; let c113:Env:=Env.setVar c111 "rat.s" c112; let c114:Nat:=Env.vars c113 "left.n"; let c115:Env:=Env.setVar c113 "rat.n" c114; let c116:Nat:=Env.vars c115 "left.d"; let c117:Env:=Env.setVar c115 "rat.d" c116; let c118:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c119:Nat:=c39 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c120:Nat→ Nat:=c10 c119; let c121:Nat:=c120 c60; let c122:Nat:=c10 c118 c121; let c123:Nat:=c41 c122; let c124:Nat:=c86 c123; let c125:Nat:=c88 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c126:Env:=Env.setVar σ "query.a.row" c125; let c127:Nat:=Env.vars c126 "query.a.row"; let c128:Env:=Env.setVar c126 "vec.i" c127; let c129:String→ String:=c19 "source.c"; let c130:String:=c129 ".s"; let c131:Nat:=Env.vars c128 "vec.i"; let c132:Nat:= @List.getD Nat (Env.arrs c128 c130) c131 ((0:Nat)); let c133:Env:=Env.setVar c128 "left.s" c132; let c134:String:=c129 ".n"; let c135:Nat:=Env.vars c133 "vec.i"; let c136:Nat:= @List.getD Nat (Env.arrs c133 c134) c135 ((0:Nat)); let c137:Env:=Env.setVar c133 "left.n" c136; let c138:String:=c129 ".d"; let c139:Nat:=Env.vars c137 "vec.i"; let c140:Nat:= @List.getD Nat (Env.arrs c137 c138) c139 ((0:Nat)); let c141:Env:=Env.setVar c137 "left.d" c140; let c142:Nat:=Env.vars c141 "left.s"; let c143:Env:=Env.setVar c141 "rat.s" c142; let c144:Nat:=Env.vars c143 "left.n"; let c145:Env:=Env.setVar c143 "rat.n" c144; let c146:Nat:=Env.vars c145 "left.d"; let c147:Env:=Env.setVar c145 "rat.d" c146; let c148:Nat:=Env.vars c147 "rat.s"; let c149:Nat:=c88 ((1:Nat)) c148; let c150:Env:=Env.setVar c147 "rat.s" c149; let c151:Nat:=c39 (Expr.size (Expr.var "query.a.row")); let c152:Expr:=Expr.get c130 (Expr.var "vec.i"); let c153:Nat:=c39 (Expr.size c152); let c154:Expr:=Expr.get c134 (Expr.var "vec.i"); let c155:Nat:=c39 (Expr.size c154); let c156:Expr:=Expr.get c138 (Expr.var "vec.i"); let c157:Nat:=c39 (Expr.size c156); let c158:Nat:=c10 c155 c157; let c159:Nat:=c10 c153 c158; let c160:Nat:=c10 c159 c58; let c161:Nat:=c10 c151 c160; let c162:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c163:Nat:=c39 (Expr.size c162); let c164:Nat:=c10 c161 c163; let c165:Nat:=c120 c164; let c166:Nat:=c41 c165; let c167:Nat:=c86 c166; let c168:Com:=Com.assign "left.n" c154; let c169:Com:=Com.assign "left.d" c156; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((64:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c40 c63) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c38 c63 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ c38 c62 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c38 c42 c61 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c9 c38 c43 c60 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c8 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_4_0_5))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c9 c18 c38 c45 c59 (RunStep.assign B c9 "vec.i" c44 c17 (RunStep.eval_add B c9 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c15 c16 (RunStep.eval_mul B c9 (Expr.var "query.a.row") (Expr.var "source.n") c13 c14 (RunStep.eval_var B c9 "query.a.row" (?nAX_g5054_4_0_6)) (RunStep.eval_var B c9 "source.n" (?nAX_g5054_4_0_7)) (?nAX_g5054_4_0_8)) (RunStep.eval_var B c9 "query.a.col" (?nAX_g5054_4_0_9)) (?nAX_g5054_4_0_10))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c18 c32 c38 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c18 c24 c32 c47 c52 (RunStep.assign B c18 "left.s" c46 c23 (RunStep.eval_get B c18 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c18 "vec.i" (?nAX_g5054_4_0_11)) (?nAX_g5054_4_0_12) (?nAX_g5054_4_0_13))) (RunStep.seq B c77 c78 c24 c28 c32 c49 c51 (RunStep.assign B c24 "left.n" c48 c27 (RunStep.eval_get B c24 c25 (Expr.var "vec.i") c26 (RunStep.eval_var B c24 "vec.i" (?nAX_g5054_4_0_14)) (?nAX_g5054_4_0_15) (?nAX_g5054_4_0_16))) (RunStep.assign B c28 "left.d" c50 c31 (RunStep.eval_get B c28 c29 (Expr.var "vec.i") c30 (RunStep.eval_var B c28 "vec.i" (?nAX_g5054_4_0_17)) (?nAX_g5054_4_0_18) (?nAX_g5054_4_0_19))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c32 c34 c38 c54 c57 (RunStep.assign B c32 "rat.s" (Expr.var "left.s") c33 (RunStep.eval_var B c32 "left.s" (?nAX_g5054_4_0_20))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c34 c36 c38 c55 c56 (RunStep.assign B c34 "rat.n" (Expr.var "left.n") c35 (RunStep.eval_var B c34 "left.n" (?nAX_g5054_4_0_21))) (RunStep.assign B c36 "rat.d" (Expr.var "left.d") c37 (RunStep.eval_var B c36 "left.d" (?nAX_g5054_4_0_22))))))))))) (?nAX_g5054_4_0_23)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c82) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_25)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c64 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_26)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_27)) hcase_1) left)) (?nAX_g5054_4_0_28)) ?_)) fun (hcase:c1) => @Or.casesOn c84 c85 (fun (x:Or c84 c85) => c5) (Classical.em c84) (fun (hcase_1:c84) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_30)) hcase) (RunStep.ite_true B c66 c72 c75 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_31)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_33)) (?nAX_g5054_4_0_34)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_35)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_36)) hcase_2) left))) (?nAX_g5054_4_0_37)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c117 (@And.intro (Run B selectEntry σ c117 ((64:Nat))) (c3 c117) (RunStep.mono B selectEntry σ c117 (c40 c124) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c117 c124 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_38)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_39)) hcase) (RunStep.ite_true B c66 c72 c75 σ c117 c123 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_40)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_41)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_42)) (?nAX_g5054_4_0_43)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c71 σ c117 c122 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_44)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_45)) hcase_2) (RunStep.seq B c68 c70 σ c90 c117 c118 c121 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c89 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_46)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_47)) (?nAX_g5054_4_0_48))) (RunStep.seq B c69 RamCertificateLoad.matrix c90 c95 c117 c119 c60 (RunStep.assign B c90 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c94 (RunStep.eval_sub B c90 (Expr.var "query.col") (Expr.var "source.n") c92 c93 (RunStep.eval_var B c90 "query.col" (?nAX_g5054_4_0_49)) (RunStep.eval_var B c90 "source.n" (?nAX_g5054_4_0_50)) (?nAX_g5054_4_0_51))) (RunStep.seq B (Com.assign "vec.i" c44) (RamArrayResult.load "source.A") c95 c102 c117 c45 c59 (RunStep.assign B c95 "vec.i" c44 c101 (RunStep.eval_add B c95 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c99 c100 (RunStep.eval_mul B c95 (Expr.var "query.a.row") (Expr.var "source.n") c97 c98 (RunStep.eval_var B c95 "query.a.row" (?nAX_g5054_4_0_52)) (RunStep.eval_var B c95 "source.n" (?nAX_g5054_4_0_53)) (?nAX_g5054_4_0_54)) (RunStep.eval_var B c95 "query.a.col" (?nAX_g5054_4_0_55)) (?nAX_g5054_4_0_56))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c102 c111 c117 c53 c58 (RunStep.seq B (Com.assign "left.s" c46) (Com.seq c77 c78) c102 c105 c111 c47 c52 (RunStep.assign B c102 "left.s" c46 c104 (RunStep.eval_get B c102 c21 (Expr.var "vec.i") c103 (RunStep.eval_var B c102 "vec.i" (?nAX_g5054_4_0_57)) (?nAX_g5054_4_0_58) (?nAX_g5054_4_0_59))) (RunStep.seq B c77 c78 c105 c108 c111 c49 c51 (RunStep.assign B c105 "left.n" c48 c107 (RunStep.eval_get B c105 c25 (Expr.var "vec.i") c106 (RunStep.eval_var B c105 "vec.i" (?nAX_g5054_4_0_60)) (?nAX_g5054_4_0_61) (?nAX_g5054_4_0_62))) (RunStep.assign B c108 "left.d" c50 c110 (RunStep.eval_get B c108 c29 (Expr.var "vec.i") c109 (RunStep.eval_var B c108 "vec.i" (?nAX_g5054_4_0_63)) (?nAX_g5054_4_0_64) (?nAX_g5054_4_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c111 c113 c117 c54 c57 (RunStep.assign B c111 "rat.s" (Expr.var "left.s") c112 (RunStep.eval_var B c111 "left.s" (?nAX_g5054_4_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c113 c115 c117 c55 c56 (RunStep.assign B c113 "rat.n" (Expr.var "left.n") c114 (RunStep.eval_var B c113 "left.n" (?nAX_g5054_4_0_67))) (RunStep.assign B c115 "rat.d" (Expr.var "left.d") c116 (RunStep.eval_var B c115 "left.d" (?nAX_g5054_4_0_68)))))))))))) (?nAX_g5054_4_0_69)) ?_)) fun (hcase_1:c85) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_2:c6) => @Exists.casesOn Env c81 (fun (x:@Exists Env c81) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c80 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c79 w ((6:Nat))) (c80 w)) => let c0:Prop:=c79 w ((6:Nat)); @And.casesOn c0 (c80 w) (fun (x:And c0 (c80 w)) => c5) h fun (left:c0) (right:c80 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c40 c87) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ w c87 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_70)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_71)) hcase) (RunStep.ite_false B c66 c72 c75 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_72)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_73)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_74)) (?nAX_g5054_4_0_75)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_76)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_77)) hcase_2) left))) (?nAX_g5054_4_0_78)) ?_)) fun (hcase_2:c7) => @Exists.intro Env c4 c150 (@And.intro (Run B selectEntry σ c150 ((64:Nat))) (c3 c150) (RunStep.mono B selectEntry σ c150 (c40 c167) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c65 c76 σ c150 c167 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_79)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_80)) hcase) (RunStep.ite_false B c66 c72 c75 σ c150 c166 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c83 (RunStep.eval_var B σ "query.row" (?nAX_g5054_4_0_81)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_82)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_4_0_83)) (?nAX_g5054_4_0_84)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c74 σ c150 c165 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_85)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_86)) hcase_2) (RunStep.seq B c73 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c126 c150 c119 c164 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c125 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_4_0_87)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_4_0_88)) (?nAX_g5054_4_0_89))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c126 c147 c150 c161 c163 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c126 c128 c147 c151 c160 (RunStep.assign B c126 "vec.i" (Expr.var "query.a.row") c127 (RunStep.eval_var B c126 "query.a.row" (?nAX_g5054_4_0_90))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c128 c141 c147 c159 c58 (RunStep.seq B (Com.assign "left.s" c152) (Com.seq c168 c169) c128 c133 c141 c153 c158 (RunStep.assign B c128 "left.s" c152 c132 (RunStep.eval_get B c128 c130 (Expr.var "vec.i") c131 (RunStep.eval_var B c128 "vec.i" (?nAX_g5054_4_0_91)) (?nAX_g5054_4_0_92) (?nAX_g5054_4_0_93))) (RunStep.seq B c168 c169 c133 c137 c141 c155 c157 (RunStep.assign B c133 "left.n" c154 c136 (RunStep.eval_get B c133 c134 (Expr.var "vec.i") c135 (RunStep.eval_var B c133 "vec.i" (?nAX_g5054_4_0_94)) (?nAX_g5054_4_0_95) (?nAX_g5054_4_0_96))) (RunStep.assign B c137 "left.d" c156 c140 (RunStep.eval_get B c137 c138 (Expr.var "vec.i") c139 (RunStep.eval_var B c137 "vec.i" (?nAX_g5054_4_0_97)) (?nAX_g5054_4_0_98) (?nAX_g5054_4_0_99))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c141 c143 c147 c54 c57 (RunStep.assign B c141 "rat.s" (Expr.var "left.s") c142 (RunStep.eval_var B c141 "left.s" (?nAX_g5054_4_0_100))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c143 c145 c147 c55 c56 (RunStep.assign B c143 "rat.n" (Expr.var "left.n") c144 (RunStep.eval_var B c143 "left.n" (?nAX_g5054_4_0_101))) (RunStep.assign B c145 "rat.d" (Expr.var "left.d") c146 (RunStep.eval_var B c145 "left.d" (?nAX_g5054_4_0_102))))))) (RunStep.assign B c147 "rat.s" c162 c149 (RunStep.eval_sub B c147 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c148 (RunStep.eval_lit B ((1:Nat)) c147 h1) (RunStep.eval_var B c147 "rat.s" (?nAX_g5054_4_0_103)) (?nAX_g5054_4_0_104)))))))) (?nAX_g5054_4_0_105)) ?_) <;> try dsimp +zetaDelta at *
           all_goals try dsimp +zetaDelta at *
           try case' nAX_g5054_4_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_91 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_92 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_93 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_94 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_95 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_96 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_97 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_98 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_99 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_100 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_101 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_102 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_103 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_104 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_4_0_105 => solve | omega | (simp <;> omega) | assumption | simp_all
          )
          all_goals clear hz
          all_goals simp_all [CertificateFamilyEntries.rayEntry,Data,Represents,arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
        · let jj:Fin n:= ⟨j.val - n,by omega⟩
          have hload:=RamCertificateLoad.objective_spec B m n P jj h1 (jj.isLt.trans hn) ((hc jj).trans_lt hMB)
          have hneg:=RamResultNegation.negateResult_spec B (P.c jj:ℚ) h1
          (expose_names;
            refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((64:Nat))) (c3 σ'); let c5:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "source.n"); let c6:Prop:=Not c5; let c7:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col"; let c8:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat→ Nat:=Nat.mul; let c11:String→ Nat:=Env.vars c8; let c12:Nat:=c11 "query.a.row"; let c13:Nat:=c11 "source.n"; let c14:Nat:=c10 c12 c13; let c15:Nat:=c11 "query.a.col"; let c16:Nat:=c9 c14 c15; let c17:Env:=Env.setVar c8 "vec.i" c16; let c18:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.A"; let c19:String:=c18 ".s"; let c20:Nat:=Env.vars c17 "vec.i"; let c21:Nat:= @List.getD Nat (Env.arrs c17 c19) c20 ((0:Nat)); let c22:Env:=Env.setVar c17 "left.s" c21; let c23:String:=c18 ".n"; let c24:Nat:=Env.vars c22 "vec.i"; let c25:Nat:= @List.getD Nat (Env.arrs c22 c23) c24 ((0:Nat)); let c26:Env:=Env.setVar c22 "left.n" c25; let c27:String:=c18 ".d"; let c28:Nat:=Env.vars c26 "vec.i"; let c29:Nat:= @List.getD Nat (Env.arrs c26 c27) c28 ((0:Nat)); let c30:Env:=Env.setVar c26 "left.d" c29; let c31:Nat:=Env.vars c30 "left.s"; let c32:Env:=Env.setVar c30 "rat.s" c31; let c33:Nat:=Env.vars c32 "left.n"; let c34:Env:=Env.setVar c32 "rat.n" c33; let c35:Nat:=Env.vars c34 "left.d"; let c36:Env:=Env.setVar c34 "rat.d" c35; let c37:Nat→ Nat:=c9 ((1:Nat)); let c38:Nat→ Nat:=c9 (c37 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c39:Nat→ Nat:=c9 (c37 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "source.n")))); let c40:Nat:=c37 (Expr.size (Expr.var "query.row")); let c41:Nat:=c37 (Expr.size (Expr.var "query.col")); let c42:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c43:Nat:=c37 (Expr.size c42); let c44:Expr:=Expr.get c19 (Expr.var "vec.i"); let c45:Nat:=c37 (Expr.size c44); let c46:Expr:=Expr.get c23 (Expr.var "vec.i"); let c47:Nat:=c37 (Expr.size c46); let c48:Expr:=Expr.get c27 (Expr.var "vec.i"); let c49:Nat:=c37 (Expr.size c48); let c50:Nat:=c9 c47 c49; let c51:Nat:=c9 c45 c50; let c52:Nat:=c37 (Expr.size (Expr.var "left.s")); let c53:Nat:=c37 (Expr.size (Expr.var "left.n")); let c54:Nat:=c37 (Expr.size (Expr.var "left.d")); let c55:Nat:=c9 c53 c54; let c56:Nat:=c9 c52 c55; let c57:Nat:=c9 c51 c56; let c58:Nat:=c9 c43 c57; let c59:Nat:=c9 c41 c58; let c60:Nat:=c9 c40 c59; let c61:Nat:=c39 c60; let c62:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix); let c63:Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c62 (RamPadSelector.constantFraction ((0:Nat))); let c64:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c65:Com→ Com:=Com.ite (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))); let c66:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c67:Com:=Com.assign "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c68:Com:=Com.seq c67 RamCertificateLoad.matrix; let c69:Com:=Com.seq c66 c68; let c70:Com:=c65 c69; let c71:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")); let c72:Com:=Com.seq c71 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c73:Com:=c65 c72; let c74:Com:=Com.ite c64 c70 c73; let c75:Com:=Com.assign "left.n" c46; let c76:Com:=Com.assign "left.d" c48; let c77:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c78:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c79:Env→ Prop:=fun (σ':Env) => And (c77 σ' ((6:Nat))) (c78 σ'); let c80:Nat:=c39 ((6:Nat)); let c81:Nat:=c9 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c82:Prop:=Nat.lt (Env.vars σ "query.row") c81; let c83:Prop:=Not c82; let c84:Nat→ Nat:=c9 (c37 (Cond.size c64)); let c85:Nat:=c84 c80; let c86:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c87:Nat:=c86 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c88:Env:=Env.setVar σ "query.a.row" c87; let c89:String→ Nat:=Env.vars c88; let c90:Nat:=c89 "query.col"; let c91:Nat:=c89 "source.n"; let c92:Nat:=c86 c90 c91; let c93:Env:=Env.setVar c88 "query.a.col" c92; let c94:String→ Nat:=Env.vars c93; let c95:Nat:=c94 "query.a.row"; let c96:Nat:=c94 "source.n"; let c97:Nat:=c10 c95 c96; let c98:Nat:=c94 "query.a.col"; let c99:Nat:=c9 c97 c98; let c100:Env:=Env.setVar c93 "vec.i" c99; let c101:Nat:=Env.vars c100 "vec.i"; let c102:Nat:= @List.getD Nat (Env.arrs c100 c19) c101 ((0:Nat)); let c103:Env:=Env.setVar c100 "left.s" c102; let c104:Nat:=Env.vars c103 "vec.i"; let c105:Nat:= @List.getD Nat (Env.arrs c103 c23) c104 ((0:Nat)); let c106:Env:=Env.setVar c103 "left.n" c105; let c107:Nat:=Env.vars c106 "vec.i"; let c108:Nat:= @List.getD Nat (Env.arrs c106 c27) c107 ((0:Nat)); let c109:Env:=Env.setVar c106 "left.d" c108; let c110:Nat:=Env.vars c109 "left.s"; let c111:Env:=Env.setVar c109 "rat.s" c110; let c112:Nat:=Env.vars c111 "left.n"; let c113:Env:=Env.setVar c111 "rat.n" c112; let c114:Nat:=Env.vars c113 "left.d"; let c115:Env:=Env.setVar c113 "rat.d" c114; let c116:Nat:=c37 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c117:Nat:=c37 (Expr.size (Expr.sub (Expr.var "query.col") (Expr.var "source.n"))); let c118:Nat→ Nat:=c9 c117; let c119:Nat:=c118 c58; let c120:Nat:=c9 c116 c119; let c121:Nat:=c39 c120; let c122:Nat:=c84 c121; let c123:Nat:=c86 (Env.vars σ "query.col") (Env.vars σ "source.n"); let c124:Env:=Env.setVar σ "query.a.row" c123; let c125:Env→ Nat→ Prop:=Run B (RamCertificateLoad.vector "source.c") c124; let c126:Rat:= @Int.cast Rat Rat.instIntCast (@Program.c Int m n P jj); let c127:Env→ Prop:=FractionOutput c126; let c128:Env→ Prop:=fun (σ':Env) => And (c125 σ' ((17:Nat))) (And (@Data m n P σ') (c127 σ')); let c129:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg c126); let c130:Nat:=c9 ((17:Nat)) ((4:Nat)); let c131:Nat:=c118 c130; let c132:Nat:=c39 c131; let c133:Nat:=c84 c132; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_1:c5) => @Exists.intro Env c4 c36 (@And.intro (Run B selectEntry σ c36 ((64:Nat))) (c3 c36) (RunStep.mono B selectEntry σ c36 (c38 c61) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ c36 c61 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c62 (RamPadSelector.constantFraction ((0:Nat))) σ c36 c60 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_3)) hcase_1) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (Com.seq (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix) σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c36 c40 c59 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_4))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.col")) RamCertificateLoad.matrix (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c8 c36 c41 c58 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.col" (Expr.var "query.col") c7 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.col" (?nAX_g5054_5_0_5))) (RunStep.seq B (Com.assign "vec.i" c42) (RamArrayResult.load "source.A") c8 c17 c36 c43 c57 (RunStep.assign B c8 "vec.i" c42 c16 (RunStep.eval_add B c8 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c14 c15 (RunStep.eval_mul B c8 (Expr.var "query.a.row") (Expr.var "source.n") c12 c13 (RunStep.eval_var B c8 "query.a.row" (?nAX_g5054_5_0_6)) (RunStep.eval_var B c8 "source.n" (?nAX_g5054_5_0_7)) (?nAX_g5054_5_0_8)) (RunStep.eval_var B c8 "query.a.col" (?nAX_g5054_5_0_9)) (?nAX_g5054_5_0_10))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c17 c30 c36 c51 c56 (RunStep.seq B (Com.assign "left.s" c44) (Com.seq c75 c76) c17 c22 c30 c45 c50 (RunStep.assign B c17 "left.s" c44 c21 (RunStep.eval_get B c17 c19 (Expr.var "vec.i") c20 (RunStep.eval_var B c17 "vec.i" (?nAX_g5054_5_0_11)) (?nAX_g5054_5_0_12) (?nAX_g5054_5_0_13))) (RunStep.seq B c75 c76 c22 c26 c30 c47 c49 (RunStep.assign B c22 "left.n" c46 c25 (RunStep.eval_get B c22 c23 (Expr.var "vec.i") c24 (RunStep.eval_var B c22 "vec.i" (?nAX_g5054_5_0_14)) (?nAX_g5054_5_0_15) (?nAX_g5054_5_0_16))) (RunStep.assign B c26 "left.d" c48 c29 (RunStep.eval_get B c26 c27 (Expr.var "vec.i") c28 (RunStep.eval_var B c26 "vec.i" (?nAX_g5054_5_0_17)) (?nAX_g5054_5_0_18) (?nAX_g5054_5_0_19))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c30 c32 c36 c52 c55 (RunStep.assign B c30 "rat.s" (Expr.var "left.s") c31 (RunStep.eval_var B c30 "left.s" (?nAX_g5054_5_0_20))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c32 c34 c36 c53 c54 (RunStep.assign B c32 "rat.n" (Expr.var "left.n") c33 (RunStep.eval_var B c32 "left.n" (?nAX_g5054_5_0_21))) (RunStep.assign B c34 "rat.d" (Expr.var "left.d") c35 (RunStep.eval_var B c34 "left.d" (?nAX_g5054_5_0_22))))))))))) (?nAX_g5054_5_0_23)) ?_)) fun (hcase_1:c6) => @Exists.casesOn Env c79 (fun (x:@Exists Env c79) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c78 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c77 w ((6:Nat))) (c78 w)) => let c0:Prop:=c77 w ((6:Nat)); @And.casesOn c0 (c78 w) (fun (x:And c0 (c78 w)) => @Exists Env c4) h fun (left:c0) (right:c78 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c38 c80) ((64:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ w c80 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_24)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_25)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) c62 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_26)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_27)) hcase_1) left)) (?nAX_g5054_5_0_28)) ?_)) fun (hcase:c1) => @Or.casesOn c82 c83 (fun (x:Or c82 c83) => @Exists Env c4) (Classical.em c82) (fun (hcase_1:c82) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c79 (fun (x:@Exists Env c79) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c78 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c77 w ((6:Nat))) (c78 w)) => let c0:Prop:=c77 w ((6:Nat)); @And.casesOn c0 (c78 w) (fun (x:And c0 (c78 w)) => @Exists Env c4) h fun (left:c0) (right:c78 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c38 c85) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ w c85 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_30)) hcase) (RunStep.ite_true B c64 c70 c73 σ w c80 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c81 (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_31)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_33)) (?nAX_g5054_5_0_34)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c69 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_35)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_36)) hcase_2) left))) (?nAX_g5054_5_0_37)) ?_)) fun (hcase_2:c6) => @Exists.intro Env c4 c115 (@And.intro (Run B selectEntry σ c115 ((64:Nat))) (c3 c115) (RunStep.mono B selectEntry σ c115 (c38 c122) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ c115 c122 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_38)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_39)) hcase) (RunStep.ite_true B c64 c70 c73 σ c115 c121 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c81 (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_40)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_41)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_42)) (?nAX_g5054_5_0_43)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c69 σ c115 c120 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_44)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_45)) hcase_2) (RunStep.seq B c66 c68 σ c88 c115 c116 c119 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c87 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_46)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_47)) (?nAX_g5054_5_0_48))) (RunStep.seq B c67 RamCertificateLoad.matrix c88 c93 c115 c117 c58 (RunStep.assign B c88 "query.a.col" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c92 (RunStep.eval_sub B c88 (Expr.var "query.col") (Expr.var "source.n") c90 c91 (RunStep.eval_var B c88 "query.col" (?nAX_g5054_5_0_49)) (RunStep.eval_var B c88 "source.n" (?nAX_g5054_5_0_50)) (?nAX_g5054_5_0_51))) (RunStep.seq B (Com.assign "vec.i" c42) (RamArrayResult.load "source.A") c93 c100 c115 c43 c57 (RunStep.assign B c93 "vec.i" c42 c99 (RunStep.eval_add B c93 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c97 c98 (RunStep.eval_mul B c93 (Expr.var "query.a.row") (Expr.var "source.n") c95 c96 (RunStep.eval_var B c93 "query.a.row" (?nAX_g5054_5_0_52)) (RunStep.eval_var B c93 "source.n" (?nAX_g5054_5_0_53)) (?nAX_g5054_5_0_54)) (RunStep.eval_var B c93 "query.a.col" (?nAX_g5054_5_0_55)) (?nAX_g5054_5_0_56))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c100 c109 c115 c51 c56 (RunStep.seq B (Com.assign "left.s" c44) (Com.seq c75 c76) c100 c103 c109 c45 c50 (RunStep.assign B c100 "left.s" c44 c102 (RunStep.eval_get B c100 c19 (Expr.var "vec.i") c101 (RunStep.eval_var B c100 "vec.i" (?nAX_g5054_5_0_57)) (?nAX_g5054_5_0_58) (?nAX_g5054_5_0_59))) (RunStep.seq B c75 c76 c103 c106 c109 c47 c49 (RunStep.assign B c103 "left.n" c46 c105 (RunStep.eval_get B c103 c23 (Expr.var "vec.i") c104 (RunStep.eval_var B c103 "vec.i" (?nAX_g5054_5_0_60)) (?nAX_g5054_5_0_61) (?nAX_g5054_5_0_62))) (RunStep.assign B c106 "left.d" c48 c108 (RunStep.eval_get B c106 c27 (Expr.var "vec.i") c107 (RunStep.eval_var B c106 "vec.i" (?nAX_g5054_5_0_63)) (?nAX_g5054_5_0_64) (?nAX_g5054_5_0_65))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c109 c111 c115 c52 c55 (RunStep.assign B c109 "rat.s" (Expr.var "left.s") c110 (RunStep.eval_var B c109 "left.s" (?nAX_g5054_5_0_66))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c111 c113 c115 c53 c54 (RunStep.assign B c111 "rat.n" (Expr.var "left.n") c112 (RunStep.eval_var B c111 "left.n" (?nAX_g5054_5_0_67))) (RunStep.assign B c113 "rat.d" (Expr.var "left.d") c114 (RunStep.eval_var B c113 "left.d" (?nAX_g5054_5_0_68)))))))))))) (?nAX_g5054_5_0_69)) ?_)) fun (hcase_1:c83) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_2:c5) => @Exists.casesOn Env c79 (fun (x:@Exists Env c79) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c78 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c77 w ((6:Nat))) (c78 w)) => let c0:Prop:=c77 w ((6:Nat)); @And.casesOn c0 (c78 w) (fun (x:And c0 (c78 w)) => @Exists Env c4) h fun (left:c0) (right:c78 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((64:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c38 c85) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ w c85 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_70)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_71)) hcase) (RunStep.ite_false B c64 c70 c73 σ w c80 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c81 (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_72)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_73)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_74)) (?nAX_g5054_5_0_75)) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c72 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_76)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_77)) hcase_2) left))) (?nAX_g5054_5_0_78)) ?_)) fun (hcase_2:c6) => @Exists.casesOn Env c128 (fun (x:@Exists Env c128) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val n jj))) (RamCertificateLoad.vector "source.c") (fun (x τ:Env) => And (@Data m n P τ) (c127 τ)) ((17:Nat)) hload c124 ?_) fun (w:Env) (h:And (c125 w ((17:Nat))) (And (@Data m n P w) (c127 w))) => let c0:Prop:=c125 w ((17:Nat)); let c1:Prop:=And (@Data m n P w) (c127 w); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult w σ' ((4:Nat))) (c129 σ'); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c4) (RunStep.use B c127 RamResultNegation.negateResult (fun (x τ:Env) => c129 τ) ((4:Nat)) hneg w ?_) fun (w_1:Env) (h:And (Run B RamResultNegation.negateResult w w_1 ((4:Nat))) (c129 w_1)) => let c0:Prop:=Run B RamResultNegation.negateResult w w_1 ((4:Nat)); @And.casesOn c0 (c129 w_1) (fun (x:And c0 (c129 w_1)) => @Exists Env c4) h fun (left_1:c0) (right:c129 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectEntry σ w_1 ((64:Nat))) (c3 w_1) (RunStep.mono B selectEntry σ w_1 (c38 c133) ((64:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c63 c74 σ w_1 c133 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_79)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_80)) hcase) (RunStep.ite_false B c64 c70 c73 σ w_1 c132 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c81 (RunStep.eval_var B σ "query.row" (?nAX_g5054_5_0_81)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_82)) (RunStep.eval_var B σ "source.m" (?nAX_g5054_5_0_83)) (?nAX_g5054_5_0_84)) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "source.n")) (RamPadSelector.constantFraction ((0:Nat))) c72 σ w_1 c131 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_85)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_86)) hcase_2) (RunStep.seq B c71 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c124 w_1 c117 c130 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.col") (Expr.var "source.n")) c123 (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "source.n") (Env.vars σ "query.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.col" (?nAX_g5054_5_0_87)) (RunStep.eval_var B σ "source.n" (?nAX_g5054_5_0_88)) (?nAX_g5054_5_0_89))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c124 w w_1 ((17:Nat)) ((4:Nat)) left left_1))))) (?nAX_g5054_5_0_90)) ?_) <;> try dsimp +zetaDelta at *
           all_goals try dsimp +zetaDelta at *
           try case' nAX_g5054_5_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all
           try case' nAX_g5054_5_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all
          )
          all_goals clear hload hneg hz
          all_goals simp_all [CertificateFamilyEntries.rayEntry,jj,Data,Represents,arrs_setVar]
          all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

set_option maxHeartbeats 800000 in
theorem selectBound_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + (m + 1)))
    (hM:1≤ M) (hMB:M < B) (hB:2 * m + 4 < B) (hb:∀ r, (P.b r).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.rayRhs P i:ℚ) τ) 32:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hmm:m + m < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hz:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have ho:=RamPadSelector.constantFraction_spec B 1 h1 h1
  have hneg:=RamResultNegation.negateResult_spec B 1 h1
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => FractionOutput (CertificateFamilyEntries.rayRhs P i:ℚ) τ) 32:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσrow⟩
    by_cases hi:i.val < m
    · let ii:Fin m:= ⟨i.val,hi⟩
      have hload:=RamCertificateLoad.bound_spec B m n P ii h1 (ii.isLt.trans hm) ((hb ii).trans_lt hMB)
      (expose_names;
        refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayRhs m n P i)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((32:Nat))) (c3 σ'); let c5:Env→ Nat→ Prop:=Run B (RamCertificateLoad.vector "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.row")); let c6:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.b Int m n P ii)); let c7:Env→ Prop:=fun (σ':Env) => And (c5 σ' ((17:Nat))) (And (@Data m n P σ') (c6 σ')); let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat→ Nat:=c8 ((1:Nat)); let c10:Nat→ Nat:=c8 (c9 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c11:Nat:=c9 (Expr.size (Expr.var "query.row")); let c12:Nat:=c8 c11 ((17:Nat)); let c13:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b"); let c14:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")); let c15:Com:=Com.seq (RamPadSelector.constantFraction ((1:Nat))) RamResultNegation.negateResult; let c16:Com:=Com.ite c14 (RamPadSelector.constantFraction ((0:Nat))) c15; let c17:Nat:=c8 (Env.vars σ "source.m") (Env.vars σ "source.m"); let c18:Prop:=Nat.lt (Env.vars σ "query.row") c17; let c19:Prop:=Not c18; let c20:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c21:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c22:Env→ Prop:=fun (σ':Env) => And (c20 σ' ((6:Nat))) (c21 σ'); let c23:Nat→ Nat:=c8 (c9 (Cond.size c14)); let c24:Nat:=c23 ((6:Nat)); let c25:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((1:Nat))) σ; let c26:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat))); let c27:Env→ Prop:=fun (σ':Env) => And (c25 σ' ((6:Nat))) (c26 σ'); let c28:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c29:Nat:=c8 ((6:Nat)) ((4:Nat)); let c30:Nat:=c23 c29; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => @Exists Env c4) (RunStep.use B (fun (σ:Env) => And (@Data m n P σ) (@Eq Nat (Env.vars σ "query.a.row") (@Fin.val m ii))) (RamCertificateLoad.vector "source.b") (fun (x τ:Env) => And (@Data m n P τ) (c6 τ)) ((17:Nat)) hload (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) ?_) fun (w:Env) (h:And (c5 w ((17:Nat))) (And (@Data m n P w) (c6 w))) => let c0:Prop:=c5 w ((17:Nat)); let c1:Prop:=And (@Data m n P w) (c6 w); @And.casesOn c0 c1 (fun (x:And c0 c1) => @Exists Env c4) h fun (left:c0) (right:c1) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((32:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c10 c12) ((32:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c16 σ w c12 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) w c11 ((17:Nat)) (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_2))) left)) (?nAX_g5056_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => @Exists Env c4) (Classical.em c18) (fun (hcase_1:c18) => @Exists.casesOn Env c22 (fun (x:@Exists Env c22) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c21 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c20 w ((6:Nat))) (c21 w)) => let c0:Prop:=c20 w ((6:Nat)); @And.casesOn c0 (c21 w) (fun (x:And c0 (c21 w)) => @Exists Env c4) h fun (left:c0) (right:c21 w) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((32:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c10 c24) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c16 σ w c24 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_4)) (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_5)) hcase) (RunStep.ite_true B c14 (RamPadSelector.constantFraction ((0:Nat))) c15 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c17 (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_6)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_7)) (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_8)) (?nAX_g5056_0_0_9)) hcase_1) left)) (?nAX_g5056_0_0_10)) ?_)) fun (hcase_1:c19) => @Exists.casesOn Env c27 (fun (x:@Exists Env c27) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((1:Nat))) (fun (x τ:Env) => c26 τ) ((6:Nat)) ho σ ?_) fun (w:Env) (h:And (c25 w ((6:Nat))) (c26 w)) => let c0:Prop:=c25 w ((6:Nat)); let c1:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult w σ' ((4:Nat))) (c28 σ'); @And.casesOn c0 (c26 w) (fun (x:And c0 (c26 w)) => @Exists Env c4) h fun (left:c0) (right:c26 w) => @Exists.casesOn Env c1 (fun (x:@Exists Env c1) => @Exists Env c4) (RunStep.use B (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) RamResultNegation.negateResult (fun (x τ:Env) => c28 τ) ((4:Nat)) hneg w ?_) fun (w_1:Env) (h:And (Run B RamResultNegation.negateResult w w_1 ((4:Nat))) (c28 w_1)) => let c0:Prop:=Run B RamResultNegation.negateResult w w_1 ((4:Nat)); @And.casesOn c0 (c28 w_1) (fun (x:And c0 (c28 w_1)) => @Exists Env c4) h fun (left_1:c0) (right:c28 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectBound σ w_1 ((32:Nat))) (c3 w_1) (RunStep.mono B selectBound σ w_1 (c10 c30) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c16 σ w_1 c30 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_11)) (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_12)) hcase) (RunStep.ite_false B c14 (RamPadSelector.constantFraction ((0:Nat))) c15 σ w_1 c29 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c17 (RunStep.eval_var B σ "query.row" (?nAX_g5056_0_0_13)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m") (Env.vars σ "source.m") (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_14)) (RunStep.eval_var B σ "source.m" (?nAX_g5056_0_0_15)) (?nAX_g5056_0_0_16)) hcase_1) (RunStep.seq B (RamPadSelector.constantFraction ((1:Nat))) RamResultNegation.negateResult σ w w_1 ((6:Nat)) ((4:Nat)) left left_1))) (?nAX_g5056_0_0_17)) ?_) <;> try dsimp +zetaDelta at *
       all_goals try dsimp +zetaDelta at *
       try case' nAX_g5056_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all
       try case' nAX_g5056_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all
      )
      all_goals clear hload hz ho hneg
      all_goals simp_all [CertificateFamilyEntries.rayRhs,ii,Data,Represents,arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hir:i.val < m + m
      all_goals (expose_names;
                  refine
                      let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m");
                      let c1:Prop:=Not c0;
                      let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.rayRhs m n P i));
                      let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ;
                      let c4:Env→ Prop:=fun (σ':Env) =>
                        And (Run B selectBound σ σ' ((32:Nat))) (c3 σ');
                      let c5:Prop:= @Exists Env c4;
                      let c6:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row";
                      let c7:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i" c6;
                      let c8:String→ String:=
                        @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.b";
                      let c9:String:=c8 ".s";
                      let c10:Nat:=Env.vars c7 "vec.i";
                      let c11:Nat:= @List.getD Nat (Env.arrs c7 c9) c10 ((0:Nat));
                      let c12:Env:=Env.setVar c7 "left.s" c11;
                      let c13:String:=c8 ".n";
                      let c14:Nat:=Env.vars c12 "vec.i";
                      let c15:Nat:= @List.getD Nat (Env.arrs c12 c13) c14 ((0:Nat));
                      let c16:Env:=Env.setVar c12 "left.n" c15;
                      let c17:String:=c8 ".d";
                      let c18:Nat:=Env.vars c16 "vec.i";
                      let c19:Nat:= @List.getD Nat (Env.arrs c16 c17) c18 ((0:Nat));
                      let c20:Env:=Env.setVar c16 "left.d" c19;
                      let c21:Nat:=Env.vars c20 "left.s";
                      let c22:Env:=Env.setVar c20 "rat.s" c21;
                      let c23:Nat:=Env.vars c22 "left.n";
                      let c24:Env:=Env.setVar c22 "rat.n" c23;
                      let c25:Nat:=Env.vars c24 "left.d";
                      let c26:Env:=Env.setVar c24 "rat.d" c25;
                      let c27:Nat→ Nat→ Nat:=Nat.add;
                      let c28:Nat→ Nat:=c27 ((1:Nat));
                      let c29:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m"))));
                      let c30:Nat:=c28 (Expr.size (Expr.var "query.row"));
                      let c31:Nat:=c28 (Expr.size (Expr.var "query.a.row"));
                      let c32:Expr:=Expr.get c9 (Expr.var "vec.i");
                      let c33:Nat:=c28 (Expr.size c32);
                      let c34:Expr:=Expr.get c13 (Expr.var "vec.i");
                      let c35:Nat:=c28 (Expr.size c34);
                      let c36:Expr:=Expr.get c17 (Expr.var "vec.i");
                      let c37:Nat:=c28 (Expr.size c36);
                      let c38:Nat:=c27 c35 c37;
                      let c39:Nat:=c27 c33 c38;
                      let c40:Nat:=c28 (Expr.size (Expr.var "left.s"));
                      let c41:Nat:=c28 (Expr.size (Expr.var "left.n"));
                      let c42:Nat:=c28 (Expr.size (Expr.var "left.d"));
                      let c43:Nat:=c27 c41 c42;
                      let c44:Nat:=c27 c40 c43;
                      let c45:Nat:=c27 c39 c44;
                      let c46:Nat:=c27 c31 c45;
                      let c47:Nat:=c27 c30 c46;
                      let c48:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b");
                      let c49:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.m"));
                      let c50:Com:=
                        Com.seq (RamPadSelector.constantFraction ((1:Nat)))
                          RamResultNegation.negateResult;
                      let c51:Com:=
                        Com.ite c49 (RamPadSelector.constantFraction ((0:Nat))) c50;
                      let c52:Com:=Com.assign "left.n" c34;
                      let c53:Com:=Com.assign "left.d" c36;
                      let c54:Nat:=c27 (Env.vars σ "source.m") (Env.vars σ "source.m");
                      let c55:Prop:=Nat.lt (Env.vars σ "query.row") c54;
                      let c56:Prop:=Not c55;
                      let c57:Env→ Nat→ Prop:=
                        Run B (RamPadSelector.constantFraction ((0:Nat))) σ;
                      let c58:Env→ Prop:=
                        FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat)));
                      let c59:Env→ Prop:=fun (σ':Env) =>
                        And (c57 σ' ((6:Nat))) (c58 σ');
                      let c60:Nat→ Nat:=c27 (c28 (Cond.size c49));
                      let c61:Nat:=c60 ((6:Nat));
                      let c62:Env→ Nat→ Prop:=
                        Run B (RamPadSelector.constantFraction ((1:Nat))) σ;
                      let c63:Env→ Prop:=
                        FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat)));
                      let c64:Env→ Prop:=fun (σ':Env) =>
                        And (c62 σ' ((6:Nat))) (c63 σ');
                      let c65:Env→ Prop:=
                        FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))));
                      let c66:Nat:=
                        c27 ((6:Nat))
                          ((4:Nat));
                      let c67:Nat:=c60 c66;
                      @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0)
                        (fun (hcase:c0) =>
                          @Exists.intro Env c4 c26
                            (@And.intro (Run B selectBound σ c26 ((32:Nat))) (c3 c26)
                              (RunStep.mono B selectBound σ c26 (c29 c47) ((32:Nat))
                                (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c48 c51 σ c26 c47
                                  (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row")
                                    (Env.vars σ "source.m")
                                    (RunStep.eval_var B σ "query.row"
                                      ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                    (RunStep.eval_var B σ "source.m"
                                      ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                    hcase)
                                  (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row"))
                                    (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c26
                                    c30 c46
                                    (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row")
                                      (RunStep.eval_var B σ "query.row"
                                        ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                    (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.b")
                                      (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c7 c26 c31 c45
                                      (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i"
                                        (Expr.var "query.a.row") c6
                                        (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row"
                                          ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                      (RunStep.seq B (loadLeft "source.b") RamCopy.leftToResult c7 c20 c26 c39 c44
                                        (RunStep.seq B (Com.assign "left.s" c32) (Com.seq c52 c53) c7 c12 c20 c33 c38
                                          (RunStep.assign B c7 "left.s" c32 c11
                                            (RunStep.eval_get B c7 c9 (Expr.var "vec.i") c10
                                              (RunStep.eval_var B c7 "vec.i"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                          (RunStep.seq B c52 c53 c12 c16 c20 c35 c37
                                            (RunStep.assign B c12 "left.n" c34 c15
                                              (RunStep.eval_get B c12 c13 (Expr.var "vec.i") c14
                                                (RunStep.eval_var B c12 "vec.i"
                                                  ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                            (RunStep.assign B c16 "left.d" c36 c19
                                              (RunStep.eval_get B c16 c17 (Expr.var "vec.i") c18
                                                (RunStep.eval_var B c16 "vec.i"
                                                  ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))))
                                        (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s"))
                                          (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")))
                                          c20 c22 c26 c40 c43
                                          (RunStep.assign B c20 "rat.s" (Expr.var "left.s") c21
                                            (RunStep.eval_var B c20 "left.s"
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                          (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n"))
                                            (Com.assign "rat.d" (Expr.var "left.d")) c22 c24 c26 c41 c42
                                            (RunStep.assign B c22 "rat.n" (Expr.var "left.n") c23
                                              (RunStep.eval_var B c22 "left.n"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))
                                            (RunStep.assign B c24 "rat.d" (Expr.var "left.d") c25
                                              (RunStep.eval_var B c24 "left.d"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all))))))))))
                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                              ?_))
                        fun (hcase:c1) =>
                        @Or.casesOn c55 c56 (fun (x:Or c55 c56) => c5) (Classical.em c55)
                          (fun (hcase_1:c55) =>
                            @Exists.casesOn Env c59 (fun (x:@Exists Env c59) => c5)
                              (RunStep.use B (fun (x:Env) => True)
                                (RamPadSelector.constantFraction ((0:Nat)))
                                (fun (x τ:Env) => c58 τ) ((6:Nat)) hz σ ?_)
                              fun (w:Env) (h:And (c57 w ((6:Nat))) (c58 w)) =>
                              let c0:Prop:=c57 w ((6:Nat));
                              @And.casesOn c0 (c58 w) (fun (x:And c0 (c58 w)) => c5) h fun (left:c0) (right:c58 w) =>
                                @Exists.intro Env c4 w
                                  (@And.intro (Run B selectBound σ w ((32:Nat))) (c3 w)
                                    (RunStep.mono B selectBound σ w (c29 c61)
                                      ((32:Nat))
                                      (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c48 c51 σ w c61
                                        (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row")
                                          (Env.vars σ "source.m")
                                          (RunStep.eval_var B σ "query.row"
                                            ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                          (RunStep.eval_var B σ "source.m"
                                            ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                          hcase)
                                        (RunStep.ite_true B c49
                                          (RamPadSelector.constantFraction ((0:Nat)))
                                          c50 σ w ((6:Nat))
                                          (RunStep.cond_lt_true B σ (Expr.var "query.row")
                                            (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c54
                                            (RunStep.eval_var B σ "query.row"
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                            (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m")
                                              (Env.vars σ "source.m")
                                              (RunStep.eval_var B σ "source.m"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                              (RunStep.eval_var B σ "source.m"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                            hcase_1)
                                          left))
                                      ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                    ?_))
                          fun (hcase_1:c56) =>
                          @Exists.casesOn Env c64 (fun (x:@Exists Env c64) => c5)
                            (RunStep.use B (fun (x:Env) => True)
                              (RamPadSelector.constantFraction ((1:Nat)))
                              (fun (x τ:Env) => c63 τ) ((6:Nat)) ho σ ?_)
                            fun (w:Env) (h:And (c62 w ((6:Nat))) (c63 w)) =>
                            let c0:Prop:=c62 w ((6:Nat));
                            let c1:Env→ Prop:=fun (σ':Env) =>
                              And (Run B RamResultNegation.negateResult w σ' ((4:Nat)))
                                (c65 σ');
                            @And.casesOn c0 (c63 w) (fun (x:And c0 (c63 w)) => c5) h fun (left:c0) (right:c63 w) =>
                              @Exists.casesOn Env c1 (fun (x:@Exists Env c1) => c5)
                                (RunStep.use B (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                                  RamResultNegation.negateResult (fun (x τ:Env) => c65 τ)
                                  ((4:Nat)) hneg w ?_)
                                fun (w_1:Env)
                                  (h:
                                    And
                                      (Run B RamResultNegation.negateResult w w_1
                                        ((4:Nat)))
                                      (c65 w_1)) =>
                                let c0:Prop:=
                                  Run B RamResultNegation.negateResult w w_1 ((4:Nat));
                                @And.casesOn c0 (c65 w_1) (fun (x:And c0 (c65 w_1)) => c5) h fun (left_1:c0) (right:c65 w_1) =>
                                  @Exists.intro Env c4 w_1
                                    (@And.intro (Run B selectBound σ w_1 ((32:Nat)))
                                      (c3 w_1)
                                      (RunStep.mono B selectBound σ w_1 (c29 c67)
                                        ((32:Nat))
                                        (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c48 c51 σ w_1 c67
                                          (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m")
                                            (Env.vars σ "query.row") (Env.vars σ "source.m")
                                            (RunStep.eval_var B σ "query.row"
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                            (RunStep.eval_var B σ "source.m"
                                              ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                            hcase)
                                          (RunStep.ite_false B c49
                                            (RamPadSelector.constantFraction ((0:Nat)))
                                            c50 σ w_1 c66
                                            (RunStep.cond_lt_false B σ (Expr.var "query.row")
                                              (Expr.add (Expr.var "source.m") (Expr.var "source.m")) (Env.vars σ "query.row") c54
                                              (RunStep.eval_var B σ "query.row"
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                              (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.m") (Env.vars σ "source.m")
                                                (Env.vars σ "source.m")
                                                (RunStep.eval_var B σ "source.m"
                                                  ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                                (RunStep.eval_var B σ "source.m"
                                                  ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                                ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                              hcase_1)
                                            (RunStep.seq B
                                              (RamPadSelector.constantFraction
                                                ((1:Nat)))
                                              RamResultNegation.negateResult σ w w_1
                                              ((6:Nat))
                                              ((4:Nat)) left left_1)))
                                        ((by dsimp +zetaDelta at *; first | omega | (simp <;> omega) | assumption | simp_all)))
                                      ?_) <;> try dsimp +zetaDelta at *
                 all_goals try dsimp +zetaDelta at *
                )
      all_goals clear hz ho hneg
      all_goals simp_all [CertificateFamilyEntries.rayRhs]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

end Lax109476Proofs.RamRaySelector

end

section

namespace Lax109476Proofs.CertificateFamilyHeight

open Lax109476.LinearProgram
open CertificateFamilyPrograms CertificateFamilyEntries

theorem unbounded_A_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hc:∀ j, (P.c j).natAbs≤ M):
    ∀ i j, ((unbounded P).A i j).natAbs≤ M:=by
  intro i j
  rw [← rayEntry_eq]
  unfold rayEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem unbounded_b_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ) (hM:1≤ M)
    (hb:∀ i, (P.b i).natAbs≤ M):∀ i, ((unbounded P).b i).natAbs≤ M:=by
  intro i
  rw [← rayRhs_eq]
  unfold rayRhs
  split_ifs <;> simp_all

end Lax109476Proofs.CertificateFamilyHeight

end

section

namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource CertificateFamilyPrograms CertificateFamilyEntries

theorem withMetadata_spec (B m n r s metadataCost buildCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (metadata matrixSelector boundSelector:Com)
    (hmetadata:Spec B (Data P) metadata (fun _ τ => RamCertificateContext.Context P r s τ) metadataCost)
    (hbuild:Spec B (fun σ => RamCertificateContext.Context P r s σ∧ Extents "system.A" (r * s) σ∧ Extents "system.b" r σ)
      (RamCertificateBuilder.buildSystem matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) buildCost):
    Spec B (Input P r s) (withMetadata metadata matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) (metadataCost + buildCost):=by
  rintro σ ⟨hσData,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτContext⟩:=hmetadata σ hσData
  obtain ⟨υ,hr₂,hυ⟩:=hbuild τ ⟨hτContext,
    RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσA,
    RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

theorem unbounded_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hSource:m * n + 2 * m + 2 * n + 8 < B)
    (hSystem:(m + (m + 1)) * (n + n) + (m + (m + 1)) + (n + n) + 4 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M)
    (hc:∀ j, (P.c j).natAbs≤ M):
    Spec B (Input P (m + (m + 1)) (n + n)) unbounded
      (fun _ τ => Data P τ∧ RamEquationData.Data (CertificateFamilyPrograms.unbounded P) τ)
      (134 * ((m + (m + 1)) * (n + n)) + 90 * (m + (m + 1)) + 74):=by
  have hbuild:=RamCertificateBuilder.buildSystem_spec B M m n (m + (m + 1)) (n + n) 64 32 P
    (CertificateFamilyPrograms.unbounded P) RamRaySelector.selectEntry RamRaySelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.unbounded_A_bound P M hA hc) (CertificateFamilyHeight.unbounded_b_bound P M hM hb)
    (fun i j => by simpa only [rayEntry_eq] using RamRaySelector.selectEntry_spec B M m n P i j hM hMB hSource hA hc)
    (fun i => by simpa only [rayRhs_eq] using RamRaySelector.selectBound_spec B M m n P i hM hMB (by omega) hb)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (m + (m + 1)) (n + n) 12 _ P (CertificateFamilyPrograms.unbounded P)
    RamCertificateMetadata.unbounded RamRaySelector.selectEntry RamRaySelector.selectBound
    (RamCertificateMetadata.unbounded_spec B m n P (by omega)) hbuild).mono (by omega)

end Lax109476Proofs.RamCertificateFamilies

end

theorem solution:∀ (B M m n:ℕ) (P:Lax109476.LinearProgram.Program ℤ m n),
  1≤ M→
    M < B→
      m * n + 2 * m + 2 * n + 8 < B→
        (m + (m + 1)) * (n + n) + (m + (m + 1)) + (n + n) + 4 < B→
          (∀ (i:Fin m) (j:Fin n), (P.A i j).natAbs≤ M)→
            (∀ (i:Fin m), (P.b i).natAbs≤ M)→
              (∀ (j:Fin n), (P.c j).natAbs≤ M)→
                Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamCertificateFamilies.Input P (m + (m + 1)) (n + n))
                  Lax109476Proofs.RamCertificateFamilies.unbounded
                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamCertificateSource.Data P τ∧
                      Lax109476Proofs.RamEquationData.Data (Lax109476Proofs.CertificateFamilyPrograms.unbounded P) τ)
                  (134 * ((m + (m + 1)) * (n + n)) + 90 * (m + (m + 1)) + 74):= @Lax109476Proofs.RamCertificateFamilies.unbounded_spec
