-- Prove2me | solution 1 for Lax263307Proofs.NativeOracleRounds.search_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:47:04.324193+00:00
-- url     : https://prove2.me/submissions/15ccb5e5-6092-4302-a2a4-b01dfbeed5d6

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces
import Theorems.Thm_Lax263307Proofs_NativeOracleExecution_oracle_segment

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

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

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

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem variable_frame (coefficients:List ℕ) (x:String) (hx:x ≠ "poly.value"):
    x∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars,hx]
  | cons a rest ih => simp [command,Com.wvars,ih,hx]

theorem arrays_frame (coefficients:List ℕ):(command coefficients).warrs=[]:=by
  induction coefficients with
  | nil => simp [command,Com.warrs]
  | cons a rest ih => simp [command,Com.warrs,ih]

end Lax455465Proofs.RamPolynomial

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

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

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

namespace Lax263307Proofs.NativeOracleFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs

theorem instruction_array (i:Lax808846.Ram.Instr) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.instruction i).warrs:=by
  cases i <;> simp_all [RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.warrs]

theorem dispatch_array (p:Lax808846.Ram.Program) (offset:ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.dispatch p offset).warrs:=by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or] using
      And.intro (instruction_array i a ha) (ih (offset+1))

theorem command_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉ (NativeOracleCalls.command p coeff).warrs:=by
  have hm:a∉ ["vm.addresses","vm.values","vm.output"]:=by simp_all
  have hd:=dispatch_array p 0 a hm
  simp_all [NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamPolynomial.arrays_frame,RamLpInputFrame.command,RamLpInputFrame.step,
    RamWordBuffer.append,RamVirtualProgram.execute,RamWordOps.modulus,
    RamVirtualProgram.initCommand,Com.warrs]

end Lax263307Proofs.NativeOracleFrame

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeOracleScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax455465Proofs

def reserved:List String:= ["frame.i","lookup.address","lookup.i","lookup.result","lp.position","lp.word","poly.argument","poly.value","put.address","put.value","size.count","size.i","size.total","size.value","vm.addresses","vm.count","vm.cursor","vm.input","vm.inputLength","vm.left","vm.modulus","vm.output","vm.outputLength","vm.pc","vm.result","vm.right","vm.running","vm.target","vm.values","vm.width"]

theorem instruction_variable (i:Lax808846.Ram.Instr) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.instruction i).wvars:=by
  cases i <;> simp_all [reserved,RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars]

theorem dispatch_variable (p:Lax808846.Ram.Program) (offset:ℕ) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.dispatch p offset).wvars:=by
  induction p generalizing offset with
  | nil => simp_all [reserved,RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or] using
      And.intro (instruction_variable i x hx) (ih (offset+1))

theorem command_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (x:String) (hx:x∉reserved):
    x∉(NativeOracleCalls.command p coeff).wvars:=by
  have hd:=dispatch_variable p 0 x hx
  have hp:=RamPolynomial.variable_frame coeff x (by simp_all [reserved])
  simp_all [reserved,NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,
    RamVirtualProgram.execute,RamWordOps.modulus,RamVirtualProgram.initCommand,Com.wvars]

end Lax263307Proofs.NativeOracleScalars

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

namespace Lax263307Proofs.NativeRawFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem command_variable (p:Lax808846.Ram.Program) (s:String)
    (hpre:s∉NativeRawOracle.prepare.wvars) (hvm:s∉NativeOracleScalars.reserved):
    s∉(NativeRawOracle.command p).wvars:=by
  have hv:=NativeOracleScalars.command_variable p [] s hvm
  simp only [NativeOracleCalls.command,Com.wvars,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.wvars,List.mem_append,not_or] using And.intro hpre hv.2

theorem array (p:Lax808846.Ram.Program) (a:String)
    (hpre:a∉NativeRawOracle.prepare.warrs)
    (hvm:a∉["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉(NativeRawOracle.command p).warrs:=by
  have hv:=NativeOracleFrame.command_array p [] a hvm
  simp only [NativeOracleCalls.command,Com.warrs,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.warrs,List.mem_append,not_or] using And.intro hpre hv.2

end Lax263307Proofs.NativeRawFrame

end

section

namespace Lax263307Proofs.NativeRoundedControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch Matrix

theorem update_variable (p:Lax808846.Ram.Program) (s:String)
    (hq:s∉NativeRoundedQuery.command.wvars) (hpre:s∉NativeRawOracle.prepare.wvars)
    (hvm:s∉NativeOracleScalars.reserved) (hs:s∉NativeRoundedState.command.wvars):
    s∉(NativeRoundedUpdate.command p).wvars:=by
  simpa only [NativeRoundedUpdate.command,Com.wvars,List.mem_append,not_or] using
    And.intro hq (And.intro (NativeRawFrame.command_variable p s hpre hvm) hs)

end Lax263307Proofs.NativeRoundedControl

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

namespace Lax263307Proofs.NativeRoundTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def Outcome {n m:ℕ} (Q:ℕ→ State n→ Env→ Prop) (limit k:ℕ) (state:State n)
    (reply:Reply n (Finset (Fin m))) (σ:Env):Prop:=
  match reply with
  | .found I => Stopped (some I) σ
  | .reject => Stopped (none:Option (Finset (Fin m))) σ
  | .cut a => Q (k+1) (update k state a) σ∧
      if k+1< limit then σ.vars "machine.running"=1∧ σ.vars "machine.phase"=4
      else Stopped (none:Option (Finset (Fin m))) σ

def Steps {n m:ℕ} (B:ℕ) (cfg:Config) (Base:Env→ Prop)
    (Q:ℕ→ State n→ Env→ Prop) (oracle:ℕ→ (Fin n→ ℚ)→ Reply n (Finset (Fin m)))
    (limit S K:ℕ):Prop:=
  ∀ k,k< limit→ ∀ state σ,Q k state σ→ σ.vars "machine.running"=1→ σ.vars "machine.phase"=4→
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ∧ steps≤ S∧ total≤ K∧ Base τ∧
      Outcome Q limit k state (oracle k state.2) τ

theorem scan_segment {n m:ℕ} (B:ℕ) (cfg:Config) (Base:Env→ Prop)
    (Q:ℕ→ State n→ Env→ Prop) (oracle:ℕ→ (Fin n→ ℚ)→ Reply n (Finset (Fin m)))
    (limit S K:ℕ) (hsteps:Steps B cfg Base Q oracle limit S K):
    ∀ remaining,0< remaining→ ∀ k,k+remaining=limit→ ∀ state σ,Q k state σ→
      σ.vars "machine.running"=1→ σ.vars "machine.phase"=4→
      ∃ τ steps total,Segment B (phases cfg) steps total σ τ∧ steps≤ S*remaining∧ total≤ K*remaining∧
        Base τ∧ Stopped (scan oracle k remaining state) τ:=by
  intro remaining
  induction remaining with
  | zero => intro h; omega
  | succ count ih =>
    intro hcount k hlimit state σ hQ hr hp
    obtain ⟨ν,s,t,first,hs,ht,hbase,hout⟩:=hsteps k (by omega) state σ hQ hr hp
    cases ho:oracle k state.2 with
    | found I =>
      refine ⟨ν,s,t,first,by nlinarith only [hs],by nlinarith only [ht],hbase,?_⟩
      simpa only [scan,ho,Outcome] using hout
    | reject =>
      refine ⟨ν,s,t,first,by nlinarith only [hs],by nlinarith only [ht],hbase,?_⟩
      simpa only [scan,ho,Outcome] using hout
    | cut a =>
      have hc:Q (k+1) (update k state a) ν∧
          if k+1< limit then ν.vars "machine.running"=1∧ ν.vars "machine.phase"=4
          else Stopped (none:Option (Finset (Fin m))) ν:=by
        simpa only [ho,Outcome] using hout
      cases count with
      | zero =>
        refine ⟨ν,s,t,first,by simpa using hs,by simpa using ht,hbase,?_⟩
        have he:¬k+1< limit:=by omega
        simpa only [scan,ho,he,if_false] using hc.2
      | succ rest =>
        have he:k+1< limit:=by omega
        have hnext:ν.vars "machine.running"=1∧ ν.vars "machine.phase"=4:=by
          simpa only [he,if_true] using hc.2
        obtain ⟨τ,s',t',second,hs',ht',hbase',hanswer⟩:=ih (by omega) (k+1) (by omega)
          (update k state a) ν hc.1 hnext.1 hnext.2
        refine ⟨τ,s+s',t+t',NativeMachineSegment.append first second,
          by nlinarith only [hs,hs'],by nlinarith only [ht,ht'],hbase',?_⟩
        simpa only [scan,ho] using hanswer

theorem search_segment {n m:ℕ} (B:ℕ) (cfg:Config) (Base:Env→ Prop)
    (Q:ℕ→ State n→ Env→ Prop) (oracle:ℕ→ (Fin n→ ℚ)→ Reply n (Finset (Fin m)))
    (precision S K:ℕ) (hsteps:Steps B cfg Base Q oracle (steps n precision) S K):
    ∀ σ,Q 0 (1,0) σ→ σ.vars "machine.running"=1→ σ.vars "machine.phase"=4→
      ∃ τ transitions total,Segment B (phases cfg) transitions total σ τ∧
        transitions≤ S*steps n precision∧ total≤ K*steps n precision∧
        Base τ∧ Stopped (search oracle precision) τ:=by
  intro σ hQ hr hp
  exact scan_segment B cfg Base Q oracle (steps n precision) S K hsteps _
    (by unfold steps; positivity) 0 (by omega) (1,0) σ hQ hr hp

end Lax263307Proofs.NativeRoundTrace

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

theorem RootData.refl (σ:Env):RootData σ σ:= ⟨rfl,rfl⟩

theorem RootData.trans {σ ν τ:Env} (h1:RootData σ ν) (h2:RootData ν τ):RootData σ τ:=
  ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem root_frame {B t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (ht:"root.target"∉c.wvars) (hf:"root.fuel"∉c.wvars):RootData σ τ:=
  ⟨rr.frame_var _ ht,rr.frame_var _ hf⟩

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

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem update_variable (cfg:Config) (s:String)
    (hv:s≠"vm.width") (hq:s∉NativeRoundedQuery.command.wvars)
    (hp:s∉NativeRawOracle.prepare.wvars) (ho:s∉NativeOracleScalars.reserved)
    (hs:s∉NativeRoundedState.command.wvars) (hf:s∉(NativeRoundedControl.finish 4 14).wvars):
    s∉(NativeRoundedControl.command cfg.rounded 4 14).wvars:=by
  have hu:=NativeRoundedControl.update_variable cfg.rounded s hq hp ho hs
  simp_all only [NativeRoundedControl.command,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem update_array (cfg:Config) (s:String)
    (hq:s∉NativeRoundedQuery.command.warrs) (hp:s∉NativeRawOracle.prepare.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (hs:s∉NativeRoundedState.command.warrs):
    s∉(NativeRoundedControl.command cfg.rounded 4 14).warrs:=by
  have hu:=NativeRawFrame.array cfg.rounded s hp ho
  simp_all only [NativeRoundedControl.command,NativeRoundedUpdate.command,
    NativeRoundedControl.finish,NativeAttemptReply.noneCommand,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

theorem update_frame {n B D k r p b load F fuel S v limit t:ℕ} (cfg:Config)
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B (NativeRoundedControl.command cfg.rounded 4 14) σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [NativeOracleContext.scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [NativeOracleContext.arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact update_array cfg _ (by decide) (by decide) (by decide) (by decide)

theorem update_segment {n r:ℕ} (B D k p b load F fuel S v limit c h j:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent:String→ ℕ) (front:List ℕ)
    (program:Program cfg.rounded c) (state:State (MomentLP.dimension n r))
    (a:Fin (MomentLP.dimension n r)→ ℤ)
    (bounds:Bounds B c h v n j limit cfg.rounded extent state a)
    (σ:Env) (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hs:NativeRoundedTrace.StoredState j state σ)
    (hnormal:Prefix (NativeRoundedQuery.normal a) "round.normal" σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=13):
    ∃ τ,Segment B (phases cfg) 1 (NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) h j+16) σ τ∧
      Context B D k r p b load F fuel S v limit cfg G extent front τ∧
      NativeRoundTrace.Outcome NativeRoundedTrace.StoredState limit j state
        (.cut a:Reply (MomentLP.dimension n r) (Finset (Fin n))) τ∧ RootData σ τ:=by
  have call:=program (MomentLP.dimension n r) n j h limit 4 14 bounds.dimension bounds.height
    state a bounds.shapeHeight bounds.normalHeight bounds.centerHeight bounds.positive B v bounds.width
    bounds.host bounds.time bounds.allowance bounds.query bounds.scalars bounds.words
  obtain ⟨τ,rr,po⟩:=call σ ⟨⟨hs.2.2.1,hs.2.2.2,hs.1,hnormal,hs.2.1,
      by rw [hc.lengths]; exact bounds.wordRoom⟩,hc.roundWidth,hc.moments.1.1,hc.roundLimit,
    by rw [hc.lengths]; exact bounds.inputRoom,by rw [hc.lengths]; exact bounds.addresses,
    by rw [hc.lengths]; exact bounds.values,by rw [hc.lengths]; exact bounds.output,
    by rw [hc.lengths]; exact bounds.shapeRoom,by rw [hc.lengths]; exact bounds.centerRoom⟩
  have rrPhase:Run B ((phases cfg)[13]'(by change 13<16; decide)) σ τ _:=rr
  have runningτ:=(rr.frame_var _ (update_variable cfg _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))).trans hr
  refine ⟨τ,NativeMachineSegment.phase hr ⟨13,by change 13<16; decide⟩ hp rrPhase,
    update_frame cfg rr hc,?_,root_frame rr
      (update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))⟩
  refine ⟨⟨po.1,po.2.1,po.2.2.1,po.2.2.2.2.1⟩,?_⟩
  by_cases hj:j+1< limit
  · simp only [hj,if_true]
    exact ⟨runningτ,by simpa only [NativeRoundedControl.Output,hj,if_true] using po.2.2.2.2.2⟩
  · simp only [hj,if_false]
    have hout:NativeTargetDriver.Reply (none:Option (Finset (Fin n))) τ∧ τ.vars "machine.phase"=14:=by
      simpa only [NativeRoundedControl.Output,hj,if_false] using po.2.2.2.2.2
    exact ⟨runningτ,hout.2,hout.1⟩

def Invariant {N n:ℕ} (Base:Env→ Prop) (oracle:ℕ→ (Fin N→ ℚ)→ Reply N (Finset (Fin n)))
    (j:ℕ) (state:State N) (σ:Env):Prop:=
  Base σ∧ NativeRoundedTrace.StoredState j state σ∧ state=trajectory oracle j

def WithRoot (root:Env) (Base:Env→ Prop) (σ:Env):Prop:=Base σ∧ RootData root σ

theorem steps {n r:ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ)
    (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card)))
    (root:Env) (program:Program cfg.rounded c)
    (setup:∀ j,j< limit→ NativeOracleExecution.Setup
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (oracle (r:=r) lp flow G D k p b load F child) j))
    (rounded:∀ j,j< limit→ ∀ a,
      oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a→
      Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a)
    (hcost:(16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤ oracleCost)
    (hround:∀ j,j< limit→ NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤ roundCost):
    NativeRoundTrace.Steps (2^w) cfg
      (WithRoot root (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
      (Invariant (WithRoot root (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
        (oracle (r:=r) lp flow G D k p b load F child))
      (oracle (r:=r) lp flow G D k p b load F child) limit
      ((childSteps+5)*(n+1)+7) (oracleCost+roundCost):=by
  intro j hj state σ hQ hr hp
  rcases hQ with ⟨⟨hc,hroot⟩,hs,rfl⟩
  let data:=setup j hj
  obtain ⟨ν,s,t,first,hsteps,htime,hcν,hsν,replyν,rootν⟩:=NativeOracleExecution.oracle_segment
    D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
    cfg G lp flow extent front child j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j)
    data.bounds data.hcenter data.hquery data.call data.farBounds data.nearSetup σ hc hs hr hp
  have ht:t≤ oracleCost:=htime.trans hcost
  change NativeOracleExecution.Output (oracle (r:=r) lp flow G D k p b load F child j
    (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2) ν at replyν
  cases he:oracle (r:=r) lp flow G D k p b load F child j
      (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2 with
  | reject =>
    refine ⟨ν,s,t,first,by omega,by omega,⟨hcν,hroot.trans rootν⟩,?_⟩
    simpa only [he,NativeOracleExecution.Output,NativeRoundTrace.Outcome] using replyν
  | found I =>
    refine ⟨ν,s,t,first,by omega,by omega,⟨hcν,hroot.trans rootν⟩,?_⟩
    simpa only [he,NativeOracleExecution.Output,NativeRoundTrace.Outcome] using replyν
  | cut a =>
    have raw:ν.vars "machine.running"=1∧ ν.vars "machine.phase"=13∧
        Prefix (NativeRoundedQuery.normal a) "round.normal" ν:=by
      simpa only [he,NativeOracleExecution.Output] using replyν
    obtain ⟨τ,last,hcτ,out,rootτ⟩:=update_segment (2^w) D k p b load F fuel S v limit c roundH j cfg G
      extent front program (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a
      (rounded j hj a he) ν hcν hsν raw.2.2 raw.1 raw.2.1
    have htRound:=hround j hj
    refine ⟨τ,s+1,_,NativeMachineSegment.append first last,by omega,by omega,⟨hcτ,hroot.trans (rootν.trans rootτ)⟩,?_⟩
    have hout:NativeRoundedTrace.StoredState (j+1)
        (update j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a) τ∧
        if j+1< limit then τ.vars "machine.running"=1∧ τ.vars "machine.phase"=4
        else NativeRoundTrace.Stopped (none:Option (Finset (Fin n))) τ:=out
    have next:update j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a =
        trajectory (oracle (r:=r) lp flow G D k p b load F child) (j+1):=by
      simp only [trajectory,he,selectedNormal]
    simp only [he,NativeRoundTrace.Outcome]
    exact ⟨⟨⟨hcτ,hroot.trans (rootν.trans rootτ)⟩,hout.1,next⟩,hout.2⟩

theorem search_segment {n r:ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost precision:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ)
    (child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card)))
    (data:Setup (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child)
    (hlimit:limit=RoundedOracleSearch.steps (MomentLP.dimension n r) precision)
    (σ:Env) (hc:Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs:NativeRoundedTrace.StoredState 0 ((1,0):State (MomentLP.dimension n r)) σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=4):
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ∧
      transitions≤((childSteps+5)*(n+1)+7)*limit∧ total≤(oracleCost+roundCost)*limit∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ∧
      NativeRoundTrace.Stopped (search (oracle (r:=r) lp flow G D k p b load F child) precision) τ∧ RootData σ τ:=by
  have concrete:=steps D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
    childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child σ
    data.program data.setup data.rounded data.hcost data.hround
  have scan:=NativeRoundTrace.search_segment (2^w) cfg
    (WithRoot σ (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
    (Invariant (WithRoot σ (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
      (oracle (r:=r) lp flow G D k p b load F child))
    (oracle (r:=r) lp flow G D k p b load F child) precision
    ((childSteps+5)*(n+1)+7) (oracleCost+roundCost) (by simpa only [←hlimit] using concrete)
    σ ⟨⟨hc,RootData.refl σ⟩,hs,rfl⟩ hr hp
  obtain ⟨τ,s,t,trace,hs,ht,⟨contextτ,rootτ⟩,answerτ⟩:=scan
  exact ⟨τ,s,t,trace,by simpa only [←hlimit] using hs,by simpa only [←hlimit] using ht,contextτ,answerτ,rootτ⟩

end Lax263307Proofs.NativeOracleRounds

end

theorem solution:∀ {n r:Nat}
  (D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime c roundH
    oracleCost roundCost precision:Nat)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (lp flow:List Nat→ List Nat)
  (extent:String→ Nat) (front:List Nat)
  (child:(C:Finset (Fin n))→ Nat→ Option (Finset (Fin (@Finset.card (Fin n) C)))),
  @Lax263307Proofs.NativeOracleRounds.Setup n r D k p b load F fuel S v limit w M farM nearM costH T space oracleTime
      callCost flowTime childSteps childTime c roundH oracleCost roundCost cfg G inst lp flow extent front child→
    @Eq Nat limit (Lax263307.RoundedOracleSearch.steps (Lax263307.MomentLP.dimension n r) precision)→
      ∀ (σ:Lax808846Proofs.Imp.Env),
        @Lax263307Proofs.NativeOracleContext.Context n
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            D k r p b load F fuel S v limit cfg G inst extent front σ→
          @Lax263307Proofs.NativeRoundedTrace.StoredState (Lax263307.MomentLP.dimension n r)
              ((0:Nat))
              (@Prod.mk (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                (Fin (Lax263307.MomentLP.dimension n r)→ Rat)
                (@OfNat.ofNat
                  (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                  (nat_lit 1)
                  (@One.toOfNat1
                    (Matrix (Fin (Lax263307.MomentLP.dimension n r)) (Fin (Lax263307.MomentLP.dimension n r)) Rat)
                    (@Matrix.one (Fin (Lax263307.MomentLP.dimension n r)) Rat
                      (instDecidableEqFin (Lax263307.MomentLP.dimension n r))
                      (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                      (@AddMonoidWithOne.toOne Rat
                        (@AddGroupWithOne.toAddMonoidWithOne Rat
                          (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))
                (@OfNat.ofNat (Fin (Lax263307.MomentLP.dimension n r)→ Rat) (nat_lit 0)
                  (@Zero.toOfNat0 (Fin (Lax263307.MomentLP.dimension n r)→ Rat)
                    (@Pi.instZero (Fin (Lax263307.MomentLP.dimension n r))
                      (fun (a:Fin (Lax263307.MomentLP.dimension n r)) => Rat)
                      fun (i:Fin (Lax263307.MomentLP.dimension n r)) =>
                      @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
              σ→
            @Eq Nat (σ.vars "machine.running") ((1:Nat))→
              @Eq Nat (σ.vars "machine.phase") ((4:Nat))→
                ∃ (τ:Lax808846Proofs.Imp.Env) (transitions:Nat) (total:Nat),
                  And
                    (Lax263307Proofs.NativeMachineSegment.Segment
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      (Lax263307Proofs.NativeCoreMachine.phases cfg) transitions total σ τ)
                    (And
                      (Nat.le transitions
                        (Nat.mul
                          (Nat.add
                            (Nat.mul
                              (Nat.add childSteps
                                ((5:Nat)))
                              (Nat.add n
                                ((1:Nat))))
                            ((7:Nat)))
                          limit))
                      (And
                        (Nat.le total
                          (Nat.mul
                            (Nat.add oracleCost roundCost) limit))
                        (And
                          (@Lax263307Proofs.NativeOracleContext.Context n
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat)) w)
                            D k r p b load F fuel S v limit cfg G inst extent front τ)
                          (And
                            (@Lax263307Proofs.NativeRoundTrace.Stopped n
                              (@Lax263307.RoundedOracleSearch.search (Lax263307.MomentLP.dimension n r) (Finset (Fin n))
                                (@Lax263307Proofs.NativeOracleRounds.oracle n r lp flow G inst D k p b load F child)
                                precision)
                              τ)
                            (Lax263307Proofs.NativeOracleContext.RootData σ τ))))):= @Lax263307Proofs.NativeOracleRounds.search_segment
