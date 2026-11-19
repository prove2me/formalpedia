-- Prove2me | solution 1 for Lax263307Proofs.NativeQptasZero.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:15.682595+00:00
-- url     : https://prove2.me/submissions/37484f0f-e408-4028-95cb-6f45ae56ed31

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces

namespace Lax109476.RationalFeasibility
end Lax109476.RationalFeasibility
namespace Lax109476Proofs.BinaryOptimization
end Lax109476Proofs.BinaryOptimization
namespace Lax109476Proofs.BinaryOptimizationBounds
end Lax109476Proofs.BinaryOptimizationBounds
namespace Lax109476Proofs.CertificateSystems
end Lax109476Proofs.CertificateSystems
namespace Lax109476Proofs.CoordinateOptimization
end Lax109476Proofs.CoordinateOptimization
namespace Lax109476Proofs.DeterminantBounds
end Lax109476Proofs.DeterminantBounds
namespace Lax109476Proofs.EllipsoidDeterminant
end Lax109476Proofs.EllipsoidDeterminant
namespace Lax109476Proofs.EllipsoidTermination
end Lax109476Proofs.EllipsoidTermination
namespace Lax109476Proofs.IterationBudget
end Lax109476Proofs.IterationBudget
namespace Lax109476Proofs.LexicographicBounds
end Lax109476Proofs.LexicographicBounds
namespace Lax109476Proofs.PointRecovery
end Lax109476Proofs.PointRecovery
namespace Lax109476Proofs.RamEllipsoidStoredBounds
end Lax109476Proofs.RamEllipsoidStoredBounds
namespace Lax109476Proofs.RamEllipsoidWordBounds
end Lax109476Proofs.RamEllipsoidWordBounds
namespace Lax109476Proofs.RamFrame
end Lax109476Proofs.RamFrame
namespace Lax109476Proofs.RamPadEntries
end Lax109476Proofs.RamPadEntries
namespace Lax109476Proofs.RamPrimitiveBounds
end Lax109476Proofs.RamPrimitiveBounds
namespace Lax109476Proofs.RamRecoveryData
end Lax109476Proofs.RamRecoveryData
namespace Lax109476Proofs.RamScalarFrame
end Lax109476Proofs.RamScalarFrame
namespace Lax109476Proofs.RationalFeasibility
end Lax109476Proofs.RationalFeasibility
namespace Lax109476Proofs.RationalMinima
end Lax109476Proofs.RationalMinima
namespace Lax109476Proofs.SmallFeasiblePoint
end Lax109476Proofs.SmallFeasiblePoint
namespace Lax263307.ConditioningDistribution
end Lax263307.ConditioningDistribution
namespace Lax263307.PowerBagBounds
end Lax263307.PowerBagBounds
namespace Lax263307Proofs.ConditioningDistribution
end Lax263307Proofs.ConditioningDistribution
namespace Lax263307Proofs.EntropyDecrease
end Lax263307Proofs.EntropyDecrease
namespace Lax263307Proofs.NativeDistanceEntries
end Lax263307Proofs.NativeDistanceEntries
namespace Lax263307Proofs.NativeMachineSegment
end Lax263307Proofs.NativeMachineSegment
namespace Lax263307Proofs.NativeUniformWordGuards
end Lax263307Proofs.NativeUniformWordGuards
namespace Lax455465.ShortPathFlow
end Lax455465.ShortPathFlow
namespace Lax455465Proofs.AcyclicFlowPath
end Lax455465Proofs.AcyclicFlowPath
namespace Lax455465Proofs.LargePotentialData
end Lax455465Proofs.LargePotentialData
namespace Lax455465Proofs.PathSubtraction
end Lax455465Proofs.PathSubtraction
namespace Lax455465Proofs.RamFlowData
end Lax455465Proofs.RamFlowData
namespace Lax455465Proofs.RationalParser
end Lax455465Proofs.RationalParser
namespace Lax455465Proofs.RegionHistory
end Lax455465Proofs.RegionHistory
namespace Lax455465Proofs.RegionInterval
end Lax455465Proofs.RegionInterval
namespace Lax455465Proofs.RegionRuntimeState
end Lax455465Proofs.RegionRuntimeState
namespace Lax455465Proofs.RoundingConstants
end Lax455465Proofs.RoundingConstants
namespace Lax759944.TuringPolytime
end Lax759944.TuringPolytime
namespace Lax759944Proofs.Legacy.RamPolytime
end Lax759944Proofs.Legacy.RamPolytime
namespace Lax808846.RamComputes
end Lax808846.RamComputes
namespace Lax808846Proofs.Machine
end Lax808846Proofs.Machine

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

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

def Com.decReads:(c:Com)→ Decidable c.reads
  | .skip => decidable_of_iff False (by rw [Com.reads])
  | .assign _ _ => decidable_of_iff False (by rw [Com.reads])
  | .store _ _ _ => decidable_of_iff False (by rw [Com.reads])
  | .seq c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .ite _ c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .while _ c =>
      have:=c.decReads
      decidable_of_iff c.reads (by rw [Com.reads])
  | .read _ => decidable_of_iff True (by rw [Com.reads])
  | .write _ => decidable_of_iff False (by rw [Com.reads])

instance:DecidablePred Com.reads:=Com.decReads

def Com.decNoWrite:(c:Com)→ Decidable c.NoWrite
  | .skip => decidable_of_iff True (by rw [Com.NoWrite])
  | .assign _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .store _ _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .seq c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .ite _ c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .while _ c =>
      have:=c.decNoWrite
      decidable_of_iff c.NoWrite (by rw [Com.NoWrite])
  | .read _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .write _ => decidable_of_iff False (by rw [Com.NoWrite])

instance:DecidablePred Com.NoWrite:=Com.decNoWrite

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

namespace Lax455465Proofs.RamInputCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def Invariant (xs:List ℕ) (σ:Env):Prop:=
  σ.vars "input.length"=xs.length∧ σ.vars "input.i" ≤ xs.length∧
  σ.inp=xs.drop (σ.vars "input.i")∧ xs.length≤ (σ.arrs "input.data").length∧
  ∀ j,j < σ.vars "input.i" → (σ.arrs "input.data")[j]?=xs[j]?

theorem drop_head (xs:List ℕ) (i:ℕ) (hi:i < xs.length):
    xs.drop i=xs[i]::xs.drop (i + 1):=by
  exact List.cons_getElem_drop_succ.symm

private theorem prefix_advance (xs buffer:List ℕ) (i:ℕ) (hi:i < xs.length)
    (hbuffer:xs.length≤ buffer.length) (h:∀ j,j < i→ buffer[j]?=xs[j]?):
    ∀ j,j < i + 1→ (buffer.set i xs[i])[j]?=xs[j]?:=by
  intro j hj
  by_cases he:i=j
  · subst j
    rw [List.getElem?_set_self (by omega),List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne he]
    exact h j (by omega)

theorem copyStep_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Invariant xs σ∧ σ.vars "input.i" < xs.length) copyStep
      (fun σ τ => Invariant xs τ∧ τ.vars "input.i"=σ.vars "input.i" + 1) 8:=by
  rintro σ ⟨⟨hcount,hindex,hinp,hlength,harrays⟩,hi⟩
  have hhead:=drop_head xs (σ.vars "input.i") hi
  have hv:=hwords xs[σ.vars "input.i"] (List.getElem_mem hi)
  rw [hhead] at hinp
  have hnext:=prefix_advance xs (σ.arrs "input.data") (σ.vars "input.i") hi hlength harrays
  clear hhead harrays
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (Invariant xs τ) (@Eq Nat (Env.vars τ "input.i") (c0 (Env.vars σ_1 "input.i") ((1:Nat))))) σ; let c2:String→ Nat:=Env.vars (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)); let c3:Nat:=c2 "input.i"; let c4:Nat:=c2 "input.word"; let c5:Env:=Env.setArr (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.data" c3 c4; let c6:Nat:=Env.vars c5 "input.i"; let c7:Nat:=c0 c6 ((1:Nat)); let c8:Env:=Env.setVar c5 "input.i" c7; let c9:Nat→ Nat:=c0 ((1:Nat)); let c10:Nat:=c0 (c9 (Expr.size (Expr.var "input.i"))) (Expr.size (Expr.var "input.word")); let c11:Expr:=Expr.add (Expr.var "input.i") (Expr.lit ((1:Nat))); let c12:Nat:=c9 (Expr.size c11); let c13:Nat:=c0 c10 c12; let c14:Com:=Com.assign "input.i" c11; let c15:Prop:= @Ne (List Nat) (Env.inp σ) (@List.nil Nat); let c16:List Nat→ Prop:= @Ne (List Nat) (@List.drop Nat (Env.vars σ "input.i") xs); let c17:Prop:= @Eq (List Nat) (Env.inp σ) (@List.drop Nat (Env.vars σ "input.i") xs); let c18:Nat:=c0 (Env.vars σ "input.i") ((1:Nat)); let c19:List Nat:= @List.cons Nat (@getElem (List Nat) Nat Nat (fun (as:List Nat) (i:Nat) => Nat.lt i (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) xs (Env.vars σ "input.i") hi) (@List.drop Nat c18 xs); let c20:Prop:= @Eq (List Nat) (@List.drop Nat (Env.vars σ "input.i") xs) (@List.nil Nat); let c21:Prop:= @LT.lt Nat (@Preorder.toLT Nat (@PartialOrder.toPreorder Nat (@LinearOrder.toPartialOrder Nat Nat.instLinearOrder))) (Env.vars σ "input.i") (@List.length Nat xs); let c22:Prop:=Nat.le (@List.length Nat xs) (Env.vars σ "input.i"); @Exists.intro Env (fun (σ':Env) => And (Run B copyStep σ σ' ((8:Nat))) (c1 σ')) c8 (@And.intro (Run B copyStep σ c8 ((8:Nat))) (c1 c8) (RunStep.mono B copyStep σ c8 (c9 c13) ((8:Nat)) (RunStep.seq B (Com.read "input.word") (Com.seq (Com.store "input.data" (Expr.var "input.i") (Expr.var "input.word")) c14) σ (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) c8 ((1:Nat)) c13 (RunStep.read B σ "input.word" (@of_eq_true c15 (@Eq.trans Prop c15 (c16 (@List.nil Nat)) True (@congrFun' (List Nat) Prop (@Ne (List Nat) (Env.inp σ)) c16 (@congrArg (List Nat) (List Nat→ Prop) (Env.inp σ) (@List.drop Nat (Env.vars σ "input.i") xs) (@Ne (List Nat)) (@id c17 (@Eq.mp (@Eq (List Nat) (Env.inp σ) c19) c17 (@congrArg (List Nat) Prop c19 (@List.drop Nat (Env.vars σ "input.i") xs) (@Eq (List Nat) (Env.inp σ)) (@List.getElem_cons_drop Nat xs (Env.vars σ "input.i") hi)) hinp))) (@List.nil Nat)) (@Eq.trans Prop (Not c20) c21 True (@Eq.trans Prop (Not c20) (Not c22) c21 (@congrArg Prop Prop c20 c22 Not (@List.drop_eq_nil_iff._simp_1 Nat xs (Env.vars σ "input.i"))) (@not_le._simp_1 Nat Nat.instLinearOrder (@List.length Nat xs) (Env.vars σ "input.i"))) (@eq_true (Nat.lt (Env.vars σ "input.i") (@List.length Nat xs)) hi))))) (RunStep.seq B (Com.store "input.data" (Expr.var "input.i") (Expr.var "input.word")) c14 (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) c5 c8 c10 c12 (RunStep.store B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.data" (Expr.var "input.i") (Expr.var "input.word") c3 c4 (RunStep.eval_var B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.i" (?nAX_g6127_0_0_0)) (RunStep.eval_var B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.word" ?_) (?nAX_g6127_0_0_1)) (RunStep.assign B c5 "input.i" c11 c7 (RunStep.eval_add B c5 (Expr.var "input.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "input.i" (?nAX_g6127_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c5 h1) (?nAX_g6127_0_0_3))))) (?nAX_g6127_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6127_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Invariant]

end Lax455465Proofs.RamInputCopy

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

namespace Lax455465Proofs.RamEmitWords
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Data (array:String) (stride:ℕ) (xs:List ℕ) (σ:Env):Prop:=
  ∀ i,∀ hi:i < xs.length,(σ.arrs array)[stride*i]?=some xs[i]

def Invariant (array:String) (stride:ℕ) (xs front:List ℕ) (σ:Env):Prop:=
  Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.vars "emit.i"≤ xs.length∧
    σ.out=front++xs.take (σ.vars "emit.i")

theorem command_spec (B:ℕ) (array:String) (stride:ℕ) (xs front:List ℕ)
    (h1:1 < B) (hstride:stride < B) (hoffset:stride*xs.length < B) (hlen:xs.length < B) (hwords:∀ x∈xs,x < B):
    Spec B (fun σ => Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.out=front)
      (command array stride) (fun _ τ => τ.out=front++xs) (13*xs.length+6):=by
  have hstep:Spec B (fun σ => Invariant array stride xs front σ∧ σ.vars "emit.i" < xs.length)
      (step array stride) (fun σ τ => Invariant array stride xs front τ∧ τ.vars "emit.i"=σ.vars "emit.i"+1) 9:=by
    rintro σ ⟨⟨hp,hcount,hle,hout⟩,hlt⟩
    let i:=σ.vars "emit.i"
    have hi:i < xs.length:=hlt
    have hval:xs[i] < B:=hwords _ (List.getElem_mem hi)
    have he:(Expr.get array (.mul (.lit stride) (.var "emit.i"))).evalB B σ=some xs[i]:=
      evalB_get (evalB_bin (op:=.mul) (evalB_lit hstride) (evalB_var (hi.trans hlen))
        ((Nat.mul_le_mul_left stride hi.le).trans_lt hoffset)) (hp i hi) hval
    let ν:Env:= {σ with out:=σ.out++[xs[i]]}
    have r1:Run B (.write (.get array (.mul (.lit stride) (.var "emit.i")))) σ ν 5:=Run.write he
    have r2:Run B (.assign "emit.i" (.add (.var "emit.i") (.lit 1))) ν (ν.setVar "emit.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (evalB_var (hi.trans hlen)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨_,r1.seq r2,⟨hp,by simpa [ν] using hcount,by simp; omega,?_⟩,by simp [i,ν]⟩
    change σ.out++[xs[i]]=front++xs.take (i+1)
    rw [List.take_succ_eq_append_getElem hi,←List.append_assoc]
    exact congrArg (fun a => a++[xs[i]]) hout
  have hloop:=Spec.forRangeZero "emit.i" "emit.count" (Invariant array stride xs front) xs.length 9 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hstep
  rintro σ ⟨hp,hcount,hout⟩
  obtain ⟨τ,rr,pr⟩:=hloop σ ⟨hp,by simpa using hcount,by simp,by simpa using hout⟩
  exact ⟨τ,by simpa [command] using rr,by simpa only [pr.2,List.take_length] using pr.1.2.2.2⟩

end Lax455465Proofs.RamEmitWords

end

section

namespace Lax263307Proofs.NativeFrontend

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.WeightedIndependentSet

def tailInput {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ):List ℕ:=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε

theorem tail_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ):(tailInput G w ε).length=n*n + 3*n + 3:=by
  simp [tailInput,encodeParameters,encodeRational,List.length_flatten,List.length_flatMap,
    List.sum_ofFn,Finset.sum_const,Nat.mul_comm,Nat.add_assoc]

theorem metadata_spec (B n:ℕ) (hsize:n*n+3*n+3 < B):
    Spec B (fun σ => σ.vars "input.n"=n) metadata
      (fun _ τ => τ.vars "input.n"=n∧ τ.vars "input.matrixLength"=n*n∧
        τ.vars "input.weightLength"=3*n∧ τ.vars "input.length"=n*n+3*n+3) 20:=by
  have hn:n < B:=by nlinarith only [hsize]
  have hnn:n*n < B:=by omega
  have h3n:3*n < B:=by omega
  have hadd:n*n+3*n < B:=by omega
  have h3:3 < B:=by omega
  rintro σ hσ
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 n n; let c2:Nat→ Nat:=c0 ((3:Nat)); let c3:Nat:=c2 n; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 (c4 c1 c3) ((3:Nat)); let c6:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "input.n") n) (And (@Eq Nat (Env.vars τ "input.matrixLength") c1) (And (@Eq Nat (Env.vars τ "input.weightLength") c3) (@Eq Nat (Env.vars τ "input.length") c5)))) σ; let c7:Nat:=c0 (Env.vars σ "input.n") (Env.vars σ "input.n"); let c8:Env:=Env.setVar σ "input.matrixLength" c7; let c9:Nat:=Env.vars c8 "input.n"; let c10:Nat:=c2 c9; let c11:Env:=Env.setVar c8 "input.weightLength" c10; let c12:String→ Nat:=Env.vars c11; let c13:Nat:=c12 "input.matrixLength"; let c14:Nat:=c12 "input.weightLength"; let c15:Nat:=c4 c13 c14; let c16:Nat:=c4 c15 ((3:Nat)); let c17:Env:=Env.setVar c11 "input.length" c16; let c18:Nat→ Nat:=c4 ((1:Nat)); let c19:Nat:=c18 (Expr.size (Expr.mul (Expr.var "input.n") (Expr.var "input.n"))); let c20:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "input.n"); let c21:Nat:=c18 (Expr.size c20); let c22:Expr:=Expr.add (Expr.add (Expr.var "input.matrixLength") (Expr.var "input.weightLength")) (Expr.lit ((3:Nat))); let c23:Nat:=c18 (Expr.size c22); let c24:Nat:=c4 c21 c23; let c25:Com:=Com.assign "input.weightLength" c20; let c26:Com:=Com.assign "input.length" c22; let c27:String→ Nat:=Env.vars c17; @Exists.intro Env (fun (σ':Env) => And (Run B metadata σ σ' ((20:Nat))) (c6 σ')) c17 (@And.intro (Run B metadata σ c17 ((20:Nat))) (c6 c17) (RunStep.mono B metadata σ c17 (c4 c19 c24) ((20:Nat)) (RunStep.seq B (Com.assign "input.matrixLength" (Expr.mul (Expr.var "input.n") (Expr.var "input.n"))) (Com.seq c25 c26) σ c8 c17 c19 c24 (RunStep.assign B σ "input.matrixLength" (Expr.mul (Expr.var "input.n") (Expr.var "input.n")) c7 (RunStep.eval_mul B σ (Expr.var "input.n") (Expr.var "input.n") (Env.vars σ "input.n") (Env.vars σ "input.n") (RunStep.eval_var B σ "input.n" (?nAX_g7806_0_0_0)) (RunStep.eval_var B σ "input.n" (?nAX_g7806_0_0_1)) ?_)) (RunStep.seq B c25 c26 c8 c11 c17 c21 c23 (RunStep.assign B c8 "input.weightLength" c20 c10 (RunStep.eval_mul B c8 (Expr.lit ((3:Nat))) (Expr.var "input.n") ((3:Nat)) c9 (RunStep.eval_lit B ((3:Nat)) c8 h3) (RunStep.eval_var B c8 "input.n" (?nAX_g7806_0_0_2)) (?nAX_g7806_0_0_3))) (RunStep.assign B c11 "input.length" c22 c16 (RunStep.eval_add B c11 (Expr.add (Expr.var "input.matrixLength") (Expr.var "input.weightLength")) (Expr.lit ((3:Nat))) c15 ((3:Nat)) (RunStep.eval_add B c11 (Expr.var "input.matrixLength") (Expr.var "input.weightLength") c13 c14 (RunStep.eval_var B c11 "input.matrixLength" ?_) (RunStep.eval_var B c11 "input.weightLength" (?nAX_g7806_0_0_4)) ?_) (RunStep.eval_lit B ((3:Nat)) c11 h3) ?_)))) (?nAX_g7806_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7806_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7806_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7806_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7806_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7806_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7806_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]

theorem read_input_spec (B n:ℕ) (xs:List ℕ) (hsize:n*n+3*n+3 < B)
    (hlen:xs.length=n*n+3*n+3) (hwords:∀ x∈xs,x< B):
    Spec B (fun σ => σ.inp=n::xs∧ xs.length≤(σ.arrs "input.data").length) readInput
      (fun _ τ => τ.vars "input.n"=n∧ τ.vars "input.matrixLength"=n*n∧
        τ.vars "input.weightLength"=3*n∧ τ.vars "input.length"=xs.length∧
        τ.inp=[]∧ Prefix xs "input.data" τ) (12*xs.length+30):=by
  have hn:n< B:=by nlinarith only [hsize]
  have h1:1< B:=by omega
  have hx:xs.length< B:=by omega
  have hloop:=Spec.forRangeZero "input.i" "input.length" (RamInputCopy.Invariant xs) xs.length 8 hx
    (fun _ h => h.2.1) (fun _ h => h.1) (RamInputCopy.copyStep_spec B xs h1 hx hwords)
  rintro σ ⟨hinp,hroom⟩
  let ν:= {σ.setVar "input.n" n with inp:=xs}
  have rr:Run B (.read "input.n") σ ν 1:=Run.read hinp
  obtain ⟨μ,rm,hm⟩:=metadata_spec B n hsize ν (by simp [ν])
  have hinpμ:μ.inp=xs:=(rm.frame_inp (by decide)).trans (by simp [ν])
  have hroomμ:xs.length≤(μ.arrs "input.data").length:=by
    rw [rm.frame_arr "input.data" (by decide)]
    exact hroom
  have hi:RamInputCopy.Invariant xs (μ.setVar "input.i" 0):=by
    refine ⟨?_,by simp,?_,hroomμ,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false,hlen] using hm.2.2.2
    · simpa only [inp_setVar,vars_setVar,if_true,List.drop_zero] using hinpμ
    · intro j hj
      simp only [vars_setVar,if_true] at hj
      omega
  obtain ⟨τ,rl,hl⟩:=hloop μ hi
  refine ⟨τ,(rr.seq (rm.seq rl)).mono (by omega),?_,?_,?_,hl.1.1,?_,?_⟩
  · exact (rl.frame_var "input.n" (by decide)).trans hm.1
  · exact (rl.frame_var "input.matrixLength" (by decide)).trans hm.2.1
  · exact (rl.frame_var "input.weightLength" (by decide)).trans hm.2.2.1
  · simpa only [hl.2,List.drop_length] using hl.1.2.2.1
  · intro j hj
    have hh:=hl.1.2.2.2.2 j (by simpa only [hl.2] using hj)
    simpa only [List.getElem?_eq_getElem hj] using hh

def copyCount (n wn wd en ed Wn Wd:ℕ):ℕ:=
  (2*n*wn*ed*Wd) / (wd*en*Wn)

theorem compute_copies_spec (B n wn wd en ed Wn Wd:ℕ)
    (h2:2< B) (hn:n< B) (hwn:wn< B) (hwd:wd< B) (hen:en< B) (hed:ed< B)
    (hWn:Wn< B) (hWd:Wd< B)
    (h0:2*n< B) (h1:2*n*wn< B) (h2':2*n*wn*ed< B) (h3:2*n*wn*ed*Wd< B)
    (h4:wd*en< B) (h5:wd*en*Wn< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ σ.vars "weight.n"=wn∧ σ.vars "weight.d"=wd∧
      σ.vars "accuracy.n"=en∧ σ.vars "accuracy.d"=ed∧ σ.vars "maximum.n"=Wn∧ σ.vars "maximum.d"=Wd)
      computeCopies (fun _ τ => τ.vars "copy.count"=copyCount n wn wd en ed Wn Wd) 16:=by
  have hq:copyCount n wn wd en ed Wn Wd< B:=(Nat.div_le_self _ _).trans_lt h3
  rintro σ ⟨hσn,hσwn,hσwd,hσen,hσed,hσWn,hσWd⟩
  (expose_names;
    (refine let c0:Nat:=copyCount n wn wd en ed Wn Wd; let c1:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "copy.count") c0) σ; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c2 ((2:Nat)) (Env.vars σ "input.n"); let c4:Nat:=c2 c3 (Env.vars σ "weight.n"); let c5:Nat:=c2 c4 (Env.vars σ "accuracy.d"); let c6:Nat:=c2 c5 (Env.vars σ "maximum.d"); let c7:Nat:=c2 (Env.vars σ "weight.d") (Env.vars σ "accuracy.n"); let c8:Nat:=c2 c7 (Env.vars σ "maximum.n"); let c9:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c6 c8; let c10:Env:=Env.setVar σ "copy.count" c9; let c11:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "input.n"); let c12:Expr:=Expr.mul c11 (Expr.var "weight.n"); let c13:Expr:=Expr.mul c12 (Expr.var "accuracy.d"); let c14:Expr:=Expr.mul c13 (Expr.var "maximum.d"); let c15:Expr:=Expr.mul (Expr.mul (Expr.var "weight.d") (Expr.var "accuracy.n")) (Expr.var "maximum.n"); let c16:Expr:=Expr.div c14 c15; @Exists.intro Env (fun (σ':Env) => And (Run B computeCopies σ σ' ((16:Nat))) (c1 σ')) c10 (@And.intro (Run B computeCopies σ c10 ((16:Nat))) (c1 c10) (RunStep.mono B computeCopies σ c10 (Nat.add ((1:Nat)) (Expr.size c16)) ((16:Nat)) (RunStep.assign B σ "copy.count" c16 c9 (RunStep.eval_div B σ c14 c15 c6 c8 (RunStep.eval_mul B σ c13 (Expr.var "maximum.d") c5 (Env.vars σ "maximum.d") (RunStep.eval_mul B σ c12 (Expr.var "accuracy.d") c4 (Env.vars σ "accuracy.d") (RunStep.eval_mul B σ c11 (Expr.var "weight.n") c3 (Env.vars σ "weight.n") (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "input.n") ((2:Nat)) (Env.vars σ "input.n") (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_var B σ "input.n" (?nAX_g7810_0_0_0)) (?nAX_g7810_0_0_1)) (RunStep.eval_var B σ "weight.n" (?nAX_g7810_0_0_2)) ?_) (RunStep.eval_var B σ "accuracy.d" (?nAX_g7810_0_0_3)) ?_) (RunStep.eval_var B σ "maximum.d" (?nAX_g7810_0_0_4)) ?_) (RunStep.eval_mul B σ (Expr.mul (Expr.var "weight.d") (Expr.var "accuracy.n")) (Expr.var "maximum.n") c7 (Env.vars σ "maximum.n") (RunStep.eval_mul B σ (Expr.var "weight.d") (Expr.var "accuracy.n") (Env.vars σ "weight.d") (Env.vars σ "accuracy.n") (RunStep.eval_var B σ "weight.d" (?nAX_g7810_0_0_5)) (RunStep.eval_var B σ "accuracy.n" (?nAX_g7810_0_0_6)) ?_) (RunStep.eval_var B σ "maximum.n" (?nAX_g7810_0_0_7)) ?_) ?_)) (?nAX_g7810_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7810_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7810_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [copyCount,Env.setVar]

def maximumPair (an ad bn bd:ℕ):ℕ × ℕ:=if an*bd < bn*ad then (bn,bd) else (an,ad)

theorem maximum_pair_value (an ad bn bd:ℕ) (had:0< ad) (hbd:0< bd):
    ((maximumPair an ad bn bd).1:ℚ) / (maximumPair an ad bn bd).2 =
      max ((an:ℚ)/ad) ((bn:ℚ)/bd):=by
  have hd:(0:ℚ)< ad:=Nat.cast_pos.mpr had
  have he:(0:ℚ)< bd:=Nat.cast_pos.mpr hbd
  have heq:an*bd < bn*ad↔ (an:ℚ)/ad < (bn:ℚ)/bd:=by
    rw [div_lt_div_iff₀ hd he]
    norm_cast
  unfold maximumPair
  split_ifs with h
  · exact (max_eq_right (heq.mp h).le).symm
  · exact (max_eq_left (le_of_not_gt (mt heq.mpr h))).symm

theorem update_maximum_spec (B an ad bn bd:ℕ) (han:an< B) (had:ad< B) (hbn:bn< B)
    (hbd:bd< B) (hleft:an*bd< B) (hright:bn*ad< B):
    Spec B (fun σ => σ.vars "maximum.n"=an∧ σ.vars "maximum.d"=ad∧
      σ.vars "weight.n"=bn∧ σ.vars "weight.d"=bd) updateMaximum
      (fun _ τ => τ.vars "maximum.n"=(maximumPair an ad bn bd).1∧
        τ.vars "maximum.d"=(maximumPair an ad bn bd).2) 12:=by
  rintro σ ⟨hσan,hσad,hσbn,hσbd⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "maximum.n") (Env.vars σ "weight.d"); let c2:Nat→ Prop:=Nat.lt c1; let c3:Nat:=c0 (Env.vars σ "weight.n") (Env.vars σ "maximum.d"); let c4:Prop:=c2 c3; let c5:Prop:=Not c4; let c6:Nat:= @Prod.fst Nat Nat (maximumPair an ad bn bd); let c7:Nat:= @Prod.snd Nat Nat (maximumPair an ad bn bd); let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "maximum.n") c6) (@Eq Nat (Env.vars τ "maximum.d") c7)) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B updateMaximum σ σ' ((12:Nat))) (c8 σ'); let c10:Nat:=Env.vars (Env.setVar σ "maximum.n" (Env.vars σ "weight.n")) "weight.d"; let c11:Env:=Env.setVar (Env.setVar σ "maximum.n" (Env.vars σ "weight.n")) "maximum.d" c10; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Cond:=Cond.lt (Expr.mul (Expr.var "maximum.n") (Expr.var "weight.d")) (Expr.mul (Expr.var "weight.n") (Expr.var "maximum.d")); let c15:Nat→ Nat:=c12 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.var "weight.n")); let c17:Nat:=c13 (Expr.size (Expr.var "weight.d")); let c18:Nat:=c12 c16 c17; let c19:Com:=Com.seq (Com.assign "maximum.n" (Expr.var "weight.n")) (Com.assign "maximum.d" (Expr.var "weight.d")); let c20:String→ Nat:=Env.vars c11; @Or.casesOn c4 c5 (fun (x:Or c4 c5) => @Exists Env c9) (Classical.em c4) (fun (hcase:c4) => @Exists.intro Env c9 c11 (@And.intro (Run B updateMaximum σ c11 ((12:Nat))) (c8 c11) (RunStep.mono B updateMaximum σ c11 (c15 c18) ((12:Nat)) (RunStep.ite_true B c14 c19 Com.skip σ c11 c18 (RunStep.cond_lt_true B σ (Expr.mul (Expr.var "maximum.n") (Expr.var "weight.d")) (Expr.mul (Expr.var "weight.n") (Expr.var "maximum.d")) c1 c3 (RunStep.eval_mul B σ (Expr.var "maximum.n") (Expr.var "weight.d") (Env.vars σ "maximum.n") (Env.vars σ "weight.d") (RunStep.eval_var B σ "maximum.n" (?nAX_g7814_0_0_0)) (RunStep.eval_var B σ "weight.d" (?nAX_g7814_0_0_1)) ?_) (RunStep.eval_mul B σ (Expr.var "weight.n") (Expr.var "maximum.d") (Env.vars σ "weight.n") (Env.vars σ "maximum.d") (RunStep.eval_var B σ "weight.n" (?nAX_g7814_0_0_2)) (RunStep.eval_var B σ "maximum.d" (?nAX_g7814_0_0_3)) ?_) hcase) (RunStep.seq B (Com.assign "maximum.n" (Expr.var "weight.n")) (Com.assign "maximum.d" (Expr.var "weight.d")) σ (Env.setVar σ "maximum.n" (Env.vars σ "weight.n")) c11 c16 c17 (RunStep.assign B σ "maximum.n" (Expr.var "weight.n") (Env.vars σ "weight.n") (RunStep.eval_var B σ "weight.n" (?nAX_g7814_0_0_4))) (RunStep.assign B (Env.setVar σ "maximum.n" (Env.vars σ "weight.n")) "maximum.d" (Expr.var "weight.d") c10 (RunStep.eval_var B (Env.setVar σ "maximum.n" (Env.vars σ "weight.n")) "weight.d" (?nAX_g7814_0_0_5))))) (?nAX_g7814_0_0_6)) ?_)) fun (hcase:c5) => @Exists.intro Env c9 σ (@And.intro (Run B updateMaximum σ σ ((12:Nat))) (c8 σ) (RunStep.mono B updateMaximum σ σ (c15 ((1:Nat))) ((12:Nat)) (RunStep.ite_false B c14 c19 Com.skip σ σ ((1:Nat)) (RunStep.cond_lt_false B σ (Expr.mul (Expr.var "maximum.n") (Expr.var "weight.d")) (Expr.mul (Expr.var "weight.n") (Expr.var "maximum.d")) c1 c3 (RunStep.eval_mul B σ (Expr.var "maximum.n") (Expr.var "weight.d") (Env.vars σ "maximum.n") (Env.vars σ "weight.d") (RunStep.eval_var B σ "maximum.n" (?nAX_g7814_0_0_7)) (RunStep.eval_var B σ "weight.d" (?nAX_g7814_0_0_8)) ?_) (RunStep.eval_mul B σ (Expr.var "weight.n") (Expr.var "maximum.d") (Env.vars σ "weight.n") (Env.vars σ "maximum.d") (RunStep.eval_var B σ "weight.n" (?nAX_g7814_0_0_9)) (RunStep.eval_var B σ "maximum.d" (?nAX_g7814_0_0_10)) ?_) hcase) (RunStep.skip B σ)) (?nAX_g7814_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7814_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7814_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [maximumPair,Env.setVar] <;> split_ifs <;> simp_all <;> omega

def clippedNumerator (q:ℚ):ℕ:=if q.num < 0 then 0 else q.num.natAbs

theorem clipped_value (q:ℚ):(clippedNumerator q:ℚ) / q.den=max q 0:=by
  unfold clippedNumerator
  split_ifs with h
  · have hq:q < 0:=Rat.num_neg.mp h
    simp [max_eq_right hq.le]
  · have hn:0≤ q.num:=le_of_not_gt h
    have hq:0≤ q:=Rat.num_nonneg.mp hn
    rw [max_eq_left hq]
    have hcast:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
      have he:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg hn
      simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) he
    rw [hcast,q.num_div_den]

theorem read_weight_spec (B pos:ℕ) (q:ℚ) (hp:pos+2< B) (h2:2< B)
    (hn:q.num.natAbs< B) (hd:q.den< B):
    Spec B (fun σ => σ.vars "weight.position"=pos∧
      (σ.arrs "input.data")[pos]?=some (if q.num<0 then 1 else 0)∧
      (σ.arrs "input.data")[pos+1]?=some q.num.natAbs∧
      (σ.arrs "input.data")[pos+2]?=some q.den) readWeight
      (fun _ τ => τ.vars "weight.n"=clippedNumerator q∧ τ.vars "weight.d"=q.den) 24:=by
  have hsign:(if q.num<0 then 1 else 0)< B:=by split_ifs <;> omega
  rintro σ ⟨hpos,hs,hn',hd'⟩
  have hroom:pos+2 < (σ.arrs "input.data").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hd'
    contradiction
  (expose_names;
    (refine let c0:Nat:= @List.getD Nat (Env.arrs σ "input.data") (Env.vars σ "weight.position") ((0:Nat)); let c1:Env:=Env.setVar σ "weight.s" c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=Env.vars c1 "weight.position"; let c4:Nat:=c2 c3 ((1:Nat)); let c5:Nat:= @List.getD Nat (Env.arrs c1 "input.data") c4 ((0:Nat)); let c6:Env:=Env.setVar c1 "weight.n" c5; let c7:Nat:=Env.vars c6 "weight.position"; let c8:Nat:=c2 c7 ((2:Nat)); let c9:Nat:= @List.getD Nat (Env.arrs c6 "input.data") c8 ((0:Nat)); let c10:Env:=Env.setVar c6 "weight.d" c9; let c11:String→ Nat:=Env.vars c10; let c12:Nat:=c11 "weight.s"; let c13:Prop:= @Eq Nat c12 ((1:Nat)); let c14:Prop:=Not c13; let c15:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "weight.n") (clippedNumerator q)) (@Eq Nat (Env.vars τ "weight.d") (Rat.den q))) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B readWeight σ σ' ((24:Nat))) (c15 σ'); let c17:Env:=Env.setVar c10 "weight.n" ((0:Nat)); let c18:Nat→ Nat:=c2 ((1:Nat)); let c19:Nat:=c18 (Expr.size (Expr.get "input.data" (Expr.var "weight.position"))); let c20:Nat→ Nat:=c2 c19; let c21:Expr:=Expr.add (Expr.var "weight.position") (Expr.lit ((1:Nat))); let c22:Expr:=Expr.get "input.data" c21; let c23:Nat:=c18 (Expr.size c22); let c24:Nat→ Nat:=c2 c23; let c25:Expr:=Expr.add (Expr.var "weight.position") (Expr.lit ((2:Nat))); let c26:Expr:=Expr.get "input.data" c25; let c27:Nat:=c18 (Expr.size c26); let c28:Nat→ Nat:=c2 c27; let c29:Cond:=Cond.eq (Expr.var "weight.s") (Expr.lit ((1:Nat))); let c30:Nat→ Nat:=c2 (c18 (Cond.size c29)); let c31:Nat:=c18 (Expr.size (Expr.lit ((0:Nat)))); let c32:Nat:=c30 c31; let c33:Nat:=c28 c32; let c34:Nat:=c24 c33; let c35:Com:=Com.assign "weight.n" c22; let c36:Com:=Com.assign "weight.d" c26; let c37:Com:=Com.assign "weight.n" (Expr.lit ((0:Nat))); let c38:Com:=Com.ite c29 c37 Com.skip; let c39:Com:=Com.seq c36 c38; let c40:String→ Nat:=Env.vars c17; let c41:Nat:=c30 ((1:Nat)); let c42:Nat:=c28 c41; let c43:Nat:=c24 c42; @Or.casesOn c13 c14 (fun (x:Or c13 c14) => @Exists Env c16) (Classical.em c13) (fun (hcase:c13) => @Exists.intro Env c16 c17 (@And.intro (Run B readWeight σ c17 ((24:Nat))) (c15 c17) (RunStep.mono B readWeight σ c17 (c20 c34) ((24:Nat)) (RunStep.seq B (Com.assign "weight.s" (Expr.get "input.data" (Expr.var "weight.position"))) (Com.seq c35 c39) σ c1 c17 c19 c34 (RunStep.assign B σ "weight.s" (Expr.get "input.data" (Expr.var "weight.position")) c0 (RunStep.eval_get B σ "input.data" (Expr.var "weight.position") (Env.vars σ "weight.position") (RunStep.eval_var B σ "weight.position" (?nAX_g7818_0_0_0)) (?nAX_g7818_0_0_1) ?_)) (RunStep.seq B c35 c39 c1 c6 c17 c23 c33 (RunStep.assign B c1 "weight.n" c22 c5 (RunStep.eval_get B c1 "input.data" c21 c4 (RunStep.eval_add B c1 (Expr.var "weight.position") (Expr.lit ((1:Nat))) c3 ((1:Nat)) (RunStep.eval_var B c1 "weight.position" (?nAX_g7818_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c1 (?nAX_g7818_0_0_3)) (?nAX_g7818_0_0_4)) (?nAX_g7818_0_0_5) ?_)) (RunStep.seq B c36 c38 c6 c10 c17 c27 c32 (RunStep.assign B c6 "weight.d" c26 c9 (RunStep.eval_get B c6 "input.data" c25 c8 (RunStep.eval_add B c6 (Expr.var "weight.position") (Expr.lit ((2:Nat))) c7 ((2:Nat)) (RunStep.eval_var B c6 "weight.position" (?nAX_g7818_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c6 h2) (?nAX_g7818_0_0_7)) (?nAX_g7818_0_0_8) ?_)) (RunStep.ite_true B c29 c37 Com.skip c10 c17 c31 (RunStep.cond_eq_true B c10 (Expr.var "weight.s") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c10 "weight.s" ?_) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g7818_0_0_9)) hcase) (RunStep.assign B c10 "weight.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c10 (?nAX_g7818_0_0_10))))))) (?nAX_g7818_0_0_11)) ?_)) fun (hcase:c14) => @Exists.intro Env c16 c10 (@And.intro (Run B readWeight σ c10 ((24:Nat))) (c15 c10) (RunStep.mono B readWeight σ c10 (c20 c43) ((24:Nat)) (RunStep.seq B (Com.assign "weight.s" (Expr.get "input.data" (Expr.var "weight.position"))) (Com.seq c35 c39) σ c1 c10 c19 c43 (RunStep.assign B σ "weight.s" (Expr.get "input.data" (Expr.var "weight.position")) c0 (RunStep.eval_get B σ "input.data" (Expr.var "weight.position") (Env.vars σ "weight.position") (RunStep.eval_var B σ "weight.position" (?nAX_g7818_0_0_12)) (?nAX_g7818_0_0_13) ?_)) (RunStep.seq B c35 c39 c1 c6 c10 c23 c42 (RunStep.assign B c1 "weight.n" c22 c5 (RunStep.eval_get B c1 "input.data" c21 c4 (RunStep.eval_add B c1 (Expr.var "weight.position") (Expr.lit ((1:Nat))) c3 ((1:Nat)) (RunStep.eval_var B c1 "weight.position" (?nAX_g7818_0_0_14)) (RunStep.eval_lit B ((1:Nat)) c1 (?nAX_g7818_0_0_15)) (?nAX_g7818_0_0_16)) (?nAX_g7818_0_0_17) ?_)) (RunStep.seq B c36 c38 c6 c10 c10 c27 c41 (RunStep.assign B c6 "weight.d" c26 c9 (RunStep.eval_get B c6 "input.data" c25 c8 (RunStep.eval_add B c6 (Expr.var "weight.position") (Expr.lit ((2:Nat))) c7 ((2:Nat)) (RunStep.eval_var B c6 "weight.position" (?nAX_g7818_0_0_18)) (RunStep.eval_lit B ((2:Nat)) c6 h2) (?nAX_g7818_0_0_19)) (?nAX_g7818_0_0_20) ?_)) (RunStep.ite_false B c29 c37 Com.skip c10 c10 ((1:Nat)) (RunStep.cond_eq_false B c10 (Expr.var "weight.s") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c10 "weight.s" ?_) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g7818_0_0_21)) hcase) (RunStep.skip B c10))))) (?nAX_g7818_0_0_22)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7818_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7818_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [clippedNumerator,Env.setVar]

theorem encoded_coordinate (qs:List ℚ) (i j:ℕ) (hi:i< qs.length) (hj:j<3):
    (qs.flatMap encodeRational)[3*i+j]?=(encodeRational qs[i])[j]?:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa [encodeRational] using hj)]
    | succ i =>
      have hi':i< qs.length:=by simpa using hi
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp [encodeRational]; omega)]
      have hidx:3*(i+1)+j-(encodeRational q).length=3*i+j:=by simp [encodeRational]; omega
      rw [hidx]
      exact ih i hi'

theorem encoded_length (qs:List ℚ):(qs.flatMap encodeRational).length=3*qs.length:=by
  induction qs with
  | nil => simp
  | cons q qs ih => simp [encodeRational,ih,Nat.mul_add,Nat.add_comm]; omega

theorem prefixed_coordinate (front tail:List ℕ) (qs:List ℚ) (i j:ℕ)
    (hi:i< qs.length) (hj:j<3):
    (front++qs.flatMap encodeRational++tail)[front.length+3*i+j]?=(encodeRational qs[i])[j]?:=by
  rw [List.append_assoc,List.getElem?_append_right (by omega)]
  have hidx:front.length+3*i+j-front.length=3*i+j:=by omega
  rw [hidx,List.getElem?_append_left (by rw [encoded_length]; omega)]
  exact encoded_coordinate qs i j hi hj

theorem read_weight_from_prefix_spec (B:ℕ) (front tail:List ℕ) (qs:List ℚ)
    (i:ℕ) (hi:i< qs.length) (hsize:front.length+3*qs.length+1< B)
    (h2:2< B) (hn:qs[i].num.natAbs< B) (hd:qs[i].den< B):
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
      σ.vars "weight.position"=front.length+3*i) readWeight
      (fun _ τ => τ.vars "weight.n"=clippedNumerator qs[i]∧ τ.vars "weight.d"=qs[i].den) 24:=by
  rintro σ ⟨hp,hpos⟩
  apply read_weight_spec B (front.length+3*i) qs[i] (by omega) h2 hn hd σ
  refine ⟨hpos,?_,?_,?_⟩
  all_goals
    have hget (j:ℕ) (hj:j<3):
        (σ.arrs "input.data")[front.length+3*i+j]?=(encodeRational qs[i])[j]?:=by
      have hidx:front.length+3*i+j < (front++qs.flatMap encodeRational++tail).length:=by
        rw [List.length_append,List.length_append,encoded_length]
        omega
      have hh:=hp (front.length+3*i+j) hidx
      rw [← List.getElem?_eq_getElem hidx] at hh
      exact hh.trans (prefixed_coordinate front tail qs i j hi hj)
  · simpa only [Nat.add_zero,encodeRational,List.getElem?_cons_zero] using hget 0 (by omega)
  · simpa only [encodeRational,List.getElem?_cons_succ,List.getElem?_cons_zero] using hget 1 (by omega)
  · simpa only [encodeRational,List.getElem?_cons_succ,List.getElem?_cons_zero] using hget 2 (by omega)

theorem maximum_step_spec (B an ad:ℕ) (front tail:List ℕ) (qs:List ℚ)
    (i:ℕ) (hi:i< qs.length) (hsize:front.length+3*qs.length+3< B)
    (han:an< B) (had:ad< B) (hn:qs[i].num.natAbs< B) (hd:qs[i].den< B)
    (hleft:an*qs[i].den< B) (hright:clippedNumerator qs[i]*ad< B):
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
      σ.vars "input.matrixLength"=front.length∧ σ.vars "weight.i"=i∧
      σ.vars "maximum.n"=an∧ σ.vars "maximum.d"=ad) maximumStep
      (fun _ τ => τ.vars "weight.i"=i+1∧
        τ.vars "maximum.n"=(maximumPair an ad (clippedNumerator qs[i]) qs[i].den).1∧
        τ.vars "maximum.d"=(maximumPair an ad (clippedNumerator qs[i]) qs[i].den).2) 48:=by
  have hiB:i< B:=by omega
  have hfront:front.length< B:=by omega
  have h3:3< B:=by omega
  have h3i:3*i< B:=by omega
  have hpos:front.length+3*i< B:=by omega
  have hclip:clippedNumerator qs[i]< B:=by unfold clippedNumerator; split_ifs <;> omega
  have hread:=read_weight_from_prefix_spec B front tail qs i hi (by omega) (by omega) hn hd
  have hmax:=update_maximum_spec B an ad (clippedNumerator qs[i]) qs[i].den han had hclip hd hleft hright
  rintro σ ⟨hp,hbase,hiσ,hanσ,hadσ⟩
  have hpstep:Spec B (fun σ => σ.vars "input.matrixLength"=front.length∧ σ.vars "weight.i"=i)
      (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
      (fun _ τ => τ.vars "weight.position"=front.length+3*i) 6:=by
    (expose_names;
      (refine fun (σ_1:Env) (a:And (@Eq Nat (Env.vars σ_1 "input.matrixLength") (@List.length Nat front)) (@Eq Nat (Env.vars σ_1 "weight.i") i)) => let c0:Prop:= @Eq Nat (Env.vars σ_1 "input.matrixLength") (@List.length Nat front); let c1:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "weight.i"); let c2:Expr:=Expr.add (Expr.var "input.matrixLength") c1; let c3:Com:=Com.assign "weight.position" c2; let c4:Env→ Nat→ Prop:=Run B c3 σ_1; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=Nat.mul ((3:Nat)); let c7:Nat:=c5 (@List.length Nat front) (c6 i); let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "weight.position") c7) σ_1; let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((6:Nat))) (c8 σ'); let c10:Nat:=c6 (Env.vars σ_1 "weight.i"); let c11:Nat:=c5 (Env.vars σ_1 "input.matrixLength") c10; let c12:Env:=Env.setVar σ_1 "weight.position" c11; @And.casesOn c0 (@Eq Nat (Env.vars σ_1 "weight.i") i) (fun (x:And c0 (@Eq Nat (Env.vars σ_1 "weight.i") i)) => @Exists Env c9) a fun (left:c0) (right:@Eq Nat (Env.vars σ_1 "weight.i") i) => @Exists.intro Env c9 c12 (@And.intro (c4 c12 ((6:Nat))) (c8 c12) (RunStep.mono B c3 σ_1 c12 (c5 ((1:Nat)) (Expr.size c2)) ((6:Nat)) (RunStep.assign B σ_1 "weight.position" c2 c11 (RunStep.eval_add B σ_1 (Expr.var "input.matrixLength") c1 (Env.vars σ_1 "input.matrixLength") c10 (RunStep.eval_var B σ_1 "input.matrixLength" (?nAX_g7824_0_0_0)) (RunStep.eval_mul B σ_1 (Expr.lit ((3:Nat))) (Expr.var "weight.i") ((3:Nat)) (Env.vars σ_1 "weight.i") (RunStep.eval_lit B ((3:Nat)) σ_1 h3) (RunStep.eval_var B σ_1 "weight.i" (?nAX_g7824_0_0_1)) (?nAX_g7824_0_0_2)) (?nAX_g7824_0_0_3))) (?nAX_g7824_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7824_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7824_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7824_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7824_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7824_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩:=hpstep σ ⟨hbase,hiσ⟩
  obtain ⟨μ,r2,p2⟩:=hread ν ⟨by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hp,p1⟩
  have ra:=r1.seq r2
  have ha:μ.vars "maximum.n"=an:=(ra.frame_var "maximum.n" (by decide)).trans hanσ
  have hd':μ.vars "maximum.d"=ad:=(ra.frame_var "maximum.d" (by decide)).trans hadσ
  obtain ⟨ξ,r3,p3⟩:=hmax μ ⟨ha,hd',p2.1,p2.2⟩
  have hb:=ra.seq r3
  have hiξ:ξ.vars "weight.i"=i:=(hb.frame_var "weight.i" (by decide)).trans hiσ
  let τ:=ξ.setVar "weight.i" (i+1)
  have r4:Run B (.assign "weight.i" (.add (.var "weight.i") (.lit 1))) ξ τ 4:=by
    apply Run.assign
    apply evalB_bin (op:=.add)
    · rw [evalB_var_iff]; exact ⟨hiξ.symm,hiξ ▸ hiB⟩
    · exact evalB_lit (by omega)
    · dsimp [Bop.apply]; omega
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simp [τ],?_,?_⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using p3.1
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using p3.2

end Lax263307Proofs.NativeFrontend

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeMaximum

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet

def advance (a:ℕ×ℕ) (q:ℚ):ℕ×ℕ:=maximumPair a.1 a.2 (clippedNumerator q) q.den

def maximum (qs:List ℚ):ℕ×ℕ:=qs.foldl advance (0,1)

theorem fold_bounds (M:ℕ) (a:ℕ×ℕ) (qs:List ℚ) (ha:a.1≤ M∧ a.2≤ M∧ 0< a.2)
    (hq:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    (qs.foldl advance a).1≤ M∧ (qs.foldl advance a).2≤ M∧ 0<(qs.foldl advance a).2:=by
  induction qs generalizing a with
  | nil => exact ha
  | cons q qs ih =>
    apply ih
    · have hqn:=(hq q (by simp)).1
      have hqd:=(hq q (by simp)).2
      dsimp [advance,maximumPair]
      split_ifs
      · exact ⟨by unfold clippedNumerator; split_ifs <;> omega,hqd,q.den_pos⟩
      · exact ha
    · intro q hq'
      exact hq q (by simp [hq'])

theorem maximum_bounds (M:ℕ) (hM:1≤ M) (qs:List ℚ)
    (hq:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    (maximum qs).1≤ M∧ (maximum qs).2≤ M∧ 0<(maximum qs).2:=
  fold_bounds M (0,1) qs ⟨by omega,hM,by omega⟩ hq

theorem take_succ (qs:List ℚ) (i:ℕ) (hi:i< qs.length):
    maximum (qs.take (i+1))=advance (maximum (qs.take i)) qs[i]:=by
  dsimp only [maximum]
  rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
  rfl

def Invariant (front tail:List ℕ) (qs:List ℚ) (σ:Env):Prop:=
  Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
  σ.vars "input.matrixLength"=front.length∧ σ.vars "input.n"=qs.length∧
  σ.vars "weight.i"≤ qs.length∧
  σ.vars "maximum.n"=(maximum (qs.take (σ.vars "weight.i"))).1∧
  σ.vars "maximum.d"=(maximum (qs.take (σ.vars "weight.i"))).2

theorem step_spec (B M:ℕ) (front tail:List ℕ) (qs:List ℚ) (hM:1≤ M)
    (hB:2*M^2+3< B) (hlen:front.length+3*qs.length+3< B)
    (hwords:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    Spec B (fun σ => Invariant front tail qs σ∧ σ.vars "weight.i"< qs.length)
      maximumStep (fun σ τ => Invariant front tail qs τ∧ τ.vars "weight.i"=σ.vars "weight.i"+1) 48:=by
  have hMB:M< B:=by nlinarith only [hB]
  have hMM:M*M< B:=by nlinarith only [hB]
  rintro σ ⟨⟨hp,hbase,hn,hi,hmaxn,hmaxd⟩,hlt⟩
  let i:=σ.vars "weight.i"
  let a:=maximum (qs.take i)
  have ha:=maximum_bounds M hM (qs.take i) (fun q hq => hwords q (List.mem_of_mem_take hq))
  have hq:=hwords qs[i] (List.getElem_mem hlt)
  have hc:clippedNumerator qs[i]≤ M:=by unfold clippedNumerator; split_ifs <;> omega
  have hl:a.1*qs[i].den< B:=(Nat.mul_le_mul ha.1 hq.2).trans_lt hMM
  have hr:clippedNumerator qs[i]*a.2< B:=(Nat.mul_le_mul hc ha.2.1).trans_lt hMM
  obtain ⟨τ,rr,hti,htn,htd⟩:=maximum_step_spec B a.1 a.2 front tail qs i hlt hlen
    (ha.1.trans_lt hMB) (ha.2.1.trans_lt hMB) (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) hl hr
    σ ⟨hp,hbase,rfl,hmaxn,hmaxd⟩
  refine ⟨τ,rr,?_,hti⟩
  refine ⟨?_,?_,?_,by omega,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using hp
  · exact (rr.frame_var "input.matrixLength" (by decide)).trans hbase
  · exact (rr.frame_var "input.n" (by decide)).trans hn
  · rw [hti,take_succ qs i hlt]
    exact htn
  · rw [hti,take_succ qs i hlt]
    exact htd

theorem command_spec (B M:ℕ) (front tail:List ℕ) (qs:List ℚ) (hM:1≤ M)
    (hB:2*M^2+3< B) (hlen:front.length+3*qs.length+3< B)
    (hwords:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
      σ.vars "input.matrixLength"=front.length∧ σ.vars "input.n"=qs.length)
      command (fun _ τ => τ.vars "maximum.n"=(maximum qs).1∧ τ.vars "maximum.d"=(maximum qs).2)
      (52*qs.length+10):=by
  have hlen':qs.length< B:=by omega
  have h1:1< B:=by omega
  have hl:=Spec.forRangeZero "weight.i" "input.n" (Invariant front tail qs) qs.length 48 hlen'
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (step_spec B M front tail qs hM hB hlen hwords)
  rintro σ ⟨hp,hbase,hn⟩
  let ν:=σ.setVar "maximum.n" 0
  let μ:=ν.setVar "maximum.d" 1
  have r1:Run B (.assign "maximum.n" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have r2:Run B (.assign "maximum.d" (.lit 1)) ν μ 2:=Run.assign (evalB_lit h1)
  have hi:Invariant front tail qs (μ.setVar "weight.i" 0):=by
    refine ⟨hp,?_,?_,?_,?_,?_⟩
    · simpa only [μ,ν,vars_setVar,String.reduceEq,if_false] using hbase
    · simpa only [μ,ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp only [vars_setVar,if_true]; omega
    · simp only [μ,ν,vars_setVar,String.reduceEq,if_false,if_true,List.take_zero,maximum,List.foldl_nil]
    · simp only [μ,ν,vars_setVar,String.reduceEq,if_false,if_true,List.take_zero,maximum,List.foldl_nil]
  obtain ⟨τ,rl,hpost⟩:=hl μ hi
  refine ⟨τ,(r1.seq (r2.seq rl)).mono (by omega),?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.2

def value (a:ℕ×ℕ):ℚ:=(a.1:ℚ)/a.2

theorem advance_positive (a:ℕ×ℕ) (q:ℚ) (ha:0< a.2):0<(advance a q).2:=by
  unfold advance maximumPair
  split_ifs
  · exact q.den_pos
  · exact ha

theorem advance_value (a:ℕ×ℕ) (q:ℚ) (ha:0< a.2):
    value (advance a q)=max (value a) (max q 0):=by
  dsimp only [advance,value]
  rw [maximum_pair_value _ _ _ _ ha q.den_pos,clipped_value]

theorem fold_le_iff (a:ℕ×ℕ) (ha:0< a.2) (qs:List ℚ) (W:ℚ):
    value (qs.foldl advance a)≤ W↔ value a≤ W∧ ∀ q∈qs,max q 0≤ W:=by
  induction qs generalizing a with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons,ih _ (advance_positive a q ha),advance_value a q ha]
    simp only [max_le_iff,List.mem_cons,forall_eq_or_imp]
    tauto

theorem maximum_value {n:ℕ} (w:Fin n→ ℚ):
    value (maximum (List.ofFn w)) =
      Lax263307.WeightRounding.maximumWeight (fun v => max (w v) 0):=by
  let W:=Lax263307.WeightRounding.maximumWeight (fun v => max (w v) 0)
  have hzero:(0:ℚ)≤ W:=Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hweight (v:Fin n):max (w v) 0≤ W:=by
    apply Finset.le_max'
    simp
  have hupper:value (maximum (List.ofFn w))≤ W:=by
    apply (fold_le_iff (0,1) (by omega) (List.ofFn w) W).mpr
    refine ⟨by simpa [value] using hzero,?_⟩
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hweight v
  refine le_antisymm hupper ?_
  have hbound:=(fold_le_iff (0,1) (by omega) (List.ofFn w) (value (maximum (List.ofFn w)))).mp le_rfl
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · simpa [value] using hbound.1
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hq
    exact hbound.2 (w v) (List.mem_ofFn.mpr ⟨v,rfl⟩)

end Lax263307Proofs.NativeMaximum

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeMultiplicities

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet

theorem quotient_copies (n wn wd en ed Wn Wd:ℕ) (hwd:0< wd) (hed:0< ed) (hWd:0< Wd):
    copyCount n wn wd en ed Wn Wd =
      ⌊((wn:ℚ)/wd) / (((en:ℚ)/ed)*((Wn:ℚ)/Wd)/(2*n))⌋₊:=by
  rw [copyCount, ← Rat.natFloor_natCast_div_natCast]
  congr 1
  push_cast
  have hd:(wd:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hwd)
  have he:(ed:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hed)
  have hD:(Wd:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hWd)
  field_simp

def counts (n en ed Wn Wd:ℕ) (qs:List ℚ):List ℕ:=
  qs.map fun q => copyCount n (clippedNumerator q) q.den en ed Wn Wd

def Invariant (front tail:List ℕ) (qs:List ℚ) (en ed Wn Wd:ℕ) (σ:Env):Prop:=
  Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
  σ.vars "input.matrixLength"=front.length∧ σ.vars "input.n"=qs.length∧
  σ.vars "accuracy.n"=en∧ σ.vars "accuracy.d"=ed∧
  σ.vars "maximum.n"=Wn∧ σ.vars "maximum.d"=Wd∧
  σ.vars "weight.i"≤ qs.length∧ qs.length≤(σ.arrs "copy.counts").length∧
  Prefix ((counts qs.length en ed Wn Wd qs).take (σ.vars "weight.i")) "copy.counts" σ

theorem product_bounds (B M n wn wd en ed Wn Wd:ℕ) (hM:1≤ M)
    (hB:2*M^4+3< B) (hn:n≤ M) (hwn:wn≤ M) (hwd:wd≤ M) (hen:en≤ M)
    (hed:ed≤ M) (hWn:Wn≤ M) (hWd:Wd≤ M):
    2< B∧ n< B∧ wn< B∧ wd< B∧ en< B∧ ed< B∧ Wn< B∧ Wd< B∧
    2*n< B∧ 2*n*wn< B∧ 2*n*wn*ed< B∧ 2*n*wn*ed*Wd< B∧ wd*en< B∧ wd*en*Wn< B:=by
  have hp1:M≤ M^4:=by simpa using Nat.pow_le_pow_right hM (by omega:1≤4)
  have hp2:M^2≤ M^4:=Nat.pow_le_pow_right hM (by omega)
  have hp3:M^3≤ M^4:=Nat.pow_le_pow_right hM (by omega)
  have hMB:M< B:=by omega
  have h2M:2*M^4< B:=by omega
  have p1:2*n*wn≤2*M^2:=by calc
    _≤ 2*M*M:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hwn
    _=_:=by ring
  have p2:2*n*wn*ed≤2*M^3:=by calc
    _≤ (2*M^2)*M:=Nat.mul_le_mul p1 hed
    _=_:=by ring
  have p3:2*n*wn*ed*Wd≤2*M^4:=by calc
    _≤ (2*M^3)*M:=Nat.mul_le_mul p2 hWd
    _=_:=by ring
  have p4:wd*en≤ M^2:=by simpa only [pow_two] using Nat.mul_le_mul hwd hen
  have p5:wd*en*Wn≤ M^3:=by calc
    _≤ M^2*M:=Nat.mul_le_mul p4 hWn
    _=_:=by ring
  exact ⟨by nlinarith only [hB,hM,hp1],hn.trans_lt hMB,hwn.trans_lt hMB,hwd.trans_lt hMB,
    hen.trans_lt hMB,hed.trans_lt hMB,hWn.trans_lt hMB,hWd.trans_lt hMB,
    by omega,by omega,by omega,p3.trans_lt h2M,by omega,by omega⟩

theorem step_spec (B M en ed Wn Wd:ℕ) (front tail:List ℕ) (qs:List ℚ)
    (hM:1≤ M) (hB:2*M^4+3< B) (hn:qs.length≤ M)
    (hen:en≤ M) (hed:ed≤ M) (hWn:Wn≤ M) (hWd:Wd≤ M)
    (hlen:front.length+3*qs.length+3< B)
    (hwords:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    Spec B (fun σ => Invariant front tail qs en ed Wn Wd σ∧ σ.vars "weight.i"< qs.length)
      step (fun σ τ => Invariant front tail qs en ed Wn Wd τ∧ τ.vars "weight.i"=σ.vars "weight.i"+1) 54:=by
  have hMB:M< B:=by
    have hp:M≤ M^4:=by simpa using Nat.pow_le_pow_right hM (by omega:1≤4)
    omega
  rintro σ ⟨⟨hp,hbase,hnσ,henσ,hedσ,hWnσ,hWdσ,hi,hroom,hprefix⟩,hlt⟩
  let i:=σ.vars "weight.i"
  have hq:=hwords qs[i] (List.getElem_mem hlt)
  have hc:clippedNumerator qs[i]≤ M:=by unfold clippedNumerator; split_ifs <;> omega
  have hb:=product_bounds B M qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
    hM hB hn hc hq.2 hen hed hWn hWd
  rcases hb with ⟨htwo,horder,hnum,hden,henB,hedB,hmaxn,hmaxd,hprod0,hprod1,hprod2,hprod3,hprod4,hprod5⟩
  have hpos:front.length+3*i< B:=by omega
  have hiB:i< B:=by omega
  have hfront:front.length< B:=by omega
  have h3:3< B:=by omega
  have h3i:3*i< B:=by omega
  have hpstep:Spec B (fun σ => σ.vars "input.matrixLength"=front.length∧ σ.vars "weight.i"=i)
      (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
      (fun _ τ => τ.vars "weight.position"=front.length+3*i) 6:=by
    (expose_names;
      (refine fun (σ_1:Env) (a:And (@Eq Nat (Env.vars σ_1 "input.matrixLength") (@List.length Nat front)) (@Eq Nat (Env.vars σ_1 "weight.i") i)) => let c0:Prop:= @Eq Nat (Env.vars σ_1 "input.matrixLength") (@List.length Nat front); let c1:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "weight.i"); let c2:Expr:=Expr.add (Expr.var "input.matrixLength") c1; let c3:Com:=Com.assign "weight.position" c2; let c4:Env→ Nat→ Prop:=Run B c3 σ_1; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=Nat.mul ((3:Nat)); let c7:Nat:=c5 (@List.length Nat front) (c6 i); let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "weight.position") c7) σ_1; let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((6:Nat))) (c8 σ'); let c10:Nat:=c6 (Env.vars σ_1 "weight.i"); let c11:Nat:=c5 (Env.vars σ_1 "input.matrixLength") c10; let c12:Env:=Env.setVar σ_1 "weight.position" c11; @And.casesOn c0 (@Eq Nat (Env.vars σ_1 "weight.i") i) (fun (x:And c0 (@Eq Nat (Env.vars σ_1 "weight.i") i)) => @Exists Env c9) a fun (left:c0) (right:@Eq Nat (Env.vars σ_1 "weight.i") i) => @Exists.intro Env c9 c12 (@And.intro (c4 c12 ((6:Nat))) (c8 c12) (RunStep.mono B c3 σ_1 c12 (c5 ((1:Nat)) (Expr.size c2)) ((6:Nat)) (RunStep.assign B σ_1 "weight.position" c2 c11 (RunStep.eval_add B σ_1 (Expr.var "input.matrixLength") c1 (Env.vars σ_1 "input.matrixLength") c10 (RunStep.eval_var B σ_1 "input.matrixLength" (?nAX_g7844_0_0_0)) (RunStep.eval_mul B σ_1 (Expr.lit ((3:Nat))) (Expr.var "weight.i") ((3:Nat)) (Env.vars σ_1 "weight.i") (RunStep.eval_lit B ((3:Nat)) σ_1 h3) (RunStep.eval_var B σ_1 "weight.i" (?nAX_g7844_0_0_1)) (?nAX_g7844_0_0_2)) (?nAX_g7844_0_0_3))) (?nAX_g7844_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7844_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7844_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7844_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7844_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7844_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩:=hpstep σ ⟨hbase,rfl⟩
  obtain ⟨μ,r2,p2⟩:=read_weight_from_prefix_spec B front tail qs i hlt (by omega) htwo
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) ν
    ⟨by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hp,p1⟩
  have rr:=r1.seq r2
  have hcalc:=compute_copies_spec B qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
    htwo horder hnum hden henB hedB hmaxn hmaxd hprod0 hprod1 hprod2 hprod3 hprod4 hprod5
  obtain ⟨ξ,r3,p3⟩:=hcalc μ ⟨(rr.frame_var "input.n" (by decide)).trans hnσ,p2.1,p2.2,
    (rr.frame_var "accuracy.n" (by decide)).trans henσ,(rr.frame_var "accuracy.d" (by decide)).trans hedσ,
    (rr.frame_var "maximum.n" (by decide)).trans hWnσ,(rr.frame_var "maximum.d" (by decide)).trans hWdσ⟩
  let xs:=counts qs.length en ed Wn Wd qs
  let count:=copyCount qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
  have hxs:xs.length=qs.length:=List.length_map _
  have hxsi:(xs.take i).length=i:=by simp only [List.length_take,hxs]; omega
  have hcount:count< B:=(Nat.div_le_self _ _).trans_lt hprod3
  have r123:=r1.seq (r2.seq r3)
  have hiξ:ξ.vars "weight.i"=i:=r123.frame_var "weight.i" (by decide)
  have hprefixξ:Prefix (xs.take i) "copy.counts" ξ:=by
    simpa only [Prefix,r123.frame_arr "copy.counts" (by decide)] using hprefix
  have hroomξ:i<(ξ.arrs "copy.counts").length:=by
    rw [Lax455465Proofs.RamFrames.run_array_length r123]
    omega
  obtain ⟨τ,r4,p4⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "copy.counts" "weight.i"
    (xs.take i) count (.var "copy.count") (by omega) (by rw [hxsi]; omega) ξ
    ⟨hprefixξ,by rwa [hxsi],by rwa [hxsi],by rw [evalB_var_iff]; exact ⟨p3.symm,p3 ▸ hcount⟩⟩
  have hnext:xs.take i++[count]=xs.take (i+1):=by
    rw [List.take_succ_eq_append_getElem (by omega:i< xs.length)]
    simp only [xs,counts,List.getElem_map]
    rfl
  have hti:τ.vars "weight.i"=i+1:=by simpa only [hxsi] using p4.2
  have rtotal:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by simp only [Expr.size]; omega),?_,hti⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,by omega,?_,?_⟩
  · simpa only [Prefix,rtotal.frame_arr "input.data" (by decide)] using hp
  · exact (rtotal.frame_var "input.matrixLength" (by decide)).trans hbase
  · exact (rtotal.frame_var "input.n" (by decide)).trans hnσ
  · exact (rtotal.frame_var "accuracy.n" (by decide)).trans henσ
  · exact (rtotal.frame_var "accuracy.d" (by decide)).trans hedσ
  · exact (rtotal.frame_var "maximum.n" (by decide)).trans hWnσ
  · exact (rtotal.frame_var "maximum.d" (by decide)).trans hWdσ
  · rwa [Lax455465Proofs.RamFrames.run_array_length rtotal]
  · rw [hti]
    simpa only [hnext] using p4.1

theorem command_spec (B M en ed Wn Wd:ℕ) (front tail:List ℕ) (qs:List ℚ)
    (hM:1≤ M) (hB:2*M^4+3< B) (hn:qs.length≤ M)
    (hen:en≤ M) (hed:ed≤ M) (hWn:Wn≤ M) (hWd:Wd≤ M)
    (hlen:front.length+3*qs.length+3< B)
    (hwords:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M):
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ∧
      σ.vars "input.matrixLength"=front.length∧ σ.vars "input.n"=qs.length∧
      σ.vars "accuracy.n"=en∧ σ.vars "accuracy.d"=ed∧
      σ.vars "maximum.n"=Wn∧ σ.vars "maximum.d"=Wd∧ qs.length≤(σ.arrs "copy.counts").length)
      command (fun _ τ => Prefix (counts qs.length en ed Wn Wd qs) "copy.counts" τ)
      (58*qs.length+6):=by
  have hlen':qs.length< B:=by omega
  have hstep:=step_spec B M en ed Wn Wd front tail qs hM hB hn hen hed hWn hWd hlen hwords
  have hloop:=Spec.forRangeZero "weight.i" "input.n" (Invariant front tail qs en ed Wn Wd)
    qs.length 54 hlen' (fun _ h => h.2.2.2.2.2.2.2.1) (fun _ h => h.2.2.1) hstep
  rintro σ ⟨hp,hbase,hnσ,henσ,hedσ,hWnσ,hWdσ,hroom⟩
  have hi:Invariant front tail qs en ed Wn Wd (σ.setVar "weight.i" 0):=by
    refine ⟨hp,?_,?_,?_,?_,?_,?_,by simp,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hbase
    · simpa only [vars_setVar,String.reduceEq,if_false] using hnσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using henσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hedσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hWnσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hWdσ
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,hpost⟩:=hloop σ hi
  refine ⟨τ,rr,?_⟩
  have hx:=hpost.1.2.2.2.2.2.2.2.2.2
  rw [hpost.2] at hx
  have heq:(counts qs.length en ed Wn Wd qs).take qs.length=counts qs.length en ed Wn Wd qs:=
    List.take_of_length_le (by simp [counts])
  simpa only [heq] using hx

theorem counts_correct {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ) (hε:0<ε):
    let a:=Lax263307Proofs.NativeMaximum.maximum (List.ofFn w)
    counts n ε.num.natAbs ε.den a.1 a.2 (List.ofFn w) =
      List.ofFn (Lax263307.WeightRounding.copies (fun v => max (w v) 0) ε):=by
  intro a
  have hpositive:0< a.2:=by

    have hp (qs:List ℚ) (b:ℕ×ℕ) (hb:0< b.2):
        0<(qs.foldl Lax263307Proofs.NativeMaximum.advance b).2:=by
      induction qs generalizing b with
      | nil => exact hb
      | cons q qs ih => exact ih _ (Lax263307Proofs.NativeMaximum.advance_positive b q hb)
    exact hp _ (0,1) (by omega)
  have henum:(ε.num.natAbs:ℚ)=(ε.num:ℚ):=by
    have he:(ε.num.natAbs:ℤ)=ε.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hε.le)
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) he
  simp only [counts,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  dsimp only [Function.comp_apply]
  rw [quotient_copies _ _ _ _ _ _ _ (w v).den_pos ε.den_pos hpositive,clipped_value,henum,ε.num_div_den]
  have hmax:=Lax263307Proofs.NativeMaximum.maximum_value w
  change (a.1:ℚ)/a.2=_ at hmax
  rw [hmax]
  rfl

theorem read_accuracy_spec (B:ℕ) (front:List ℕ) (qs:List ℚ) (ε:ℚ) (hε:0<ε)
    (hsize:front.length+3*qs.length+3< B) (hnum:ε.num.natAbs< B) (hden:ε.den< B):
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++encodeRational ε) "input.data" σ∧
      σ.vars "input.matrixLength"=front.length∧ σ.vars "input.weightLength"=3*qs.length)
      readAccuracy (fun _ τ => τ.vars "accuracy.n"=ε.num.natAbs∧ τ.vars "accuracy.d"=ε.den) 32:=by
  let pos:=front.length+3*qs.length
  have hpos:pos< B:=by omega
  have hfront:front.length< B:=by omega
  have hw:3*qs.length< B:=by omega
  have h2:2< B:=by omega
  have hclip:clippedNumerator ε=ε.num.natAbs:=by
    unfold clippedNumerator
    rw [if_neg (not_lt.mpr (Rat.num_nonneg.mpr hε.le))]
  rintro σ ⟨hp,hbase,hwlen⟩
  let ν:=σ.setVar "weight.position" pos
  have r1:Run B (.assign "weight.position" (.add (.var "input.matrixLength") (.var "input.weightLength"))) σ ν 4:=by
    apply Run.assign
    apply evalB_bin (op:=.add)
    · rw [evalB_var_iff]; exact ⟨hbase.symm,hbase ▸ hfront⟩
    · rw [evalB_var_iff]; exact ⟨hwlen.symm,hwlen ▸ hw⟩
    · exact hpos
  have hencoded:(front++qs.flatMap encodeRational++encodeRational ε).length=pos+3:=by
    rw [List.length_append,List.length_append,encoded_length]
    simp only [encodeRational,List.length_cons,List.length_nil]
    rfl
  have hget (j:ℕ) (hj:j<3):(ν.arrs "input.data")[pos+j]?=(encodeRational ε)[j]?:=by
    have hidx:pos+j<(front++qs.flatMap encodeRational++encodeRational ε).length:=by omega
    have hh:=hp (pos+j) hidx
    rw [← List.getElem?_eq_getElem hidx] at hh
    change (σ.arrs "input.data")[pos+j]?=(encodeRational ε)[j]?
    rw [hh,List.getElem?_append_right (by rw [List.length_append,encoded_length]; dsimp [pos]; omega)]
    congr 1
    rw [List.length_append,encoded_length]
    dsimp only [pos]
    omega
  obtain ⟨μ,r2,p2⟩:=read_weight_spec B pos ε (by omega) h2 hnum hden ν
    ⟨by simp [ν],by simpa [encodeRational] using hget 0 (by omega),
      by simpa [encodeRational] using hget 1 (by omega),
      by simpa [encodeRational] using hget 2 (by omega)⟩
  have hnμ:μ.vars "weight.n"=ε.num.natAbs:=p2.1.trans hclip
  let ξ:=μ.setVar "accuracy.n" ε.num.natAbs
  have r3:Run B (.assign "accuracy.n" (.var "weight.n")) μ ξ 2:=Run.assign (by
    rw [evalB_var_iff]; exact ⟨hnμ.symm,hnμ ▸ hnum⟩)
  let τ:=ξ.setVar "accuracy.d" ε.den
  have hdξ:ξ.vars "weight.d"=ε.den:=(r3.frame_var "weight.d" (by decide)).trans p2.2
  have r4:Run B (.assign "accuracy.d" (.var "weight.d")) ξ τ 2:=Run.assign (by
    rw [evalB_var_iff]; exact ⟨hdξ.symm,hdξ ▸ hden⟩)
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),by simp [τ,ξ],by simp [τ]⟩

end Lax263307Proofs.NativeMultiplicities

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

def emit:Com:=.seq (.assign "emit.count" (.var "input.n"))
  (Lax455465Proofs.RamEmitWords.command "copy.counts" 1)

def command:Com:=.seq prepare emit

theorem adjacency_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:
    (adjacency G).length=n*n:=by
  simp [adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const]

theorem input_words {n:ℕ} (M:ℕ) (hM:1≤ M) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ) (hw:∀ v,(w v).num.natAbs≤ M∧ (w v).den≤ M)
    (hε:ε.num.natAbs≤ M∧ ε.den≤ M):∀ z∈tailInput G w ε,z≤ M:=by
  have hr (q:ℚ) (hq:q.num.natAbs≤ M∧ q.den≤ M):∀ z∈encodeRational q,z≤ M:=by
    intro z hz
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact hq.1
    · exact hq.2
  intro z hz
  simp only [tailInput,encodeParameters,List.mem_append] at hz
  rcases hz with hgraph | hweights | hacc
  · obtain ⟨row,hrow,hz⟩:=List.mem_flatten.mp hgraph
    obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hrow
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hz
    split_ifs <;> omega
  · obtain ⟨q,hq,hz⟩:=List.mem_flatMap.mp hweights
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hr _ (hw v) z hz
  · exact hr _ hε z hacc

theorem prepare_spec {n:ℕ} (B M:ℕ) (hM:1≤ M) (hn:n≤ M)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (w:Fin n→ ℚ) (ε:ℚ) (hεpos:0<ε)
    (hw:∀ v,(w v).num.natAbs≤ M∧ (w v).den≤ M) (hε:ε.num.natAbs≤ M∧ ε.den≤ M)
    (hB:2*M^4+3< B) (hsize:n*n+3*n+3< B):
    Spec B (fun σ => σ.inp=encodeInput G w ε∧ n*n+3*n+3≤(σ.arrs "input.data").length∧
      n≤(σ.arrs "copy.counts").length) prepare
      (fun σ τ => Prefix (List.ofFn (copies (fun v => max (w v) 0) ε)) "copy.counts" τ∧
        τ.vars "input.n"=n∧ τ.out=σ.out∧ Prefix (tailInput G w ε) "input.data" τ)
      (12*(n*n+3*n+3)+110*n+78):=by
  let qs:=List.ofFn w
  let a:=NativeMaximum.maximum qs
  have hqs:qs.length=n:=List.length_ofFn
  have hp2:M^2≤ M^4:=Nat.pow_le_pow_right hM (by omega)
  have hp1:M≤ M^4:=by simpa using Nat.pow_le_pow_right hM (by omega:1≤4)
  have hMB:M< B:=by omega
  have hB2:2*M^2+3< B:=by omega
  have hwords:∀ q∈qs,q.num.natAbs≤ M∧ q.den≤ M:=by
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hw v
  have hmax:=NativeMaximum.maximum_bounds M hM qs hwords
  have htail:tailInput G w ε=adjacency G++qs.flatMap encodeRational++encodeRational ε:=by
    simp only [tailInput,adjacency,encodeParameters,List.append_assoc,qs]
  have hfront:=adjacency_length G
  rintro σ ⟨hinp,hroom,hcountsroom⟩
  obtain ⟨ν,r1,p1⟩:=read_input_spec B n (tailInput G w ε) hsize (tail_length G w ε)
    (fun z hz => (input_words M hM G w ε hw hε z hz).trans_lt hMB) σ
    ⟨by simpa only [encodeInput,tailInput,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using hinp,
      by rwa [tail_length]⟩
  obtain ⟨μ,r2,p2⟩:=NativeMaximum.command_spec B M (adjacency G) (encodeRational ε) qs hM hB2
    (by rwa [hfront,hqs]) hwords ν ⟨by simpa only [htail] using p1.2.2.2.2.2,
      p1.2.1.trans hfront.symm,p1.1.trans hqs.symm⟩
  have r12:=r1.seq r2
  have hpμ:Prefix (adjacency G++qs.flatMap encodeRational++encodeRational ε) "input.data" μ:=by
    simpa only [Prefix,r2.frame_arr "input.data" (by decide),htail] using p1.2.2.2.2.2
  have hbaseμ:μ.vars "input.matrixLength"=(adjacency G).length:=
    (r2.frame_var "input.matrixLength" (by decide)).trans (p1.2.1.trans hfront.symm)
  have hweightμ:μ.vars "input.weightLength"=3*qs.length:=
    (r2.frame_var "input.weightLength" (by decide)).trans (by simpa only [hqs] using p1.2.2.1)
  obtain ⟨ξ,r3,p3⟩:=NativeMultiplicities.read_accuracy_spec B (adjacency G) qs ε hεpos
    (by rwa [hfront,hqs]) (hε.1.trans_lt hMB) (hε.2.trans_lt hMB) μ ⟨hpμ,hbaseμ,hweightμ⟩
  have r123:=r1.seq (r2.seq r3)
  have hpξ:Prefix (adjacency G++qs.flatMap encodeRational++encodeRational ε) "input.data" ξ:=by
    simpa only [Prefix,r3.frame_arr "input.data" (by decide)] using hpμ
  have hbaseξ:=(r3.frame_var "input.matrixLength" (by decide)).trans hbaseμ
  have hnξ:ξ.vars "input.n"=qs.length:=
    (r3.frame_var "input.n" (by decide)).trans ((r2.frame_var "input.n" (by decide)).trans (p1.1.trans hqs.symm))
  have hmaxnξ:ξ.vars "maximum.n"=a.1:=(r3.frame_var "maximum.n" (by decide)).trans p2.1
  have hmaxdξ:ξ.vars "maximum.d"=a.2:=(r3.frame_var "maximum.d" (by decide)).trans p2.2
  have hcountsξ:qs.length≤(ξ.arrs "copy.counts").length:=by
    rw [Lax455465Proofs.RamFrames.run_array_length r123,hqs]
    exact hcountsroom
  obtain ⟨τ,r4,p4⟩:=NativeMultiplicities.command_spec B M ε.num.natAbs ε.den a.1 a.2
    (adjacency G) (encodeRational ε) qs hM hB (by rwa [hqs]) hε.1 hε.2 hmax.1 hmax.2.1
    (by rwa [hfront,hqs]) hwords ξ ⟨hpξ,hbaseξ,hnξ,p3.1,p3.2,hmaxnξ,hmaxdξ,hcountsξ⟩
  have rtotal:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by simp only [tail_length,hqs]; omega),?_,?_,?_,?_⟩
  · have heq:NativeMultiplicities.counts n ε.num.natAbs ε.den a.1 a.2 qs =
        List.ofFn (copies (fun v => max (w v) 0) ε):=NativeMultiplicities.counts_correct w ε hεpos
    rw [hqs] at p4
    rw [heq] at p4
    exact p4
  · exact (r4.frame_var "input.n" (by decide)).trans (hnξ.trans hqs)
  · exact rtotal.out_eq (by decide)
  · have rr:=r2.seq (r3.seq r4)
    simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using p1.2.2.2.2.2

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

def blocks {n:ℕ} (copies:Fin n→ ℕ):List (List ℕ):=
  List.ofFn fun v => List.replicate (copies v) v.val

def owners {n:ℕ} (copies:Fin n→ ℕ):List ℕ:=(blocks copies).flatten

theorem blocks_length {n:ℕ} (copies:Fin n→ ℕ):(blocks copies).length=n:=by
  simp [blocks]

theorem owners_length {n:ℕ} (copies:Fin n→ ℕ):(owners copies).length=∑ v,copies v:=by
  simp [owners,blocks,List.length_flatten,List.map_ofFn,List.sum_ofFn]

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

theorem owners_coordinate {n:ℕ} (copies:Fin n→ ℕ)
    (v:Fin n) (j:Fin (copies v)):
    (owners copies)[(finSigmaFinEquiv ⟨v,j⟩).val]?=some v.val:=by
  have hi:v.val<(blocks copies).length:=by rw [blocks_length]; exact v.isLt
  have hb:(blocks copies)[v.val]=List.replicate (copies v) v.val:=by
    simp [blocks]
  have hp:((blocks copies).take v.val).map List.length =
      List.ofFn (fun i:Fin v.val => copies (Fin.castLE v.isLt.le i)):=by
    rw [List.map_take]
    have hm:(blocks copies).map List.length=List.ofFn copies:=by
      rw [blocks,List.map_ofFn]
      congr 1
      funext v
      exact List.length_replicate
    rw [hm]
    exact (Fin.ofFn_take_eq_take_ofFn v.isLt.le copies).symm
  have hx:=flattened_coordinate (blocks copies) v.val hi j.val (by simpa only [hb,List.length_replicate] using j.isLt)
  simpa only [owners,finSigmaFinEquiv_apply,hp,List.sum_ofFn,hb,List.getElem_replicate] using hx

theorem owners_labeling {n:ℕ} (copies:Fin n→ ℕ) (i:Fin (∑ v,copies v)):
    (owners copies)[i.val]?=some (labeling copies i).1.val:=by
  have hx:=owners_coordinate copies (labeling copies i).1 (labeling copies i).2
  simpa only [labeling,Sigma.eta,Equiv.apply_symm_apply] using hx

def RepeatInvariant (xs:List ℕ) (v count:ℕ) (σ:Env):Prop:=
  σ.vars "owner.j"≤ count∧ σ.vars "owner.count"=count∧ σ.vars "owner.value"=v∧
  σ.vars "blowup.length"=xs.length+σ.vars "owner.j" ∧
  xs.length+count≤(σ.arrs "blowup.owner").length∧
  Prefix (xs++List.replicate (σ.vars "owner.j") v) "blowup.owner" σ

theorem repeat_step_spec (B:ℕ) (xs:List ℕ) (v count:ℕ)
    (hB:xs.length+count+2< B) (hv:v< B):
    Spec B (fun σ => RepeatInvariant xs v count σ∧ σ.vars "owner.j"< count)
      repeatStep (fun σ τ => RepeatInvariant xs v count τ∧ τ.vars "owner.j"=σ.vars "owner.j"+1) 11:=by
  rintro σ ⟨⟨hj,hcount,hvσ,hlen,hroom,hprefix⟩,hlt⟩
  let j:=σ.vars "owner.j"
  have hl:(xs++List.replicate j v).length=xs.length+j:=by simp
  obtain ⟨ν,r1,p1⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "blowup.owner" "blowup.length"
    (xs++List.replicate j v) v (.var "owner.value") (by omega) (by rw [hl]; omega) σ
    ⟨hprefix,by rwa [hl],by rw [hl]; omega,by rw [evalB_var_iff]; exact ⟨hvσ.symm,hvσ ▸ hv⟩⟩
  have hjν:ν.vars "owner.j"=j:=r1.frame_var "owner.j" (by decide)
  have he:(Expr.add (.var "owner.j") (.lit 1)).evalB B ν=some (j+1):=
    evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hjν.symm,hjν ▸ (by omega)⟩)
      (evalB_lit (by omega)) (by change j+1< B; dsimp [j]; omega)
  let τ:=ν.setVar "owner.j" (j+1)
  have r2:Run B (.assign "owner.j" (.add (.var "owner.j") (.lit 1))) ν τ 4:=Run.assign he
  have rr:=r1.seq r2
  have ht:τ.vars "owner.j"=j+1:=by simp [τ]
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨by rw [ht]; omega,(rr.frame_var "owner.count" (by decide)).trans hcount,
    (rr.frame_var "owner.value" (by decide)).trans hvσ,?_,?_,?_⟩
  · rw [r2.frame_var "blowup.length" (by decide),p1.2,hl,ht]
    omega
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht]
    have hx:xs++List.replicate j v++[v]=xs++List.replicate (j+1) v:=by
      rw [List.replicate_add]
      simp only [List.replicate_one,List.append_assoc]
    simpa only [Prefix,τ,arrs_setVar,hx] using p1.1

theorem repeat_spec (B:ℕ) (xs:List ℕ) (v count:ℕ)
    (hB:xs.length+count+2< B) (hv:v< B):
    Spec B (fun σ => σ.vars "owner.count"=count∧ σ.vars "owner.value"=v∧
      σ.vars "blowup.length"=xs.length∧ xs.length+count≤(σ.arrs "blowup.owner").length∧
      Prefix xs "blowup.owner" σ) repeatCommand
      (fun _ τ => Prefix (xs++List.replicate count v) "blowup.owner" τ∧
        τ.vars "blowup.length"=xs.length+count) (15*count+6):=by
  have hloop:=Spec.forRangeZero "owner.j" "owner.count" (RepeatInvariant xs v count)
    count 11 (by omega) (fun _ h => h.1) (fun _ h => h.2.1) (repeat_step_spec B xs v count hB hv)
  rintro σ ⟨hc,hvσ,hlen,hroom,hprefix⟩
  have hi:RepeatInvariant xs v count (σ.setVar "owner.j" 0):=by
    refine ⟨by simp,?_,?_,?_,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hc
    · simpa only [vars_setVar,String.reduceEq,if_false] using hvσ
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.add_zero] using hlen
    · simpa only [vars_setVar,if_true,List.replicate_zero,List.append_nil,Prefix,arrs_setVar] using hprefix
  obtain ⟨τ,rr,hpost⟩:=hloop σ hi
  refine ⟨τ,rr,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2
  · simpa only [hpost.2] using hpost.1.2.2.2.1

def ownerPrefix {n:ℕ} (copies:Fin n→ ℕ) (i:ℕ):List ℕ:=
  ((blocks copies).take i).flatten

theorem partial_length_le {n:ℕ} (copies:Fin n→ ℕ) (i:ℕ):
    (ownerPrefix copies i).length≤∑ v,copies v:=by
  have he:owners copies=ownerPrefix copies i++((blocks copies).drop i).flatten:=by
    rw [owners,ownerPrefix,←List.flatten_append,List.take_append_drop]
  have hh:=congrArg List.length he
  rw [owners_length,List.length_append] at hh
  omega

theorem partial_succ {n:ℕ} (copies:Fin n→ ℕ) (i:ℕ) (hi:i< n):
    ownerPrefix copies (i+1)=ownerPrefix copies i++List.replicate (copies ⟨i,hi⟩) i:=by
  unfold ownerPrefix
  rw [List.take_succ_eq_append_getElem (by rwa [blocks_length]),List.flatten_append]
  simp [blocks]

def OwnerInvariant {n:ℕ} (copies:Fin n→ ℕ) (σ:Env):Prop:=
  σ.vars "owner.i"≤ n∧ σ.vars "input.n"=n∧
  Prefix (List.ofFn copies) "copy.counts" σ∧
  (∑ v,copies v)≤(σ.arrs "blowup.owner").length∧
  σ.vars "blowup.length"=(ownerPrefix copies (σ.vars "owner.i")).length∧
  Prefix (ownerPrefix copies (σ.vars "owner.i")) "blowup.owner" σ

theorem owner_step_spec {n:ℕ} (B:ℕ) (copies:Fin n→ ℕ)
    (hB:n+(∑ v,copies v)+3< B):
    Spec B (fun σ => OwnerInvariant copies σ∧ σ.vars "owner.i"< n) ownerStep
      (fun σ τ => OwnerInvariant copies τ∧ τ.vars "owner.i"=σ.vars "owner.i"+1)
      (15*(∑ v,copies v)+15):=by
  rintro σ ⟨⟨hle,hn,hcounts,hroom,hlen,hprefix⟩,hlt⟩
  let i:=σ.vars "owner.i"
  let v:Fin n:= ⟨i,hlt⟩
  let xs:=ownerPrefix copies i
  have hs:=partial_length_le copies (i+1)
  rw [partial_succ copies i hlt,List.length_append,List.length_replicate] at hs
  have hcB:copies v< B:=by dsimp [v] at *; omega
  have hiB:i< B:=by omega
  have hd:(σ.arrs "copy.counts")[i]?=some (copies v):=by
    have hh:=hcounts i (by simpa using hlt)
    rw [List.getElem_ofFn] at hh
    exact hh
  have prep:Spec B (fun σ => σ.vars "owner.i"=i∧ (σ.arrs "copy.counts")[i]?=some (copies v))
      ownerPrepare (fun _ τ => τ.vars "owner.value"=i∧ τ.vars "owner.count"=copies v) 5:=by
    rintro σ ⟨hsi,hsval⟩
    have hroom:i<(σ.arrs "copy.counts").length:=by
      by_contra hh
      rw [List.getElem?_eq_none (by omega)] at hsval
      contradiction
    (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "owner.value") i) (@Eq Nat (Env.vars τ "owner.count") (copies v))) σ; let c1:Nat:=Env.vars (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "owner.i"; let c2:Nat:= @List.getD Nat (Env.arrs (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "copy.counts") c1 ((0:Nat)); let c3:Env:=Env.setVar (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "owner.count" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "owner.i")); let c7:Nat:=c5 (Expr.size (Expr.get "copy.counts" (Expr.var "owner.i"))); let c8:String→ Nat:=Env.vars c3; @Exists.intro Env (fun (σ':Env) => And (Run B ownerPrepare σ σ' ((5:Nat))) (c0 σ')) c3 (@And.intro (Run B ownerPrepare σ c3 ((5:Nat))) (c0 c3) (RunStep.mono B ownerPrepare σ c3 (c4 c6 c7) ((5:Nat)) (RunStep.seq B (Com.assign "owner.value" (Expr.var "owner.i")) (Com.assign "owner.count" (Expr.get "copy.counts" (Expr.var "owner.i"))) σ (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) c3 c6 c7 (RunStep.assign B σ "owner.value" (Expr.var "owner.i") (Env.vars σ "owner.i") (RunStep.eval_var B σ "owner.i" (?nAX_g7878_0_0_0))) (RunStep.assign B (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "owner.count" (Expr.get "copy.counts" (Expr.var "owner.i")) c2 (RunStep.eval_get B (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "copy.counts" (Expr.var "owner.i") c1 (RunStep.eval_var B (Env.setVar σ "owner.value" (Env.vars σ "owner.i")) "owner.i" (?nAX_g7878_0_0_1)) (?nAX_g7878_0_0_2) ?_))) (?nAX_g7878_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7878_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7878_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7878_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7878_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩:=prep σ ⟨rfl,hd⟩
  obtain ⟨μ,r2,p2⟩:=repeat_spec B xs i (copies v) (by dsimp [xs,v]; omega) hiB ν
    ⟨p1.2,p1.1,(r1.frame_var "blowup.length" (by decide)).trans hlen,
      by rw [Lax455465Proofs.RamFrames.run_array_length r1]; exact hs.trans hroom,
      by simpa only [Prefix,r1.frame_arr "blowup.owner" (by decide)] using hprefix⟩
  have r12:=r1.seq r2
  have hiμ:μ.vars "owner.i"=i:=r12.frame_var "owner.i" (by decide)
  let τ:=μ.setVar "owner.i" (i+1)
  have r3:Run B (.assign "owner.i" (.add (.var "owner.i") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1< B; dsimp [i]; omega))
  have rr:=r1.seq (r2.seq r3)
  have ht:τ.vars "owner.i"=i+1:=by simp [τ]
  refine ⟨τ,rr.mono (by dsimp [v] at *; omega),?_,ht⟩
  refine ⟨by rw [ht]; omega,(rr.frame_var "input.n" (by decide)).trans hn,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "copy.counts" (by decide)] using hcounts
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,partial_succ copies i hlt,List.length_append,List.length_replicate]
    exact (r3.frame_var "blowup.length" (by decide)).trans p2.2
  · rw [ht,partial_succ copies i hlt]
    simpa only [Prefix,r3.frame_arr "blowup.owner" (by decide)] using p2.1

theorem owner_command_spec {n:ℕ} (B:ℕ) (copies:Fin n→ ℕ)
    (hB:n+(∑ v,copies v)+3< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ Prefix (List.ofFn copies) "copy.counts" σ∧
      (∑ v,copies v)≤(σ.arrs "blowup.owner").length) ownerCommand
      (fun _ τ => Prefix (owners copies) "blowup.owner" τ∧ τ.vars "blowup.length"=∑ v,copies v)
      ((15*(∑ v,copies v)+19)*n+8):=by
  have hloop:=Spec.forRangeZero "owner.i" "input.n" (OwnerInvariant copies) n
    (15*(∑ v,copies v)+15) (by omega) (fun _ h => h.1) (fun _ h => h.2.1)
    (owner_step_spec B copies hB)
  rintro σ ⟨hn,hcounts,hroom⟩
  let ν:=σ.setVar "blowup.length" 0
  have r1:Run B (.assign "blowup.length" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:OwnerInvariant copies (ν.setVar "owner.i" 0):=by
    refine ⟨by simp,?_,hcounts,hroom,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,ownerPrefix]
    · simp only [vars_setVar,if_true,ownerPrefix,List.take_zero,List.flatten_nil,Prefix,List.length_nil]
      intro j hj
      omega
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  have he:ownerPrefix copies n=owners copies:=by
    unfold ownerPrefix owners
    rw [List.take_of_length_le (by rw [blocks_length])]
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),?_,?_⟩
  · simpa only [p2.2,he] using p2.1.2.2.2.2.2
  · simpa only [p2.2,he,owners_length] using p2.1.2.2.2.2.1

def matrix {n:ℕ} (f:Fin n→ Fin n→ ℕ):List ℕ:=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem matrix_length {n:ℕ} (f:Fin n→ Fin n→ ℕ):(matrix f).length=n*n:=by
  simp [matrix,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]

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

theorem matrix_entry_spec (B n N q u v entry:ℕ) (hB:n*n+N*N+n+N+3< B)
    (hq:q< N*N) (hu:u< n) (hv:v< n) (he:entry< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ σ.vars "blowup.length"=N∧ σ.vars "matrix.i"=q∧
      (σ.arrs "blowup.owner")[q/N]?=some u∧ (σ.arrs "blowup.owner")[q%N]?=some v∧
      (σ.arrs "input.data")[u*n+v]?=some entry) matrixEntry
      (fun _ τ => τ.vars "matrix.entry"=entry) 21:=by
  have hN:0< N:=by nlinarith only [hq]
  have hqN:q/N< N:=(Nat.div_lt_iff_lt_mul hN).mpr hq
  have hrN:q%N< N:=Nat.mod_lt _ hN
  have hidx:u*n+v< n*n:=by nlinarith only [hu,hv]
  have hmul:u*n< B:=by omega
  have hdivmul:q/N*N≤ q:=Nat.div_mul_le_self q N
  have hmod:q-q/N*N=q%N:=(Nat.mod_eq_sub_div_mul).symm
  rintro σ ⟨hn,hNσ,hqσ,huσ,hvσ,heσ⟩
  have hroomu:q/N<(σ.arrs "blowup.owner").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at huσ
    contradiction
  have hroomv:q%N<(σ.arrs "blowup.owner").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hvσ
    contradiction
  have hroome:u*n+v<(σ.arrs "input.data").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "matrix.entry") entry) σ; let c1:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c2:Nat:=c1 (Env.vars σ "matrix.i") (Env.vars σ "blowup.length"); let c3:Nat:= @List.getD Nat (Env.arrs σ "blowup.owner") c2 ((0:Nat)); let c4:Env:=Env.setVar σ "matrix.u" c3; let c5:List Nat:=Env.arrs c4 "blowup.owner"; let c6:String→ Nat:=Env.vars c4; let c7:Nat:=c6 "matrix.i"; let c8:Nat→ Nat→ Nat:=Nat.mul; let c9:Nat:=c6 "blowup.length"; let c10:Nat:=c1 c7 c9; let c11:Nat:=c8 c10 c9; let c12:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c11; let c13:Nat:= @List.getD Nat c5 c12 ((0:Nat)); let c14:Env:=Env.setVar c4 "matrix.v" c13; let c15:List Nat:=Env.arrs c14 "input.data"; let c16:Nat→ Nat→ Nat:=Nat.add; let c17:String→ Nat:=Env.vars c14; let c18:Nat:=c17 "matrix.u"; let c19:Nat:=c17 "input.n"; let c20:Nat:=c8 c18 c19; let c21:Nat:=c17 "matrix.v"; let c22:Nat:=c16 c20 c21; let c23:Nat:= @List.getD Nat c15 c22 ((0:Nat)); let c24:Env:=Env.setVar c14 "matrix.entry" c23; let c25:Nat→ Nat:=c16 ((1:Nat)); let c26:Expr:=Expr.get "blowup.owner" (Expr.div (Expr.var "matrix.i") (Expr.var "blowup.length")); let c27:Nat:=c25 (Expr.size c26); let c28:Expr:=Expr.mul (Expr.div (Expr.var "matrix.i") (Expr.var "blowup.length")) (Expr.var "blowup.length"); let c29:Expr:=Expr.sub (Expr.var "matrix.i") c28; let c30:Expr:=Expr.get "blowup.owner" c29; let c31:Nat:=c25 (Expr.size c30); let c32:Expr:=Expr.add (Expr.mul (Expr.var "matrix.u") (Expr.var "input.n")) (Expr.var "matrix.v"); let c33:Expr:=Expr.get "input.data" c32; let c34:Nat:=c25 (Expr.size c33); let c35:Nat:=c16 c31 c34; let c36:Com:=Com.assign "matrix.v" c30; let c37:Com:=Com.assign "matrix.entry" c33; let c38:Nat→ Prop:=Nat.lt c2; let c39:Nat→ Prop:=Nat.lt c22; @Exists.intro Env (fun (σ':Env) => And (Run B matrixEntry σ σ' ((21:Nat))) (c0 σ')) c24 (@And.intro (Run B matrixEntry σ c24 ((21:Nat))) (c0 c24) (RunStep.mono B matrixEntry σ c24 (c16 c27 c35) ((21:Nat)) (RunStep.seq B (Com.assign "matrix.u" c26) (Com.seq c36 c37) σ c4 c24 c27 c35 (RunStep.assign B σ "matrix.u" c26 c3 (RunStep.eval_get B σ "blowup.owner" (Expr.div (Expr.var "matrix.i") (Expr.var "blowup.length")) c2 (RunStep.eval_div B σ (Expr.var "matrix.i") (Expr.var "blowup.length") (Env.vars σ "matrix.i") (Env.vars σ "blowup.length") (RunStep.eval_var B σ "matrix.i" (?nAX_g7888_0_0_0)) (RunStep.eval_var B σ "blowup.length" (?nAX_g7888_0_0_1)) ?_) ?_ ?_)) (RunStep.seq B c36 c37 c4 c14 c24 c31 c34 (RunStep.assign B c4 "matrix.v" c30 c13 (RunStep.eval_get B c4 "blowup.owner" c29 c12 (RunStep.eval_sub B c4 (Expr.var "matrix.i") c28 c7 c11 (RunStep.eval_var B c4 "matrix.i" (?nAX_g7888_0_0_2)) (RunStep.eval_mul B c4 (Expr.div (Expr.var "matrix.i") (Expr.var "blowup.length")) (Expr.var "blowup.length") c10 c9 (RunStep.eval_div B c4 (Expr.var "matrix.i") (Expr.var "blowup.length") c7 c9 (RunStep.eval_var B c4 "matrix.i" (?nAX_g7888_0_0_3)) (RunStep.eval_var B c4 "blowup.length" (?nAX_g7888_0_0_4)) ?_) (RunStep.eval_var B c4 "blowup.length" (?nAX_g7888_0_0_5)) ?_) (?nAX_g7888_0_0_6)) ?_ ?_)) (RunStep.assign B c14 "matrix.entry" c33 c23 (RunStep.eval_get B c14 "input.data" c32 c22 (RunStep.eval_add B c14 (Expr.mul (Expr.var "matrix.u") (Expr.var "input.n")) (Expr.var "matrix.v") c20 c21 (RunStep.eval_mul B c14 (Expr.var "matrix.u") (Expr.var "input.n") c18 c19 (RunStep.eval_var B c14 "matrix.u" ?_) (RunStep.eval_var B c14 "input.n" (?nAX_g7888_0_0_7)) ?_) (RunStep.eval_var B c14 "matrix.v" ?_) ?_) ?_ ?_)))) (?nAX_g7888_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7888_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7888_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def numberedMatrix {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies:Fin n→ ℕ):List ℕ:=matrix (fun i j => if (numbered G copies).Adj i j then 1 else 0)

def MatrixInvariant {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies:Fin n→ ℕ) (σ:Env):Prop:=
  σ.vars "input.n"=n∧ σ.vars "blowup.length"=∑ v,copies v∧
  σ.vars "matrix.length"=(∑ v,copies v)*(∑ v,copies v)∧
  σ.vars "matrix.i"≤(numberedMatrix G copies).length∧
  Prefix (NativeWeightReduction.adjacency G) "input.data" σ∧
  Prefix (owners copies) "blowup.owner" σ∧
  (numberedMatrix G copies).length≤(σ.arrs "blowup.matrix").length∧
  Prefix ((numberedMatrix G copies).take (σ.vars "matrix.i")) "blowup.matrix" σ

theorem matrix_step_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies:Fin n→ ℕ) (hB:n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3< B):
    Spec B (fun σ => MatrixInvariant G copies σ∧ σ.vars "matrix.i"<(numberedMatrix G copies).length)
      matrixStep (fun σ τ => MatrixInvariant G copies τ∧ τ.vars "matrix.i"=σ.vars "matrix.i"+1) 28:=by
  rintro σ ⟨⟨hn,hN,hlen,hle,hgraph,howners,hroom,hprefix⟩,hlt⟩
  let N:= ∑ v,copies v
  let xs:=numberedMatrix G copies
  let q:=σ.vars "matrix.i"
  have hxs:xs.length=N*N:=matrix_length _
  have hq:q< N*N:=by simpa only [←hxs] using hlt
  let i:=row (⟨q,hq⟩:Fin (N*N))
  let j:=col (⟨q,hq⟩:Fin (N*N))
  let u:=(labeling copies i).1
  let v:=(labeling copies j).1
  let entry:=if G.Adj u v then 1 else 0
  have hentry:entry< B:=by dsimp [entry]; split_ifs <;> omega
  have hou:(σ.arrs "blowup.owner")[q/N]?=some u.val:=by
    have hh:=howners i.val (by rw [owners_length]; exact i.isLt)
    have ho:=owners_labeling copies i
    have ht:=List.getElem?_eq_getElem (by rw [owners_length]; exact i.isLt:i.val<(owners copies).length)
    rw [ht] at ho
    exact hh.trans ho
  have hov:(σ.arrs "blowup.owner")[q%N]?=some v.val:=by
    have hh:=howners j.val (by rw [owners_length]; exact j.isLt)
    have ho:=owners_labeling copies j
    have ht:=List.getElem?_eq_getElem (by rw [owners_length]; exact j.isLt:j.val<(owners copies).length)
    rw [ht] at ho
    exact hh.trans ho
  have hidx:u.val*n+v.val< n*n:=by nlinarith only [u.isLt,v.isLt]
  have hedge:(σ.arrs "input.data")[u.val*n+v.val]?=some entry:=by
    have hh:=hgraph (u.val*n+v.val) (by rwa [NativeWeightReduction.adjacency_length])
    have hc:=matrix_coordinate (fun u v => if G.Adj u v then 1 else 0) u v
    rw [List.getElem?_eq_getElem (by rwa [matrix_length])] at hc
    exact hh.trans hc
  obtain ⟨ν,r1,p1⟩:=matrix_entry_spec B n N q u.val v.val entry hB hq u.isLt v.isLt hentry σ
    ⟨hn,hN,rfl,hou,hov,hedge⟩
  have hqν:ν.vars "matrix.i"=q:=r1.frame_var "matrix.i" (by decide)
  have htake:(xs.take q).length=q:=by rw [List.length_take]; omega
  have hval:xs[q]=entry:=by
    have hc:=matrix_flat_coordinate (fun i j => if (numbered G copies).Adj i j then 1 else 0)
      (⟨q,hq⟩:Fin (N*N))
    change xs[q]?=some entry at hc
    rw [List.getElem?_eq_getElem hlt] at hc
    exact Option.some.inj hc
  obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "blowup.matrix" "matrix.i"
    (xs.take q) entry (.var "matrix.entry") (by omega) (by rw [htake]; dsimp [N] at hq; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "blowup.matrix" (by decide)] using hprefix,
      by rwa [htake],by rw [htake,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ hentry⟩⟩
  have ht:τ.vars "matrix.i"=q+1:=by simpa only [htake] using p2.2
  have rr:=r1.seq r2
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "input.n" (by decide)).trans hn,
    (rr.frame_var "blowup.length" (by decide)).trans hN,
    (rr.frame_var "matrix.length" (by decide)).trans hlen,by rw [ht]; omega,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using hgraph
  · simpa only [Prefix,rr.frame_arr "blowup.owner" (by decide)] using howners
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hlt,hval]
    exact p2.1

theorem matrix_command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies:Fin n→ ℕ) (hB:n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ σ.vars "blowup.length"=∑ v,copies v∧
      Prefix (NativeWeightReduction.adjacency G) "input.data" σ∧
      Prefix (owners copies) "blowup.owner" σ∧
      (∑ v,copies v)*(∑ v,copies v)≤(σ.arrs "blowup.matrix").length) matrixCommand
      (fun _ τ => Prefix (numberedMatrix G copies) "blowup.matrix" τ)
      (32*(∑ v,copies v)*(∑ v,copies v)+10):=by
  let N:= ∑ v,copies v
  have hlen:(numberedMatrix G copies).length=N*N:=matrix_length _
  have hNB:N< B:=by dsimp [N]; omega
  have hNNB:N*N< B:=by dsimp [N]; omega
  have hloop:=Spec.forRangeZero "matrix.i" "matrix.length" (MatrixInvariant G copies)
    (N*N) 28 hNNB (fun _ h => hlen ▸ h.2.2.2.1) (fun _ h => h.2.2.1)
    (by simpa only [hlen] using matrix_step_spec B G copies hB)
  rintro σ ⟨hn,hN,hgraph,howners,hroom⟩
  let ν:=σ.setVar "matrix.length" (N*N)
  have r1:Run B (.assign "matrix.length" (.mul (.var "blowup.length") (.var "blowup.length")))
      σ ν 4:=Run.assign (evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hNB⟩)
        (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hNB⟩) hNNB)
  have hi:MatrixInvariant G copies (ν.setVar "matrix.i" 0):=by
    refine ⟨?_,?_,by simp [ν,N],by simp,hgraph,howners,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN
    · simpa only [arrs_setVar,ν,hlen] using hroom
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by dsimp [N]; nlinarith),?_⟩
  simpa only [p2.2,←hlen,List.take_length] using p2.1.2.2.2.2.2.2.2

theorem construct_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies:Fin n→ ℕ) (hB:n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ Prefix (List.ofFn copies) "copy.counts" σ∧
      Prefix (NativeWeightReduction.adjacency G) "input.data" σ∧
      (∑ v,copies v)≤(σ.arrs "blowup.owner").length∧
      (∑ v,copies v)*(∑ v,copies v)≤(σ.arrs "blowup.matrix").length) construct
      (fun _ τ => Prefix (numberedMatrix G copies) "blowup.matrix" τ∧
        Prefix (owners copies) "blowup.owner" τ∧ τ.vars "blowup.length"=∑ v,copies v)
      ((15*(∑ v,copies v)+19)*n+32*(∑ v,copies v)*(∑ v,copies v)+18):=by
  rintro σ ⟨hn,hcounts,hgraph,hownersroom,hmatrixroom⟩
  obtain ⟨ν,r1,p1⟩:=owner_command_spec B copies (by omega) σ ⟨hn,hcounts,hownersroom⟩
  obtain ⟨τ,r2,p2⟩:=matrix_command_spec B G copies hB ν
    ⟨(r1.frame_var "input.n" (by decide)).trans hn,p1.2,
      by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hgraph,p1.1,
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),p2,?_,?_⟩
  · simpa only [Prefix,r2.frame_arr "blowup.owner" (by decide)] using p1.1
  · exact (r2.frame_var "blowup.length" (by decide)).trans p1.2

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

theorem prepare_spec {n:ℕ} (B M:ℕ) (hM:1≤ M) (hn:n≤ M)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (w:Fin n→ ℚ) (ε:ℚ) (hεpos:0<ε)
    (hw:∀ v,(w v).num.natAbs≤ M∧ (w v).den≤ M) (hε:ε.num.natAbs≤ M∧ ε.den≤ M)
    (hB:2*M^4+3< B) (hsize:n*n+3*n+3< B)
    (hgraph:n*n+(∑ v,copies (fun v => max (w v) 0) ε v)^2+n+
      (∑ v,copies (fun v => max (w v) 0) ε v)+3< B):
    let cs:=copies (fun v => max (w v) 0) ε
    let N:= ∑ v,cs v
    Spec B (fun σ => σ.inp=encodeInput G w ε∧ n*n+3*n+3≤(σ.arrs "input.data").length∧
      n≤(σ.arrs "copy.counts").length∧ N≤(σ.arrs "blowup.owner").length∧
      N*N≤(σ.arrs "blowup.matrix").length) prepare
      (fun σ τ => Prefix (numberedMatrix G cs) "blowup.matrix" τ∧
        Prefix (owners cs) "blowup.owner" τ∧ τ.vars "blowup.length"=N∧
        Prefix (tailInput G w ε) "input.data" τ∧ τ.out=σ.out∧ τ.vars "input.n"=n) (cost n N):=by
  dsimp only
  let cs:=copies (fun v => max (w v) 0) ε
  let N:= ∑ v,cs v
  rintro σ ⟨hinp,hinputroom,hcountsroom,hownersroom,hmatrixroom⟩
  obtain ⟨ν,r1,hcounts,hnν,hout,hinput⟩:=NativeWeightReduction.prepare_spec B M hM hn
    G w ε hεpos hw hε hB hsize σ ⟨hinp,hinputroom,hcountsroom⟩
  have hfront:Prefix (NativeWeightReduction.adjacency G) "input.data" ν:=by
    intro i hi
    have hfull:i<(tailInput G w ε).length:=by
      rw [tail_length]
      rw [NativeWeightReduction.adjacency_length] at hi
      omega
    have hh:=hinput i hfull
    have he:tailInput G w ε=NativeWeightReduction.adjacency G++encodeParameters w ε:=rfl
    simpa only [he,List.getElem_append_left hi] using hh
  obtain ⟨τ,r2,p2⟩:=construct_spec B G cs (by simpa only [cs,pow_two] using hgraph) ν
    ⟨hnν,hcounts,hfront,by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq r2).mono (by dsimp [cost,N,cs]; omega),p2.1,p2.2.1,p2.2.2,?_,?_,?_⟩
  · simpa only [Prefix,r2.frame_arr "input.data" (by decide)] using hinput
  · exact (r1.seq r2).out_eq (by decide)
  · exact (r2.frame_var _ (by decide)).trans hnν

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

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

end Lax263307Proofs.NativeMasks

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

namespace Lax263307Proofs.NativeEmptyOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs
open Lax263307 WeightedIndependentSet

theorem command_spec (B n:ℕ) (hB:n+3< B):
    Spec B (fun σ => σ.vars "input.n"=n∧ (σ.arrs "weighted.output").length=n)
      command (fun σ τ => τ.out=σ.out++encodeOutput (∅:Finset (Fin n))) (24*n+14):=by
  have hfill:=Fill.loop_spec B n "weighted.output" "empty.i" "input.n" (.lit 0) (fun _ => 0)
    (by decide) (by omega) (fun _ _ _ _ => evalB_lit (by omega:0< B))
  rintro σ ⟨hn,hlen⟩
  have harray:∃ g,σ.arrs "weighted.output"=arrOf n g:=by
    refine ⟨fun i => (σ.arrs "weighted.output").getD i 0,?_⟩
    apply List.ext_getElem
    · simp [arrOf,hlen]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range]
      exact List.getElem_eq_getD 0
  obtain ⟨ν,r1,⟨g,hg,hzero⟩,hi⟩:=hfill σ ⟨harray,hn⟩
  have hnν:ν.vars "input.n"=n:=(r1.frame_var _ (by simp [Fill.put,Com.wvars])).trans hn
  let μ:=ν.setVar "emit.count" n
  have r2:Run B (.assign "emit.count" (.var "input.n")) ν μ 2:=Run.assign (by
    rw [evalB_var_iff]; exact ⟨hnν.symm,hnν ▸ (by omega)⟩)
  have hp:RamEmitWords.Data "weighted.output" 1 (encodeOutput (∅:Finset (Fin n))) μ:=by
    intro i hii
    have hin:i< n:=by simpa [encodeOutput] using hii
    simp only [μ,arrs_setVar,hg,arrOf,List.getElem?_ofFn,List.length_ofFn]
    simp [hin,hzero i hin,encodeOutput]
  obtain ⟨τ,r3,po⟩:=RamEmitWords.command_spec B "weighted.output" 1
    (encodeOutput (∅:Finset (Fin n))) σ.out (by omega) (by omega)
    (by simp [encodeOutput]; omega) (by simp [encodeOutput]; omega)
    (by intro z hz; simp [encodeOutput,List.mem_ofFn] at hz; rcases hz with ⟨i,rfl⟩; omega) μ
    ⟨hp,by simp [μ,encodeOutput],by simpa [μ] using r1.out_eq (by simp [Fill.put,Com.NoWrite])⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by simp [Expr.size,encodeOutput]; omega),po⟩

end Lax263307Proofs.NativeEmptyOutput

end

section

namespace Lax263307Proofs.NativeQptasProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet

theorem zero_size_result {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (weights:Fin n→ ℚ) (ε:ℚ)
    (hzero:(∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v)=0):
    WeightedAlgorithm.solve lp flow a K b G weights ε=∅:=by
  let cs:=WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
  let I:=RecursiveAlgorithm.independentSet lp flow a K b (WeightedAlgorithm.numbered G cs) (ε/2)
  have hI:I=∅:=by
    ext v
    have hv:=v.isLt
    change v.val<∑ w,cs w at hv
    change (∑ w,cs w)=0 at hzero
    omega
  dsimp only [WeightedAlgorithm.solve]
  split_ifs
  · rfl
  · change PositiveWeights.discardNonpositive weights
      (IndependentBlowUp.project (I.image (WeightedAlgorithm.labeling cs)))=∅
    simp [hI,IndependentBlowUp.project,PositiveWeights.discardNonpositive]

end Lax263307Proofs.NativeQptasProgram

end

section

namespace Lax263307Proofs.NativeQptasZero

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax263307 WeightedIndependentSet NativeFrontend

theorem command_spec {n:ℕ} (B M:ℕ) (hM:1≤ M) (hn:n≤ M)
    (cfg:NativeCoreMachine.Config) (C d Q e:ℕ) (lp flow:List ℕ→ List ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (weights:Fin n→ ℚ) (ε:ℚ)
    (hεpos:0<ε) (hw:∀ v,(weights v).num.natAbs≤ M∧ (weights v).den≤ M)
    (hε:ε.num.natAbs≤ M∧ ε.den≤ M) (hB:2*M^4+3< B) (hsize:n*n+3*n+3< B)
    (hzero:(∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v)=0):
    Spec B (fun σ => σ.inp=encodeInput G weights ε∧ n*n+3*n+3≤(σ.arrs "input.data").length∧
      n≤(σ.arrs "copy.counts").length∧ (σ.arrs "weighted.output").length=n)
      (NativeQptasProgram.command cfg C d Q e)
      (fun σ τ => τ.out=σ.out++encodeOutput (WeightedAlgorithm.solve lp flow cfg.a cfg.K cfg.b G weights ε))
      (NativeBlowUp.cost n 0+24*n+20):=by
  have hz:(∑ v,WeightRounding.copies (fun v => max (weights v) 0) ε v)=0:=hzero
  rintro σ ⟨hinp,hinput,hcounts,houtput⟩
  obtain ⟨ν,r1,hmatrix,howner,hN,hdata,hout,horder⟩:=NativeBlowUp.prepare_spec B M hM hn G weights ε
    hεpos hw hε hB hsize (by rw [hz]; simp; omega) σ
    ⟨hinp,hinput,hcounts,by rw [hz]; omega,by rw [hz]; simp⟩
  have hN0:ν.vars "blowup.length"=0:=hN.trans hz
  let μ:=ν.setVar "graph.n" 0
  have r2:Run B NativeQptasProgram.order ν μ 2:=Run.assign (by
    rw [evalB_var_iff]; exact ⟨hN0.symm,hN0 ▸ (by omega)⟩)
  have hnμ:μ.vars "input.n"=n:=(r2.frame_var _ (by decide)).trans horder
  obtain ⟨τ,r3,post⟩:=NativeEmptyOutput.command_spec B n (by omega) μ
    ⟨hnμ,by rw [RamFrames.run_array_length (r1.seq r2)]; exact houtput⟩
  have htest:(Cond.eq (.var "graph.n") (.lit 0)).evalB B μ=some true:=
    evalB_condEq (show (Expr.var "graph.n").evalB B μ=some 0 from by
      rw [evalB_var_iff]; simp [μ]; omega) (evalB_lit (by omega:0< B))
  have run:Run B (NativeQptasProgram.command cfg C d Q e) σ τ _:=
    r1.seq (r2.seq (Run.ite_true htest r3))
  refine ⟨τ,run.mono (by rw [hz]; simp [Cond.size,Expr.size]; omega),?_⟩
  rw [NativeQptasProgram.zero_size_result lp flow cfg.a cfg.K cfg.b G weights ε hzero]
  change τ.out=σ.out++encodeOutput (∅:Finset (Fin n))
  rw [post,(r2.out_eq (by decide)).trans hout]

end Lax263307Proofs.NativeQptasZero

end

theorem solution:∀ {n:Nat} (B M:Nat),
  Nat.le ((1:Nat)) M→
    Nat.le n M→
      ∀ (cfg:Lax263307Proofs.NativeCoreMachine.Config) (C d Q e:Nat) (lp flow:List Nat→ List Nat)
        (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
        (weights:Fin n→ Rat) (ε:Rat),
        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
          (∀ (v:Fin n),
              And (Nat.le (weights v).num.natAbs M) (Nat.le (weights v).den M))→
            And (Nat.le ε.num.natAbs M) (Nat.le ε.den M)→
              Nat.lt
                  (Nat.add
                    (Nat.mul
                      ((2:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        M ((4:Nat))))
                    ((3:Nat)))
                  B→
                Nat.lt
                    (Nat.add
                      (Nat.add
                        (Nat.mul n n)
                        (Nat.mul
                          ((3:Nat)) n))
                      ((3:Nat)))
                    B→
                  @Eq Nat
                      (∑ v:Fin n,
                        @Lax263307.WeightRounding.copies n (@Lax263307.PositiveWeights.positiveWeights n weights) ε v)
                      ((0:Nat))→
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                          (And
                            (Nat.le
                              (Nat.add
                                (Nat.add
                                  (Nat.mul n n)
                                  (Nat.mul
                                    ((3:Nat)) n))
                                ((3:Nat)))
                              (@List.length Nat (σ.arrs "input.data")))
                            (And (Nat.le n (@List.length Nat (σ.arrs "copy.counts")))
                              (@Eq Nat (@List.length Nat (σ.arrs "weighted.output")) n))))
                      (Lax263307Proofs.NativeQptasProgram.command cfg C d Q e)
                      (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                        @Eq (List Nat) τ.out
                          (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                            (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                            (@Lax263307.IndependentSetEncoding.encodeOutput n
                              (@Lax263307.WeightedAlgorithm.solve n lp flow cfg.a cfg.K cfg.b G inst weights ε))))
                      (Nat.add
                        (Nat.add
                          (Lax263307Proofs.NativeBlowUp.cost n
                            ((0:Nat)))
                          (Nat.mul
                            ((24:Nat)) n))
                        ((20:Nat))):= @Lax263307Proofs.NativeQptasZero.command_spec
