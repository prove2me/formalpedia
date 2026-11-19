-- Prove2me | solution 1 for Lax455465Proofs.RamVirtualExecution.execute_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:27:13.347206+00:00
-- url     : https://prove2.me/submissions/e4b398d3-3316-4bb8-84c7-354b07e0019f

import Mathlib.Tactic
import Mathlib.Data.List.TakeDrop
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces

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

theorem Run.frame_arrs_eqOn {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.warrs=[]):σ'.arrs=σ.arrs:=
  funext fun a => h.frame_arr a (by simp [hc])

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

theorem eval_shiftl (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * 2 ^ n < B):
    (Expr.bin .shiftl e f).evalB B σ=some (m * 2 ^ n):=evalB_bin he hf h

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

namespace Lax455465Proofs.SparseRam

open Lax808846.Ram

theorem effect_memory_le (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs; simp [assign,write])
    | solve | (cases hi:s.inp.head? <;> (try simp only [hi,Option.map_some,Option.map_none] at hs) <;> cases hs <;> simp [assign,write])

theorem step_memory_le (w:ℕ) (p:Program) (s τ:SparseState)
    (hs:step w p s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  unfold step at hs
  cases hi:p[s.pc]? with
  | none => simp only [hi,Option.bind_none] at hs; cases hs
  | some i =>
    simp only [hi,Option.bind_some] at hs
    exact effect_memory_le w i s τ hs

def shiftValue (w value count:ℕ):ℕ:=
  if count < w then (value * 2 ^ count) % 2 ^ w else 0

theorem shiftValue_eq (w value count:ℕ):
    shiftValue w value count=(value * 2 ^ count) % 2 ^ w:=by
  unfold shiftValue
  split_ifs with h
  · rfl
  · have hc:count=w + (count - w):=by omega
    rw [hc,pow_add]
    simp only [Nat.mul_mod,Nat.mod_self,zero_mul,mul_zero,Nat.zero_mod]

end Lax455465Proofs.SparseRam

end

section

namespace Lax455465Proofs.RamSparseMemory

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def update (address old:ℕ) (record:ℕ × ℕ):ℕ:=if record.1=address then record.2 else old

def seen (records:List (ℕ × ℕ)) (address count:ℕ):ℕ:=
  (records.take count).foldl (update address) 0

theorem seen_zero (records:List (ℕ × ℕ)) (address:ℕ):seen records address 0=0:=rfl

theorem seen_step (records:List (ℕ × ℕ)) (address i:ℕ) (hi:i < records.length):
    seen records address (i + 1)=update address (seen records address i) records[i]:=by
  unfold seen
  rw [← List.take_concat_get' records i hi,List.foldl_append]
  rfl

theorem seen_reverse (m:SparseRam.Memory) (address:ℕ):
    seen m.reverse address m.length=SparseRam.lookup m address:=by
  unfold seen
  rw [← List.length_reverse,List.take_length]
  induction m with
  | nil => rfl
  | cons r rest ih =>
    rw [List.reverse_cons,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,update,SparseRam.lookup]
    by_cases he:r.1=address
    · rw [if_pos he,if_pos he.symm]
    · have hn:address ≠ r.1:=fun h => he h.symm
      rw [if_neg he,if_neg hn]

private theorem fold_bounded (records:List (ℕ × ℕ)) (address start B:ℕ)
    (hs:start < B) (hwords:∀ r∈ records,r.2 < B):
    records.foldl (update address) start < B:=by
  induction records generalizing start with
  | nil => exact hs
  | cons r rest ih =>
    apply ih
    · unfold update
      split_ifs
      · exact hwords r (List.mem_cons_self)
      · exact hs
    · exact fun r hr => hwords r (List.mem_cons_of_mem _ hr)

theorem seen_bounded (records:List (ℕ × ℕ)) (address i B:ℕ) (hB:0 < B)
    (hwords:∀ r∈ records,r.2 < B):seen records address i < B:=by
  exact fold_bounded _ address 0 B hB (fun r hr => hwords r (List.mem_of_mem_take hr))

def Inputs (records:List (ℕ × ℕ)) (address:ℕ) (σ:Env):Prop:=
  (∀ i (hi:i < records.length), (σ.arrs "vm.addresses")[i]?=some records[i].1∧
    (σ.arrs "vm.values")[i]?=some records[i].2)∧
    σ.vars "vm.count"=records.length∧ σ.vars "lookup.address"=address

theorem scanStep_spec (B:ℕ) (records:List (ℕ × ℕ)) (address i:ℕ)
    (h1:1 < B) (haddress:address < B) (hlen:records.length < B) (hi:i < records.length)
    (hwords:∀ r∈ records,r.1 < B∧ r.2 < B):
    Spec B (fun σ => Inputs records address σ∧ σ.vars "lookup.i"=i∧
        σ.vars "lookup.result"=seen records address i) scanStep
      (fun _ τ => Inputs records address τ∧ τ.vars "lookup.i"=i + 1∧
        τ.vars "lookup.result"=seen records address (i + 1)) 12:=by
  rintro σ ⟨⟨harrays,hcount,haddr⟩,hindex,hresult⟩
  have ha:=(hwords records[i] (List.getElem_mem hi)).1
  have hv:=(hwords records[i] (List.getElem_mem hi)).2
  have hgetA:=(harrays i hi).1
  have hgetV:=(harrays i hi).2
  have hlenA:i < (σ.arrs "vm.addresses").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetA
    cases hgetA
  have hlenV:i < (σ.arrs "vm.values").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetV
    cases hgetV
  (expose_names;
    (refine let c0:Nat:= @List.getD Nat (Env.arrs σ "vm.addresses") (Env.vars σ "lookup.i") ((0:Nat)); let c1:Prop:= @Eq Nat c0 (Env.vars σ "lookup.address"); let c2:Prop:=Not c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=c3 i ((1:Nat)); let c5:Nat:=seen records address c4; let c6:Env→ Prop:=(fun (x τ:Env) => And (Inputs records address τ) (And (@Eq Nat (Env.vars τ "lookup.i") c4) (@Eq Nat (Env.vars τ "lookup.result") c5))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B scanStep σ σ' ((12:Nat))) (c6 σ'); let c8:Nat:= @List.getD Nat (Env.arrs σ "vm.values") (Env.vars σ "lookup.i") ((0:Nat)); let c9:Env:=Env.setVar σ "lookup.result" c8; let c10:Nat:=Env.vars c9 "lookup.i"; let c11:Nat:=c3 c10 ((1:Nat)); let c12:Env:=Env.setVar c9 "lookup.i" c11; let c13:Nat→ Nat:=c3 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.get "vm.addresses" (Expr.var "lookup.i")) (Expr.var "lookup.address"); let c15:Nat→ Nat:=c3 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.get "vm.values" (Expr.var "lookup.i"))); let c17:Nat:=c15 c16; let c18:Expr:=Expr.add (Expr.var "lookup.i") (Expr.lit ((1:Nat))); let c19:Nat:=c13 (Expr.size c18); let c20:String→ Nat:=Env.vars c12; let c21:Nat:=c3 (Env.vars σ "lookup.i") ((1:Nat)); let c22:Env:=Env.setVar σ "lookup.i" c21; let c23:Nat:=c15 ((1:Nat)); let c24:String→ Nat:=Env.vars c22; @Or.casesOn c1 c2 (fun (x:Or c1 c2) => @Exists Env c7) (Classical.em c1) (fun (hcase:c1) => @Exists.intro Env c7 c12 (@And.intro (Run B scanStep σ c12 ((12:Nat))) (c6 c12) (RunStep.mono B scanStep σ c12 (c3 c17 c19) ((12:Nat)) (RunStep.seq B (Com.ite c14 (Com.assign "lookup.result" (Expr.get "vm.values" (Expr.var "lookup.i"))) Com.skip) (Com.assign "lookup.i" c18) σ c9 c12 c17 c19 (RunStep.ite_true B c14 (Com.assign "lookup.result" (Expr.get "vm.values" (Expr.var "lookup.i"))) Com.skip σ c9 c16 (RunStep.cond_eq_true B σ (Expr.get "vm.addresses" (Expr.var "lookup.i")) (Expr.var "lookup.address") c0 (Env.vars σ "lookup.address") (RunStep.eval_get B σ "vm.addresses" (Expr.var "lookup.i") (Env.vars σ "lookup.i") (RunStep.eval_var B σ "lookup.i" (?nAX_g5712_0_0_0)) (?nAX_g5712_0_0_1) ?_) (RunStep.eval_var B σ "lookup.address" (?nAX_g5712_0_0_2)) hcase) (RunStep.assign B σ "lookup.result" (Expr.get "vm.values" (Expr.var "lookup.i")) c8 (RunStep.eval_get B σ "vm.values" (Expr.var "lookup.i") (Env.vars σ "lookup.i") (RunStep.eval_var B σ "lookup.i" (?nAX_g5712_0_0_3)) (?nAX_g5712_0_0_4) ?_))) (RunStep.assign B c9 "lookup.i" c18 c11 (RunStep.eval_add B c9 (Expr.var "lookup.i") (Expr.lit ((1:Nat))) c10 ((1:Nat)) (RunStep.eval_var B c9 "lookup.i" (?nAX_g5712_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c9 h1) (?nAX_g5712_0_0_6)))) (?nAX_g5712_0_0_7)) ?_)) fun (hcase:c2) => @Exists.intro Env c7 c22 (@And.intro (Run B scanStep σ c22 ((12:Nat))) (c6 c22) (RunStep.mono B scanStep σ c22 (c3 c23 c19) ((12:Nat)) (RunStep.seq B (Com.ite c14 (Com.assign "lookup.result" (Expr.get "vm.values" (Expr.var "lookup.i"))) Com.skip) (Com.assign "lookup.i" c18) σ σ c22 c23 c19 (RunStep.ite_false B c14 (Com.assign "lookup.result" (Expr.get "vm.values" (Expr.var "lookup.i"))) Com.skip σ σ ((1:Nat)) (RunStep.cond_eq_false B σ (Expr.get "vm.addresses" (Expr.var "lookup.i")) (Expr.var "lookup.address") c0 (Env.vars σ "lookup.address") (RunStep.eval_get B σ "vm.addresses" (Expr.var "lookup.i") (Env.vars σ "lookup.i") (RunStep.eval_var B σ "lookup.i" (?nAX_g5712_0_0_8)) (?nAX_g5712_0_0_9) ?_) (RunStep.eval_var B σ "lookup.address" (?nAX_g5712_0_0_10)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "lookup.i" c18 c21 (RunStep.eval_add B σ (Expr.var "lookup.i") (Expr.lit ((1:Nat))) (Env.vars σ "lookup.i") ((1:Nat)) (RunStep.eval_var B σ "lookup.i" (?nAX_g5712_0_0_11)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5712_0_0_12)))) (?nAX_g5712_0_0_13)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5712_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5712_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Inputs,seen_step,update]

def Invariant (records:List (ℕ × ℕ)) (address:ℕ) (σ:Env):Prop:=
  Inputs records address σ∧ σ.vars "lookup.i" ≤ records.length∧
    σ.vars "lookup.result"=seen records address (σ.vars "lookup.i")

theorem lookup_spec (B:ℕ) (records:List (ℕ × ℕ)) (address:ℕ)
    (h1:1 < B) (haddress:address < B) (hlen:records.length < B)
    (hwords:∀ r∈ records,r.1 < B∧ r.2 < B):
    Spec B (Inputs records address) lookup
      (fun _ τ => Inputs records address τ∧ τ.vars "lookup.result"=seen records address records.length)
      (16 * records.length + 8):=by
  have hbody:Spec B (fun σ => Invariant records address σ∧ σ.vars "lookup.i" < records.length)
      scanStep (fun σ τ => Invariant records address τ∧ τ.vars "lookup.i"=σ.vars "lookup.i" + 1) 12:=by
    rintro σ ⟨⟨hinputs,hindex,hresult⟩,hi⟩
    obtain ⟨τ,hr,ht⟩:=scanStep_spec B records address (σ.vars "lookup.i") h1 haddress hlen hi hwords
      σ ⟨hinputs,rfl,hresult⟩
    refine ⟨τ,hr, ⟨ht.1, ?_, ?_⟩,ht.2.1⟩
    · rw [ht.2.1]
      omega
    · rw [ht.2.1]
      exact ht.2.2
  have hlo:=Spec.forRangeZero "lookup.i" "vm.count" (Invariant records address) records.length 12 hlen
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) hbody
  have hfinal:=hlo.post (fun _ τ _ h =>
    (show Inputs records address τ∧ τ.vars "lookup.result"=seen records address records.length from
      ⟨h.1.1,by simpa only [h.2] using h.1.2.2⟩))
  intro σ hσ
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "lookup.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "lookup.i") (Expr.var "vm.count")) scanStep); let c1:Env:=Env.setVar σ "lookup.result" ((0:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c3 (c4 (c3 ((12:Nat)) ((4:Nat))) (@List.length (Prod Nat Nat) records)) ((6:Nat)); let c6:Nat:=seen records address (@List.length (Prod Nat Nat) records); let c7:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (Inputs records address σ') (@Eq Nat (Env.vars σ' "lookup.result") c6)); let c8:Nat:=c3 (c4 ((16:Nat)) (@List.length (Prod Nat Nat) records)) ((8:Nat)); let c9:Env→ Env→ Prop:=fun (x τ:Env) => And (Inputs records address τ) (@Eq Nat (Env.vars τ "lookup.result") c6); let c10:Env→ Prop:=c9 σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B lookup σ σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => c12) (RunStep.use B (fun (σ_1:Env) => Invariant records address (Env.setVar σ_1 "lookup.i" ((0:Nat)))) c0 c9 c5 hfinal c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (Inputs records address w) (@Eq Nat (Env.vars w "lookup.result") c6))) => let c0_1:Prop:=And (Inputs records address w) (@Eq Nat (Env.vars w "lookup.result") c6); @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c12) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c11 w (@And.intro (Run B lookup σ w c8) (c10 w) (RunStep.mono B lookup σ w (c3 c13 c5) c8 (RunStep.seq B (Com.assign "lookup.result" (Expr.lit ((0:Nat)))) c0 σ c1 w c13 c5 (RunStep.assign B σ "lookup.result" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5715_0_0_0))) left) (?nAX_g5715_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5715_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5715_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [Invariant,Inputs,seen_zero]

theorem prefix_append (records:List (ℕ × ℕ)) (a v:ℕ) (σ:Env)
    (h:∀ i (hi:i < records.length),
      (σ.arrs "vm.addresses")[i]?=some records[i].1∧
      (σ.arrs "vm.values")[i]?=some records[i].2)
    (hA:records.length < (σ.arrs "vm.addresses").length)
    (hV:records.length < (σ.arrs "vm.values").length):
    ∀ i (hi:i < (records ++ [(a,v)]).length),
      ((σ.arrs "vm.addresses").set records.length a)[i]?=some (records ++ [(a,v)])[i].1∧
      ((σ.arrs "vm.values").set records.length v)[i]?=some (records ++ [(a,v)])[i].2:=by
  intro i hi
  by_cases hlt:i < records.length
  · rw [← List.getElem_append_left' hlt]
    have hne:records.length ≠ i:=by omega
    simpa only [List.getElem?_set_ne hne] using h i hlt
  · have he:i=records.length:=by
      simp only [List.length_append,List.length_singleton] at hi
      omega
    subst i
    simp only [List.getElem?_set_self hA,List.getElem?_set_self hV]
    simp

theorem put_spec (B:ℕ) (records:List (ℕ × ℕ)) (lookupAddress a v:ℕ)
    (h1:1 < B) (ha:a < B) (hv:v < B) (hlen:records.length + 1 < B):
    Spec B (fun σ => Inputs records lookupAddress σ∧ σ.vars "put.address"=a∧
      σ.vars "put.value"=v∧ records.length < (σ.arrs "vm.addresses").length∧
      records.length < (σ.arrs "vm.values").length) put
      (fun _ τ => Inputs (records ++ [(a,v)]) lookupAddress τ) 10:=by
  rintro σ ⟨⟨harrays,hcount,haddr⟩,hputA,hputV,hA,hV⟩
  have happend:=prefix_append records a v σ harrays hA hV
  (expose_names;
    (refine let c0:Env→ Prop:=Inputs (@HAppend.hAppend (List (Prod Nat Nat)) (List (Prod Nat Nat)) (List (Prod Nat Nat)) (@instHAppendOfAppend (List (Prod Nat Nat)) (@List.instAppend (Prod Nat Nat))) records (@List.cons (Prod Nat Nat) (@Prod.mk Nat Nat a v) (@List.nil (Prod Nat Nat)))) lookupAddress; let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setArr σ "vm.addresses" (Env.vars σ "vm.count") (Env.vars σ "put.address"); let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "vm.count"; let c5:Nat:=c3 "put.value"; let c6:Env:=Env.setArr c2 "vm.values" c4 c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c6 "vm.count"; let c9:Nat:=c7 c8 ((1:Nat)); let c10:Env:=Env.setVar c6 "vm.count" c9; let c11:Nat→ Nat:=c7 ((1:Nat)); let c12:Nat→ Nat:=c7 (c11 (Expr.size (Expr.var "vm.count"))); let c13:Nat:=c12 (Expr.size (Expr.var "put.address")); let c14:Nat:=c12 (Expr.size (Expr.var "put.value")); let c15:Expr:=Expr.add (Expr.var "vm.count") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Nat:=c7 c14 c16; let c18:Com:=Com.assign "vm.count" c15; @Exists.intro Env (fun (σ':Env) => And (Run B put σ σ' ((10:Nat))) (c1 σ')) c10 (@And.intro (Run B put σ c10 ((10:Nat))) (c1 c10) (RunStep.mono B put σ c10 (c7 c13 c17) ((10:Nat)) (RunStep.seq B (Com.store "vm.addresses" (Expr.var "vm.count") (Expr.var "put.address")) (Com.seq (Com.store "vm.values" (Expr.var "vm.count") (Expr.var "put.value")) c18) σ c2 c10 c13 c17 (RunStep.store B σ "vm.addresses" (Expr.var "vm.count") (Expr.var "put.address") (Env.vars σ "vm.count") (Env.vars σ "put.address") (RunStep.eval_var B σ "vm.count" (?nAX_g5718_0_0_0)) (RunStep.eval_var B σ "put.address" (?nAX_g5718_0_0_1)) (?nAX_g5718_0_0_2)) (RunStep.seq B (Com.store "vm.values" (Expr.var "vm.count") (Expr.var "put.value")) c18 c2 c6 c10 c14 c16 (RunStep.store B c2 "vm.values" (Expr.var "vm.count") (Expr.var "put.value") c4 c5 (RunStep.eval_var B c2 "vm.count" (?nAX_g5718_0_0_3)) (RunStep.eval_var B c2 "put.value" (?nAX_g5718_0_0_4)) (?nAX_g5718_0_0_5)) (RunStep.assign B c6 "vm.count" c15 c9 (RunStep.eval_add B c6 (Expr.var "vm.count") (Expr.lit ((1:Nat))) c8 ((1:Nat)) (RunStep.eval_var B c6 "vm.count" (?nAX_g5718_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c6 h1) (?nAX_g5718_0_0_7))))) (?nAX_g5718_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5718_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5718_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Inputs]

end Lax455465Proofs.RamSparseMemory

end

section

namespace Lax455465Proofs.RamWordOps

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem reduce_spec (B M value:ℕ) (hM:M < B) (hv:value < B):
    Spec B (fun σ => σ.vars "vm.result"=value∧ σ.vars "vm.modulus"=M) reduce
      (fun _ τ => τ.vars "vm.result"=value % M) 8:=by
  have hd:value / M < B:=(Nat.div_le_self _ _).trans_lt hv
  have hp:value / M * M < B:=(Nat.div_mul_le_self _ _).trans_lt hv
  have hr:value - value / M * M < B:=(Nat.sub_le _ _).trans_lt hv
  rintro σ ⟨hsvalue,hsM⟩
  (expose_names;
    (refine let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) value M; let c1:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") c0) σ; let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "vm.result") (Env.vars σ "vm.modulus"); let c3:Nat:=Nat.mul c2 (Env.vars σ "vm.modulus"); let c4:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "vm.result") c3; let c5:Env:=Env.setVar σ "vm.result" c4; let c6:Expr:=Expr.mul (Expr.div (Expr.var "vm.result") (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c7:Expr:=Expr.sub (Expr.var "vm.result") c6; @Exists.intro Env (fun (σ':Env) => And (Run B reduce σ σ' ((8:Nat))) (c1 σ')) c5 (@And.intro (Run B reduce σ c5 ((8:Nat))) (c1 c5) (RunStep.mono B reduce σ c5 (Nat.add ((1:Nat)) (Expr.size c7)) ((8:Nat)) (RunStep.assign B σ "vm.result" c7 c4 (RunStep.eval_sub B σ (Expr.var "vm.result") c6 (Env.vars σ "vm.result") c3 (RunStep.eval_var B σ "vm.result" (?nAX_g5720_0_0_0)) (RunStep.eval_mul B σ (Expr.div (Expr.var "vm.result") (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c2 (Env.vars σ "vm.modulus") (RunStep.eval_div B σ (Expr.var "vm.result") (Expr.var "vm.modulus") (Env.vars σ "vm.result") (Env.vars σ "vm.modulus") (RunStep.eval_var B σ "vm.result" (?nAX_g5720_0_0_1)) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5720_0_0_2)) ?_) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5720_0_0_3)) ?_) (?nAX_g5720_0_0_4))) (?nAX_g5720_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5720_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5720_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5720_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5720_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5720_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5720_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

theorem binary_spec (B M left right:ℕ) (op:Bop) (hM:M < B)
    (hl:left < B) (hr:right < B) (hop:op.apply left right < B):
    Spec B (fun σ => σ.vars "vm.modulus"=M∧ σ.vars "vm.left"=left∧
      σ.vars "vm.right"=right) (binary op)
      (fun _ τ => τ.vars "vm.result"=op.apply left right % M) 12:=by
  rintro σ ⟨hsM,hsl,hsr⟩
  have hassign:Run B (.assign "vm.result" (.bin op (.var "vm.left") (.var "vm.right")))
      σ (σ.setVar "vm.result" (op.apply left right)) 4:=
    Run.assign (evalB_bin (by simpa [hsl] using evalB_var (show σ.vars "vm.left" < B by omega))
      (by simpa [hsr] using evalB_var (show σ.vars "vm.right" < B by omega)) hop)
  obtain ⟨τ,hrun,hpost⟩:=reduce_spec B M (op.apply left right) hM hop
    (σ.setVar "vm.result" (op.apply left right)) (by simp [hsM])
  exact ⟨τ,hassign.seq hrun,hpost⟩

theorem shift_spec (B w left right:ℕ) (hB:2 * (2 ^ w) ^ 2 + 3 < B)
    (hl:left < 2 ^ w) (hr:right < 2 ^ w):
    Spec B (fun σ => σ.vars "vm.modulus"=2 ^ w∧ σ.vars "vm.width"=w∧
      σ.vars "vm.left"=left∧ σ.vars "vm.right"=right) shift
      (fun _ τ => τ.vars "vm.result"=SparseRam.shiftValue w left right) 16:=by
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have hw:w < B:=(Nat.lt_two_pow_self).trans hM
  have hlB:=hl.trans hM
  have hrB:=hr.trans hM
  have hzero:0 < B:=by omega
  have hsafe:right < w→ Bop.shiftl.apply left right < B:=by
    intro h
    have hp:2 ^ right≤ 2 ^ w:=Nat.pow_le_pow_right (by decide) h.le
    have hmul:left * 2 ^ right≤ (2 ^ w) ^ 2:=by nlinarith
    exact hmul.trans_lt (by nlinarith)
  have hbranch:Spec B (fun σ => σ.vars "vm.modulus"=2 ^ w∧
      σ.vars "vm.left"=left∧ σ.vars "vm.right"=right∧ right < w)
      (binary .shiftl) (fun _ τ => τ.vars "vm.result"=left * 2 ^ right % 2 ^ w) 12:=by
    rintro σ ⟨hsM,hsl,hsr,h⟩
    exact binary_spec B (2 ^ w) left right .shiftl hM hlB hrB (hsafe h) σ ⟨hsM,hsl,hsr⟩
  rintro σ ⟨hsM,hsw,hsl,hsr⟩
  (expose_names;
    (refine let c0:Prop:=Nat.lt (Env.vars σ "vm.right") (Env.vars σ "vm.width"); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") (SparseRam.shiftValue w left right)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B shift σ σ' ((16:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)); let c6:Nat:=c5 w; let c7:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) (Nat.mul left (c5 right)) c6; let c8:Env→ Prop:=fun (σ':Env) => And (Run B (binary Bop.shiftl) σ σ' ((12:Nat))) (@Eq Nat (Env.vars σ' "vm.result") c7); let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat→ Nat:=c9 (c10 (Cond.size (Cond.lt (Expr.var "vm.right") (Expr.var "vm.width")))); let c12:Com:=Com.assign "vm.result" (Expr.lit ((0:Nat))); let c13:Env:=Env.setVar σ "vm.result" ((0:Nat)); let c14:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c4) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "vm.modulus") c6) (And (@Eq Nat (Env.vars σ_1 "vm.left") left) (And (@Eq Nat (Env.vars σ_1 "vm.right") right) (Nat.lt right w)))) (binary Bop.shiftl) (fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") c7) ((12:Nat)) hbranch σ ?_) fun (w_1:Env) (h:And (Run B (binary Bop.shiftl) σ w_1 ((12:Nat))) (@Eq Nat (Env.vars w_1 "vm.result") c7)) => let c0_1:Prop:=Run B (binary Bop.shiftl) σ w_1 ((12:Nat)); @And.casesOn c0_1 (@Eq Nat (Env.vars w_1 "vm.result") c7) (fun (x:And c0_1 (@Eq Nat (Env.vars w_1 "vm.result") c7)) => c4) h fun (left_1:c0_1) (right_1:@Eq Nat (Env.vars w_1 "vm.result") c7) => @Exists.intro Env c3 w_1 (@And.intro (Run B shift σ w_1 ((16:Nat))) (c2 w_1) (RunStep.mono B shift σ w_1 (c11 ((12:Nat))) ((16:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "vm.right") (Expr.var "vm.width")) (binary Bop.shiftl) c12 σ w_1 ((12:Nat)) (RunStep.cond_lt_true B σ (Expr.var "vm.right") (Expr.var "vm.width") (Env.vars σ "vm.right") (Env.vars σ "vm.width") (RunStep.eval_var B σ "vm.right" (?nAX_g5724_0_0_0)) (RunStep.eval_var B σ "vm.width" (?nAX_g5724_0_0_1)) hcase) left_1) (?nAX_g5724_0_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c3 c13 (@And.intro (Run B shift σ c13 ((16:Nat))) (c2 c13) (RunStep.mono B shift σ c13 (c11 c14) ((16:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "vm.right") (Expr.var "vm.width")) (binary Bop.shiftl) c12 σ c13 c14 (RunStep.cond_lt_false B σ (Expr.var "vm.right") (Expr.var "vm.width") (Env.vars σ "vm.right") (Env.vars σ "vm.width") (RunStep.eval_var B σ "vm.right" (?nAX_g5724_0_0_3)) (RunStep.eval_var B σ "vm.width" (?nAX_g5724_0_0_4)) hcase) (RunStep.assign B σ "vm.result" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero))) (?nAX_g5724_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5724_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5724_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5724_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5724_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5724_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5724_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_1))
  all_goals simp_all [SparseRam.shiftValue]

theorem complement_spec (B w left:ℕ) (hB:2 ^ w < B) (hl:left < 2 ^ w):
    Spec B (fun σ => σ.vars "vm.modulus"=2 ^ w∧ σ.vars "vm.left"=left) complement
      (fun _ τ => τ.vars "vm.result"=2 ^ w - 1 - left) 6:=by
  have h1:1 < B:=by have:=Nat.two_pow_pos w; omega
  have hlB:=hl.trans hB
  have hmask:2 ^ w - 1 < B:=(Nat.sub_le _ _).trans_lt hB
  have hresult:2 ^ w - 1 - left < B:=(Nat.sub_le _ _).trans_lt hmask
  rintro σ ⟨hsM,hsl⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c1:Nat:=c0 (c0 (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w) ((1:Nat))) left; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") c1) σ; let c3:Nat:=c0 (Env.vars σ "vm.modulus") ((1:Nat)); let c4:Nat:=c0 c3 (Env.vars σ "vm.left"); let c5:Env:=Env.setVar σ "vm.result" c4; let c6:Expr:=Expr.sub (Expr.var "vm.modulus") (Expr.lit ((1:Nat))); let c7:Expr:=Expr.sub c6 (Expr.var "vm.left"); @Exists.intro Env (fun (σ':Env) => And (Run B complement σ σ' ((6:Nat))) (c2 σ')) c5 (@And.intro (Run B complement σ c5 ((6:Nat))) (c2 c5) (RunStep.mono B complement σ c5 (Nat.add ((1:Nat)) (Expr.size c7)) ((6:Nat)) (RunStep.assign B σ "vm.result" c7 c4 (RunStep.eval_sub B σ c6 (Expr.var "vm.left") c3 (Env.vars σ "vm.left") (RunStep.eval_sub B σ (Expr.var "vm.modulus") (Expr.lit ((1:Nat))) (Env.vars σ "vm.modulus") ((1:Nat)) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5726_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5726_0_0_1)) (RunStep.eval_var B σ "vm.left" (?nAX_g5726_0_0_2)) (?nAX_g5726_0_0_3))) (?nAX_g5726_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5726_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5726_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5726_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5726_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5726_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem basic_bounds (w left right:ℕ) (hl:left < 2 ^ w) (hr:right < 2 ^ w):
    left + right < 2 * (2 ^ w) ^ 2 + 3∧
    left - right < 2 * (2 ^ w) ^ 2 + 3∧
    left * right < 2 * (2 ^ w) ^ 2 + 3∧
    left / right < 2 * (2 ^ w) ^ 2 + 3∧
    Nat.land left right < 2 * (2 ^ w) ^ 2 + 3:=by
  have hM:=Nat.two_pow_pos w
  have hlimit:2 ^ w < 2 * (2 ^ w) ^ 2 + 3:=by nlinarith
  have hl':=hl.trans hlimit
  have hsub:=(Nat.sub_le left right).trans_lt hl'
  have hdiv:=(Nat.div_le_self left right).trans_lt hl'
  have hand:Nat.land left right≤ left:=Nat.and_le_left
  have hmul:left * right≤ (2 ^ w) ^ 2:=by nlinarith
  exact ⟨by nlinarith,hsub,by nlinarith,hdiv,hand.trans_lt hl'⟩

theorem modulus_spec (B w:ℕ) (hB:2 ^ w < B):
    Spec B (fun σ => σ.vars "vm.width"=w) modulus
      (fun _ τ => τ.vars "vm.modulus"=2 ^ w) 4:=by
  have h1:1 < B:=by have:=Nat.two_pow_pos w; omega
  have hw:w < B:=Nat.lt_two_pow_self.trans hB
  rintro σ hσ
  (expose_names;
    (refine let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)); let c1:Nat:=c0 w; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.modulus") c1) σ; let c3:Nat:=Nat.mul ((1:Nat)) (c0 (Env.vars σ "vm.width")); let c4:Env:=Env.setVar σ "vm.modulus" c3; let c5:Expr:=Expr.shiftl (Expr.lit ((1:Nat))) (Expr.var "vm.width"); @Exists.intro Env (fun (σ':Env) => And (Run B modulus σ σ' ((4:Nat))) (c2 σ')) c4 (@And.intro (Run B modulus σ c4 ((4:Nat))) (c2 c4) (RunStep.mono B modulus σ c4 (Nat.add ((1:Nat)) (Expr.size c5)) ((4:Nat)) (RunStep.assign B σ "vm.modulus" c5 c3 (RunStep.eval_shiftl B σ (Expr.lit ((1:Nat))) (Expr.var "vm.width") ((1:Nat)) (Env.vars σ "vm.width") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "vm.width" (?nAX_g5729_0_0_0)) ?_)) (?nAX_g5729_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5729_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5729_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

end Lax455465Proofs.RamWordOps

end

section

namespace Lax455465Proofs.RamSparseRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSparseMemory

theorem read_spec (B:ℕ) (records:List (ℕ × ℕ)) (a:ℕ) (target:String) (e:Expr)
    (h1:1 < B) (ha:a < B) (hlen:records.length < B)
    (hwords:∀ r∈ records,r.1 < B∧ r.2 < B) (htarget:target ≠ "vm.count"):
    Spec B (fun σ => _root_.Lax455465Proofs.RamSparseRead.Representation records σ∧ e.evalB B σ=some a) (read target e)
      (fun _ τ => _root_.Lax455465Proofs.RamSparseRead.Representation records τ∧ τ.vars target=seen records a records.length)
      (16 * records.length + e.size + 11):=by
  rintro σ ⟨⟨harrays,hcount⟩,he⟩
  have hstart:Run B (.assign "lookup.address" e) σ (σ.setVar "lookup.address" a)
      (1 + e.size):=Run.assign he
  have hinputs:Inputs records a (σ.setVar "lookup.address" a):=by
    simp only [Inputs,arrs_setVar,vars_setVar]
    exact ⟨harrays,by simpa using hcount,by simp⟩
  obtain ⟨ν,hlookup,hpost⟩:=lookup_spec B records a h1 ha hlen hwords _ hinputs
  have hbound:ν.vars "lookup.result" < B:=by
    rw [hpost.2]
    exact seen_bounded records a records.length B (by omega) (fun r hr => (hwords r hr).2)
  have hfinish:Run B (.assign target (.var "lookup.result")) ν
      (ν.setVar target (ν.vars "lookup.result")) 2:=Run.assign (evalB_var hbound)
  refine ⟨ν.setVar target (ν.vars "lookup.result"), (hstart.seq (hlookup.seq hfinish)).mono ?_, ?_⟩
  · omega
  · rcases hpost.1 with ⟨harrays',hcount',_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [arrs_setVar] using harrays'
    · simpa only [vars_setVar,if_neg (Ne.symm htarget)] using hcount'
    · simp only [vars_setVar]
      exact hpost.2

theorem read_sparse_spec (B:ℕ) (m:SparseRam.Memory) (a:ℕ) (target:String) (e:Expr)
    (h1:1 < B) (ha:a < B) (hlen:m.length < B)
    (hwords:∀ r∈ m,r.1 < B∧ r.2 < B) (htarget:target ≠ "vm.count"):
    Spec B (fun σ => _root_.Lax455465Proofs.RamSparseRead.Representation m.reverse σ∧ e.evalB B σ=some a) (read target e)
      (fun _ τ => _root_.Lax455465Proofs.RamSparseRead.Representation m.reverse τ∧ τ.vars target=SparseRam.lookup m a)
      (16 * m.length + e.size + 11):=by
  have h:=read_spec B m.reverse a target e h1 ha (by simpa using hlen)
    (fun r hr => hwords r (List.mem_reverse.mp hr)) htarget
  simpa only [List.length_reverse,seen_reverse] using h

theorem write_spec (B:ℕ) (records:List (ℕ × ℕ)) (a v:ℕ)
    (h1:1 < B) (ha:a < B) (hv:v < B) (hlen:records.length + 1 < B):
    Spec B (fun σ => _root_.Lax455465Proofs.RamSparseRead.Representation records σ∧ σ.vars "vm.target"=a∧
      σ.vars "vm.result"=v∧ records.length < (σ.arrs "vm.addresses").length∧
      records.length < (σ.arrs "vm.values").length) write
      (fun _ τ => _root_.Lax455465Proofs.RamSparseRead.Representation (records ++ [(a,v)]) τ) 14:=by
  have hput:Spec B (fun σ => _root_.Lax455465Proofs.RamSparseRead.Representation records σ∧ σ.vars "put.address"=a∧
      σ.vars "put.value"=v∧ records.length < (σ.arrs "vm.addresses").length∧
      records.length < (σ.arrs "vm.values").length) put
      (fun _ τ => _root_.Lax455465Proofs.RamSparseRead.Representation (records ++ [(a,v)]) τ) 10:=by
    rintro σ ⟨⟨harrays,hcount⟩,hsa,hsv,hA,hV⟩
    obtain ⟨τ,hrun,hpost⟩:=put_spec B records (σ.vars "lookup.address") a v h1 ha hv hlen
      σ ⟨⟨harrays,hcount,rfl⟩,hsa,hsv,hA,hV⟩
    exact ⟨τ,hrun,hpost.1,hpost.2.1⟩
  rintro σ ⟨⟨harrays,hcount⟩,hsa,hsv,hA,hV⟩
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "put.address" (Env.vars σ "vm.target")) "vm.result"; let c1:Env:=Env.setVar (Env.setVar σ "put.address" (Env.vars σ "vm.target")) "put.value" c0; let c2:Env→ Nat→ Prop:=Run B put c1; let c3:Env→ Prop:=_root_.Lax455465Proofs.RamSparseRead.Representation (@HAppend.hAppend (List (Prod Nat Nat)) (List (Prod Nat Nat)) (List (Prod Nat Nat)) (@instHAppendOfAppend (List (Prod Nat Nat)) (@List.instAppend (Prod Nat Nat))) records (@List.cons (Prod Nat Nat) (@Prod.mk Nat Nat a v) (@List.nil (Prod Nat Nat)))); let c4:Env→ Prop:=fun (σ':Env) => And (c2 σ' ((10:Nat))) (c3 σ'); let c5:Env→ Env→ Prop:=fun (x τ:Env) => c3 τ; let c6:Env→ Prop:=c5 σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B write σ σ' ((14:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) records); let c10:String→ Nat:=Env.vars c1; let c11:String→ List Nat:=Env.arrs c1; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat:=c13 (Expr.size (Expr.var "vm.target")); let c15:Nat:=c13 (Expr.size (Expr.var "vm.result")); let c16:Nat:=c12 c15 ((10:Nat)); @Exists.casesOn Env c4 (fun (x:@Exists Env c4) => c8) (RunStep.use B (fun (σ_1:Env) => And (_root_.Lax455465Proofs.RamSparseRead.Representation records σ_1) (And (@Eq Nat (Env.vars σ_1 "put.address") a) (And (@Eq Nat (Env.vars σ_1 "put.value") v) (And (c9 (@List.length Nat (Env.arrs σ_1 "vm.addresses"))) (c9 (@List.length Nat (Env.arrs σ_1 "vm.values"))))))) put c5 ((10:Nat)) hput c1 ?_) fun (w:Env) (h:And (c2 w ((10:Nat))) (c3 w)) => let c0_1:Prop:=c2 w ((10:Nat)); @And.casesOn c0_1 (c3 w) (fun (x:And c0_1 (c3 w)) => c8) h fun (left:c0_1) (right:c3 w) => @Exists.intro Env c7 w (@And.intro (Run B write σ w ((14:Nat))) (c6 w) (RunStep.mono B write σ w (c12 c14 c16) ((14:Nat)) (RunStep.seq B (Com.assign "put.address" (Expr.var "vm.target")) (Com.seq (Com.assign "put.value" (Expr.var "vm.result")) put) σ (Env.setVar σ "put.address" (Env.vars σ "vm.target")) w c14 c16 (RunStep.assign B σ "put.address" (Expr.var "vm.target") (Env.vars σ "vm.target") (RunStep.eval_var B σ "vm.target" (?nAX_g5735_0_0_0))) (RunStep.seq B (Com.assign "put.value" (Expr.var "vm.result")) put (Env.setVar σ "put.address" (Env.vars σ "vm.target")) c1 w c15 ((10:Nat)) (RunStep.assign B (Env.setVar σ "put.address" (Env.vars σ "vm.target")) "put.value" (Expr.var "vm.result") c0 (RunStep.eval_var B (Env.setVar σ "put.address" (Env.vars σ "vm.target")) "vm.result" (?nAX_g5735_0_0_1))) left)) (?nAX_g5735_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5735_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5735_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5735_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [_root_.Lax455465Proofs.RamSparseRead.Representation]

theorem write_sparse_spec (B w:ℕ) (m:SparseRam.Memory) (a v:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < 2 ^ w) (hv:v < 2 ^ w)
    (hlen:m.length + 1 < B):
    Spec B (fun σ => _root_.Lax455465Proofs.RamSparseRead.Representation m.reverse σ∧ σ.vars "vm.target"=a∧
      σ.vars "vm.result"=v∧ m.length < (σ.arrs "vm.addresses").length∧
      m.length < (σ.arrs "vm.values").length) write
      (fun _ τ => _root_.Lax455465Proofs.RamSparseRead.Representation (SparseRam.write w m a v).reverse τ) 14:=by
  have h:=write_spec B m.reverse a v h1 (ha.trans hM) (hv.trans hM) (by simpa using hlen)
  simpa only [List.length_reverse,SparseRam.write,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hv,
    List.reverse_cons] using h

end Lax455465Proofs.RamSparseRead

end

section

namespace Lax455465Proofs.RamVirtualProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem evalB_remainder {B M value:ℕ} {σ:Env} {e:Expr}
    (he:e.evalB B σ=some value) (hM:σ.vars "vm.modulus"=M)
    (hMB:M < B) (hv:value < B):
    (remainder e).evalB B σ=some (value % M):=by
  have hmod:(Expr.var "vm.modulus").evalB B σ=some M:=by
    rw [evalB_var_iff]
    exact ⟨hM.symm,hM ▸ hMB⟩
  have hd:=(Nat.div_le_self value M).trans_lt hv
  have hp:=(Nat.div_mul_le_self value M).trans_lt hv
  have hs:=(Nat.sub_le value (value / M * M)).trans_lt hv
  have hdiv:=evalB_bin (op:=.div) he hmod hd
  have hmul:=evalB_bin (op:=.mul) hdiv hmod hp
  have hsub:=evalB_bin (op:=.sub) he hmul hs
  change (remainder e).evalB B σ=some (value - value / M * M) at hsub
  simpa only [Nat.mod_def,Nat.mul_comm] using hsub

end Lax455465Proofs.RamVirtualProgram

end

section

namespace Lax455465Proofs.SparseBounds

open Lax808846.Ram SparseRam

def MemoryWords (w:ℕ) (m:Memory):Prop:= ∀ r∈ m,r.1 < 2 ^ w∧ r.2 < 2 ^ w

theorem lookup_bound (w:ℕ) (m:Memory) (a:ℕ) (h:MemoryWords w m):
    lookup m a < 2 ^ w:=by
  induction m with
  | nil => exact Nat.two_pow_pos w
  | cons r rest ih =>
    unfold lookup
    split_ifs
    · exact (h r List.mem_cons_self).2
    · exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem write_words (w:ℕ) (m:Memory) (a v:ℕ) (h:MemoryWords w m):
    MemoryWords w (write w m a v):=by
  intro r hr
  rcases List.mem_cons.mp hr with he | ht
  · subst r
    exact ⟨Nat.mod_lt _ (Nat.two_pow_pos w),Nat.mod_lt _ (Nat.two_pow_pos w)⟩
  · exact h r ht

theorem effect_words (w:ℕ) (i:Instr) (s τ:SparseState)
    (hwords:MemoryWords w s.memory) (hs:effect w i s=some τ):MemoryWords w τ.memory:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> exact write_words _ _ _ _ hwords)
    | solve | (cases hs <;> exact hwords)
    | solve | (cases hi:s.inp.head? <;>
      (try simp only [hi,Option.map_some,Option.map_none] at hs) <;>
      cases hs <;> exact write_words _ _ _ _ hwords)

theorem effect_output_le (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.out.length≤ s.out.length + 1:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> simp [assign])
    | solve | (cases hi:s.inp.head? <;>
      (try simp only [hi,Option.map_some,Option.map_none] at hs) <;>
      cases hs <;> simp [assign])

theorem effect_input_eq (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.input=s.input:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs <;> rfl)
    | solve | (cases hi:s.inp.head? <;>
      (try simp only [hi,Option.map_some,Option.map_none] at hs) <;>
      cases hs <;> rfl)

theorem step_words (w:ℕ) (p:Program) (s τ:SparseState)
    (hwords:MemoryWords w s.memory) (hs:step w p s=some τ):MemoryWords w τ.memory:=by
  obtain ⟨i,_,he⟩:=Option.bind_eq_some_iff.mp hs
  exact effect_words w i s τ hwords he

theorem step_output_le (w:ℕ) (p:Program) (s τ:SparseState)
    (hs:step w p s=some τ):τ.out.length≤ s.out.length + 1:=by
  obtain ⟨i,_,he⟩:=Option.bind_eq_some_iff.mp hs
  exact effect_output_le w i s τ he

end Lax455465Proofs.SparseBounds

end

section

namespace Lax455465Proofs.RamVirtualCore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualProgram RamSparseRead

theorem read_expression_spec (B w pc:ℕ) (m:SparseRam.Memory) (a:ℕ) (target:String) (e:Expr)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hlen:m.length < B)
    (hwords:SparseBounds.MemoryWords w m)
    (htarget:target ≠ "vm.count") (hpc:target ≠ "vm.pc")
    (hmodulus:target ≠ "vm.modulus") (hwidth:target ≠ "vm.width"):
    Spec B (fun σ => Core w pc m σ∧ e.evalB B σ=some a) (RamSparseRead.read target e)
      (fun _ τ => Core w pc m τ∧ τ.vars target=SparseRam.lookup m a)
      (16 * m.length + e.size + 11):=by
  rintro σ ⟨⟨hrep,hσpc,hσmod,hσwidth⟩,he⟩
  obtain ⟨τ,hrun,hpost⟩:=read_sparse_spec B m a target e h1 ha hlen
    (fun r hr => ⟨(hwords r hr).1.trans hM, (hwords r hr).2.trans hM⟩) htarget σ ⟨hrep,he⟩
  have hpc':=hrun.frame_var "vm.pc" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hpc])
  have hmod':=hrun.frame_var "vm.modulus" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hmodulus])
  have hwidth':=hrun.frame_var "vm.width" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hwidth])
  exact ⟨τ,hrun, ⟨hpost.1,hpc'.trans hσpc,hmod'.trans hσmod,hwidth'.trans hσwidth⟩,hpost.2⟩

theorem read_literal_spec (B w pc:ℕ) (m:SparseRam.Memory) (a:ℕ) (target:String)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hlen:m.length < B)
    (hwords:SparseBounds.MemoryWords w m)
    (htarget:target ≠ "vm.count") (hpc:target ≠ "vm.pc")
    (hmodulus:target ≠ "vm.modulus") (hwidth:target ≠ "vm.width"):
    Spec B (Core w pc m) (RamSparseRead.read target (remainder (.lit a)))
      (fun _ τ => Core w pc m τ∧ τ.vars target=SparseRam.lookup m (a % 2 ^ w))
      (16 * m.length + 18):=by
  rintro σ ⟨hrep,hσpc,hσmod,hσwidth⟩
  have he:=evalB_remainder (evalB_lit ha) hσmod hM ha
  obtain ⟨τ,hrun,hpost⟩:=read_sparse_spec B m (a % 2 ^ w) target (remainder (.lit a)) h1
    ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) hlen
    (fun r hr => ⟨(hwords r hr).1.trans hM, (hwords r hr).2.trans hM⟩) htarget σ ⟨hrep,he⟩
  have hpc':=hrun.frame_var "vm.pc" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hpc])
  have hmod':=hrun.frame_var "vm.modulus" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hmodulus])
  have hwidth':=hrun.frame_var "vm.width" (by simp [RamSparseRead.read,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,Com.wvars,Ne.symm hwidth])
  exact ⟨τ,hrun, ⟨hpost.1,hpc'.trans hσpc,hmod'.trans hσmod,hwidth'.trans hσwidth⟩,hpost.2⟩

theorem write_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a value:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < 2 ^ w) (hv:value < 2 ^ w)
    (hlen:m.length + 1 < B):
    Spec B (fun σ => Core w pc m σ∧ σ.vars "vm.target"=a∧
      σ.vars "vm.result"=value∧ m.length < (σ.arrs "vm.addresses").length∧
      m.length < (σ.arrs "vm.values").length) RamSparseRead.write
      (fun _ τ => Core w pc (SparseRam.write w m a value) τ) 14:=by
  rintro σ ⟨⟨hrep,hspc,hsmod,hsw⟩,htarget,hvalue,hA,hV⟩
  obtain ⟨τ,hr,ht⟩:=write_sparse_spec B w m a value h1 hM ha hv hlen
    σ ⟨hrep,htarget,hvalue,hA,hV⟩
  exact ⟨τ,hr,ht, (hr.frame_var "vm.pc" (by decide)).trans hspc,
    (hr.frame_var "vm.modulus" (by decide)).trans hsmod,
    (hr.frame_var "vm.width" (by decide)).trans hsw⟩

theorem writeBack_general_spec (B w pc:ℕ) (m:SparseRam.Memory) (a value:ℕ)
    (targetExpr valueExpr:Expr) (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hv:value < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Core w pc m σ∧ m.length < (σ.arrs "vm.addresses").length∧
      m.length < (σ.arrs "vm.values").length∧ targetExpr.evalB B σ=some a∧
      valueExpr.evalB B (σ.setVar "vm.target" (a % 2 ^ w))=some value)
      (writeBack targetExpr valueExpr)
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ)
      (2 * targetExpr.size + 2 * valueExpr.size + 30):=by
  rintro σ ⟨hcore,hA,hV,htarget,hvalue⟩
  have hmσ:=hcore.2.2.1
  have ht:=evalB_remainder htarget hmσ hM ha
  have hmν:(σ.setVar "vm.target" (a % 2 ^ w)).vars "vm.modulus"=2 ^ w:=by simpa using hmσ
  have hv':=evalB_remainder hvalue hmν hM hv
  have hfirst:=Run.assign (x:= "vm.target") ht
  have hsecond:=Run.assign (x:= "vm.result") hv'
  have hpre:Core w pc m ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w))∧
      ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).vars "vm.target"=a % 2 ^ w∧
      ((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).vars "vm.result"=value % 2 ^ w∧
      m.length < (((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).arrs "vm.addresses").length∧
      m.length < (((σ.setVar "vm.target" (a % 2 ^ w)).setVar "vm.result" (value % 2 ^ w)).arrs "vm.values").length:=by
    simpa only [Core,RamSparseRead.Representation,arrs_setVar,vars_setVar,
      String.reduceEq,if_true,if_false,true_and] using And.intro hcore (And.intro hA hV)
  obtain ⟨τ,hwrite,hpost⟩:=write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w)
    h1 hM (Nat.mod_lt _ (Nat.two_pow_pos w)) (Nat.mod_lt _ (Nat.two_pow_pos w)) hlen _ hpre
  have hwrites:SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w)=SparseRam.write w m a value:=by
    simp only [SparseRam.write,Nat.mod_mod]
  rw [hwrites] at hpost
  have hinc:Run B increment τ (τ.setVar "vm.pc" (pc + 1)) 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hpost.2.1.symm,by rw [hpost.2.1]; omega⟩)
      (evalB_lit h1) hpc)
  refine ⟨τ.setVar "vm.pc" (pc + 1), (hfirst.seq (hsecond.seq (hwrite.seq hinc))).mono ?_, ?_⟩
  · simp only [remainder,Expr.size]
    omega
  · simpa only [Core,RamSparseRead.Representation,arrs_setVar,vars_setVar,
      String.reduceEq,if_true,if_false,true_and] using And.intro hpost.1 hpost.2.2

theorem set_spec (B w pc:ℕ) (m:SparseRam.Memory) (a value:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hv:value < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Core w pc m σ∧ m.length < (σ.arrs "vm.addresses").length∧
      m.length < (σ.arrs "vm.values").length) (instruction (.set a value))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) 40:=by
  have ham:=Nat.mod_lt a (Nat.two_pow_pos w)
  have hvm:=Nat.mod_lt value (Nat.two_pow_pos w)
  have hwrite:=write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w) h1 hM ham hvm hlen
  have hwrites:SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w)=SparseRam.write w m a value:=by
    simp only [SparseRam.write,Nat.mod_mod]
  rw [hwrites] at hwrite
  rintro σ ⟨⟨hrep,hσpc,hσmod,hσwidth⟩,hA,hV⟩
  have had:a / 2 ^ w < B:=(Nat.div_le_self _ _).trans_lt ha
  have hap:a / 2 ^ w * 2 ^ w < B:=(Nat.div_mul_le_self _ _).trans_lt ha
  have has:a - a / 2 ^ w * 2 ^ w < B:=(Nat.sub_le _ _).trans_lt ha
  have hvd:value / 2 ^ w < B:=(Nat.div_le_self _ _).trans_lt hv
  have hvp:value / 2 ^ w * 2 ^ w < B:=(Nat.div_mul_le_self _ _).trans_lt hv
  have hvs:value - value / 2 ^ w * 2 ^ w < B:=(Nat.sub_le _ _).trans_lt hv
  simp only [instruction,writeBack,remainder,increment]
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c3:Nat:=c2 a (Env.vars σ "vm.modulus"); let c4:Nat:=c1 c3 (Env.vars σ "vm.modulus"); let c5:Nat:=c0 a c4; let c6:Env:=Env.setVar σ "vm.target" c5; let c7:Nat:=Env.vars c6 "vm.modulus"; let c8:Nat:=c2 value c7; let c9:Nat:=c1 c8 c7; let c10:Nat:=c0 value c9; let c11:Env:=Env.setVar c6 "vm.result" c10; let c12:Env→ Nat→ Prop:=Run B write c11; let c13:Env→ Prop:=Core w pc (SparseRam.write w m a value); let c14:Env→ Prop:=fun (σ':Env) => And (c12 σ' ((14:Nat))) (c13 σ'); let c15:Expr:=Expr.mul (Expr.div (Expr.lit a) (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c16:Expr:=Expr.sub (Expr.lit a) c15; let c17:Com:=Com.assign "vm.target" c16; let c18:Expr:=Expr.mul (Expr.div (Expr.lit value) (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c19:Expr:=Expr.sub (Expr.lit value) c18; let c20:Com:=Com.assign "vm.result" c19; let c21:Expr:=Expr.add (Expr.var "vm.pc") (Expr.lit ((1:Nat))); let c22:Com:=Com.assign "vm.pc" c21; let c23:Com:=Com.seq write c22; let c24:Com:=Com.seq c20 c23; let c25:Com:=Com.seq c17 c24; let c26:Env→ Nat→ Prop:=Run B c25 σ; let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Env→ Prop:=Core w (c27 pc ((1:Nat))) (SparseRam.write w m a value); let c29:Env→ Prop:=fun (σ':Env) => And (c26 σ' ((40:Nat))) (c28 σ'); let c30:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c31:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w; let c32:Nat:=c30 a c31; let c33:Nat:=c30 value c31; let c34:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c35:String→ Nat:=Env.vars c11; let c36:String→ List Nat:=Env.arrs c11; let c37:Nat→ Nat:=c27 ((1:Nat)); let c38:Nat:=c37 (Expr.size c16); let c39:Nat:=c37 (Expr.size c19); let c40:Nat:=c37 (Expr.size c21); let c41:Nat:=c27 ((14:Nat)) c40; let c42:Nat:=c27 c39 c41; @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => @Exists Env c29) (RunStep.use B (fun (σ_1:Env) => And (Core w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.target") c32) (And (@Eq Nat (Env.vars σ_1 "vm.result") c33) (And (c34 (@List.length Nat (Env.arrs σ_1 "vm.addresses"))) (c34 (@List.length Nat (Env.arrs σ_1 "vm.values"))))))) write (fun (x τ:Env) => c13 τ) ((14:Nat)) hwrite c11 ?_) fun (w_1:Env) (h:And (c12 w_1 ((14:Nat))) (c13 w_1)) => let c0_1:Prop:=c12 w_1 ((14:Nat)); let c1_1:Nat:=c27 (Env.vars w_1 "vm.pc") ((1:Nat)); let c2_1:Env:=Env.setVar w_1 "vm.pc" c1_1; let c3_1:Prop:=c28 c2_1; @And.casesOn c0_1 (c13 w_1) (fun (x:And c0_1 (c13 w_1)) => @Exists Env c29) h fun (left:c0_1) (right:c13 w_1) => @Exists.intro Env c29 c2_1 (@And.intro (c26 c2_1 ((40:Nat))) c3_1 (RunStep.mono B c25 σ c2_1 (c27 c38 c42) ((40:Nat)) (RunStep.seq B c17 c24 σ c6 c2_1 c38 c42 (RunStep.assign B σ "vm.target" c16 c5 (RunStep.eval_sub B σ (Expr.lit a) c15 a c4 (RunStep.eval_lit B a σ ha) (RunStep.eval_mul B σ (Expr.div (Expr.lit a) (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c3 (Env.vars σ "vm.modulus") (RunStep.eval_div B σ (Expr.lit a) (Expr.var "vm.modulus") a (Env.vars σ "vm.modulus") (RunStep.eval_lit B a σ ha) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5763_0_0_0)) ?_) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5763_0_0_1)) ?_) (?nAX_g5763_0_0_2))) (RunStep.seq B c20 c23 c6 c11 c2_1 c39 c41 (RunStep.assign B c6 "vm.result" c19 c10 (RunStep.eval_sub B c6 (Expr.lit value) c18 value c9 (RunStep.eval_lit B value c6 hv) (RunStep.eval_mul B c6 (Expr.div (Expr.lit value) (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c8 c7 (RunStep.eval_div B c6 (Expr.lit value) (Expr.var "vm.modulus") value c7 (RunStep.eval_lit B value c6 hv) (RunStep.eval_var B c6 "vm.modulus" (?nAX_g5763_0_0_3)) ?_) (RunStep.eval_var B c6 "vm.modulus" (?nAX_g5763_0_0_4)) ?_) (?nAX_g5763_0_0_5))) (RunStep.seq B write c22 c11 w_1 c2_1 ((14:Nat)) c40 left (RunStep.assign B w_1 "vm.pc" c21 c1_1 (RunStep.eval_add B w_1 (Expr.var "vm.pc") (Expr.lit ((1:Nat))) (Env.vars w_1 "vm.pc") ((1:Nat)) (RunStep.eval_var B w_1 "vm.pc" ?_) (RunStep.eval_lit B ((1:Nat)) w_1 h1) ?_))))) (?nAX_g5763_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5763_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5763_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [Core,_root_.Lax455465Proofs.RamSparseRead.Representation,Nat.mod_def,Nat.mul_comm]
  all_goals omega

theorem writeBack_register_spec (B w pc:ℕ) (m:SparseRam.Memory) (a value:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hv:value < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Core w pc m σ∧ σ.vars "vm.result"=value∧
      m.length < (σ.arrs "vm.addresses").length∧ m.length < (σ.arrs "vm.values").length)
      (writeBack (.lit a) (.var "vm.result"))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) 40:=by
  have ham:=Nat.mod_lt a (Nat.two_pow_pos w)
  have hvm:=Nat.mod_lt value (Nat.two_pow_pos w)
  have hwrite:=write_core_spec B w pc m (a % 2 ^ w) (value % 2 ^ w) h1 hM ham hvm hlen
  have hwrites:SparseRam.write w m (a % 2 ^ w) (value % 2 ^ w)=SparseRam.write w m a value:=by
    simp only [SparseRam.write,Nat.mod_mod]
  rw [hwrites] at hwrite
  rintro σ ⟨⟨hrep,hσpc,hσmod,hσwidth⟩,hσvalue,hA,hV⟩
  have had:a / 2 ^ w < B:=(Nat.div_le_self _ _).trans_lt ha
  have hap:a / 2 ^ w * 2 ^ w < B:=(Nat.div_mul_le_self _ _).trans_lt ha
  have has:a - a / 2 ^ w * 2 ^ w < B:=(Nat.sub_le _ _).trans_lt ha
  have hvd:value / 2 ^ w < B:=(Nat.div_le_self _ _).trans_lt hv
  have hvp:value / 2 ^ w * 2 ^ w < B:=(Nat.div_mul_le_self _ _).trans_lt hv
  have hvs:value - value / 2 ^ w * 2 ^ w < B:=(Nat.sub_le _ _).trans_lt hv
  simp only [writeBack,remainder,increment]
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c3:Nat:=c2 a (Env.vars σ "vm.modulus"); let c4:Nat:=c1 c3 (Env.vars σ "vm.modulus"); let c5:Nat:=c0 a c4; let c6:Env:=Env.setVar σ "vm.target" c5; let c7:String→ Nat:=Env.vars c6; let c8:Nat:=c7 "vm.result"; let c9:Nat:=c7 "vm.modulus"; let c10:Nat:=c2 c8 c9; let c11:Nat:=c1 c10 c9; let c12:Nat:=c0 c8 c11; let c13:Env:=Env.setVar c6 "vm.result" c12; let c14:Env→ Nat→ Prop:=Run B write c13; let c15:Env→ Prop:=Core w pc (SparseRam.write w m a value); let c16:Env→ Prop:=fun (σ':Env) => And (c14 σ' ((14:Nat))) (c15 σ'); let c17:Expr:=Expr.mul (Expr.div (Expr.lit a) (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c18:Expr:=Expr.sub (Expr.lit a) c17; let c19:Com:=Com.assign "vm.target" c18; let c20:Expr:=Expr.mul (Expr.div (Expr.var "vm.result") (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c21:Expr:=Expr.sub (Expr.var "vm.result") c20; let c22:Com:=Com.assign "vm.result" c21; let c23:Expr:=Expr.add (Expr.var "vm.pc") (Expr.lit ((1:Nat))); let c24:Com:=Com.assign "vm.pc" c23; let c25:Com:=Com.seq write c24; let c26:Com:=Com.seq c22 c25; let c27:Com:=Com.seq c19 c26; let c28:Env→ Nat→ Prop:=Run B c27 σ; let c29:Nat→ Nat→ Nat:=Nat.add; let c30:Env→ Prop:=Core w (c29 pc ((1:Nat))) (SparseRam.write w m a value); let c31:Env→ Prop:=fun (σ':Env) => And (c28 σ' ((40:Nat))) (c30 σ'); let c32:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c33:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w; let c34:Nat:=c32 a c33; let c35:Nat:=c32 value c33; let c36:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c37:String→ Nat:=Env.vars c13; let c38:String→ List Nat:=Env.arrs c13; let c39:Nat→ Nat:=c29 ((1:Nat)); let c40:Nat:=c39 (Expr.size c18); let c41:Nat:=c39 (Expr.size c21); let c42:Nat:=c39 (Expr.size c23); let c43:Nat:=c29 ((14:Nat)) c42; let c44:Nat:=c29 c41 c43; @Exists.casesOn Env c16 (fun (x:@Exists Env c16) => @Exists Env c31) (RunStep.use B (fun (σ_1:Env) => And (Core w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.target") c34) (And (@Eq Nat (Env.vars σ_1 "vm.result") c35) (And (c36 (@List.length Nat (Env.arrs σ_1 "vm.addresses"))) (c36 (@List.length Nat (Env.arrs σ_1 "vm.values"))))))) write (fun (x τ:Env) => c15 τ) ((14:Nat)) hwrite c13 ?_) fun (w_1:Env) (h:And (c14 w_1 ((14:Nat))) (c15 w_1)) => let c0_1:Prop:=c14 w_1 ((14:Nat)); let c1_1:Nat:=c29 (Env.vars w_1 "vm.pc") ((1:Nat)); let c2_1:Env:=Env.setVar w_1 "vm.pc" c1_1; let c3_1:Prop:=c30 c2_1; @And.casesOn c0_1 (c15 w_1) (fun (x:And c0_1 (c15 w_1)) => @Exists Env c31) h fun (left:c0_1) (right:c15 w_1) => @Exists.intro Env c31 c2_1 (@And.intro (c28 c2_1 ((40:Nat))) c3_1 (RunStep.mono B c27 σ c2_1 (c29 c40 c44) ((40:Nat)) (RunStep.seq B c19 c26 σ c6 c2_1 c40 c44 (RunStep.assign B σ "vm.target" c18 c5 (RunStep.eval_sub B σ (Expr.lit a) c17 a c4 (RunStep.eval_lit B a σ ha) (RunStep.eval_mul B σ (Expr.div (Expr.lit a) (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c3 (Env.vars σ "vm.modulus") (RunStep.eval_div B σ (Expr.lit a) (Expr.var "vm.modulus") a (Env.vars σ "vm.modulus") (RunStep.eval_lit B a σ ha) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5764_0_0_0)) ?_) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5764_0_0_1)) ?_) (?nAX_g5764_0_0_2))) (RunStep.seq B c22 c25 c6 c13 c2_1 c41 c43 (RunStep.assign B c6 "vm.result" c21 c12 (RunStep.eval_sub B c6 (Expr.var "vm.result") c20 c8 c11 (RunStep.eval_var B c6 "vm.result" (?nAX_g5764_0_0_3)) (RunStep.eval_mul B c6 (Expr.div (Expr.var "vm.result") (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c10 c9 (RunStep.eval_div B c6 (Expr.var "vm.result") (Expr.var "vm.modulus") c8 c9 (RunStep.eval_var B c6 "vm.result" (?nAX_g5764_0_0_4)) (RunStep.eval_var B c6 "vm.modulus" (?nAX_g5764_0_0_5)) ?_) (RunStep.eval_var B c6 "vm.modulus" (?nAX_g5764_0_0_6)) ?_) (?nAX_g5764_0_0_7))) (RunStep.seq B write c24 c13 w_1 c2_1 ((14:Nat)) c42 left (RunStep.assign B w_1 "vm.pc" c23 c1_1 (RunStep.eval_add B w_1 (Expr.var "vm.pc") (Expr.lit ((1:Nat))) (Env.vars w_1 "vm.pc") ((1:Nat)) (RunStep.eval_var B w_1 "vm.pc" ?_) (RunStep.eval_lit B ((1:Nat)) w_1 h1) ?_))))) (?nAX_g5764_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5764_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5764_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [Core,_root_.Lax455465Proofs.RamSparseRead.Representation,Nat.mod_def,Nat.mul_comm]
  all_goals omega

theorem jump_spec (B w pc:ℕ) (m:SparseRam.Memory) (label:ℕ) (hlabel:label < B):
    Spec B (Core w pc m) (instruction (.jump label))
      (fun _ τ => Core w label m τ) 2:=by
  rintro σ ⟨hrep,hσpc,hσmod,hσwidth⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Core w label m τ) σ; @Exists.intro Env (fun (σ':Env) => And (Run B (instruction (Lax808846.Ram.Instr.jump label)) σ σ' ((2:Nat))) (c0 σ')) (Env.setVar σ "vm.pc" label) (@And.intro (Run B (instruction (Lax808846.Ram.Instr.jump label)) σ (Env.setVar σ "vm.pc" label) ((2:Nat))) (c0 (Env.setVar σ "vm.pc" label)) (RunStep.mono B (instruction (Lax808846.Ram.Instr.jump label)) σ (Env.setVar σ "vm.pc" label) (Nat.add ((1:Nat)) (Expr.size (Expr.lit label))) ((2:Nat)) (RunStep.assign B σ "vm.pc" (Expr.lit label) label (RunStep.eval_lit B label σ hlabel)) (?nAX_g5765_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5765_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Core,_root_.Lax455465Proofs.RamSparseRead.Representation]

end Lax455465Proofs.RamVirtualCore

end

section

namespace Lax455465Proofs.RamVirtualState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualCore RamVirtualProgram

theorem init_spec (B w:ℕ) (input:List ℕ) (h1:1 < B):
    Spec B (fun σ => σ.vars "vm.modulus"=2 ^ w∧ σ.vars "vm.width"=w∧
      Prefix input "vm.input" σ∧ σ.vars "vm.inputLength"=input.length) initCommand
      (fun _ τ => Represents w (SparseRam.init input) τ∧ τ.vars "vm.running"=1) 10:=by
  rintro σ ⟨hM,hw,hp,hlen⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (Represents w (SparseRam.init input) τ) (@Eq Nat (Env.vars τ "vm.running") ((1:Nat)))) σ; let c1:Env:=Env.setVar σ "vm.pc" ((0:Nat)); let c2:Env:=Env.setVar c1 "vm.count" ((0:Nat)); let c3:Env:=Env.setVar c2 "vm.cursor" ((0:Nat)); let c4:Env:=Env.setVar c3 "vm.outputLength" ((0:Nat)); let c5:Env:=Env.setVar c4 "vm.running" ((1:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat→ Nat:=c6 c8; let c10:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c11:Nat:=c9 c10; let c12:Nat:=c9 c11; let c13:Nat:=c9 c12; let c14:Com:=Com.assign "vm.count" (Expr.lit ((0:Nat))); let c15:Com:=Com.assign "vm.cursor" (Expr.lit ((0:Nat))); let c16:Com:=Com.assign "vm.outputLength" (Expr.lit ((0:Nat))); let c17:Com:=Com.assign "vm.running" (Expr.lit ((1:Nat))); let c18:Com:=Com.seq c16 c17; let c19:Com:=Com.seq c15 c18; @Exists.intro Env (fun (σ':Env) => And (Run B initCommand σ σ' ((10:Nat))) (c0 σ')) c5 (@And.intro (Run B initCommand σ c5 ((10:Nat))) (c0 c5) (RunStep.mono B initCommand σ c5 (c9 c13) ((10:Nat)) (RunStep.seq B (Com.assign "vm.pc" (Expr.lit ((0:Nat)))) (Com.seq c14 c19) σ c1 c5 c8 c13 (RunStep.assign B σ "vm.pc" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5769_0_0_0))) (RunStep.seq B c14 c19 c1 c2 c5 c8 c12 (RunStep.assign B c1 "vm.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5769_0_0_1))) (RunStep.seq B c15 c18 c2 c3 c5 c8 c11 (RunStep.assign B c2 "vm.cursor" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g5769_0_0_2))) (RunStep.seq B c16 c17 c3 c4 c5 c8 c10 (RunStep.assign B c3 "vm.outputLength" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c3 (?nAX_g5769_0_0_3))) (RunStep.assign B c4 "vm.running" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1)))))) (?nAX_g5769_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5769_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5769_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5769_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5769_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5769_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Core,Tapes,RamSparseRead.Representation,Prefix,SparseRam.init]

theorem stop_spec (B w:ℕ) (s:SparseRam.SparseState) (hB:0 < B):
    Spec B (Represents w s) stop
      (fun _ τ => Represents w s τ∧ τ.vars "vm.running"=0) 2:=by
  rintro σ ⟨hcore,htapes⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (Represents w s τ) (@Eq Nat (Env.vars τ "vm.running") ((0:Nat)))) σ; let c1:Env:=Env.setVar σ "vm.running" ((0:Nat)); @Exists.intro Env (fun (σ':Env) => And (Run B stop σ σ' ((2:Nat))) (c0 σ')) c1 (@And.intro (Run B stop σ c1 ((2:Nat))) (c0 c1) (RunStep.mono B stop σ c1 (Nat.add ((1:Nat)) (Expr.size (Expr.lit ((0:Nat))))) ((2:Nat)) (RunStep.assign B σ "vm.running" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hB)) (?nAX_g5770_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5770_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Core,Tapes,RamSparseRead.Representation,Prefix]

theorem tapes_frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (s:SparseRam.SparseState) (ht:Tapes s σ)
    (hinput:"vm.input" ∉ c.warrs) (houtput:"vm.output" ∉ c.warrs)
    (hinlen:"vm.inputLength" ∉ c.wvars) (hcursor:"vm.cursor" ∉ c.wvars)
    (houtlen:"vm.outputLength" ∉ c.wvars):Tapes s τ:=by
  have hi:=hr.frame_arr "vm.input" hinput
  have ho:=hr.frame_arr "vm.output" houtput
  have hl:=hr.frame_var "vm.inputLength" hinlen
  have hc:=hr.frame_var "vm.cursor" hcursor
  have hol:=hr.frame_var "vm.outputLength" houtlen
  simpa only [Tapes,Prefix,hi,ho,hl,hc,hol] using ht

theorem empty_iff_cursor (s:SparseRam.SparseState) (σ:Env) (h:Tapes s σ):
    s.inp=[]↔ σ.vars "vm.cursor"=s.input.length:=by
  rw [h.2.2.2.1,List.drop_eq_nil_iff]
  have hb:=h.2.2.1
  omega

end Lax455465Proofs.RamVirtualState

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

theorem keep_space {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (h:Spec B P c Q K) (a:String) (used:ℕ):
    Spec B (fun σ => P σ∧ used < (σ.arrs a).length) c
      (fun σ τ => Q σ τ∧ used < (τ.arrs a).length) K:=by
  rintro σ ⟨hp,hs⟩
  obtain ⟨τ,hr,hq⟩:=h σ hp
  exact ⟨τ,hr,hq,by rwa [run_array_length hr a]⟩

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamVirtualArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualProgram RamVirtualCore RamSparseRead RamFrames

def Working (w pc:ℕ) (m:SparseRam.Memory) (σ:Env):Prop:=
  Core w pc m σ∧ m.length < (σ.arrs "vm.addresses").length∧
    m.length < (σ.arrs "vm.values").length

theorem binary_stage_spec (B w pc:ℕ) (m:SparseRam.Memory) (target left right:ℕ) (op:Bop)
    (h1:1 < B) (hM:2 ^ w < B) (htarget:target < B) (hl:left < B) (hr:right < B)
    (hop:op.apply left right < B) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=left∧ σ.vars "vm.right"=right)
      (.seq (RamWordOps.binary op) (writeBack (.lit target) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target (op.apply left right)) τ) 52:=by
  have hbody:Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=left∧ σ.vars "vm.right"=right)
      (RamWordOps.binary op) (fun _ τ => Working w pc m τ∧ τ.vars "vm.result"=op.apply left right % 2 ^ w) 12:=by
    rintro σ ⟨⟨hcore,hA,hV⟩,hleft,hright⟩
    obtain ⟨τ,hrun,hpost⟩:=RamWordOps.binary_spec B (2 ^ w) left right op hM hl hr hop
      σ ⟨hcore.2.2.1,hleft,hright⟩
    have hframe:τ.arrs=σ.arrs:=hrun.frame_arrs_eqOn
      (by simp [RamWordOps.binary,RamWordOps.reduce,Com.warrs])
    have hcount:=hrun.frame_var "vm.count" (by simp [RamWordOps.binary,RamWordOps.reduce,Com.wvars])
    have hcounter:=hrun.frame_var "vm.pc" (by simp [RamWordOps.binary,RamWordOps.reduce,Com.wvars])
    have hmod:=hrun.frame_var "vm.modulus" (by simp [RamWordOps.binary,RamWordOps.reduce,Com.wvars])
    have hwidth:=hrun.frame_var "vm.width" (by simp [RamWordOps.binary,RamWordOps.reduce,Com.wvars])
    have hcore':Core w pc m τ:=by
      simpa only [Core,_root_.Lax455465Proofs.RamSparseRead.Representation,hframe,hcount,hcounter,hmod,hwidth] using hcore
    exact ⟨τ,hrun, ⟨hcore',by simpa only [hframe] using hA,by simpa only [hframe] using hV⟩,hpost⟩
  have hfinish:=writeBack_register_spec B w pc m target (op.apply left right % 2 ^ w)
    h1 hM htarget ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) hpc hlen
  have hnormalize:SparseRam.write w m target (op.apply left right % 2 ^ w) =
      SparseRam.write w m target (op.apply left right):=by simp only [SparseRam.write,Nat.mod_mod]
  rw [hnormalize] at hfinish
  rintro σ ⟨⟨hcore,hA,hV⟩,hleft,hright⟩
  (expose_names;
    (refine let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) (Bop.apply op left right) (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w); let c1:Env→ Prop:=fun (σ':Env) => And (Run B (RamWordOps.binary op) σ σ' ((12:Nat))) (And (Working w pc m σ') (@Eq Nat (Env.vars σ' "vm.result") c0)); let c2:Com:=Com.seq (RamWordOps.binary op) (writeBack (Expr.lit target) (Expr.var "vm.result")); let c3:Env→ Nat→ Prop:=Run B c2 σ; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Env→ Prop:=Core w (c4 pc ((1:Nat))) (SparseRam.write w m target (Bop.apply op left right)); let c6:Env→ Env→ Prop:=fun (x τ:Env) => c5 τ; let c7:Env→ Prop:=c6 σ; let c8:Env→ Prop:=fun (σ':Env) => And (c3 σ' ((52:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Env→ Env→ Nat→ Prop:=Run B (writeBack (Expr.lit target) (Expr.var "vm.result")); let c11:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); @Exists.casesOn Env c1 (fun (x:@Exists Env c1) => c9) (RunStep.use B (fun (σ_1:Env) => And (Working w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.left") left) (@Eq Nat (Env.vars σ_1 "vm.right") right))) (RamWordOps.binary op) (fun (x τ:Env) => And (Working w pc m τ) (@Eq Nat (Env.vars τ "vm.result") c0)) ((12:Nat)) hbody σ ?_) fun (w_1:Env) (h:And (Run B (RamWordOps.binary op) σ w_1 ((12:Nat))) (And (Working w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.result") c0))) => let c0_1:Prop:=Run B (RamWordOps.binary op) σ w_1 ((12:Nat)); let c1_1:Prop:=And (Working w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.result") c0); let c2_1:Env→ Prop:=fun (σ':Env) => And (c10 w_1 σ' ((40:Nat))) (c5 σ'); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c9) h fun (left_1:c0_1) (right_1:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c9) (RunStep.use B (fun (σ_1:Env) => And (Core w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.result") c0) (And (c11 (@List.length Nat (Env.arrs σ_1 "vm.addresses"))) (c11 (@List.length Nat (Env.arrs σ_1 "vm.values")))))) (writeBack (Expr.lit target) (Expr.var "vm.result")) c6 ((40:Nat)) hfinish w_1 ?_) fun (w_2:Env) (h_1:And (c10 w_1 w_2 ((40:Nat))) (c5 w_2)) => let c0_2:Prop:=c10 w_1 w_2 ((40:Nat)); @And.casesOn c0_2 (c5 w_2) (fun (x:And c0_2 (c5 w_2)) => c9) h_1 fun (left_2:c0_2) (right_2:c5 w_2) => @Exists.intro Env c8 w_2 (@And.intro (c3 w_2 ((52:Nat))) (c7 w_2) (RunStep.mono B c2 σ w_2 (c4 ((12:Nat)) ((40:Nat))) ((52:Nat)) (RunStep.seq B (RamWordOps.binary op) (writeBack (Expr.lit target) (Expr.var "vm.result")) σ w_1 w_2 ((12:Nat)) ((40:Nat)) left_1 left_2) (?nAX_g5959_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5959_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_1); (all_goals try clear h_1); (all_goals try clear left_2))
  all_goals simp_all [Working]

theorem operand_spec (B w pc:ℕ) (m:SparseRam.Memory) (address:ℕ)
    (body:Com) (K:ℕ) (Q:Env→ Prop)
    (h1:1 < B) (hM:2 ^ w < B) (ha:address < B)
    (hlen:m.length < B) (hwords:SparseBounds.MemoryWords w m)
    (hbody:Spec B (fun σ => Working w pc m σ∧
      σ.vars "vm.left"=SparseRam.lookup m (address % 2 ^ w)) body (fun _ τ => Q τ) K):
    Spec B (Working w pc m)
      (.seq (RamSparseRead.read "vm.left" (remainder (.lit address))) body)
      (fun _ τ => Q τ) (16 * m.length + 18 + K):=by
  have hget:=read_literal_spec B w pc m address "vm.left" h1 hM ha hlen hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread:=keep_space (keep_space hget "vm.addresses" m.length) "vm.values" m.length
  rintro σ ⟨hcore,hA,hV⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.left" (remainder (Expr.lit address))) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 (Nat.mul ((16:Nat)) (@List.length (Prod Nat Nat) m)) ((18:Nat)); let c3:Nat:=SparseRam.lookup m (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) address (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w)); let c4:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' c2) (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.left") c3)) (c4 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c4 (@List.length Nat (Env.arrs σ' "vm.values")))); let c6:Com:=Com.seq (RamSparseRead.read "vm.left" (remainder (Expr.lit address))) body; let c7:Env→ Nat→ Prop:=Run B c6 σ; let c8:Nat:=c1 c2 K; let c9:Env→ Prop:=fun (σ':Env) => And (c7 σ' c8) ((fun (x τ:Env) => Q τ) σ σ'); let c10:Prop:= @Exists Env c9; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (And (Core w pc m σ_1) (c4 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c4 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.left" (remainder (Expr.lit address))) (fun (σ_1 τ:Env) => And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.left") c3)) (c4 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c4 (@List.length Nat (Env.arrs τ "vm.values")))) c2 hread σ ?_) fun (w_1:Env) (h:And (c0 w_1 c2) (And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c3)) (c4 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c4 (@List.length Nat (Env.arrs w_1 "vm.values"))))) => let c0_1:Prop:=And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c3)) (c4 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c4 (@List.length Nat (Env.arrs w_1 "vm.values"))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B body w_1 σ' K) (Q σ'); @And.casesOn (c0 w_1 c2) c0_1 (fun (x:And (c0 w_1 c2) c0_1) => c10) h fun (left:c0 w_1 c2) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c10) (RunStep.use B (fun (σ_1:Env) => And (Working w pc m σ_1) (@Eq Nat (Env.vars σ_1 "vm.left") c3)) body (fun (x τ:Env) => Q τ) K hbody w_1 ?_) fun (w_2:Env) (h_1:And (Run B body w_1 w_2 K) (Q w_2)) => @And.casesOn (Run B body w_1 w_2 K) (Q w_2) (fun (x:And (Run B body w_1 w_2 K) (Q w_2)) => c10) h_1 fun (left_1:Run B body w_1 w_2 K) (right_1:Q w_2) => @Exists.intro Env c9 w_2 (@And.intro (c7 w_2 c8) ((fun (x τ:Env) => Q τ) σ w_2) (RunStep.mono B c6 σ w_2 c8 c8 (RunStep.seq B (RamSparseRead.read "vm.left" (remainder (Expr.lit address))) body σ w_1 w_2 c2 K left left_1) (?nAX_g5960_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5960_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals simp_all [Working]

theorem operands_spec (B w pc:ℕ) (m:SparseRam.Memory) (left right:ℕ)
    (body:Com) (K:ℕ) (Q:Env→ Prop)
    (h1:1 < B) (hM:2 ^ w < B) (hl:left < B) (hr:right < B)
    (hlen:m.length < B) (hwords:SparseBounds.MemoryWords w m)
    (hbody:Spec B (fun σ => Working w pc m σ∧
      σ.vars "vm.left"=SparseRam.lookup m (left % 2 ^ w)∧
      σ.vars "vm.right"=SparseRam.lookup m (right % 2 ^ w)) body (fun _ τ => Q τ) K):
    Spec B (Working w pc m) (operands left right body) (fun _ τ => Q τ) (32 * m.length + 36 + K):=by
  let l:=SparseRam.lookup m (left % 2 ^ w)
  have hgetL:=read_literal_spec B w pc m left "vm.left" h1 hM hl hlen hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetR:=keep_scalar (read_literal_spec B w pc m right "vm.right" h1 hM hr hlen hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.left" l
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
  have hleft:=keep_space (keep_space hgetL "vm.addresses" m.length) "vm.values" m.length
  have hright:=keep_space (keep_space hgetR "vm.addresses" m.length) "vm.values" m.length
  rintro σ ⟨hcore,hA,hV⟩
  unfold operands
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c1 (c2 ((16:Nat)) (@List.length (Prod Nat Nat) m)) ((18:Nat)); let c4:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c5:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w; let c6:Nat:=SparseRam.lookup m (c4 left c5); let c7:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c8:Env→ Prop:=fun (σ':Env) => And (c0 σ' c3) (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.left") c6)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); let c9:Com:=Com.seq (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) body; let c10:Com:=Com.seq (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) c9; let c11:Env→ Nat→ Prop:=Run B c10 σ; let c12:Nat:=c1 (c1 (c2 ((32:Nat)) (@List.length (Prod Nat Nat) m)) ((36:Nat))) K; let c13:Env→ Prop:=fun (σ':Env) => And (c11 σ' c12) ((fun (x τ:Env) => Q τ) σ σ'); let c14:Prop:= @Exists Env c13; let c15:Env→ Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.right" (remainder (Expr.lit right))); let c16:Nat:=SparseRam.lookup m (c4 right c5); let c17:Nat→ Nat:=c1 c3; let c18:Nat:=c17 K; @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c14) (RunStep.use B (fun (σ_1:Env) => And (And (Core w pc m σ_1) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) (fun (σ_1 τ:Env) => And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.left") c6)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hleft σ ?_) fun (w_1:Env) (h:And (c0 w_1 c3) (And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))))) => let c0_1:Prop:=And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))); let c1_1:Env→ Prop:=fun (σ':Env) => And (c15 w_1 σ' c3) (And (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.right") c16)) (@Eq Nat (Env.vars σ' "vm.left") l)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); @And.casesOn (c0 w_1 c3) c0_1 (fun (x:And (c0 w_1 c3) c0_1) => c14) h fun (left_1:c0 w_1 c3) (right_1:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c14) (RunStep.use B (fun (σ_1:Env) => And (And (And (Core w pc m σ_1) (@Eq Nat (Env.vars σ_1 "vm.left") l)) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) (fun (σ_1 τ:Env) => And (And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.right") c16)) (@Eq Nat (Env.vars τ "vm.left") l)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hright w_1 ?_) fun (w_2:Env) (h_1:And (c15 w_1 w_2 c3) (And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.right") c16)) (@Eq Nat (Env.vars w_2 "vm.left") l)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))))) => let c0_2:Prop:=And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.right") c16)) (@Eq Nat (Env.vars w_2 "vm.left") l)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))); let c1_2:Env→ Prop:=fun (σ':Env) => And (Run B body w_2 σ' K) (Q σ'); @And.casesOn (c15 w_1 w_2 c3) c0_2 (fun (x:And (c15 w_1 w_2 c3) c0_2) => c14) h_1 fun (left_2:c15 w_1 w_2 c3) (right_2:c0_2) => @Exists.casesOn Env c1_2 (fun (x:@Exists Env c1_2) => c14) (RunStep.use B (fun (σ_1:Env) => And (Working w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.left") c6) (@Eq Nat (Env.vars σ_1 "vm.right") c16))) body (fun (x τ:Env) => Q τ) K hbody w_2 ?_) fun (w_3:Env) (h_2:And (Run B body w_2 w_3 K) (Q w_3)) => @And.casesOn (Run B body w_2 w_3 K) (Q w_3) (fun (x:And (Run B body w_2 w_3 K) (Q w_3)) => c14) h_2 fun (left_3:Run B body w_2 w_3 K) (right_3:Q w_3) => @Exists.intro Env c13 w_3 (@And.intro (c11 w_3 c12) ((fun (x τ:Env) => Q τ) σ w_3) (RunStep.mono B c10 σ w_3 (c17 c18) c12 (RunStep.seq B (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) c9 σ w_1 w_3 c3 c18 left_1 (RunStep.seq B (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) body w_1 w_2 w_3 c3 K left_2 left_3)) (?nAX_g5961_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5961_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_1); (all_goals try clear h_1); (all_goals try clear left_2); (all_goals try clear h_2); (all_goals try clear left_3))
  all_goals simp_all [Working,l]

theorem binary_spec (B w pc:ℕ) (m:SparseRam.Memory) (target left right:ℕ) (op:Bop)
    (h1:1 < B) (hM:2 ^ w < B) (htarget:target < B) (hl:left < B) (hr:right < B)
    (hwords:SparseBounds.MemoryWords w m)
    (hop:op.apply (SparseRam.lookup m (left % 2 ^ w)) (SparseRam.lookup m (right % 2 ^ w)) < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (Working w pc m) (RamVirtualProgram.binary op target left right)
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target
        (op.apply (SparseRam.lookup m (left % 2 ^ w)) (SparseRam.lookup m (right % 2 ^ w)))) τ)
      (32 * m.length + 88):=by
  let l:=SparseRam.lookup m (left % 2 ^ w)
  let r:=SparseRam.lookup m (right % 2 ^ w)
  have hlB:l < B:=(SparseBounds.lookup_bound w m _ hwords).trans hM
  have hrB:r < B:=(SparseBounds.lookup_bound w m _ hwords).trans hM
  have hgetL:=read_literal_spec B w pc m left "vm.left" h1 hM hl (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetR:=keep_scalar (read_literal_spec B w pc m right "vm.right" h1 hM hr (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.left" l (by simp [RamSparseRead.read,RamSparseMemory.lookup,
      RamSparseMemory.scanStep,Com.wvars])
  have hleft:=keep_space (keep_space hgetL "vm.addresses" m.length) "vm.values" m.length
  have hright:=keep_space (keep_space hgetR "vm.addresses" m.length) "vm.values" m.length
  have hstage:=binary_stage_spec B w pc m target l r op h1 hM htarget hlB hrB hop hpc hlen
  rintro σ ⟨hcore,hA,hV⟩
  simp only [RamVirtualProgram.binary,operands]
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c1 (c2 ((16:Nat)) (@List.length (Prod Nat Nat) m)) ((18:Nat)); let c4:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c5:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w; let c6:Nat:=SparseRam.lookup m (c4 left c5); let c7:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c8:Env→ Prop:=fun (σ':Env) => And (c0 σ' c3) (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.left") c6)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); let c9:Com:=Com.seq (RamWordOps.binary op) (writeBack (Expr.lit target) (Expr.var "vm.result")); let c10:Com:=Com.seq (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) c9; let c11:Com:=Com.seq (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) c10; let c12:Env→ Nat→ Prop:=Run B c11 σ; let c13:Nat:=c1 (c2 ((32:Nat)) (@List.length (Prod Nat Nat) m)) ((88:Nat)); let c14:SparseRam.Memory→ Env→ Prop:=Core w (c1 pc ((1:Nat))); let c15:Nat:=SparseRam.lookup m (c4 right c5); let c16:Env→ Prop:=c14 (SparseRam.write w m target (Bop.apply op c6 c15)); let c17:Env→ Prop:=fun (σ':Env) => And (c12 σ' c13) (c16 σ'); let c18:Prop:= @Exists Env c17; let c19:Env→ Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.right" (remainder (Expr.lit right))); let c20:Env→ Env→ Nat→ Prop:=Run B c9; let c21:Env→ Prop:=c14 (SparseRam.write w m target (Bop.apply op l r)); let c22:Nat→ Nat:=c1 c3; let c23:Nat:=c22 ((52:Nat)); @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c18) (RunStep.use B (fun (σ_1:Env) => And (And (Core w pc m σ_1) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) (fun (σ_1 τ:Env) => And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.left") c6)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hleft σ ?_) fun (w_1:Env) (h:And (c0 w_1 c3) (And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))))) => let c0_1:Prop:=And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.left") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))); let c1_1:Env→ Prop:=fun (σ':Env) => And (c19 w_1 σ' c3) (And (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.right") c15)) (@Eq Nat (Env.vars σ' "vm.left") l)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); @And.casesOn (c0 w_1 c3) c0_1 (fun (x:And (c0 w_1 c3) c0_1) => c18) h fun (left_1:c0 w_1 c3) (right_1:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c18) (RunStep.use B (fun (σ_1:Env) => And (And (And (Core w pc m σ_1) (@Eq Nat (Env.vars σ_1 "vm.left") l)) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) (fun (σ_1 τ:Env) => And (And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.right") c15)) (@Eq Nat (Env.vars τ "vm.left") l)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hright w_1 ?_) fun (w_2:Env) (h_1:And (c19 w_1 w_2 c3) (And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.right") c15)) (@Eq Nat (Env.vars w_2 "vm.left") l)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))))) => let c0_2:Prop:=And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.right") c15)) (@Eq Nat (Env.vars w_2 "vm.left") l)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))); let c1_2:Env→ Prop:=fun (σ':Env) => And (c20 w_2 σ' ((52:Nat))) (c21 σ'); @And.casesOn (c19 w_1 w_2 c3) c0_2 (fun (x:And (c19 w_1 w_2 c3) c0_2) => c18) h_1 fun (left_2:c19 w_1 w_2 c3) (right_2:c0_2) => @Exists.casesOn Env c1_2 (fun (x:@Exists Env c1_2) => c18) (RunStep.use B (fun (σ_1:Env) => And (Working w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.left") l) (@Eq Nat (Env.vars σ_1 "vm.right") r))) c9 (fun (x τ:Env) => c21 τ) ((52:Nat)) hstage w_2 ?_) fun (w_3:Env) (h_2:And (c20 w_2 w_3 ((52:Nat))) (c21 w_3)) => let c0_3:Prop:=c20 w_2 w_3 ((52:Nat)); @And.casesOn c0_3 (c21 w_3) (fun (x:And c0_3 (c21 w_3)) => c18) h_2 fun (left_3:c0_3) (right_3:c21 w_3) => @Exists.intro Env c17 w_3 (@And.intro (c12 w_3 c13) (c16 w_3) (RunStep.mono B c11 σ w_3 (c22 c23) c13 (RunStep.seq B (RamSparseRead.read "vm.left" (remainder (Expr.lit left))) c10 σ w_1 w_3 c3 c23 left_1 (RunStep.seq B (RamSparseRead.read "vm.right" (remainder (Expr.lit right))) c9 w_1 w_2 w_3 c3 ((52:Nat)) left_2 left_3)) (?nAX_g5962_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_1); (all_goals try clear h_1); (all_goals try clear left_2); (all_goals try clear h_2); (all_goals try clear left_3))
  all_goals simp_all [Working,l,r]

end Lax455465Proofs.RamVirtualArithmetic

end

section

namespace Lax455465Proofs.RamVirtualFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

def Quiet:Lax808846.Ram.Instr→ Prop
  | .read _ | .write _ | .halt => False
  | _ => True

theorem quiet_arrays (i:Lax808846.Ram.Instr) (hq:Quiet i):
    "vm.input" ∉ (instruction i).warrs∧ "vm.output" ∉ (instruction i).warrs:=by
  cases i <;> simp_all [Quiet,instruction,binary,operands,RamWordOps.binary,
    RamWordOps.reduce,RamWordOps.shift,RamWordOps.complement,writeBack,
    RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,increment,Com.warrs]

theorem quiet_variables (i:Lax808846.Ram.Instr) (hq:Quiet i):
    ∀ x∈ ["vm.inputLength", "vm.cursor", "vm.outputLength", "vm.running"],
      x∉ (instruction i).wvars:=by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    cases i <;> simp_all [Quiet,instruction,binary,operands,RamWordOps.binary,
      RamWordOps.reduce,RamWordOps.shift,RamWordOps.complement,writeBack,
      RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
      RamSparseMemory.scanStep,RamSparseMemory.put,increment,Com.wvars]

theorem lift_spec (B w K:ℕ) (i:Lax808846.Ram.Instr) (s t:SparseRam.SparseState)
    (P:Env→ Prop) (hq:Quiet i)
    (ht:t.input=s.input∧ t.inp=s.inp∧ t.out=s.out)
    (hspec:Spec B P (instruction i) (fun _ τ => Core w t.pc t.memory τ) K)
    (hpre:∀ σ,Represents w s σ→ s.memory.length < (σ.arrs "vm.addresses").length→
      s.memory.length < (σ.arrs "vm.values").length→ P σ):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧
      s.memory.length < (σ.arrs "vm.addresses").length∧
      s.memory.length < (σ.arrs "vm.values").length) (instruction i)
      (fun _ τ => Represents w t τ∧ τ.vars "vm.running"=1) K:=by
  rintro σ ⟨hrep,hrunning,hA,hV⟩
  obtain ⟨τ,hrun,hcore⟩:=hspec σ (hpre σ hrep hA hV)
  have harr:=quiet_arrays i hq
  have hvar:=quiet_variables i hq
  have htapes:=tapes_frame hrun s hrep.2 harr.1 harr.2
    (hvar _ (by simp)) (hvar _ (by simp)) (hvar _ (by simp))
  have htapes':Tapes t τ:=by simpa only [Tapes,ht.1,ht.2.1,ht.2.2] using htapes
  exact ⟨τ,hrun, ⟨hcore,htapes'⟩,
    (hrun.frame_var _ (hvar _ (by simp))).trans hrunning⟩

end Lax455465Proofs.RamVirtualFrame

end

section

namespace Lax455465Proofs.RamVirtualBasic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualState

inductive Kind | add | sub | mul | div | and

def operation:Kind→ Bop
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .and => .and

def source (kind:Kind) (a b c:ℕ):Lax808846.Ram.Instr:=
  match kind with
  | .add => .add a b c | .sub => .sub a b c | .mul => .mul a b c
  | .div => .div a b c | .and => .and a b c

def result (kind:Kind) (w:ℕ) (m:SparseRam.Memory) (b c:ℕ):ℕ:=
  (operation kind).apply (SparseRam.lookup m (b % 2 ^ w)) (SparseRam.lookup m (c % 2 ^ w))

theorem result_bound (kind:Kind) (w:ℕ) (m:SparseRam.Memory) (b c:ℕ)
    (hwords:SparseBounds.MemoryWords w m):result kind w m b c < 2 * (2 ^ w) ^ 2 + 3:=by
  have h:=RamWordOps.basic_bounds w (SparseRam.lookup m (b % 2 ^ w))
    (SparseRam.lookup m (c % 2 ^ w)) (SparseBounds.lookup_bound _ _ _ hwords)
    (SparseBounds.lookup_bound _ _ _ hwords)
  cases kind with
  | add => exact h.1
  | sub => exact h.2.1
  | mul => exact h.2.2.1
  | div => exact h.2.2.2.1
  | and => exact h.2.2.2.2

theorem instruction_spec (B w:ℕ) (kind:Kind) (s:SparseRam.SparseState) (a b c:ℕ)
    (hB:2 * (2 ^ w) ^ 2 + 3 < B) (ha:a < B) (hb:b < B) (hc:c < B)
    (hwords:SparseBounds.MemoryWords w s.memory) (hpc:s.pc + 1 < B)
    (hlen:s.memory.length + 1 < B):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧
      s.memory.length < (σ.arrs "vm.addresses").length∧
      s.memory.length < (σ.arrs "vm.values").length)
      (RamVirtualProgram.instruction (source kind a b c))
      (fun _ τ => Represents w (SparseRam.assign w s a (result kind w s.memory b c)) τ∧
        τ.vars "vm.running"=1) (32 * s.memory.length + 88):=by
  have h1:1 < B:=by omega
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have hcore:Spec B (Working w s.pc s.memory)
      (RamVirtualProgram.instruction (source kind a b c))
      (fun _ τ => Core w (s.pc + 1) (SparseRam.write w s.memory a (result kind w s.memory b c)) τ)
      (32 * s.memory.length + 88):=by
    have h:=RamVirtualArithmetic.binary_spec B w s.pc s.memory a b c (operation kind)
      h1 hM ha hb hc hwords ((result_bound kind w s.memory b c hwords).trans hB) hpc hlen
    cases kind <;> exact h
  rintro σ ⟨⟨hcoreσ,htapes⟩,hrunning,hA,hV⟩
  obtain ⟨τ,hrun,hpost⟩:=hcore σ ⟨hcoreσ,hA,hV⟩
  have hcommand:RamVirtualProgram.instruction (source kind a b c) =
      RamVirtualProgram.binary (operation kind) a b c:=by cases kind <;> rfl
  have hinput:"vm.input" ∉ (RamVirtualProgram.instruction (source kind a b c)).warrs:=by
    rw [hcommand]
    simp [RamVirtualProgram.binary,
      RamVirtualProgram.operands,RamWordOps.binary,RamWordOps.reduce,
      RamVirtualProgram.writeBack,RamSparseRead.read,RamSparseRead.write,
      RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamVirtualProgram.increment,Com.warrs]
  have houtput:"vm.output" ∉ (RamVirtualProgram.instruction (source kind a b c)).warrs:=by
    rw [hcommand]
    simp [RamVirtualProgram.binary,
      RamVirtualProgram.operands,RamWordOps.binary,RamWordOps.reduce,
      RamVirtualProgram.writeBack,RamSparseRead.read,RamSparseRead.write,
      RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamVirtualProgram.increment,Com.warrs]
  have hvars:∀ x∈ ["vm.inputLength", "vm.cursor", "vm.outputLength", "vm.running"],
      x∉ (RamVirtualProgram.instruction (source kind a b c)).wvars:=by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hcommand]
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [RamVirtualProgram.binary,
        RamVirtualProgram.operands,RamWordOps.binary,RamWordOps.reduce,
        RamVirtualProgram.writeBack,RamSparseRead.read,RamSparseRead.write,
        RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamVirtualProgram.increment,Com.wvars]
  have htapes':=tapes_frame hrun s htapes hinput houtput
    (hvars _ (by simp)) (hvars _ (by simp)) (hvars _ (by simp))
  exact ⟨τ,hrun, ⟨hpost,htapes'⟩, (hrun.frame_var _ (hvars _ (by simp))).trans hrunning⟩

end Lax455465Proofs.RamVirtualBasic

end

section

namespace Lax455465Proofs.RamVirtualStage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamSparseRead

theorem working_frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (w pc:ℕ) (m:SparseRam.Memory) (h:Working w pc m σ)
    (harrays:c.warrs=[])
    (hvars:∀ x∈ ["vm.count", "vm.pc", "vm.modulus", "vm.width"],x∉ c.wvars):
    Working w pc m τ:=by
  have ha:=hr.frame_arrs_eqOn harrays
  have hcount:=hr.frame_var "vm.count" (hvars _ (by simp))
  have hpc:=hr.frame_var "vm.pc" (hvars _ (by simp))
  have hmod:=hr.frame_var "vm.modulus" (hvars _ (by simp))
  have hw:=hr.frame_var "vm.width" (hvars _ (by simp))
  simpa only [Working,Core,_root_.Lax455465Proofs.RamSparseRead.Representation,ha,hcount,hpc,hmod,hw] using h

theorem result_spec (B w pc:ℕ) (m:SparseRam.Memory) (target value:ℕ)
    (body:Com) (K:ℕ) (P:Env→ Prop)
    (hbody:Spec B P body (fun _ τ => τ.vars "vm.result"=value) K)
    (harrays:body.warrs=[])
    (hvars:∀ x∈ ["vm.count", "vm.pc", "vm.modulus", "vm.width"],x∉ body.wvars)
    (h1:1 < B) (hM:2 ^ w < B) (htarget:target < B) (hv:value < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Working w pc m σ∧ P σ)
      (.seq body (writeBack (.lit target) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m target value) τ) (K + 40):=by
  have hstage:Spec B (fun σ => Working w pc m σ∧ P σ) body
      (fun _ τ => Working w pc m τ∧ τ.vars "vm.result"=value) K:=by
    rintro σ ⟨hwork,hp⟩
    obtain ⟨τ,hr,hq⟩:=hbody σ hp
    exact ⟨τ,hr,working_frame hr w pc m hwork harrays hvars,hq⟩
  have hfinish:=writeBack_register_spec B w pc m target value h1 hM htarget hv hpc hlen
  exact hstage.seq hfinish
    (fun _ _ _ h => ⟨h.1.1,h.2,h.1.2.1,h.1.2.2⟩)
    (fun _ _ _ _ _ h => h)

end Lax455465Proofs.RamVirtualStage

end

section

namespace Lax455465Proofs.RamVirtualBitOps

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram

theorem shift_bound (w value count:ℕ):SparseRam.shiftValue w value count < 2 ^ w:=by
  unfold SparseRam.shiftValue
  split_ifs
  · exact Nat.mod_lt _ (Nat.two_pow_pos w)
  · exact Nat.two_pow_pos w

theorem shift_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a b c:ℕ)
    (hB:2 * (2 ^ w) ^ 2 + 3 < B) (ha:a < B) (hb:b < B) (hc:c < B)
    (hwords:SparseBounds.MemoryWords w m) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (Working w pc m) (instruction (.shiftl a b c))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (SparseRam.lookup m (b % 2 ^ w) * 2 ^ SparseRam.lookup m (c % 2 ^ w))) τ)
      (32 * m.length + 92):=by
  let l:=SparseRam.lookup m (b % 2 ^ w)
  let r:=SparseRam.lookup m (c % 2 ^ w)
  have h1:1 < B:=by omega
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have hl:=SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hr:=SparseBounds.lookup_bound w m (c % 2 ^ w) hwords
  have hshift:=RamWordOps.shift_spec B w l r hB hl hr
  have hstage:=RamVirtualStage.result_spec B w pc m a (SparseRam.shiftValue w l r)
    RamWordOps.shift 16 _ hshift
    (by simp [RamWordOps.shift,RamWordOps.binary,RamWordOps.reduce,Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [RamWordOps.shift,RamWordOps.binary,RamWordOps.reduce,Com.wvars])
    h1 hM ha ((shift_bound w l r).trans hM) hpc hlen
  have heq:SparseRam.write w m a (SparseRam.shiftValue w l r) =
      SparseRam.write w m a (l * 2 ^ r):=by
    simp only [SparseRam.shiftValue_eq,SparseRam.write,Nat.mod_mod]
  rw [heq] at hstage
  have hstage':Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=l∧ σ.vars "vm.right"=r)
      (.seq RamWordOps.shift (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a (l * 2 ^ r)) τ) 56:=
    hstage.pre (fun _ h => ⟨h.1,h.1.1.2.2.1,h.1.1.2.2.2,h.2.1,h.2.2⟩)
  have h:=operands_spec B w pc m b c _ 56 _ h1 hM hb hc (by omega) hwords hstage'
  simpa only [instruction,Nat.add_assoc,Nat.reduceAdd,l,r] using h

theorem complement_bound (w left:ℕ):2 ^ w - 1 - left < 2 ^ w:=by
  have h:=Nat.two_pow_pos w
  omega

theorem not_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a b:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hb:b < B)
    (hwords:SparseBounds.MemoryWords w m) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (Working w pc m) (instruction (.not a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (2 ^ w - 1 - SparseRam.lookup m (b % 2 ^ w))) τ) (16 * m.length + 64):=by
  let l:=SparseRam.lookup m (b % 2 ^ w)
  have hleft:=SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hnot:=RamWordOps.complement_spec B w l hM hleft
  have hstage:=RamVirtualStage.result_spec B w pc m a (2 ^ w - 1 - l)
    RamWordOps.complement 6 _ hnot
    (by simp [RamWordOps.complement,Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [RamWordOps.complement,Com.wvars])
    h1 hM ha ((complement_bound w l).trans hM) hpc hlen
  have hstage':Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=l)
      (.seq RamWordOps.complement (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a (2 ^ w - 1 - l)) τ) 46:=
    hstage.pre (fun _ h => ⟨h.1,h.1.1.2.2.1,h.2⟩)
  have h:=operand_spec B w pc m b _ 46 _ h1 hM hb (by omega) hwords hstage'
  simpa only [instruction,Nat.add_assoc,Nat.reduceAdd,l] using h

end Lax455465Proofs.RamVirtualBitOps

end

section

namespace Lax455465Proofs.RamVirtualControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

theorem jzero_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a label:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hlabel:label < B)
    (hpc:pc + 1 < B) (hlen:m.length < B) (hwords:SparseBounds.MemoryWords w m):
    Spec B (Working w pc m) (instruction (.jzero a label))
      (fun _ τ => Core w (if SparseRam.lookup m (a % 2 ^ w)=0 then label else pc + 1) m τ)
      (16 * m.length + 26):=by
  let value:=SparseRam.lookup m (a % 2 ^ w)
  have hvalue:=(SparseBounds.lookup_bound w m (a % 2 ^ w) hwords).trans hM
  have hbody:Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=value)
      (.ite (.eq (.var "vm.left") (.lit 0)) (.assign "vm.pc" (.lit label)) increment)
      (fun _ τ => Core w (if value=0 then label else pc + 1) m τ) 8:=by
    rintro σ ⟨⟨⟨hrep,hσpc,hσM,hσw⟩,hA,hV⟩,hσvalue⟩
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "vm.left") ((0:Nat)); let c1:Prop:=Not c0; let c2:Cond:=Cond.eq (Expr.var "vm.left") (Expr.lit ((0:Nat))); let c3:Com:=Com.ite c2 (Com.assign "vm.pc" (Expr.lit label)) increment; let c4:Env→ Nat→ Prop:=Run B c3 σ; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Env→ Prop:=Core w (@ite Nat (@Eq Nat value ((0:Nat))) (instDecidableEqNat value ((0:Nat))) label (c5 pc ((1:Nat)))) m; let c7:Env→ Prop:=(fun (x τ:Env) => c6 τ) σ; let c8:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((8:Nat))) (c7 σ'); let c9:Nat→ Nat:=c5 ((1:Nat)); let c10:Nat→ Nat:=c5 (c9 (Cond.size c2)); let c11:Nat:=c9 (Expr.size (Expr.lit label)); let c12:Nat:=c5 (Env.vars σ "vm.pc") ((1:Nat)); let c13:Env:=Env.setVar σ "vm.pc" c12; let c14:Expr:=Expr.add (Expr.var "vm.pc") (Expr.lit ((1:Nat))); let c15:Nat:=c9 (Expr.size c14); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c8) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c8 (Env.setVar σ "vm.pc" label) (@And.intro (c4 (Env.setVar σ "vm.pc" label) ((8:Nat))) (c7 (Env.setVar σ "vm.pc" label)) (RunStep.mono B c3 σ (Env.setVar σ "vm.pc" label) (c10 c11) ((8:Nat)) (RunStep.ite_true B c2 (Com.assign "vm.pc" (Expr.lit label)) increment σ (Env.setVar σ "vm.pc" label) c11 (RunStep.cond_eq_true B σ (Expr.var "vm.left") (Expr.lit ((0:Nat))) (Env.vars σ "vm.left") ((0:Nat)) (RunStep.eval_var B σ "vm.left" (?nAX_g5980_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5980_0_0_1)) hcase) (RunStep.assign B σ "vm.pc" (Expr.lit label) label (RunStep.eval_lit B label σ hlabel))) (?nAX_g5980_0_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c8 c13 (@And.intro (c4 c13 ((8:Nat))) (c7 c13) (RunStep.mono B c3 σ c13 (c10 c15) ((8:Nat)) (RunStep.ite_false B c2 (Com.assign "vm.pc" (Expr.lit label)) increment σ c13 c15 (RunStep.cond_eq_false B σ (Expr.var "vm.left") (Expr.lit ((0:Nat))) (Env.vars σ "vm.left") ((0:Nat)) (RunStep.eval_var B σ "vm.left" (?nAX_g5980_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5980_0_0_4)) hcase) (RunStep.assign B σ "vm.pc" c14 c12 (RunStep.eval_add B σ (Expr.var "vm.pc") (Expr.lit ((1:Nat))) (Env.vars σ "vm.pc") ((1:Nat)) (RunStep.eval_var B σ "vm.pc" (?nAX_g5980_0_0_5)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5980_0_0_6)))) (?nAX_g5980_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5980_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5980_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Core,RamSparseRead.Representation]
  have h:=operand_spec B w pc m a _ 8 _ h1 hM ha hlen hwords hbody
  simpa only [instruction,Nat.add_assoc,Nat.reduceAdd,value] using h

theorem jeof_spec (B w:ℕ) (s:SparseRam.SparseState) (label:ℕ)
    (hlabel:label < B) (hlen:s.input.length < B) (hpc:s.pc + 1 < B) (h1:1 < B):
    Spec B (Represents w s) (instruction (.jeof label))
      (fun _ τ => Represents w { s with pc:=if s.inp.isEmpty then label else s.pc + 1 } τ) 8:=by
  rintro σ ⟨hcore,htapes⟩
  have hcursorB:=htapes.2.2.1.trans_lt hlen
  have heof:=empty_iff_cursor s σ htapes
  have hinputlen:=htapes.2.1
  have hpcσ:=hcore.2.1
  have hnil:s.inp.isEmpty=true↔ σ.vars "vm.cursor"=σ.vars "vm.inputLength" :=by
    simpa only [List.isEmpty_iff,hinputlen] using heof
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "vm.cursor") (Env.vars σ "vm.inputLength"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Env→ Prop:=Represents w (SparseRam.SparseState.mk (@ite Nat (@Eq Bool (@List.isEmpty Nat (SparseRam.SparseState.inp s)) true) (instDecidableEqBool (@List.isEmpty Nat (SparseRam.SparseState.inp s)) true) label (c2 (SparseRam.SparseState.pc s) ((1:Nat)))) (SparseRam.SparseState.memory s) (SparseRam.SparseState.input s) (SparseRam.SparseState.inp s) (SparseRam.SparseState.out s)); let c4:Env→ Prop:=(fun (x τ:Env) => c3 τ) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B (instruction (Lax808846.Ram.Instr.jeof label)) σ σ' ((8:Nat))) (c4 σ'); let c6:Nat→ Nat:=c2 ((1:Nat)); let c7:Nat→ Nat:=c2 (c6 (Cond.size (Cond.eq (Expr.var "vm.cursor") (Expr.var "vm.inputLength")))); let c8:Nat:=c6 (Expr.size (Expr.lit label)); let c9:Nat:=c2 (Env.vars σ "vm.pc") ((1:Nat)); let c10:Env:=Env.setVar σ "vm.pc" c9; let c11:Expr:=Expr.add (Expr.var "vm.pc") (Expr.lit ((1:Nat))); let c12:Nat:=c6 (Expr.size c11); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c5 (Env.setVar σ "vm.pc" label) (@And.intro (Run B (instruction (Lax808846.Ram.Instr.jeof label)) σ (Env.setVar σ "vm.pc" label) ((8:Nat))) (c4 (Env.setVar σ "vm.pc" label)) (RunStep.mono B (instruction (Lax808846.Ram.Instr.jeof label)) σ (Env.setVar σ "vm.pc" label) (c7 c8) ((8:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "vm.cursor") (Expr.var "vm.inputLength")) (Com.assign "vm.pc" (Expr.lit label)) increment σ (Env.setVar σ "vm.pc" label) c8 (RunStep.cond_eq_true B σ (Expr.var "vm.cursor") (Expr.var "vm.inputLength") (Env.vars σ "vm.cursor") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.cursor" hcursorB) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5981_0_0_0)) hcase) (RunStep.assign B σ "vm.pc" (Expr.lit label) label (RunStep.eval_lit B label σ hlabel))) (?nAX_g5981_0_0_1)) ?_)) fun (hcase:c1) => @Exists.intro Env c5 c10 (@And.intro (Run B (instruction (Lax808846.Ram.Instr.jeof label)) σ c10 ((8:Nat))) (c4 c10) (RunStep.mono B (instruction (Lax808846.Ram.Instr.jeof label)) σ c10 (c7 c12) ((8:Nat)) (RunStep.ite_false B (Cond.eq (Expr.var "vm.cursor") (Expr.var "vm.inputLength")) (Com.assign "vm.pc" (Expr.lit label)) increment σ c10 c12 (RunStep.cond_eq_false B σ (Expr.var "vm.cursor") (Expr.var "vm.inputLength") (Env.vars σ "vm.cursor") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.cursor" hcursorB) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5981_0_0_2)) hcase) (RunStep.assign B σ "vm.pc" c11 c9 (RunStep.eval_add B σ (Expr.var "vm.pc") (Expr.lit ((1:Nat))) (Env.vars σ "vm.pc") ((1:Nat)) (RunStep.eval_var B σ "vm.pc" (?nAX_g5981_0_0_3)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5981_0_0_4)))) (?nAX_g5981_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5981_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5981_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5981_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5981_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5981_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5981_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Core,Tapes,Prefix,RamSparseRead.Representation]

end Lax455465Proofs.RamVirtualControl

end

section

namespace Lax455465Proofs.RamVirtualIndirect

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamFrames

theorem load_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a b:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hb:b < B)
    (hwords:SparseBounds.MemoryWords w m) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (Working w pc m) (instruction (.load a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (SparseRam.lookup m (SparseRam.lookup m (b % 2 ^ w) % 2 ^ w))) τ)
      (32 * m.length + 76):=by
  let address:=SparseRam.lookup m (b % 2 ^ w)
  let value:=SparseRam.lookup m (address % 2 ^ w)
  have haddress:=SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hvalue:=(SparseBounds.lookup_bound w m (address % 2 ^ w) hwords).trans hM
  have hread0:=read_expression_spec B w pc m (address % 2 ^ w) "vm.result"
    (remainder (.var "vm.left")) h1 hM
    ((Nat.mod_lt _ (Nat.two_pow_pos w)).trans hM) (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread:=hread0.mono (show 16 * m.length + (remainder (.var "vm.left")).size + 11≤
      16 * m.length + 18 by simp [remainder,Expr.size])
  have hread':=keep_space (keep_space hread "vm.addresses" m.length) "vm.values" m.length
  have hfinish:=writeBack_register_spec B w pc m a value h1 hM ha hvalue hpc hlen
  have hbody:Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.left"=address)
      (.seq (RamSparseRead.read "vm.result" (remainder (.var "vm.left")))
        (writeBack (.lit a) (.var "vm.result")))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a value) τ) (16 * m.length + 58):=by
    rintro σ ⟨⟨hcore,hA,hV⟩,hleft⟩
    have he:(remainder (.var "vm.left")).evalB B σ=some (address % 2 ^ w):=
      evalB_remainder (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ haddress.trans hM⟩)
        hcore.2.2.1 hM (haddress.trans hM)
    (expose_names;
      (refine let c0:Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.result" (remainder (Expr.var "vm.left"))) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat:=c1 (Nat.mul ((16:Nat)) (@List.length (Prod Nat Nat) m)); let c3:Nat:=c2 ((18:Nat)); let c4:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) address (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w); let c5:Nat:=SparseRam.lookup m c4; let c6:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c7:Env→ Prop:=fun (σ':Env) => And (c0 σ' c3) (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.result") c5)) (c6 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c6 (@List.length Nat (Env.arrs σ' "vm.values")))); let c8:Com:=Com.seq (RamSparseRead.read "vm.result" (remainder (Expr.var "vm.left"))) (writeBack (Expr.lit a) (Expr.var "vm.result")); let c9:Env→ Nat→ Prop:=Run B c8 σ; let c10:Nat:=c2 ((58:Nat)); let c11:Env→ Prop:=Core w (c1 pc ((1:Nat))) (SparseRam.write w m a value); let c12:Env→ Env→ Prop:=fun (x τ:Env) => c11 τ; let c13:Env→ Prop:=c12 σ; let c14:Env→ Prop:=fun (σ':Env) => And (c9 σ' c10) (c13 σ'); let c15:Option Nat:= @some Nat c4; let c16:Env→ Env→ Nat→ Prop:=Run B (writeBack (Expr.lit a) (Expr.var "vm.result")); @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => @Exists Env c14) (RunStep.use B (fun (σ_1:Env) => And (And (And (Core w pc m σ_1) (@Eq (Option Nat) (Expr.evalB B (remainder (Expr.var "vm.left")) σ_1) c15)) (c6 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c6 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.result" (remainder (Expr.var "vm.left"))) (fun (σ_1 τ:Env) => And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.result") c5)) (c6 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c6 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hread' σ ?_) fun (w_1:Env) (h:And (c0 w_1 c3) (And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.result") c5)) (c6 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c6 (@List.length Nat (Env.arrs w_1 "vm.values"))))) => let c0_1:Prop:=And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.result") c5)) (c6 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c6 (@List.length Nat (Env.arrs w_1 "vm.values"))); let c1_1:Env→ Prop:=fun (σ':Env) => And (c16 w_1 σ' ((40:Nat))) (c11 σ'); @And.casesOn (c0 w_1 c3) c0_1 (fun (x:And (c0 w_1 c3) c0_1) => @Exists Env c14) h fun (left:c0 w_1 c3) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c14) (RunStep.use B (fun (σ_1:Env) => And (Core w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.result") value) (And (c6 (@List.length Nat (Env.arrs σ_1 "vm.addresses"))) (c6 (@List.length Nat (Env.arrs σ_1 "vm.values")))))) (writeBack (Expr.lit a) (Expr.var "vm.result")) c12 ((40:Nat)) hfinish w_1 ?_) fun (w_2:Env) (h_1:And (c16 w_1 w_2 ((40:Nat))) (c11 w_2)) => let c0_2:Prop:=c16 w_1 w_2 ((40:Nat)); @And.casesOn c0_2 (c11 w_2) (fun (x:And c0_2 (c11 w_2)) => @Exists Env c14) h_1 fun (left_1:c0_2) (right_1:c11 w_2) => @Exists.intro Env c14 w_2 (@And.intro (c9 w_2 c10) (c13 w_2) (RunStep.mono B c8 σ w_2 (c1 c3 ((40:Nat))) c10 (RunStep.seq B (RamSparseRead.read "vm.result" (remainder (Expr.var "vm.left"))) (writeBack (Expr.lit a) (Expr.var "vm.result")) σ w_1 w_2 c3 ((40:Nat)) left left_1) (?nAX_g5982_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5982_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals simp_all [value]
  have h:=operand_spec B w pc m b _ (16 * m.length + 58) _ h1 hM hb (by omega) hwords hbody
  exact h.mono (by omega)

theorem store_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (a b:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hb:b < B)
    (hwords:SparseBounds.MemoryWords w m) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (Working w pc m) (instruction (.store a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m
        (SparseRam.lookup m (a % 2 ^ w)) (SparseRam.lookup m (b % 2 ^ w))) τ)
      (32 * m.length + 76):=by
  let address:=SparseRam.lookup m (a % 2 ^ w)
  let value:=SparseRam.lookup m (b % 2 ^ w)
  have haddress:=(SparseBounds.lookup_bound w m (a % 2 ^ w) hwords).trans hM
  have hvalue:=(SparseBounds.lookup_bound w m (b % 2 ^ w) hwords).trans hM
  have hgetA:=read_literal_spec B w pc m a "vm.target" h1 hM ha (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hgetB:=keep_scalar (read_literal_spec B w pc m b "vm.result" h1 hM hb (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)) "vm.target" address
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
  have hleft:=keep_space (keep_space hgetA "vm.addresses" m.length) "vm.values" m.length
  have hright:=keep_space (keep_space hgetB "vm.addresses" m.length) "vm.values" m.length
  have hbase:=writeBack_general_spec B w pc m address value (.var "vm.target") (.var "vm.result")
    h1 hM haddress hvalue hpc hlen
  have hfinish:Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.target"=address∧ σ.vars "vm.result"=value)
      (writeBack (.var "vm.target") (.var "vm.result"))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m address value) τ) 40:=
    (hbase.pre (by
      rintro σ ⟨⟨hcore,hA,hV⟩,htarget,hσvalue⟩
      refine ⟨hcore,hA,hV, ?_, ?_⟩
      · rw [evalB_var_iff]
        exact ⟨htarget.symm,htarget ▸ haddress⟩
      · rw [evalB_var_iff]
        simp only [vars_setVar,String.reduceEq,if_false]
        exact ⟨hσvalue.symm,hσvalue ▸ hvalue⟩)).mono (by decide)
  rintro σ ⟨hcore,hA,hV⟩
  simp only [instruction]
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.target" (remainder (Expr.lit a))) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c1 (c2 ((16:Nat)) (@List.length (Prod Nat Nat) m)) ((18:Nat)); let c4:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c5:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w; let c6:Nat:=SparseRam.lookup m (c4 a c5); let c7:Nat→ Prop:=Nat.lt (@List.length (Prod Nat Nat) m); let c8:Env→ Prop:=fun (σ':Env) => And (c0 σ' c3) (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.target") c6)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); let c9:Com:=Com.seq (RamSparseRead.read "vm.result" (remainder (Expr.lit b))) (writeBack (Expr.var "vm.target") (Expr.var "vm.result")); let c10:Com:=Com.seq (RamSparseRead.read "vm.target" (remainder (Expr.lit a))) c9; let c11:Env→ Nat→ Prop:=Run B c10 σ; let c12:Nat:=c1 (c2 ((32:Nat)) (@List.length (Prod Nat Nat) m)) ((76:Nat)); let c13:SparseRam.Memory→ Env→ Prop:=Core w (c1 pc ((1:Nat))); let c14:Nat:=SparseRam.lookup m (c4 b c5); let c15:Env→ Prop:=c13 (SparseRam.write w m c6 c14); let c16:Env→ Prop:=fun (σ':Env) => And (c11 σ' c12) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Env→ Env→ Nat→ Prop:=Run B (RamSparseRead.read "vm.result" (remainder (Expr.lit b))); let c19:Env→ Env→ Nat→ Prop:=Run B (writeBack (Expr.var "vm.target") (Expr.var "vm.result")); let c20:Env→ Prop:=c13 (SparseRam.write w m address value); let c21:Nat→ Nat:=c1 c3; let c22:Nat:=c21 ((40:Nat)); @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c17) (RunStep.use B (fun (σ_1:Env) => And (And (Core w pc m σ_1) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.target" (remainder (Expr.lit a))) (fun (σ_1 τ:Env) => And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.target") c6)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hleft σ ?_) fun (w_1:Env) (h:And (c0 w_1 c3) (And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.target") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))))) => let c0_1:Prop:=And (And (And (Core w pc m w_1) (@Eq Nat (Env.vars w_1 "vm.target") c6)) (c7 (@List.length Nat (Env.arrs w_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_1 "vm.values"))); let c1_1:Env→ Prop:=fun (σ':Env) => And (c18 w_1 σ' c3) (And (And (And (And (Core w pc m σ') (@Eq Nat (Env.vars σ' "vm.result") c14)) (@Eq Nat (Env.vars σ' "vm.target") address)) (c7 (@List.length Nat (Env.arrs σ' "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ' "vm.values")))); @And.casesOn (c0 w_1 c3) c0_1 (fun (x:And (c0 w_1 c3) c0_1) => c17) h fun (left:c0 w_1 c3) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c17) (RunStep.use B (fun (σ_1:Env) => And (And (And (Core w pc m σ_1) (@Eq Nat (Env.vars σ_1 "vm.target") address)) (c7 (@List.length Nat (Env.arrs σ_1 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs σ_1 "vm.values")))) (RamSparseRead.read "vm.result" (remainder (Expr.lit b))) (fun (σ_1 τ:Env) => And (And (And (And (Core w pc m τ) (@Eq Nat (Env.vars τ "vm.result") c14)) (@Eq Nat (Env.vars τ "vm.target") address)) (c7 (@List.length Nat (Env.arrs τ "vm.addresses")))) (c7 (@List.length Nat (Env.arrs τ "vm.values")))) c3 hright w_1 ?_) fun (w_2:Env) (h_1:And (c18 w_1 w_2 c3) (And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.result") c14)) (@Eq Nat (Env.vars w_2 "vm.target") address)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))))) => let c0_2:Prop:=And (And (And (And (Core w pc m w_2) (@Eq Nat (Env.vars w_2 "vm.result") c14)) (@Eq Nat (Env.vars w_2 "vm.target") address)) (c7 (@List.length Nat (Env.arrs w_2 "vm.addresses")))) (c7 (@List.length Nat (Env.arrs w_2 "vm.values"))); let c1_2:Env→ Prop:=fun (σ':Env) => And (c19 w_2 σ' ((40:Nat))) (c20 σ'); @And.casesOn (c18 w_1 w_2 c3) c0_2 (fun (x:And (c18 w_1 w_2 c3) c0_2) => c17) h_1 fun (left_1:c18 w_1 w_2 c3) (right_1:c0_2) => @Exists.casesOn Env c1_2 (fun (x:@Exists Env c1_2) => c17) (RunStep.use B (fun (σ_1:Env) => And (Working w pc m σ_1) (And (@Eq Nat (Env.vars σ_1 "vm.target") address) (@Eq Nat (Env.vars σ_1 "vm.result") value))) (writeBack (Expr.var "vm.target") (Expr.var "vm.result")) (fun (x τ:Env) => c20 τ) ((40:Nat)) hfinish w_2 ?_) fun (w_3:Env) (h_2:And (c19 w_2 w_3 ((40:Nat))) (c20 w_3)) => let c0_3:Prop:=c19 w_2 w_3 ((40:Nat)); @And.casesOn c0_3 (c20 w_3) (fun (x:And c0_3 (c20 w_3)) => c17) h_2 fun (left_2:c0_3) (right_2:c20 w_3) => @Exists.intro Env c16 w_3 (@And.intro (c11 w_3 c12) (c15 w_3) (RunStep.mono B c10 σ w_3 (c21 c22) c12 (RunStep.seq B (RamSparseRead.read "vm.target" (remainder (Expr.lit a))) c9 σ w_1 w_3 c3 c22 left (RunStep.seq B (RamSparseRead.read "vm.result" (remainder (Expr.lit b))) (writeBack (Expr.var "vm.target") (Expr.var "vm.result")) w_1 w_2 w_3 c3 ((40:Nat)) left_1 left_2)) (?nAX_g5983_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5983_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals simp_all [Working,address,value]

end Lax455465Proofs.RamVirtualIndirect

end

section

namespace Lax455465Proofs.RamVirtualInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState RamFrames

def indexed:Com:=.ite (.lt (.var "vm.left") (.var "vm.inputLength"))
  (.assign "vm.result" (.get "vm.input" (.var "vm.left"))) (.assign "vm.result" (.lit 0))

theorem indexed_spec (B index:ℕ) (input:List ℕ) (hiB:index < B)
    (hlen:input.length < B) (hwords:∀ x∈ input,x < B):
    Spec B (fun σ => σ.vars "vm.left"=index∧ σ.vars "vm.inputLength"=input.length∧
      Prefix input "vm.input" σ) indexed
      (fun _ τ => τ.vars "vm.result"=input[index]?.getD 0) 7:=by
  rintro σ ⟨hindex,hlength,hprefix⟩
  have h0:0 < B:=by omega
  by_cases hi:index < input.length
  · have hget:=hprefix index hi
    have hv:=hwords input[index] (List.getElem_mem hi)
    have harray:index < (σ.arrs "vm.input").length:=by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hget
      cases hget
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength"); let c1:Prop:=Not c0; let c2:Nat:= @Option.getD Nat (@getElem? (List Nat) Nat Nat (fun (as:List Nat) (i:Nat) => Nat.lt i (@List.length Nat as)) (@List.instGetElem?NatLtLength Nat) input index) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B indexed σ σ' ((7:Nat))) (c3 σ'); let c5:Nat:= @List.getD Nat (Env.arrs σ "vm.input") (Env.vars σ "vm.left") ((0:Nat)); let c6:Env:=Env.setVar σ "vm.result" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat→ Nat:=c7 (c8 (Cond.size (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")))); let c10:Nat:=c8 (Expr.size (Expr.get "vm.input" (Expr.var "vm.left"))); let c11:Com:=Com.assign "vm.result" (Expr.lit ((0:Nat))); let c12:Env:=Env.setVar σ "vm.result" ((0:Nat)); let c13:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c6 (@And.intro (Run B indexed σ c6 ((7:Nat))) (c3 c6) (RunStep.mono B indexed σ c6 (c9 c10) ((7:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")) (Com.assign "vm.result" (Expr.get "vm.input" (Expr.var "vm.left"))) c11 σ c6 c10 (RunStep.cond_lt_true B σ (Expr.var "vm.left") (Expr.var "vm.inputLength") (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_0_0_0)) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5985_0_0_1)) hcase) (RunStep.assign B σ "vm.result" (Expr.get "vm.input" (Expr.var "vm.left")) c5 (RunStep.eval_get B σ "vm.input" (Expr.var "vm.left") (Env.vars σ "vm.left") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_0_0_2)) (?nAX_g5985_0_0_3) ?_))) (?nAX_g5985_0_0_4)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c12 (@And.intro (Run B indexed σ c12 ((7:Nat))) (c3 c12) (RunStep.mono B indexed σ c12 (c9 c13) ((7:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")) (Com.assign "vm.result" (Expr.get "vm.input" (Expr.var "vm.left"))) c11 σ c12 c13 (RunStep.cond_lt_false B σ (Expr.var "vm.left") (Expr.var "vm.inputLength") (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_0_0_5)) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5985_0_0_6)) hcase) (RunStep.assign B σ "vm.result" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ h0))) (?nAX_g5985_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5985_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  · have hget:input[index]?=none:=List.getElem?_eq_none (by omega)
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength"); let c1:Prop:=Not c0; let c2:Nat:= @Option.getD Nat (@getElem? (List Nat) Nat Nat (fun (as:List Nat) (i:Nat) => Nat.lt i (@List.length Nat as)) (@List.instGetElem?NatLtLength Nat) input index) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "vm.result") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B indexed σ σ' ((7:Nat))) (c3 σ'); let c5:Nat:= @List.getD Nat (Env.arrs σ "vm.input") (Env.vars σ "vm.left") ((0:Nat)); let c6:Env:=Env.setVar σ "vm.result" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat→ Nat:=c7 (c8 (Cond.size (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")))); let c10:Nat:=c8 (Expr.size (Expr.get "vm.input" (Expr.var "vm.left"))); let c11:Com:=Com.assign "vm.result" (Expr.lit ((0:Nat))); let c12:Env:=Env.setVar σ "vm.result" ((0:Nat)); let c13:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c6 (@And.intro (Run B indexed σ c6 ((7:Nat))) (c3 c6) (RunStep.mono B indexed σ c6 (c9 c10) ((7:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")) (Com.assign "vm.result" (Expr.get "vm.input" (Expr.var "vm.left"))) c11 σ c6 c10 (RunStep.cond_lt_true B σ (Expr.var "vm.left") (Expr.var "vm.inputLength") (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_1_0_0)) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5985_1_0_1)) hcase) (RunStep.assign B σ "vm.result" (Expr.get "vm.input" (Expr.var "vm.left")) c5 (RunStep.eval_get B σ "vm.input" (Expr.var "vm.left") (Env.vars σ "vm.left") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_1_0_2)) (?nAX_g5985_1_0_3) (?nAX_g5985_1_0_4)))) (?nAX_g5985_1_0_5)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c12 (@And.intro (Run B indexed σ c12 ((7:Nat))) (c3 c12) (RunStep.mono B indexed σ c12 (c9 c13) ((7:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "vm.left") (Expr.var "vm.inputLength")) (Com.assign "vm.result" (Expr.get "vm.input" (Expr.var "vm.left"))) c11 σ c12 c13 (RunStep.cond_lt_false B σ (Expr.var "vm.left") (Expr.var "vm.inputLength") (Env.vars σ "vm.left") (Env.vars σ "vm.inputLength") (RunStep.eval_var B σ "vm.left" (?nAX_g5985_1_0_6)) (RunStep.eval_var B σ "vm.inputLength" (?nAX_g5985_1_0_7)) hcase) (RunStep.assign B σ "vm.result" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ h0))) (?nAX_g5985_1_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5985_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5985_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all <;> omega

theorem length_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (inputLength a:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hinput:inputLength < B)
    (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Working w pc m σ∧ σ.vars "vm.inputLength"=inputLength)
      (instruction (.inputLength a))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a inputLength) τ) 40:=by
  have hbase:=writeBack_general_spec B w pc m a inputLength (.lit a) (.var "vm.inputLength")
    h1 hM ha hinput hpc hlen
  apply (hbase.pre ?_).mono (by simp [Expr.size])
  rintro σ ⟨⟨hcore,hA,hV⟩,hσlen⟩
  refine ⟨hcore,hA,hV,evalB_lit ha, ?_⟩
  rw [evalB_var_iff]
  simp only [vars_setVar,String.reduceEq,if_false]
  exact ⟨hσlen.symm,hσlen ▸ hinput⟩

theorem load_core_spec (B w pc:ℕ) (m:SparseRam.Memory) (input:List ℕ) (a b:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hb:b < B)
    (hinput:input.length < B) (hinputWords:∀ x∈ input,x < B)
    (hwords:SparseBounds.MemoryWords w m) (hpc:pc + 1 < B) (hlen:m.length + 1 < B):
    Spec B (fun σ => Working w pc m σ∧ Prefix input "vm.input" σ∧ σ.vars "vm.inputLength"=input.length)
      (instruction (.inputLoad a b))
      (fun _ τ => Core w (pc + 1) (SparseRam.write w m a
        (input[SparseRam.lookup m (b % 2 ^ w) % 2 ^ w]?.getD 0)) τ) (16 * m.length + 65):=by
  let index:=SparseRam.lookup m (b % 2 ^ w)
  have hi:=SparseBounds.lookup_bound w m (b % 2 ^ w) hwords
  have hiB:=hi.trans hM
  have hvalue:input[index]?.getD 0 < B:=by
    by_cases hindex:index < input.length
    · simpa only [List.getElem?_eq_getElem hindex,Option.getD_some] using
        hinputWords input[index] (List.getElem_mem hindex)
    · simp only [List.getElem?_eq_none (by omega:input.length≤ index),Option.getD_none]
      omega
  have hindexed:=indexed_spec B index input hiB hinput hinputWords
  have hbase:=RamVirtualStage.result_spec B w pc m a (input[index]?.getD 0) indexed 7 _ hindexed
    (by simp [indexed,Com.warrs])
    (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [indexed,Com.wvars])
    h1 hM ha hvalue hpc hlen
  have hget:=read_literal_spec B w pc m b "vm.left" h1 hM hb (by omega) hwords
    (by decide) (by decide) (by decide) (by decide)
  have hread:=keep_space (keep_space hget "vm.addresses" m.length) "vm.values" m.length

  rintro σ ⟨⟨hcore,hA,hV⟩,hprefix,hlength⟩
  obtain ⟨ν,hr,hpost⟩:=hread σ ⟨⟨hcore,hA⟩,hV⟩
  have hinputArr:=hr.frame_arr "vm.input" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.warrs])
  have hinputLen:=hr.frame_var "vm.inputLength" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
  have hpν:Prefix input "vm.input" ν:=by simpa only [Prefix,hinputArr] using hprefix
  have hlν:ν.vars "vm.inputLength"=input.length:=hinputLen.trans hlength
  obtain ⟨τ,hstage,hfinal⟩:=hbase ν ⟨⟨hpost.1.1.1,hpost.1.2,hpost.2⟩,
    hpost.1.1.2,hlν,hpν⟩
  refine ⟨τ, (hr.seq hstage).mono ?_, ?_⟩
  · omega
  · simpa only [instruction,indexed,index,Nat.mod_eq_of_lt hi] using hfinal

end Lax455465Proofs.RamVirtualInput

end

section

namespace Lax455465Proofs.RamVirtualRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState

def advance:Com:=.seq (.assign "vm.result" (.get "vm.input" (.var "vm.cursor")))
  (.assign "vm.cursor" (.add (.var "vm.cursor") (.lit 1)))

theorem advance_spec (B w:ℕ) (s:SparseRam.SparseState) (value:ℕ) (rest:List ℕ)
    (h1:1 < B) (hlen:s.input.length < B) (hwords:∀ x∈ s.input,x < B)
    (hread:s.inp=value::rest):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1) advance
      (fun _ τ => Represents w { s with inp:=rest } τ∧ τ.vars "vm.result"=value∧
        τ.vars "vm.running"=1) 7:=by
  rintro σ ⟨⟨hcore,htapes⟩,hrunning⟩
  have hcursor:=htapes.2.2.1
  have hpos:σ.vars "vm.cursor" < s.input.length:=by
    have hempty:=empty_iff_cursor s σ htapes
    have hne:s.inp ≠ []:=by rw [hread]; simp
    exact Nat.lt_of_le_of_ne hcursor (fun he => hne (hempty.mpr he))
  have hdrop:s.input.drop (σ.vars "vm.cursor") =
      s.input[σ.vars "vm.cursor"]::s.input.drop (σ.vars "vm.cursor" + 1):=
    List.cons_getElem_drop_succ.symm
  have heq:value::rest=s.input[σ.vars "vm.cursor"]::s.input.drop (σ.vars "vm.cursor" + 1):=
    hread.symm.trans (htapes.2.2.2.1.trans hdrop)
  have hhead:=(List.cons.inj heq).1
  have htail:=(List.cons.inj heq).2
  have hv:value < B:=hhead ▸ hwords s.input[σ.vars "vm.cursor"] (List.getElem_mem hpos)
  have hget:(σ.arrs "vm.input")[σ.vars "vm.cursor"]?=some value:=by
    rw [htapes.1 _ hpos, ← hhead]
  have harray:σ.vars "vm.cursor" < (σ.arrs "vm.input").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  clear hdrop heq
  (expose_names;
    (refine let c0:Env→ Prop:=Represents w (SparseRam.SparseState.mk (SparseRam.SparseState.pc s) (SparseRam.SparseState.memory s) (SparseRam.SparseState.input s) rest (SparseRam.SparseState.out s)); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (And (@Eq Nat (Env.vars τ "vm.result") value) (@Eq Nat (Env.vars τ "vm.running") ((1:Nat))))) σ; let c2:Nat:= @List.getD Nat (Env.arrs σ "vm.input") (Env.vars σ "vm.cursor") ((0:Nat)); let c3:Env:=Env.setVar σ "vm.result" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=Env.vars c3 "vm.cursor"; let c6:Nat:=c4 c5 ((1:Nat)); let c7:Env:=Env.setVar c3 "vm.cursor" c6; let c8:Nat→ Nat:=c4 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.get "vm.input" (Expr.var "vm.cursor"))); let c10:Expr:=Expr.add (Expr.var "vm.cursor") (Expr.lit ((1:Nat))); let c11:Nat:=c8 (Expr.size c10); let c12:String→ Nat:=Env.vars c7; @Exists.intro Env (fun (σ':Env) => And (Run B advance σ σ' ((7:Nat))) (c1 σ')) c7 (@And.intro (Run B advance σ c7 ((7:Nat))) (c1 c7) (RunStep.mono B advance σ c7 (c4 c9 c11) ((7:Nat)) (RunStep.seq B (Com.assign "vm.result" (Expr.get "vm.input" (Expr.var "vm.cursor"))) (Com.assign "vm.cursor" c10) σ c3 c7 c9 c11 (RunStep.assign B σ "vm.result" (Expr.get "vm.input" (Expr.var "vm.cursor")) c2 (RunStep.eval_get B σ "vm.input" (Expr.var "vm.cursor") (Env.vars σ "vm.cursor") (RunStep.eval_var B σ "vm.cursor" (?nAX_g5989_0_0_0)) harray ?_)) (RunStep.assign B c3 "vm.cursor" c10 c6 (RunStep.eval_add B c3 (Expr.var "vm.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c3 "vm.cursor" (?nAX_g5989_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c3 h1) (?nAX_g5989_0_0_2)))) (?nAX_g5989_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5989_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5989_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5989_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5989_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Core,Tapes,Prefix,RamSparseRead.Representation]

theorem empty_spec (B w:ℕ) (s:SparseRam.SparseState) (a:ℕ)
    (hB:0 < B) (hlen:s.input.length < B) (he:s.inp=[]):
    Spec B (Represents w s) (instruction (.read a))
      (fun _ τ => Represents w s τ∧ τ.vars "vm.running"=0) 6:=by
  have hstop:=stop_spec B w s hB
  rintro σ ⟨hcore,htapes⟩
  have hcursor:=(empty_iff_cursor s σ htapes).mp he
  have hinputlen:=htapes.2.1
  obtain ⟨τ,hrun,hpost⟩:=hstop σ ⟨hcore,htapes⟩
  have hbranch:(Cond.lt (.var "vm.cursor") (.var "vm.inputLength")).evalB B σ=some false:=by
    rw [evalB_condLt_iff]
    exact ⟨s.input.length,s.input.length,
      by rw [evalB_var_iff]; exact ⟨hcursor.symm,hcursor ▸ hlen⟩,
      by rw [evalB_var_iff]; exact ⟨hinputlen.symm,hinputlen ▸ hlen⟩,by simp⟩
  exact ⟨τ, (Run.ite_false hbranch hrun).mono (by simp [Cond.size,Expr.size]),hpost⟩

theorem nonempty_spec (B w:ℕ) (s:SparseRam.SparseState) (a value:ℕ) (rest:List ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B) (hinput:s.input.length < B)
    (hwords:∀ x∈ s.input,x < B) (hread:s.inp=value::rest)
    (hpc:s.pc + 1 < B) (hmem:s.memory.length + 1 < B):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧
      s.memory.length < (σ.arrs "vm.addresses").length∧ s.memory.length < (σ.arrs "vm.values").length)
      (instruction (.read a))
      (fun _ τ => Represents w { SparseRam.assign w s a value with inp:=rest } τ∧
        τ.vars "vm.running"=1) 51:=by
  rintro σ ⟨⟨hcore,htapes⟩,hrunning,hA,hV⟩
  have hcursor:σ.vars "vm.cursor" < s.input.length:=by
    have hempty:=empty_iff_cursor s σ htapes
    have hne:s.inp ≠ []:=by rw [hread]; simp
    have hb:=htapes.2.2.1
    exact Nat.lt_of_le_of_ne hb (fun he => hne (hempty.mpr he))
  have hv:value < B:=by
    apply hwords value
    rw [htapes.2.2.2.1] at hread
    exact List.mem_of_mem_drop (hread ▸ List.mem_cons_self)
  have hadvance:=advance_spec B w s value rest h1 hinput hwords hread
  obtain ⟨ν,hadvance,hpost⟩:=hadvance σ ⟨⟨hcore,htapes⟩,hrunning⟩
  have hAν:s.memory.length < (ν.arrs "vm.addresses").length:=by
    rwa [RamFrames.run_array_length hadvance "vm.addresses"]
  have hVν:s.memory.length < (ν.arrs "vm.values").length:=by
    rwa [RamFrames.run_array_length hadvance "vm.values"]
  obtain ⟨τ,hwrite,hfinal⟩:=writeBack_register_spec B w s.pc s.memory a value h1 hM ha hv hpc hmem
    ν ⟨hpost.1.1,hpost.2.1,hAν,hVν⟩
  have htapesτ:=tapes_frame hwrite { s with inp:=rest } hpost.1.2
    (by simp [writeBack,RamSparseRead.write,RamSparseMemory.put,increment,Com.warrs])
    (by simp [writeBack,RamSparseRead.write,RamSparseMemory.put,increment,Com.warrs])
    (by simp [writeBack,RamSparseRead.write,RamSparseMemory.put,increment,Com.wvars])
    (by simp [writeBack,RamSparseRead.write,RamSparseMemory.put,increment,Com.wvars])
    (by simp [writeBack,RamSparseRead.write,RamSparseMemory.put,increment,Com.wvars])
  have hrunningτ:=(hwrite.frame_var "vm.running" (by simp [writeBack,
    RamSparseRead.write,RamSparseMemory.put,increment,Com.wvars])).trans hpost.2.2
  have hbranch:(Cond.lt (.var "vm.cursor") (.var "vm.inputLength")).evalB B σ=some true:=by
    rw [evalB_condLt_iff]
    exact ⟨σ.vars "vm.cursor",s.input.length,evalB_var (hcursor.trans hinput),
      by rw [evalB_var_iff]; exact ⟨htapes.2.1.symm,htapes.2.1 ▸ hinput⟩,
      by simp [hcursor]⟩
  refine ⟨τ, (Run.ite_true hbranch (hadvance.seq hwrite)).mono ?_, ⟨hfinal,htapesτ⟩,hrunningτ⟩
  · simp [Cond.size,Expr.size]

end Lax455465Proofs.RamVirtualRead

end

section

namespace Lax455465Proofs.RamVirtualOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState

private theorem prefix_append (words buffer:List ℕ) (value:ℕ)
    (h:∀ i (hi:i < words.length),buffer[i]?=some words[i])
    (hroom:words.length < buffer.length):
    ∀ i (hi:i < (words ++ [value]).length),
      (buffer.set words.length value)[i]?=some (words ++ [value])[i]:=by
  intro i hi
  by_cases hlt:i < words.length
  · rw [← List.getElem_append_left' hlt,List.getElem?_set_ne (by omega:words.length ≠ i)]
    exact h i hlt
  · have he:i=words.length:=by
      simp only [List.length_append,List.length_singleton] at hi
      omega
    subst i
    simp [List.getElem?_set_self hroom]

def append:Com:=.seq (.store "vm.output" (.var "vm.outputLength") (remainder (.var "vm.left")))
  (.seq (.assign "vm.outputLength" (.add (.var "vm.outputLength") (.lit 1))) increment)

theorem append_spec (B w:ℕ) (s:SparseRam.SparseState) (value:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (hv:value < B) (hpc:s.pc + 1 < B)
    (hlen:s.out.length + 1 < B):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧ σ.vars "vm.left"=value∧
      s.out.length < (σ.arrs "vm.output").length) append
      (fun _ τ => Represents w { s with pc:=s.pc + 1,out:=s.out ++ [value % 2 ^ w] } τ∧
        τ.vars "vm.running"=1) 17:=by
  rintro σ ⟨⟨hcore,htapes⟩,hrunning,hvalue,hroom⟩
  have hσpc:=hcore.2.1
  have hσM:=hcore.2.2.1
  have hσout:=htapes.2.2.2.2.2
  have hprefix:=htapes.2.2.2.2.1
  have happend:=prefix_append s.out (σ.arrs "vm.output") (value % 2 ^ w) hprefix hroom
  have hd:=(Nat.div_le_self value (2 ^ w)).trans_lt hv
  have hp:=(Nat.div_mul_le_self value (2 ^ w)).trans_lt hv
  have hs:=(Nat.sub_le value (value / 2 ^ w * 2 ^ w)).trans_lt hv
  simp only [append,remainder,increment]
  (expose_names;
    (refine let c0:Expr:=Expr.mul (Expr.div (Expr.var "vm.left") (Expr.var "vm.modulus")) (Expr.var "vm.modulus"); let c1:Expr:=Expr.sub (Expr.var "vm.left") c0; let c2:Com:=Com.store "vm.output" (Expr.var "vm.outputLength") c1; let c3:Expr:=Expr.add (Expr.var "vm.outputLength") (Expr.lit ((1:Nat))); let c4:Com:=Com.assign "vm.outputLength" c3; let c5:Expr:=Expr.add (Expr.var "vm.pc") (Expr.lit ((1:Nat))); let c6:Com:=Com.assign "vm.pc" c5; let c7:Com:=Com.seq c4 c6; let c8:Com:=Com.seq c2 c7; let c9:Env→ Nat→ Prop:=Run B c8 σ; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Env→ Prop:=Represents w (SparseRam.SparseState.mk (c10 (SparseRam.SparseState.pc s) ((1:Nat))) (SparseRam.SparseState.memory s) (SparseRam.SparseState.input s) (SparseRam.SparseState.inp s) (@HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) (SparseRam.SparseState.out s) (@List.cons Nat (@HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) value (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) w)) (@List.nil Nat)))); let c12:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "vm.left") (Env.vars σ "vm.modulus"); let c13:Nat:=Nat.mul c12 (Env.vars σ "vm.modulus"); let c14:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "vm.left") c13; let c15:Env:=Env.setArr σ "vm.output" (Env.vars σ "vm.outputLength") c14; let c16:Nat:=Env.vars c15 "vm.outputLength"; let c17:Nat:=c10 c16 ((1:Nat)); let c18:Env:=Env.setVar c15 "vm.outputLength" c17; let c19:Nat:=Env.vars c18 "vm.pc"; let c20:Nat:=c10 c19 ((1:Nat)); let c21:Env:=Env.setVar c18 "vm.pc" c20; let c22:Prop:=And (c11 c21) (@Eq Nat (Env.vars c21 "vm.running") ((1:Nat))); let c23:Nat→ Nat:=c10 ((1:Nat)); let c24:Nat:=c10 (c23 (Expr.size (Expr.var "vm.outputLength"))) (Expr.size c1); let c25:Nat:=c23 (Expr.size c3); let c26:Nat:=c23 (Expr.size c5); let c27:Nat:=c10 c25 c26; @Exists.intro Env (fun (σ':Env) => And (c9 σ' ((17:Nat))) (And (c11 σ') (@Eq Nat (Env.vars σ' "vm.running") ((1:Nat))))) c21 (@And.intro (c9 c21 ((17:Nat))) c22 (RunStep.mono B c8 σ c21 (c10 c24 c27) ((17:Nat)) (RunStep.seq B c2 c7 σ c15 c21 c24 c27 (RunStep.store B σ "vm.output" (Expr.var "vm.outputLength") c1 (Env.vars σ "vm.outputLength") c14 (RunStep.eval_var B σ "vm.outputLength" (?nAX_g5994_0_0_0)) (RunStep.eval_sub B σ (Expr.var "vm.left") c0 (Env.vars σ "vm.left") c13 (RunStep.eval_var B σ "vm.left" (?nAX_g5994_0_0_1)) (RunStep.eval_mul B σ (Expr.div (Expr.var "vm.left") (Expr.var "vm.modulus")) (Expr.var "vm.modulus") c12 (Env.vars σ "vm.modulus") (RunStep.eval_div B σ (Expr.var "vm.left") (Expr.var "vm.modulus") (Env.vars σ "vm.left") (Env.vars σ "vm.modulus") (RunStep.eval_var B σ "vm.left" (?nAX_g5994_0_0_2)) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5994_0_0_3)) ?_) (RunStep.eval_var B σ "vm.modulus" (?nAX_g5994_0_0_4)) ?_) (?nAX_g5994_0_0_5)) (?nAX_g5994_0_0_6)) (RunStep.seq B c4 c6 c15 c18 c21 c25 c26 (RunStep.assign B c15 "vm.outputLength" c3 c17 (RunStep.eval_add B c15 (Expr.var "vm.outputLength") (Expr.lit ((1:Nat))) c16 ((1:Nat)) (RunStep.eval_var B c15 "vm.outputLength" (?nAX_g5994_0_0_7)) (RunStep.eval_lit B ((1:Nat)) c15 h1) (?nAX_g5994_0_0_8))) (RunStep.assign B c18 "vm.pc" c5 c20 (RunStep.eval_add B c18 (Expr.var "vm.pc") (Expr.lit ((1:Nat))) c19 ((1:Nat)) (RunStep.eval_var B c18 "vm.pc" (?nAX_g5994_0_0_9)) (RunStep.eval_lit B ((1:Nat)) c18 h1) (?nAX_g5994_0_0_10))))) (?nAX_g5994_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5994_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5994_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Core,Tapes,Prefix,RamSparseRead.Representation,
    Nat.mod_def,Nat.mul_comm]

theorem write_spec (B w:ℕ) (s:SparseRam.SparseState) (a:ℕ)
    (h1:1 < B) (hM:2 ^ w < B) (ha:a < B)
    (hwords:SparseBounds.MemoryWords w s.memory) (hpc:s.pc + 1 < B)
    (hmem:s.memory.length < B) (hout:s.out.length + 1 < B):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧
      s.out.length < (σ.arrs "vm.output").length) (instruction (.write a))
      (fun _ τ => Represents w { s with pc:=s.pc + 1,out:=s.out ++ [SparseRam.lookup s.memory (a % 2 ^ w) % 2 ^ w] } τ∧
        τ.vars "vm.running"=1) (16 * s.memory.length + 35):=by
  let value:=SparseRam.lookup s.memory (a % 2 ^ w)
  have hvalue:=(SparseBounds.lookup_bound w s.memory (a % 2 ^ w) hwords).trans hM
  have hread:=read_literal_spec B w s.pc s.memory a "vm.left" h1 hM ha hmem hwords
    (by decide) (by decide) (by decide) (by decide)
  rintro σ ⟨⟨hcore,htapes⟩,hrunning,hroom⟩
  obtain ⟨ν,hget,hpost⟩:=hread σ hcore
  have htapesν:=tapes_frame hget s htapes
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.warrs])
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.warrs])
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
    (by simp [RamSparseRead.read,RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])
  have hrunningν:=(hget.frame_var "vm.running" (by simp [RamSparseRead.read,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,Com.wvars])).trans hrunning
  have hroomν:s.out.length < (ν.arrs "vm.output").length:=by
    rwa [RamFrames.run_array_length hget "vm.output"]
  obtain ⟨τ,hwrite,hfinal⟩:=append_spec B w s value h1 hM hvalue hpc hout ν
    ⟨⟨hpost.1,htapesν⟩,hrunningν,hpost.2,hroomν⟩
  exact ⟨τ, (hget.seq hwrite).mono (by omega),hfinal⟩

end Lax455465Proofs.RamVirtualOutput

end

section

namespace Lax455465Proofs.RamVirtualInstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualArithmetic RamVirtualProgram RamVirtualState RamVirtualFrame

def Ready (w:ℕ) (s:SparseRam.SparseState) (σ:Env):Prop:=
  Represents w s σ∧ σ.vars "vm.running"=1∧
  s.memory.length < (σ.arrs "vm.addresses").length∧
  s.memory.length < (σ.arrs "vm.values").length∧
  s.out.length < (σ.arrs "vm.output").length

def Result (w:ℕ) (s:SparseRam.SparseState) (i:Lax808846.Ram.Instr) (τ:Env):Prop:=
  match SparseRam.effect w i s with
  | some t => Represents w t τ∧ τ.vars "vm.running"=1
  | none => Represents w s τ∧ τ.vars "vm.running"=0

theorem instruction_spec (B w:ℕ) (s:SparseRam.SparseState) (i:Lax808846.Ram.Instr)
    (hB:2 * (2 ^ w) ^ 2 + 3 < B) (hlit:LiteralsFit B i)
    (hwords:SparseBounds.MemoryWords w s.memory)
    (hinput:s.input.length < B) (hinputWords:∀ x∈ s.input,x < B)
    (hpc:s.pc + 1 < B) (hmem:s.memory.length + 1 < B) (hout:s.out.length + 1 < B):
    Spec B (Ready w s) (instruction i) (fun _ τ => Result w s i τ)
      (32 * s.memory.length + 100):=by
  have h1:1 < B:=by omega
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have lift (j:Lax808846.Ram.Instr) (t:SparseRam.SparseState) (K:ℕ) (P:Env→ Prop)
      (hq:Quiet j) (ht:t.input=s.input∧ t.inp=s.inp∧ t.out=s.out)
      (hspec:Spec B P (instruction j) (fun _ τ => Core w t.pc t.memory τ) K)
      (hpre:∀ σ,Represents w s σ→ s.memory.length < (σ.arrs "vm.addresses").length→
        s.memory.length < (σ.arrs "vm.values").length→ P σ)
      (hK:K≤ 32 * s.memory.length + 100):
      Spec B (Ready w s) (instruction j)
        (fun _ τ => Represents w t τ∧ τ.vars "vm.running"=1) (32 * s.memory.length + 100):=
    ((lift_spec B w K j s t P hq ht hspec hpre).pre
      (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono hK
  cases i with
  | set a v =>
    exact lift (.set a v) (SparseRam.assign w s a v) 40 _ trivial ⟨rfl,rfl,rfl⟩
      (set_spec B w s.pc s.memory a v h1 hM hlit.1 hlit.2 hpc hmem)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | load a b =>
    exact lift (.load a b) (SparseRam.assign w s a
        (SparseRam.lookup s.memory (SparseRam.lookup s.memory (b % 2 ^ w) % 2 ^ w))) _ _
      trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualIndirect.load_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | store a b =>
    exact lift (.store a b) (SparseRam.assign w s (SparseRam.lookup s.memory (a % 2 ^ w))
        (SparseRam.lookup s.memory (b % 2 ^ w))) _ _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualIndirect.store_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | add a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .add s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono (by omega)
  | sub a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .sub s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono (by omega)
  | mul a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .mul s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono (by omega)
  | div a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .div s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono (by omega)
  | and a b c =>
    exact ((RamVirtualBasic.instruction_spec B w .and s a b c hB hlit.1 hlit.2.1 hlit.2.2
      hwords hpc hmem).pre (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono (by omega)
  | shiftl a b c =>
    exact lift (.shiftl a b c) (SparseRam.assign w s a (SparseRam.lookup s.memory (b % 2 ^ w) *
        2 ^ SparseRam.lookup s.memory (c % 2 ^ w))) _ _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualBitOps.shift_core_spec B w s.pc s.memory a b c hB hlit.1 hlit.2.1 hlit.2.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | not a b =>
    exact lift (.not a b) (SparseRam.assign w s a (2 ^ w - 1 - SparseRam.lookup s.memory (b % 2 ^ w)))
      _ _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualBitOps.not_core_spec B w s.pc s.memory a b h1 hM hlit.1 hlit.2 hwords hpc hmem)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | jump l =>
    exact lift (.jump l) { s with pc:=l } 2 _ trivial ⟨rfl,rfl,rfl⟩
      (jump_spec B w s.pc s.memory l hlit) (fun _ h _ _ => h.1) (by omega)
  | jzero a l =>
    exact lift (.jzero a l) { s with pc:=if SparseRam.lookup s.memory (a % 2 ^ w)=0 then l else s.pc + 1 }
      _ _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualControl.jzero_core_spec B w s.pc s.memory a l h1 hM hlit.1 hlit.2 hpc (by omega) hwords)
      (fun _ h hA hV => ⟨h.1,hA,hV⟩) (by omega)
  | jeof l =>
    have hj:=RamFrames.keep_scalar (RamVirtualControl.jeof_spec B w s l hlit hinput hpc h1)
      "vm.running" 1 (by simp [instruction,increment,Com.wvars])
    exact (hj.pre (fun _ h => ⟨h.1,h.2.1⟩)).mono (by omega)
  | inputLength a =>
    exact lift (.inputLength a) (SparseRam.assign w s a s.input.length) 40 _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualInput.length_core_spec B w s.pc s.memory s.input.length a h1 hM hlit hinput hpc hmem)
      (fun _ h hA hV => ⟨⟨h.1,hA,hV⟩,h.2.2.1⟩) (by omega)
  | inputLoad a b =>
    exact lift (.inputLoad a b) (SparseRam.assign w s a
        (s.input[SparseRam.lookup s.memory (b % 2 ^ w) % 2 ^ w]?.getD 0)) _ _ trivial ⟨rfl,rfl,rfl⟩
      (RamVirtualInput.load_core_spec B w s.pc s.memory s.input a b h1 hM hlit.1 hlit.2
        hinput hinputWords hwords hpc hmem)
      (fun _ h hA hV => ⟨⟨h.1,hA,hV⟩,h.2.1,h.2.2.1⟩) (by omega)
  | halt => exact ((stop_spec B w s (by omega)).pre (fun _ h => h.1)).mono (by omega)
  | read a =>
    cases hi:s.inp with
    | nil =>
      simpa only [Result,SparseRam.effect,hi,List.head?_nil,Option.map_none] using
        (((RamVirtualRead.empty_spec B w s a (by omega) hinput hi).pre (fun _ h => h.1)).mono
          (show 6≤ 32 * s.memory.length + 100 by omega))
    | cons value rest =>
      simpa only [Result,SparseRam.effect,hi,List.head?_cons,List.tail_cons,Option.map_some] using
        (((RamVirtualRead.nonempty_spec B w s a value rest h1 hM hlit hinput hinputWords hi hpc hmem).pre
          (fun _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)).mono
          (show 51≤ 32 * s.memory.length + 100 by omega))
  | write a =>
    exact ((RamVirtualOutput.write_spec B w s a h1 hM hlit hwords hpc (by omega) hout).pre
      (fun _ h => ⟨h.1,h.2.1,h.2.2.2.2⟩)).mono (by omega)

end Lax455465Proofs.RamVirtualInstruction

end

section

namespace Lax455465Proofs.RamVirtualDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

def fetch:List Lax808846.Ram.Instr→ ℕ→ ℕ→ Option Lax808846.Ram.Instr
  | [],_,_ => none
  | i::rest,offset,pc => if pc=offset then some i else fetch rest (offset + 1) pc

theorem fetch_eq (p:List Lax808846.Ram.Instr) (offset pc:ℕ):
    fetch p offset pc=if offset≤ pc then p[pc - offset]? else none:=by
  induction p generalizing offset with
  | nil => simp [fetch]
  | cons i rest ih =>
    by_cases he:pc=offset
    · subst pc; simp [fetch]
    · rw [fetch,if_neg he,ih]
      by_cases hlo:offset≤ pc
      · have hsucc:offset + 1≤ pc:=by omega
        have hsub:pc - offset=(pc - (offset + 1)) + 1:=by omega
        simp [hlo,hsucc,hsub]
      · have hsucc:¬offset + 1≤ pc:=by omega
        simp [hlo,hsucc]

def Result (w:ℕ) (s:SparseRam.SparseState) (p:List Lax808846.Ram.Instr) (offset:ℕ)
    (τ:Env):Prop:=
  match fetch p offset s.pc with
  | none => Represents w s τ∧ τ.vars "vm.running"=0
  | some i => RamVirtualInstruction.Result w s i τ

theorem dispatch_spec (B w:ℕ) (s:SparseRam.SparseState) (p:List Lax808846.Ram.Instr)
    (offset:ℕ) (hB:2 * (2 ^ w) ^ 2 + 3 < B)
    (hlit:∀ i∈ p,LiteralsFit B i) (hoff:offset + p.length < B)
    (hwords:SparseBounds.MemoryWords w s.memory)
    (hinput:s.input.length < B) (hinputWords:∀ x∈ s.input,x < B)
    (hpc:s.pc + 1 < B) (hmem:s.memory.length + 1 < B) (hout:s.out.length + 1 < B):
    Spec B (Ready w s) (dispatch p offset) (fun _ τ => Result w s p offset τ)
      (4 * p.length + 32 * s.memory.length + 100):=by
  induction p generalizing offset with
  | nil =>
    exact ((stop_spec B w s (by omega)).pre (fun _ h => h.1)).mono (by simp)
  | cons i rest ih =>
    rintro σ hready
    have hpcσ:=hready.1.1.2.1
    have hpcB:σ.vars "vm.pc" < B:=by rw [hpcσ]; omega
    have hoffB:offset < B:=by simp only [List.length_cons] at hoff; omega
    by_cases he:s.pc=offset
    · have hcond:(Cond.eq (.var "vm.pc") (.lit offset)).evalB B σ=some true:=by
        rw [evalB_condEq_iff]
        exact ⟨s.pc,offset,by simpa only [hpcσ] using evalB_var hpcB,evalB_lit hoffB,by simp [he]⟩
      obtain ⟨τ,hrun,hpost⟩:=instruction_spec B w s i hB (hlit i List.mem_cons_self)
        hwords hinput hinputWords hpc hmem hout σ hready
      refine ⟨τ, (Run.ite_true hcond hrun).mono ?_, ?_⟩
      · simp only [Cond.size,Expr.size,List.length_cons]; omega
      · simpa only [Result,fetch,if_pos he] using hpost
    · have hcond:(Cond.eq (.var "vm.pc") (.lit offset)).evalB B σ=some false:=by
        rw [evalB_condEq_iff]
        exact ⟨s.pc,offset,by simpa only [hpcσ] using evalB_var hpcB,evalB_lit hoffB,by simp [he]⟩
      obtain ⟨τ,hrun,hpost⟩:=ih (offset + 1)
        (fun j hj => hlit j (List.mem_cons_of_mem i hj)) (by simp only [List.length_cons] at hoff; omega) σ hready
      refine ⟨τ, (Run.ite_false hcond hrun).mono ?_, ?_⟩
      · simp only [Cond.size,Expr.size,List.length_cons]; omega
      · simpa only [Result,fetch,if_neg he] using hpost

theorem result_zero (w:ℕ) (s:SparseRam.SparseState) (p:Lax808846.Ram.Program) (τ:Env):
    Result w s p 0 τ =
      match SparseRam.step w p s with
      | none => Represents w s τ∧ τ.vars "vm.running"=0
      | some t => Represents w t τ∧ τ.vars "vm.running"=1:=by
  simp only [Result,fetch_eq,Nat.zero_le,if_true,Nat.sub_zero,SparseRam.step]
  cases hi:p[s.pc]? with
  | none => rfl
  | some i =>
    simp only [RamVirtualInstruction.Result,Option.bind_some]
    cases SparseRam.effect w i s <;> rfl

end Lax455465Proofs.RamVirtualDispatch

end

section

namespace Lax455465Proofs.RamVirtualTraceBounds

open Lax808846.Ram SparseRam RamVirtualInstruction

theorem literals_mono (i:Instr) {A B:ℕ} (h:LiteralsFit A i) (hab:A≤ B):
    LiteralsFit B i:=by
  cases i <;> simp_all [LiteralsFit] <;> omega

theorem step_input (w:ℕ) (p:Program) (s t:SparseState)
    (h:step w p s=some t):t.input=s.input:=by
  obtain ⟨i,_,he⟩:=Option.bind_eq_some_iff.mp h
  exact SparseBounds.effect_input_eq w i s t he

theorem step_pc (B w:ℕ) (p:Program) (s t:SparseState)
    (hp:p.length + 1 < B) (hlit:∀ i∈ p,LiteralsFit (B - 1) i)
    (hs:step w p s=some t):t.pc + 1 < B:=by
  obtain ⟨i,hi,he⟩:=Option.bind_eq_some_iff.mp hs
  have hpos:s.pc < p.length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  have hilit:=hlit i (List.mem_of_getElem? hi)
  have hseq:s.pc + 2 < B:=by omega
  cases i <;> simp only [effect] at he
  all_goals first
    | solve | (cases he <;> simp_all [assign,LiteralsFit] <;> omega)
    | solve | (cases he <;> simp_all [assign,LiteralsFit] <;> split_ifs <;> omega)
    | solve | (cases hr:s.inp.head? <;>
        simp only [hr,Option.map_some,Option.map_none] at he <;>
        cases he <;> simp_all [assign,LiteralsFit] <;> omega)

theorem run_pc (B w:ℕ) (p:Program) (s t:SparseState) (k:ℕ)
    (hp:p.length + 1 < B) (hlit:∀ i∈ p,LiteralsFit (B - 1) i)
    (hstart:s.pc + 1 < B) (hr:run w p k s=some t):t.pc + 1 < B:=by
  induction k generalizing s with
  | zero => cases hr; exact hstart
  | succ k ih =>
    obtain ⟨u,hs,ht⟩:=Option.bind_eq_some_iff.mp hr
    exact ih u (step_pc B w p s u hp hlit hs) ht

end Lax455465Proofs.RamVirtualTraceBounds

end

section

namespace Lax455465Proofs.RamVirtualLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

def command (p:Lax808846.Ram.Program):Com:=
  .while (.lt (.lit 0) (.var "vm.running")) (dispatch p 0)

private theorem running_test {B:ℕ} {σ:Env} {v:ℕ}
    (hB:0 < B) (hv:v < B) (hflag:σ.vars "vm.running"=v):
    (Cond.lt (.lit 0) (.var "vm.running")).evalB B σ=some (decide (0 < v)):=by
  apply evalB_condLt (evalB_lit hB)
  rw [evalB_var_iff]
  exact ⟨hflag.symm,hflag ▸ hv⟩

private theorem while_true {B K K':ℕ} {p:Lax808846.Ram.Program} {σ ν τ:Env}
    (hcond:(Cond.lt (.lit 0) (.var "vm.running")).evalB B σ=some true)
    (hbody:Run B (dispatch p 0) σ ν K) (htail:Run B (command p) ν τ K'):
    Run B (command p) σ τ (4 + K + K'):=by
  obtain ⟨k,hk,hb⟩:=hbody
  obtain ⟨k',hk',ht⟩:=htail
  exact ⟨4 + k + k',by omega,BigStepB.while_true hcond hb ht⟩

theorem loop_spec (B w N k:ℕ) (p:Lax808846.Ram.Program) (s f:SparseRam.SparseState)
    (hB:2 * (2 ^ w) ^ 2 + 3 < B) (hN:N + 1 < B)
    (hp:p.length < B) (hlit:∀ i∈ p,LiteralsFit B i)
    (hwords:SparseBounds.MemoryWords w s.memory)
    (hinput:s.input.length < B) (hinputWords:∀ x∈ s.input,x < B)
    (hm:s.memory.length + k≤ N) (ho:s.out.length + k≤ N)
    (hpcs:∀ j≤ k, ∀ t,SparseRam.run w p j s=some t→ t.pc + 1 < B)
    (hr:SparseRam.run w p k s=some f) (hhalt:SparseRam.step w p f=none):
    Spec B (fun σ => Represents w s σ∧ σ.vars "vm.running"=1∧
      N < (σ.arrs "vm.addresses").length∧ N < (σ.arrs "vm.values").length∧
      N < (σ.arrs "vm.output").length) (command p)
      (fun _ τ => Represents w f τ∧ τ.vars "vm.running"=0)
      ((k + 1) * (4 * p.length + 32 * N + 104) + 4):=by
  have h1:1 < B:=by omega
  induction k generalizing s with
  | zero =>
    have heq:s=f:=Option.some.inj hr
    subst s
    rintro σ ⟨hrep,hflag,hA,hV,hO⟩
    have hpc:=hpcs 0 (by omega) f rfl
    obtain ⟨τ,hbody,hpost⟩:=RamVirtualDispatch.dispatch_spec B w f p 0 hB hlit
      (by simpa using hp) hwords hinput hinputWords hpc (by omega) (by omega) σ
      ⟨hrep,hflag,by omega,by omega,by omega⟩
    rw [RamVirtualDispatch.result_zero,hhalt] at hpost
    have htrue:(Cond.lt (.lit 0) (.var "vm.running")).evalB B σ=some true:=
      running_test (by omega) h1 hflag
    have hfalse:(Cond.lt (.lit 0) (.var "vm.running")).evalB B τ=some false:=
      running_test (by omega) (by omega) hpost.2
    exact ⟨τ, (while_true htrue hbody (Run.while_false hfalse)).mono
      (by simp only [Cond.size,Expr.size,Nat.zero_add,Nat.one_mul] ; omega),hpost⟩
  | succ k ih =>
    obtain ⟨u,hstep,hrest⟩:=Option.bind_eq_some_iff.mp hr
    have hmu:=SparseRam.step_memory_le w p s u hstep
    have hou:=SparseBounds.step_output_le w p s u hstep
    have hwordsu:=SparseBounds.step_words w p s u hwords hstep
    have hinputu:=RamVirtualTraceBounds.step_input w p s u hstep
    have hpc:=hpcs 0 (by omega) s rfl
    have hpcsu:∀ j≤ k, ∀ t,SparseRam.run w p j u=some t→ t.pc + 1 < B:=by
      intro j hj t ht
      apply hpcs (j + 1) (by omega) t
      simp only [SparseRam.run,hstep,Option.bind_some,ht]
    rintro σ ⟨hrep,hflag,hA,hV,hO⟩
    obtain ⟨ν,hbody,hpost⟩:=RamVirtualDispatch.dispatch_spec B w s p 0 hB hlit
      (by simpa using hp) hwords hinput hinputWords hpc (by omega) (by omega) σ
      ⟨hrep,hflag,by omega,by omega,by omega⟩
    rw [RamVirtualDispatch.result_zero,hstep] at hpost
    have hAν:N < (ν.arrs "vm.addresses").length:=by
      rwa [RamFrames.run_array_length hbody "vm.addresses"]
    have hVν:N < (ν.arrs "vm.values").length:=by
      rwa [RamFrames.run_array_length hbody "vm.values"]
    have hOν:N < (ν.arrs "vm.output").length:=by
      rwa [RamFrames.run_array_length hbody "vm.output"]
    obtain ⟨τ,htail,hfinal⟩:=ih u hwordsu (by rwa [hinputu])
      (by simpa only [hinputu] using hinputWords) (by omega) (by omega) hpcsu hrest ν
      ⟨hpost.1,hpost.2,hAν,hVν,hOν⟩
    have htrue:(Cond.lt (.lit 0) (.var "vm.running")).evalB B σ=some true:=
      running_test (by omega) h1 hflag
    refine ⟨τ, (while_true htrue hbody htail).mono ?_,hfinal⟩
    simp only [Nat.add_mul,Nat.one_mul]
    omega

end Lax455465Proofs.RamVirtualLoop

end

section

namespace Lax455465Proofs.RamVirtualExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualCore RamVirtualProgram RamVirtualState RamVirtualInstruction

theorem execute_spec (B w k:ℕ) (p:Lax808846.Ram.Program) (input:List ℕ)
    (f:SparseRam.SparseState) (hB:2 * (2 ^ w) ^ 2 + 3 < B)
    (hk:k + 1 < B) (hp:p.length + 1 < B)
    (hlit:∀ i∈ p,LiteralsFit (B - 1) i)
    (hinput:input.length < B) (hinputWords:∀ x∈ input,x < B)
    (hr:SparseRam.run w p k (SparseRam.init input)=some f)
    (hhalt:SparseRam.step w p f=none):
    Spec B (fun σ => σ.vars "vm.width"=w∧ Prefix input "vm.input" σ∧
      σ.vars "vm.inputLength"=input.length∧ k < (σ.arrs "vm.addresses").length∧
      k < (σ.arrs "vm.values").length∧ k < (σ.arrs "vm.output").length)
      (execute p) (fun _ τ => Represents w f τ∧ τ.vars "vm.running"=0)
      ((k + 1) * (4 * p.length + 32 * k + 104) + 18):=by
  have h1:1 < B:=by omega
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  rintro σ ⟨hwidth,hprefix,hlen,hA,hV,hO⟩
  obtain ⟨ν,hmod,hmodulus⟩:=RamWordOps.modulus_spec B w hM σ hwidth
  have hwidthν:=(hmod.frame_var "vm.width" (by decide)).trans hwidth
  have hprefixν:Prefix input "vm.input" ν:=by
    simpa only [Prefix,hmod.frame_arr "vm.input" (by decide)] using hprefix
  have hlenν:=(hmod.frame_var "vm.inputLength" (by decide)).trans hlen
  obtain ⟨μ,hinit,hrep⟩:=init_spec B w input h1 ν ⟨hmodulus,hwidthν,hprefixν,hlenν⟩
  have hAμ:k < (μ.arrs "vm.addresses").length:=by
    rwa [RamFrames.run_array_length hinit "vm.addresses",RamFrames.run_array_length hmod "vm.addresses"]
  have hVμ:k < (μ.arrs "vm.values").length:=by
    rwa [RamFrames.run_array_length hinit "vm.values",RamFrames.run_array_length hmod "vm.values"]
  have hOμ:k < (μ.arrs "vm.output").length:=by
    rwa [RamFrames.run_array_length hinit "vm.output",RamFrames.run_array_length hmod "vm.output"]
  have hpcs:∀ j≤ k, ∀ t,SparseRam.run w p j (SparseRam.init input)=some t→ t.pc + 1 < B:=by
    intro j _ t hj
    exact RamVirtualTraceBounds.run_pc B w p (SparseRam.init input) t j hp hlit (by simp [SparseRam.init]; omega) hj
  have hwords:SparseBounds.MemoryWords w (SparseRam.init input).memory:=by
    simp [SparseBounds.MemoryWords,SparseRam.init]
  obtain ⟨τ,hloop,hfinal⟩:=RamVirtualLoop.loop_spec B w k k p (SparseRam.init input) f hB hk
    (by omega) (fun i hi => RamVirtualTraceBounds.literals_mono i (hlit i hi) (by omega))
    hwords hinput hinputWords (by simp [SparseRam.init]) (by simp [SparseRam.init]) hpcs hr hhalt μ
    ⟨hrep.1,hrep.2,hAμ,hVμ,hOμ⟩
  exact ⟨τ, (hmod.seq (hinit.seq hloop)).mono (by omega),hfinal⟩

end Lax455465Proofs.RamVirtualExecution

end

theorem solution:∀ (B w k:Nat) (p:Lax808846.Ram.Program) (input:List Nat) (f:Lax455465Proofs.SparseRam.SparseState),
  Nat.lt
      (Nat.add
        (Nat.mul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            ((2:Nat))))
        ((3:Nat)))
      B→
    Nat.lt
        (Nat.add k ((1:Nat)))
        B→
      Nat.lt
          (Nat.add (@List.length Lax808846.Ram.Instr p)
            ((1:Nat)))
          B→
        (∀ (i:Lax808846.Ram.Instr),
            @Membership.mem Lax808846.Ram.Instr Lax808846.Ram.Program (@List.instMembership Lax808846.Ram.Instr) p i→
              Lax455465Proofs.RamVirtualInstruction.LiteralsFit
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) B
                  ((1:Nat)))
                i)→
          Nat.lt (@List.length Nat input) B→
            (∀ (x:Nat),
                @Membership.mem Nat (List Nat) (@List.instMembership Nat) input x→ Nat.lt x B)→
              @Eq (Option Lax455465Proofs.SparseRam.SparseState)
                  (Lax455465Proofs.SparseRam.run w p k (Lax455465Proofs.SparseRam.init input))
                  (@Option.some Lax455465Proofs.SparseRam.SparseState f)→
                @Eq (Option Lax455465Proofs.SparseRam.SparseState) (Lax455465Proofs.SparseRam.step w p f)
                    (@Option.none Lax455465Proofs.SparseRam.SparseState)→
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Eq Nat (σ.vars "vm.width") w)
                        (And (Lax455465Proofs.RamVirtualState.Prefix input "vm.input" σ)
                          (And (@Eq Nat (σ.vars "vm.inputLength") (@List.length Nat input))
                            (And (Nat.lt k (@List.length Nat (σ.arrs "vm.addresses")))
                              (And (Nat.lt k (@List.length Nat (σ.arrs "vm.values")))
                                (Nat.lt k (@List.length Nat (σ.arrs "vm.output"))))))))
                    (Lax455465Proofs.RamVirtualProgram.execute p)
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (Lax455465Proofs.RamVirtualState.Represents w f τ)
                        (@Eq Nat (τ.vars "vm.running") ((0:Nat))))
                    (Nat.add
                      (Nat.mul
                        (Nat.add k
                          ((1:Nat)))
                        (Nat.add
                          (Nat.add
                            (Nat.mul
                              ((4:Nat))
                              (@List.length Lax808846.Ram.Instr p))
                            (Nat.mul
                              ((32:Nat)) k))
                          ((104:Nat))))
                      ((18:Nat))):= @Lax455465Proofs.RamVirtualExecution.execute_spec
