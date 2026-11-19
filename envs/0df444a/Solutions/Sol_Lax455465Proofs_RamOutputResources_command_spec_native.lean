-- Prove2me | solution 1 for Lax455465Proofs.RamOutputResources.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:56:45.527209+00:00
-- url     : https://prove2.me/submissions/0445e86e-d9b7-455b-a0c0-afa4526ed634

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

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

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

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

end Lax455465Proofs.RamRational

end

section

namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

@[simp] theorem length_encode (qs:List ℚ≥0):(encode qs).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

theorem numerator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i]?=some qs[i].num:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)=Nat.succ (Nat.succ (2*i)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem denominator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i+1]?=some qs[i].den:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)+1=Nat.succ (Nat.succ (2*i+1)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem read_spec (B:ℕ) (array index:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s"):
    Spec B (fun σ => Prefix (encode qs) array σ∧ σ.vars index=i) (read array index)
      (fun _ τ => FractionOutput (qs[i]:ℚ) τ∧ τ.vars "rat.s"=0) 14:=by
  have hnum:=numerator_at qs i hi
  have hden:=denominator_at qs i hi
  rintro σ ⟨hp,hv⟩
  have hni:2*i < (encode qs).length:=by simp only [length_encode]; omega
  have hdi:2*i+1 < (encode qs).length:=by simp only [length_encode]; omega
  have hnumval:(encode qs)[2*i]=qs[i].num:=by simpa only [List.getElem?_eq_getElem hni,Option.some.injEq] using hnum
  have hdenval:(encode qs)[2*i+1]=qs[i].den:=by simpa only [List.getElem?_eq_getElem hdi,Option.some.injEq] using hden
  have hgN:=(hp (2*i) hni).trans (congrArg some hnumval)
  have hgD:=(hp (2*i+1) hdi).trans (congrArg some hdenval)
  have hN:2*i < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgN; cases hgN
  have hD:2*i+1 < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgD; cases hgD
  have hni':i < B:=by omega
  have hmul:2*i < B:=by omega
  have hvalue:fractionValue 0 qs[i].num qs[i].den=(qs[i]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den qs[i])
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (@getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i_1:Nat) => Nat.lt i_1 (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) qs i hi)); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (@Eq Nat (Env.vars τ "rat.s") ((0:Nat)))) σ; let c2:Nat→ Nat:=Nat.mul ((2:Nat)); let c3:Nat:=c2 (Env.vars σ index); let c4:Nat:= @List.getD Nat (Env.arrs σ array) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "rat.n" c4; let c6:List Nat:=Env.arrs c5 array; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c5 index; let c9:Nat:=c2 c8; let c10:Nat:=c7 c9 ((1:Nat)); let c11:Nat:= @List.getD Nat c6 c10 ((0:Nat)); let c12:Env:=Env.setVar c5 "rat.d" c11; let c13:Env:=Env.setVar c12 "rat.s" ((0:Nat)); let c14:Nat→ Nat:=c7 ((1:Nat)); let c15:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var index); let c16:Expr:=Expr.get array c15; let c17:Nat:=c14 (Expr.size c16); let c18:Expr:=Expr.add c15 (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c14 (Expr.size c19); let c21:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c22:Nat:=c7 c20 c21; let c23:Com:=Com.assign "rat.d" c19; let c24:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c25:Nat→ Prop:=Nat.lt c10; @Exists.intro Env (fun (σ':Env) => And (Run B (read array index) σ σ' ((14:Nat))) (c1 σ')) c13 (@And.intro (Run B (read array index) σ c13 ((14:Nat))) (c1 c13) (RunStep.mono B (read array index) σ c13 (c7 c17 c22) ((14:Nat)) (RunStep.seq B (Com.assign "rat.n" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "rat.n" c16 c4 (RunStep.eval_get B σ array c15 c3 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) (Env.vars σ index) (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_var B σ index (?nAX_g5778_0_0_0)) (?nAX_g5778_0_0_1)) (?nAX_g5778_0_0_2) ?_)) (RunStep.seq B c23 c24 c5 c12 c13 c20 c21 (RunStep.assign B c5 "rat.d" c19 c11 (RunStep.eval_get B c5 array c18 c10 (RunStep.eval_add B c5 c15 (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_mul B c5 (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) c8 (RunStep.eval_lit B ((2:Nat)) c5 h2) (RunStep.eval_var B c5 index ?_) ?_) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g5778_0_0_3)) ?_) ?_ ?_)) (RunStep.assign B c12 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c12 (?nAX_g5778_0_0_4))))) (?nAX_g5778_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5778_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

end Lax455465Proofs.RamUnsignedBuffer

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

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem arc_value {n:ℕ} (s t u v:Fin n):
    (arcIndex n ((s,t), (u,v))).val=(s.val * n + t.val) * (n * n) + (u.val * n + v.val):=by
  simp [arcIndex,edgeIndex,finProdFinEquiv]
  ring

theorem value_variable {n:ℕ} (v:Fin 1):(variableIndex n (.inl v)).val=0:=by
  simp [variableIndex,finSumFinEquiv,Equiv.sumCongr]

end Lax455465Proofs.FlowLpIndices

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

open scoped NNRat

namespace Lax455465Proofs.InstanceParser

open Lax455465.RationalEncoding Lax455465.ProductNetwork

theorem encoded_length (qs:List ℚ≥0):(qs.flatMap encodeRational).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.flatMap_cons,encodeRational,ih]; omega

end Lax455465Proofs.InstanceParser

end

section

namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

theorem height_mono {M N:ℕ} {q:ℚ} (h:Height M q) (hmn:M≤ N):Height N q:=
  ⟨h.1.trans hmn,h.2.trans hmn⟩

theorem height_mul {M N:ℕ} {q r:ℚ} (hq:Height M q) (hr:Height N r):
    Height (M * N) (q * r):=by
  constructor
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1)
  · rw [Rat.mul_den]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hq.2 hr.2)

theorem input_dimension {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    n≤ bitSize (encodeInput kind I):=by
  apply le_trans (b:=(encodeInput kind I).length) _ (WordSize.length_le _)
  simp only [encodeInput,List.length_append,InstanceParser.encoded_length,List.length_ofFn,
    List.length_cons,List.length_nil]
  omega

end Lax455465Proofs.LpInputSize

end

section

namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B:ℕ) (array cursor:String) (q:ℚ≥0) (words:List ℕ) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B) (hlen:words.length+2 < B) (hfresh:cursor ≠ "rat.d"):
    Spec B (fun σ => FractionOutput (q:ℚ) σ∧ Prefix words array σ∧
      σ.vars cursor=words.length∧ words.length+1 < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (words ++ Lax455465.RationalEncoding.encodeRational q) array τ∧
        τ.vars cursor=words.length+2) 14:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  have hnum:σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hf.2.1
  have hden:σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hf.2.2.1
  have hfirst:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B array cursor words q.num (.var "rat.n") h1 (by omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars,Ne.symm hfresh])
  obtain ⟨ν,hrn,hnPost⟩:=hfirst σ ⟨⟨hp,hpos,by omega,
    by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩⟩,hden⟩
  have hroomν:(words ++ [q.num]).length < (ν.arrs array).length:=by
    rw [RamFrames.run_array_length hrn array,List.length_append,List.length_singleton]; exact hroom
  obtain ⟨τ,hrd,hdPost⟩:=RamWordBuffer.append_spec B array cursor (words ++ [q.num]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ν
      ⟨hnPost.1.1,by simpa only [List.length_append,List.length_singleton] using hnPost.1.2,hroomν,
        by rw [evalB_var_iff]; exact ⟨hnPost.2.symm,hnPost.2 ▸ hd⟩⟩
  refine ⟨τ,hrn.seq hrd,?_,?_⟩
  · simpa only [Lax455465.RationalEncoding.encodeRational,List.append_assoc,List.cons_append,List.nil_append] using hdPost.1
  · simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hdPost.2

end Lax455465Proofs.RamUnsignedEncoding

end

section

namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

@[simp] theorem length_vector {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i):
    (vector x hx).length=k:=List.length_ofFn

end Lax455465Proofs.RamOptimalDecode

end

section

namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (words:List ℕ) (array cursor:String) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ RamUnsignedBuffer.encode (qs.take (σ.vars index))) array σ∧
    σ.vars cursor=words.length+2*σ.vars index∧
    words.length+2*qs.length < (σ.arrs array).length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit array cursor:String)
    (qs:List ℚ≥0) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+2*qs.length+2 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput (qs[i]:ℚ) τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:cursor∉ body.wvars)
    (hbodyArray:array∉ body.warrs)
    (hemitIndex:index∉ (RamUnsignedEncoding.command array cursor).wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B (RamUnsignedEncoding.command array cursor) σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ cursor) (hcursorDen:cursor ≠ "rat.d"):
    Spec B (fun σ => R σ∧ Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length+2*qs.length < (σ.arrs array).length) (command index limit array cursor body)
      (fun _ τ => R τ∧ Prefix (words ++ RamUnsignedBuffer.encode qs) array τ∧
        τ.vars cursor=words.length+2*qs.length) ((K+22)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words array cursor σ∧ σ.vars index < qs.length)
      (step index array cursor body) (fun σ τ => Invariant R index qs words array cursor τ∧ τ.vars index=σ.vars index+1)
      (K+18):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ RamUnsignedBuffer.encode (qs.take i)).length=words.length+2*i:=by
      simp only [List.length_append,RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars cursor=words.length+2*i:=
      (hproduce.frame_var cursor hbodyPosition).trans hpos
    have hpν:Prefix (words ++ RamUnsignedBuffer.encode (qs.take i)) array ν:=by
      simpa only [Prefix,hproduce.frame_arr array hbodyArray] using hp
    have hroomν:words.length+2*qs.length < (ν.arrs array).length:=by
      rwa [RamFrames.run_array_length hproduce array]
    obtain ⟨μ,hemit,hemitted⟩:=RamUnsignedEncoding.command_spec B array cursor qs[i] (words ++ RamUnsignedBuffer.encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) hcursorDen ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+2*qs.length < (μ.arrs array).length:=by
      rwa [RamFrames.run_array_length hemit array]
    have hpμ:Prefix (words ++ RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars cursor=words.length+2*(i+1):=by rw [hpLen] at hemitted; omega
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
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words array cursor) qs.length (K+18)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words array cursor (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamUnsignedVector

end

section

namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

theorem num_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.num≤ M:=by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.den≤ M:=by
  simpa only [NNRat.den_coe] using h.2

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamHalfFraction
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RamRegionContext
open scoped NNRat

theorem command_spec (B M:ℕ) (q:ℚ≥0) (h2:2 < B) (hB:2*M < B)
    (hq:LpInputSize.Height M (q:ℚ)):
    Spec B (fun σ => FractionOutput (q:ℚ) σ∧ σ.vars "rat.s"=0) command
      (fun _ τ => FractionOutput ((q/2:ℚ≥0):ℚ) τ∧ τ.vars "rat.s"=0) (36*(2*M).size+20):=by
  have hnum:q.num < B:=(num_bound hq).trans_lt (by omega)
  have hden:q.den < B:=(den_bound hq).trans_lt (by omega)
  have htwoden:2*q.den < B:=(Nat.mul_le_mul_left 2 (den_bound hq)).trans_lt hB
  have hquot:(q.num:ℚ)/(q.den:ℚ)=(q:ℚ):=by
    exact congrArg (fun x:ℚ≥0 => (x:ℚ)) (NNRat.num_div_den q)
  have hvalue:fractionValue 0 q.num (2*q.den)=((q/2:ℚ≥0):ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false,Nat.cast_mul,Nat.cast_ofNat,NNRat.coe_div]
    rw [mul_comm (2:ℚ),div_mul_eq_div_div,hquot]
    norm_num
  rintro σ ⟨hqσ,hsσ⟩
  have hnσ:σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hqσ.2.1
  have hdσ:σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hqσ.2.2.1
  let ν:=σ.setVar "rat.d" (2*q.den)
  have r1:Run B (.assign "rat.d" (.mul (.lit 2) (.var "rat.d"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨hdσ.symm,hdσ ▸ hden⟩) htwoden)
  obtain ⟨τ,r2,p2⟩:=normalizeFraction_output_spec B 0 q.num (2*q.den) (by omega) hnum htwoden
    (by have:=q.den_pos; omega) ν
    ⟨by simpa [ν] using hnσ,by simp [ν],by simpa [ν] using hsσ⟩
  have hsize:(2*q.den).size≤ (2*M).size:=Nat.size_le_size (Nat.mul_le_mul_left 2 (den_bound hq))
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [hvalue] using p2,
    ((r1.seq r2).frame_var "rat.s" (by decide)).trans hsσ⟩

end Lax455465Proofs.RamHalfFraction

end

section

namespace Lax455465Proofs.PrimalEncoding
open Lax455465.RationalEncoding Lax455465.ProductNetwork DirectedFlowLP
open scoped NNRat

def converted {n:ℕ} (kind:EdgeKind) (z:Fin (1+(n*n)*(n*n))→ ℚ)  :List ℚ≥0:=
  List.ofFn fun i => if kind=.undirected∧ i.val≠0 then (z i).toNNRat/2 else (z i).toNNRat

theorem ofFn_arcs {n:ℕ} {α:Type} (f:CommodityArc n→ α):
    List.ofFn (fun i => f ((arcIndex n).symm i))=
      (List.ofFn fun s => List.ofFn fun t => List.ofFn fun u => List.ofFn fun v => f ((s,t),(u,v))).flatten.flatten.flatten:=by
  rw [List.ofFn_mul]
  simp_rw [List.ofFn_mul]
  simp only [List.flatten_flatten,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext s
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext t
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have he:(arcIndex n).symm ⟨(s.val*n+t.val)*(n*n)+(u.val*n+v.val),by simpa only [FlowLpIndices.arc_value] using (arcIndex n ((s,t),(u,v))).isLt⟩=((s,t),(u,v)):=by
    apply (arcIndex n).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    exact (FlowLpIndices.arc_value s t u v).symm
  exact congrArg f he

def arcValues {n:ℕ} (F:ArcCertificate n):List ℚ≥0:=
  List.ofFn fun i => let a:=(arcIndex n).symm i; F.arcs a.1.1 a.1.2 a.2.1 a.2.2

theorem converted_eq {n:ℕ} (kind:EdgeKind) (z:Fin (1+(n*n)*(n*n))→ ℚ):
    converted kind z=[(CertificatePostprocessing.primalFlow z).value]++
      arcValues (CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)):=by
  unfold converted
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · simp only [List.ofFn_succ,List.ofFn_zero]
    congr 1
    have hi:(0:Fin 1).castLE (Nat.le_add_right 1 ((n*n)*(n*n)))=variableIndex n (.inl 0):=by
      apply Fin.ext
      exact (FlowLpIndices.value_variable 0).symm
    rw [hi]
    simp [FlowLpIndices.value_variable,CertificatePostprocessing.primalFlow]
  · apply congrArg List.ofFn
    funext i
    have hi:i.natAdd 1=variableIndex n (.inr ((arcIndex n).symm i)):=by
      apply Fin.ext
      simp [variableIndex,finSumFinEquiv,Equiv.sumCongr]
    have hnz:(i.natAdd 1).val ≠ 0:=by simp
    have hi0:variableIndex n (.inr ((arcIndex n).symm i)) ≠ 0:=by
      intro h; apply hnz; rw [hi,h]; rfl
    rw [hi]
    cases kind <;> simp [CertificatePostprocessing.convertFlow,CertificatePostprocessing.primalFlow,UndirectedConversion.halve,hi0]

theorem encoded_arcs {n:ℕ} (F:ArcCertificate n):
    RamUnsignedBuffer.encode ([F.value]++arcValues F)=encodeArcs F:=by
  unfold RamUnsignedBuffer.encode arcValues
  rw [ofFn_arcs (fun a:CommodityArc n => F.arcs a.1.1 a.1.2 a.2.1 a.2.2)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  unfold encodeArcs
  congr 1
  simp only [List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def]

theorem encoding {n:ℕ} (kind:EdgeKind) (z:Fin (1+(n*n)*(n*n))→ ℚ):
    RamUnsignedBuffer.encode (converted kind z)=
      encodeArcs (CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)):=by
  rw [converted_eq]
  have hv:(CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)).value=
      (CertificatePostprocessing.primalFlow z).value:=by cases kind <;> rfl
  rw [←hv]
  exact encoded_arcs _

end Lax455465Proofs.PrimalEncoding

end

section

namespace Lax455465Proofs.RamFlowConvert
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def values (kind:EdgeKind) (qs:List ℚ≥0):List ℚ≥0:=
  List.ofFn fun i:Fin qs.length => if kind=.undirected∧ i.val≠0 then qs[i.val]/2 else qs[i.val]

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {kind:EdgeKind} {qs:List ℚ≥0} (h:Context kind qs σ)
    (hx:∀ x∈["flow.kind","lp.columns"],x∉cmd.wvars) (ha:"flow.primal"∉cmd.warrs):Context kind qs τ:=by
  simpa only [Context,Prefix,rr.frame_var "flow.kind" (hx _ (by simp)),
    rr.frame_var "lp.columns" (hx _ (by simp)),rr.frame_arr "flow.primal" ha] using h

def bodyCost (M:ℕ):ℕ:=36*(2*M).size+42

def cost (k M:ℕ):ℕ:=(bodyCost M+22)*k+8

theorem choose_spec (B M:ℕ) (kind:EdgeKind) (q:ℚ≥0) (i:ℕ)
    (h2:2 < B) (hB:2*M < B) (hi:i < B) (hq:LpInputSize.Height M (q:ℚ)):
    Spec B (fun σ => σ.vars "flow.kind"=RamGraphHeader.tag kind∧ σ.vars "emit.coordinate"=i∧
      FractionOutput (q:ℚ) σ∧ σ.vars "rat.s"=0) choose
      (fun _ τ => FractionOutput ((if kind=.undirected∧ i≠0 then q/2 else q:ℚ≥0):ℚ) τ)
      (36*(2*M).size+28):=by
  rintro σ ⟨hk,hiσ,hqσ,hs⟩
  have ht:RamGraphHeader.tag kind < B:=by cases kind <;> simp only [RamGraphHeader.tag] <;> omega
  have hc:=evalB_condEq (evalB_var (hk ▸ ht)) (evalB_lit (by omega:0 < B))
  rw [hk] at hc
  cases kind with
  | directed =>
    have hc':(Cond.eq (.var "flow.kind") (.lit 0)).evalB B σ=some false:=hc
    exact ⟨σ,(Run.ite_false (c:=.ite (.eq (.var "emit.coordinate") (.lit 0)) .skip RamHalfFraction.command) hc' Run.skip).mono
      (by dsimp [Cond.size,Expr.size]; omega),by simpa using hqσ⟩
  | undirected =>
    have hc':(Cond.eq (.var "flow.kind") (.lit 0)).evalB B σ=some true:=hc
    have hci:=evalB_condEq (evalB_var (hiσ ▸ hi)) (evalB_lit (by omega:0 < B))
    rw [hiσ] at hci
    by_cases hz:i=0
    · have hci':(Cond.eq (.var "emit.coordinate") (.lit 0)).evalB B σ=some true:=by simpa [hz] using hci
      exact ⟨σ,(Run.ite_true (d:=.skip) hc' (Run.ite_true (d:=RamHalfFraction.command) hci' Run.skip)).mono
        (by dsimp [Cond.size,Expr.size]; omega),by simpa [hz] using hqσ⟩
    · have hci':(Cond.eq (.var "emit.coordinate") (.lit 0)).evalB B σ=some false:=by simpa [hz] using hci
      obtain ⟨τ,rr,pr⟩:=RamHalfFraction.command_spec B M q h2 hB hq σ ⟨hqσ,hs⟩
      exact ⟨τ,(Run.ite_true (d:=.skip) hc' (Run.ite_false (c:=.skip) hci' rr)).mono
        (by dsimp [Cond.size,Expr.size]; omega),by simpa [hz] using pr.1⟩

theorem value_height (M:ℕ) (kind:EdgeKind) (qs:List ℚ≥0)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)) (i:ℕ) (hi:i < (values kind qs).length):
    LpInputSize.Height (2*M) ((values kind qs)[i]:ℚ):=by
  have hi':i < qs.length:=by simpa [values] using hi
  simp only [values,List.getElem_ofFn]
  split_ifs
  · have hh:=LpInputSize.height_mul (hq qs[i] (List.getElem_mem hi'))
      (show LpInputSize.Height 2 (1/2:ℚ) from by norm_num [LpInputSize.Height])
    change LpInputSize.Height (2*M) ((qs[i]:ℚ)/2)
    simpa only [div_eq_mul_inv,one_mul,Nat.mul_comm] using hh
  · exact LpInputSize.height_mono (hq qs[i] (List.getElem_mem hi')) (by omega)

theorem body_spec (B M:ℕ) (kind:EdgeKind) (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length)
    (h2:2 < B) (hB:2*M < B) (hlen:2*qs.length+2 < B)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)):
    Spec B (fun σ => Context kind qs σ∧ σ.vars "emit.coordinate"=i) body
      (fun _ τ => Context kind qs τ∧
        FractionOutput ((if kind=.undirected∧ i≠0 then qs[i]/2 else qs[i]:ℚ≥0):ℚ) τ) (bodyCost M):=by
  rintro σ ⟨hc,hidx⟩
  have hh:=hq qs[i] (List.getElem_mem hi)
  obtain ⟨ν,r1,p1⟩:=RamUnsignedBuffer.read_spec B "flow.primal" "emit.coordinate" qs i hi h2 (by omega)
    ((num_bound hh).trans_lt (by omega)) ((den_bound hh).trans_lt (by omega)) (by decide) σ ⟨hc.2.2,hidx⟩
  have hcν:=frame r1 hc (by decide) (by decide)
  obtain ⟨τ,r2,p2⟩:=choose_spec B M kind qs[i] i h2 hB (by omega) hh ν
    ⟨hcν.1,(r1.frame_var "emit.coordinate" (by decide)).trans hidx,p1⟩
  exact ⟨τ,(r1.seq r2).mono (by dsimp [bodyCost]; omega),frame r2 hcν (by decide) (by decide),p2⟩

theorem command_spec (B M:ℕ) (kind:EdgeKind) (qs:List ℚ≥0)
    (h2:2 < B) (hB:2*M < B) (hlen:2*qs.length+2 < B)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)):
    Spec B (fun σ => Context kind qs σ∧ 2*qs.length < (σ.arrs "flow.converted").length) command
      (fun _ τ => Context kind qs τ∧ Prefix (RamUnsignedBuffer.encode (values kind qs)) "flow.converted" τ)
      (cost qs.length M):=by
  have hvalues:(values kind qs).length=qs.length:=List.length_ofFn
  have hloop:=RamUnsignedVector.command_spec B (bodyCost M) (Context kind qs)
    "emit.coordinate" "lp.columns" "flow.converted" "emit.convertedPos" (values kind qs) [] body (by omega)
    (by simpa only [List.length_nil,Nat.zero_add,hvalues] using hlen)
    (fun i hi => (num_bound (value_height M kind qs hq i hi)).trans_lt hB)
    (fun i hi => (den_bound (value_height M kind qs hq i hi)).trans_lt hB)
    (fun _ h => h.2.1.trans hvalues.symm)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      have hi':i < qs.length:=hvalues ▸ hi
      obtain ⟨τ,rr,pr⟩:=body_spec B M kind qs i hi' h2 hB hlen hq σ hσ
      exact ⟨τ,rr,pr.1,by simpa only [values,List.getElem_ofFn] using pr.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hc,hroom⟩
  let ν:=σ.setVar "emit.convertedPos" 0
  have rz:Run B (.assign "emit.convertedPos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rl,pl⟩:=hloop ν ⟨frame rz hc (by decide) (by decide),by intro i hi; simp at hi,
    by simp [ν],by simpa only [List.length_nil,Nat.zero_add,hvalues,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [cost,hvalues]; omega),pl.1,by simpa only [List.nil_append] using pl.2.1⟩

theorem primal_values {n:ℕ} (kind:EdgeKind) (z:Fin (1+(n*n)*(n*n))→ ℚ) (hz:∀ i,0≤ z i):
    values kind (RamOptimalDecode.vector z hz)=PrimalEncoding.converted kind z:=by
  have hv:RamOptimalDecode.vector z hz=List.ofFn (fun i => (z i).toNNRat):=by
    change List.ofFn (fun i => (⟨z i,hz i⟩:ℚ≥0))=_
    apply congrArg List.ofFn
    funext i
    apply NNRat.coe_injective
    simp [Rat.coe_toNNRat _ (hz i)]
  rw [hv]
  unfold values PrimalEncoding.converted
  simp only [List.length_ofFn,List.getElem_ofFn,Fin.val_cast,Fin.eta]

end Lax455465Proofs.RamFlowConvert

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

namespace Lax455465Proofs.RamJointOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def cost (n k M:ℕ):ℕ:=RamFlowConvert.cost k M+13*n+26*k+18

theorem mask_data {n:ℕ} (S:Finset (Fin n)) {σ:Env}
    (hp:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ):
    RamEmitWords.Data "cut.flags" 2 (encodeCut S) σ:=by
  intro i hi
  have hi':i < n:=by simpa only [encodeCut,List.length_ofFn] using hi
  have hflags:(CutScoreData.vertexFlags S).length=n:=List.length_ofFn
  have hidx:2*i < (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)).length:=by
    rw [RamUnsignedBuffer.length_encode,hflags]; omega
  have hn:=RamUnsignedBuffer.numerator_at (CutScoreData.vertexFlags S) i (by omega)
  rw [List.getElem?_eq_getElem hidx] at hn
  have h:=(hp (2*i) hidx).trans hn
  simpa [encodeCut,CutScoreData.vertexFlags,MaskedMassData.flags,ResidualData.mask,apply_ite] using h

theorem buffer_data (xs:List ℕ) {σ:Env} (hp:Prefix xs "flow.converted" σ):
    RamEmitWords.Data "flow.converted" 1 xs σ:=by
  intro i hi
  simpa only [Nat.one_mul] using hp i hi

theorem emit_spec (B:ℕ) {n:ℕ} (S:Finset (Fin n)) (qs:List ℚ≥0) (front:List ℕ)
    (h2:2 < B) (hvertex:2*n < B) (hlen:2*qs.length < B)
    (hq:∀ q∈qs,q.num < B∧ q.den < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "lp.columns"=qs.length∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ∧
      Prefix (RamUnsignedBuffer.encode qs) "flow.converted" σ∧ σ.out=front) emit
      (fun _ τ => τ.out=front++encodeCut S++RamUnsignedBuffer.encode qs) (13*n+26*qs.length+18):=by
  rintro σ ⟨hn,hcols,hmask,hflow,hout⟩
  let ν:=σ.setVar "emit.count" n
  have r1:Run B (.assign "emit.count" (.var "metric.n")) σ ν 2:=Run.assign (by
    rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n < B)⟩)
  have hcutlen:(encodeCut S).length=n:=List.length_ofFn
  have hcutwords:∀ x∈encodeCut S,x < B:=by
    intro x hx
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hx
    split_ifs <;> omega
  obtain ⟨μ,r2,p2⟩:=RamEmitWords.command_spec B "cut.flags" 2 (encodeCut S) front (by omega) h2
    (by rwa [hcutlen]) (by rw [hcutlen]; omega) hcutwords ν
    ⟨mask_data S hmask,by simp [ν,hcutlen],hout⟩
  let ρ:=μ.setVar "emit.count" (2*qs.length)
  have hcμ:μ.vars "lp.columns"=qs.length:=
    (r2.frame_var "lp.columns" (by decide)).trans (by simpa [ν] using hcols)
  have r3:Run B (.assign "emit.count" (.mul (.lit 2) (.var "lp.columns"))) μ ρ 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit h2)
      (by rw [evalB_var_iff]; exact ⟨hcμ.symm,hcμ ▸ (by omega:qs.length < B)⟩) hlen)
  have hflowρ:Prefix (RamUnsignedBuffer.encode qs) "flow.converted" ρ:=by
    simpa only [Prefix,ρ,arrs_setVar,r2.frame_arr "flow.converted" (by decide),ν,arrs_setVar] using hflow
  have hwords:∀ x∈RamUnsignedBuffer.encode qs,x < B:=by
    intro x hx
    obtain ⟨q,hq',hx⟩:=List.mem_flatMap.mp hx
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact (hq q hq').1
    · exact (hq q hq').2
  obtain ⟨τ,r4,p4⟩:=RamEmitWords.command_spec B "flow.converted" 1 (RamUnsignedBuffer.encode qs)
    (front++encodeCut S) (by omega) (by omega)
    (by simpa only [Nat.one_mul,RamUnsignedBuffer.length_encode] using hlen)
    (by simpa only [RamUnsignedBuffer.length_encode] using hlen) hwords ρ
    ⟨buffer_data _ hflowρ,by simp [ρ],p2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hcutlen,RamUnsignedBuffer.length_encode]; omega),p4⟩

theorem command_spec (B M:ℕ) {n:ℕ} (kind:EdgeKind) (S:Finset (Fin n))
    (qs:List ℚ≥0) (front:List ℕ) (h2:2 < B) (hB:2*M < B)
    (hvertex:2*n < B) (hlen:2*qs.length+2 < B)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)):
    Spec B (fun σ => RamFlowConvert.Context kind qs σ∧ σ.vars "metric.n"=n∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ∧
      2*qs.length < (σ.arrs "flow.converted").length∧ σ.out=front) command
      (fun _ τ => τ.out=front++encodeCut S++RamUnsignedBuffer.encode (RamFlowConvert.values kind qs))
      (cost n qs.length M):=by
  rintro σ ⟨hc,hn,hmask,hroom,hout⟩
  obtain ⟨ν,r1,p1⟩:=RamFlowConvert.command_spec B M kind qs h2 hB hlen hq σ ⟨hc,hroom⟩
  have hvlen:(RamFlowConvert.values kind qs).length=qs.length:=List.length_ofFn
  have hwords:∀ q∈RamFlowConvert.values kind qs,q.num < B∧ q.den < B:=by
    intro q hmem
    obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hmem
    have hh:=RamFlowConvert.value_height M kind qs hq i hi
    exact ⟨(num_bound hh).trans_lt hB,(den_bound hh).trans_lt hB⟩
  obtain ⟨τ,r2,p2⟩:=emit_spec B S (RamFlowConvert.values kind qs) front h2 hvertex
    (by rw [hvlen]; omega) hwords ν
    ⟨(r1.frame_var "metric.n" (by decide)).trans hn,p1.1.2.1.trans hvlen.symm,
      by simpa only [Prefix,r1.frame_arr "cut.flags" (by decide)] using hmask,p1.2,
      (r1.out_eq (by decide)).trans hout⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hvlen]; dsimp [cost]; omega),p2⟩

theorem primal_spec (B M:ℕ) {n:ℕ} (kind:EdgeKind) (S:Finset (Fin n))
    (z:Fin (1+(n*n)*(n*n))→ ℚ) (hz:∀ i,0≤ z i)
    (h2:2 < B) (hB:2*M < B) (hvertex:2*n < B)
    (hlen:2*(1+(n*n)*(n*n))+2 < B) (hq:∀ i,LpInputSize.Height M (z i)):
    Spec B (fun σ => RamFlowConvert.Context kind (RamOptimalDecode.vector z hz) σ∧ σ.vars "metric.n"=n∧
      Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length∧ σ.out=[]) command
      (fun _ τ => τ.out=Lax455465.FlowCutCertificate.encodeCertificate
        ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩)
      (cost n (1+(n*n)*(n*n)) M):=by
  have hh:∀ q∈RamOptimalDecode.vector z hz,LpInputSize.Height M (q:ℚ):=by
    intro q hmem
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hmem
    exact hq i
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩:=command_spec B M kind S (RamOptimalDecode.vector z hz) [] h2 hB hvertex
    (by simpa only [RamOptimalDecode.length_vector] using hlen) hh σ (by simpa only [RamOptimalDecode.length_vector] using hσ)
  refine ⟨τ,by simpa only [RamOptimalDecode.length_vector] using rr,?_⟩
  simpa only [List.nil_append,RamFlowConvert.primal_values,PrimalEncoding.encoding,
    Lax455465.FlowCutCertificate.encodeCertificate] using pr

end Lax455465Proofs.RamJointOutput

end

section

namespace Lax455465Proofs.RamOutputResources
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

theorem time_bound (P:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    RamJointOutput.cost n (1+(n*n)*(n*n)) (2^(P.eval (bitSize (encodeInput kind I))))≤
      (timeBound P).eval (bitSize (encodeInput kind I)):=by
  let L:=bitSize (encodeInput kind I)
  let w:=P.eval L
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hs:(2*2^w).size=w+2:=by
    rw [show 2*2^w=2^(w+1) by rw [pow_succ,Nat.mul_comm],Nat.size_pow]
  simp only [RamJointOutput.cost,RamFlowConvert.cost,RamFlowConvert.bodyCost,timeBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_pow]
  change (36*(2*2^w).size+42+22)*(1+n*n*(n*n))+8+13*n+26*(1+n*n*(n*n))+18≤
    (36*(w+2)+90)*(1+L^4)+13*L+26
  have hcols:1+n*n*(n*n)≤ 1+L^4:=by
    simpa only [pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using
      Nat.add_le_add_left (Nat.pow_le_pow_left hn 4) 1
  rw [hs]
  have hm:=Nat.mul_le_mul_left (36*(w+2)+90) hcols
  nlinarith

theorem host_bounds (P:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (W:ℕ)
    (hW:(wordBound P).eval (bitSize (encodeInput kind I))≤ W):
    2 < 2^W∧ 2*2^(P.eval (bitSize (encodeInput kind I))) < 2^W∧
      2*n < 2^W∧ 2*(1+(n*n)*(n*n))+2 < 2^W:=by
  let L:=bitSize (encodeInput kind I)
  let w:=P.eval L
  have hn:n≤ L:=LpInputSize.input_dimension kind I
  have hcols:1+n*n*(n*n)≤ 1+L^4:=by
    simpa only [pow_succ,pow_zero,Nat.mul_one,Nat.one_mul,Nat.mul_assoc] using
      Nat.add_le_add_left (Nat.pow_le_pow_left hn 4) 1
  have hW':2*w+2*(1+L^4)+2*L+16≤ W:=by simpa [wordBound,L,w] using hW
  have hWP:W < 2^W:=Nat.lt_two_pow_self
  have hp:2^(w+2)≤ 2^W:=Nat.pow_le_pow_right (by decide) (by omega)
  have hpos:=Nat.two_pow_pos w
  have htwice:2*2^w < 2^W:=by rw [pow_add] at hp; norm_num at hp; omega
  exact ⟨by omega,htwice,by omega,by omega⟩

theorem command_spec (P:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (S:Finset (Fin n))
    (z:Fin (1+(n*n)*(n*n))→ ℚ) (hz:∀ i,0≤ z i)
    (hheight:∀ i,LpInputSize.Height (2^(P.eval (bitSize (encodeInput kind I)))) (z i))
    (W:ℕ) (hW:(wordBound P).eval (bitSize (encodeInput kind I))≤ W):
    Spec (2^W) (fun σ => RamFlowConvert.Context kind (RamOptimalDecode.vector z hz) σ∧ σ.vars "metric.n"=n∧
      RamVirtualState.Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length∧ σ.out=[]) RamJointOutput.command
      (fun _ τ => τ.out=Lax455465.FlowCutCertificate.encodeCertificate
        ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩)
      ((timeBound P).eval (bitSize (encodeInput kind I))):=by
  obtain ⟨h2,hB,hvertex,hlen⟩:=host_bounds P kind I W hW
  intro σ hσ
  obtain ⟨τ,rr,pr⟩:=RamJointOutput.primal_spec (2^W) (2^(P.eval (bitSize (encodeInput kind I))))
    kind S z hz h2 hB hvertex hlen hheight σ hσ
  exact ⟨τ,rr.mono (time_bound P kind I),pr⟩

end Lax455465Proofs.RamOutputResources

end

theorem solution:∀ (P:@Polynomial Nat Nat.instSemiring) {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind)
  (I:Lax455465.RationalEncoding.RationalInstance n) (S:Finset (Fin n))
  (z:
    Fin
        (Nat.add ((1:Nat))
          (Nat.mul (Nat.mul n n)
            (Nat.mul n n)))→
      Rat)
  (hz:
    ∀
      (i:
        Fin
          (Nat.add ((1:Nat))
            (Nat.mul (Nat.mul n n)
              (Nat.mul n n)))),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (z i)),
  (∀
      (i:
        Fin
          (Nat.add ((1:Nat))
            (Nat.mul (Nat.mul n n)
              (Nat.mul n n)))),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (z i))→
    ∀ (W:Nat),
      Nat.le
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.wordBound P))
          W→
        Lax808846Proofs.Reasoning.Spec
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) W)
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And
              (Lax455465Proofs.RamFlowConvert.Context kind
                (@Lax455465Proofs.RamOptimalDecode.vector
                  (Nat.add
                    ((1:Nat))
                    (Nat.mul
                      (Nat.mul n n)
                      (Nat.mul n n)))
                  z hz)
                σ)
              (And (@Eq Nat (σ.vars "metric.n") n)
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix
                    (Lax455465Proofs.RamUnsignedBuffer.encode (@Lax455465Proofs.CutScoreData.vertexFlags n S))
                    "cut.flags" σ)
                  (And
                    (Nat.lt
                      (Nat.mul
                        ((2:Nat))
                        (Nat.add
                          ((1:Nat))
                          (Nat.mul
                            (Nat.mul n n)
                            (Nat.mul n n))))
                      (@List.length Nat (σ.arrs "flow.converted")))
                    (@Eq (List Nat) σ.out (@List.nil Nat))))))
          Lax455465Proofs.RamJointOutput.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            @Eq (List Nat) τ.out
              (@Lax455465.FlowCutCertificate.encodeCertificate n
                (@Lax455465.FlowCutCertificate.Certificate.mk n S
                  (@Lax455465Proofs.CertificatePostprocessing.convertFlow n kind
                    (@Lax455465Proofs.CertificatePostprocessing.primalFlow n z)))))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.timeBound P)):= @Lax455465Proofs.RamOutputResources.command_spec
