-- Prove2me | solution 1 for Lax109476Proofs.RamRecoverySelector.selectEntry_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:39:26.31423+00:00
-- url     : https://prove2.me/submissions/fdacae09-7770-46a1-b995-3905ad571b33

import Mathlib.Tactic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces

set_option maxHeartbeats 0
set_option maxRecDepth 30000

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
namespace Lax109476Proofs.EllipsoidStateSize
end Lax109476Proofs.EllipsoidStateSize
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
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
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
    (refine let c0:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat:= @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat)); let c5:Env:=Env.setVar σ "left.s" c4; let c6:String:=c2 ".n"; let c7:Nat:=Env.vars c5 "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat)); let c9:Env:=Env.setVar c5 "left.n" c8; let c10:String:=c2 ".d"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "left.d" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Expr:=Expr.get c3 (Expr.var "vec.i"); let c17:Nat:=c15 (Expr.size c16); let c18:Expr:=Expr.get c6 (Expr.var "vec.i"); let c19:Nat:=c15 (Expr.size c18); let c20:Expr:=Expr.get c10 (Expr.var "vec.i"); let c21:Nat:=c15 (Expr.size c20); let c22:Nat:=c14 c19 c21; let c23:Com:=Com.assign "left.n" c18; let c24:Com:=Com.assign "left.d" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (loadLeft a) σ σ' ((9:Nat))) (c1 σ')) c13 (@And.intro (Run B (loadLeft a) σ c13 ((9:Nat))) (c1 c13) (RunStep.mono B (loadLeft a) σ c13 (c14 c17 c22) ((9:Nat)) (RunStep.seq B (Com.assign "left.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "left.s" c16 c4 (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3955_0_0_0)) (?nAX_g3955_0_0_1) ?_)) (RunStep.seq B c23 c24 c5 c9 c13 c19 c21 (RunStep.assign B c5 "left.n" c18 c8 (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7 (RunStep.eval_var B c5 "vec.i" (?nAX_g3955_0_0_2)) (?nAX_g3955_0_0_3) ?_)) (RunStep.assign B c9 "left.d" c20 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g3955_0_0_4)) (?nAX_g3955_0_0_5) ?_)))) (?nAX_g3955_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3955_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3955_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftOutput]

end Lax109476Proofs.RamRationalArrays

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

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "left.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "left.s")); let c7:Nat:=c5 (Expr.size (Expr.var "left.n")); let c8:Nat:=c5 (Expr.size (Expr.var "left.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B leftToResult σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c3 (@And.intro (Run B leftToResult σ c3 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c3) (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4081_0_0_0))) (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2 (RunStep.eval_var B c1 "left.d" (?nAX_g4081_0_0_1))))) (?nAX_g4081_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

end Lax109476Proofs.RamCopy

end

section

namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

@[simp] theorem flatten_length {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ):
    (flatten A).length=m * n:=by simp [flatten]

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

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax109476Proofs.RamPadSelector

end

section

namespace Lax109476Proofs.RamRecoverySelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds RecoveryQueryEntries

theorem negativeOne_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) negativeOne (fun _ τ => FractionOutput (-1) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c3:Env:=Env.setVar c2 "rat.n" ((1:Nat)); let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c5 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); let c7:Nat→ Nat:=c5 c6; let c8:Nat:=c7 c6; let c9:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B negativeOne σ σ' ((6:Nat))) (c1 σ')) c4 (@And.intro (Run B negativeOne σ c4 ((6:Nat))) (c1 c4) (RunStep.mono B negativeOne σ c4 (c7 c8) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) (Com.seq c9 c10) σ c2 c4 c6 c8 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B c9 c10 c2 c3 c4 c6 c6 (RunStep.assign B c2 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g4449_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4449_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals norm_num [FractionOutput,fractionValue]

def fields:List String:= ["point.m", "point.n", "point.k", "query.row", "query.col"]

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n k:ℕ) (P:Program ℚ m n) (hk:k < n)
    (i:Fin ((m + (n + n)) + 1)) (j:Fin n) (hM:1≤ M) (hMB:M < B)
    (hB:((m + (n + n)) + 1) * n + m + (n + n) + 4 < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Represents "point.A" (RamMatrixStorage.flatten P.A) σ∧
      σ.vars "point.m"=m∧ σ.vars "point.n"=n∧ σ.vars "point.k"=k∧
      σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => FractionOutput (entry P k i j) τ) 76:=by
  have h1:1 < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hkB:k < B:=hk.trans hn
  have hmnB:m * n < B:=(Nat.mul_le_mul_right n (show m≤ (m + (n + n)) + 1 by omega)).trans_lt (by omega)
  have hzero:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hone:=RamPadSelector.constantFraction_spec B 1 h1 h1
  have hneg:=negativeOne_spec B h1
  rintro σ ⟨hσA,hσm,hσn,hσk,hσi,hσj⟩
  by_cases hi:i.val < m
  · let ii:Fin m:= ⟨i.val,hi⟩
    let index:=i.val * n + j.val
    have hindex:index < (RamMatrixStorage.flatten P.A).length:=by
      simpa [index,ii,RamMatrixStorage.flatten] using RamMatrixStorage.row_index_lt ii j
    have hindexB:index < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hindex:index < m * n).trans hmnB
    have hmulB:i.val * n < B:=by dsimp only [index] at hindexB; omega
    have hentry:(RamMatrixStorage.flatten P.A)[index]=P.A ii j:=RamMatrixStorage.flatten_entry P.A ii j
    have hq:=hA ii j
    have hload:=spec_with_fields fields
      (loadLeft_spec B "point.A" (RamMatrixStorage.flatten P.A) index hindex h1 hindexB
        (by rw [hentry]; exact hq.1.trans_lt hMB) (by rw [hentry]; exact hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    have hresult:=RamCopy.leftToResult_spec B (P.A ii j) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "point.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P k i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((76:Nat))) (c3 σ'); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=Nat.mul (Env.vars σ "query.row") (Env.vars σ "point.n"); let c7:Nat:=c5 c6 (Env.vars σ "query.col"); let c8:Env:=Env.setVar σ "vec.i" c7; let c9:Env→ Nat→ Prop:=Run B (loadLeft "point.A") c8; let c10:List Rat:= @flatten m n (@Program.A Rat m n P); let c11:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c10 index hindex); let c12:Env→ Prop:=FieldsAgree fields c8; let c13:String→ List Nat:=Env.arrs c8; let c14:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((9:Nat))) (And (c11 σ') (And (c12 σ') (@Eq (String→ List Nat) (Env.arrs σ') c13))); let c15:Env→ Prop:=Represents "point.A" c10; let c16:Rat:= @Program.A Rat m n P ii j; let c17:Env→ Prop:=FractionOutput c16; let c18:Env→ Prop:=LeftOutput c16; let c19:Nat→ Nat:=c5 ((1:Nat)); let c20:Nat→ Nat:=c5 (c19 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "point.m")))); let c21:Expr:=Expr.add (Expr.mul (Expr.var "query.row") (Expr.var "point.n")) (Expr.var "query.col"); let c22:Nat:=c19 (Expr.size c21); let c23:Nat:=c5 ((9:Nat)) ((6:Nat)); let c24:Nat:=c5 c22 c23; let c25:Com:=Com.assign "vec.i" c21; let c26:Com:=Com.seq c25 (Com.seq (loadLeft "point.A") RamCopy.leftToResult); let c27:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")); let c28:Cond:=Cond.lt (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k"); let c29:Cond:=Cond.eq (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")); let c30:Com:=Com.ite c29 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c31:Com:=Com.ite c28 c30 (RamPadSelector.constantFraction ((0:Nat))); let c32:Expr:=Expr.add (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n"); let c33:Cond:=Cond.lt (Expr.var "query.row") c32; let c34:Expr:=Expr.sub (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n"); let c35:Cond:=Cond.lt c34 (Expr.var "point.k"); let c36:Cond:=Cond.eq (Expr.var "query.col") c34; let c37:Com:=Com.ite c36 negativeOne (RamPadSelector.constantFraction ((0:Nat))); let c38:Com:=Com.ite c35 c37 (RamPadSelector.constantFraction ((0:Nat))); let c39:Com:=Com.ite (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c40:Com:=Com.ite c33 c38 c39; let c41:Com:=Com.ite c27 c31 c40; let c42:Nat:=c5 (Env.vars σ "point.m") (Env.vars σ "point.n"); let c43:Prop:=Nat.lt (Env.vars σ "query.row") c42; let c44:Prop:=Not c43; let c45:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c46:Nat:=c45 (Env.vars σ "query.row") (Env.vars σ "point.m"); let c47:Prop:=Nat.lt c46 (Env.vars σ "point.k"); let c48:Prop:=Not c47; let c49:Prop:= @Eq Nat (Env.vars σ "query.col") c46; let c50:Prop:=Not c49; let c51:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c52:Nat→ Env:=Env.setVar c51 "rat.n"; let c53:Env:=c52 ((1:Nat)); let c54:Env:=Env.setVar c53 "rat.d" ((1:Nat)); let c55:Nat→ Nat:=c5 (c19 (Cond.size c27)); let c56:Nat→ Nat:=c5 (c19 (Cond.size c28)); let c57:Nat→ Nat:=c5 (c19 (Cond.size c29)); let c58:Nat:=c19 (Expr.size (Expr.lit ((0:Nat)))); let c59:Nat→ Nat:=c5 c58; let c60:Nat:=c19 (Expr.size (Expr.lit ((1:Nat)))); let c61:Nat→ Nat:=c5 c60; let c62:Nat:=c61 c60; let c63:Nat:=c59 c62; let c64:Nat:=c57 c63; let c65:Nat:=c56 c64; let c66:Nat:=c55 c65; let c67:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c68:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c69:Com:=Com.seq c67 c68; let c70:Env:=c52 ((0:Nat)); let c71:Env:=Env.setVar c70 "rat.d" ((1:Nat)); let c72:Nat:=c59 c60; let c73:Nat:=c59 c72; let c74:Nat:=c57 c73; let c75:Nat:=c56 c74; let c76:Nat:=c55 c75; let c77:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c78:Nat:=c56 c73; let c79:Nat:=c55 c78; let c80:Nat:=c5 c42 (Env.vars σ "point.n"); let c81:Prop:=Nat.lt (Env.vars σ "query.row") c80; let c82:Prop:=Not c81; let c83:Nat:=c45 c46 (Env.vars σ "point.n"); let c84:Prop:=Nat.lt c83 (Env.vars σ "point.k"); let c85:Prop:=Not c84; let c86:Prop:= @Eq Nat (Env.vars σ "query.col") c83; let c87:Prop:=Not c86; let c88:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c89:Env:=Env.setVar c88 "rat.n" ((1:Nat)); let c90:Env:=Env.setVar c89 "rat.d" ((1:Nat)); let c91:Nat→ Nat:=c5 (c19 (Cond.size c33)); let c92:Nat→ Nat:=c5 (c19 (Cond.size c35)); let c93:Nat→ Nat:=c5 (c19 (Cond.size c36)); let c94:Nat:=c61 c62; let c95:Nat:=c93 c94; let c96:Nat:=c92 c95; let c97:Nat:=c91 c96; let c98:Nat:=c55 c97; let c99:Nat:=c93 c73; let c100:Nat:=c92 c99; let c101:Nat:=c91 c100; let c102:Nat:=c55 c101; let c103:Nat:=c92 c73; let c104:Nat:=c91 c103; let c105:Nat:=c55 c104; let c106:Prop:= @Eq Nat (Env.vars σ "query.col") (Env.vars σ "point.k"); let c107:Prop:=Not c106; let c108:Nat→ Nat:=c5 (c19 (Cond.size (Cond.eq (Expr.var "query.col") (Expr.var "point.k")))); let c109:Nat:=c108 c63; let c110:Nat:=c91 c109; let c111:Nat:=c55 c110; let c112:Nat:=c108 c73; let c113:Nat:=c91 c112; let c114:Nat:=c55 c113; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (c15 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") index)) (loadLeft "point.A") (fun (σ_1 τ:Env) => And (c11 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload c8 ?_) fun (w:Env) (h:And (c9 w ((9:Nat))) (And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)))) => let c0_1:Prop:=c9 w ((9:Nat)); let c1_1:Prop:=And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B RamCopy.leftToResult w σ' ((6:Nat))) (c17 σ'); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c4) (RunStep.use B c18 RamCopy.leftToResult (fun (x τ:Env) => c17 τ) ((6:Nat)) hresult w ?_) fun (w_1:Env) (h_1:And (Run B RamCopy.leftToResult w w_1 ((6:Nat))) (c17 w_1)) => let c0_2:Prop:=Run B RamCopy.leftToResult w w_1 ((6:Nat)); @And.casesOn c0_2 (c17 w_1) (fun (x:And c0_2 (c17 w_1)) => @Exists Env c4) h_1 fun (left_1:c0_2) (right_1:c17 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectEntry σ w_1 ((76:Nat))) (c3 w_1) (RunStep.mono B selectEntry σ w_1 (c20 c24) ((76:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ w_1 c24 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_0)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_1)) hcase) (RunStep.seq B c25 (Com.seq (loadLeft "point.A") RamCopy.leftToResult) σ c8 w_1 c22 c23 (RunStep.assign B σ "vec.i" c21 c7 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.row") (Expr.var "point.n")) (Expr.var "query.col") c6 (Env.vars σ "query.col") (RunStep.eval_mul B σ (Expr.var "query.row") (Expr.var "point.n") (Env.vars σ "query.row") (Env.vars σ "point.n") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_2)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_3)) ?_) (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_4)) ?_)) (RunStep.seq B (loadLeft "point.A") RamCopy.leftToResult c8 w w_1 ((9:Nat)) ((6:Nat)) left left_1))) (?nAX_g4452_0_0_5)) ?_)) fun (hcase:c1) => @Or.casesOn c43 c44 (fun (x:Or c43 c44) => @Exists Env c4) (Classical.em c43) (fun (hcase_1:c43) => @Or.casesOn c47 c48 (fun (x:Or c47 c48) => @Exists Env c4) (Classical.em c47) (fun (hcase_2:c47) => @Or.casesOn c49 c50 (fun (x:Or c49 c50) => @Exists Env c4) (Classical.em c49) (fun (hcase_3:c49) => @Exists.intro Env c4 c54 (@And.intro (Run B selectEntry σ c54 ((76:Nat))) (c3 c54) (RunStep.mono B selectEntry σ c54 (c20 c66) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c54 c66 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_6)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_7)) hcase) (RunStep.ite_true B c27 c31 c40 σ c54 c65 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_8)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_9)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_10)) (?nAX_g4452_0_0_11)) hcase_1) (RunStep.ite_true B c28 c30 (RamPadSelector.constantFraction ((0:Nat))) σ c54 c64 (RunStep.cond_lt_true B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c46 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_12)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_13)) (?nAX_g4452_0_0_14)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_15)) hcase_2) (RunStep.ite_true B c29 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c54 c63 (RunStep.cond_eq_true B σ (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Env.vars σ "query.col") c46 (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_16)) (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_17)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_18)) (?nAX_g4452_0_0_19)) hcase_3) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) c69 σ c51 c54 c58 c62 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_20))) (RunStep.seq B c67 c68 c51 c53 c54 c60 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c51 h1)) (RunStep.assign B c53 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c53 h1)))))))) (?nAX_g4452_0_0_21)) ?_)) fun (hcase_3:c50) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((76:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c20 c76) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c71 c76 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_22)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_23)) hcase) (RunStep.ite_true B c27 c31 c40 σ c71 c75 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_24)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_25)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_26)) (?nAX_g4452_0_0_27)) hcase_1) (RunStep.ite_true B c28 c30 (RamPadSelector.constantFraction ((0:Nat))) σ c71 c74 (RunStep.cond_lt_true B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c46 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_28)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_29)) (?nAX_g4452_0_0_30)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_31)) hcase_2) (RunStep.ite_false B c29 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c71 c73 (RunStep.cond_eq_false B σ (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Env.vars σ "query.col") c46 (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_32)) (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_33)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_34)) (?nAX_g4452_0_0_35)) hcase_3) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c77 c68) σ c51 c71 c58 c72 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_36))) (RunStep.seq B c77 c68 c51 c70 c71 c58 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c51 (?nAX_g4452_0_0_37))) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1)))))))) (?nAX_g4452_0_0_38)) ?_)) fun (hcase_2:c48) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((76:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c20 c79) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c71 c79 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_39)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_40)) hcase) (RunStep.ite_true B c27 c31 c40 σ c71 c78 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_41)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_42)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_43)) (?nAX_g4452_0_0_44)) hcase_1) (RunStep.ite_false B c28 c30 (RamPadSelector.constantFraction ((0:Nat))) σ c71 c73 (RunStep.cond_lt_false B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c46 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_45)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_46)) (?nAX_g4452_0_0_47)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_48)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c77 c68) σ c51 c71 c58 c72 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_49))) (RunStep.seq B c77 c68 c51 c70 c71 c58 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c51 (?nAX_g4452_0_0_50))) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1))))))) (?nAX_g4452_0_0_51)) ?_)) fun (hcase_1:c44) => @Or.casesOn c81 c82 (fun (x:Or c81 c82) => @Exists Env c4) (Classical.em c81) (fun (hcase_2:c81) => @Or.casesOn c84 c85 (fun (x:Or c84 c85) => @Exists Env c4) (Classical.em c84) (fun (hcase_3:c84) => @Or.casesOn c86 c87 (fun (x:Or c86 c87) => @Exists Env c4) (Classical.em c86) (fun (hcase_4:c86) => @Exists.intro Env c4 c90 (@And.intro (Run B selectEntry σ c90 ((76:Nat))) (c3 c90) (RunStep.mono B selectEntry σ c90 (c20 c98) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c90 c98 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_52)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_53)) hcase) (RunStep.ite_false B c27 c31 c40 σ c90 c97 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_54)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_55)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_56)) (?nAX_g4452_0_0_57)) hcase_1) (RunStep.ite_true B c33 c38 c39 σ c90 c96 (RunStep.cond_lt_true B σ (Expr.var "query.row") c32 (Env.vars σ "query.row") c80 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_58)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c42 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_59)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_60)) (?nAX_g4452_0_0_61)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_62)) (?nAX_g4452_0_0_63)) hcase_2) (RunStep.ite_true B c35 c37 (RamPadSelector.constantFraction ((0:Nat))) σ c90 c95 (RunStep.cond_lt_true B σ c34 (Expr.var "point.k") c83 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c46 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_64)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_65)) (?nAX_g4452_0_0_66)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_67)) (?nAX_g4452_0_0_68)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_69)) hcase_3) (RunStep.ite_true B c36 negativeOne (RamPadSelector.constantFraction ((0:Nat))) σ c90 c94 (RunStep.cond_eq_true B σ (Expr.var "query.col") c34 (Env.vars σ "query.col") c83 (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_70)) (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c46 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_71)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_72)) (?nAX_g4452_0_0_73)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_74)) (?nAX_g4452_0_0_75)) hcase_4) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) c69 σ c88 c90 c60 c62 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B c67 c68 c88 c89 c90 c60 c60 (RunStep.assign B c88 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c88 h1)) (RunStep.assign B c89 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c89 h1))))))))) (?nAX_g4452_0_0_76)) ?_)) fun (hcase_4:c87) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((76:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c20 c102) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c71 c102 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_77)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_78)) hcase) (RunStep.ite_false B c27 c31 c40 σ c71 c101 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_79)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_80)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_81)) (?nAX_g4452_0_0_82)) hcase_1) (RunStep.ite_true B c33 c38 c39 σ c71 c100 (RunStep.cond_lt_true B σ (Expr.var "query.row") c32 (Env.vars σ "query.row") c80 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_83)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c42 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_84)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_85)) (?nAX_g4452_0_0_86)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_87)) (?nAX_g4452_0_0_88)) hcase_2) (RunStep.ite_true B c35 c37 (RamPadSelector.constantFraction ((0:Nat))) σ c71 c99 (RunStep.cond_lt_true B σ c34 (Expr.var "point.k") c83 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c46 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_89)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_90)) (?nAX_g4452_0_0_91)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_92)) (?nAX_g4452_0_0_93)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_94)) hcase_3) (RunStep.ite_false B c36 negativeOne (RamPadSelector.constantFraction ((0:Nat))) σ c71 c73 (RunStep.cond_eq_false B σ (Expr.var "query.col") c34 (Env.vars σ "query.col") c83 (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_95)) (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c46 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_96)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_97)) (?nAX_g4452_0_0_98)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_99)) (?nAX_g4452_0_0_100)) hcase_4) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c77 c68) σ c51 c71 c58 c72 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_101))) (RunStep.seq B c77 c68 c51 c70 c71 c58 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c51 (?nAX_g4452_0_0_102))) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1))))))))) (?nAX_g4452_0_0_103)) ?_)) fun (hcase_3:c85) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((76:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c20 c105) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c71 c105 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_104)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_105)) hcase) (RunStep.ite_false B c27 c31 c40 σ c71 c104 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_106)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_107)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_108)) (?nAX_g4452_0_0_109)) hcase_1) (RunStep.ite_true B c33 c38 c39 σ c71 c103 (RunStep.cond_lt_true B σ (Expr.var "query.row") c32 (Env.vars σ "query.row") c80 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_110)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c42 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_111)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_112)) (?nAX_g4452_0_0_113)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_114)) (?nAX_g4452_0_0_115)) hcase_2) (RunStep.ite_false B c35 c37 (RamPadSelector.constantFraction ((0:Nat))) σ c71 c73 (RunStep.cond_lt_false B σ c34 (Expr.var "point.k") c83 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c46 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_116)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_117)) (?nAX_g4452_0_0_118)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_119)) (?nAX_g4452_0_0_120)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_121)) hcase_3) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c77 c68) σ c51 c71 c58 c72 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_122))) (RunStep.seq B c77 c68 c51 c70 c71 c58 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c51 (?nAX_g4452_0_0_123))) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1)))))))) (?nAX_g4452_0_0_124)) ?_)) fun (hcase_2:c82) => @Or.casesOn c106 c107 (fun (x:Or c106 c107) => @Exists Env c4) (Classical.em c106) (fun (hcase_3:c106) => @Exists.intro Env c4 c54 (@And.intro (Run B selectEntry σ c54 ((76:Nat))) (c3 c54) (RunStep.mono B selectEntry σ c54 (c20 c111) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c54 c111 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_125)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_126)) hcase) (RunStep.ite_false B c27 c31 c40 σ c54 c110 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_127)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_128)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_129)) (?nAX_g4452_0_0_130)) hcase_1) (RunStep.ite_false B c33 c38 c39 σ c54 c109 (RunStep.cond_lt_false B σ (Expr.var "query.row") c32 (Env.vars σ "query.row") c80 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_131)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c42 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_132)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_133)) (?nAX_g4452_0_0_134)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_135)) (?nAX_g4452_0_0_136)) hcase_2) (RunStep.ite_true B (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c54 c63 (RunStep.cond_eq_true B σ (Expr.var "query.col") (Expr.var "point.k") (Env.vars σ "query.col") (Env.vars σ "point.k") (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_137)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_138)) hcase_3) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) c69 σ c51 c54 c58 c62 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_139))) (RunStep.seq B c67 c68 c51 c53 c54 c60 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c51 h1)) (RunStep.assign B c53 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c53 h1)))))))) (?nAX_g4452_0_0_140)) ?_)) fun (hcase_3:c107) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((76:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c20 c114) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c26 c41 σ c71 c114 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_141)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_142)) hcase) (RunStep.ite_false B c27 c31 c40 σ c71 c113 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c42 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_143)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_144)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_145)) (?nAX_g4452_0_0_146)) hcase_1) (RunStep.ite_false B c33 c38 c39 σ c71 c112 (RunStep.cond_lt_false B σ (Expr.var "query.row") c32 (Env.vars σ "query.row") c80 (RunStep.eval_var B σ "query.row" (?nAX_g4452_0_0_147)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c42 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_0_0_148)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_149)) (?nAX_g4452_0_0_150)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_0_0_151)) (?nAX_g4452_0_0_152)) hcase_2) (RunStep.ite_false B (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c71 c73 (RunStep.cond_eq_false B σ (Expr.var "query.col") (Expr.var "point.k") (Env.vars σ "query.col") (Env.vars σ "point.k") (RunStep.eval_var B σ "query.col" (?nAX_g4452_0_0_153)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_0_0_154)) hcase_3) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c77 c68) σ c51 c71 c58 c72 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4452_0_0_155))) (RunStep.seq B c77 c68 c51 c70 c71 c58 c60 (RunStep.assign B c51 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c51 (?nAX_g4452_0_0_156))) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1)))))))) (?nAX_g4452_0_0_157)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4452_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_91 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_92 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_93 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_94 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_95 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_96 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_97 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_98 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_99 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_100 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_101 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_102 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_103 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_104 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_105 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_106 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_107 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_108 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_109 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_110 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_111 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_112 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_113 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_114 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_115 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_116 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_117 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_118 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_119 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_120 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_121 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_122 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_123 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_124 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_125 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_126 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_127 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_128 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_129 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_130 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_131 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_132 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_133 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_134 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_135 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_136 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_137 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_138 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_139 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_140 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_141 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_142 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_143 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_144 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_145 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_146 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_147 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_148 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_149 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_150 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_151 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_152 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_153 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_154 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_155 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_156 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_0_0_157 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals clear hload hresult
    all_goals simp_all [fields,FieldsAgree,entry,index,ii,Represents]
    all_goals omega
  · (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "point.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P k i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((76:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=Nat.mul (Env.vars σ "query.row") (Env.vars σ "point.n"); let c8:Nat:=c6 c7 (Env.vars σ "query.col"); let c9:Env:=Env.setVar σ "vec.i" c8; let c10:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "point.A"; let c11:String:=c10 ".s"; let c12:Nat:=Env.vars c9 "vec.i"; let c13:Nat:= @List.getD Nat (Env.arrs c9 c11) c12 ((0:Nat)); let c14:Env:=Env.setVar c9 "left.s" c13; let c15:String:=c10 ".n"; let c16:Nat:=Env.vars c14 "vec.i"; let c17:Nat:= @List.getD Nat (Env.arrs c14 c15) c16 ((0:Nat)); let c18:Env:=Env.setVar c14 "left.n" c17; let c19:String:=c10 ".d"; let c20:Nat:=Env.vars c18 "vec.i"; let c21:Nat:= @List.getD Nat (Env.arrs c18 c19) c20 ((0:Nat)); let c22:Env:=Env.setVar c18 "left.d" c21; let c23:Nat:=Env.vars c22 "left.s"; let c24:Env:=Env.setVar c22 "rat.s" c23; let c25:Nat:=Env.vars c24 "left.n"; let c26:Env:=Env.setVar c24 "rat.n" c25; let c27:Nat:=Env.vars c26 "left.d"; let c28:Env:=Env.setVar c26 "rat.d" c27; let c29:Nat→ Nat:=c6 ((1:Nat)); let c30:Nat→ Nat:=c6 (c29 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "point.m")))); let c31:Expr:=Expr.add (Expr.mul (Expr.var "query.row") (Expr.var "point.n")) (Expr.var "query.col"); let c32:Nat:=c29 (Expr.size c31); let c33:Expr:=Expr.get c11 (Expr.var "vec.i"); let c34:Nat:=c29 (Expr.size c33); let c35:Expr:=Expr.get c15 (Expr.var "vec.i"); let c36:Nat:=c29 (Expr.size c35); let c37:Expr:=Expr.get c19 (Expr.var "vec.i"); let c38:Nat:=c29 (Expr.size c37); let c39:Nat:=c6 c36 c38; let c40:Nat:=c6 c34 c39; let c41:Nat:=c29 (Expr.size (Expr.var "left.s")); let c42:Nat:=c29 (Expr.size (Expr.var "left.n")); let c43:Nat:=c29 (Expr.size (Expr.var "left.d")); let c44:Nat:=c6 c42 c43; let c45:Nat:=c6 c41 c44; let c46:Nat:=c6 c40 c45; let c47:Nat:=c6 c32 c46; let c48:Com:=Com.assign "vec.i" c31; let c49:Com:=Com.seq c48 (Com.seq (loadLeft "point.A") RamCopy.leftToResult); let c50:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")); let c51:Cond:=Cond.lt (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k"); let c52:Cond:=Cond.eq (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")); let c53:Com:=Com.ite c52 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c54:Com:=Com.ite c51 c53 (RamPadSelector.constantFraction ((0:Nat))); let c55:Expr:=Expr.add (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n"); let c56:Cond:=Cond.lt (Expr.var "query.row") c55; let c57:Expr:=Expr.sub (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n"); let c58:Cond:=Cond.lt c57 (Expr.var "point.k"); let c59:Cond:=Cond.eq (Expr.var "query.col") c57; let c60:Com:=Com.ite c59 negativeOne (RamPadSelector.constantFraction ((0:Nat))); let c61:Com:=Com.ite c58 c60 (RamPadSelector.constantFraction ((0:Nat))); let c62:Com:=Com.ite (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c63:Com:=Com.ite c56 c61 c62; let c64:Com:=Com.ite c50 c54 c63; let c65:Com:=Com.assign "left.n" c35; let c66:Com:=Com.assign "left.d" c37; let c67:Nat:=c6 (Env.vars σ "point.m") (Env.vars σ "point.n"); let c68:Prop:=Nat.lt (Env.vars σ "query.row") c67; let c69:Prop:=Not c68; let c70:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c71:Nat:=c70 (Env.vars σ "query.row") (Env.vars σ "point.m"); let c72:Prop:=Nat.lt c71 (Env.vars σ "point.k"); let c73:Prop:=Not c72; let c74:Prop:= @Eq Nat (Env.vars σ "query.col") c71; let c75:Prop:=Not c74; let c76:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((1:Nat))) σ; let c77:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat))); let c78:Env→ Prop:=fun (σ':Env) => And (c76 σ' ((6:Nat))) (c77 σ'); let c79:Nat→ Nat:=c6 (c29 (Cond.size c50)); let c80:Nat→ Nat:=c6 (c29 (Cond.size c51)); let c81:Nat:=c6 (c29 (Cond.size c52)) ((6:Nat)); let c82:Nat:=c80 c81; let c83:Nat:=c79 c82; let c84:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c85:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c86:Env→ Prop:=fun (σ':Env) => And (c84 σ' ((6:Nat))) (c85 σ'); let c87:Nat:=c80 ((6:Nat)); let c88:Nat:=c79 c87; let c89:Nat:=c6 c67 (Env.vars σ "point.n"); let c90:Prop:=Nat.lt (Env.vars σ "query.row") c89; let c91:Prop:=Not c90; let c92:Nat:=c70 c71 (Env.vars σ "point.n"); let c93:Prop:=Nat.lt c92 (Env.vars σ "point.k"); let c94:Prop:=Not c93; let c95:Prop:= @Eq Nat (Env.vars σ "query.col") c92; let c96:Prop:=Not c95; let c97:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c98:Env→ Prop:=fun (σ':Env) => And (Run B negativeOne σ σ' ((6:Nat))) (c97 σ'); let c99:Nat→ Nat:=c6 (c29 (Cond.size c56)); let c100:Nat→ Nat:=c6 (c29 (Cond.size c58)); let c101:Nat:=c6 (c29 (Cond.size c59)) ((6:Nat)); let c102:Nat:=c100 c101; let c103:Nat:=c99 c102; let c104:Nat:=c79 c103; let c105:Nat:=c100 ((6:Nat)); let c106:Nat:=c99 c105; let c107:Nat:=c79 c106; let c108:Prop:= @Eq Nat (Env.vars σ "query.col") (Env.vars σ "point.k"); let c109:Prop:=Not c108; let c110:Nat:=c6 (c29 (Cond.size (Cond.eq (Expr.var "query.col") (Expr.var "point.k")))) ((6:Nat)); let c111:Nat:=c99 c110; let c112:Nat:=c79 c111; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c28 (@And.intro (Run B selectEntry σ c28 ((76:Nat))) (c3 c28) (RunStep.mono B selectEntry σ c28 (c30 c47) ((76:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ c28 c47 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_0)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_1)) hcase) (RunStep.seq B c48 (Com.seq (loadLeft "point.A") RamCopy.leftToResult) σ c9 c28 c32 c46 (RunStep.assign B σ "vec.i" c31 c8 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.row") (Expr.var "point.n")) (Expr.var "query.col") c7 (Env.vars σ "query.col") (RunStep.eval_mul B σ (Expr.var "query.row") (Expr.var "point.n") (Env.vars σ "query.row") (Env.vars σ "point.n") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_2)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_3)) (?nAX_g4452_1_0_4)) (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_5)) (?nAX_g4452_1_0_6))) (RunStep.seq B (loadLeft "point.A") RamCopy.leftToResult c9 c22 c28 c40 c45 (RunStep.seq B (Com.assign "left.s" c33) (Com.seq c65 c66) c9 c14 c22 c34 c39 (RunStep.assign B c9 "left.s" c33 c13 (RunStep.eval_get B c9 c11 (Expr.var "vec.i") c12 (RunStep.eval_var B c9 "vec.i" (?nAX_g4452_1_0_7)) (?nAX_g4452_1_0_8) (?nAX_g4452_1_0_9))) (RunStep.seq B c65 c66 c14 c18 c22 c36 c38 (RunStep.assign B c14 "left.n" c35 c17 (RunStep.eval_get B c14 c15 (Expr.var "vec.i") c16 (RunStep.eval_var B c14 "vec.i" (?nAX_g4452_1_0_10)) (?nAX_g4452_1_0_11) (?nAX_g4452_1_0_12))) (RunStep.assign B c18 "left.d" c37 c21 (RunStep.eval_get B c18 c19 (Expr.var "vec.i") c20 (RunStep.eval_var B c18 "vec.i" (?nAX_g4452_1_0_13)) (?nAX_g4452_1_0_14) (?nAX_g4452_1_0_15))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c22 c24 c28 c41 c44 (RunStep.assign B c22 "rat.s" (Expr.var "left.s") c23 (RunStep.eval_var B c22 "left.s" (?nAX_g4452_1_0_16))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c24 c26 c28 c42 c43 (RunStep.assign B c24 "rat.n" (Expr.var "left.n") c25 (RunStep.eval_var B c24 "left.n" (?nAX_g4452_1_0_17))) (RunStep.assign B c26 "rat.d" (Expr.var "left.d") c27 (RunStep.eval_var B c26 "left.d" (?nAX_g4452_1_0_18)))))))) (?nAX_g4452_1_0_19)) ?_)) fun (hcase:c1) => @Or.casesOn c68 c69 (fun (x:Or c68 c69) => c5) (Classical.em c68) (fun (hcase_1:c68) => @Or.casesOn c72 c73 (fun (x:Or c72 c73) => c5) (Classical.em c72) (fun (hcase_2:c72) => @Or.casesOn c74 c75 (fun (x:Or c74 c75) => c5) (Classical.em c74) (fun (hcase_3:c74) => @Exists.casesOn Env c78 (fun (x:@Exists Env c78) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((1:Nat))) (fun (x τ:Env) => c77 τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (c76 w ((6:Nat))) (c77 w)) => let c0_1:Prop:=c76 w ((6:Nat)); @And.casesOn c0_1 (c77 w) (fun (x:And c0_1 (c77 w)) => c5) h fun (left:c0_1) (right:c77 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c83) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c83 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_20)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_21)) hcase) (RunStep.ite_true B c50 c54 c63 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_22)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_23)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_24)) (?nAX_g4452_1_0_25)) hcase_1) (RunStep.ite_true B c51 c53 (RamPadSelector.constantFraction ((0:Nat))) σ w c81 (RunStep.cond_lt_true B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c71 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_26)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_27)) (?nAX_g4452_1_0_28)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_29)) hcase_2) (RunStep.ite_true B c52 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Env.vars σ "query.col") c71 (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_30)) (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_31)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_32)) (?nAX_g4452_1_0_33)) hcase_3) left)))) (?nAX_g4452_1_0_34)) ?_)) fun (hcase_3:c75) => @Exists.casesOn Env c86 (fun (x:@Exists Env c86) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c85 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c84 w ((6:Nat))) (c85 w)) => let c0_1:Prop:=c84 w ((6:Nat)); @And.casesOn c0_1 (c85 w) (fun (x:And c0_1 (c85 w)) => c5) h fun (left:c0_1) (right:c85 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c83) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c83 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_35)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_36)) hcase) (RunStep.ite_true B c50 c54 c63 σ w c82 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_37)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_38)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_39)) (?nAX_g4452_1_0_40)) hcase_1) (RunStep.ite_true B c51 c53 (RamPadSelector.constantFraction ((0:Nat))) σ w c81 (RunStep.cond_lt_true B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c71 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_41)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_42)) (?nAX_g4452_1_0_43)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_44)) hcase_2) (RunStep.ite_false B c52 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "query.col") (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Env.vars σ "query.col") c71 (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_45)) (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_46)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_47)) (?nAX_g4452_1_0_48)) hcase_3) left)))) (?nAX_g4452_1_0_49)) ?_)) fun (hcase_2:c73) => @Exists.casesOn Env c86 (fun (x:@Exists Env c86) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c85 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c84 w ((6:Nat))) (c85 w)) => let c0_1:Prop:=c84 w ((6:Nat)); @And.casesOn c0_1 (c85 w) (fun (x:And c0_1 (c85 w)) => c5) h fun (left:c0_1) (right:c85 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c88) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c88 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_50)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_51)) hcase) (RunStep.ite_true B c50 c54 c63 σ w c87 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_52)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_53)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_54)) (?nAX_g4452_1_0_55)) hcase_1) (RunStep.ite_false B c51 c53 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.k") c71 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_56)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_57)) (?nAX_g4452_1_0_58)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_59)) hcase_2) left))) (?nAX_g4452_1_0_60)) ?_)) fun (hcase_1:c69) => @Or.casesOn c90 c91 (fun (x:Or c90 c91) => c5) (Classical.em c90) (fun (hcase_2:c90) => @Or.casesOn c93 c94 (fun (x:Or c93 c94) => c5) (Classical.em c93) (fun (hcase_3:c93) => @Or.casesOn c95 c96 (fun (x:Or c95 c96) => c5) (Classical.em c95) (fun (hcase_4:c95) => @Exists.casesOn Env c98 (fun (x:@Exists Env c98) => c5) (RunStep.use B (fun (x:Env) => True) negativeOne (fun (x τ:Env) => c97 τ) ((6:Nat)) hneg σ ?_) fun (w:Env) (h:And (Run B negativeOne σ w ((6:Nat))) (c97 w)) => let c0_1:Prop:=Run B negativeOne σ w ((6:Nat)); @And.casesOn c0_1 (c97 w) (fun (x:And c0_1 (c97 w)) => c5) h fun (left:c0_1) (right:c97 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c104) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c104 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_61)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_62)) hcase) (RunStep.ite_false B c50 c54 c63 σ w c103 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_63)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_64)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_65)) (?nAX_g4452_1_0_66)) hcase_1) (RunStep.ite_true B c56 c61 c62 σ w c102 (RunStep.cond_lt_true B σ (Expr.var "query.row") c55 (Env.vars σ "query.row") c89 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_67)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c67 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_68)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_69)) (?nAX_g4452_1_0_70)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_71)) (?nAX_g4452_1_0_72)) hcase_2) (RunStep.ite_true B c58 c60 (RamPadSelector.constantFraction ((0:Nat))) σ w c101 (RunStep.cond_lt_true B σ c57 (Expr.var "point.k") c92 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c71 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_73)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_74)) (?nAX_g4452_1_0_75)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_76)) (?nAX_g4452_1_0_77)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_78)) hcase_3) (RunStep.ite_true B c59 negativeOne (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "query.col") c57 (Env.vars σ "query.col") c92 (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_79)) (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c71 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_80)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_81)) (?nAX_g4452_1_0_82)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_83)) (?nAX_g4452_1_0_84)) hcase_4) left))))) (?nAX_g4452_1_0_85)) ?_)) fun (hcase_4:c96) => @Exists.casesOn Env c86 (fun (x:@Exists Env c86) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c85 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c84 w ((6:Nat))) (c85 w)) => let c0_1:Prop:=c84 w ((6:Nat)); @And.casesOn c0_1 (c85 w) (fun (x:And c0_1 (c85 w)) => c5) h fun (left:c0_1) (right:c85 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c104) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c104 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_86)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_87)) hcase) (RunStep.ite_false B c50 c54 c63 σ w c103 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_88)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_89)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_90)) (?nAX_g4452_1_0_91)) hcase_1) (RunStep.ite_true B c56 c61 c62 σ w c102 (RunStep.cond_lt_true B σ (Expr.var "query.row") c55 (Env.vars σ "query.row") c89 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_92)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c67 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_93)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_94)) (?nAX_g4452_1_0_95)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_96)) (?nAX_g4452_1_0_97)) hcase_2) (RunStep.ite_true B c58 c60 (RamPadSelector.constantFraction ((0:Nat))) σ w c101 (RunStep.cond_lt_true B σ c57 (Expr.var "point.k") c92 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c71 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_98)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_99)) (?nAX_g4452_1_0_100)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_101)) (?nAX_g4452_1_0_102)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_103)) hcase_3) (RunStep.ite_false B c59 negativeOne (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "query.col") c57 (Env.vars σ "query.col") c92 (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_104)) (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c71 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_105)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_106)) (?nAX_g4452_1_0_107)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_108)) (?nAX_g4452_1_0_109)) hcase_4) left))))) (?nAX_g4452_1_0_110)) ?_)) fun (hcase_3:c94) => @Exists.casesOn Env c86 (fun (x:@Exists Env c86) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c85 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c84 w ((6:Nat))) (c85 w)) => let c0_1:Prop:=c84 w ((6:Nat)); @And.casesOn c0_1 (c85 w) (fun (x:And c0_1 (c85 w)) => c5) h fun (left:c0_1) (right:c85 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c107) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c107 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_111)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_112)) hcase) (RunStep.ite_false B c50 c54 c63 σ w c106 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_113)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_114)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_115)) (?nAX_g4452_1_0_116)) hcase_1) (RunStep.ite_true B c56 c61 c62 σ w c105 (RunStep.cond_lt_true B σ (Expr.var "query.row") c55 (Env.vars σ "query.row") c89 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_117)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c67 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_118)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_119)) (?nAX_g4452_1_0_120)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_121)) (?nAX_g4452_1_0_122)) hcase_2) (RunStep.ite_false B c58 c60 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ c57 (Expr.var "point.k") c92 (Env.vars σ "point.k") (RunStep.eval_sub B σ (Expr.sub (Expr.var "query.row") (Expr.var "point.m")) (Expr.var "point.n") c71 (Env.vars σ "point.n") (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_123)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_124)) (?nAX_g4452_1_0_125)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_126)) (?nAX_g4452_1_0_127)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_128)) hcase_3) left)))) (?nAX_g4452_1_0_129)) ?_)) fun (hcase_2:c91) => @Or.casesOn c108 c109 (fun (x:Or c108 c109) => c5) (Classical.em c108) (fun (hcase_3:c108) => @Exists.casesOn Env c78 (fun (x:@Exists Env c78) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((1:Nat))) (fun (x τ:Env) => c77 τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (c76 w ((6:Nat))) (c77 w)) => let c0_1:Prop:=c76 w ((6:Nat)); @And.casesOn c0_1 (c77 w) (fun (x:And c0_1 (c77 w)) => c5) h fun (left:c0_1) (right:c77 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c112) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c112 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_130)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_131)) hcase) (RunStep.ite_false B c50 c54 c63 σ w c111 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_132)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_133)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_134)) (?nAX_g4452_1_0_135)) hcase_1) (RunStep.ite_false B c56 c61 c62 σ w c110 (RunStep.cond_lt_false B σ (Expr.var "query.row") c55 (Env.vars σ "query.row") c89 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_136)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c67 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_137)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_138)) (?nAX_g4452_1_0_139)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_140)) (?nAX_g4452_1_0_141)) hcase_2) (RunStep.ite_true B (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "query.col") (Expr.var "point.k") (Env.vars σ "query.col") (Env.vars σ "point.k") (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_142)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_143)) hcase_3) left)))) (?nAX_g4452_1_0_144)) ?_)) fun (hcase_3:c109) => @Exists.casesOn Env c86 (fun (x:@Exists Env c86) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c85 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c84 w ((6:Nat))) (c85 w)) => let c0_1:Prop:=c84 w ((6:Nat)); @And.casesOn c0_1 (c85 w) (fun (x:And c0_1 (c85 w)) => c5) h fun (left:c0_1) (right:c85 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((76:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c30 c112) ((76:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "point.m")) c49 c64 σ w c112 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "point.m") (Env.vars σ "query.row") (Env.vars σ "point.m") (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_145)) (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_146)) hcase) (RunStep.ite_false B c50 c54 c63 σ w c111 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Env.vars σ "query.row") c67 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_147)) (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_148)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_149)) (?nAX_g4452_1_0_150)) hcase_1) (RunStep.ite_false B c56 c61 c62 σ w c110 (RunStep.cond_lt_false B σ (Expr.var "query.row") c55 (Env.vars σ "query.row") c89 (RunStep.eval_var B σ "query.row" (?nAX_g4452_1_0_151)) (RunStep.eval_add B σ (Expr.add (Expr.var "point.m") (Expr.var "point.n")) (Expr.var "point.n") c67 (Env.vars σ "point.n") (RunStep.eval_add B σ (Expr.var "point.m") (Expr.var "point.n") (Env.vars σ "point.m") (Env.vars σ "point.n") (RunStep.eval_var B σ "point.m" (?nAX_g4452_1_0_152)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_153)) (?nAX_g4452_1_0_154)) (RunStep.eval_var B σ "point.n" (?nAX_g4452_1_0_155)) (?nAX_g4452_1_0_156)) hcase_2) (RunStep.ite_false B (Cond.eq (Expr.var "query.col") (Expr.var "point.k")) (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "query.col") (Expr.var "point.k") (Env.vars σ "query.col") (Env.vars σ "point.k") (RunStep.eval_var B σ "query.col" (?nAX_g4452_1_0_157)) (RunStep.eval_var B σ "point.k" (?nAX_g4452_1_0_158)) hcase_3) left)))) (?nAX_g4452_1_0_159)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4452_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_78 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_79 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_80 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_81 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_82 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_83 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_84 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_85 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_86 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_87 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_88 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_89 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_90 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_91 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_92 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_93 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_94 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_95 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_96 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_97 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_98 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_99 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_100 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_101 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_102 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_103 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_104 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_105 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_106 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_107 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_108 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_109 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_110 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_111 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_112 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_113 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_114 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_115 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_116 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_117 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_118 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_119 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_120 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_121 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_122 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_123 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_124 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_125 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_126 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_127 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_128 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_129 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_130 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_131 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_132 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_133 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_134 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_135 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_136 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_137 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_138 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_139 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_140 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_141 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_142 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_143 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_144 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_145 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_146 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_147 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_148 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_149 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_150 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_151 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_152 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_153 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_154 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_155 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_156 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_157 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_158 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4452_1_0_159 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hzero hone hneg
    all_goals simp_all [entry,Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamRecoverySelector

end

theorem solution:∀ (B M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n),
  Nat.lt k n→
    ∀
      (i:
        Fin
          (Nat.add
            (Nat.add m
              (Nat.add n n))
            ((1:Nat))))
      (j:Fin n),
      Nat.le ((1:Nat)) M→
        Nat.lt M B→
          Nat.lt
              (Nat.add
                (Nat.add
                  (Nat.add
                    (Nat.mul
                      (Nat.add
                        (Nat.add m
                          (Nat.add n n))
                        ((1:Nat)))
                      n)
                    m)
                  (Nat.add n n))
                ((4:Nat)))
              B→
            (∀ (i:Fin m) (j:Fin n),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And
                    (Lax109476Proofs.RamRationalArrays.Represents "point.A"
                      (@Lax109476Proofs.RamMatrixStorage.flatten m n (@Lax109476.LinearProgram.Program.A Rat m n P)) σ)
                    (And (@Eq Nat (σ.vars "point.m") m)
                      (And (@Eq Nat (σ.vars "point.n") n)
                        (And (@Eq Nat (σ.vars "point.k") k)
                          (And
                            (@Eq Nat (σ.vars "query.row")
                              (@Fin.val
                                (Nat.add
                                  (Nat.add m
                                    (Nat.add n n))
                                  ((1:Nat)))
                                i))
                            (@Eq Nat (σ.vars "query.col") (@Fin.val n j)))))))
                Lax109476Proofs.RamRecoverySelector.selectEntry
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamRational.FractionOutput (@Lax109476Proofs.RecoveryQueryEntries.entry m n P k i j)
                    τ)
                ((76:Nat)):= @Lax109476Proofs.RamRecoverySelector.selectEntry_spec
