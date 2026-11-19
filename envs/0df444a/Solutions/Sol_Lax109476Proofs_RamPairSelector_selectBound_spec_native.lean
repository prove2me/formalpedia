-- Prove2me | solution 1 for Lax109476Proofs.RamPairSelector.selectBound_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:54:28.368392+00:00
-- url     : https://prove2.me/submissions/d134e568-771d-4e9e-b887-ec80a0fc7ae0

import Mathlib.Tactic
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

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

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

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRounding RationalArithmeticBounds

theorem fractionValue_flip (s n d:ℕ) (hs:s≤ 1):
    fractionValue (1 - s) n d=-fractionValue s n d:=by
  interval_cases s <;> simp [fractionValue,neg_div]

end Lax109476Proofs.RamFractionInterface

end

section

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds

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

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

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

end Lax109476Proofs.RamCertificateSource

end

section

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
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
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negateResult σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negateResult σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negateResult σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g4454_0_0_0))) (?nAX_g4454_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4454_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4454_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax109476Proofs.RamResultNegation

end

section

namespace Lax109476Proofs.RamCertificateLoad

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds RamCertificateSource IntegerEncoding

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
      (refine let c0:Env→ Nat→ Prop:=Run B (RamArrayResult.load a) (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")); let c1:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) (@List.ofFn Rat r v) (@Fin.val r i) (?nAX_g5027_0_0_0)); let c2:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((15:Nat))) (c1 σ'); let c3:Env→ Prop:=(fun (x τ:Env) => FractionOutput (v i) τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (vector a) σ σ' ((17:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 ((1:Nat)) (Expr.size (Expr.var "query.a.row")); @Exists.casesOn Env c2 (fun (x:@Exists Env c2) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents a (@List.ofFn Rat r v) σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") (@Fin.val r i))) (RamArrayResult.load a) (fun (x τ:Env) => c1 τ) ((15:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) ?_) fun (w:Env) (h:And (c0 w ((15:Nat))) (c1 w)) => let c0_1:Prop:=c0 w ((15:Nat)); @And.casesOn c0_1 (c1 w) (fun (x:And c0_1 (c1 w)) => c5) h fun (left:c0_1) (right:c1 w) => @Exists.intro Env c4 w (@And.intro (Run B (vector a) σ w ((17:Nat))) (c3 w) (RunStep.mono B (vector a) σ w (c6 c7 ((15:Nat))) ((17:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load a) σ (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) w c7 ((15:Nat)) (RunStep.assign B σ "vec.i" (Expr.var "query.a.row") (Env.vars σ "query.a.row") (RunStep.eval_var B σ "query.a.row" (?nAX_g5027_0_0_1))) left) (?nAX_g5027_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5027_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5027_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5027_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
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

namespace Lax109476Proofs.RamPairSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds RamCertificateSource IntegerEncoding

set_option maxHeartbeats 0 in
theorem selectBound_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + (n + 2)))
    (hM:1≤ M) (hMB:M < B) (hB:m + n + 4 < B)
    (hb:∀ r, (P.b r).natAbs≤ M) (hc:∀ s, (P.c s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.pairRhs P i:ℚ) τ) 40:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hmn:m + n < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hisub:i.val - m < B:=(Nat.sub_le _ _).trans_lt hiB
  have hz:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => FractionOutput (CertificateFamilyEntries.pairRhs P i:ℚ) τ) 40:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσrow⟩
    by_cases hi:i.val < m
    · let ii:Fin m:= ⟨i.val,hi⟩
      have hload:=RamCertificateLoad.bound_spec B m n P ii h1 (ii.isLt.trans hm) ((hb ii).trans_lt hMB)
      (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.pairRhs m n P i)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((40:Nat))) (c3 σ'); let c5:Env→ Nat→ Prop:=Run B (RamCertificateLoad.vector "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.row")); let c6:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.b Int m n P ii)); let c7:Env→ Prop:=fun (σ':Env) => And (c5 σ' ((17:Nat))) (And (@Data m n P σ') (c6 σ')); let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat→ Nat:=c8 ((1:Nat)); let c10:Nat→ Nat:=c8 (c9 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c11:Nat:=c9 (Expr.size (Expr.var "query.row")); let c12:Nat:=c8 c11 ((17:Nat)); let c13:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b"); let c14:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")); let c15:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c16:Com:=Com.seq c15 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c17:Com:=Com.ite c14 c16 (RamPadSelector.constantFraction ((0:Nat))); let c18:Nat:=c8 (Env.vars σ "source.m") (Env.vars σ "source.n"); let c19:Prop:=Nat.lt (Env.vars σ "query.row") c18; let c20:Prop:=Not c19; let c21:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c22:Nat:=c21 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c23:Env:=Env.setVar σ "query.a.row" c22; let c24:Nat:=Env.vars c23 "query.a.row"; let c25:Env:=Env.setVar c23 "vec.i" c24; let c26:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.c"; let c27:String:=c26 ".s"; let c28:Nat:=Env.vars c25 "vec.i"; let c29:Nat:= @List.getD Nat (Env.arrs c25 c27) c28 ((0:Nat)); let c30:Env:=Env.setVar c25 "left.s" c29; let c31:String:=c26 ".n"; let c32:Nat:=Env.vars c30 "vec.i"; let c33:Nat:= @List.getD Nat (Env.arrs c30 c31) c32 ((0:Nat)); let c34:Env:=Env.setVar c30 "left.n" c33; let c35:String:=c26 ".d"; let c36:Nat:=Env.vars c34 "vec.i"; let c37:Nat:= @List.getD Nat (Env.arrs c34 c35) c36 ((0:Nat)); let c38:Env:=Env.setVar c34 "left.d" c37; let c39:Nat:=Env.vars c38 "left.s"; let c40:Env:=Env.setVar c38 "rat.s" c39; let c41:Nat:=Env.vars c40 "left.n"; let c42:Env:=Env.setVar c40 "rat.n" c41; let c43:Nat:=Env.vars c42 "left.d"; let c44:Env:=Env.setVar c42 "rat.d" c43; let c45:Nat:=Env.vars c44 "rat.s"; let c46:Nat:=c21 ((1:Nat)) c45; let c47:Env:=Env.setVar c44 "rat.s" c46; let c48:Nat→ Nat:=c8 (c9 (Cond.size c14)); let c49:Nat:=c9 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c50:Nat:=c9 (Expr.size (Expr.var "query.a.row")); let c51:Expr:=Expr.get c27 (Expr.var "vec.i"); let c52:Nat:=c9 (Expr.size c51); let c53:Expr:=Expr.get c31 (Expr.var "vec.i"); let c54:Nat:=c9 (Expr.size c53); let c55:Expr:=Expr.get c35 (Expr.var "vec.i"); let c56:Nat:=c9 (Expr.size c55); let c57:Nat:=c8 c54 c56; let c58:Nat:=c8 c52 c57; let c59:Nat:=c9 (Expr.size (Expr.var "left.s")); let c60:Nat:=c9 (Expr.size (Expr.var "left.n")); let c61:Nat:=c9 (Expr.size (Expr.var "left.d")); let c62:Nat:=c8 c60 c61; let c63:Nat:=c8 c59 c62; let c64:Nat:=c8 c58 c63; let c65:Nat:=c8 c50 c64; let c66:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c67:Nat:=c9 (Expr.size c66); let c68:Nat:=c8 c65 c67; let c69:Nat:=c8 c49 c68; let c70:Nat:=c48 c69; let c71:Com:=Com.assign "left.n" c53; let c72:Com:=Com.assign "left.d" c55; let c73:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c74:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c75:Env→ Prop:=fun (σ':Env) => And (c73 σ' ((6:Nat))) (c74 σ'); let c76:Nat:=c48 ((6:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (@Eq Nat (Env.vars σ_1 "query.a.row") (@Fin.val m ii))) (RamCertificateLoad.vector "source.b") (fun (x τ:Env) => And (@Data m n P τ) (c6 τ)) ((17:Nat)) hload (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) ?_) fun (w:Env) (h:And (c5 w ((17:Nat))) (And (@Data m n P w) (c6 w))) => let c0_1:Prop:=c5 w ((17:Nat)); let c1_1:Prop:=And (@Data m n P w) (c6 w); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((40:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c10 c12) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c17 σ w c12 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) w c11 ((17:Nat)) (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_2))) left)) (?nAX_g5048_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c19 c20 (fun (x:Or c19 c20) => @Exists Env c4) (Classical.em c19) (fun (hcase_1:c19) => @Exists.intro Env c4 c47 (@And.intro (Run B selectBound σ c47 ((40:Nat))) (c3 c47) (RunStep.mono B selectBound σ c47 (c10 c70) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c17 σ c47 c70 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_4)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_5)) hcase) (RunStep.ite_true B c14 c16 (RamPadSelector.constantFraction ((0:Nat))) σ c47 c69 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c18 (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_6)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_7)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_0_0_8)) (?nAX_g5048_0_0_9)) hcase_1) (RunStep.seq B c15 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c23 c47 c49 c68 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c22 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_10)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_11)) (?nAX_g5048_0_0_12))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c23 c44 c47 c65 c67 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c23 c25 c44 c50 c64 (RunStep.assign B c23 "vec.i" (Expr.var "query.a.row") c24 (RunStep.eval_var B c23 "query.a.row" (?nAX_g5048_0_0_13))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c25 c38 c44 c58 c63 (RunStep.seq B (Com.assign "left.s" c51) (Com.seq c71 c72) c25 c30 c38 c52 c57 (RunStep.assign B c25 "left.s" c51 c29 (RunStep.eval_get B c25 c27 (Expr.var "vec.i") c28 (RunStep.eval_var B c25 "vec.i" (?nAX_g5048_0_0_14)) (?nAX_g5048_0_0_15) (?nAX_g5048_0_0_16))) (RunStep.seq B c71 c72 c30 c34 c38 c54 c56 (RunStep.assign B c30 "left.n" c53 c33 (RunStep.eval_get B c30 c31 (Expr.var "vec.i") c32 (RunStep.eval_var B c30 "vec.i" (?nAX_g5048_0_0_17)) (?nAX_g5048_0_0_18) (?nAX_g5048_0_0_19))) (RunStep.assign B c34 "left.d" c55 c37 (RunStep.eval_get B c34 c35 (Expr.var "vec.i") c36 (RunStep.eval_var B c34 "vec.i" (?nAX_g5048_0_0_20)) (?nAX_g5048_0_0_21) (?nAX_g5048_0_0_22))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c38 c40 c44 c59 c62 (RunStep.assign B c38 "rat.s" (Expr.var "left.s") c39 (RunStep.eval_var B c38 "left.s" (?nAX_g5048_0_0_23))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c40 c42 c44 c60 c61 (RunStep.assign B c40 "rat.n" (Expr.var "left.n") c41 (RunStep.eval_var B c40 "left.n" (?nAX_g5048_0_0_24))) (RunStep.assign B c42 "rat.d" (Expr.var "left.d") c43 (RunStep.eval_var B c42 "left.d" (?nAX_g5048_0_0_25))))))) (RunStep.assign B c44 "rat.s" c66 c46 (RunStep.eval_sub B c44 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c45 (RunStep.eval_lit B ((1:Nat)) c44 h1) (RunStep.eval_var B c44 "rat.s" (?nAX_g5048_0_0_26)) (?nAX_g5048_0_0_27))))))) (?nAX_g5048_0_0_28)) ?_)) fun (hcase_1:c20) => @Exists.casesOn Env c75 (fun (x:@Exists Env c75) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c74 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c73 w ((6:Nat))) (c74 w)) => let c0_1:Prop:=c73 w ((6:Nat)); @And.casesOn c0_1 (c74 w) (fun (x:And c0_1 (c74 w)) => @Exists Env c4) h fun (left:c0_1) (right:c74 w) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((40:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c10 c76) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c13 c17 σ w c76 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_30)) hcase) (RunStep.ite_false B c14 c16 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c18 (RunStep.eval_var B σ "query.row" (?nAX_g5048_0_0_31)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_0_0_32)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_0_0_33)) (?nAX_g5048_0_0_34)) hcase_1) left)) (?nAX_g5048_0_0_35)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5048_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals clear hload hz
      all_goals simp_all [CertificateFamilyEntries.pairRhs,ii,Data,Represents,arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases hir:i.val < m + n
      · let ii:Fin n:= ⟨i.val - m,by omega⟩
        have hload:=RamCertificateLoad.objective_spec B m n P ii h1 (ii.isLt.trans hn) ((hc ii).trans_lt hMB)
        have hneg:=RamResultNegation.negateResult_spec B (P.c ii:ℚ) h1
        (expose_names;
          (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.pairRhs m n P i)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((40:Nat))) (c3 σ'); let c5:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row"; let c6:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i" c5; let c7:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.b"; let c8:String:=c7 ".s"; let c9:Nat:=Env.vars c6 "vec.i"; let c10:Nat:= @List.getD Nat (Env.arrs c6 c8) c9 ((0:Nat)); let c11:Env:=Env.setVar c6 "left.s" c10; let c12:String:=c7 ".n"; let c13:Nat:=Env.vars c11 "vec.i"; let c14:Nat:= @List.getD Nat (Env.arrs c11 c12) c13 ((0:Nat)); let c15:Env:=Env.setVar c11 "left.n" c14; let c16:String:=c7 ".d"; let c17:Nat:=Env.vars c15 "vec.i"; let c18:Nat:= @List.getD Nat (Env.arrs c15 c16) c17 ((0:Nat)); let c19:Env:=Env.setVar c15 "left.d" c18; let c20:Nat:=Env.vars c19 "left.s"; let c21:Env:=Env.setVar c19 "rat.s" c20; let c22:Nat:=Env.vars c21 "left.n"; let c23:Env:=Env.setVar c21 "rat.n" c22; let c24:Nat:=Env.vars c23 "left.d"; let c25:Env:=Env.setVar c23 "rat.d" c24; let c26:Nat→ Nat→ Nat:=Nat.add; let c27:Nat→ Nat:=c26 ((1:Nat)); let c28:Nat→ Nat:=c26 (c27 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c29:Nat:=c27 (Expr.size (Expr.var "query.row")); let c30:Nat:=c27 (Expr.size (Expr.var "query.a.row")); let c31:Expr:=Expr.get c8 (Expr.var "vec.i"); let c32:Nat:=c27 (Expr.size c31); let c33:Expr:=Expr.get c12 (Expr.var "vec.i"); let c34:Nat:=c27 (Expr.size c33); let c35:Expr:=Expr.get c16 (Expr.var "vec.i"); let c36:Nat:=c27 (Expr.size c35); let c37:Nat:=c26 c34 c36; let c38:Nat:=c26 c32 c37; let c39:Nat:=c27 (Expr.size (Expr.var "left.s")); let c40:Nat:=c27 (Expr.size (Expr.var "left.n")); let c41:Nat:=c27 (Expr.size (Expr.var "left.d")); let c42:Nat:=c26 c40 c41; let c43:Nat:=c26 c39 c42; let c44:Nat:=c26 c38 c43; let c45:Nat:=c26 c30 c44; let c46:Nat:=c26 c29 c45; let c47:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b"); let c48:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")); let c49:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c50:Com:=Com.seq c49 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c51:Com:=Com.ite c48 c50 (RamPadSelector.constantFraction ((0:Nat))); let c52:Com:=Com.assign "left.n" c33; let c53:Com:=Com.assign "left.d" c35; let c54:Nat:=c26 (Env.vars σ "source.m") (Env.vars σ "source.n"); let c55:Prop:=Nat.lt (Env.vars σ "query.row") c54; let c56:Prop:=Not c55; let c57:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "query.row") (Env.vars σ "source.m"); let c58:Env:=Env.setVar σ "query.a.row" c57; let c59:Env→ Nat→ Prop:=Run B (RamCertificateLoad.vector "source.c") c58; let c60:Rat:= @Int.cast Rat Rat.instIntCast (@Program.c Int m n P ii); let c61:Env→ Prop:=FractionOutput c60; let c62:Env→ Prop:=fun (σ':Env) => And (c59 σ' ((17:Nat))) (And (@Data m n P σ') (c61 σ')); let c63:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg c60); let c64:Nat→ Nat:=c26 (c27 (Cond.size c48)); let c65:Nat:=c27 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c66:Nat:=c26 ((17:Nat)) ((4:Nat)); let c67:Nat:=c26 c65 c66; let c68:Nat:=c64 c67; let c69:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c70:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c71:Env→ Prop:=fun (σ':Env) => And (c69 σ' ((6:Nat))) (c70 σ'); let c72:Nat:=c64 ((6:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c25 (@And.intro (Run B selectBound σ c25 ((40:Nat))) (c3 c25) (RunStep.mono B selectBound σ c25 (c28 c46) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c47 c51 σ c25 c46 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c25 c29 c45 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_2))) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c6 c25 c30 c44 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i" (Expr.var "query.a.row") c5 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row" (?nAX_g5048_1_0_3))) (RunStep.seq B (loadLeft "source.b") RamCopy.leftToResult c6 c19 c25 c38 c43 (RunStep.seq B (Com.assign "left.s" c31) (Com.seq c52 c53) c6 c11 c19 c32 c37 (RunStep.assign B c6 "left.s" c31 c10 (RunStep.eval_get B c6 c8 (Expr.var "vec.i") c9 (RunStep.eval_var B c6 "vec.i" (?nAX_g5048_1_0_4)) (?nAX_g5048_1_0_5) (?nAX_g5048_1_0_6))) (RunStep.seq B c52 c53 c11 c15 c19 c34 c36 (RunStep.assign B c11 "left.n" c33 c14 (RunStep.eval_get B c11 c12 (Expr.var "vec.i") c13 (RunStep.eval_var B c11 "vec.i" (?nAX_g5048_1_0_7)) (?nAX_g5048_1_0_8) (?nAX_g5048_1_0_9))) (RunStep.assign B c15 "left.d" c35 c18 (RunStep.eval_get B c15 c16 (Expr.var "vec.i") c17 (RunStep.eval_var B c15 "vec.i" (?nAX_g5048_1_0_10)) (?nAX_g5048_1_0_11) (?nAX_g5048_1_0_12))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c19 c21 c25 c39 c42 (RunStep.assign B c19 "rat.s" (Expr.var "left.s") c20 (RunStep.eval_var B c19 "left.s" (?nAX_g5048_1_0_13))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c21 c23 c25 c40 c41 (RunStep.assign B c21 "rat.n" (Expr.var "left.n") c22 (RunStep.eval_var B c21 "left.n" (?nAX_g5048_1_0_14))) (RunStep.assign B c23 "rat.d" (Expr.var "left.d") c24 (RunStep.eval_var B c23 "left.d" (?nAX_g5048_1_0_15))))))))) (?nAX_g5048_1_0_16)) ?_)) fun (hcase:c1) => @Or.casesOn c55 c56 (fun (x:Or c55 c56) => @Exists Env c4) (Classical.em c55) (fun (hcase_1:c55) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (@Eq Nat (Env.vars σ_1 "query.a.row") (@Fin.val n ii))) (RamCertificateLoad.vector "source.c") (fun (x τ:Env) => And (@Data m n P τ) (c61 τ)) ((17:Nat)) hload c58 ?_) fun (w:Env) (h:And (c59 w ((17:Nat))) (And (@Data m n P w) (c61 w))) => let c0_1:Prop:=c59 w ((17:Nat)); let c1_1:Prop:=And (@Data m n P w) (c61 w); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult w σ' ((4:Nat))) (c63 σ'); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c4) (RunStep.use B c61 RamResultNegation.negateResult (fun (x τ:Env) => c63 τ) ((4:Nat)) hneg w ?_) fun (w_1:Env) (h_1:And (Run B RamResultNegation.negateResult w w_1 ((4:Nat))) (c63 w_1)) => let c0_2:Prop:=Run B RamResultNegation.negateResult w w_1 ((4:Nat)); @And.casesOn c0_2 (c63 w_1) (fun (x:And c0_2 (c63 w_1)) => @Exists Env c4) h_1 fun (left_1:c0_2) (right_1:c63 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectBound σ w_1 ((40:Nat))) (c3 w_1) (RunStep.mono B selectBound σ w_1 (c28 c68) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c47 c51 σ w_1 c68 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_17)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_18)) hcase) (RunStep.ite_true B c48 c50 (RamPadSelector.constantFraction ((0:Nat))) σ w_1 c67 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c54 (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_19)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_20)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_1_0_21)) (?nAX_g5048_1_0_22)) hcase_1) (RunStep.seq B c49 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c58 w_1 c65 c66 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c57 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_23)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_24)) (?nAX_g5048_1_0_25))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c58 w w_1 ((17:Nat)) ((4:Nat)) left left_1)))) (?nAX_g5048_1_0_26)) ?_)) fun (hcase_1:c56) => @Exists.casesOn Env c71 (fun (x:@Exists Env c71) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c70 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c69 w ((6:Nat))) (c70 w)) => let c0_1:Prop:=c69 w ((6:Nat)); @And.casesOn c0_1 (c70 w) (fun (x:And c0_1 (c70 w)) => @Exists Env c4) h fun (left:c0_1) (right:c70 w) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((40:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c28 c72) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c47 c51 σ w c72 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_27)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_28)) hcase) (RunStep.ite_false B c48 c50 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c54 (RunStep.eval_var B σ "query.row" (?nAX_g5048_1_0_29)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_1_0_30)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_1_0_31)) (?nAX_g5048_1_0_32)) hcase_1) left)) (?nAX_g5048_1_0_33)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5048_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
        all_goals clear hload hneg hz
        all_goals simp_all [CertificateFamilyEntries.pairRhs,ii,Data,Represents,arrs_setVar]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · (expose_names;
          (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.pairRhs m n P i)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row"; let c7:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i" c6; let c8:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c9:String→ String:=c8 "source.b"; let c10:String:=c9 ".s"; let c11:Nat:=Env.vars c7 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c7 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c7 "left.s" c12; let c14:String:=c9 ".n"; let c15:Nat:=Env.vars c13 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c13 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c13 "left.n" c16; let c18:String:=c9 ".d"; let c19:Nat:=Env.vars c17 "vec.i"; let c20:Nat:= @List.getD Nat (Env.arrs c17 c18) c19 ((0:Nat)); let c21:Env:=Env.setVar c17 "left.d" c20; let c22:Nat:=Env.vars c21 "left.s"; let c23:Env:=Env.setVar c21 "rat.s" c22; let c24:Nat:=Env.vars c23 "left.n"; let c25:Env:=Env.setVar c23 "rat.n" c24; let c26:Nat:=Env.vars c25 "left.d"; let c27:Env:=Env.setVar c25 "rat.d" c26; let c28:Nat→ Nat→ Nat:=Nat.add; let c29:Nat→ Nat:=c28 ((1:Nat)); let c30:Nat→ Nat:=c28 (c29 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.m")))); let c31:Nat:=c29 (Expr.size (Expr.var "query.row")); let c32:Nat:=c29 (Expr.size (Expr.var "query.a.row")); let c33:Nat→ Nat:=c28 c32; let c34:Expr:=Expr.get c10 (Expr.var "vec.i"); let c35:Nat:=c29 (Expr.size c34); let c36:Expr:=Expr.get c14 (Expr.var "vec.i"); let c37:Nat:=c29 (Expr.size c36); let c38:Expr:=Expr.get c18 (Expr.var "vec.i"); let c39:Nat:=c29 (Expr.size c38); let c40:Nat:=c28 c37 c39; let c41:Nat:=c28 c35 c40; let c42:Nat:=c29 (Expr.size (Expr.var "left.s")); let c43:Nat:=c29 (Expr.size (Expr.var "left.n")); let c44:Nat:=c29 (Expr.size (Expr.var "left.d")); let c45:Nat:=c28 c43 c44; let c46:Nat:=c28 c42 c45; let c47:Nat:=c28 c41 c46; let c48:Nat:=c33 c47; let c49:Nat:=c28 c31 c48; let c50:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b"); let c51:Cond:=Cond.lt (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")); let c52:Com:=Com.assign "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")); let c53:Com:=Com.seq c52 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult); let c54:Com:=Com.ite c51 c53 (RamPadSelector.constantFraction ((0:Nat))); let c55:Com:=Com.assign "left.n" c36; let c56:Com:=Com.assign "left.d" c38; let c57:Nat:=c28 (Env.vars σ "source.m") (Env.vars σ "source.n"); let c58:Prop:=Nat.lt (Env.vars σ "query.row") c57; let c59:Prop:=Not c58; let c60:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c61:Nat:=c60 (Env.vars σ "query.row") (Env.vars σ "source.m"); let c62:Env:=Env.setVar σ "query.a.row" c61; let c63:Nat:=Env.vars c62 "query.a.row"; let c64:Env:=Env.setVar c62 "vec.i" c63; let c65:String→ String:=c8 "source.c"; let c66:String:=c65 ".s"; let c67:Nat:=Env.vars c64 "vec.i"; let c68:Nat:= @List.getD Nat (Env.arrs c64 c66) c67 ((0:Nat)); let c69:Env:=Env.setVar c64 "left.s" c68; let c70:String:=c65 ".n"; let c71:Nat:=Env.vars c69 "vec.i"; let c72:Nat:= @List.getD Nat (Env.arrs c69 c70) c71 ((0:Nat)); let c73:Env:=Env.setVar c69 "left.n" c72; let c74:String:=c65 ".d"; let c75:Nat:=Env.vars c73 "vec.i"; let c76:Nat:= @List.getD Nat (Env.arrs c73 c74) c75 ((0:Nat)); let c77:Env:=Env.setVar c73 "left.d" c76; let c78:Nat:=Env.vars c77 "left.s"; let c79:Env:=Env.setVar c77 "rat.s" c78; let c80:Nat:=Env.vars c79 "left.n"; let c81:Env:=Env.setVar c79 "rat.n" c80; let c82:Nat:=Env.vars c81 "left.d"; let c83:Env:=Env.setVar c81 "rat.d" c82; let c84:Nat:=Env.vars c83 "rat.s"; let c85:Nat:=c60 ((1:Nat)) c84; let c86:Env:=Env.setVar c83 "rat.s" c85; let c87:Nat→ Nat:=c28 (c29 (Cond.size c51)); let c88:Nat:=c29 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "source.m"))); let c89:Expr:=Expr.get c66 (Expr.var "vec.i"); let c90:Nat:=c29 (Expr.size c89); let c91:Expr:=Expr.get c70 (Expr.var "vec.i"); let c92:Nat:=c29 (Expr.size c91); let c93:Expr:=Expr.get c74 (Expr.var "vec.i"); let c94:Nat:=c29 (Expr.size c93); let c95:Nat:=c28 c92 c94; let c96:Nat:=c28 c90 c95; let c97:Nat:=c28 c96 c46; let c98:Nat:=c33 c97; let c99:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c100:Nat:=c29 (Expr.size c99); let c101:Nat:=c28 c98 c100; let c102:Nat:=c28 c88 c101; let c103:Nat:=c87 c102; let c104:Com:=Com.assign "left.n" c91; let c105:Com:=Com.assign "left.d" c93; let c106:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c107:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c108:Env→ Prop:=fun (σ':Env) => And (c106 σ' ((6:Nat))) (c107 σ'); let c109:Nat:=c87 ((6:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c27 (@And.intro (Run B selectBound σ c27 ((40:Nat))) (c3 c27) (RunStep.mono B selectBound σ c27 (c30 c49) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c50 c54 σ c27 c49 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.row")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c27 c31 c48 (RunStep.assign B σ "query.a.row" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_2))) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) c7 c27 c32 c47 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "vec.i" (Expr.var "query.a.row") c6 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.row")) "query.a.row" (?nAX_g5048_2_0_3))) (RunStep.seq B (loadLeft "source.b") RamCopy.leftToResult c7 c21 c27 c41 c46 (RunStep.seq B (Com.assign "left.s" c34) (Com.seq c55 c56) c7 c13 c21 c35 c40 (RunStep.assign B c7 "left.s" c34 c12 (RunStep.eval_get B c7 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c7 "vec.i" (?nAX_g5048_2_0_4)) (?nAX_g5048_2_0_5) (?nAX_g5048_2_0_6))) (RunStep.seq B c55 c56 c13 c17 c21 c37 c39 (RunStep.assign B c13 "left.n" c36 c16 (RunStep.eval_get B c13 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c13 "vec.i" (?nAX_g5048_2_0_7)) (?nAX_g5048_2_0_8) (?nAX_g5048_2_0_9))) (RunStep.assign B c17 "left.d" c38 c20 (RunStep.eval_get B c17 c18 (Expr.var "vec.i") c19 (RunStep.eval_var B c17 "vec.i" (?nAX_g5048_2_0_10)) (?nAX_g5048_2_0_11) (?nAX_g5048_2_0_12))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c21 c23 c27 c42 c45 (RunStep.assign B c21 "rat.s" (Expr.var "left.s") c22 (RunStep.eval_var B c21 "left.s" (?nAX_g5048_2_0_13))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c23 c25 c27 c43 c44 (RunStep.assign B c23 "rat.n" (Expr.var "left.n") c24 (RunStep.eval_var B c23 "left.n" (?nAX_g5048_2_0_14))) (RunStep.assign B c25 "rat.d" (Expr.var "left.d") c26 (RunStep.eval_var B c25 "left.d" (?nAX_g5048_2_0_15))))))))) (?nAX_g5048_2_0_16)) ?_)) fun (hcase:c1) => @Or.casesOn c58 c59 (fun (x:Or c58 c59) => c5) (Classical.em c58) (fun (hcase_1:c58) => @Exists.intro Env c4 c86 (@And.intro (Run B selectBound σ c86 ((40:Nat))) (c3 c86) (RunStep.mono B selectBound σ c86 (c30 c103) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c50 c54 σ c86 c103 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_17)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_18)) hcase) (RunStep.ite_true B c51 c53 (RamPadSelector.constantFraction ((0:Nat))) σ c86 c102 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c57 (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_19)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_20)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_2_0_21)) (?nAX_g5048_2_0_22)) hcase_1) (RunStep.seq B c52 (Com.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult) σ c62 c86 c88 c101 (RunStep.assign B σ "query.a.row" (Expr.sub (Expr.var "query.row") (Expr.var "source.m")) c61 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_23)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_24)) (?nAX_g5048_2_0_25))) (RunStep.seq B (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult c62 c83 c86 c98 c100 (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.c") c62 c64 c83 c32 c97 (RunStep.assign B c62 "vec.i" (Expr.var "query.a.row") c63 (RunStep.eval_var B c62 "query.a.row" (?nAX_g5048_2_0_26))) (RunStep.seq B (loadLeft "source.c") RamCopy.leftToResult c64 c77 c83 c96 c46 (RunStep.seq B (Com.assign "left.s" c89) (Com.seq c104 c105) c64 c69 c77 c90 c95 (RunStep.assign B c64 "left.s" c89 c68 (RunStep.eval_get B c64 c66 (Expr.var "vec.i") c67 (RunStep.eval_var B c64 "vec.i" (?nAX_g5048_2_0_27)) (?nAX_g5048_2_0_28) (?nAX_g5048_2_0_29))) (RunStep.seq B c104 c105 c69 c73 c77 c92 c94 (RunStep.assign B c69 "left.n" c91 c72 (RunStep.eval_get B c69 c70 (Expr.var "vec.i") c71 (RunStep.eval_var B c69 "vec.i" (?nAX_g5048_2_0_30)) (?nAX_g5048_2_0_31) (?nAX_g5048_2_0_32))) (RunStep.assign B c73 "left.d" c93 c76 (RunStep.eval_get B c73 c74 (Expr.var "vec.i") c75 (RunStep.eval_var B c73 "vec.i" (?nAX_g5048_2_0_33)) (?nAX_g5048_2_0_34) (?nAX_g5048_2_0_35))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c77 c79 c83 c42 c45 (RunStep.assign B c77 "rat.s" (Expr.var "left.s") c78 (RunStep.eval_var B c77 "left.s" (?nAX_g5048_2_0_36))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c79 c81 c83 c43 c44 (RunStep.assign B c79 "rat.n" (Expr.var "left.n") c80 (RunStep.eval_var B c79 "left.n" (?nAX_g5048_2_0_37))) (RunStep.assign B c81 "rat.d" (Expr.var "left.d") c82 (RunStep.eval_var B c81 "left.d" (?nAX_g5048_2_0_38))))))) (RunStep.assign B c83 "rat.s" c99 c85 (RunStep.eval_sub B c83 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c84 (RunStep.eval_lit B ((1:Nat)) c83 h1) (RunStep.eval_var B c83 "rat.s" (?nAX_g5048_2_0_39)) (?nAX_g5048_2_0_40))))))) (?nAX_g5048_2_0_41)) ?_)) fun (hcase_1:c59) => @Exists.casesOn Env c108 (fun (x:@Exists Env c108) => c5) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c107 τ) ((6:Nat)) hz σ ?_) fun (w:Env) (h:And (c106 w ((6:Nat))) (c107 w)) => let c0_1:Prop:=c106 w ((6:Nat)); @And.casesOn c0_1 (c107 w) (fun (x:And c0_1 (c107 w)) => c5) h fun (left:c0_1) (right:c107 w) => @Exists.intro Env c4 w (@And.intro (Run B selectBound σ w ((40:Nat))) (c3 w) (RunStep.mono B selectBound σ w (c30 c109) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.m")) c50 c54 σ w c109 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.m") (Env.vars σ "query.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_42)) (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_43)) hcase) (RunStep.ite_false B c51 c53 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.add (Expr.var "source.m") (Expr.var "source.n")) (Env.vars σ "query.row") c57 (RunStep.eval_var B σ "query.row" (?nAX_g5048_2_0_44)) (RunStep.eval_add B σ (Expr.var "source.m") (Expr.var "source.n") (Env.vars σ "source.m") (Env.vars σ "source.n") (RunStep.eval_var B σ "source.m" (?nAX_g5048_2_0_45)) (RunStep.eval_var B σ "source.n" (?nAX_g5048_2_0_46)) (?nAX_g5048_2_0_47)) hcase_1) left)) (?nAX_g5048_2_0_48)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5048_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5048_2_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
        all_goals clear hz
        all_goals simp_all [CertificateFamilyEntries.pairRhs]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

end Lax109476Proofs.RamPairSelector

end

theorem solution:∀ (B M m n:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (i:
    Fin
      (Nat.add m
        (Nat.add n
          ((2:Nat))))),
  Nat.le ((1:Nat)) M→
    Nat.lt M B→
      Nat.lt
          (Nat.add (Nat.add m n)
            ((4:Nat)))
          B→
        (∀ (r:Fin m),Nat.le (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M)→
          (∀ (s:Fin n),Nat.le (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M)→
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                  (@Eq Nat (σ.vars "query.row")
                    (@Fin.val
                      (Nat.add m
                        (Nat.add n
                          ((2:Nat))))
                      i)))
              Lax109476Proofs.RamPairSelector.selectBound
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                  (Lax109476Proofs.RamRational.FractionOutput
                    (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairRhs m n P i)) τ))
              ((40:Nat)):= @Lax109476Proofs.RamPairSelector.selectBound_spec
