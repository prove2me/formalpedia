-- Prove2me | solution 1 for Lax263307Proofs.NativeMomentVectors.read_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:39.926572+00:00
-- url     : https://prove2.me/submissions/790c09f9-7e04-414b-879e-dc3ed35f19b0

import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
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

theorem ite_true (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_true hb h

theorem ite_false (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_false hb h

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

end RunStep

end Lax808846Proofs.Reasoning
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

theorem mask_member {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    (mask I).testBit v.val=decide (v∈I):=by
  rw [mask_test_bit]
  congr 1
  simp [Finset.mem_image,Fin.val_inj]

theorem mask_injective (n:ℕ):Function.Injective (mask (n:=n)):=by
  intro I J h
  ext v
  have hh:=congrArg (fun m:ℕ => m.testBit v.val) h
  simpa only [mask_member,decide_eq_decide] using hh

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

theorem candidates_length (n k:ℕ):(candidates n k).length=n.choose k:=by
  simp [candidates,List.length_sublistsLen]

open Lax109476Proofs

end Lax263307Proofs.NativeExhaustive

end

section

namespace Lax263307Proofs.NativeCatalogOrder

open Lax263307

theorem sublist_toFinset_injective (n:ℕ) (xs ys:List (Fin n))
    (hx:xs.Sublist (List.finRange n)) (hy:ys.Sublist (List.finRange n))
    (he:xs.toFinset=ys.toFinset):xs=ys:=by
  have hs:(List.finRange n).Pairwise (fun u v:Fin n => u< v):=by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.getElem_finRange,Fin.lt_def,Fin.val_cast] using hij
  apply (hs.sublist hx).eq_of_mem_iff (hs.sublist hy)
  intro v
  have hh:=congrArg (fun I:Finset (Fin n) => v∈I) he
  simpa only [List.mem_toFinset] using Iff.of_eq hh

theorem candidates_nodup (n k:ℕ):(ExhaustiveTargets.candidates n k).Nodup:=by
  exact List.Nodup.map_on (by
    intro xs hx ys hy he
    exact sublist_toFinset_injective n xs ys (List.mem_sublistsLen.mp hx).1
      (List.mem_sublistsLen.mp hy).1 he)
    (List.nodup_sublistsLen k (List.nodup_finRange n))

theorem candidate_card (n k:ℕ) (I:Finset (Fin n)) (hI:I∈ExhaustiveTargets.candidates n k):
    I.card=k:=by
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hI
  obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hxs
  rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]

theorem all_candidates_nodup (n R:ℕ):(RationalConditioning.candidates n R).Nodup:=by
  change ((List.range (R+1)).flatMap (fun k => ExhaustiveTargets.candidates n k)).Nodup
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => candidates_nodup n k,?_⟩
  apply List.nodup_range.imp
  intro k l hne I hI hJ
  exact hne ((candidate_card n k I hI).symm.trans (candidate_card n l I hJ))

theorem sets_eq (n r:ℕ):CoordinateCatalog.sets n r=RationalConditioning.candidates n (r+2):=by
  exact List.dedup_eq_self.mpr (all_candidates_nodup n (r+2))

theorem catalog_values (n r:ℕ):
    (CoordinateCatalog.catalog n r).map Subtype.val=RationalConditioning.candidates n (r+2):=by
  rw [CoordinateCatalog.catalog,List.map_map]
  simpa only [Function.comp_def,List.attach_map_subtype_val] using sets_eq n r

theorem catalog_index (n r:ℕ) (j:Fin (CoordinateCatalog.catalog n r).length):
    (RationalConditioning.candidates n (r+2))[j.val]?=some (CoordinateCatalog.indexing n r j).val:=by
  rw [←catalog_values,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

theorem all_candidates_succ (n R:ℕ):
    RationalConditioning.candidates n (R+1)=
      RationalConditioning.candidates n R++ExhaustiveTargets.candidates n (R+1):=by
  unfold RationalConditioning.candidates ExhaustiveTargets.candidates
  rw [List.range_succ,List.flatMap_append]
  simp

end Lax263307Proofs.NativeCatalogOrder

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCatalog

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

def block (n k:ℕ):List ℕ:=
  (ExhaustiveTargets.candidates n k).map NativeMasks.mask

theorem block_length (n k:ℕ):(block n k).length=n.choose k:=by
  simp only [block,List.length_map,NativeExhaustive.candidates_length]

def rows (n q:ℕ):List ℕ:=(List.range q).flatMap (block n)

theorem rows_zero (n:ℕ):rows n 0=[]:=rfl

theorem rows_succ (n q:ℕ):rows n (q+1)=rows n q++block n q:=by
  simp only [rows,List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem rows_length_mono (n:ℕ):Monotone (fun q => (rows n q).length):=by
  apply monotone_nat_of_le_succ
  intro q
  rw [rows_succ,List.length_append]
  omega

theorem rows_length_step (n q:ℕ):(rows n (q+1)).length=(rows n q).length+n.choose q:=by
  rw [rows_succ,List.length_append,block_length]

theorem rows_exact (n r:ℕ):rows n (r+3)=
    (CoordinateCatalog.catalog n r).map (fun A => NativeMasks.mask A.val):=by
  change rows n (r+3)=(CoordinateCatalog.catalog n r).map (NativeMasks.mask ∘ Subtype.val)
  rw [←List.map_map,NativeCatalogOrder.catalog_values]
  simp only [rows,RationalConditioning.candidates,List.map_flatMap]
  rfl

theorem rows_words (n r:ℕ):rows n (r+3)=Lax263307.NativeCatalog.words n r:=rows_exact n r

theorem rows_positive (n R:ℕ):1≤(rows n (R+1)).length:=by
  have h:=rows_length_mono n (show 1≤ R+1 by omega)
  have h1:(rows n 1).length=1:=by
    rw [show 1=0+1 from rfl,rows_length_step,rows_zero]
    simp
  simpa only [h1] using h

open Lax109476Proofs

end Lax263307Proofs.NativeCatalog

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

namespace Lax263307Proofs.NativeMaskUnpack

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks

theorem bit_value {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    Nat.land (mask I / 2^v.val) 1=if v∈I then 1 else 0:=by
  rw [Nat.land_eq,Nat.and_one_is_mod]
  have h:=mask_member I v
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have hm:=Nat.mod_lt (mask I / 2^v.val) (by omega:0<2)
  by_cases hv:v∈I
  · simp only [hv,decide_true,decide_eq_true_eq,if_true] at h ⊢
    exact h
  · simp only [hv,decide_false,decide_eq_false_iff_not,if_false] at h ⊢
    omega

theorem prefix_card_step {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    (initialSet I (i+1)).card=(initialSet I i).card+(if (⟨i,hi⟩:Fin n)∈I then 1 else 0):=by
  rw [prefix_succ I i hi]
  have hm:(⟨i,hi⟩:Fin n)∉initialSet I i:=by simp [initialSet]
  by_cases h:(⟨i,hi⟩:Fin n)∈I <;> simp [h,Finset.card_insert_of_notMem hm]

theorem card_bound {n:ℕ} (I:Finset (Fin n)):I.card≤ n:=by
  simpa using Finset.card_le_univ I

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "unpack.mask"=mask I∧ σ.vars "unpack.i"≤ n∧
  n≤(σ.arrs "subset.bits").length∧
  Prefix ((encodeOutput I).take (σ.vars "unpack.i")) "subset.bits" σ∧
  σ.vars "unpack.card"=(initialSet I (σ.vars "unpack.i")).card

theorem step_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant I σ∧ σ.vars "unpack.i"< n) step
      (fun σ τ => Invariant I τ∧ τ.vars "unpack.i"=σ.vars "unpack.i"+1) 17:=by
  rintro σ ⟨⟨hn,hmask,hle,hroom,hprefix,hcard⟩,hlt⟩
  let i:=σ.vars "unpack.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈I then 1 else 0
  have hbit:bit≤1:=by dsimp [bit]; split_ifs <;> omega
  have hbitB:bit< B:=by omega
  have hiB:i< B:=by omega
  have hmaskB:mask I< B:=(mask_bound I).trans hm
  have hdiv:mask I/2^i< B:=(Nat.div_le_self _ _).trans_lt hmaskB
  have hval:(Expr.and (.shiftr (.var "unpack.mask") (.var "unpack.i")) (.lit 1)).evalB B σ=some bit:=by
    have hh:=evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr)
        (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hmaskB⟩) (evalB_var hiB) hdiv)
      (evalB_lit (show 1< B by omega)) (by change Nat.land (mask I/2^i) 1< B; rw [bit_value I ⟨i,hlt⟩]; exact hbitB)
    exact hh.trans (congrArg some (bit_value I ⟨i,hlt⟩))
  let ν:=σ.setVar "unpack.bit" bit
  have r1:Run B read σ ν 6:=Run.assign hval
  have hcardν:ν.vars "unpack.card"=(initialSet I i).card:=
    (r1.frame_var "unpack.card" (by decide)).trans hcard
  have hnextB:(initialSet I (i+1)).card< B:=(card_bound _).trans_lt (by omega)
  have hsum:(initialSet I i).card+bit< B:=by rw [←prefix_card_step I i hlt]; exact hnextB
  let μ:=ν.setVar "unpack.card" ((initialSet I i).card+bit)
  have r2:Run B (.assign "unpack.card" (.add (.var "unpack.card") (.var "unpack.bit"))) ν μ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hcardν.symm,hcardν ▸ (card_bound _).trans_lt (by omega)⟩)
      (by simpa [ν] using evalB_var (σ:=ν) (x:="unpack.bit") (show ν.vars "unpack.bit"< B by simp [ν]; exact hbitB)) hsum)
  have r12:=r1.seq r2
  have hiμ:μ.vars "unpack.i"=i:=r12.frame_var "unpack.i" (by decide)
  have hbitμ:μ.vars "unpack.bit"=bit:=by simp [μ,ν]
  have hlen:(encodeOutput I).length=n:=List.length_ofFn
  have hilen:i<(encodeOutput I).length:=by rwa [hlen]
  have htake:((encodeOutput I).take i).length=i:=by rw [List.length_take,hlen,Nat.min_eq_left hle]
  have hentry:(encodeOutput I)[i]=bit:=by simp [encodeOutput,bit]
  obtain ⟨τ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "unpack.i"
    ((encodeOutput I).take i) bit (.var "unpack.bit") (by omega) (by rw [htake]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htake],by rw [htake,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨hbitμ.symm,hbitμ ▸ hbitB⟩⟩
  have ht:τ.vars "unpack.i"=i+1:=by simpa only [htake] using p3.2
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "unpack.mask" (by decide)).trans hmask,by rw [ht]; omega,?_,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hilen,hentry]
    exact p3.1
  · rw [ht,prefix_card_step I i hlt,r3.frame_var "unpack.card" (by decide)]
    simp [μ,bit]

theorem command_spec {n:ℕ} (B:ℕ) (I:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "unpack.mask"=mask I∧ n≤(σ.arrs "subset.bits").length)
      command (fun _ τ => Prefix (encodeOutput I) "subset.bits" τ∧ τ.vars "unpack.card"=I.card) (21*n+8):=by
  have hloop:=Spec.forRangeZero "unpack.i" "graph.n" (Invariant I) n 17 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hmask,hroom⟩
  let ν:=σ.setVar "unpack.card" 0
  have r1:Run B (.assign "unpack.card" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant I (ν.setVar "unpack.i" 0):=by
    refine ⟨?_,?_,by simp,hroom,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hmask
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_,?_⟩
  · have htake:(encodeOutput I).take n=encodeOutput I:=List.take_of_length_le (by simp [encodeOutput])
    simpa only [p2.2,htake] using p2.1.2.2.2.2.1
  · simpa only [p2.2,prefix_full] using p2.1.2.2.2.2.2

end Lax263307Proofs.NativeMaskUnpack

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

theorem read_mask_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readMask
      (fun _ τ => Data G r τ∧ τ.vars "unpack.mask"=NativeMasks.mask (atIndex n r i)) 3:=by
  rintro σ ⟨hd,hi⟩
  have hlen:(Lax263307.NativeCatalog.words n r).length=N n r:=by simp [Lax263307.NativeCatalog.words]
  have hget:=hd.2.2.1 i.val (by rw [hlen]; exact i.isLt)
  have hw:(Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i):=by
    simp only [Lax263307.NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let τ:=σ.setVar "unpack.mask" (NativeMasks.mask (atIndex n r i))
  have rr:Run B readMask σ τ 3:=Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hget ((NativeMasks.mask_bound _).trans hm))
  exact ⟨τ,rr,data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,by simp [τ]⟩

theorem prepare_set_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) prepareSet
      (fun _ τ => Data G r τ∧ Prefix (encodeOutput (atIndex n r i)) "subset.bits" τ∧
        τ.vars "unpack.card"=(atIndex n r i).card) (21*n+11):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=read_mask_spec B G r i hN hm σ ⟨hd,hi⟩
  obtain ⟨τ,r2,p2⟩:=NativeMaskUnpack.command_spec B (atIndex n r i) hB hm ν
    ⟨p1.1.1,p1.2,p1.1.2.2.2.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,p2⟩

theorem read_card_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readCard
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=(atIndex n r i).card) (21*n+13):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i hB hN hm σ ⟨hd,hi⟩
  let τ:=ν.setVar "fill.value" (atIndex n r i).card
  have r2:Run B (.assign "fill.value" (.var "unpack.card")) ν τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p1.2.2.symm,p1.2.2 ▸ (NativeMaskUnpack.card_bound _).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,by simp [τ]⟩

theorem read_independent_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n*n+n+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readIndependent
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)
      (38*n*n+21*n+25):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i (by omega) hN hm σ ⟨hd,hi⟩
  obtain ⟨μ,r2,p2⟩:=NativeIndependentTest.command_spec B G (atIndex n r i) "search.graph" "subset.bits" hB ν
    ⟨p1.1.1,p1.1.2.2.2.1,p1.2.1⟩
  have hok:μ.vars "test.ok"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0:=by
    split_ifs with h
    · exact p2.2.2.mpr h
    · have hh:μ.vars "test.ok"≠1:=fun h1 => h (p2.2.2.mp h1)
      omega
  let τ:=μ.setVar "fill.value" (μ.vars "test.ok")
  have r3:Run B (.assign "fill.value" (.var "test.ok")) μ τ 2:=Run.assign (evalB_var (p2.2.1.trans_lt (by omega)))
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,
    by simpa only [τ,vars_setVar,if_true] using hok⟩

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (hB:n*n+n+3< B) (hN:N n r+1< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ N n r≤(σ.arrs "catalog.card").length∧ N n r≤(σ.arrs "catalog.independent").length)
      command (fun _ τ => Data G r τ∧ Prefix (cards n r) "catalog.card" τ∧ Prefix (independent G r) "catalog.independent" τ)
      ((38*n*n+42*n+60)*(N n r)+14):=by
  have hc:(cards n r).length=N n r:=List.length_ofFn
  have hi:(independent G r).length=N n r:=List.length_ofFn
  have hcards:=NativeTabulate.command_spec B (cards n r) "catalog.card" (Data G r) readCard (21*n+13)
    (by rwa [hc]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega))
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i hi; simpa only [cards,List.getElem_ofFn] using read_card_spec B G r ⟨i,by rwa [hc] at hi⟩ (by omega) (by omega) hm)
  have hind:=NativeTabulate.command_spec B (independent G r) "catalog.independent" (Data G r) readIndependent (38*n*n+21*n+25)
    (by rwa [hi]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; split_ifs <;> omega)
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i h; simpa only [independent,List.getElem_ofFn] using read_independent_spec B G r ⟨i,by rwa [hi] at h⟩ hB (by omega) hm)
  rintro σ ⟨hd,hcr,hir⟩
  let ν:=σ.setVar "fill.length" (N n r)
  have r1:Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (by omega)⟩)
  have d1:=data_frame G r r1 (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩:=hcards ν ⟨d1,by simp [ν,hc],by simpa only [ν,arrs_setVar,hc] using hcr⟩
  have hlength:μ.vars "fill.length"=(independent G r).length:=by
    rw [r2.frame_var "fill.length" (by decide)]
    simp [ν,hi]
  obtain ⟨τ,r3,p3⟩:=hind μ ⟨p2.1,hlength,by rw [hi,Lax455465Proofs.RamFrames.run_array_length r2]; exact hir⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hc,hi]; nlinarith),p3.1,?_,p3.2⟩
  simpa only [Prefix,r3.frame_arr "catalog.card" (by decide)] using p2.2

end Lax263307Proofs.NativeCatalogMetadata

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks
open Lax263307

def same {n:ℕ} (A J:Finset (Fin n)):ℕ:=if A=J then 1 else 0

theorem same_le {n:ℕ} (A J:Finset (Fin n)):same A J≤1:=by unfold same; split_ifs <;> omega

theorem same_masks {n:ℕ} (A J:Finset (Fin n)):
    (if mask A=mask J then 1 else 0)=same A J:=by simp only [(mask_injective n).eq_iff,same]

theorem same_single_row {n r:ℕ} (A:Finset (Fin n)) (j:MomentLP.Index n r):
    (same A (CoordinateCatalog.indexing n r j).val:ℚ)=MomentLP.singleRow A j:=by
  simp only [same,MomentLP.singleRow,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem compare_spec (B a b:ℕ) (dst left right:String) (ha:a< B) (hb:b< B) (h1:1< B):
    Spec B (fun σ => σ.vars left=a∧ σ.vars right=b) (compare dst left right)
      (fun _ τ => τ.vars dst=if a=b then 1 else 0) 6:=by
  rintro σ ⟨hleft,hright⟩
  have hcond:=evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ ha⟩)
    (by rw [evalB_var_iff]; exact ⟨hright.symm,hright ▸ hb⟩)
  by_cases h:a=b
  · have hc:(Cond.eq (.var left) (.var right)).evalB B σ=some true:=by simpa only [h,beq_self_eq_true] using hcond
    have hr:=Run.ite_true (d:=.assign dst (.lit 0)) hc (Run.assign (x:=dst) (evalB_lit h1))
    exact ⟨_,hr,by simp [h]⟩
  · have hc:(Cond.eq (.var left) (.var right)).evalB B σ=some false:=by simpa only [beq_eq_false_iff_ne.mpr h] using hcond
    have hr:=Run.ite_false (c:=.assign dst (.lit 1)) hc (Run.assign (x:=dst) (evalB_lit (by omega:0< B)))
    exact ⟨_,hr,by simp [h]⟩

theorem insert_spec {n:ℕ} (B:ℕ) (A:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "row.v"=v.val) insertCommand
      (fun _ τ => τ.vars "row.insert"=mask (insert v A)) 6:=by
  rintro σ ⟨hA,hv⟩
  have hAv:mask A< B:=(mask_bound _).trans hm
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hpow:2^v.val< B:=(Nat.pow_lt_pow_right (by omega) v.isLt).trans hm
  have hins:mask (insert v A)< B:=(mask_bound _).trans hm
  have hval:(Expr.or (.var "row.mask") (.shiftl (.lit 1) (.var "row.v"))).evalB B σ=some (mask (insert v A)):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hA.symm,hA ▸ hAv⟩)
      (evalB_bin (op:=.shiftl) (evalB_lit (show 1< B by omega))
        (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ hvB⟩) (by simpa only [Bop.apply_shiftl,one_mul] using hpow))
      (by change Nat.lor (mask A) (1*2^v.val)< B; simpa only [one_mul,←mask_insert] using hins)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←mask_insert] using hh
  exact ⟨_,Run.assign hval,by simp⟩

theorem monotone_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => τ.vars "coefficient.positive"=same (insert v A) J∧ τ.vars "coefficient.negative"=same A J) 18:=by
  rintro σ ⟨hA,hJ,hv⟩
  obtain ⟨ν,r1,p1⟩:=insert_spec B A v hB hm σ ⟨hA,hv⟩
  obtain ⟨μ,r2,p2⟩:=compare_spec B (mask (insert v A)) (mask J) "coefficient.positive" "row.insert" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨p1,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have r12:=r1.seq r2
  obtain ⟨τ,r3,p3⟩:=compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) μ
    ⟨(r12.frame_var "row.mask" (by decide)).trans hA,(r12.frame_var "column.mask" (by decide)).trans hJ⟩
  refine ⟨τ,r1.seq (r2.seq r3),?_,?_⟩
  · rw [r3.frame_var "coefficient.positive" (by decide),p2,same_masks]
  · simpa only [same_masks] using p3

theorem monotone_value {n r:ℕ} (A:Finset (Fin n)) (v:Fin n) (j:MomentLP.Index n r):
    (same (insert v A) (CoordinateCatalog.indexing n r j).val:ℚ)-same A (CoordinateCatalog.indexing n r j).val=
      MomentLP.monotoneRow A v j:=by rw [same_single_row,same_single_row]; rfl

def matchCount {n:ℕ} (A J:Finset (Fin n)) (i:ℕ):ℕ:=
  ((List.finRange n).take i).countP fun v => decide (insert v A=J)

theorem matches_zero {n:ℕ} (A J:Finset (Fin n)):matchCount A J 0=0:=by simp [matchCount]

theorem matches_bound {n:ℕ} (A J:Finset (Fin n)) (i:ℕ):matchCount A J i≤ n:=by
  have h:matchCount A J i≤((List.finRange n).take i).length:=List.countP_le_length
  simp only [List.length_take,List.length_finRange] at h
  omega

theorem matches_succ {n:ℕ} (A J:Finset (Fin n)) (i:ℕ) (hi:i< n):
    matchCount A J (i+1)=matchCount A J i+same (insert ⟨i,hi⟩ A) J:=by
  have hilen:i<(List.finRange n).length:=by simpa using hi
  simp only [matchCount,List.take_succ_eq_append_getElem hilen,List.countP_append,List.countP_singleton,
    List.getElem_finRange,same,decide_eq_true_eq]
  rfl

theorem countP_as_sum {α:Type*} (xs:List α) (f:α→ Bool):
    xs.countP f=(xs.map fun x => if f x then 1 else 0).sum:=by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h:f a <;> simp [h,ih,Nat.add_comm]

theorem matches_value {n r:ℕ} (A:Finset (Fin n)) (j:MomentLP.Index n r):
    (matchCount A (CoordinateCatalog.indexing n r j).val n:ℚ)=∑ v,MomentLP.singleRow (insert v A) j:=by
  rw [matchCount,List.take_of_length_le (by simp),countP_as_sum,←List.ofFn_eq_map,List.sum_ofFn]
  simp [MomentLP.singleRow]

theorem mass_value {n r:ℕ} (A:Finset (Fin n)) (k:ℕ) (j:MomentLP.Index n r):
    (matchCount A (CoordinateCatalog.indexing n r j).val n:ℚ)-(k*same A (CoordinateCatalog.indexing n r j).val:ℕ)=
      MomentLP.massRow A k j:=by
  rw [matches_value,Nat.cast_mul,same_single_row]
  rfl

def CountInvariant {n:ℕ} (A J:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧
  σ.vars "row.v"≤ n∧ σ.vars "coefficient.positive"=matchCount A J (σ.vars "row.v")

theorem count_step_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => CountInvariant A J σ∧ σ.vars "row.v"< n) countStep
      (fun σ τ => CountInvariant A J τ∧ τ.vars "row.v"=σ.vars "row.v"+1) 18:=by
  rintro σ ⟨⟨hn,hA,hJ,hle,hcount⟩,hlt⟩
  let i:=σ.vars "row.v"
  let v:Fin n:= ⟨i,hlt⟩
  have hiB:i< B:=by omega
  obtain ⟨ν,r1,p1⟩:=insert_spec B A v hB hm σ ⟨hA,rfl⟩
  have hcolν:ν.vars "column.mask"=mask J:=(r1.frame_var "column.mask" (by decide)).trans hJ
  have hcountν:ν.vars "coefficient.positive"=matchCount A J i:=
    (r1.frame_var "coefficient.positive" (by decide)).trans hcount
  have hcB:matchCount A J i< B:=(matches_bound A J i).trans_lt (by omega)
  have hc1B:matchCount A J i+1< B:=by have h:=matches_bound A J i; omega
  have heval:=evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (mask_bound _).trans hm⟩)
    (by rw [evalB_var_iff]; exact ⟨hcolν.symm,hcolν ▸ (mask_bound _).trans hm⟩)
  obtain ⟨μ,r2,p2⟩:∃ μ,Run B countBranch ν μ 8∧ μ.vars "coefficient.positive"=matchCount A J (i+1):=by
    by_cases h:insert v A=J
    · have he:mask (insert v A)=mask J:=congrArg mask h
      have hb:(Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some true:=by
        simpa only [he,beq_self_eq_true] using heval
      have hv:(Expr.add (.var "coefficient.positive") (.lit 1)).evalB B ν=some (matchCount A J i+1):=
        evalB_bin (op:=.add)
          (by rw [evalB_var_iff]; exact ⟨hcountν.symm,hcountν ▸ hcB⟩) (evalB_lit (by omega)) hc1B
      refine ⟨_,Run.ite_true (d:=.skip) hb (Run.assign hv),?_⟩
      simp only [vars_setVar,if_true,matches_succ A J i hlt,same,show insert ⟨i,hlt⟩ A=J from h,if_true]
    · have he:mask (insert v A)≠mask J:=fun he => h ((mask_injective n) he)
      have hb:(Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some false:=by
        simpa only [beq_eq_false_iff_ne.mpr he] using heval
      refine ⟨ν,(Run.ite_false (c:=.assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))) hb Run.skip).mono (by decide),?_⟩
      simpa only [matches_succ A J i hlt,same,show ¬insert ⟨i,hlt⟩ A=J from h,if_false,Nat.add_zero] using hcountν
  have r12:=r1.seq r2
  have hiμ:μ.vars "row.v"=i:=r12.frame_var "row.v" (by decide)
  let τ:=μ.setVar "row.v" (i+1)
  have r3:Run B (.assign "row.v" (.add (.var "row.v") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) (evalB_lit (by omega)) (by change i+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  have ht:τ.vars "row.v"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "row.mask" (by decide)).trans hA,(rr.frame_var "column.mask" (by decide)).trans hJ,
    by rw [ht]; omega,?_⟩,ht⟩
  rw [ht,r3.frame_var "coefficient.positive" (by decide)]
  exact p2

theorem count_command_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J)
      countCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n) (22*n+8):=by
  have hloop:=Spec.forRangeZero "row.v" "graph.n" (CountInvariant A J) n 18 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1) (count_step_spec B A J hB hm)
  rintro σ ⟨hn,hA,hJ⟩
  let ν:=σ.setVar "coefficient.positive" 0
  have r1:Run B (.assign "coefficient.positive" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have r0:Run B (.assign "row.v" (.lit 0)) ν (ν.setVar "row.v" 0) 2:=Run.assign (evalB_lit (by omega))
  have hi:CountInvariant A J (ν.setVar "row.v" 0):=by
    refine ⟨?_,?_,?_,by simp,?_⟩
    · exact ((r1.seq r0).frame_var "graph.n" (by decide)).trans hn
    · exact ((r1.seq r0).frame_var "row.mask" (by decide)).trans hA
    · exact ((r1.seq r0).frame_var "column.mask" (by decide)).trans hJ
    · change 0=matchCount A J 0
      exact (matches_zero A J).symm
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [p2.2] using p2.1.2.2.2.2⟩

theorem mass_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (k:ℕ) (hB:n+2< B) (hk:k< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n∧ τ.vars "coefficient.negative"=k*same A J)
      (22*n+18):=by
  rintro σ ⟨hn,hA,hJ,hkσ⟩
  obtain ⟨ν,r1,p1⟩:=count_command_spec B A J hB hm σ ⟨hn,hA,hJ⟩
  obtain ⟨μ,r2,p2⟩:=compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨(r1.frame_var "row.mask" (by decide)).trans hA,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have hb:μ.vars "coefficient.negative"=same A J:=by simpa only [same_masks] using p2
  have r12:=r1.seq r2
  have hkμ:μ.vars "row.k"=k:=(r12.frame_var "row.k" (by decide)).trans hkσ
  have hprod:k*same A J< B:=(by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J):k*same A J≤ k).trans_lt hk
  let τ:=μ.setVar "coefficient.negative" (k*same A J)
  have r3:Run B (.assign "coefficient.negative" (.mul (.var "row.k") (.var "coefficient.negative"))) μ τ 4:=Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ hk⟩)
      (by rw [evalB_var_iff]; exact ⟨hb.symm,hb ▸ (same_le A J).trans_lt (by omega)⟩) hprod)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,by simp [τ]⟩
  exact ((r2.seq r3).frame_var "coefficient.positive" (by decide)).trans p1

end Lax263307Proofs.NativeMomentRows

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata

theorem activate_spec (B c r:ℕ) (hB:c+r+3< B):
    Spec B (fun σ => σ.vars "row.card"=c∧ σ.vars "moment.r"=r) activate
      (fun _ τ => τ.vars "row.active"=if c≤ r+1 then 1 else 0) 8:=by
  by_cases h:c< r+2
  · have h':c≤ r+1:=by omega
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 r ((1:Nat)); let c2:Nat:= @ite Nat (Nat.le c c1) (Nat.decLe c c1) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "row.active") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B activate σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat:=c0 (Env.vars σ "moment.r") ((2:Nat)); let c7:Prop:=Nat.lt (Env.vars σ "row.card") c6; let c8:Prop:=Not c7; let c9:Env:=Env.setVar σ "row.active" ((1:Nat)); let c10:Nat→ Nat:=c0 ((1:Nat)); let c11:Expr:=Expr.add (Expr.var "moment.r") (Expr.lit ((2:Nat))); let c12:Cond:=Cond.lt (Expr.var "row.card") c11; let c13:Nat→ Nat:=c0 (c10 (Cond.size c12)); let c14:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c15:Com:=Com.assign "row.active" (Expr.lit ((1:Nat))); let c16:Com:=Com.assign "row.active" (Expr.lit ((0:Nat))); let c17:Env:=Env.setVar σ "row.active" ((0:Nat)); let c18:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); @And.casesOn (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r) (fun (x:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => c5) a fun (left:@Eq Nat (Env.vars σ "row.card") c) (right:@Eq Nat (Env.vars σ "moment.r") r) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c5) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c4 c9 (@And.intro (Run B activate σ c9 ((8:Nat))) (c3 c9) (RunStep.mono B activate σ c9 (c13 c14) ((8:Nat)) (RunStep.ite_true B c12 c15 c16 σ c9 c14 (RunStep.cond_lt_true B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_0_0_0)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_0_0_1)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_0_0_2)) (?nAX_g8118_0_0_3)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8118_0_0_4)))) (?nAX_g8118_0_0_5)) ?_)) fun (hcase:c8) => @Exists.intro Env c4 c17 (@And.intro (Run B activate σ c17 ((8:Nat))) (c3 c17) (RunStep.mono B activate σ c17 (c13 c18) ((8:Nat)) (RunStep.ite_false B c12 c15 c16 σ c17 c18 (RunStep.cond_lt_false B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_0_0_6)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_0_0_7)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_0_0_8)) (?nAX_g8118_0_0_9)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8118_0_0_10)))) (?nAX_g8118_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8118_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · have h':¬c≤ r+1:=by omega
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 r ((1:Nat)); let c2:Nat:= @ite Nat (Nat.le c c1) (Nat.decLe c c1) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "row.active") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B activate σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat:=c0 (Env.vars σ "moment.r") ((2:Nat)); let c7:Prop:=Nat.lt (Env.vars σ "row.card") c6; let c8:Prop:=Not c7; let c9:Env:=Env.setVar σ "row.active" ((1:Nat)); let c10:Nat→ Nat:=c0 ((1:Nat)); let c11:Expr:=Expr.add (Expr.var "moment.r") (Expr.lit ((2:Nat))); let c12:Cond:=Cond.lt (Expr.var "row.card") c11; let c13:Nat→ Nat:=c0 (c10 (Cond.size c12)); let c14:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c15:Com:=Com.assign "row.active" (Expr.lit ((1:Nat))); let c16:Com:=Com.assign "row.active" (Expr.lit ((0:Nat))); let c17:Env:=Env.setVar σ "row.active" ((0:Nat)); let c18:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); @And.casesOn (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r) (fun (x:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => c5) a fun (left:@Eq Nat (Env.vars σ "row.card") c) (right:@Eq Nat (Env.vars σ "moment.r") r) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c5) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c4 c9 (@And.intro (Run B activate σ c9 ((8:Nat))) (c3 c9) (RunStep.mono B activate σ c9 (c13 c14) ((8:Nat)) (RunStep.ite_true B c12 c15 c16 σ c9 c14 (RunStep.cond_lt_true B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_1_0_0)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_1_0_1)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_1_0_2)) (?nAX_g8118_1_0_3)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8118_1_0_4)))) (?nAX_g8118_1_0_5)) ?_)) fun (hcase:c8) => @Exists.intro Env c4 c17 (@And.intro (Run B activate σ c17 ((8:Nat))) (c3 c17) (RunStep.mono B activate σ c17 (c13 c18) ((8:Nat)) (RunStep.ite_false B c12 c15 c16 σ c17 c18 (RunStep.cond_lt_false B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_1_0_6)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_1_0_7)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_1_0_8)) (?nAX_g8118_1_0_9)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8118_1_0_10)))) (?nAX_g8118_1_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8118_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
    all_goals omega

def Loaded {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (σ:Env):Prop:=
  σ.vars "row.mask"=NativeMasks.mask (atIndex n r i)∧
  σ.vars "column.mask"=NativeMasks.mask (atIndex n r j)∧
  σ.vars "row.card"=(atIndex n r i).card∧
  σ.vars "row.independent"=(if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)

theorem mask_word (n r:ℕ) (i:Fin (N n r)):
    (Lax263307.NativeCatalog.words n r)[i.val]?=some (NativeMasks.mask (atIndex n r i)):=by
  rw [Lax263307.NativeCatalog.words,List.getElem?_map,List.getElem?_eq_getElem i.isLt]
  rfl

theorem load_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (hB:n+r+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "row.index"=i.val∧ σ.vars "column.index"=j.val)
      load (fun _ τ => Loaded G r i j τ) 12:=by
  rintro σ ⟨hd,hi,hj⟩
  have hlen:(Lax263307.NativeCatalog.words n r).length=N n r:=by simp [Lax263307.NativeCatalog.words]
  have hmask:∀ l:Fin (N n r),(σ.arrs "catalog.mask")[l.val]?=some (NativeMasks.mask (atIndex n r l)):=by
    intro l
    have hli:l.val<(Lax263307.NativeCatalog.words n r).length:=by rw [hlen]; exact l.isLt
    have hh:=hd.1.2.2.1 l.val hli
    have he:=mask_word n r l
    rw [List.getElem?_eq_getElem hli] at he
    exact hh.trans he
  have hcard:(σ.arrs "catalog.card")[i.val]?=some (atIndex n r i).card:=by
    have hh:=hd.2.1 i.val (by simp [cards])
    simpa only [cards,List.getElem_ofFn] using hh
  have hind:(σ.arrs "catalog.independent")[i.val]?=
      some (if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0):=by
    have hh:=hd.2.2.1 i.val (by simp [independent])
    simpa only [independent,List.getElem_ofFn] using hh
  have hcardB:(atIndex n r i).card< B:=(NativeMaskUnpack.card_bound _).trans_lt (by omega)
  have hindB:(if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)< B:=by split_ifs <;> omega
  have hiB:=i.isLt.trans hN
  have hjB:=j.isLt.trans hN
  have hrowB:=(NativeMasks.mask_bound (atIndex n r i)).trans hm
  have hcolB:=(NativeMasks.mask_bound (atIndex n r j)).trans hm
  let ν:=σ.setVar "row.mask" (NativeMasks.mask (atIndex n r i))
  have r1:Run B (.assign "row.mask" (.get "catalog.mask" (.var "row.index"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (hmask i) hrowB)
  have hiν:ν.vars "row.index"=i.val:=(r1.frame_var "row.index" (by decide)).trans hi
  let μ:=ν.setVar "row.card" (atIndex n r i).card
  have r2:Run B (.assign "row.card" (.get "catalog.card" (.var "row.index"))) ν μ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) hcard hcardB)
  have hiμ:μ.vars "row.index"=i.val:=(r2.frame_var "row.index" (by decide)).trans hiν
  let ξ:=μ.setVar "row.independent" (if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)
  have r3:Run B (.assign "row.independent" (.get "catalog.independent" (.var "row.index"))) μ ξ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) hind hindB)
  have hjξ:ξ.vars "column.index"=j.val:=((r1.seq (r2.seq r3)).frame_var "column.index" (by decide)).trans hj
  let τ:=ξ.setVar "column.mask" (NativeMasks.mask (atIndex n r j))
  have r4:Run B (.assign "column.mask" (.get "catalog.mask" (.var "column.index"))) ξ τ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hjξ.symm,hjξ ▸ hjB⟩) (hmask j) hcolB)
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr,?_,?_,?_,?_⟩
  · rw [(r2.seq (r3.seq r4)).frame_var "row.mask" (by decide)]
    exact (vars_setVar σ "row.mask" (NativeMasks.mask (atIndex n r i)) "row.mask").trans (if_pos rfl)
  · exact (vars_setVar ξ "column.mask" (NativeMasks.mask (atIndex n r j)) "column.mask").trans (if_pos rfl)
  · rw [(r3.seq r4).frame_var "row.card" (by decide)]
    exact (vars_setVar ν "row.card" (atIndex n r i).card "row.card").trans (if_pos rfl)
  · rw [r4.frame_var "row.independent" (by decide)]
    exact (vars_setVar μ "row.independent" _ "row.independent").trans (if_pos rfl)

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (hB:n+r+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "row.index"=i.val∧ σ.vars "column.index"=j.val)
      command (fun _ τ => Loaded G r i j τ∧ τ.vars "row.active"=if (atIndex n r i).card≤ r+1 then 1 else 0) 20:=by
  rintro σ ⟨hd,hi,hj⟩
  obtain ⟨ν,r1,p1⟩:=load_spec B G r i j hB hN hm σ ⟨hd,hi,hj⟩
  obtain ⟨τ,r2,p2⟩:=activate_spec B (atIndex n r i).card r
    (by have h:=NativeMaskUnpack.card_bound (atIndex n r i); omega) ν
    ⟨p1.2.2.1,(r1.frame_var "moment.r" (by decide)).trans hd.2.2.2⟩
  refine ⟨τ,r1.seq r2,?_,p2⟩
  simpa only [Loaded,r2.frame_var "row.mask" (by decide),r2.frame_var "column.mask" (by decide),
    r2.frame_var "row.card" (by decide),r2.frame_var "row.independent" (by decide)] using p1

end Lax263307Proofs.NativeMomentAccess

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentProduce

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks NativeMomentRows

theorem zero_spec (B:ℕ) (hB:0< B):Spec B (fun _ => True) zeroCommand (fun _ τ => Value B 0 τ) 4:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=Value B (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c3:Env:=Env.setVar c2 "coefficient.negative" ((0:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B zeroCommand σ σ' ((4:Nat))) (c1 σ')) c3 (@And.intro (Run B zeroCommand σ c3 ((4:Nat))) (c1 c3) (RunStep.mono B zeroCommand σ c3 (c4 c5 c5) ((4:Nat)) (RunStep.seq B (Com.assign "coefficient.positive" (Expr.lit ((0:Nat)))) (Com.assign "coefficient.negative" (Expr.lit ((0:Nat)))) σ c2 c3 c5 c5 (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hB)) (RunStep.assign B c2 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 hB))) (?nAX_g8126_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8126_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,Env.setVar]

theorem single_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (h1:1< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J)
      singleCommand (fun _ τ => Value B (same A J) τ) 8:=by
  rintro σ ⟨hA,hJ⟩
  obtain ⟨ν,r1,p1⟩:=compare_spec B (mask A) (mask J) "coefficient.positive" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) h1 σ ⟨hA,hJ⟩
  have hp:ν.vars "coefficient.positive"=same A J:=by simpa only [same_masks] using p1
  let τ:=ν.setVar "coefficient.negative" 0
  have r2:Run B (.assign "coefficient.negative" (.lit 0)) ν τ 2:=Run.assign (evalB_lit (by omega))
  refine ⟨τ,r1.seq r2,?_,by simp [τ]; omega,?_⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,hp] using (same_le A J).trans_lt h1
  · simp only [τ,vars_setVar,String.reduceEq,if_false,if_true,hp,Nat.cast_zero,sub_zero]

theorem monotone_value_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => Value B ((same (insert v A) J:ℚ)-same A J) τ) 18:=by
  intro σ hσ
  obtain ⟨τ,rr,p⟩:=monotone_spec B A J v hB hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.2]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.1,p.2]

theorem mass_value_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (k:ℕ) (hB:n+2< B) (hk:k< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => Value B ((matchCount A J n:ℚ)-(k*same A J:ℕ)) τ) (22*n+18):=by
  intro σ hσ
  obtain ⟨τ,rr,p⟩:=mass_spec B A J k hB hk hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (matches_bound A J n).trans_lt (by omega)
  · rw [p.2]
    exact (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J):k*same A J≤ k).trans_lt hk
  · rw [p.1,p.2]

theorem swap_spec (B:ℕ) (q:ℚ):Spec B (Value B q) swap (fun _ τ => Value B (-q) τ) 6:=by
  rintro σ ⟨hp,hn,hq⟩
  let ν:=σ.setVar "coefficient.temp" (σ.vars "coefficient.positive")
  have r1:Run B (.assign "coefficient.temp" (.var "coefficient.positive")) σ ν 2:=Run.assign (evalB_var hp)
  let μ:=ν.setVar "coefficient.positive" (σ.vars "coefficient.negative")
  have r2:Run B (.assign "coefficient.positive" (.var "coefficient.negative")) ν μ 2:=Run.assign (evalB_var hn)
  let τ:=μ.setVar "coefficient.negative" (σ.vars "coefficient.positive")
  have r3:Run B (.assign "coefficient.negative" (.var "coefficient.temp")) μ τ 2:=Run.assign (evalB_var hp)
  refine ⟨τ,r1.seq (r2.seq r3),hn,hp,?_⟩
  change (σ.vars "coefficient.negative" :ℚ)-σ.vars "coefficient.positive"=-q
  rw [←hq]
  ring

theorem guard_spec (B expected K:ℕ) (flag:String) (P:Env→ Prop) (test:Prop) [Decidable test]
    (q:ℚ) (c:Com) (hB:1< B) (hex:expected≤1)
    (hc:Spec B P c (fun _ τ => Value B q τ) K):
    Spec B (fun σ => P σ∧ σ.vars flag=if test then expected else 1-expected)
      (guard flag expected c) (fun _ τ => Value B (if test then q else 0) τ) (K+8):=by
  rintro σ ⟨hP,hflag⟩
  have heB:expected< B:=hex.trans_lt hB
  have hnB:1-expected< B:=by omega
  by_cases h:test
  · have hf:σ.vars flag=expected:=by simpa only [if_pos h] using hflag
    obtain ⟨τ,rr,p⟩:=hc σ hP
    have hb:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some true:=by
      have hh:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some (expected==expected):=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ heB⟩) (evalB_lit heB)
      simpa using hh
    exact ⟨τ,(Run.ite_true (d:=zeroCommand) hb rr).mono (by simp [Cond.size,Expr.size]; omega),by simpa only [if_pos h] using p⟩
  · have hf:σ.vars flag=1-expected:=by simpa only [if_neg h] using hflag
    obtain ⟨τ,rr,p⟩:=zero_spec B (by omega) σ trivial
    have hne:1-expected≠expected:=by omega
    have hb:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some false:=by
      have hh:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some (1-expected==expected):=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hnB⟩) (evalB_lit heB)
      simpa only [beq_eq_false_iff_ne.mpr hne] using hh
    exact ⟨τ,(Run.ite_false (c:=c) hb rr).mono (by simp [Cond.size,Expr.size]),by simpa only [if_neg h] using p⟩

end Lax263307Proofs.NativeMomentProduce

end

section

namespace Lax263307Proofs.NativeMomentAssembly

open Lax263307 Lax109476.RationalEncoding
open MomentLP CoordinateCatalog

def normalization (n r:ℕ):Fin 2→ Index n r→ ℚ:=
  fun i j => if i=0 then singleRow ∅ j else -singleRow ∅ j

def upper (n r:ℕ):Index n r→ Index n r→ ℚ:=fun i => singleRow (indexing n r i).val

def nonindependent {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if G.IsIndepSet ((indexing n r i).val:Set (Fin n)) then 0 else singleRow (indexing n r i).val j

def monotone (n r:ℕ):Fin (dimension n r*n)→ Index n r→ ℚ:=
  fun i => let uv:=finProdFinEquiv.symm i
    if (indexing n r uv.1).val.card≤ r+1 then monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0

def massPositive (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i => if (indexing n r i).val.card≤ r+1 then massRow (indexing n r i).val k else fun _ => 0

def massNegative (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if (indexing n r i).val.card≤ r+1 then -massRow (indexing n r i).val k j else 0

end Lax263307Proofs.NativeMomentAssembly

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP

def rowCount (kind:Kind) (n r:ℕ):ℕ:=match kind with
  | .normalization => 2
  | .monotone => dimension n r*n
  | _ => dimension n r

def matrix (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    Fin (rowCount kind n r)→ Index n r→ ℚ:=match kind with
  | .normalization => NativeMomentAssembly.normalization n r
  | .upper => NativeMomentAssembly.upper n r
  | .nonindependent => NativeMomentAssembly.nonindependent G r
  | .monotone => NativeMomentAssembly.monotone n r
  | .massPositive => NativeMomentAssembly.massPositive n k r
  | .massNegative => NativeMomentAssembly.massNegative n k r

theorem coordinates_spec (B q columns:ℕ) (hB:q+columns+3< B):
    Spec B (fun σ => σ.vars "fill.i"=q∧ σ.vars "catalog.count"=columns) coordinates
      (fun _ τ => τ.vars "family.row"=q/columns∧ τ.vars "column.index"=q%columns) 10:=by
  have hdiv:q/columns≤ q:=Nat.div_le_self _ _
  have hmul:q/columns*columns≤ q:=Nat.div_mul_le_self _ _
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns)) => let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 q columns; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) q columns; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "family.row") c1) (@Eq Nat (Env.vars τ "column.index") c2)) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B coordinates σ σ' ((10:Nat))) (c3 σ'); let c5:Nat:=c0 (Env.vars σ "fill.i") (Env.vars σ "catalog.count"); let c6:Env:=Env.setVar σ "family.row" c5; let c7:String→ Nat:=Env.vars c6; let c8:Nat:=c7 "fill.i"; let c9:Nat:=c7 "family.row"; let c10:Nat:=c7 "catalog.count"; let c11:Nat:=Nat.mul c9 c10; let c12:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c8 c11; let c13:Env:=Env.setVar c6 "column.index" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count"))); let c17:Expr:=Expr.sub (Expr.var "fill.i") (Expr.mul (Expr.var "family.row") (Expr.var "catalog.count")); let c18:Nat:=c15 (Expr.size c17); let c19:String→ Nat:=Env.vars c13; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns)) => @Exists Env c4) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") columns) => @Exists.intro Env c4 c13 (@And.intro (Run B coordinates σ c13 ((10:Nat))) (c3 c13) (RunStep.mono B coordinates σ c13 (c14 c16 c18) ((10:Nat)) (RunStep.seq B (Com.assign "family.row" (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count"))) (Com.assign "column.index" c17) σ c6 c13 c16 c18 (RunStep.assign B σ "family.row" (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count")) c5 (RunStep.eval_div B σ (Expr.var "fill.i") (Expr.var "catalog.count") (Env.vars σ "fill.i") (Env.vars σ "catalog.count") (RunStep.eval_var B σ "fill.i" (?nAX_g8178_0_0_0)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8178_0_0_1)) ?_)) (RunStep.assign B c6 "column.index" c17 c12 (RunStep.eval_sub B c6 (Expr.var "fill.i") (Expr.mul (Expr.var "family.row") (Expr.var "catalog.count")) c8 c11 (RunStep.eval_var B c6 "fill.i" (?nAX_g8178_0_0_2)) (RunStep.eval_mul B c6 (Expr.var "family.row") (Expr.var "catalog.count") c9 c10 (RunStep.eval_var B c6 "family.row" ?_) (RunStep.eval_var B c6 "catalog.count" (?nAX_g8178_0_0_3)) ?_) (?nAX_g8178_0_0_4)))) (?nAX_g8178_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8178_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,Nat.mod_eq_sub_div_mul]
  all_goals omega

theorem candidates_first (n R:ℕ):(RationalConditioning.candidates n R)[0]?=some (∅:Finset (Fin n)):=by
  induction R with
  | zero => simp [RationalConditioning.candidates]
  | succ R ih =>
    rw [NativeCatalogOrder.all_candidates_succ]
    have hp:0<(RationalConditioning.candidates n R).length:=by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at ih
      contradiction
    rw [List.getElem?_append_left hp]
    exact ih

theorem dimension_positive (n r:ℕ):0< dimension n r:=by
  have h:=NativeCatalog.rows_positive n (r+2)
  change 1≤(NativeCatalog.rows n (r+3)).length at h
  rw [NativeCatalog.rows_words] at h
  simpa only [Lax263307.NativeCatalog.words,List.length_map,Nat.succ_le_iff] using h

theorem first_coordinate (n r:ℕ):
    (CoordinateCatalog.indexing n r ⟨0,dimension_positive n r⟩).val=∅:=by
  have hi:=NativeCatalogOrder.catalog_index n r ⟨0,dimension_positive n r⟩
  have he:=candidates_first n (r+2)
  exact Option.some.inj (hi.symm.trans he)

def rowSlot (kind:Kind) (n r:ℕ) (i:Fin (rowCount kind n r)):Index n r:=match kind with
  | .normalization => ⟨0,dimension_positive n r⟩
  | .monotone => (finProdFinEquiv.symm i).1
  | .upper => i
  | .nonindependent => i
  | .massPositive => i
  | .massNegative => i

def Vertex (kind:Kind) (n r:ℕ) (i:Fin (rowCount kind n r)) (σ:Env):Prop:=match kind with
  | .monotone => σ.vars "row.v"=(finProdFinEquiv.symm i).2.val
  | _ => True

theorem select_row_spec (kind:Kind) (n r B:ℕ) (i:Fin (rowCount kind n r))
    (hB:i.val+n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "family.row"=i.val) (selectRow kind)
      (fun _ τ => τ.vars "row.index"=(rowSlot kind n r i).val∧ Vertex kind n r i τ) 10:=by
  have hdiv:i.val/n≤ i.val:=Nat.div_le_self _ _
  have hmul:i.val/n*n≤ i.val:=Nat.div_mul_le_self _ _
  cases kind <;> (first
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.normalization n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.normalization n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.normalization n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.normalization n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.normalization) σ σ' ((10:Nat)))
                              (c2 σ');
                          let c4:Env:=Env.setVar σ "row.index" ((0:Nat));
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 c4
                              (@And.intro
                                (Run B (selectRow Kind.normalization) σ c4 ((10:Nat)))
                                (c2 c4)
                                (RunStep.mono B (selectRow Kind.normalization) σ c4
                                  (Nat.add
                                    ((1:Nat))
                                    (Expr.size (Expr.lit ((0:Nat)))))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.lit ((0:Nat)))
                                    ((0:Nat))
                                    (RunStep.eval_lit B ((0:Nat)) σ
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.upper n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.upper n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.upper n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.upper n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.upper) σ σ' ((10:Nat))) (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.upper) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.upper) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.nonindependent n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.nonindependent n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.nonindependent n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.nonindependent n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.nonindependent) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.nonindependent) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.nonindependent) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.monotone n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.monotone n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.monotone n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.monotone n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.monotone) σ σ' ((10:Nat))) (c2 σ');
                          let c4:Nat:=
                            @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "family.row") (Env.vars σ "graph.n");
                          let c5:Env:=Env.setVar σ "row.index" c4;
                          let c6:String→ Nat:=Env.vars c5;
                          let c7:Nat:=c6 "family.row";
                          let c8:Nat:=c6 "row.index";
                          let c9:Nat:=c6 "graph.n";
                          let c10:Nat:=Nat.mul c8 c9;
                          let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10;
                          let c12:Env:=Env.setVar c5 "row.v" c11;
                          let c13:Nat→ Nat→ Nat:=Nat.add;
                          let c14:Nat→ Nat:=c13 ((1:Nat));
                          let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "family.row") (Expr.var "graph.n")));
                          let c16:Expr:=Expr.sub (Expr.var "family.row") (Expr.mul (Expr.var "row.index") (Expr.var "graph.n"));
                          let c17:Nat:=c14 (Expr.size c16);
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 c12
                              (@And.intro
                                (Run B (selectRow Kind.monotone) σ c12 ((10:Nat))) (c2 c12)
                                (RunStep.mono B (selectRow Kind.monotone) σ c12 (c13 c15 c17)
                                  ((10:Nat))
                                  (RunStep.seq B (Com.assign "row.index" (Expr.div (Expr.var "family.row") (Expr.var "graph.n")))
                                    (Com.assign "row.v" c16) σ c5 c12 c15 c17
                                    (RunStep.assign B σ "row.index" (Expr.div (Expr.var "family.row") (Expr.var "graph.n")) c4
                                      (RunStep.eval_div B σ (Expr.var "family.row") (Expr.var "graph.n") (Env.vars σ "family.row")
                                        (Env.vars σ "graph.n")
                                        (RunStep.eval_var B σ "family.row"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        (RunStep.eval_var B σ "graph.n"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        ?_))
                                    (RunStep.assign B c5 "row.v" c16 c11
                                      (RunStep.eval_sub B c5 (Expr.var "family.row") (Expr.mul (Expr.var "row.index") (Expr.var "graph.n"))
                                        c7 c10
                                        (RunStep.eval_var B c5 "family.row"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        (RunStep.eval_mul B c5 (Expr.var "row.index") (Expr.var "graph.n") c8 c9
                                          (RunStep.eval_var B c5 "row.index" ?_)
                                          (RunStep.eval_var B c5 "graph.n"
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_)
                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massPositive n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massPositive n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.massPositive n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.massPositive n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.massPositive) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.massPositive) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.massPositive) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massNegative n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massNegative n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.massNegative n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.massNegative n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.massNegative) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.massNegative) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.massNegative) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                 )
  all_goals simp_all [rowSlot,Vertex,Env.setVar,finProdFinEquiv,Fin.divNat,Fin.modNat,Nat.mod_eq_sub_div_mul]
  all_goals omega

def fixedVars:List String:= ["graph.n","catalog.count","moment.r","row.k"]
def fixedArrays:List String:= ["catalog.mask","search.graph","catalog.card","catalog.independent"]

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hv:∀ x∈ fixedVars,x∉c.wvars) (ha:∀ x∈ fixedArrays,x∉c.warrs)
    (hσ:Data G k r σ):Data G k r τ:=by
  refine ⟨⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by decide)) (hv _ (by decide))
    (ha _ (by decide)) (ha _ (by decide)) hσ.1.1,?_,?_,?_⟩,?_⟩
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.card" (ha _ (by decide))] using hσ.1.2.1
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.independent" (ha _ (by decide))] using hσ.1.2.2.1
  · exact (rr.frame_var "moment.r" (hv _ (by decide))).trans hσ.1.2.2.2
  · exact (rr.frame_var "row.k" (hv _ (by decide))).trans hσ.2

open NativeCatalogMetadata NativeMomentProduce

def Ready (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (i:Fin (rowCount kind n r)) (j:Index n r) (σ:Env):Prop:=
  NativeMomentAccess.Loaded G r (rowSlot kind n r i) j σ∧ σ.vars "graph.n"=n∧
  σ.vars "row.k"=k∧ σ.vars "row.active"=(if (atIndex n r (rowSlot kind n r i)).card≤ r+1 then 1 else 0)∧
  σ.vars "family.row"=i.val∧ Vertex kind n r i σ

theorem produce_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (i:Fin (rowCount kind n r)) (j:Index n r) (hB:n+k+3 < B) (hm:2^n < B):
    Spec B (Ready kind G k r i j) (produce kind)
      (fun _ τ => Value B (matrix kind G k r i j) τ) (22*n+50):=by
  rintro σ ⟨hl,hn,hk,ha,hi,hv⟩
  have h1:1 < B:=by omega
  cases kind with
  | normalization =>
    change Fin 2 at i
    have hz:atIndex n r (rowSlot .normalization n r i)=∅:=first_coordinate n r
    obtain ⟨ν,r1,p1⟩:=single_spec B (atIndex n r (rowSlot .normalization n r i)) (atIndex n r j)
      h1 hm σ ⟨hl.1,hl.2.1⟩
    have pv:Value B (MomentLP.singleRow ∅ j) ν:=by
      rw [hz] at p1
      simpa only [atIndex,NativeMomentRows.same_single_row] using p1
    have hiB:i.val < B:=i.isLt.trans (by change 2 < B; omega)
    have hc:(Cond.eq (.var "family.row") (.lit 0)).evalB B σ=some (i.val==0):=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (evalB_lit (show 0 < B by omega))
    by_cases he:i=0
    · have hei:i.val=0:=congrArg Fin.val he
      have rr:=Run.ite_true (d:=.seq singleCommand swap) (by simpa only [hei,beq_self_eq_true] using hc) r1
      exact ⟨ν,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_pos he] using pv⟩
    · have hei:i.val≠0:=fun hh => he (Fin.ext hh)
      obtain ⟨τ,r2,p2⟩:=swap_spec B (MomentLP.singleRow ∅ j) ν pv
      have rr:=Run.ite_false (c:=singleCommand) (by simpa only [beq_eq_false_iff_ne.mpr hei] using hc) (r1.seq r2)
      exact ⟨τ,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_neg he] using p2⟩
  | upper =>
    obtain ⟨τ,rr,p⟩:=single_spec B (atIndex n r i) (atIndex n r j) h1 hm σ ⟨hl.1,hl.2.1⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,matrix,NativeMomentAssembly.upper] using p
  | nonindependent =>
    have hf:σ.vars "row.independent"=(if ¬G.IsIndepSet (atIndex n r i:Set (Fin n)) then 0 else 1-0):=by
      by_cases h:G.IsIndepSet (atIndex n r i:Set (Fin n))
      · simpa [rowSlot,h] using hl.2.2.2
      · simpa [rowSlot,h] using hl.2.2.2
    obtain ⟨τ,rr,p⟩:=guard_spec B 0 8 "row.independent" _ (¬G.IsIndepSet (atIndex n r i:Set (Fin n)))
      (NativeMomentRows.same (atIndex n r i) (atIndex n r j)) singleCommand h1 (by omega)
      (single_spec B (atIndex n r i) (atIndex n r j) h1 hm) σ ⟨⟨hl.1,hl.2.1⟩,hf⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,ite_not,matrix,NativeMomentAssembly.nonindependent] using p
  | monotone =>
    let v:Fin n:=(finProdFinEquiv.symm i).2
    let A:=atIndex n r (finProdFinEquiv.symm i).1
    obtain ⟨τ,rr,p⟩:=guard_spec B 1 18 "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.same (insert v A) (atIndex n r j):ℚ)-NativeMomentRows.same A (atIndex n r j))
      NativeMomentRows.monotoneCommand h1 (by omega)
      (monotone_value_spec B A (atIndex n r j) v (by omega) hm) σ ⟨⟨hl.1,hl.2.1,hv⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,v,atIndex,NativeMomentRows.monotone_value,matrix,NativeMomentAssembly.monotone,ite_apply] using p
  | massPositive =>
    let A:=atIndex n r i
    obtain ⟨τ,rr,p⟩:=guard_spec B 1 (22*n+18) "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n:ℚ)-(k*NativeMomentRows.same A (atIndex n r j):ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,matrix,NativeMomentAssembly.massPositive,ite_apply] using p
  | massNegative =>
    let A:=atIndex n r i
    obtain ⟨ν,r1,p1⟩:=guard_spec B 1 (22*n+18) "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n:ℚ)-(k*NativeMomentRows.same A (atIndex n r j):ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    obtain ⟨τ,r2,p2⟩:=swap_spec B _ ν p1
    refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,apply_ite,neg_zero,matrix,NativeMomentAssembly.massNegative] using p2

theorem read_fixed_vars (kind:Kind):∀ x∈ fixedVars,x∉(read kind).wvars:=by
  cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_fixed_arrays (kind:Kind):∀ x∈ fixedArrays,x∉(read kind).warrs:=by
  cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (z:Fin (rowCount kind n r*dimension n r))
    (hB:rowCount kind n r*dimension n r+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "fill.i"=z.val) (read kind)
      (fun _ τ => Data G k r τ∧ Value B
        (matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) τ) (22*n+90):=by
  rintro σ ⟨hd,hz⟩
  let i:=(finProdFinEquiv.symm z).1
  let j:=(finProdFinEquiv.symm z).2
  have hiq:i.val=z.val/dimension n r:=rfl
  have hjq:j.val=z.val%dimension n r:=rfl
  have hiq':i.val≤ z.val:=by rw [hiq]; exact Nat.div_le_self _ _
  obtain ⟨ν,r1,p1⟩:=coordinates_spec B z.val (dimension n r) (by have h:=z.isLt; omega) σ ⟨hz,hd.1.1.2.1⟩
  have d1:Data G k r ν:=data_frame G k r r1
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd
  obtain ⟨μ,r2,p2⟩:=select_row_spec kind n r B i (by have h:=z.isLt; omega) ν ⟨d1.1.1.1,p1.1⟩
  have d2:Data G k r μ:=data_frame G k r r2
    (by cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide)
    (by cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide) d1
  obtain ⟨ξ,r3,p3⟩:=NativeMomentAccess.command_spec B G r (rowSlot kind n r i) j (by omega) (by change dimension n r < B; omega) hm μ
    ⟨d2.1,p2.1,(r2.frame_var "column.index" (by cases kind <;> decide)).trans p1.2⟩
  have hn:ξ.vars "graph.n"=n:=(r3.frame_var "graph.n" (by decide)).trans d2.1.1.1
  have hk:ξ.vars "row.k"=k:=(r3.frame_var "row.k" (by decide)).trans d2.2
  have hir:ξ.vars "family.row"=i.val:=((r2.seq r3).frame_var "family.row" (by cases kind <;> decide)).trans p1.1
  have hv:Vertex kind n r i ξ:=by
    cases kind <;> simp only [Vertex] at p2 ⊢
    all_goals first | trivial | exact (r3.frame_var "row.v" (by decide)).trans p2.2
  obtain ⟨τ,r4,p4⟩:=produce_spec kind B G k r i j (by omega) hm ξ ⟨p3.1,hn,hk,p3.2,hir,hv⟩
  have rr:Run B (read kind) σ τ (10+(10+(20+(22*n+50)))):=r1.seq (r2.seq (r3.seq r4))
  exact ⟨τ,rr.mono (by omega),data_frame G k r rr (read_fixed_vars kind) (read_fixed_arrays kind) hd,p4⟩

end Lax263307Proofs.NativeMomentFamily

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce

theorem read_spec (B N q:ℕ) (hB:q+N+4 < B):
    Spec B (fun σ => σ.vars "fill.i"=q∧ σ.vars "catalog.count"=N) read
      (fun _ τ => Value B (value N q) τ) 18:=by
  by_cases hq:q=1
  · subst q
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") ((1:Nat))) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c1:Env→ Prop:=Value B (value N ((1:Nat))); let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Prop:=Not c0; let c6:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c7:Nat:=Env.vars c6 "fill.i"; let c8:Prop:= @Eq Nat c7 ((1:Nat)); let c9:Prop:=Not c8; let c10:Nat→ Env:=Env.setVar c6 "coefficient.negative"; let c11:Env:=c10 ((1:Nat)); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c15:Nat→ Nat:=c12 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat:=c15 c16; let c18:Nat→ Nat:=c12 c17; let c19:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c20:Nat:=c15 c19; let c21:Com→ Com→ Com:=Com.ite c14; let c22:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c23:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c24:Cond:=Cond.lt (Expr.var "fill.i") c23; let c25:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c26:Com:=Com.ite c24 c25 c22; let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c28:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c29:Env:=c10 ((0:Nat)); let c30:Nat:=c12 (Env.vars σ "catalog.count") ((2:Nat)); let c31:Prop:=Nat.lt (Env.vars σ "fill.i") c30; let c32:Prop:=Not c31; let c33:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c34:Nat:=Env.vars c33 "fill.i"; let c35:Prop:= @Eq Nat c34 ((1:Nat)); let c36:Prop:=Not c35; let c37:Nat→ Env:=Env.setVar c33 "coefficient.negative"; let c38:Env:=c37 ((1:Nat)); let c39:Nat→ Nat:=c12 (c13 (Cond.size c24)); let c40:Nat:=c39 c19; let c41:Nat:=c15 c40; let c42:Nat→ Nat:=c12 c41; let c43:Env:=c37 ((0:Nat)); let c44:Nat:=c39 c16; let c45:Nat:=c15 c44; let c46:Nat→ Nat:=c12 c45; @And.casesOn c0 (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And c0 (@Eq Nat (Env.vars σ "catalog.count") N)) => c4) a fun (left:c0) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c0 c5 (fun (x:Or c0 c5) => c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c4) (Classical.em c8) (fun (hcase_1:c8) => @Exists.intro Env c3 c11 (@And.intro (Run B read σ c11 ((18:Nat))) (c2 c11) (RunStep.mono B read σ c11 (c18 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c11 c17 c20 (RunStep.ite_true B c14 c22 c26 σ c6 c16 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_2)))) (RunStep.ite_true B c14 c27 c28 c6 c11 c19 (RunStep.cond_eq_true B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_4)) hcase_1) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_5))))) (?nAX_g8213_0_0_6)) ?_)) fun (hcase_1:c9) => @Exists.intro Env c3 c29 (@And.intro (Run B read σ c29 ((18:Nat))) (c2 c29) (RunStep.mono B read σ c29 (c18 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c29 c17 c17 (RunStep.ite_true B c14 c22 c26 σ c6 c16 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_9)))) (RunStep.ite_false B c14 c27 c28 c6 c29 c16 (RunStep.cond_eq_false B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_10)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_11)) hcase_1) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c6 (?nAX_g8213_0_0_12))))) (?nAX_g8213_0_0_13)) ?_)) fun (hcase:c5) => @Or.casesOn c31 c32 (fun (x:Or c31 c32) => c4) (Classical.em c31) (fun (hcase_1:c31) => @Or.casesOn c35 c36 (fun (x:Or c35 c36) => c4) (Classical.em c35) (fun (hcase_2:c35) => @Exists.intro Env c3 c38 (@And.intro (Run B read σ c38 ((18:Nat))) (c2 c38) (RunStep.mono B read σ c38 (c42 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c33 c38 c41 c20 (RunStep.ite_false B c14 c22 c26 σ c33 c40 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_15)) hcase) (RunStep.ite_true B c24 c25 c22 σ c33 c19 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_18)) (?nAX_g8213_0_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_20))))) (RunStep.ite_true B c14 c27 c28 c33 c38 c19 (RunStep.cond_eq_true B c33 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c34 ((1:Nat)) (RunStep.eval_var B c33 "fill.i" (?nAX_g8213_0_0_21)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_22)) hcase_2) (RunStep.assign B c33 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_23))))) (?nAX_g8213_0_0_24)) ?_)) fun (hcase_2:c36) => @Exists.intro Env c3 c43 (@And.intro (Run B read σ c43 ((18:Nat))) (c2 c43) (RunStep.mono B read σ c43 (c42 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c33 c43 c41 c17 (RunStep.ite_false B c14 c22 c26 σ c33 c40 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_26)) hcase) (RunStep.ite_true B c24 c25 c22 σ c33 c19 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_29)) (?nAX_g8213_0_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_31))))) (RunStep.ite_false B c14 c27 c28 c33 c43 c16 (RunStep.cond_eq_false B c33 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c34 ((1:Nat)) (RunStep.eval_var B c33 "fill.i" (?nAX_g8213_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_33)) hcase_2) (RunStep.assign B c33 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c33 (?nAX_g8213_0_0_34))))) (?nAX_g8213_0_0_35)) ?_)) fun (hcase_1:c32) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c4) (Classical.em c8) (fun (hcase_2:c8) => @Exists.intro Env c3 c11 (@And.intro (Run B read σ c11 ((18:Nat))) (c2 c11) (RunStep.mono B read σ c11 (c46 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c11 c45 c20 (RunStep.ite_false B c14 c22 c26 σ c6 c44 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_37)) hcase) (RunStep.ite_false B c24 c25 c22 σ c6 c16 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_40)) (?nAX_g8213_0_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_42))))) (RunStep.ite_true B c14 c27 c28 c6 c11 c19 (RunStep.cond_eq_true B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_43)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_44)) hcase_2) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_45))))) (?nAX_g8213_0_0_46)) ?_)) fun (hcase_2:c9) => @Exists.intro Env c3 c29 (@And.intro (Run B read σ c29 ((18:Nat))) (c2 c29) (RunStep.mono B read σ c29 (c46 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c29 c45 c17 (RunStep.ite_false B c14 c22 c26 σ c6 c44 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_48)) hcase) (RunStep.ite_false B c24 c25 c22 σ c6 c16 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_51)) (?nAX_g8213_0_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_53))))) (RunStep.ite_false B c14 c27 c28 c6 c29 c16 (RunStep.cond_eq_false B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_54)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_55)) hcase_2) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c6 (?nAX_g8213_0_0_56))))) (?nAX_g8213_0_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Value,value,Env.setVar]
    all_goals omega
  · by_cases ht:q < N+2
    · (expose_names;
        (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Env→ Prop:=(fun (x τ:Env) => Value B (value N q) τ) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c6:Nat:=Env.vars c5 "fill.i"; let c7:Prop:= @Eq Nat c6 ((1:Nat)); let c8:Prop:=Not c7; let c9:Nat→ Env:=Env.setVar c5 "coefficient.negative"; let c10:Env:=c9 ((1:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat:=c14 c15; let c17:Nat→ Nat:=c11 c16; let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c19:Nat:=c14 c18; let c20:Com→ Com→ Com:=Com.ite c13; let c21:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c22:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c23:Cond:=Cond.lt (Expr.var "fill.i") c22; let c24:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c25:Com:=Com.ite c23 c24 c21; let c26:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c28:Env:=c9 ((0:Nat)); let c29:Nat:=c11 (Env.vars σ "catalog.count") ((2:Nat)); let c30:Prop:=Nat.lt (Env.vars σ "fill.i") c29; let c31:Prop:=Not c30; let c32:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c33:Nat:=Env.vars c32 "fill.i"; let c34:Prop:= @Eq Nat c33 ((1:Nat)); let c35:Prop:=Not c34; let c36:Nat→ Env:=Env.setVar c32 "coefficient.negative"; let c37:Env:=c36 ((1:Nat)); let c38:Nat→ Nat:=c11 (c12 (Cond.size c23)); let c39:Nat:=c38 c18; let c40:Nat:=c14 c39; let c41:Nat→ Nat:=c11 c40; let c42:Env:=c36 ((0:Nat)); let c43:Nat:=c38 c15; let c44:Nat:=c14 c43; let c45:Nat→ Nat:=c11 c44; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => c2) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_1:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c17 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c16 c19 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_2)))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_3)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_4)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_5))))) (?nAX_g8213_1_0_6)) ?_)) fun (hcase_1:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c17 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c16 c16 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_9)))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_10)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_11)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_1_0_12))))) (?nAX_g8213_1_0_13)) ?_)) fun (hcase:c4) => @Or.casesOn c30 c31 (fun (x:Or c30 c31) => c2) (Classical.em c30) (fun (hcase_1:c30) => @Or.casesOn c34 c35 (fun (x:Or c34 c35) => c2) (Classical.em c34) (fun (hcase_2:c34) => @Exists.intro Env c1 c37 (@And.intro (Run B read σ c37 ((18:Nat))) (c0 c37) (RunStep.mono B read σ c37 (c41 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c37 c40 c19 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_15)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_18)) (?nAX_g8213_1_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_20))))) (RunStep.ite_true B c13 c26 c27 c32 c37 c18 (RunStep.cond_eq_true B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_1_0_21)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_22)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_23))))) (?nAX_g8213_1_0_24)) ?_)) fun (hcase_2:c35) => @Exists.intro Env c1 c42 (@And.intro (Run B read σ c42 ((18:Nat))) (c0 c42) (RunStep.mono B read σ c42 (c41 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c42 c40 c16 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_26)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_29)) (?nAX_g8213_1_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_31))))) (RunStep.ite_false B c13 c26 c27 c32 c42 c15 (RunStep.cond_eq_false B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_1_0_32)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_33)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c32 (?nAX_g8213_1_0_34))))) (?nAX_g8213_1_0_35)) ?_)) fun (hcase_1:c31) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_2:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c45 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c44 c19 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_37)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_40)) (?nAX_g8213_1_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_42))))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_43)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_44)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_45))))) (?nAX_g8213_1_0_46)) ?_)) fun (hcase_2:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c45 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c44 c16 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_48)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_51)) (?nAX_g8213_1_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_53))))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_54)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_55)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_1_0_56))))) (?nAX_g8213_1_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega
    · (expose_names;
        (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Env→ Prop:=(fun (x τ:Env) => Value B (value N q) τ) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c6:Nat:=Env.vars c5 "fill.i"; let c7:Prop:= @Eq Nat c6 ((1:Nat)); let c8:Prop:=Not c7; let c9:Nat→ Env:=Env.setVar c5 "coefficient.negative"; let c10:Env:=c9 ((1:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat:=c14 c15; let c17:Nat→ Nat:=c11 c16; let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c19:Nat:=c14 c18; let c20:Com→ Com→ Com:=Com.ite c13; let c21:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c22:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c23:Cond:=Cond.lt (Expr.var "fill.i") c22; let c24:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c25:Com:=Com.ite c23 c24 c21; let c26:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c28:Env:=c9 ((0:Nat)); let c29:Nat:=c11 (Env.vars σ "catalog.count") ((2:Nat)); let c30:Prop:=Nat.lt (Env.vars σ "fill.i") c29; let c31:Prop:=Not c30; let c32:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c33:Nat:=Env.vars c32 "fill.i"; let c34:Prop:= @Eq Nat c33 ((1:Nat)); let c35:Prop:=Not c34; let c36:Nat→ Env:=Env.setVar c32 "coefficient.negative"; let c37:Env:=c36 ((1:Nat)); let c38:Nat→ Nat:=c11 (c12 (Cond.size c23)); let c39:Nat:=c38 c18; let c40:Nat:=c14 c39; let c41:Nat→ Nat:=c11 c40; let c42:Env:=c36 ((0:Nat)); let c43:Nat:=c38 c15; let c44:Nat:=c14 c43; let c45:Nat→ Nat:=c11 c44; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => c2) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_1:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c17 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c16 c19 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_2)))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_3)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_4)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_5))))) (?nAX_g8213_2_0_6)) ?_)) fun (hcase_1:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c17 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c16 c16 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_9)))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_10)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_11)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_2_0_12))))) (?nAX_g8213_2_0_13)) ?_)) fun (hcase:c4) => @Or.casesOn c30 c31 (fun (x:Or c30 c31) => c2) (Classical.em c30) (fun (hcase_1:c30) => @Or.casesOn c34 c35 (fun (x:Or c34 c35) => c2) (Classical.em c34) (fun (hcase_2:c34) => @Exists.intro Env c1 c37 (@And.intro (Run B read σ c37 ((18:Nat))) (c0 c37) (RunStep.mono B read σ c37 (c41 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c37 c40 c19 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_15)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_18)) (?nAX_g8213_2_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_20))))) (RunStep.ite_true B c13 c26 c27 c32 c37 c18 (RunStep.cond_eq_true B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_2_0_21)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_22)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_23))))) (?nAX_g8213_2_0_24)) ?_)) fun (hcase_2:c35) => @Exists.intro Env c1 c42 (@And.intro (Run B read σ c42 ((18:Nat))) (c0 c42) (RunStep.mono B read σ c42 (c41 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c42 c40 c16 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_26)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_29)) (?nAX_g8213_2_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_31))))) (RunStep.ite_false B c13 c26 c27 c32 c42 c15 (RunStep.cond_eq_false B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_2_0_32)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_33)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c32 (?nAX_g8213_2_0_34))))) (?nAX_g8213_2_0_35)) ?_)) fun (hcase_1:c31) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_2:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c45 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c44 c19 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_37)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_40)) (?nAX_g8213_2_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_42))))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_43)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_44)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_45))))) (?nAX_g8213_2_0_46)) ?_)) fun (hcase_2:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c45 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c44 c16 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_48)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_51)) (?nAX_g8213_2_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_53))))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_54)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_55)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_2_0_56))))) (?nAX_g8213_2_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega

end Lax263307Proofs.NativeMomentVectors

end

theorem solution:∀ (B N q:Nat),
  Nat.lt
      (Nat.add (Nat.add q N)
        ((4:Nat)))
      B→
    Lax808846Proofs.Reasoning.Spec B
      (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "fill.i") q) (@Eq Nat (σ.vars "catalog.count") N))
      Lax263307Proofs.NativeMomentVectors.read
      (fun (x τ:Lax808846Proofs.Imp.Env) =>
        Lax263307Proofs.NativeMomentProduce.Value B (Lax263307Proofs.NativeMomentVectors.value N q) τ)
      ((18:Nat)):= @Lax263307Proofs.NativeMomentVectors.read_spec
