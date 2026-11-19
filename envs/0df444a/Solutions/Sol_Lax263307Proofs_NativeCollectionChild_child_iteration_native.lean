-- Prove2me | solution 1 for Lax263307Proofs.NativeCollectionChild.child_iteration_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:03:30.592967+00:00
-- url     : https://prove2.me/submissions/3e6f0a69-89d1-4c44-be38-4d62d1038a69

import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.Int.NatAbs
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

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

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

@[simp] theorem Com.wvars_skip:Com.skip.wvars=[]:=by simp [Com.wvars]

@[simp] theorem Com.warrs_skip:Com.skip.warrs=[]:=by simp [Com.warrs]

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

namespace Lax263307Proofs.NativeIntegerEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def sign (p q:ℕ):ℕ:=if p< q then 1 else 0

def magnitude (p q:ℕ):ℕ:=if p< q then q-p else p-q

theorem sign_le (p q:ℕ):sign p q≤1:=by unfold sign; split_ifs <;> omega

theorem magnitude_bound (p q:ℕ):magnitude p q≤ max p q:=by unfold magnitude; split_ifs <;> omega

theorem encoding (p q:ℕ):encodeRational ((p:ℚ)-q)=[sign p q,magnitude p q,1]:=by
  have he:(p:ℚ)-q=(((p:ℤ)-(q:ℤ):ℤ):ℚ):=by simp
  rw [he,encodeRational]
  simp only [Rat.num_intCast,Rat.den_intCast]
  have hsg:((p:ℤ)-(q:ℤ)<0)↔ p< q:=by omega
  simp only [hsg,sign,magnitude]
  by_cases h:p< q
  · simp only [if_pos h,Int.natAbs_natCast_sub_natCast_of_le h.le]
  · simp only [if_neg h,Int.natAbs_natCast_sub_natCast_of_ge (by omega:q≤ p)]

theorem normalize_spec (B p q:ℕ) (h1:1< B) (hp:p< B) (hq:q< B):
    Spec B (fun σ => σ.vars "coefficient.positive"=p∧ σ.vars "coefficient.negative"=q) normalize
      (fun _ τ => τ.vars "coefficient.sign"=sign p q∧ τ.vars "coefficient.magnitude"=magnitude p q) 10:=by
  by_cases h:p< q
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "coefficient.sign") (sign p q)) (@Eq Nat (Env.vars τ "coefficient.magnitude") (magnitude p q))) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B normalize σ σ' ((10:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:=Nat.lt (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative"); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.sign" ((1:Nat)); let c6:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c7:String→ Nat:=Env.vars c5; let c8:Nat:=c7 "coefficient.negative"; let c9:Nat:=c7 "coefficient.positive"; let c10:Nat:=c6 c8 c9; let c11:Env:=Env.setVar c5 "coefficient.magnitude" c10; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat→ Nat:=c12 (c13 (Cond.size (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")))); let c15:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive"))); let c17:Nat:=c12 c15 c16; let c18:Com:=Com.assign "coefficient.sign" (Expr.lit ((1:Nat))); let c19:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")); let c20:Com:=Com.seq c18 c19; let c21:Com:=Com.assign "coefficient.sign" (Expr.lit ((0:Nat))); let c22:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")); let c23:Com:=Com.seq c21 c22; let c24:String→ Nat:=Env.vars c11; let c25:Env:=Env.setVar σ "coefficient.sign" ((0:Nat)); let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "coefficient.positive"; let c28:Nat:=c26 "coefficient.negative"; let c29:Nat:=c6 c27 c28; let c30:Env:=Env.setVar c25 "coefficient.magnitude" c29; let c31:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c32:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative"))); let c33:Nat:=c12 c31 c32; let c34:String→ Nat:=Env.vars c30; @And.casesOn (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q) (fun (x:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => c2) a fun (left:@Eq Nat (Env.vars σ "coefficient.positive") p) (right:@Eq Nat (Env.vars σ "coefficient.negative") q) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Exists.intro Env c1 c11 (@And.intro (Run B normalize σ c11 ((10:Nat))) (c0 c11) (RunStep.mono B normalize σ c11 (c14 c17) ((10:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c11 c17 (RunStep.cond_lt_true B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_0_0_0)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_0_0_1)) hcase) (RunStep.seq B c18 c19 σ c5 c11 c15 c16 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.assign B c5 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")) c10 (RunStep.eval_sub B c5 (Expr.var "coefficient.negative") (Expr.var "coefficient.positive") c8 c9 (RunStep.eval_var B c5 "coefficient.negative" (?nAX_g8141_0_0_2)) (RunStep.eval_var B c5 "coefficient.positive" (?nAX_g8141_0_0_3)) (?nAX_g8141_0_0_4))))) (?nAX_g8141_0_0_5)) ?_)) fun (hcase:c4) => @Exists.intro Env c1 c30 (@And.intro (Run B normalize σ c30 ((10:Nat))) (c0 c30) (RunStep.mono B normalize σ c30 (c14 c33) ((10:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c30 c33 (RunStep.cond_lt_false B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_0_0_6)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_0_0_7)) hcase) (RunStep.seq B c21 c22 σ c25 c30 c31 c32 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8141_0_0_8))) (RunStep.assign B c25 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c29 (RunStep.eval_sub B c25 (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") c27 c28 (RunStep.eval_var B c25 "coefficient.positive" (?nAX_g8141_0_0_9)) (RunStep.eval_var B c25 "coefficient.negative" (?nAX_g8141_0_0_10)) (?nAX_g8141_0_0_11))))) (?nAX_g8141_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8141_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,sign,magnitude]
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "coefficient.sign") (sign p q)) (@Eq Nat (Env.vars τ "coefficient.magnitude") (magnitude p q))) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B normalize σ σ' ((10:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:=Nat.lt (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative"); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.sign" ((1:Nat)); let c6:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c7:String→ Nat:=Env.vars c5; let c8:Nat:=c7 "coefficient.negative"; let c9:Nat:=c7 "coefficient.positive"; let c10:Nat:=c6 c8 c9; let c11:Env:=Env.setVar c5 "coefficient.magnitude" c10; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat→ Nat:=c12 (c13 (Cond.size (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")))); let c15:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive"))); let c17:Nat:=c12 c15 c16; let c18:Com:=Com.assign "coefficient.sign" (Expr.lit ((1:Nat))); let c19:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")); let c20:Com:=Com.seq c18 c19; let c21:Com:=Com.assign "coefficient.sign" (Expr.lit ((0:Nat))); let c22:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")); let c23:Com:=Com.seq c21 c22; let c24:String→ Nat:=Env.vars c11; let c25:Env:=Env.setVar σ "coefficient.sign" ((0:Nat)); let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "coefficient.positive"; let c28:Nat:=c26 "coefficient.negative"; let c29:Nat:=c6 c27 c28; let c30:Env:=Env.setVar c25 "coefficient.magnitude" c29; let c31:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c32:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative"))); let c33:Nat:=c12 c31 c32; let c34:String→ Nat:=Env.vars c30; @And.casesOn (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q) (fun (x:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => c2) a fun (left:@Eq Nat (Env.vars σ "coefficient.positive") p) (right:@Eq Nat (Env.vars σ "coefficient.negative") q) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Exists.intro Env c1 c11 (@And.intro (Run B normalize σ c11 ((10:Nat))) (c0 c11) (RunStep.mono B normalize σ c11 (c14 c17) ((10:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c11 c17 (RunStep.cond_lt_true B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_1_0_0)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_1_0_1)) hcase) (RunStep.seq B c18 c19 σ c5 c11 c15 c16 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.assign B c5 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")) c10 (RunStep.eval_sub B c5 (Expr.var "coefficient.negative") (Expr.var "coefficient.positive") c8 c9 (RunStep.eval_var B c5 "coefficient.negative" (?nAX_g8141_1_0_2)) (RunStep.eval_var B c5 "coefficient.positive" (?nAX_g8141_1_0_3)) (?nAX_g8141_1_0_4))))) (?nAX_g8141_1_0_5)) ?_)) fun (hcase:c4) => @Exists.intro Env c1 c30 (@And.intro (Run B normalize σ c30 ((10:Nat))) (c0 c30) (RunStep.mono B normalize σ c30 (c14 c33) ((10:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c30 c33 (RunStep.cond_lt_false B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_1_0_6)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_1_0_7)) hcase) (RunStep.seq B c21 c22 σ c25 c30 c31 c32 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8141_1_0_8))) (RunStep.assign B c25 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c29 (RunStep.eval_sub B c25 (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") c27 c28 (RunStep.eval_var B c25 "coefficient.positive" (?nAX_g8141_1_0_9)) (RunStep.eval_var B c25 "coefficient.negative" (?nAX_g8141_1_0_10)) (?nAX_g8141_1_0_11))))) (?nAX_g8141_1_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8141_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,sign,magnitude]

theorem append_spec (B p q:ℕ) (front:List ℕ) (h1:1< B) (hp:p< B) (hq:q< B) (hlen:front.length+3< B):
    Spec B (fun σ => σ.vars "coefficient.positive"=p∧ σ.vars "coefficient.negative"=q∧
      Prefix front "lp.input" σ∧ σ.vars "lp.length"=front.length∧ front.length+3≤(σ.arrs "lp.input").length)
      append (fun _ τ => Prefix (front++encodeRational ((p:ℚ)-q)) "lp.input" τ∧ τ.vars "lp.length"=front.length+3) 31:=by
  rintro σ ⟨hpos,hneg,hprefix,hcount,hroom⟩
  obtain ⟨ν,r1,p1⟩:=normalize_spec B p q h1 hp hq σ ⟨hpos,hneg⟩
  have hs:sign p q< B:=(sign_le p q).trans_lt h1
  have hm:magnitude p q< B:=(magnitude_bound p q).trans_lt (max_lt hp hq)
  obtain ⟨μ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" front (sign p q)
    (.var "coefficient.sign") h1 (by omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hprefix,
      (r1.frame_var "lp.length" (by decide)).trans hcount,
      by rw [Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hs⟩⟩
  have hlen1:(front++[sign p q]).length=front.length+1:=by simp
  have hmag:μ.vars "coefficient.magnitude"=magnitude p q:=(r2.frame_var "coefficient.magnitude" (by decide)).trans p1.2
  obtain ⟨ξ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" (front++[sign p q]) (magnitude p q)
    (.var "coefficient.magnitude") h1 (by rw [hlen1]; omega) μ
    ⟨p2.1,by rw [hlen1]; exact p2.2,by rw [hlen1,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨hmag.symm,hmag ▸ hm⟩⟩
  have hlen2:((front++[sign p q])++[magnitude p q]).length=front.length+2:=by simp
  obtain ⟨τ,r4,p4⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" ((front++[sign p q])++[magnitude p q]) 1
    (.lit 1) h1 (by rw [hlen2]; omega) ξ
    ⟨p3.1,by simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using p3.2,
      by rw [hlen2,Lax455465Proofs.RamFrames.run_array_length r3,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      evalB_lit h1⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp [Expr.size]),?_,?_⟩
  · simpa only [encoding,List.append_assoc,List.cons_append,List.nil_append] using p4.1
  · simpa only [hlen2,Nat.add_assoc] using p4.2

end Lax263307Proofs.NativeIntegerEncoding

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

theorem words_append (xs ys:List ℚ):words (xs++ys)=words xs++words ys:=List.flatMap_append

theorem words_take_succ (xs:List ℚ) (i:ℕ) (hi:i< xs.length):
    words (xs.take (i+1))=words (xs.take i)++encodeRational xs[i]:=by
  rw [List.take_succ_eq_append_getElem hi,words_append]
  simp [words]

def Invariant (P:Env→ Prop) (xs:List ℚ) (front:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "fill.i"≤ xs.length∧
  σ.vars "lp.length"=front.length+3*σ.vars "fill.i" ∧
  front.length+3*xs.length≤(σ.arrs "lp.input").length∧
  Prefix (front++words (xs.take (σ.vars "fill.i"))) "lp.input" σ

theorem command_spec (B:ℕ) (xs:List ℚ) (front:List ℕ) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:front.length+3*xs.length+2< B)
    (hri:"fill.i"∉read.wvars) (hrl:"fill.length"∉read.wvars)
    (hrlen:"lp.length"∉read.wvars) (hra:"lp.input"∉read.warrs)
    (hinit:∀ σ,P σ→ P (σ.setVar "fill.i" 0))
    (hwrite:∀ σ τ,Run B NativeIntegerEncoding.append σ τ 31→ P σ→ P τ)
    (hadvance:∀ σ τ,Run B advance σ τ 4→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ∧ τ.vars "coefficient.positive"< B∧ τ.vars "coefficient.negative"< B∧
        ((τ.vars "coefficient.positive" :ℕ):ℚ)-τ.vars "coefficient.negative"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "lp.length"=front.length∧
      front.length+3*xs.length≤(σ.arrs "lp.input").length∧ Prefix front "lp.input" σ)
      (command read) (fun _ τ => P τ∧ τ.vars "lp.length"=front.length+3*xs.length∧ Prefix (front++words xs) "lp.input" τ)
      ((K+39)*xs.length+6):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant P xs front σ∧ σ.vars "fill.i"< xs.length)
      (body read) (fun σ τ => Invariant P xs front τ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+35):=by
    rintro σ ⟨⟨hP,hlen,hle,hcount,hroom,hprefix⟩,hlt⟩
    let i:=σ.vars "fill.i"
    have htake:(xs.take i).length=i:=by rw [List.length_take,Nat.min_eq_left hle]
    have hfront:(front++words (xs.take i)).length=front.length+3*i:=by rw [List.length_append,words_length,htake]
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hP,rfl⟩
    obtain ⟨μ,r2,p2⟩:=NativeIntegerEncoding.append_spec B (ν.vars "coefficient.positive") (ν.vars "coefficient.negative")
      (front++words (xs.take i)) h1 p1.2.1 p1.2.2.1 (by rw [hfront]; omega) ν
      ⟨rfl,rfl,by simpa only [Prefix,r1.frame_arr "lp.input" hra] using hprefix,
        by rw [hfront]; exact (r1.frame_var "lp.length" hrlen).trans hcount,
        by rw [hfront,Lax455465Proofs.RamFrames.run_array_length r1]; omega⟩
    have hPμ:=hwrite ν μ r2 p1.1
    have hiμ:μ.vars "fill.i"=i:=
      (r2.frame_var "fill.i" (by decide)).trans (r1.frame_var "fill.i" hri)
    let τ:=μ.setVar "fill.i" (i+1)
    have r3:Run B advance μ τ 4:=Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega)⟩) (evalB_lit h1) (by change i+1< B; omega))
    have rr:=r1.seq (r2.seq r3)
    have ht:τ.vars "fill.i"=i+1:=by simp [τ]
    refine ⟨τ,rr.mono (by omega),⟨hadvance μ τ r3 hPμ,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
    · exact ((r2.seq r3).frame_var "fill.length" (by decide)).trans ((r1.frame_var "fill.length" hrl).trans hlen)
    · rw [ht]
      have hc:=(r3.frame_var "lp.length" (by decide)).trans p2.2
      rw [hfront] at hc
      omega
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,words_take_succ xs i hlt,←List.append_assoc,←p1.2.2.2]
      simpa only [Prefix,r3.frame_arr "lp.input" (by decide)] using p2.1
  have hloop:=Spec.forRangeZero "fill.i" "fill.length" (Invariant P xs front) xs.length (K+35)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hcount,hroom,hprefix⟩
  have hi:Invariant P xs front (σ.setVar "fill.i" 0):=by
    refine ⟨hinit σ hP,?_,by simp,?_,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.mul_zero,Nat.add_zero] using hcount
    · simpa only [vars_setVar,if_true,List.take_zero,words,List.flatMap_nil,List.append_nil,Prefix,arrs_setVar] using hprefix
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_,?_⟩
  · simpa only [p.2] using p.1.2.2.2.1
  · simpa only [p.2,List.take_length] using p.1.2.2.2.2.2

end Lax263307Proofs.NativeRationalTabulate

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

namespace Lax263307Proofs.NativeProgramCache

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem copy_spec (B:ℕ) (source target lengthVar:String) (xs:List ℕ)
    (hne:source≠target) (hB:xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars lengthVar=xs.length∧ xs.length≤(σ.arrs target).length)
      (copy source target lengthVar)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (16*xs.length+10):=by
  rintro σ ⟨hp,hlen,hroom⟩
  let ν:=σ.setVar "fill.length" xs.length
  have r1:Run B (.assign "fill.length" (.var lengthVar)) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega)⟩)
  let μ:=ν.setVar "slice.start" 0
  have r2:Run B (.assign "slice.start" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (show 0< B by omega))
  obtain ⟨τ,r3,p3⟩:=NativeSlice.command_spec B source target [] xs [] hne (by simp; omega) hv μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,(r1.seq r2).frame_arr source (by simp [Com.warrs])] using hp,
      by rfl⟩,by simp [μ,ν],by rw [RamFrames.run_array_length (r1.seq r2)]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    by simpa only [NativeSlice.Context,List.nil_append,List.append_nil] using p3.1.1,p3.2⟩

end Lax263307Proofs.NativeProgramCache

end

section

namespace Lax263307Proofs.NativeMatrixOrder

theorem row_pair (n:ℕ) (u v:Fin n):
    NativeBlowUp.row ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=u:=by
  have hn:0< n:=by have hu:=u.isLt; omega
  apply Fin.ext
  change (u.val*n+v.val)/n=u.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt,Nat.zero_add]

theorem col_pair (n:ℕ) (u v:Fin n):
    NativeBlowUp.col ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=v:=by
  apply Fin.ext
  simp [NativeBlowUp.col,Nat.mod_eq_of_lt v.isLt]

theorem flatten {α:Type*} (n:ℕ) (f:Fin n→ Fin n→ α):
    List.ofFn (fun i:Fin (n*n) => f (NativeBlowUp.row i) (NativeBlowUp.col i))=
      (List.ofFn fun u => List.ofFn (f u)).flatten:=by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  simp only [row_pair,col_pair]

end Lax263307Proofs.NativeMatrixOrder

end

section

namespace Lax263307Proofs.NativeRoundedQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch

theorem vector_length {n:ℕ} (v:Fin n→ ℚ):(encodeVector v).length=3*n:=by
  simp [encodeVector,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const] <;> ring

end Lax263307Proofs.NativeRoundedQuery

end

section

namespace Lax263307Proofs.NativeArrayBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

theorem big_step {B K:ℕ} {c:Com} {σ τ:Env} (rr:BigStepB B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hb
  | assign _ => exact hb
  | store hi he hj =>
    intro a z hz
    simp only [arrs_setArr] at hz
    split_ifs at hz with h
    · obtain hz|rfl:=List.mem_or_eq_of_mem_set hz
      · exact hb _ _ hz
      · exact Expr.lt_of_evalB he
    · exact hb _ _ hz
  | seq _ _ ih ih' => exact ih' (ih hb)
  | ite_true _ _ ih => exact ih hb
  | ite_false _ _ ih => exact ih hb
  | while_true _ _ _ ih ih' => exact ih' (ih hb)
  | while_false _ => exact hb
  | read _ => exact hb
  | write _ => exact hb

theorem run {B K:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,h⟩:=rr
  exact big_step h hb

theorem prefix_words {B:ℕ} {σ:Env} {xs:List ℕ} {a:String} (hb:Bounded B σ)
    (hp:Prefix xs a σ):∀ z∈ xs,z < B:=by
  intro z hz
  obtain ⟨i,hi,hz⟩:=List.getElem_of_mem hz
  have he:=hp i hi
  rw [hz] at he
  exact hb a z (List.mem_of_getElem? he)

end Lax263307Proofs.NativeArrayBounds

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRestrictionRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

theorem frame {B n K:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ} {R:Finset (Fin n)} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hd:Data G x R σ)
    (ha:∀ s∈["restrict.vertices","search.graph","near.costs"],s∉c.warrs)
    (hv:∀ s∈["restrict.count","graph.n"],s∉c.wvars):Data G x R τ:=by
  refine ⟨?_,?_,?_,(rr.frame_var "restrict.count" (hv _ (by simp))).trans hd.count,
    (rr.frame_var "graph.n" (hv _ (by simp))).trans hd.order⟩
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" (ha _ (by simp))] using hd.labels
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp))] using hd.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp))] using hd.costs

theorem label_get {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ} {R:Finset (Fin n)} {σ:Env} (hd:Data G x R σ) (i:Fin R.card):
    (σ.arrs "restrict.vertices")[i.val]?=some (ComputedSeparators.label R i).val:=by
  simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
    hd.labels i.val (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using i.isLt)

theorem graph_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i j:Fin R.card) (hB:n*n+n+3< B):
    Spec B (fun σ => Data G x R σ∧ σ.vars "restrict.row"=i.val∧ σ.vars "restrict.col"=j.val)
      graphRead (fun _ τ => Data G x R τ∧
        τ.vars "restrict.edge"=if (ComputedSeparators.restriction G R).Adj i j then 1 else 0) 13:=by
  let u:=ComputedSeparators.label R i
  let v:=ComputedSeparators.label R j
  have hiB:i.val< B:=i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have hjB:j.val< B:=j.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB:u.val< B:=u.isLt.trans (by omega)
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hind:u.val*n+v.val< n*n:=by nlinarith [u.isLt,v.isLt]
  rintro σ ⟨hd,hi,hj⟩
  let ν:=σ.setVar "restrict.u" u.val
  have r1:Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ:=ν.setVar "restrict.v" v.val
  have r2:Run B (.assign "restrict.v" (.get "restrict.vertices" (.var "restrict.col"))) ν μ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using
      (show j.val=σ.vars "restrict.col" ∧ σ.vars "restrict.col"< B from ⟨hj.symm,hj ▸ hjB⟩)) (label_get hd j) hvB)
  have hget:=NativeBlowUp.matrix_coordinate (fun a b => if G.Adj a b then 1 else 0) u v
  change (NativeWeightReduction.adjacency G)[u.val*n+v.val]?=some (if G.Adj u v then 1 else 0) at hget
  have hlen:u.val*n+v.val<(NativeWeightReduction.adjacency G).length:=by
    rw [NativeWeightReduction.adjacency_length]; exact hind
  rw [List.getElem?_eq_getElem hlen] at hget
  have hg:=(hd.graph _ hlen).trans hget
  let bit:ℕ:=if G.Adj u v then 1 else 0
  let τ:=μ.setVar "restrict.edge" bit
  have hgμ:(μ.arrs "search.graph")[u.val*n+v.val]?=some bit:=hg
  have r3:Run B (.assign "restrict.edge" (.get "search.graph" (.add (.mul (.var "restrict.u") (.var "graph.n")) (.var "restrict.v")))) μ τ 7:=by
    apply Run.assign
    apply evalB_get _ hgμ (by dsimp [bit]; split_ifs <;> omega)
    apply evalB_bin (op:=.add) _ _ (hind.trans (by omega))
    · apply evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; simp [μ,ν,huB])
        (by rw [evalB_var_iff]; simp only [μ,ν,vars_setVar,String.reduceEq,if_false]; exact ⟨hd.order.symm,hd.order ▸ (by omega:n< B)⟩)
        (by change u.val*n< B; nlinarith only [hind,hB])
    · rw [evalB_var_iff]
      simp [μ,hvB]
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simp [τ,bit,u,v,ComputedSeparators.restriction]⟩

end Lax263307Proofs.NativeRestrictionRead

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

namespace Lax263307Proofs.NativeSetMasks

open NativeMasks

theorem outside {n:ℕ} (A:Finset (Fin n)) (j:ℕ) (hj:n≤ j):(mask A).testBit j=false:=by
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro h
  obtain ⟨v,hv,hvj⟩:=Finset.mem_image.mp h
  have hh:=v.isLt
  omega

theorem union {n:ℕ} (A C:Finset (Fin n)):mask (A∪C)=Nat.lor (mask A) (mask C):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A∪C)).testBit j=((mask A)|||(mask C)).testBit j
  rw [Nat.testBit_or]
  by_cases hj:j< n
  · change (mask (A∪C)).testBit (⟨j,hj⟩:Fin n).val=_
    rw [mask_member (A∪C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA:(⟨j,hj⟩:Fin n)∈A <;> by_cases hC:(⟨j,hj⟩:Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.or_false]

end Lax263307Proofs.NativeSetMasks

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks

def hits {n:ℕ} (A C J:Finset (Fin n)):Finset (Fin n):=
  C.filter fun v => insert v A=J

theorem hits_card {n:ℕ} (A C J:Finset (Fin n)):
    ((hits A C J).card:ℤ)=∑ v∈ C,if insert v A=J then 1 else 0:=by
  simp only [hits,Finset.card_filter]
  push_cast
  rfl

def Context {n:ℕ} (A C J:Finset (Fin n)) (u:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "conditioning.choice"=mask A∧
  σ.vars "component.mask"=mask C∧ σ.vars "cut.column"=mask J∧
  σ.vars "component.target"=u

theorem frame {n B K:ℕ} (A C J:Finset (Fin n)) (u:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"conditioning.choice"∉c.wvars)
    (h2:"component.mask"∉c.wvars) (h3:"cut.column"∉c.wvars)
    (h4:"component.target"∉c.wvars) (h:Context A C J u σ):Context A C J u τ:=
  ⟨(rr.frame_var _ h0).trans h.1,(rr.frame_var _ h1).trans h.2.1,
    (rr.frame_var _ h2).trans h.2.2.1,(rr.frame_var _ h3).trans h.2.2.2.1,
    (rr.frame_var _ h4).trans h.2.2.2.2⟩

def Invariant {n:ℕ} (A C J:Finset (Fin n)) (u:ℕ) (σ:Env):Prop:=
  Context A C J u σ∧ σ.vars "cut.vertex"≤ n∧
  σ.vars "coefficient.positive"=(initialSet (hits A C J) (σ.vars "cut.vertex")).card

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem step_spec {n:ℕ} (B:ℕ) (A C J:Finset (Fin n)) (u:ℕ)
    (hB:n+u+10< B) (hm:2^n< B):
    Spec B (fun σ => Invariant A C J u σ∧ σ.vars "cut.vertex"< n) step
      (fun σ τ => Invariant A C J u τ∧ τ.vars "cut.vertex"=σ.vars "cut.vertex"+1) 24:=by
  rintro σ ⟨⟨hc,hle,hcount⟩,hlt⟩
  let i:=σ.vars "cut.vertex"
  let v:Fin n:= ⟨i,hlt⟩
  let count:=(initialSet (hits A C J) i).card
  let bit:ℕ:=if v∈C then 1 else 0
  have hiB:i< B:=by omega
  have hbitB:bit< B:=by dsimp [bit]; split_ifs <;> omega
  have hCB:mask C< B:=(mask_bound C).trans hm
  have hAB:mask A< B:=(mask_bound A).trans hm
  have hJB:mask J< B:=(mask_bound J).trans hm
  have hIB:mask (insert v A)< B:=(mask_bound _).trans hm
  have hpB:2^i< B:=(Nat.pow_le_pow_right (by decide) hle).trans_lt hm
  have hbit:(Expr.and (.shiftr (.var "component.mask") (.var "cut.vertex")) (.lit 1)).evalB B σ=some bit:=by
    have hh:=evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr) (value hc.2.2.1 hCB) (evalB_var hiB)
        ((Nat.div_le_self _ _).trans_lt hCB)) (evalB_lit (show 1< B by omega))
      (by change Nat.land (mask C/2^i) 1< B; rw [NativeMaskUnpack.bit_value C v]; exact hbitB)
    exact hh.trans (congrArg some (NativeMaskUnpack.bit_value C v))
  have hs:selected.evalB B σ=some (decide (v∈C)):=by
    have hh:=evalB_condEq hbit (evalB_lit (show 1< B by omega))
    by_cases hv:v∈C <;> simpa [selected,Bool.beq_eq_decide_eq,bit,hv] using hh
  have hins:(Expr.or (.var "conditioning.choice") (.shiftl (.lit 1) (.var "cut.vertex"))).evalB B σ=some (mask (insert v A)):=by
    have hh:=evalB_bin (op:=.or) (value hc.2.1 hAB)
      (evalB_bin (op:=.shiftl) (evalB_lit (show 1< B by omega)) (evalB_var hiB)
        (by change 1*2^i< B; simpa only [one_mul] using hpB))
      (by change Nat.lor (mask A) (1*2^i)< B; simpa only [one_mul,mask_insert] using hIB)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,mask_insert] using hh
  have heq:sameColumn.evalB B σ=some (decide (insert v A=J)):=by
    have hh:=evalB_condEq hins (value hc.2.2.2.1 hJB)
    have hinj:mask (insert v A)=mask J↔ insert v A=J:=(mask_injective n).eq_iff
    simpa only [sameColumn,Bool.beq_eq_decide_eq,hinj] using hh
  have hnext:=NativeMaskUnpack.prefix_card_step (hits A C J) i hlt
  have hcountB:count+1< B:=by
    have hh:=NativeMaskUnpack.card_bound (initialSet (hits A C J) i)
    dsimp [count]
    omega
  obtain ⟨ν,rr,hpos⟩:∃ ν,Run B collect σ ν 20∧
      ν.vars "coefficient.positive"=(initialSet (hits A C J) (i+1)).card:=by
    by_cases hv:v∈C
    · by_cases he:insert v A=J
      · let ν:=σ.setVar "coefficient.positive" (count+1)
        have ri:Run B increment σ ν 4:=Run.assign (evalB_bin (op:=.add)
          (value hcount (by omega)) (evalB_lit (show 1< B by omega)) hcountB)
        have rr:=Run.ite_true (d:=Com.skip) (by simpa only [he,decide_true] using heq) ri
        have rr':=Run.ite_true (d:=Com.skip) (by simpa only [hv,decide_true] using hs) rr
        refine ⟨ν,rr'.mono (by simp [selected,sameColumn,Cond.size,Expr.size]),?_⟩
        rw [hnext]
        simp [ν,count,hits,hv,he,v]
      · have rr:=Run.ite_false (c:=increment) (by simpa only [he,decide_false] using heq) (Run.skip (σ:=σ))
        have rr':=Run.ite_true (d:=Com.skip) (by simpa only [hv,decide_true] using hs) rr
        refine ⟨σ,rr'.mono (by simp [selected,sameColumn,Cond.size,Expr.size]),?_⟩
        rw [hnext]
        change σ.vars "coefficient.positive"=count+(if v∈hits A C J then 1 else 0)
        simp only [hits,Finset.mem_filter,he,and_false,if_false,Nat.add_zero]
        exact hcount
    · have rr:=Run.ite_false (c:=Com.ite sameColumn increment Com.skip)
        (by simpa only [hv,decide_false] using hs) (Run.skip (σ:=σ))
      refine ⟨σ,rr.mono (by simp [selected,Cond.size,Expr.size]),?_⟩
      rw [hnext]
      change σ.vars "coefficient.positive"=count+(if v∈hits A C J then 1 else 0)
      simp only [hits,Finset.mem_filter,hv,false_and,if_false,Nat.add_zero]
      exact hcount
  have hiν:ν.vars "cut.vertex"=i:=rr.frame_var _ (by decide)
  let τ:=ν.setVar "cut.vertex" (i+1)
  have r2:Run B (.assign "cut.vertex" (.add (.var "cut.vertex") (.lit 1))) ν τ 4:=
    Run.assign (evalB_bin (op:=.add) (value hiν hiB) (evalB_lit (show 1< B by omega))
      (by change i+1< B; omega))
  have total:=rr.seq r2
  have ht:τ.vars "cut.vertex"=i+1:=by simp [τ]
  refine ⟨τ,total,⟨frame A C J u total (by decide) (by decide) (by decide) (by decide) (by decide) hc,
    by rw [ht]; omega,?_⟩,ht⟩
  rw [ht,r2.frame_var "coefficient.positive" (by decide)]
  exact hpos

theorem positive_spec {n:ℕ} (B:ℕ) (A C J:Finset (Fin n)) (u:ℕ)
    (hB:n+u+10< B) (hm:2^n< B):
    Spec B (Context A C J u) positive
      (fun _ τ => Context A C J u τ∧ τ.vars "coefficient.positive"=(hits A C J).card) (28*n+8):=by
  have hloop:=Spec.forRangeZero "cut.vertex" "graph.n" (Invariant A C J u) n 24 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (step_spec B A C J u hB hm)
  intro σ hc
  let ν:=σ.setVar "coefficient.positive" 0
  have r1:Run B (.assign "coefficient.positive" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (show 0< B by omega))
  have hi:Invariant A C J u (ν.setVar "cut.vertex" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa [Context,ν,Env.setVar] using hc
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,
    by simpa only [p2.2,prefix_full] using p2.1.2.2⟩

theorem command_spec {n r:ℕ} (B:ℕ) (A C:Finset (Fin n)) (J:Lax263307.LinearRelaxation.Coordinate n r)
    (u:ℕ) (hB:n+u+10< B) (hm:2^n< B):
    Spec B (Context A C J.val u) command
      (fun _ τ => Context A C J.val u τ∧ τ.vars "coefficient.positive"< B∧ τ.vars "coefficient.negative"< B∧
        ((τ.vars "coefficient.positive" :ℕ):ℚ)-τ.vars "coefficient.negative"=
          (Lax263307.ComponentCutEncoding.coefficient A C u J:ℚ)) (28*n+14):=by
  intro σ hc
  obtain ⟨ν,r1,p1⟩:=positive_spec B A C J.val u hB hm σ hc
  have hinj:mask A=mask J.val↔ A=J.val:=(mask_injective n).eq_iff
  have hn:Spec B (Context A C J.val u) negative
      (fun _ τ => τ.vars "coefficient.negative"=if A=J.val then u else 0) 6:=by
    intro ξ hd
    have haB:mask A< B:=(mask_bound A).trans hm
    have hjB:mask J.val< B:=(mask_bound J.val).trans hm
    have he:(Cond.eq (.var "conditioning.choice") (.var "cut.column")).evalB B ξ=
        some (decide (A=J.val)):=by
      have hh:=evalB_condEq (value hd.2.1 haB) (value hd.2.2.2.1 hjB)
      simpa only [Bool.beq_eq_decide_eq,hinj] using hh
    by_cases heq:A=J.val
    · let τ:=ξ.setVar "coefficient.negative" u
      have ri:Run B (.assign "coefficient.negative" (.var "component.target")) ξ τ 2:=
        Run.assign (value hd.2.2.2.2 (by omega))
      refine ⟨τ,(Run.ite_true (d:=Com.assign "coefficient.negative" (.lit 0))
        (by simpa only [heq,decide_true] using he) ri).mono (by simp [Cond.size,Expr.size]),?_⟩
      simp [τ,heq]
    · let τ:=ξ.setVar "coefficient.negative" 0
      have ri:Run B (.assign "coefficient.negative" (.lit 0)) ξ τ 2:=
        Run.assign (evalB_lit (show 0< B by omega))
      refine ⟨τ,(Run.ite_false (c:=Com.assign "coefficient.negative" (.var "component.target"))
        (by simpa only [heq,decide_false] using he) ri).mono (by simp [Cond.size,Expr.size]),?_⟩
      simp [τ,heq]
  obtain ⟨τ,r2,p2⟩:=hn ν p1.1
  have hp:τ.vars "coefficient.positive"=(hits A C J.val).card:=
    (r2.frame_var _ (by decide)).trans p1.2
  refine ⟨τ,r1.seq r2,frame A C J.val u r2 (by decide) (by decide) (by decide) (by decide) (by decide) p1.1,
    by rw [hp]; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega),
    by rw [p2]; split_ifs <;> omega,?_⟩
  rw [hp,p2,Lax263307.ComponentCutEncoding.coefficient,Int.cast_sub,←hits_card]
  split_ifs <;> simp

end Lax263307Proofs.NativeComponentCoefficient

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks NativeCatalogMetadata

def values {n:ℕ} (r:ℕ) (A C:Finset (Fin n)) (u:ℕ):List ℚ:=
  List.ofFn (RoundedOracleSearch.rationalNormal (normal (r:=r) A C u))

theorem cleared_integer {N:ℕ} (a:Fin N→ ℤ):
    RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal a)=a:=by
  funext i
  simp [RationalCutBuffer.integerNormal,RationalCutBuffer.denominator,RoundedOracleSearch.rationalNormal]

structure Data {n:ℕ} (r:ℕ) (A C:Finset (Fin n)) (u:ℕ) (σ:Env):Prop where
  order:σ.vars "graph.n"=n
  count:σ.vars "catalog.count"=N n r
  catalog:Prefix (NativeCatalog.words n r) "catalog.mask" σ
  conditioning:σ.vars "conditioning.choice"=mask A
  component:σ.vars "component.mask"=mask C
  target:σ.vars "component.target"=u

theorem frame {n B K r u:ℕ} {A C:Finset (Fin n)} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hd:Data r A C u σ)
    (h0:"graph.n"∉c.wvars) (h1:"catalog.count"∉c.wvars)
    (h2:"catalog.mask"∉c.warrs) (h3:"conditioning.choice"∉c.wvars)
    (h4:"component.mask"∉c.wvars) (h5:"component.target"∉c.wvars):Data r A C u τ:=by
  refine ⟨(rr.frame_var _ h0).trans hd.order,(rr.frame_var _ h1).trans hd.count,?_,
    (rr.frame_var _ h3).trans hd.conditioning,(rr.frame_var _ h4).trans hd.component,
    (rr.frame_var _ h5).trans hd.target⟩
  simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hd.catalog

theorem read_spec {n:ℕ} (B r:ℕ) (A C:Finset (Fin n)) (u:ℕ)
    (i:ℕ) (hi:i<(values r A C u).length) (hB:n+u+3*N n r+10< B) (hm:2^n< B):
    Spec B (fun σ => Data r A C u σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data r A C u τ∧ τ.vars "coefficient.positive"< B∧ τ.vars "coefficient.negative"< B∧
        ((τ.vars "coefficient.positive" :ℕ):ℚ)-τ.vars "coefficient.negative"=(values r A C u)[i])
      (28*n+17):=by
  let j:Fin (N n r):= ⟨i,by simpa only [values,List.length_ofFn] using hi⟩
  let J:=CoordinateCatalog.indexing n r j
  rintro σ ⟨hd,hidx⟩
  have hlen:(NativeCatalog.words n r).length=N n r:=by simp [NativeCatalog.words]
  have hic:i<(NativeCatalog.words n r).length:=by rw [hlen]; exact j.isLt
  have hget:=hd.catalog i hic
  have hw:(NativeCatalog.words n r)[i]=mask J.val:=by
    simp only [NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let ν:=σ.setVar "cut.column" (mask J.val)
  have r1:Run B (.assign "cut.column" (.get "catalog.mask" (.var "fill.i"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ (by have hj:=j.isLt; omega)⟩)
      hget ((mask_bound _).trans hm))
  have d1:=frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨τ,r2,p2⟩:=NativeComponentCoefficient.command_spec B A C J u (by omega) hm ν
    ⟨d1.order,d1.conditioning,d1.component,by simp [ν],d1.target⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    frame r2 d1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    p2.2.1,p2.2.2.1,by simpa only [values,List.getElem_ofFn,RoundedOracleSearch.rationalNormal,normal,MomentLP.encode] using p2.2.2.2⟩

theorem table_spec {n:ℕ} (B r:ℕ) (A C:Finset (Fin n)) (u:ℕ)
    (hB:n+u+3*N n r+10< B) (hm:2^n< B):
    Spec B (fun σ => Data r A C u σ∧ 3*N n r≤(σ.arrs "lp.input").length) table
      (fun _ τ => Data r A C u τ∧ τ.vars "lp.length"=3*N n r∧
        Prefix (NativeRoundedQuery.normal (normal (r:=r) A C u)) "lp.input" τ)
      ((28*n+56)*N n r+10):=by
  have hlen:(values r A C u).length=N n r:=List.length_ofFn
  have ht:=NativeRationalTabulate.command_spec B (values r A C u) [] (Data r A C u) read (28*n+17)
    (by simp only [List.length_nil,Nat.zero_add,hlen]; omega)
    (by decide) (by decide) (by decide) (by decide)
    (by
      intro σ hd
      exact ⟨by simpa using hd.order,by simpa using hd.count,hd.catalog,
        by simpa using hd.conditioning,by simpa using hd.component,by simpa using hd.target⟩)
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun i hi => read_spec B r A C u i hi hB hm)
  rintro σ ⟨hd,hroom⟩
  let ν:=σ.setVar "fill.length" (N n r)
  have r1:Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega)⟩)
  let μ:=ν.setVar "lp.length" 0
  have r2:Run B (.assign "lp.length" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (show 0< B by omega))
  have d2:=frame (r1.seq r2) hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩:=ht μ ⟨d2,by simp [μ,ν,hlen],by simp [μ],
    by simpa only [List.length_nil,Nat.zero_add,hlen,μ,ν,arrs_setVar] using hroom,by simp [Prefix]⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; nlinarith only []),p3.1,?_,?_⟩
  · simpa only [List.length_nil,Nat.zero_add,hlen] using p3.2.1
  · exact p3.2.2

theorem command_spec {n:ℕ} (B r:ℕ) (A C:Finset (Fin n)) (u:ℕ)
    (hB:n+u+3*N n r+10< B) (hm:2^n< B):
    Spec B (fun σ => Data r A C u σ∧ NativeArrayBounds.Bounded B σ∧
      3*N n r≤(σ.arrs "lp.input").length∧ 3*N n r≤(σ.arrs "round.normal").length) command
      (fun _ τ => Data r A C u τ∧ Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal (normal (r:=r) A C u)))) "round.normal" τ)
      ((28*n+104)*N n r+20):=by
  rintro σ ⟨hd,hb,hlp,hr⟩
  obtain ⟨ν,r1,p1⟩:=table_spec B r A C u hB hm σ ⟨hd,hlp⟩
  have hlen:(NativeRoundedQuery.normal (normal (r:=r) A C u)).length=3*N n r:=
    NativeRoundedQuery.vector_length _
  obtain ⟨τ,r2,p2⟩:=NativeProgramCache.copy_spec B "lp.input" "round.normal" "lp.length"
    (NativeRoundedQuery.normal (normal (r:=r) A C u)) (by decide) (by rw [hlen]; omega)
    (NativeArrayBounds.prefix_words (NativeArrayBounds.run r1 hb) p1.2.2) ν
    ⟨p1.2.2,by simpa only [hlen] using p1.2.1,by rw [hlen,RamFrames.run_array_length r1]; exact hr⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [hlen]; nlinarith only []),
    frame r2 p1.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),?_⟩
  simpa only [cleared_integer] using p2.2

end Lax263307Proofs.NativeComponentNormal

end

section

namespace Lax263307Proofs.NativeOracleCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

theorem failed_child_spec {n:ℕ} (B r next:ℕ) (A C:Finset (Fin n)) (t:ℕ)
    (hB:n+t+3*NativeCatalogMetadata.N n r+next+10< B) (hm:2^n< B):
    Spec B (fun σ => NativeComponentNormal.Data r A C t σ∧ NativeArrayBounds.Bounded B σ∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
      (failedChild next) (fun _ τ => Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
          (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ∧ τ.vars "machine.phase"=next)
      ((28*n+104)*NativeCatalogMetadata.N n r+26):=by
  rintro σ ⟨hd,hb,hlp,hr⟩
  let ν:=σ.setVar "component.target" (t-1)
  have r1:Run B (.assign "component.target" (.sub (.var "component.target") (.lit 1))) σ ν 4:=
    Run.assign (evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨hd.target.symm,hd.target ▸ (by omega)⟩)
      (evalB_lit (show 1< B by omega)) (by change t-1< B; omega))
  have d1:NativeComponentNormal.Data r A C (t-1) ν:=
    ⟨(r1.frame_var _ (by decide)).trans hd.order,(r1.frame_var _ (by decide)).trans hd.count,
      hd.catalog,(r1.frame_var _ (by decide)).trans hd.conditioning,
      (r1.frame_var _ (by decide)).trans hd.component,by simp [ν]⟩
  obtain ⟨μ,r2,p2⟩:=NativeComponentNormal.command_spec B r A C (t-1) (by omega) hm ν
    ⟨d1,NativeArrayBounds.run r1 hb,by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1]⟩
  let τ:=μ.setVar "machine.phase" next
  have r3:Run B (.assign "machine.phase" (.lit next)) μ τ 2:=Run.assign (evalB_lit (show next< B by omega))
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p2.2,by simp [τ]⟩

end Lax263307Proofs.NativeOracleCut

end

section

namespace Lax263307Proofs.NativeChildLift

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def selected {n:ℕ} (R:Finset (Fin n)) (I:Finset (Fin R.card)) (i:ℕ):Finset (Fin n):=
  (initialSet I i).image (label R)

theorem selected_step {n:ℕ} (R:Finset (Fin n)) (I:Finset (Fin R.card))
    (i:ℕ) (hi:i< R.card):
    selected R I (i+1)=if (⟨i,hi⟩:Fin R.card)∈I then
      insert (label R ⟨i,hi⟩) (selected R I i) else selected R I i:=by
  rw [selected,prefix_succ I i hi]
  split_ifs <;> simp only [Finset.image_insert,selected]

structure Context {n:ℕ} (R:Finset (Fin n)) (I:Finset (Fin R.card)) (σ:Env):Prop where
  order:σ.vars "graph.n"=R.card
  bits:Prefix (IndependentSetEncoding.encodeOutput I) "subset.bits" σ
  labels:Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ

theorem frame {B K n:ℕ} {R:Finset (Fin n)} {I:Finset (Fin R.card)} {c:Com} {σ τ:Env}
    (rr:Run B c σ τ K) (hd:Context R I σ) (hn:"graph.n"∉c.wvars)
    (hb:"subset.bits"∉c.warrs) (hl:"restrict.vertices"∉c.warrs):Context R I τ:=by
  refine ⟨(rr.frame_var _ hn).trans hd.order,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" hb] using hd.bits
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" hl] using hd.labels

structure Invariant {n:ℕ} (R:Finset (Fin n)) (I:Finset (Fin R.card)) (σ:Env):Prop where
  context:Context R I σ
  index:σ.vars "lift.i"≤ R.card
  value:σ.vars "lift.mask"=mask (selected R I (σ.vars "lift.i"))

theorem step_spec (B n:ℕ) (R:Finset (Fin n)) (I:Finset (Fin R.card))
    (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => Invariant R I σ∧ σ.vars "lift.i"< R.card) step
      (fun σ τ => Invariant R I τ∧ τ.vars "lift.i"=σ.vars "lift.i"+1) 20:=by
  rintro σ ⟨hd,hi⟩
  let i:=σ.vars "lift.i"
  let v:=label R (⟨i,hi⟩:Fin R.card)
  let bit:ℕ:=if (⟨i,hi⟩:Fin R.card)∈I then 1 else 0
  have hr:=NativeMaskUnpack.card_bound R
  have hiB:i< B:=hi.trans_le hr |>.trans (by omega)
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hbB:bit< B:=by dsimp [bit]; split_ifs <;> omega
  have hgetb:(σ.arrs "subset.bits")[i]?=some bit:=by
    simpa only [IndependentSetEncoding.encodeOutput,List.getElem_ofFn] using
      hd.context.bits i (by simpa only [IndependentSetEncoding.encodeOutput,List.length_ofFn] using hi)
  have hgetv:(σ.arrs "restrict.vertices")[i]?=some v.val:=by
    simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
      hd.context.labels i (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using hi)
  let ν:=σ.setVar "lift.bit" bit
  have r1:Run B (.assign "lift.bit" (.get "subset.bits" (.var "lift.i"))) σ ν 3:=Run.assign
    (evalB_get (evalB_var hiB) hgetb hbB)
  let μ:=ν.setVar "lift.vertex" v.val
  have r2:Run B (.assign "lift.vertex" (.get "restrict.vertices" (.var "lift.i"))) ν μ 3:=Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨(r1.frame_var "lift.i" (by decide)).symm,
      (r1.frame_var "lift.i" (by decide)) ▸ hiB⟩) hgetv hvB)
  have hc:(Cond.eq (.var "lift.bit") (.lit 1)).evalB B μ=some (decide (bit=1)):=
    evalB_condEq (by rw [evalB_var_iff]; simp [μ,ν,hbB]) (evalB_lit (show 1< B by omega))
  have hmμ:μ.vars "lift.mask"=mask (selected R I i):=
    ((r1.seq r2).frame_var "lift.mask" (by decide)).trans hd.value
  have hbranch:∃ ρ,Run B choose μ ρ 10∧ ρ.vars "lift.mask"=mask (selected R I (i+1)):=by
    by_cases h:(⟨i,hi⟩:Fin R.card)∈I
    · have hnew:Nat.lor (mask (selected R I i)) (2^v.val)=mask (selected R I (i+1)):=by
        rw [selected_step R I i hi,if_pos h]
        exact (mask_insert _ v).symm
      let ρ:=μ.setVar "lift.mask" (mask (selected R I (i+1)))
      have he:(Expr.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex"))).evalB B μ=
          some (mask (selected R I (i+1))):=by
        have hh:(Expr.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex"))).evalB B μ=
            some (Nat.lor (mask (selected R I i)) (1*2^v.val)):=evalB_bin (op:=.or)
          (by rw [evalB_var_iff]; exact ⟨hmμ.symm,hmμ ▸ (mask_bound _).trans hm⟩)
          (evalB_bin (op:=.shiftl) (evalB_lit (show 1< B by omega))
            (by rw [evalB_var_iff]; simp [μ,hvB])
            (by change 1*2^v.val< B; rw [one_mul]; exact (Nat.pow_le_pow_right (by decide) v.isLt.le).trans_lt hm))
          (by change Nat.lor (mask (selected R I i)) (1*2^v.val)< B; rw [one_mul,hnew]; exact (mask_bound _).trans hm)
        simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,hnew] using hh
      have rr:Run B insertCommand μ ρ 6:=Run.assign he
      exact ⟨ρ,(Run.ite_true (d:=.skip) (by simpa [bit,h] using hc) rr).mono (by decide),by simp [ρ]⟩
    · exact ⟨μ,(Run.ite_false (c:=insertCommand) (by simpa [bit,h] using hc) Run.skip).mono (by decide),
        by rw [selected_step R I i hi,if_neg h]; exact hmμ⟩
  obtain ⟨ρ,r3,hmask⟩:=hbranch
  have rr:=r1.seq (r2.seq r3)
  have hiρ:ρ.vars "lift.i"=i:=rr.frame_var "lift.i" (by decide)
  let τ:=ρ.setVar "lift.i" (i+1)
  have r4:Run B (.assign "lift.i" (.add (.var "lift.i") (.lit 1))) ρ τ 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiρ.symm,hiρ ▸ hiB⟩)
      (evalB_lit (show 1< B by omega)) (by change i+1< B; omega))
  have ht:τ.vars "lift.i"=i+1:=by simp [τ]
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),
    ⟨frame (rr.seq r4) hd.context (by decide) (by decide) (by decide),by rw [ht]; omega,
      by rw [ht]; exact (r4.frame_var "lift.mask" (by decide)).trans hmask⟩,ht⟩

theorem command_spec (B n:ℕ) (R:Finset (Fin n)) (I:Finset (Fin R.card))
    (hB:n+2< B) (hm:2^n< B):
    Spec B (Context R I) command
      (fun _ τ => Context R I τ∧ τ.vars "lift.mask"=mask (I.image (label R))) (24*R.card+8):=by
  have hr:=NativeMaskUnpack.card_bound R
  have hloop:=Spec.forRangeZero "lift.i" "graph.n" (Invariant R I) R.card 20 (by omega)
    (fun _ h => h.index) (fun _ h => h.context.order) (step_spec B n R I hB hm)
  intro σ hd
  let ν:=σ.setVar "lift.mask" 0
  have r1:Run B (.assign "lift.mask" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (show 0< B by omega))
  have r0:Run B (.assign "lift.i" (.lit 0)) ν (ν.setVar "lift.i" 0) 2:=Run.assign (evalB_lit (show 0< B by omega))
  have hi:Invariant R I (ν.setVar "lift.i" 0):=by
    refine ⟨frame (r1.seq r0) hd (by decide) (by decide) (by decide),by simp,?_⟩
    simp only [vars_setVar,if_true,selected,prefix_zero,Finset.image_empty,mask_empty]
    exact (r0.frame_var "lift.mask" (by decide)).trans (by simp [ν])
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.context,
    by simpa only [p2.2,selected,prefix_full] using p2.1.value⟩

end Lax263307Proofs.NativeChildLift

end

section

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

theorem setup_spec (B n r m:ℕ) (hn:n< B) (hr:r< B) (hm:m< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "restrict.count"=r∧ σ.vars "recursion.return.mask"=m) setup
      (fun _ τ => τ.vars "lift.parent.n"=n∧ τ.vars "graph.n"=r∧ τ.vars "unpack.mask"=m) 6:=by
  rintro σ ⟨hnσ,hrσ,hmσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lift.parent.n") n) (And (@Eq Nat (Env.vars τ "graph.n") r) (@Eq Nat (Env.vars τ "unpack.mask") m))) σ; let c1:Nat:=Env.vars (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) "restrict.count"; let c2:Env:=Env.setVar (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) "graph.n" c1; let c3:Nat:=Env.vars c2 "recursion.return.mask"; let c4:Env:=Env.setVar c2 "unpack.mask" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "graph.n")); let c8:Nat:=c6 (Expr.size (Expr.var "restrict.count")); let c9:Nat:=c6 (Expr.size (Expr.var "recursion.return.mask")); let c10:Nat:=c5 c8 c9; let c11:String→ Nat:=Env.vars c4; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B setup σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B setup σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "lift.parent.n" (Expr.var "graph.n")) (Com.seq (Com.assign "graph.n" (Expr.var "restrict.count")) (Com.assign "unpack.mask" (Expr.var "recursion.return.mask"))) σ (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) c4 c7 c10 (RunStep.assign B σ "lift.parent.n" (Expr.var "graph.n") (Env.vars σ "graph.n") (RunStep.eval_var B σ "graph.n" (?nAX_g9021_0_0_0))) (RunStep.seq B (Com.assign "graph.n" (Expr.var "restrict.count")) (Com.assign "unpack.mask" (Expr.var "recursion.return.mask")) (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) "graph.n" (Expr.var "restrict.count") c1 (RunStep.eval_var B (Env.setVar σ "lift.parent.n" (Env.vars σ "graph.n")) "restrict.count" (?nAX_g9021_0_0_1))) (RunStep.assign B c2 "unpack.mask" (Expr.var "recursion.return.mask") c3 (RunStep.eval_var B c2 "recursion.return.mask" (?nAX_g9021_0_0_2))))) (?nAX_g9021_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9021_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9021_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9021_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9021_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]

theorem lift_spec (B n:ℕ) (R:Finset (Fin n)) (I:Finset (Fin R.card))
    (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "restrict.count"=R.card∧
      σ.vars "recursion.return.mask"=mask I∧ Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ∧
      R.card≤(σ.arrs "subset.bits").length) liftCommand
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "lift.mask"=mask (I.image (label R))∧
        Prefix (NativeRestrictionOrder.words R) "restrict.vertices" τ) (45*R.card+24):=by
  have hr:=NativeMaskUnpack.card_bound R
  have hmR:2^R.card< B:=(Nat.pow_le_pow_right (by decide) hr).trans_lt hm
  rintro σ ⟨hn,hcount,hmask,hlabels,hroom⟩
  obtain ⟨ν,r1,p1⟩:=setup_spec B n R.card (mask I) (by omega) (by omega) ((mask_bound I).trans hmR)
    σ ⟨hn,hcount,hmask⟩
  obtain ⟨μ,r2,p2⟩:=NativeMaskUnpack.command_spec B I (by omega) hmR ν
    ⟨p1.2.1,p1.2.2,by rwa [RamFrames.run_array_length r1]⟩
  have rr:=r1.seq r2
  obtain ⟨ρ,r3,p3⟩:=NativeChildLift.command_spec B n R I hB hm μ
    ⟨(r2.frame_var "graph.n" (by decide)).trans p1.2.1,p2.1,
      by simpa only [Prefix,rr.frame_arr "restrict.vertices" (by decide)] using hlabels⟩
  have hparent:=((r2.seq r3).frame_var "lift.parent.n" (by decide)).trans p1.1
  let τ:=ρ.setVar "graph.n" n
  have r4:Run B (.assign "graph.n" (.var "lift.parent.n")) ρ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hparent.symm,hparent ▸ (by omega:n< B)⟩)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simp [τ],
    (r4.frame_var "lift.mask" (by decide)).trans p3.2,
    by simpa only [Prefix,τ,arrs_setVar] using p3.1.labels⟩

end Lax263307Proofs.NativeChildReturn

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks ComputedSeparators

theorem advance_spec (B i next:ℕ) (hB:i+next+3< B):
    Spec B (fun σ => σ.vars "component.i"=i) (advance next)
      (fun _ τ => τ.vars "component.i"=i+1∧ τ.vars "machine.phase"=next) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 i ((1:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "component.i") c1) (@Eq Nat (Env.vars τ "machine.phase") next)) σ; let c3:Nat:=c0 (Env.vars σ "component.i") ((1:Nat)); let c4:Env:=Env.setVar σ "component.i" c3; let c5:Env:=Env.setVar c4 "machine.phase" next; let c6:Nat→ Nat:=c0 ((1:Nat)); let c7:Expr:=Expr.add (Expr.var "component.i") (Expr.lit ((1:Nat))); let c8:Nat:=c6 (Expr.size c7); let c9:Nat:=c6 (Expr.size (Expr.lit next)); let c10:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B (advance next) σ σ' ((6:Nat))) (c2 σ')) c5 (@And.intro (Run B (advance next) σ c5 ((6:Nat))) (c2 c5) (RunStep.mono B (advance next) σ c5 (c0 c8 c9) ((6:Nat)) (RunStep.seq B (Com.assign "component.i" c7) (Com.assign "machine.phase" (Expr.lit next)) σ c4 c5 c8 c9 (RunStep.assign B σ "component.i" c7 c3 (RunStep.eval_add B σ (Expr.var "component.i") (Expr.lit ((1:Nat))) (Env.vars σ "component.i") ((1:Nat)) (RunStep.eval_var B σ "component.i" (?nAX_g9027_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9027_0_0_1)) (?nAX_g9027_0_0_2))) (RunStep.assign B c4 "machine.phase" (Expr.lit next) next (RunStep.eval_lit B next c4 (?nAX_g9027_0_0_3)))) (?nAX_g9027_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9027_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9027_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9027_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9027_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9027_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem append_spec {n:ℕ} (B i next:ℕ) (S I:Finset (Fin n))
    (hB:i+next+3< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "component.i"=i∧ σ.vars "component.union"=mask S∧ σ.vars "lift.mask"=mask I)
      (append next) (fun _ τ => τ.vars "component.i"=i+1∧ τ.vars "component.union"=mask (S∪I)∧
        τ.vars "machine.phase"=next) 10:=by
  rintro σ ⟨hi,hs,hI⟩
  let ν:=σ.setVar "component.union" (mask (S∪I))
  have r1:Run B (.assign "component.union" (.or (.var "component.union") (.var "lift.mask"))) σ ν 4:=by
    apply Run.assign
    rw [NativeSetMasks.union]
    exact evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (mask_bound S).trans hm⟩)
      (by rw [evalB_var_iff]; exact ⟨hI.symm,hI ▸ (mask_bound I).trans hm⟩)
      (by change Nat.lor (mask S) (mask I)< B; rw [←NativeSetMasks.union]; exact (mask_bound _).trans hm)
  obtain ⟨τ,r2,p2⟩:=advance_spec B i next hB ν ((r1.frame_var _ (by decide)).trans hi)
  exact ⟨τ,r1.seq r2,p2.1,(r2.frame_var _ (by simp [advance,Com.wvars])).trans (by simp [ν]),p2.2⟩

theorem child_some_spec {n:ℕ} (B i more update:ℕ) (C S:Finset (Fin n))
    (I:Finset (Fin C.card)) (hB:n+i+more+5< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "recursion.return.tag"=1∧ σ.vars "graph.n"=n∧
      σ.vars "restrict.count"=C.card∧ σ.vars "recursion.return.mask"=mask I∧
      Prefix (NativeRestrictionOrder.words C) "restrict.vertices" σ∧ C.card≤(σ.arrs "subset.bits").length∧
      σ.vars "component.i"=i∧ σ.vars "component.union"=mask S)
      (childReply more update) (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "component.i"=i+1∧
        τ.vars "component.union"=mask (S∪I.image (label C))∧ τ.vars "machine.phase"=more)
      (45*C.card+38):=by
  rintro σ ⟨htag,hn,hc,hmask,hlabels,hroom,hi,hs⟩
  obtain ⟨ν,r1,p1⟩:=NativeChildReturn.lift_spec B n C I (by omega) hm σ ⟨hn,hc,hmask,hlabels,hroom⟩
  obtain ⟨τ,r2,p2⟩:=append_spec B i more S (I.image (label C)) (by omega) hm ν
    ⟨(r1.frame_var _ (by decide)).trans hi,(r1.frame_var _ (by decide)).trans hs,p1.2.1⟩
  have hcond:(Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some true:=by
    have hh:=evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega:1< B)⟩) (evalB_lit (show 1< B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_true (d:=NativeOracleCut.failedChild update) hcond (r1.seq r2)).mono
    (by simp [Cond.size,Expr.size]; omega),
    (r2.frame_var _ (by simp [append,advance,Com.wvars])).trans p1.1,p2⟩

theorem child_none_spec {n:ℕ} (B r more update:ℕ) (A C:Finset (Fin n)) (t:ℕ)
    (hB:n+t+3*NativeCatalogMetadata.N n r+update+10< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "recursion.return.tag"=0∧ NativeComponentNormal.Data r A C t σ∧
      NativeArrayBounds.Bounded B σ∧ 3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
      (childReply more update) (fun _ τ => Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
          (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ∧ τ.vars "machine.phase"=update)
      ((28*n+104)*NativeCatalogMetadata.N n r+30):=by
  rintro σ ⟨htag,hd⟩
  obtain ⟨τ,rr,p⟩:=NativeOracleCut.failed_child_spec B r update A C t hB hm σ hd
  have hcond:(Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some false:=by
    have hh:=evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega:0< B)⟩) (evalB_lit (show 1< B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_false (c:=.seq NativeChildReturn.liftCommand (append more)) hcond rr).mono
    (by simp [Cond.size,Expr.size]; omega),p⟩

end Lax263307Proofs.NativeComponentControl

end

section

namespace Lax263307Proofs.NativeChildGraph

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeRestrictionRead

theorem flat_entry {r:ℕ} (G:SimpleGraph (Fin r)) [DecidableRel G.Adj] (i:Fin (r*r)):
    (NativeWeightReduction.adjacency G)[i.val]'(by rw [NativeWeightReduction.adjacency_length]; exact i.isLt)=
      if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then 1 else 0:=by
  have he:=NativeMatrixOrder.flatten r (fun u v => if G.Adj u v then 1 else 0)
  change List.ofFn _=NativeWeightReduction.adjacency G at he
  simp only [← he,List.getElem_ofFn]

theorem read_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i:ℕ)
    (hi:i<(NativeWeightReduction.adjacency (restriction G R)).length) (hB:n*n+n+3< B):
    Spec B (fun σ => Data G x R σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data G x R τ∧
        τ.vars "fill.value"=(NativeWeightReduction.adjacency (restriction G R))[i]) 25:=by
  have hir:i< R.card*R.card:=by simpa only [NativeWeightReduction.adjacency_length] using hi
  let row:=NativeBlowUp.row (⟨i,hir⟩:Fin (R.card*R.card))
  let col:=NativeBlowUp.col (⟨i,hir⟩:Fin (R.card*R.card))
  have hr:=NativeMaskUnpack.card_bound R
  have hiB:i< B:=hir.trans_le (Nat.mul_self_le_mul_self hr) |>.trans (by omega)
  have hrow:row.val< B:=row.isLt.trans_le hr |>.trans (by omega)
  have hcol:col.val< B:=col.isLt.trans_le hr |>.trans (by omega)
  rintro σ ⟨hd,hs⟩
  let ν:=σ.setVar "restrict.row" row.val
  have r1:Run B (.assign "restrict.row" (.div (.var "fill.i") (.var "restrict.count"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.div)
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega:R.card< B)⟩)
      (by change i/R.card< B; exact hrow))
  have hd1:=frame r1 hd (by decide) (by decide)
  let μ:=ν.setVar "restrict.col" col.val
  have hmul:row.val*R.card≤ i:=Nat.div_mul_le_self i R.card
  have r2:Run B (.assign "restrict.col" (.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count")))) ν μ 6:=by
    apply Run.assign
    change (Expr.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count"))).evalB B ν=some (i%R.card)
    rw [Nat.mod_eq_sub_div_mul]
    exact evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨((r1.frame_var "fill.i" (by decide)).trans hs).symm,
        ((r1.frame_var "fill.i" (by decide)).trans hs) ▸ hiB⟩)
      (evalB_bin (op:=.mul) (by rw [evalB_var_iff]; simp only [ν,vars_setVar,if_true]; exact ⟨rfl,hrow⟩)
        (by rw [evalB_var_iff]; exact ⟨hd1.count.symm,hd1.count ▸ (by omega:R.card< B)⟩)
        (by change row.val*R.card< B; omega))
      (by change i-row.val*R.card< B; omega)
  have hd2:=frame r2 hd1 (by decide) (by decide)
  obtain ⟨ρ,r3,p3⟩:=graph_spec B n G x R row col hB μ
    ⟨hd2,(r2.frame_var "restrict.row" (by decide)).trans (by simp [ν]),by simp [μ]⟩
  let bit:ℕ:=if (restriction G R).Adj row col then 1 else 0
  have hb:bit< B:=by dsimp [bit]; split_ifs <;> omega
  let τ:=ρ.setVar "fill.value" bit
  have r4:Run B (.assign "fill.value" (.var "restrict.edge")) ρ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p3.2.symm,p3.2 ▸ hb⟩)
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),frame r4 p3.1 (by decide) (by decide),
    by simpa only [τ,vars_setVar,if_true] using (flat_entry (restriction G R) ⟨i,hir⟩).symm⟩

theorem command_spec (B n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (hB:n*n+n+3< B):
    Spec B (fun σ => Data G x R σ∧ R.card*R.card≤(σ.arrs "child.graph").length) command
      (fun _ τ => Data G x R τ∧ Prefix (NativeWeightReduction.adjacency (restriction G R)) "child.graph" τ)
      (36*(R.card*R.card)+10):=by
  let xs:=NativeWeightReduction.adjacency (restriction G R)
  have hlen:xs.length=R.card*R.card:=NativeWeightReduction.adjacency_length _
  have hr:=NativeMaskUnpack.card_bound R
  have hsq:=Nat.mul_self_le_mul_self hr
  have hv:=NativeTabulate.command_spec B xs "child.graph" (Data G x R) read 25
    (by rw [hlen]; omega)
    (by
      intro z hz
      have hbit:z=0∨ z=1:=by
        obtain ⟨row,hrow,hz⟩:=List.mem_flatten.mp hz
        obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hrow
        obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hz
        split_ifs <;> simp
      rcases hbit with rfl | rfl <;> omega)
    (by decide) (by decide) (by decide)
    (by
      intro σ hd
      have rr:Run B (.assign "fill.i" (.lit 0)) σ (σ.setVar "fill.i" 0) 2:=Run.assign (evalB_lit (by omega))
      exact frame rr hd (by decide) (by decide))
    (fun _ _ rr hd => frame rr hd (by decide) (by decide))
    (fun i hi => read_spec B n G x R i hi hB)
  rintro σ ⟨hd,hroom⟩
  let ν:=σ.setVar "fill.length" (R.card*R.card)
  have r1:Run B (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega:R.card< B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega:R.card< B)⟩)
      (by change R.card*R.card< B; omega))
  obtain ⟨τ,r2,p2⟩:=hv ν ⟨frame r1 hd (by decide) (by decide),by simp [ν,hlen],by simpa only [ν,arrs_setVar,hlen] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2⟩

end Lax263307Proofs.NativeChildGraph

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

theorem step_spec (B:ℕ) (source target:String) (front xs:List ℕ) (hne:source≠target)
    (hB:front.length+xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Invariant source target front xs σ∧ σ.vars "stack.i"< xs.length)
      (step source target) (fun σ τ => Invariant source target front xs τ∧
        τ.vars "stack.i"=σ.vars "stack.i"+1) 12:=by
  rintro σ ⟨hd,hi⟩
  let i:=σ.vars "stack.i"
  have hroom:=hd.room
  have hlen:(front++xs.take i).length=front.length+i:=by
    rw [List.length_append,List.length_take,Nat.min_eq_left (show i≤ xs.length from hd.index)]
  obtain ⟨ν,r1,p1⟩:=RamWordBuffer.append_spec B target "stack.words" (front++xs.take i) xs[i]
    (.get source (.var "stack.i")) (by omega) (by rw [hlen]; omega) σ
    ⟨hd.target,by rw [hlen]; exact hd.position,by rw [hlen]; omega,
      evalB_get (evalB_var (by omega:i< B)) (hd.source i hi) (hv _ (List.getElem_mem hi))⟩
  have hiν:ν.vars "stack.i"=i:=r1.frame_var "stack.i" (by simp [RamWordBuffer.append,Com.wvars])
  let τ:=ν.setVar "stack.i" (i+1)
  have r2:Run B (.assign "stack.i" (.add (.var "stack.i") (.lit 1))) ν τ 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i< B)⟩)
      (evalB_lit (show 1< B by omega)) (by change i+1< B; omega))
  have rr:=r1.seq r2
  have ht:τ.vars "stack.i"=i+1:=by simp [τ]
  refine ⟨τ,rr.mono (by simp [Expr.size]),⟨?_,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr source (by simp [step,RamWordBuffer.append,Com.warrs,hne])] using hd.source
  · exact (rr.frame_var "stack.copy.length" (by simp [step,RamWordBuffer.append,Com.wvars])).trans hd.count
  · rw [r2.frame_var "stack.words" (by decide),p1.2,hlen,ht]
    omega
  · rw [RamFrames.run_array_length rr]; exact hd.room
  · rw [ht,List.take_succ_eq_append_getElem hi]
    simpa only [Prefix,τ,arrs_setVar,List.append_assoc] using p1.1

theorem command_spec (B:ℕ) (source target:String) (front xs:List ℕ) (hne:source≠target)
    (hB:front.length+xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix xs source σ∧ Prefix front target σ∧
      σ.vars "stack.words"=front.length∧ σ.vars "stack.copy.length"=xs.length∧
      front.length+xs.length≤(σ.arrs target).length) (command source target)
      (fun _ τ => Prefix xs source τ∧ Prefix (front++xs) target τ∧
        τ.vars "stack.words"=front.length+xs.length) (16*xs.length+6):=by
  have hloop:=Spec.forRangeZero "stack.i" "stack.copy.length" (Invariant source target front xs)
    xs.length 12 (by omega) (fun _ h => h.index) (fun _ h => h.count)
    (step_spec B source target front xs hne hB hv)
  rintro σ ⟨hs,hf,hpos,hcount,hroom⟩
  have hi:Invariant source target front xs (σ.setVar "stack.i" 0):=by
    refine ⟨hs,by simpa using hcount,by simp,by simpa using hpos,hroom,?_⟩
    simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using hf
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  exact ⟨τ,rr.mono (by nlinarith only []),p.1.source,
    by simpa only [p.2,List.take_length] using p.1.target,by simpa only [p.2] using p.1.position⟩

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

theorem words_congr (names:List String) (σ τ:Env)
    (h:∀ a∈names,σ.arrs a=τ.arrs a):words names σ=words names τ:=by
  induction names with
  | nil => rfl
  | cons a as ih =>
    have hi:=ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    change List.flatMap σ.arrs as=List.flatMap τ.arrs as at hi
    simp only [words,List.flatMap_cons]
    rw [h a (by simp),hi]

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

theorem array_frame (names:List String) (a:String) (ha:a≠"recursion.frames"):a∉(save names).warrs:=by
  induction names with
  | nil => simp [save,Com.warrs]
  | cons b bs ih => simp [save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.warrs,ha,ih]

theorem save_spec (B S:ℕ) (names:List String) (front:List ℕ)
    (hne:"recursion.frames"∉names) (hB:front.length+S*names.length+2< B):
    Spec B (fun σ => NativeStateBounds.Bounded B σ∧ Prefix front "recursion.frames" σ∧
      σ.vars "stack.words"=front.length∧ σ.vars "recursion.stride"=S∧
      (∀ a∈names,(σ.arrs a).length=S)∧
      front.length+S*names.length≤(σ.arrs "recursion.frames").length) (save names)
      (fun σ τ => NativeStateBounds.Bounded B τ∧
        Prefix (front++words names σ) "recursion.frames" τ∧
        τ.vars "stack.words"=front.length+S*names.length) ((16*S+8)*names.length+1):=by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hd,hf,hp,hs,he,hr⟩
    exact ⟨σ,Run.skip,hd,by simpa only [words,List.flatMap_nil,List.append_nil] using hf,
      by simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hp⟩
  | cons a as ih =>
    rintro σ ⟨hd,hf,hp,hs,he,hr⟩
    have ha:a≠"recursion.frames" :=by intro h; apply hne; simp [h]
    have has:"recursion.frames"∉as:=by intro h; exact hne (List.mem_cons_of_mem a h)
    let xs:=σ.arrs a
    have hlen:xs.length=S:=he a (by simp)
    let ν:=σ.setVar "stack.copy.length" S
    have r1:Run B (.assign "stack.copy.length" (.var "recursion.stride")) σ ν 2:=Run.assign
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hd.1 _⟩)
    have hheadB:front.length+xs.length+2< B:=by rw [hlen]; simp only [List.length_cons] at hB; nlinarith only [hB]
    obtain ⟨μ,r2,p2⟩:=NativeBlockAppend.command_spec B a "recursion.frames" front xs ha hheadB
      (fun z hz => hd.2.1 a z hz) ν
      ⟨by intro i hi; exact List.getElem?_eq_getElem hi,
        by simpa only [Prefix,ν,arrs_setVar] using hf,by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hp,
        by simp [ν,hlen],by simpa only [ν,arrs_setVar,hlen] using
          (show front.length+S≤(σ.arrs "recursion.frames").length by simp only [List.length_cons] at hr; nlinarith only [hr])⟩
    have rr:=r1.seq r2
    have hd2:=NativeStateBounds.run rr hd
    have hwords:words as μ=words as σ:=by
      apply words_congr
      intro b hb
      have hbne:b≠"recursion.frames" :=by intro h; exact has (h ▸ hb)
      exact rr.frame_arr b (by simp [NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.warrs,hbne])
    have hstride:=(rr.frame_var "recursion.stride" (by simp [NativeBlockAppend.command,NativeBlockAppend.step,
      RamWordBuffer.append,Com.wvars])).trans hs
    have htB:(front++xs).length+S*as.length+2< B:=by
      simp only [List.length_append,hlen,List.length_cons] at hB ⊢
      nlinarith only [hB]
    obtain ⟨τ,r3,p3⟩:=ih (front++xs) has htB μ
      ⟨hd2,p2.2.1,by simpa only [List.length_append] using p2.2.2,hstride,
        (fun b hb => by rw [RamFrames.run_array_length rr]; exact he b (List.mem_cons_of_mem a hb)),
        by rw [RamFrames.run_array_length rr]; simp only [List.length_append,hlen,List.length_cons] at hr ⊢; nlinarith only [hr]⟩
    refine ⟨τ,((r1.seq r2).seq r3).mono ?_,p3.1,?_,?_⟩
    · rw [hlen]; simp only [List.length_cons]; nlinarith only []
    · rw [hwords] at p3
      simpa only [words,List.flatMap_cons,List.append_assoc] using p3.2.1
    · simp only [List.length_append,hlen,List.length_cons] at p3 ⊢
      nlinarith only [p3.2.2]

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeBlockRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem setup_spec (B base count:ℕ) (hB:base+count+2< B):
    Spec B (fun σ => σ.vars "stack.read.i"=base∧ σ.vars "stack.copy.length"=count) setup
      (fun _ τ => τ.vars "fill.length"=count∧ τ.vars "slice.start"=base) 4:=by
  rintro σ ⟨hb,hc⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "fill.length") count) (@Eq Nat (Env.vars τ "slice.start") base)) σ; let c1:Nat:=Env.vars (Env.setVar σ "fill.length" (Env.vars σ "stack.copy.length")) "stack.read.i"; let c2:Env:=Env.setVar (Env.setVar σ "fill.length" (Env.vars σ "stack.copy.length")) "slice.start" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 ((1:Nat)); let c5:Nat:=c4 (Expr.size (Expr.var "stack.copy.length")); let c6:Nat:=c4 (Expr.size (Expr.var "stack.read.i")); let c7:String→ Nat:=Env.vars c2; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B setup σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B setup σ c2 (c3 c5 c6) ((4:Nat)) (RunStep.seq B (Com.assign "fill.length" (Expr.var "stack.copy.length")) (Com.assign "slice.start" (Expr.var "stack.read.i")) σ (Env.setVar σ "fill.length" (Env.vars σ "stack.copy.length")) c2 c5 c6 (RunStep.assign B σ "fill.length" (Expr.var "stack.copy.length") (Env.vars σ "stack.copy.length") (RunStep.eval_var B σ "stack.copy.length" (?nAX_g9059_0_0_0))) (RunStep.assign B (Env.setVar σ "fill.length" (Env.vars σ "stack.copy.length")) "slice.start" (Expr.var "stack.read.i") c1 (RunStep.eval_var B (Env.setVar σ "fill.length" (Env.vars σ "stack.copy.length")) "stack.read.i" (?nAX_g9059_0_0_1)))) (?nAX_g9059_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9059_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9059_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9059_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]

theorem command_spec (B:ℕ) (target:String) (front xs:List ℕ)
    (hne:"recursion.frames"≠target) (hB:front.length+xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix (front++xs) "recursion.frames" σ∧
      σ.vars "stack.read.i"=front.length∧ σ.vars "stack.copy.length"=xs.length∧
      xs.length≤(σ.arrs target).length) (command target)
      (fun _ τ => Prefix (front++xs) "recursion.frames" τ∧ Prefix xs target τ∧
        τ.vars "stack.read.i"=front.length+xs.length) (16*xs.length+14):=by
  rintro σ ⟨hp,hi,hl,hroom⟩
  obtain ⟨ν,r1,p1⟩:=setup_spec B front.length xs.length hB σ ⟨hi,hl⟩
  obtain ⟨μ,r2,p2⟩:=NativeSlice.command_spec B "recursion.frames" target front xs [] hne (by omega) hv ν
    ⟨⟨by simpa only [List.append_nil,Prefix,r1.frame_arr "recursion.frames" (by decide)] using hp,p1.2⟩,
      p1.1,by rwa [RamFrames.run_array_length r1]⟩
  have hiμ:=((r1.seq r2).frame_var "stack.read.i" (by simp [setup,NativeSlice.command,
    NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hi
  have hlμ:=((r1.seq r2).frame_var "stack.copy.length" (by simp [setup,NativeSlice.command,
    NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hl
  let τ:=μ.setVar "stack.read.i" (front.length+xs.length)
  have r3:Run B (.assign "stack.read.i" (.add (.var "stack.read.i") (.var "stack.copy.length"))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:front.length< B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlμ.symm,hlμ ▸ (by omega:xs.length< B)⟩)
      (by change front.length+xs.length< B; omega))
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,?_,by simp [τ]⟩
  · simpa only [NativeSlice.Context,List.append_nil,Prefix,τ,arrs_setVar] using p2.1.1
  · simpa only [Prefix,τ,arrs_setVar] using p2.2

end Lax263307Proofs.NativeBlockRestore

end

section

namespace Lax263307Proofs.NativeFrameBufferRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem array_frame (names:List String) (a:String) (ha:a∉names):a∉(command names).warrs:=by
  induction names with
  | nil => simp [command,Com.warrs]
  | cons b bs ih =>
    simp only [List.mem_cons,not_or] at ha
    simp [command,NativeBlockRestore.command,NativeBlockRestore.setup,NativeSlice.command,
      NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.warrs,ha.1,ih ha.2]

theorem prefix_left (front tail:List ℕ) (a:String) (σ:Env) (hp:Prefix (front++tail) a σ):
    Prefix front a σ:=by
  intro i hi
  have hx:i<(front++tail).length:=by simp only [List.length_append]; omega
  have he:(front++tail)[i]'hx=front[i]:=List.getElem_append_left hi
  simpa only [he] using hp i hx

theorem prefix_full (xs:List ℕ) (a:String) (σ:Env)
    (hp:Prefix xs a σ) (hlen:(σ.arrs a).length=xs.length):σ.arrs a=xs:=by
  apply List.ext_getElem
  · exact hlen
  · intro i hi hj
    have hh:=hp i hj
    simpa only [List.getElem?_eq_getElem hi,Option.some.injEq] using hh

theorem command_spec (B S:ℕ) (names:List String) (front:List ℕ) (saved:Env)
    (hnames:names.Nodup) (hne:"recursion.frames"∉names)
    (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈names,(saved.arrs a).length=S) (hB:front.length+S*names.length+2< B):
    Spec B (fun σ => Prefix (front++NativeFrameBuffers.words names saved) "recursion.frames" σ∧
      σ.vars "stack.read.i"=front.length∧ σ.vars "recursion.stride"=S∧
      ∀ a∈names,(σ.arrs a).length=S) (command names)
      (fun _ τ => Prefix (front++NativeFrameBuffers.words names saved) "recursion.frames" τ∧
        (∀ a∈names,τ.arrs a=saved.arrs a)∧ τ.vars "stack.read.i"=front.length+S*names.length)
      ((16*S+16)*names.length+1):=by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hp,hi,hs,he⟩
    exact ⟨σ,Run.skip,hp,by simp,by simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hi⟩
  | cons a as ih =>
    have hnd:=List.nodup_cons.mp hnames
    have ha:"recursion.frames"≠a:=by intro h; apply hne; simp [h]
    have has:"recursion.frames"∉as:=by intro h; exact hne (List.mem_cons_of_mem a h)
    let xs:=saved.arrs a
    have hlen:xs.length=S:=hext a (by simp)
    rintro σ ⟨hp,hi,hs,he⟩
    let ν:=σ.setVar "stack.copy.length" S
    have hSB:S< B:=by simp only [List.length_cons] at hB; nlinarith only [hB]
    have r1:Run B (.assign "stack.copy.length" (.var "recursion.stride")) σ ν 2:=Run.assign
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hSB⟩)
    have hhead:Prefix (front++xs) "recursion.frames" ν:=prefix_left (front++xs)
      (NativeFrameBuffers.words as saved) "recursion.frames" ν
      (by simpa only [Prefix,ν,arrs_setVar,NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using hp)
    obtain ⟨μ,r2,p2⟩:=NativeBlockRestore.command_spec B a front xs ha
      (by rw [hlen]; simp only [List.length_cons] at hB; nlinarith only [hB])
      (fun z hz => hsaved.2.1 a z hz) ν
      ⟨hhead,by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hi,by simp [ν,hlen],
        by simpa only [ν,arrs_setVar,hlen] using (he a (by simp)).ge⟩
    have rr:=r1.seq r2
    have harray:μ.arrs a=xs:=prefix_full xs a μ p2.2.1
      (by rw [RamFrames.run_array_length rr,he a (by simp),hlen])
    have hstride:=(rr.frame_var "recursion.stride" (by simp [NativeBlockRestore.command,NativeBlockRestore.setup,
      NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hs
    have hsource:Prefix ((front++xs)++NativeFrameBuffers.words as saved) "recursion.frames" μ:=by
      simpa only [Prefix,rr.frame_arr "recursion.frames" (by simp [NativeBlockRestore.command,NativeBlockRestore.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.warrs,ha]),
        NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using hp
    obtain ⟨τ,r3,p3⟩:=ih (front++xs) hnd.2 has (fun b hb => hext b (List.mem_cons_of_mem a hb))
      (by simp only [List.length_append,hlen,List.length_cons] at hB ⊢; nlinarith only [hB]) μ
      ⟨hsource,by simpa only [List.length_append] using p2.2.2,hstride,
        fun b hb => by rw [RamFrames.run_array_length rr]; exact he b (List.mem_cons_of_mem a hb)⟩
    refine ⟨τ,(rr.seq r3).mono ?_,?_,?_,?_⟩
    · rw [hlen]; simp only [List.length_cons]; nlinarith only []
    · simpa only [NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using p3.1
    · intro b hb
      rcases List.mem_cons.mp hb with h | hb
      · rw [h]
        exact (r3.frame_arr a (array_frame as a hnd.1)).trans harray
      · exact p3.2.1 b hb
    · simp only [List.length_append,hlen,List.length_cons] at p3 ⊢
      nlinarith only [p3.2.2]

end Lax263307Proofs.NativeFrameBufferRestore

end

section

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (names:List String) (s:String) (hs:s≠"stack.words"):s∉(save names).wvars:=by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

theorem save_spec (B:ℕ) (names:List String) (front:List ℕ)
    (hne:"stack.words"∉names) (hB:front.length+names.length+2< B):
    Spec B (fun σ => NativeStateBounds.Bounded B σ∧ Prefix front "recursion.frames" σ∧
      σ.vars "stack.words"=front.length∧ front.length+names.length≤(σ.arrs "recursion.frames").length)
      (save names) (fun σ τ => NativeStateBounds.Bounded B τ∧
        Prefix (front++words names σ) "recursion.frames" τ∧
        τ.vars "stack.words"=front.length+names.length) (7*names.length+1):=by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hd,hf,hp,hr⟩
    exact ⟨σ,Run.skip,hd,by simpa only [words,List.map_nil,List.append_nil] using hf,
      by simpa only [List.length_nil,Nat.add_zero] using hp⟩
  | cons s ss ih =>
    rintro σ ⟨hd,hf,hp,hr⟩
    have hs:s≠"stack.words" :=by intro h; apply hne; simp [h]
    have hss:"stack.words"∉ss:=by intro h; exact hne (List.mem_cons_of_mem s h)
    let v:=σ.vars s
    obtain ⟨ν,r1,p1⟩:=RamWordBuffer.append_spec B "recursion.frames" "stack.words" front v (.var s)
      (by omega) (by simp only [List.length_cons] at hB; omega) σ
      ⟨hf,hp,by simp only [List.length_cons] at hr; omega,evalB_var (hd.1 s)⟩
    have r1':Run B (RamWordBuffer.append "recursion.frames" "stack.words" (.var s)) σ ν 7:=r1
    have hd1:=NativeStateBounds.run r1' hd
    have hword:words ss ν=words ss σ:=by
      apply List.map_congr_left
      intro t ht
      have htne:t≠"stack.words" :=by intro h; exact hss (h ▸ ht)
      exact r1'.frame_var t (by simp [RamWordBuffer.append,Com.wvars,htne])
    have htB:(front++[v]).length+ss.length+2< B:=by
      simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hB ⊢
      omega
    have htroom:(front++[v]).length+ss.length≤(ν.arrs "recursion.frames").length:=by
      rw [RamFrames.run_array_length r1']
      simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hr ⊢
      omega
    obtain ⟨τ,r2,p2⟩:=ih (front++[v]) hss htB
      ν ⟨hd1,p1.1,by simpa only [List.length_append,List.length_singleton,List.length_nil] using p1.2,htroom⟩
    refine ⟨τ,(r1'.seq r2).mono (by simp only [List.length_cons]; omega),p2.1,?_,?_⟩
    · rw [hword] at p2
      simpa only [words,List.map_cons,List.append_assoc,List.singleton_append] using p2.2.1
    · simpa only [List.length_append,List.length_singleton,List.length_nil,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using p2.2.2

end Lax263307Proofs.NativeFrameScalars

end

section

namespace Lax263307Proofs.NativeFrameRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem variable_frame (names:List String) (s:String) (hs:s∉names) (hr:s≠"stack.read.i"):
    s∉(command names).wvars:=by
  induction names with
  | nil => simp [command,Com.wvars]
  | cons t ts ih => simp only [List.mem_cons,not_or] at hs; simp [command,step,Com.wvars,hs.1,hr,ih hs.2]

theorem command_spec (B:ℕ) (names:List String) (front xs:List ℕ)
    (hnames:names.Nodup) (hne:"stack.read.i"∉names) (hlen:xs.length=names.length)
    (hB:front.length+xs.length+2< B) (hv:∀ z∈xs,z< B):
    Spec B (fun σ => Prefix (front++xs) "recursion.frames" σ∧ σ.vars "stack.read.i"=front.length)
      (command names) (fun _ τ => Prefix (front++xs) "recursion.frames" τ∧
        NativeFrameScalars.words names τ=xs∧ τ.vars "stack.read.i"=front.length+xs.length)
      (7*names.length+1):=by
  induction names generalizing front xs with
  | nil =>
    have hx:xs=[]:=List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen)
    subst xs
    rintro σ ⟨hp,hi⟩
    exact ⟨σ,Run.skip,hp,rfl,by simpa only [List.length_nil,Nat.add_zero] using hi⟩
  | cons s ss ih =>
    cases xs with
    | nil => simp at hlen
    | cons v vs =>
      have hnd:=List.nodup_cons.mp hnames
      have hs:s≠"stack.read.i" :=by intro h; apply hne; simp [h]
      have hss:"stack.read.i"∉ss:=by intro h; exact hne (List.mem_cons_of_mem s h)
      have hvB:v< B:=hv v (by simp)
      rintro σ ⟨hp,hi⟩
      have hg:(σ.arrs "recursion.frames")[front.length]?=some v:=by
        have hh:=hp front.length (by simp)
        simpa only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero] using hh
      let ν:=σ.setVar s v
      have r1:Run B (.assign s (.get "recursion.frames" (.var "stack.read.i"))) σ ν 3:=
        Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by simp only [List.length_cons] at hB; omega)⟩) hg hvB)
      have hiν:ν.vars "stack.read.i"=front.length:=(r1.frame_var "stack.read.i" (by simp [Com.wvars,Ne.symm hs])).trans hi
      let μ:=ν.setVar "stack.read.i" (front.length+1)
      have r2:Run B (.assign "stack.read.i" (.add (.var "stack.read.i") (.lit 1))) ν μ 4:=
        Run.assign (evalB_bin (op:=.add)
          (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by simp only [List.length_cons] at hB; omega)⟩)
          (evalB_lit (show 1< B by simp only [List.length_cons] at hB; omega))
          (by change front.length+1< B; simp only [List.length_cons] at hB; omega))
      have rr:Run B (step s) σ μ 7:=r1.seq r2
      obtain ⟨τ,r3,p3⟩:=ih (front++[v]) vs hnd.2 hss (by simp only [List.length_cons] at hlen; omega)
        (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hB ⊢; omega)
        (fun z hz => hv z (List.mem_cons_of_mem v hz)) μ
        ⟨by simpa only [Prefix,rr.frame_arr "recursion.frames" (by simp [step,Com.warrs]),List.append_assoc,List.singleton_append] using hp,
          by simp [μ]⟩
      have hsτ:τ.vars s=v:=(r3.frame_var s (variable_frame ss s hnd.1 hs)).trans
        ((r2.frame_var s (by simp [Com.wvars,hs])).trans (by simp [ν]))
      refine ⟨τ,(rr.seq r3).mono (by simp only [List.length_cons]; omega),?_,?_,?_⟩
      · simpa only [List.append_assoc,List.singleton_append] using p3.1
      · simpa only [NativeFrameScalars.words,List.map_cons,hsτ] using congrArg (List.cons v) p3.2.1
      · simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc,Nat.add_comm 1] using p3.2.2

end Lax263307Proofs.NativeFrameRestore

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem scalars_array (names:List String) (a:String):a∉(NativeFrameRestore.command names).warrs:=by
  induction names with
  | nil => simp [NativeFrameRestore.command,Com.warrs]
  | cons s ss ih => simp [NativeFrameRestore.command,NativeFrameRestore.step,Com.warrs,ih]

theorem buffers_variable (names:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):s∉(NativeFrameBuffers.save names).wvars:=by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

theorem scalar_values (names:List String) (σ τ:Env)
    (h:NativeFrameScalars.words names τ=NativeFrameScalars.words names σ):
    ∀ s∈names,τ.vars s=σ.vars s:=by
  induction names with
  | nil => simp
  | cons a as ih =>
    simp only [NativeFrameScalars.words,List.map_cons,List.cons.injEq] at h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 s hs

theorem save_spec (B S:ℕ) (arrays scalars:List String) (front:List ℕ)
    (ha:"recursion.frames"∉arrays)
    (hv:∀ s∈scalars,s∉["stack.i","stack.copy.length","stack.words"])
    (hB:front.length+S*arrays.length+scalars.length+2< B):
    Spec B (fun σ => NativeStateBounds.Bounded B σ∧ Prefix front "recursion.frames" σ∧
      σ.vars "stack.words"=front.length∧ σ.vars "recursion.stride"=S∧
      (∀ a∈arrays,(σ.arrs a).length=S)∧
      front.length+S*arrays.length+scalars.length≤(σ.arrs "recursion.frames").length)
      (save arrays scalars) (fun σ τ => NativeStateBounds.Bounded B τ∧
        Prefix (front++words arrays scalars σ) "recursion.frames" τ∧
        τ.vars "stack.words"=front.length+S*arrays.length+scalars.length)
      ((16*S+8)*arrays.length+7*scalars.length+2):=by
  rintro σ ⟨hd,hp,hi,hs,he,hr⟩
  obtain ⟨ν,r1,p1⟩:=NativeFrameBuffers.save_spec B S arrays front ha (by omega) σ
    ⟨hd,hp,hi,hs,he,by omega⟩
  have hlen:=NativeFrameBuffers.words_length arrays S σ he
  have hword:NativeFrameScalars.words scalars ν=NativeFrameScalars.words scalars σ:=by
    apply List.map_congr_left
    intro s hs
    exact r1.frame_var s (buffers_variable arrays s (hv s hs))
  have hn:"stack.words"∉scalars:=by
    intro h
    exact hv "stack.words" h (by simp)
  obtain ⟨τ,r2,p2⟩:=NativeFrameScalars.save_spec B scalars (front++NativeFrameBuffers.words arrays σ)
    hn (by simp only [List.length_append,hlen]; omega) ν
    ⟨p1.1,p1.2.1,by simpa only [List.length_append,hlen] using p1.2.2,
      by rw [RamFrames.run_array_length r1]; simp only [List.length_append,hlen]; omega⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1,?_,?_⟩
  · rw [hword] at p2
    simpa only [words,List.append_assoc] using p2.2.1
  · simpa only [List.length_append,hlen,Nat.add_assoc] using p2.2.2

theorem restore_spec (B S:ℕ) (arrays scalars:List String) (front:List ℕ) (saved:Env)
    (ha:"recursion.frames"∉arrays) (harrays:arrays.Nodup) (hscalars:scalars.Nodup)
    (hv:"stack.read.i"∉scalars) (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈arrays,(saved.arrs a).length=S)
    (hB:front.length+S*arrays.length+scalars.length+2< B):
    Spec B (fun σ => Prefix (front++words arrays scalars saved) "recursion.frames" σ∧
      σ.vars "stack.read.i"=front.length∧ σ.vars "recursion.stride"=S∧
      ∀ a∈arrays,(σ.arrs a).length=S) (restore arrays scalars)
      (fun _ τ => Prefix (front++words arrays scalars saved) "recursion.frames" τ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a)∧ (∀ s∈scalars,τ.vars s=saved.vars s)∧
        τ.vars "stack.read.i"=front.length+S*arrays.length+scalars.length)
      ((16*S+16)*arrays.length+7*scalars.length+2):=by
  rintro σ ⟨hp,hi,hs,he⟩
  have hlen:=NativeFrameBuffers.words_length arrays S saved hext
  have hvarslen:(NativeFrameScalars.words scalars saved).length=scalars.length:=by simp [NativeFrameScalars.words]
  have hfront:Prefix (front++NativeFrameBuffers.words arrays saved) "recursion.frames" σ:=
    NativeFrameBufferRestore.prefix_left _ _ _ _ (by simpa only [words,List.append_assoc] using hp)
  obtain ⟨ν,r1,p1⟩:=NativeFrameBufferRestore.command_spec B S arrays front saved harrays ha hsaved hext (by omega)
    σ ⟨hfront,hi,hs,he⟩
  have hframes:"recursion.frames"∉(NativeFrameBufferRestore.command arrays).warrs:=
    NativeFrameBufferRestore.array_frame arrays _ ha
  obtain ⟨τ,r2,p2⟩:=NativeFrameRestore.command_spec B scalars (front++NativeFrameBuffers.words arrays saved)
    (NativeFrameScalars.words scalars saved) hscalars hv hvarslen
    (by simp only [List.length_append,hlen,hvarslen]; omega)
    (by intro z hz; obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hz; exact hsaved.1 s) ν
    ⟨by simpa only [words,List.append_assoc,Prefix,r1.frame_arr "recursion.frames" hframes] using hp,
      by simpa only [List.length_append,hlen] using p1.2.2⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),?_,?_,scalar_values scalars saved τ p2.2.1,?_⟩
  · simpa only [words,List.append_assoc] using p2.1
  · intro a ha
    exact (r2.frame_arr a (scalars_array scalars a)).trans (p1.2.1 a ha)
  · simpa only [List.length_append,hlen,hvarslen,Nat.add_assoc] using p2.2.2

end Lax263307Proofs.NativeRecursionFrame

end

section

namespace Lax263307Proofs.NativeChildActivate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem setup_spec (B r:ℕ) (hB:r*r+r+3< B):
    Spec B (fun σ => σ.vars "restrict.count"=r) setup
      (fun _ τ => τ.vars "fill.length"=r*r∧ τ.vars "slice.start"=0∧ τ.vars "restrict.count"=r) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 r r; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "fill.length") c1) (And (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))) (@Eq Nat (Env.vars τ "restrict.count") r))) σ; let c3:Nat:=c0 (Env.vars σ "restrict.count") (Env.vars σ "restrict.count"); let c4:Env:=Env.setVar σ "fill.length" c3; let c5:Env:=Env.setVar c4 "slice.start" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.mul (Expr.var "restrict.count") (Expr.var "restrict.count"))); let c9:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c10:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c2 σ')) c5 (@And.intro (Run B setup σ c5 ((6:Nat))) (c2 c5) (RunStep.mono B setup σ c5 (c6 c8 c9) ((6:Nat)) (RunStep.seq B (Com.assign "fill.length" (Expr.mul (Expr.var "restrict.count") (Expr.var "restrict.count"))) (Com.assign "slice.start" (Expr.lit ((0:Nat)))) σ c4 c5 c8 c9 (RunStep.assign B σ "fill.length" (Expr.mul (Expr.var "restrict.count") (Expr.var "restrict.count")) c3 (RunStep.eval_mul B σ (Expr.var "restrict.count") (Expr.var "restrict.count") (Env.vars σ "restrict.count") (Env.vars σ "restrict.count") (RunStep.eval_var B σ "restrict.count" (?nAX_g9084_0_0_0)) (RunStep.eval_var B σ "restrict.count" (?nAX_g9084_0_0_1)) ?_)) (RunStep.assign B c4 "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g9084_0_0_2)))) (?nAX_g9084_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9084_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9084_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9084_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9084_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar] <;> omega

theorem command_spec (B r:ℕ) (G:SimpleGraph (Fin r)) [DecidableRel G.Adj] (hB:r*r+r+3< B):
    Spec B (fun σ => Prefix (NativeWeightReduction.adjacency G) "child.graph" σ∧
      σ.vars "restrict.count"=r∧ r*r≤(σ.arrs "search.graph").length) command
      (fun _ τ => Prefix (NativeWeightReduction.adjacency G) "search.graph" τ∧ τ.vars "graph.n"=r)
      (16*(r*r)+14):=by
  let xs:=NativeWeightReduction.adjacency G
  have hlen:xs.length=r*r:=NativeWeightReduction.adjacency_length G
  have hwords:∀ z∈xs,z< B:=by
    intro z hz
    obtain ⟨row,hrow,hz⟩:=List.mem_flatten.mp hz
    obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hrow
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hz
    split_ifs <;> omega
  rintro σ ⟨hg,hr,hroom⟩
  obtain ⟨ν,r1,p1⟩:=setup_spec B r hB σ hr
  obtain ⟨μ,r2,p2⟩:=NativeSlice.command_spec B "child.graph" "search.graph" [] xs [] (by decide)
    (by simp [hlen]; omega) hwords ν
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,r1.frame_arr "child.graph" (by decide)] using hg,
      by simpa only [List.length_nil] using p1.2.1⟩,
      by simpa only [hlen] using p1.1,by simpa only [hlen,RamFrames.run_array_length r1] using hroom⟩
  have hr2:=(r2.frame_var "restrict.count" (by decide)).trans p1.2.2
  let τ:=μ.setVar "graph.n" r
  have r3:Run B (.assign "graph.n" (.var "restrict.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hr2.symm,hr2 ▸ (by omega:r< B)⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]; omega),
    by simpa only [Prefix,τ,arrs_setVar] using p2.2,by simp [τ]⟩

end Lax263307Proofs.NativeChildActivate

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

theorem save_array (arrays scalars:List String) (a:String) (ha:a≠"recursion.frames"):
    a∉(NativeRecursionFrame.save arrays scalars).warrs:=by
  have hs:a∉(NativeFrameScalars.save scalars).warrs:=by
    induction scalars with
    | nil => simp [NativeFrameScalars.save,Com.warrs]
    | cons s ss ih => simp [NativeFrameScalars.save,RamWordBuffer.append,Com.warrs,ha,ih]
  simpa only [NativeRecursionFrame.save,Com.warrs,List.mem_append,not_or] using
    And.intro (NativeFrameBuffers.array_frame arrays a ha) hs

theorem enter_spec (B target fuel entry:ℕ) (hB:target+fuel+entry+3< B):
    Spec B (fun σ => σ.vars "component.target"=target∧ σ.vars "recursion.fuel"=fuel+1) (enter entry)
      (fun _ τ => τ.vars "node.k"=target∧ τ.vars "recursion.fuel"=fuel∧ τ.vars "machine.phase"=entry) 8:=by
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "node.k") target) (And (@Eq Nat (Env.vars τ "recursion.fuel") fuel) (@Eq Nat (Env.vars τ "machine.phase") entry))) σ; let c1:Nat:=Env.vars (Env.setVar σ "node.k" (Env.vars σ "component.target")) "recursion.fuel"; let c2:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c1 ((1:Nat)); let c3:Env:=Env.setVar (Env.setVar σ "node.k" (Env.vars σ "component.target")) "recursion.fuel" c2; let c4:Env:=Env.setVar c3 "machine.phase" entry; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "component.target")); let c8:Expr:=Expr.sub (Expr.var "recursion.fuel") (Expr.lit ((1:Nat))); let c9:Nat:=c6 (Expr.size c8); let c10:Nat:=c6 (Expr.size (Expr.lit entry)); let c11:Nat:=c5 c9 c10; let c12:Com:=Com.assign "recursion.fuel" c8; let c13:String→ Nat:=Env.vars c4; @Exists.intro Env (fun (σ':Env) => And (Run B (enter entry) σ σ' ((8:Nat))) (c0 σ')) c4 (@And.intro (Run B (enter entry) σ c4 ((8:Nat))) (c0 c4) (RunStep.mono B (enter entry) σ c4 (c5 c7 c11) ((8:Nat)) (RunStep.seq B (Com.assign "node.k" (Expr.var "component.target")) (Com.seq c12 (Com.assign "machine.phase" (Expr.lit entry))) σ (Env.setVar σ "node.k" (Env.vars σ "component.target")) c4 c7 c11 (RunStep.assign B σ "node.k" (Expr.var "component.target") (Env.vars σ "component.target") (RunStep.eval_var B σ "component.target" (?nAX_g9089_0_0_0))) (RunStep.seq B c12 (Com.assign "machine.phase" (Expr.lit entry)) (Env.setVar σ "node.k" (Env.vars σ "component.target")) c3 c4 c9 c10 (RunStep.assign B (Env.setVar σ "node.k" (Env.vars σ "component.target")) "recursion.fuel" c8 c2 (RunStep.eval_sub B (Env.setVar σ "node.k" (Env.vars σ "component.target")) (Expr.var "recursion.fuel") (Expr.lit ((1:Nat))) c1 ((1:Nat)) (RunStep.eval_var B (Env.setVar σ "node.k" (Env.vars σ "component.target")) "recursion.fuel" (?nAX_g9089_0_0_1)) (RunStep.eval_lit B ((1:Nat)) (Env.setVar σ "node.k" (Env.vars σ "component.target")) (?nAX_g9089_0_0_2)) (?nAX_g9089_0_0_3))) (RunStep.assign B c3 "machine.phase" (Expr.lit entry) entry (RunStep.eval_lit B entry c3 (?nAX_g9089_0_0_4))))) (?nAX_g9089_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9089_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9089_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9089_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9089_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9089_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9089_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem command_spec (B S r target fuel entry continuation:ℕ) (G:SimpleGraph (Fin r)) [DecidableRel G.Adj]
    (arrays scalars:List String) (front:List ℕ)
    (ha:"recursion.frames"∉arrays)
    (hv:∀ s∈scalars,s∉["stack.i","stack.copy.length","stack.words"])
    (hB:front.length+S*arrays.length+scalars.length+r*r+r+target+fuel+entry+continuation+10< B):
    Spec B (fun σ => NativeStateBounds.Bounded B σ∧ Prefix front "recursion.frames" σ∧
      σ.vars "stack.words"=front.length∧ σ.vars "recursion.stride"=S∧
      (∀ a∈arrays,(σ.arrs a).length=S)∧
      front.length+S*arrays.length+scalars.length≤(σ.arrs "recursion.frames").length∧
      Prefix (NativeWeightReduction.adjacency G) "child.graph" σ∧ σ.vars "restrict.count"=r∧
      r*r≤(σ.arrs "search.graph").length∧ σ.vars "component.target"=target∧ σ.vars "recursion.fuel"=fuel+1)
      (command arrays scalars entry continuation)
      (fun σ τ => Prefix (front++NativeRecursionFrame.words arrays scalars (σ.setVar "machine.phase" continuation))
          "recursion.frames" τ∧ τ.vars "stack.words"=front.length+S*arrays.length+scalars.length∧
        Prefix (NativeWeightReduction.adjacency G) "search.graph" τ∧ τ.vars "graph.n"=r∧
        τ.vars "node.k"=target∧ τ.vars "recursion.fuel"=fuel∧ τ.vars "machine.phase"=entry)
      ((16*S+8)*arrays.length+7*scalars.length+16*(r*r)+26):=by
  rintro σ ⟨hb,hfront,hwords,hstride,hext,hroom,hgraph,hr,hgraphroom,ht,hfuel⟩
  let ν:=σ.setVar "machine.phase" continuation
  have r0:Run B (.assign "machine.phase" (.lit continuation)) σ ν 2:=
    Run.assign (evalB_lit (show continuation< B by omega))
  obtain ⟨μ,r1,p1⟩:=NativeRecursionFrame.save_spec B S arrays scalars front ha hv (by omega) ν
    ⟨NativeStateBounds.run r0 hb,hfront,(r0.frame_var _ (by simp [Com.wvars])).trans hwords,
      (r0.frame_var _ (by simp [Com.wvars])).trans hstride,hext,hroom⟩
  have hgraph1:Prefix (NativeWeightReduction.adjacency G) "child.graph" μ:=by
    simpa only [Prefix,r1.frame_arr "child.graph" (save_array arrays scalars _ (by decide)),ν,arrs_setVar] using hgraph
  have hr1:μ.vars "restrict.count"=r:=
    (r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans hr)
  obtain ⟨ρ,r2,p2⟩:=NativeChildActivate.command_spec B r G (by omega) μ
    ⟨hgraph1,hr1,by rw [RamFrames.run_array_length (r0.seq r1)]; exact hgraphroom⟩
  have ht2:ρ.vars "component.target"=target:=(r2.frame_var _ (by decide)).trans
    ((r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans ht))
  have hf2:ρ.vars "recursion.fuel"=fuel+1:=(r2.frame_var _ (by decide)).trans
    ((r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans hfuel))
  obtain ⟨τ,r3,p3⟩:=enter_spec B target fuel entry (by omega) ρ ⟨ht2,hf2⟩
  refine ⟨τ,(r0.seq (r1.seq (r2.seq r3))).mono (by omega),?_,?_,?_,?_,p3⟩
  · simpa only [Prefix,(r2.seq r3).frame_arr "recursion.frames"
      (by simp [Com.warrs,enter,NativeChildActivate.command,NativeChildActivate.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append])] using p1.2.1
  · exact ((r2.seq r3).frame_var "stack.words" (by
      simp [Com.wvars,enter,NativeChildActivate.command,NativeChildActivate.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append])).trans p1.2.2
  · simpa only [Prefix,r3.frame_arr "search.graph" (by simp [enter,Com.warrs])] using p2.1
  · exact (r3.frame_var "graph.n" (by simp [enter,Com.wvars])).trans p2.2

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeStackReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def bufferScratch:List String:=
  ["stack.copy.length","fill.length","slice.start","fill.value","fill.i","stack.read.i"]

theorem buffers_variable (arrays:List String) (s:String) (hs:s∉bufferScratch):
    s∉(NativeFrameBufferRestore.command arrays).wvars:=by
  simp only [bufferScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
  induction arrays with
  | nil => simp [NativeFrameBufferRestore.command,Com.wvars]
  | cons a as ih =>
    simp [NativeFrameBufferRestore.command,NativeBlockRestore.command,NativeBlockRestore.setup,
      NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,
      RamWordBuffer.append,Com.wvars,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2,ih]

theorem restore_variable (arrays scalars:List String) (s:String)
    (hs:s∉bufferScratch) (hn:s∉scalars):s∉(NativeRecursionFrame.restore arrays scalars).wvars:=by
  have hr:s≠"stack.read.i" :=fun h => hs (by simp [bufferScratch,h])
  simpa only [NativeRecursionFrame.restore,Com.wvars,List.mem_append,not_or] using
    And.intro (buffers_variable arrays s hs) (NativeFrameRestore.variable_frame scalars s hn hr)

theorem pop_spec (B S:ℕ) (arrays scalars:List String) (front:List ℕ) (saved:Env)
    (ha:"recursion.frames"∉arrays) (harrays:arrays.Nodup) (hscalars:scalars.Nodup)
    (hv:"stack.read.i"∉scalars) (hw:"stack.words"∉scalars)
    (htag:"recursion.return.tag"∉scalars) (hmask:"recursion.return.mask"∉scalars)
    (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈arrays,(saved.arrs a).length=S)
    (hB:front.length+S*arrays.length+scalars.length+2< B):
    Spec B (fun σ => Prefix (front++NativeRecursionFrame.words arrays scalars saved) "recursion.frames" σ∧
      σ.vars "stack.words"=front.length+S*arrays.length+scalars.length∧
      σ.vars "frame.length"=S*arrays.length+scalars.length∧ σ.vars "recursion.stride"=S∧
      ∀ a∈arrays,(σ.arrs a).length=S) (pop arrays scalars)
      (fun σ τ => Prefix front "recursion.frames" τ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a)∧ (∀ s∈scalars,τ.vars s=saved.vars s)∧
        τ.vars "stack.words"=front.length∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
      ((16*S+16)*arrays.length+7*scalars.length+8):=by
  rintro σ ⟨hp,hwords,hlen,hstride,he⟩
  let ν:=σ.setVar "stack.words" front.length
  have r1:Run B (.assign "stack.words" (.sub (.var "stack.words") (.var "frame.length"))) σ ν 4:=by
    apply Run.assign
    have ew:(Expr.var "stack.words").evalB B σ=some (front.length+S*arrays.length+scalars.length):=by
      rw [evalB_var_iff]
      exact ⟨hwords.symm,hwords ▸ (by omega)⟩
    have el:(Expr.var "frame.length").evalB B σ=some (S*arrays.length+scalars.length):=by
      rw [evalB_var_iff]
      exact ⟨hlen.symm,hlen ▸ (by omega)⟩
    have hh:=evalB_bin (op:=.sub)
      ew el
      (by change front.length+S*arrays.length+scalars.length-(S*arrays.length+scalars.length)< B; omega)
    have heq:front.length+S*arrays.length+scalars.length-(S*arrays.length+scalars.length)=front.length:=by omega
    simpa only [Bop.apply_sub,heq] using hh
  let μ:=ν.setVar "stack.read.i" front.length
  have r2:Run B (.assign "stack.read.i" (.var "stack.words")) ν μ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨by simp [ν],by simp [ν]; omega⟩)
  obtain ⟨τ,r3,p3⟩:=NativeRecursionFrame.restore_spec B S arrays scalars front saved ha harrays hscalars hv hsaved hext hB μ
    ⟨hp,by simp [μ],(r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by decide)).trans hstride),
      by intro a ha; rw [RamFrames.run_array_length (r1.seq r2)]; exact he a ha⟩
  have rr:=(r1.seq r2).seq r3
  refine ⟨τ,rr.mono (by omega),NativeFrameBufferRestore.prefix_left _ _ _ _ p3.1,p3.2.1,p3.2.2.1,?_,?_,?_⟩
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) hw)).trans
      ((r2.frame_var _ (by decide)).trans (by simp [ν]))
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) htag)).trans ((r1.seq r2).frame_var _ (by decide))
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) hmask)).trans ((r1.seq r2).frame_var _ (by decide))

theorem child_spec (B S root:ℕ) (arrays scalars:List String) (front:List ℕ) (saved:Env)
    (ha:"recursion.frames"∉arrays) (harrays:arrays.Nodup) (hscalars:scalars.Nodup)
    (hv:"stack.read.i"∉scalars) (hw:"stack.words"∉scalars)
    (htag:"recursion.return.tag"∉scalars) (hmask:"recursion.return.mask"∉scalars)
    (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈arrays,(saved.arrs a).length=S)
    (hpos:0< front.length+S*arrays.length+scalars.length)
    (hB:front.length+S*arrays.length+scalars.length+2< B):
    Spec B (fun σ => Prefix (front++NativeRecursionFrame.words arrays scalars saved) "recursion.frames" σ∧
      σ.vars "stack.words"=front.length+S*arrays.length+scalars.length∧
      σ.vars "frame.length"=S*arrays.length+scalars.length∧ σ.vars "recursion.stride"=S∧
      ∀ a∈arrays,(σ.arrs a).length=S) (command arrays scalars root)
      (fun σ τ => Prefix front "recursion.frames" τ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a)∧ (∀ s∈scalars,τ.vars s=saved.vars s)∧
        τ.vars "stack.words"=front.length∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
      ((16*S+16)*arrays.length+7*scalars.length+12):=by
  intro σ hσ
  obtain ⟨τ,rr,hτ⟩:=pop_spec B S arrays scalars front saved ha harrays hscalars hv hw htag hmask
    hsaved hext hB σ hσ
  have hc:(Cond.eq (.var "stack.words") (.lit 0)).evalB B σ=some false:=by
    have hh:=evalB_condEq
      (show (Expr.var "stack.words").evalB B σ=some (front.length+S*arrays.length+scalars.length) by
        rw [evalB_var_iff]; exact ⟨hσ.2.1.symm,hσ.2.1 ▸ (by omega)⟩)
      (evalB_lit (show 0< B by omega))
    have hz:(front.length+S*arrays.length+scalars.length == 0)=false:=by
      exact beq_eq_false_iff_ne.mpr (by omega)
    simpa only [hz] using hh
  exact ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit root)) hc rr).mono
    (by simp [Cond.size,Expr.size]; omega),hτ⟩

end Lax263307Proofs.NativeStackReturn

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

namespace Lax263307Proofs.NativeCoreMachine

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem arrays_nodup (cfg:Config):(frameArrays cfg).Nodup:=by
  apply List.Nodup.filter
  exact List.nodup_dedup _

theorem scalars_nodup (cfg:Config):(frameScalars cfg).Nodup:=by
  apply List.Nodup.filter
  exact List.nodup_dedup _

theorem frames_not_saved (cfg:Config):"recursion.frames"∉frameArrays cfg:=by
  simp [frameArrays]

theorem scalar_not_saved (cfg:Config) (s:String) (hs:s∈excludedScalars):s∉frameScalars cfg:=by
  simp [frameScalars,hs]

theorem scalar_saved (cfg:Config) (s:String) (c:Com)
    (hc:c∈cases cfg [] []) (hs:s∈c.wvars) (he:s∉excludedScalars):s∈frameScalars cfg:=by
  simp only [frameScalars,List.mem_filter,List.mem_dedup,decide_eq_true_eq]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,hs⟩,he⟩

theorem phase_saved (cfg:Config):"machine.phase"∈frameScalars cfg:=by
  exact scalar_saved cfg _ rootTarget (by simp [cases])
    (by simp [rootTarget,emptyRoot,go,Com.wvars]) (by decide)

theorem running_saved (cfg:Config):"machine.running"∈frameScalars cfg:=by
  exact scalar_saved cfg _ rootTarget (by simp [cases])
    (by simp [rootTarget,emptyRoot,go,Com.wvars]) (by decide)

end Lax263307Proofs.NativeCoreMachine

end

section

namespace Lax263307Proofs.NativeComponentTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic NativeMasks

theorem child_some_segment {n:ℕ} (B i:ℕ) (cfg:Config) (C S:Finset (Fin n))
    (I:Finset (Fin C.card)) (hB:n+i+14< B) (hm:2^n< B) (σ:Env)
    (hd:σ.vars "recursion.return.tag"=1∧ σ.vars "graph.n"=n∧
      σ.vars "restrict.count"=C.card∧ σ.vars "recursion.return.mask"=mask I∧
      Prefix (NativeRestrictionOrder.words C) "restrict.vertices" σ∧ C.card≤(σ.arrs "subset.bits").length∧
      σ.vars "component.i"=i∧ σ.vars "component.union"=mask S)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=12):
    ∃ τ,Segment B (phases cfg) 1 (45*C.card+38) σ τ∧ τ.vars "graph.n"=n∧
      τ.vars "component.i"=i+1∧ τ.vars "component.union"=mask (S∪I.image (ComputedSeparators.label C))∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=9:=by
  obtain ⟨τ,rr,po⟩:=NativeComponentControl.child_some_spec B i 9 13 C S I hB hm σ hd
  exact ⟨τ,NativeMachineSegment.phase hr ⟨12,by change 12<16; decide⟩ hp rr,
    po.1,po.2.1,po.2.2.1,(rr.frame_var _ (by decide)).trans hr,po.2.2.2⟩

theorem child_none_segment {n:ℕ} (B r:ℕ) (cfg:Config) (A C:Finset (Fin n)) (t:ℕ)
    (hB:n+t+3*NativeCatalogMetadata.N n r+23< B) (hm:2^n< B) (σ:Env)
    (hd:σ.vars "recursion.return.tag"=0∧ NativeComponentNormal.Data r A C t σ∧
      NativeArrayBounds.Bounded B σ∧ 3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=12):
    ∃ τ,Segment B (phases cfg) 1 ((28*n+104)*NativeCatalogMetadata.N n r+30) σ τ∧
      Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
        (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=13:=by
  obtain ⟨τ,rr,po⟩:=NativeComponentControl.child_none_spec B r 9 13 A C t hB hm σ hd
  exact ⟨τ,NativeMachineSegment.phase hr ⟨12,by change 12<16; decide⟩ hp rr,
    po.1,(rr.frame_var _ (by decide)).trans hr,po.2⟩

end Lax263307Proofs.NativeComponentTrace

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

theorem child_segment {n:ℕ} (B S:ℕ) (cfg:Config)
    (front:List ℕ) (saved:Env) (answer:Option (Finset (Fin n)))
    (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈frameArrays cfg,(saved.arrs a).length=S)
    (hB:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+2< B)
    (hr:saved.vars "machine.running"=1) (hp:saved.vars "machine.phase"=12)
    (σ:Env) (h:NativeRoundTrace.Stopped answer σ)
    (hs:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" σ∧
      σ.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length∧
      σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length∧ σ.vars "recursion.stride"=S∧
      ∀ a∈frameArrays cfg,(σ.arrs a).length=S):
    ∃ τ,Segment B (phases cfg) 1
      ((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12) σ τ∧
      Prefix front "recursion.frames" τ∧
      (∀ a∈frameArrays cfg,τ.arrs a=saved.arrs a)∧
      (∀ s∈frameScalars cfg,τ.vars s=saved.vars s)∧ τ.vars "stack.words"=front.length∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=12∧ NativeTargetDriver.Reply answer τ:=by
  have hlen:0<(frameScalars cfg).length:=List.length_pos_of_mem (phase_saved cfg)
  obtain ⟨τ,rr,po⟩:=NativeStackReturn.child_spec B S 15 (frameArrays cfg) (frameScalars cfg) front saved
    (frames_not_saved cfg) (arrays_nodup cfg) (scalars_nodup cfg)
    (scalar_not_saved cfg _ (by decide)) (scalar_not_saved cfg _ (by decide))
    (scalar_not_saved cfg _ (by decide)) (scalar_not_saved cfg _ (by decide)) hsaved hext (by omega) hB σ hs
  exact ⟨τ,NativeMachineSegment.phase h.1 ⟨14,by change 14<16; decide⟩ h.2.1 rr,
    po.1,po.2.1,po.2.2.1,po.2.2.2.1,(po.2.2.1 _ (running_saved cfg)).trans hr,
    (po.2.2.1 _ (phase_saved cfg)).trans hp,
    reply_transfer answer po.2.2.2.2.1 po.2.2.2.2.2 h.2.2⟩

end Lax263307Proofs.NativeReturnTrace

end

section

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

theorem scalar {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (s:String)
    (hs:∀ c∈cases,s∉c.wvars):τ.vars s=σ.vars s:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (rr.frame_var s (hs _ (List.getElem_mem j.isLt)))

theorem array {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (a:String)
    (ha:∀ c∈cases,a∉c.warrs):τ.arrs a=σ.arrs a:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (rr.frame_arr a (ha _ (List.getElem_mem j.isLt)))

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCoreFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine NativeMachineSegment

theorem array_saved (cfg:Config) (a:String) (c:Com)
    (hc:c∈cases cfg [] []) (ha:a∈c.warrs) (he:a≠"recursion.frames"):a∈frameArrays cfg:=by
  simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,ha⟩,he⟩

theorem scratch_covered (cfg:Config) (s:String) (hs:s∈NativeStackReturn.bufferScratch):
    s∈frameScalars cfg∨ s∈excludedScalars:=by
  have hprep:∀ s∈["fill.length","slice.start","fill.value","fill.i"],
      s∈NativeProjectionPrepare.command.wvars:=by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> decide
  have hsave (s:String) (hs:s∈["fill.length","slice.start","fill.value","fill.i"])
      (he:s∉excludedScalars):s∈frameScalars cfg:=by
    apply scalar_saved cfg s
      (.seq NativeProjectionPrepare.command (.seq (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (go 5)))
    · simp [cases]
    · exact List.mem_append_left _ (hprep s hs)
    · exact he
  simp only [NativeStackReturn.bufferScratch,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr (by decide)
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inr (by decide)

theorem scalar_unwritten (cfg:Config) (s:String) (hs:s∉frameScalars cfg)
    (he:s∉excludedScalars):∀ c∈phases cfg,s∉c.wvars:=by
  have hb (c:Com) (hc:c∈cases cfg [] []):s∉c.wvars:=
    fun hw => hs (scalar_saved cfg s c hc hw he)
  have hsave:s∉(NativeRecursionFrame.save (frameArrays cfg) (frameScalars cfg)).wvars:=by
    apply NativeChildCall.save_variable
    intro h
    apply he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> decide
  have hrestore:s∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).wvars:=
    NativeStackReturn.restore_variable _ _ s
      (fun h => (scratch_covered cfg s h).elim hs he) hs
  have hc:=hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht:=hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.wvars,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.wvars,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.wvars,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

theorem array_unwritten (cfg:Config) (a:String) (ha:a∉frameArrays cfg)
    (he:a≠"recursion.frames"):∀ c∈phases cfg,a∉c.warrs:=by
  have hb (c:Com) (hc:c∈cases cfg [] []):a∉c.warrs:=
    fun hw => ha (array_saved cfg a c hc hw he)
  have hsave:=NativeChildCall.save_array (frameArrays cfg) (frameScalars cfg) a he
  have hrestore:a∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).warrs:=by
    simpa only [NativeRecursionFrame.restore,Com.warrs,List.mem_append,not_or] using
      And.intro (NativeFrameBufferRestore.array_frame _ a ha) (NativeRecursionFrame.scalars_array _ a)
  have hc:=hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht:=hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.warrs,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.warrs,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.warrs,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

theorem segment_scalar {B steps total:ℕ} {cfg:Config} {σ τ:Env}
    (trace:Segment B (phases cfg) steps total σ τ) (s:String)
    (hs:s∉frameScalars cfg) (he:s∉excludedScalars):τ.vars s=σ.vars s:=
  NativeMachineFrame.scalar trace s (scalar_unwritten cfg s hs he)

theorem segment_array {B steps total:ℕ} {cfg:Config} {σ τ:Env}
    (trace:Segment B (phases cfg) steps total σ τ) (a:String)
    (ha:a∉frameArrays cfg) (he:a≠"recursion.frames"):τ.arrs a=σ.arrs a:=
  NativeMachineFrame.array trace a (array_unwritten cfg a ha he)

theorem parent_restored {B steps total prepTime:ℕ} {cfg:Config} {σ saved τ:Env}
    (snapshot:Run B (Com.seq NativeChildGraph.command (go 12)) σ saved prepTime)
    (trace:Segment B (phases cfg) steps total σ τ)
    (hv:∀ s∈frameScalars cfg,τ.vars s=saved.vars s)
    (ha:∀ a∈frameArrays cfg,τ.arrs a=saved.arrs a):
    (∀ s,s∉excludedScalars→ τ.vars s=saved.vars s)∧
      (∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a):=by
  constructor
  · intro s he
    by_cases hs:s∈frameScalars cfg
    · exact hv s hs
    · have hw:=scalar_unwritten cfg s hs he
        (Com.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12))
        (by simp [phases,cases])
      simp only [NativeChildCall.command,Com.wvars,List.mem_append,not_or] at hw
      have hp:s∉(Com.seq NativeChildGraph.command (go 12)).wvars:=by
        simpa only [go,Com.wvars,List.mem_append,not_or] using And.intro hw.1 hw.2.1
      exact (segment_scalar trace s hs he).trans (snapshot.frame_var s hp).symm
  · intro a he
    by_cases hs:a∈frameArrays cfg
    · exact ha a hs
    · have hw:=array_unwritten cfg a hs he
        (Com.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12))
        (by simp [phases,cases])
      simp only [NativeChildCall.command,Com.warrs,List.mem_append,not_or] at hw
      have hp:a∉(Com.seq NativeChildGraph.command (go 12)).warrs:=by
        simpa only [go,Com.warrs,List.mem_append,not_or] using And.intro hw.1 hw.2.1
      exact (segment_array trace a hs he).trans (snapshot.frame_arr a hp).symm

end Lax263307Proofs.NativeCoreFrame

end

section

namespace Lax263307Proofs.NativeChildTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment

theorem call_segment {n:ℕ} (B S target fuel:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ) (C:Finset (Fin n))
    (front:List ℕ)
    (hB:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+n+target+fuel+23< B)
    (σ:Env) (hb:NativeStateBounds.Bounded B σ) (hd:NativeRestrictionRead.Data G x C σ)
    (hfront:Prefix front "recursion.frames" σ) (hwords:σ.vars "stack.words"=front.length)
    (hstride:σ.vars "recursion.stride"=S) (hext:∀ a∈frameArrays cfg,(σ.arrs a).length=S)
    (hstack:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤(σ.arrs "recursion.frames").length)
    (hchild:C.card*C.card≤(σ.arrs "child.graph").length)
    (hsearch:C.card*C.card≤(σ.arrs "search.graph").length)
    (ht:σ.vars "component.target"=target) (hf:σ.vars "recursion.fuel"=fuel+1)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=11):
    ∃ saved τ,Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12)∧
      NativeStateBounds.Bounded B saved∧ saved.vars "machine.running"=1∧ saved.vars "machine.phase"=12∧
      Segment B (phases cfg) 1
        ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) σ τ∧
      Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" τ∧
      τ.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length∧
      Prefix (NativeWeightReduction.adjacency (restriction G C)) "search.graph" τ∧
      τ.vars "graph.n"=C.card∧ τ.vars "node.k"=target∧ τ.vars "recursion.fuel"=fuel∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=1:=by
  have hc:C.card≤ n:=NativeMaskUnpack.card_bound C
  have hsq:C.card*C.card≤ n*n:=Nat.mul_self_le_mul_self hc
  obtain ⟨ν,r1,p1⟩:=NativeChildGraph.command_spec B n G x C (by omega) σ ⟨hd,hchild⟩
  have hv:∀ s∈frameScalars cfg,s∉["stack.i","stack.copy.length","stack.words"]:=by
    intro s hs he
    apply scalar_not_saved cfg s _ hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> decide
  obtain ⟨τ,r2,p2⟩:=NativeChildCall.command_spec B S C.card target fuel 1 12 (restriction G C)
    (frameArrays cfg) (frameScalars cfg) front (frames_not_saved cfg) hv (by omega) ν
    ⟨NativeStateBounds.run r1 hb,
      by simpa only [Prefix,r1.frame_arr "recursion.frames" (by decide)] using hfront,
      (r1.frame_var _ (by decide)).trans hwords,(r1.frame_var _ (by decide)).trans hstride,
      by intro a ha; rw [RamFrames.run_array_length r1]; exact hext a ha,
      by simpa only [RamFrames.run_array_length r1] using hstack,p1.2,p1.1.count,
      by simpa only [RamFrames.run_array_length r1] using hsearch,
      (r1.frame_var _ (by decide)).trans ht,(r1.frame_var _ (by decide)).trans hf⟩
  let saved:=ν.setVar "machine.phase" 12
  have rsave:Run B (go 12) ν saved 2:=Run.assign (evalB_lit (show 12< B by omega))
  have snapshot:Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12):=
    (r1.seq rsave).mono (by omega)
  have running1:ν.vars "machine.running"=1:=(r1.frame_var _ (by decide)).trans hr
  have running2:"machine.running"∉(NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12).wvars:=by
    simp only [NativeChildCall.command,Com.wvars,List.mem_append,not_or]
    exact ⟨by decide,NativeChildCall.save_variable _ _ _ (by decide),by decide,by decide⟩
  have run:Run B (.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12)) σ τ
      ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36):=
    (r1.seq r2).mono (by omega)
  exact ⟨saved,τ,snapshot,NativeStateBounds.run snapshot hb,(rsave.frame_var _ (by decide)).trans running1,
    by simp [saved],NativeMachineSegment.phase hr ⟨11,by change 11<16; decide⟩ hp run,
    p2.1,p2.2.1,p2.2.2.1,p2.2.2.2.1,p2.2.2.2.2.1,p2.2.2.2.2.2.1,
    (r2.frame_var _ running2).trans running1,p2.2.2.2.2.2.2⟩

end Lax263307Proofs.NativeChildTrace

end

section

namespace Lax263307Proofs.NativeChildExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem returned_segment {n:ℕ} (B S:ℕ) (cfg:Config)
    (front:List ℕ) (parent saved entry done:Env) (answer:Option (Finset (Fin n)))
    (callSteps callTime childSteps childTime prepTime:ℕ)
    (snapshot:Run B (.seq NativeChildGraph.command (go 12)) parent saved prepTime)
    (hsaved:NativeStateBounds.Bounded B saved)
    (hext:∀ a∈frameArrays cfg,(saved.arrs a).length=S)
    (hB:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+2< B)
    (hr:saved.vars "machine.running"=1) (hp:saved.vars "machine.phase"=12)
    (call:Segment B (phases cfg) callSteps callTime parent entry)
    (recursive:Segment B (phases cfg) childSteps childTime entry done)
    (reply:NativeRoundTrace.Stopped answer done)
    (hstack:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" done∧
      done.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length∧
      done.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length∧ done.vars "recursion.stride"=S):
    ∃ τ,Segment B (phases cfg) (callSteps+childSteps+1)
      (callTime+childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)) parent τ∧
      Prefix front "recursion.frames" τ∧ τ.vars "stack.words"=front.length∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=12∧ NativeTargetDriver.Reply answer τ∧
      (∀ s,s∉excludedScalars→ τ.vars s=saved.vars s)∧
      (∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a):=by
  have before:=NativeMachineSegment.append call recursive
  have extDone:∀ a∈frameArrays cfg,(done.arrs a).length=S:=by
    intro a ha
    have hlen:=NativeMachineFrame.array_length before a
    have hprep:=RamFrames.run_array_length snapshot a
    rw [hlen,←hprep]
    exact hext a ha
  obtain ⟨τ,ret,hfront,ha,hv,hwords,hr',hp',hreply⟩:=NativeReturnTrace.child_segment B S cfg front saved answer
    hsaved hext hB hr hp done reply ⟨hstack.1,hstack.2.1,hstack.2.2.1,hstack.2.2.2,extDone⟩
  have whole:=NativeMachineSegment.append before ret
  have restored:=NativeCoreFrame.parent_restored snapshot whole hv ha
  exact ⟨τ,whole,hfront,hwords,hr',hp',hreply,restored⟩

end Lax263307Proofs.NativeChildExecution

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

namespace Lax263307Proofs.NativeCollectionAnchor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine

theorem refl (σ:Env):Anchor σ σ:= ⟨fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {base σ τ:Env} (h:Anchor base σ) (hnext:Anchor σ τ):Anchor base τ:=
  ⟨fun s hs => (hnext.1 s hs).trans (h.1 s hs),
    fun a ha => (hnext.2 a ha).trans (h.2 a ha)⟩

theorem frame {B K:ℕ} {c:Com} {base σ τ:Env} (rr:Run B c σ τ K)
    (hc:Anchor base σ) (hv:∀ s∈c.wvars,s∈workScalars)
    (ha:∀ a∈c.warrs,a∈workArrays):Anchor base τ:=by
  constructor
  · intro s hs
    exact (rr.frame_var s (fun h => hs (hv s h))).trans (hc.1 s hs)
  · intro a ha'
    exact (rr.frame_arr a (fun h => ha' (ha a h))).trans (hc.2 a ha')

theorem restored {base saved τ:Env} (hc:Anchor base saved)
    (hv:∀ s,s∉excludedScalars→ τ.vars s=saved.vars s)
    (ha:∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a):Anchor base τ:=by
  constructor
  · intro s hs
    have he:s∉excludedScalars:=by
      intro h
      apply hs
      simp [workScalars,h]
    exact (hv s he).trans (hc.1 s hs)
  · intro a ha'
    have he:a≠"recursion.frames" :=by
      intro h
      apply ha'
      simp [workArrays,h]
    exact (ha a he).trans (hc.2 a ha')

end Lax263307Proofs.NativeCollectionAnchor

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCollectionContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

def scalars:List String:= ["graph.n","component.count","algorithm.D",
  "conditioning.k","catalog.count","conditioning.choice","stack.words",
  "recursion.stride","recursion.fuel"]
def arrays:List String:= ["search.graph","near.costs","separator.pieces",
  "catalog.mask","recursion.frames"]

theorem frame_order {n B D k r fuel stride K:ℕ}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {x:Fin n→ ℚ≥0}
    {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    {extent:String→ ℕ} {front:List ℕ} {σ τ:Env} {c:Com}
    (rr:Run B c σ τ K) (hc:Context B D k r fuel stride G x parts A extent front σ)
    (hn:τ.vars "graph.n"=n)
    (hv:∀ s∈scalars,s≠"graph.n" → s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r fuel stride G x parts A extent front τ:=by
  refine ⟨hn,?_,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.count,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.denominator,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.target,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.dimension,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.conditioning,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.width,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.depth⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp [arrays]))] using hc.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp [arrays]))] using hc.costs
  · simpa only [Prefix,rr.frame_arr "separator.pieces" (ha _ (by simp [arrays]))] using hc.pieces
  · simpa only [Prefix,rr.frame_arr "catalog.mask" (ha _ (by simp [arrays]))] using hc.catalog
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" (ha _ (by simp [arrays]))] using hc.stack

theorem frame {n B D k r fuel stride K:ℕ}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {x:Fin n→ ℚ≥0}
    {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    {extent:String→ ℕ} {front:List ℕ} {σ τ:Env} {c:Com}
    (rr:Run B c σ τ K) (hc:Context B D k r fuel stride G x parts A extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r fuel stride G x parts A extent front τ:=by
  exact frame_order rr hc ((rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.order)
    (fun s hs _ => hv s hs) ha

theorem restored {n B D k r fuel stride steps total:ℕ}
    {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x:Fin n→ ℚ≥0} {parts:List (Finset (Fin n))} {A:Finset (Fin n)}
    {extent:String→ ℕ} {front:List ℕ} {parent saved τ:Env}
    (hc:Context B D k r fuel stride G x parts A extent front saved)
    (trace:Segment B (phases cfg) steps total parent τ)
    (hparent:NativeStateBounds.Bounded B parent)
    (hlength:∀ a,(parent.arrs a).length=extent a)
    (hv:∀ s,s∉excludedScalars→ τ.vars s=saved.vars s)
    (ha:∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a)
    (hfront:Prefix front "recursion.frames" τ) (hcursor:τ.vars "stack.words"=front.length):
    Context B D k r fuel stride G x parts A extent front τ:=by
  refine ⟨(hv _ (by decide)).trans hc.order,?_,?_,?_,
    (hv _ (by decide)).trans hc.count,(hv _ (by decide)).trans hc.denominator,
    (hv _ (by decide)).trans hc.target,(hv _ (by decide)).trans hc.dimension,?_,
    (hv _ (by decide)).trans hc.conditioning,NativeMachineBounds.state trace hparent,
    ?_,hfront,hcursor,(hv _ (by decide)).trans hc.width,(hv _ (by decide)).trans hc.depth⟩
  · simpa only [Prefix,ha "search.graph" (by decide)] using hc.graph
  · simpa only [Prefix,ha "near.costs" (by decide)] using hc.costs
  · simpa only [Prefix,ha "separator.pieces" (by decide)] using hc.pieces
  · simpa only [Prefix,ha "catalog.mask" (by decide)] using hc.catalog
  · intro a; rw [NativeMachineFrame.array_length trace]; exact hlength a

end Lax263307Proofs.NativeCollectionContext

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCollectionChild

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext

private theorem none_order {B K:ℕ} {σ τ:Env}
    (rr:Run B (NativeComponentControl.childReply 9 13) σ τ K)
    (hB:1< B) (htag:σ.vars "recursion.return.tag"=0):
    τ.vars "graph.n"=σ.vars "graph.n" :=by
  have ht:(Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some false:=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega)⟩)
      (evalB_lit hB)
  obtain ⟨cost,hcost,step⟩:=rr
  cases step with
  | ite_true he _ => rw [ht] at he; cases he
  | ite_false _ step =>
    have r:Run B (NativeOracleCut.failedChild 13) σ τ _:= ⟨_,Nat.le_refl _,step⟩
    exact r.frame_var _ (by decide)

theorem child_iteration {n:ℕ} (B S D k r fuel i target childSteps childTime:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
    (parts:List (Finset (Fin n))) (A C U:Finset (Fin n))
    (extent:String→ ℕ) (front:List ℕ) (answer:Option (Finset (Fin C.card)))
    (hB:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+
      n*n+n+i+target+fuel+3*NativeCatalogMetadata.N n r+50< B)
    (hm:2^n< B) (hext:∀ a∈frameArrays cfg,extent a=S)
    (hstack:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤ extent "recursion.frames")
    (hchild:C.card*C.card≤ extent "child.graph") (hsearch:C.card*C.card≤ extent "search.graph")
    (hbits:C.card≤ extent "subset.bits")
    (hlp:3*NativeCatalogMetadata.N n r≤ extent "lp.input")
    (hnormal:3*NativeCatalogMetadata.N n r≤ extent "round.normal")
    (σ:Env) (hc:Context B D k r fuel S G x parts A extent front σ)
    (hd:NativeRestrictionRead.Data G (fun v => (x v:ℚ)) C σ)
    (hmask:σ.vars "component.mask"=mask C) (htarget:σ.vars "component.target"=target)
    (hi:σ.vars "component.i"=i) (hu:σ.vars "component.union"=mask U)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=11)
    (recursive:Recursive B S fuel childSteps childTime cfg G C target front σ answer):
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ∧ steps≤ childSteps+3∧
      total≤((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36)+
        childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
        ((45*C.card+38)+((28*n+104)*NativeCatalogMetadata.N n r+30))∧
      NativeCollectionAnchor.Anchor σ τ∧
      match (generalizing:=false) answer with
      | some I => NativeCollectionTrace.At (Context B D k r fuel S G x parts A extent front)
          (i+1) (U∪I.image (ComputedSeparators.label C)) τ
      | none => NativeCollectionTrace.ResultOutput (Context B D k r fuel S G x parts A extent front)
          (fun C u τ => Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal
            (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))) "round.normal" τ)
          (.cut C (target-1)) τ:=by
  obtain ⟨saved,entry,snapshot,hsaved,rsaved,psaved,call,hfront,hwords,hgraph,horder,hk,hfuel,rentry,pentry⟩:=
    NativeChildTrace.call_segment B S target fuel cfg G (fun v => (x v:ℚ)) C front (by omega) σ
      hc.bounded hd hc.stack hc.cursor hc.width
      (by intro a ha; rw [hc.lengths]; exact hext a ha)
      (by rw [hc.lengths]; exact hstack) (by rw [hc.lengths]; exact hchild)
      (by rw [hc.lengths]; exact hsearch) htarget hc.depth hr hp
  have csaved:=NativeCollectionContext.frame snapshot hc (by decide) (by decide)
  obtain ⟨done,s,t,recur,hs,ht,reply,stackDone,wordsDone,lengthDone,strideDone⟩:=
    recursive saved entry snapshot call hfront hwords hgraph horder hk hfuel rentry pentry
  obtain ⟨ν,returned,frontν,wordsν,runningν,phaseν,replyν,varsν,arraysν⟩:=
    NativeChildExecution.returned_segment B S cfg front σ saved entry done answer 1
      ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) s t
      (36*(C.card*C.card)+12) snapshot hsaved
      (by intro a ha; rw [csaved.lengths]; exact hext a ha) (by omega) rsaved psaved call recur reply
      ⟨stackDone,wordsDone,lengthDone,strideDone⟩
  have savedAnchor:=NativeCollectionAnchor.frame snapshot (NativeCollectionAnchor.refl σ) (by decide) (by decide)
  have returnedAnchor:=NativeCollectionAnchor.restored savedAnchor varsν arraysν
  have cν:=NativeCollectionContext.restored csaved returned hc.bounded hc.lengths varsν arraysν frontν wordsν
  have indexν:ν.vars "component.i"=i:=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hi)
  have unionν:ν.vars "component.union"=mask U:=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hu)
  have maskν:ν.vars "component.mask"=mask C:=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hmask)
  have targetν:ν.vars "component.target"=target:=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans htarget)
  have countν:ν.vars "restrict.count"=C.card:=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hd.count)
  have labelsν:Prefix (NativeRestrictionOrder.words C) "restrict.vertices" ν:=by
    simpa only [Prefix,arraysν "restrict.vertices" (by decide),
      snapshot.frame_arr "restrict.vertices" (by decide)] using hd.labels
  cases answer with
  | some I =>
    obtain ⟨τ,last,orderτ,indexτ,unionτ,runningτ,phaseτ⟩:=NativeComponentTrace.child_some_segment B i cfg C U I
      (by omega) hm ν ⟨replyν.1,cν.order,countν,replyν.2,labelsν,
        by rw [cν.lengths]; exact hbits,indexν,unionν⟩ runningν phaseν
    have rr:=NativeMachineFrame.single_run last ⟨12,by change 12<16; decide⟩ phaseν
    change Run B (NativeComponentControl.childReply 9 13) ν τ _ at rr
    refine ⟨τ,_,_,NativeMachineSegment.append returned last,by omega,by omega,
      NativeCollectionAnchor.frame rr returnedAnchor (by decide) (by decide),
      NativeCollectionContext.frame_order rr cν orderτ (by decide) (by decide),indexτ,unionτ,runningτ,phaseτ⟩
  | none =>
    obtain ⟨τ,last,normalτ,runningτ,phaseτ⟩:=NativeComponentTrace.child_none_segment B r cfg A C target
      (by omega) hm ν ⟨replyν,⟨cν.order,cν.dimension,cν.catalog,cν.conditioning,maskν,targetν⟩,
        cν.bounded.2.1,by rw [cν.lengths]; exact hlp,by rw [cν.lengths]; exact hnormal⟩ runningν phaseν
    have rr:=NativeMachineFrame.single_run last ⟨12,by change 12<16; decide⟩ phaseν
    change Run B (NativeComponentControl.childReply 9 13) ν τ _ at rr
    refine ⟨τ,_,_,NativeMachineSegment.append returned last,by omega,by omega,
      NativeCollectionAnchor.frame rr returnedAnchor (by decide) (by decide),
      NativeCollectionContext.frame_order rr cν ((none_order rr (by omega) replyν).trans cν.order)
        (by decide) (by decide),runningτ,phaseτ,normalτ⟩

end Lax263307Proofs.NativeCollectionChild

end


theorem solution : ∀ {n : Nat} (B S D k r fuel i target childSteps childTime : Nat) (cfg : Lax263307Proofs.NativeCoreMachine.Config)
  (G : SimpleGraph (Fin n)) [inst : @DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x : Fin n → NNRat)
  (parts : List (Finset (Fin n))) (A C U : Finset (Fin n)) (extent : String → Nat) (front : List Nat)
  (answer : Option (Finset (Fin (@Finset.card (Fin n) C)))),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
                      (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                  n)
                i)
              target)
            fuel)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (Lax263307Proofs.NativeCatalogMetadata.N n r)))
        (@OfNat.ofNat Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      B →
    @LT.lt Nat instLTNat
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
        B →
      (∀ (a : String),
          @Membership.mem String (List String) (@List.instMembership String)
              (Lax263307Proofs.NativeCoreMachine.frameArrays cfg) a →
            @Eq Nat (extent a) S) →
        @LE.le Nat instLENat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@List.length Nat front)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) S
                  (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg))))
              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
            (extent "recursion.frames") →
          @LE.le Nat instLENat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))
              (extent "child.graph") →
            @LE.le Nat instLENat
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))
                (extent "search.graph") →
              @LE.le Nat instLENat (@Finset.card (Fin n) C) (extent "subset.bits") →
                @LE.le Nat instLENat
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (Lax263307Proofs.NativeCatalogMetadata.N n r))
                    (extent "lp.input") →
                  @LE.le Nat instLENat
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (Lax263307Proofs.NativeCatalogMetadata.N n r))
                      (extent "round.normal") →
                    ∀ (σ : Lax808846Proofs.Imp.Env),
                      @Lax263307Proofs.NativeCollectionContext.Context n B D k r fuel S G inst x parts A extent front
                          σ →
                        @Lax263307Proofs.NativeRestrictionRead.Data n G inst
                            (fun (v : Fin n) => @NNRat.cast Rat Rat.instNNRatCast (x v)) C σ →
                          @Eq Nat (σ.vars "component.mask") (@Lax263307Proofs.NativeMasks.mask n C) →
                            @Eq Nat (σ.vars "component.target") target →
                              @Eq Nat (σ.vars "component.i") i →
                                @Eq Nat (σ.vars "component.union") (@Lax263307Proofs.NativeMasks.mask n U) →
                                  @Eq Nat (σ.vars "machine.running")
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                                    @Eq Nat (σ.vars "machine.phase")
                                        (@OfNat.ofNat Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) →
                                      @Lax263307Proofs.NativeCollectionChild.Recursive n B S fuel childSteps childTime
                                          cfg G inst C target front σ answer →
                                        ∃ (τ : Lax808846Proofs.Imp.Env) (steps : Nat) (total : Nat),
                                          And
                                            (Lax263307Proofs.NativeMachineSegment.Segment B
                                              (Lax263307Proofs.NativeCoreMachine.phases cfg) steps total σ τ)
                                            (And
                                              (@LE.le Nat instLENat steps
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) childSteps
                                                  (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                              (And
                                                (@LE.le Nat instLENat total
                                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                    (@OfNat.ofNat Nat (nat_lit 16)
                                                                      (instOfNatNat (nat_lit 16)))
                                                                    S)
                                                                  (@OfNat.ofNat Nat (nat_lit 8)
                                                                    (instOfNatNat (nat_lit 8))))
                                                                (@List.length String
                                                                  (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@OfNat.ofNat Nat (nat_lit 7)
                                                                  (instOfNatNat (nat_lit 7)))
                                                                (@List.length String
                                                                  (Lax263307Proofs.NativeCoreMachine.frameScalars
                                                                    cfg))))
                                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                              (@OfNat.ofNat Nat (nat_lit 52)
                                                                (instOfNatNat (nat_lit 52)))
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@Finset.card (Fin n) C) (@Finset.card (Fin n) C))))
                                                          (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                                        childTime)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                                (@OfNat.ofNat Nat (nat_lit 16)
                                                                  (instOfNatNat (nat_lit 16)))
                                                                S)
                                                              (@OfNat.ofNat Nat (nat_lit 16)
                                                                (instOfNatNat (nat_lit 16))))
                                                            (@List.length String
                                                              (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                            (@OfNat.ofNat Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                                            (@List.length String
                                                              (Lax263307Proofs.NativeCoreMachine.frameScalars cfg))))
                                                        (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@OfNat.ofNat Nat (nat_lit 45) (instOfNatNat (nat_lit 45)))
                                                          (@Finset.card (Fin n) C))
                                                        (@OfNat.ofNat Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
                                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                              (@OfNat.ofNat Nat (nat_lit 28)
                                                                (instOfNatNat (nat_lit 28)))
                                                              n)
                                                            (@OfNat.ofNat Nat (nat_lit 104)
                                                              (instOfNatNat (nat_lit 104))))
                                                          (Lax263307Proofs.NativeCatalogMetadata.N n r))
                                                        (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                                                (And (Lax263307Proofs.NativeCollectionAnchor.Anchor σ τ)
                                                  (@Option.casesOn (Finset (Fin (@Finset.card (Fin n) C)))
                                                    (fun (x : Option (Finset (Fin (@Finset.card (Fin n) C)))) =>
                                                      (fun (answer : Option (Finset (Fin (@Finset.card (Fin n) C)))) =>
                                                          Prop)
                                                        x)
                                                    answer
                                                    ((fun (_ : Unit) =>
                                                        @Lax263307Proofs.NativeCollectionTrace.ResultOutput n
                                                          (@Lax263307Proofs.NativeCollectionContext.Context n B D k r
                                                            fuel S G inst x parts A extent front)
                                                          (fun (C : Finset (Fin n)) (u : Nat)
                                                              (τ : Lax808846Proofs.Imp.Env) =>
                                                            Lax455465Proofs.RamVirtualState.Prefix
                                                              (@Lax263307Proofs.NativeRoundedQuery.normal
                                                                (Lax263307.MomentLP.dimension n r)
                                                                (@Lax263307.RationalCutBuffer.integerNormal
                                                                  (Lax263307.MomentLP.dimension n r)
                                                                  (@Lax263307.RoundedOracleSearch.rationalNormal
                                                                    (Lax263307.MomentLP.dimension n r)
                                                                    (@Lax263307Proofs.NativeComponentNormal.normal n r A
                                                                      C u))))
                                                              "round.normal" τ)
                                                          (@Lax263307.ComputedRounding.Result.cut n C
                                                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) target
                                                              (@OfNat.ofNat Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1)))))
                                                          τ)
                                                      Unit.unit)
                                                    fun (val : Finset (Fin (@Finset.card (Fin n) C))) =>
                                                    (fun (I : Finset (Fin (@Finset.card (Fin n) C))) =>
                                                        @Lax263307Proofs.NativeCollectionTrace.At n
                                                          (@Lax263307Proofs.NativeCollectionContext.Context n B D k r
                                                            fuel S G inst x parts A extent front)
                                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) i
                                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                          (@Union.union (Finset (Fin n))
                                                            (@Finset.instUnion (Fin n) (instDecidableEqFin n)) U
                                                            (@Finset.image (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                              (instDecidableEqFin n)
                                                              (@DFunLike.coe
                                                                (@OrderEmbedding (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                                  (@instLEFin (@Finset.card (Fin n) C)) (@instLEFin n))
                                                                (Fin (@Finset.card (Fin n) C))
                                                                (fun (x : Fin (@Finset.card (Fin n) C)) => Fin n)
                                                                (@instFunLikeOrderEmbedding
                                                                  (Fin (@Finset.card (Fin n) C)) (Fin n)
                                                                  (@instLEFin (@Finset.card (Fin n) C)) (@instLEFin n))
                                                                (@Lax263307.ComputedSeparators.label n C))
                                                              I))
                                                          τ)
                                                      val)))) := by
  intro n B S D k r fuel i target childSteps childTime cfg G inst x parts A C U extent front answer hB hm hext hstack hchild hsearch hbits hlp hnormal σ hc hd hmask htarget hi hu hr hp recursive
  obtain ⟨τ,steps,total,seg,hs,ht,ha,hout⟩ := @Lax263307Proofs.NativeCollectionChild.child_iteration n B S D k r fuel i target childSteps childTime cfg G inst x parts A C U extent front answer hB hm hext hstack hchild hsearch hbits hlp hnormal σ hc hd hmask htarget hi hu hr hp recursive
  refine ⟨τ,steps,total,seg,hs,ht,ha,?_⟩
  split at hout <;> simp_all
