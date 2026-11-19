-- Prove2me | solution 1 for Lax263307Proofs.NativeRootBudget.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:02:00.790641+00:00
-- url     : https://prove2.me/submissions/bef5b658-211e-42ae-89c3-55555e3a3b9d

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces

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

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

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

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

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

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

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

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem word_spec (B v:ℕ) (h2:2 < B) (hv:v < B):
    Spec B (fun σ => σ.vars "size.value"=v) word
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 6):=by
  let I:=fun σ:Env => σ.vars "size.value" ≤ v∧
    σ.vars "size.count" + (σ.vars "size.value").size=v.size
  have hs:v.size≤ v:=Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hlo:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => I τ∧ (Cond.lt (.lit 0) (.var "size.value")).evalB B τ=some false)
      (12 * v.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "size.value").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))⟩
    · rintro σ ⟨hI,hcond⟩
      have hval:=hI.1.trans_lt hv
      have hp:0 < σ.vars "size.value" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hval)] at hcond
        simpa using hcond
      have hhalf:=WordSize.size_half (σ.vars "size.value") hp
      have hcounter:σ.vars "size.count" + 1 < B:=by
        have hsz:=Nat.size_pos.mpr hp
        have heq:=hI.2
        omega
      have hdiv:=(Nat.div_le_self (σ.vars "size.value") 2).trans_lt hval
      have hle:=(Nat.div_le_self (σ.vars "size.value") 2).trans hI.1
      (expose_names;
        (refine let c0:Env→ Prop:=(fun (σ_1 σ':Env) => And (I σ') (Nat.lt (Nat.size (Env.vars σ' "size.value")) (Nat.size (Env.vars σ_1 "size.value")))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "size.value") ((2:Nat)); let c2:Env:=Env.setVar σ "size.value" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=Env.vars c2 "size.count"; let c5:Nat:=c3 c4 ((1:Nat)); let c6:Env:=Env.setVar c2 "size.count" c5; let c7:Nat→ Nat:=c3 ((1:Nat)); let c8:Expr:=Expr.div (Expr.var "size.value") (Expr.lit ((2:Nat))); let c9:Nat:=c7 (Expr.size c8); let c10:Expr:=Expr.add (Expr.var "size.count") (Expr.lit ((1:Nat))); let c11:Nat:=c7 (Expr.size c10); @Exists.intro Env (fun (σ':Env) => And (Run B wordStep σ σ' ((8:Nat))) (c0 σ')) c6 (@And.intro (Run B wordStep σ c6 ((8:Nat))) (c0 c6) (RunStep.mono B wordStep σ c6 (c3 c9 c11) ((8:Nat)) (RunStep.seq B (Com.assign "size.value" c8) (Com.assign "size.count" c10) σ c2 c6 c9 c11 (RunStep.assign B σ "size.value" c8 c1 (RunStep.eval_div B σ (Expr.var "size.value") (Expr.lit ((2:Nat))) (Env.vars σ "size.value") ((2:Nat)) (RunStep.eval_var B σ "size.value" hval) (RunStep.eval_lit B ((2:Nat)) σ h2) hdiv)) (RunStep.assign B c2 "size.count" c10 c5 (RunStep.eval_add B c2 (Expr.var "size.count") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c2 "size.count" (?nAX_g6023_0_0_0)) (RunStep.eval_lit B ((1:Nat)) c2 (?nAX_g6023_0_0_1)) (?nAX_g6023_0_0_2)))) (?nAX_g6023_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [I]
      all_goals omega
    · rintro σ ⟨hvalue,hcount⟩
      simp [I,hvalue,hcount]
    · rintro σ ⟨hvalue,hcount⟩
      simp [hvalue]
  have hfinish:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 4):=hlo.post (by
    rintro σ τ _ ⟨hI,hcond⟩
    have hzero:τ.vars "size.value"=0:=by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))] at hcond
      simpa using hcond
    exact ⟨hzero,by simpa only [hzero,Nat.size_zero,Nat.add_zero] using hI.2⟩)
  rintro σ hvalue
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "size.count" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B wordLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size v)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "size.value") ((0:Nat))) (@Eq Nat (Env.vars σ' "size.count") (Nat.size v))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x τ:Env) => And (@Eq Nat (Env.vars τ "size.value") ((0:Nat))) (@Eq Nat (Env.vars τ "size.count") (Nat.size v)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B word σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "size.value") v) (@Eq Nat (Env.vars σ_1 "size.count") ((0:Nat)))) wordLoop c7 c4 hfinish c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B word σ w c6) (c8 w) (RunStep.mono B word σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "size.count" (Expr.lit ((0:Nat)))) wordLoop σ c0 w c12 c4 (RunStep.assign B σ "size.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6023_1_0_0))) left) (?nAX_g6023_1_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

open RamVirtualState Lax759944.BinaryWordEncoding

end Lax455465Proofs.RamBitSize

end

section

namespace Lax263307Proofs.NativeLogarithms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open Lax455465Proofs

theorem size_eq (n:ℕ) (hn:0< n):n.size=Nat.log2 n+1:=by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  · have hp:2^Nat.log2 n≤ n:=by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hs:=Nat.lt_size.mpr hp
    omega

theorem small_spec (B n:ℕ) (hn:0< n) (hB:n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) small
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1) (12*n.size+10):=by
  intro σ hs
  let ν:=σ.setVar "size.value" n
  have r1:Run B (.assign "size.value" (.var "graph.n")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩)
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B n (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.log" n.size
  have hsize:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.log" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change n.size=Nat.log2 n+1; exact size_eq n hn⟩

theorem large_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) large
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.logarithm"=logarithm n) (12*(2*n).size+12):=by
  intro σ hs
  let ν:=σ.setVar "size.value" (2*n)
  have r1:Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩) (by change 2*n< B; omega))
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.logarithm" (2*n).size
  have hsize:(2*n).size≤2*n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.logarithm" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change (2*n).size=Nat.log2 (2*n)+1; exact size_eq (2*n) (by omega)⟩

theorem command_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1∧
        τ.vars "node.logarithm"=logarithm n) (12*n.size+12*(2*n).size+22):=by
  intro σ hs
  obtain ⟨ν,r1,p1⟩:=small_spec B n hn (by omega) σ hs
  obtain ⟨τ,r2,p2⟩:=large_spec B n hn hB ν p1.1
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1,
    (r2.frame_var "node.log" (by decide)).trans p1.2,p2.2⟩

end Lax263307Proofs.NativeLogarithms

end

section

namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Context (b e:ℕ) (σ:Env):Prop:=σ.vars "power.base"=b∧ σ.vars "power.exponent"=e

def Invariant (b e:ℕ) (σ:Env):Prop:=
  Context b e σ∧ σ.vars "power.i"≤ e∧ σ.vars "power.value"=b^(σ.vars "power.i")

theorem step_spec (B b e i:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B) (hi:i< e):
    Spec B (fun σ => Context b e σ∧ σ.vars "power.i"=i∧ σ.vars "power.value"=b^i) step
      (fun _ τ => Context b e τ∧ τ.vars "power.i"=i+1∧ τ.vars "power.value"=b^(i+1)) 8:=by
  have hp:b^i< B:=(Nat.pow_le_pow_right hb hi.le).trans_lt (by omega)
  have hnext:b^i*b< B:=by
    rw [←pow_succ]
    exact (Nat.pow_le_pow_right hb hi).trans_lt (by omega)
  (expose_names;
    (refine fun (σ:Env) (a:And (Context b e σ) (And (@Eq Nat (Env.vars σ "power.i") i) (@Eq Nat (Env.vars σ "power.value") (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b i)))) => let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b; let c1:Prop:= @Eq Nat (Env.vars σ "power.value") (c0 i); let c2:Prop:=And (@Eq Nat (Env.vars σ "power.i") i) c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=c3 i ((1:Nat)); let c5:Nat:=c0 c4; let c6:Env→ Prop:=(fun (x τ:Env) => And (Context b e τ) (And (@Eq Nat (Env.vars τ "power.i") c4) (@Eq Nat (Env.vars τ "power.value") c5))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B step σ σ' ((8:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c10:Env:=Env.setVar σ "power.value" c9; let c11:Nat:=Env.vars c10 "power.i"; let c12:Nat:=c3 c11 ((1:Nat)); let c13:Env:=Env.setVar c10 "power.i" c12; let c14:Nat→ Nat:=c3 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c16:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c13; @And.casesOn (Context b e σ) c2 (fun (x:And (Context b e σ) c2) => c8) a fun (left:Context b e σ) (right:c2) => @And.casesOn (@Eq Nat (Env.vars σ "power.i") i) c1 (fun (x:c2) => c8) right fun (left_1:@Eq Nat (Env.vars σ "power.i") i) (right_1:c1) => @Exists.intro Env c7 c13 (@And.intro (Run B step σ c13 ((8:Nat))) (c6 c13) (RunStep.mono B step σ c13 (c3 c15 c17) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c16) σ c10 c13 c15 c17 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c9 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g8253_0_0_0)) (RunStep.eval_var B σ "power.base" ?_) ?_)) (RunStep.assign B c10 "power.i" c16 c12 (RunStep.eval_add B c10 (Expr.var "power.i") (Expr.lit ((1:Nat))) c11 ((1:Nat)) (RunStep.eval_var B c10 "power.i" (?nAX_g8253_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g8253_0_0_2)) (?nAX_g8253_0_0_3)))) (?nAX_g8253_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8253_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,pow_succ]
  all_goals omega

theorem command_spec (B b e:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B):
    Spec B (Context b e) command
      (fun _ τ => Context b e τ∧ τ.vars "power.value"=b^e) (12*e+8):=by
  have hbody:Spec B (fun σ => Invariant b e σ∧ σ.vars "power.i"< e) step
      (fun σ τ => Invariant b e τ∧ τ.vars "power.i"=σ.vars "power.i"+1) 8:=by
    rintro σ ⟨⟨hc,hle,hv⟩,hlt⟩
    obtain ⟨τ,rr,ht⟩:=step_spec B b e (σ.vars "power.i") hb hB hlt σ ⟨hc,rfl,hv⟩
    exact ⟨τ,rr,⟨ht.1,by rw [ht.2.1]; omega,by simpa only [ht.2.1] using ht.2.2⟩,ht.2.1⟩
  have hloop:=Spec.forRangeZero "power.i" "power.exponent" (Invariant b e) e 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν:=σ.setVar "power.value" 1
  have r1:Run B (.assign "power.value" (.lit 1)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant b e (ν.setVar "power.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,ν,vars_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,by simpa only [p2.2] using p2.1.2.2⟩

end Lax263307Proofs.NativeNaturalPower

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRootBudget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open NativeRootResource

theorem first_spec (B d D L:ℕ) (hB:d+D+L+D*L+3< B):
    Spec B (fun σ => σ.vars "node.D"=D∧ σ.vars "node.logarithm"=L) (first d)
      (fun _ τ => NativeNaturalPower.Context (D*L) d τ) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Env→ Prop:=NativeNaturalPower.Context (c0 D L) d; let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ; let c3:Nat:=c0 (Env.vars σ "node.D") (Env.vars σ "node.logarithm"); let c4:Env:=Env.setVar σ "power.base" c3; let c5:Env:=Env.setVar c4 "power.exponent" d; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.mul (Expr.var "node.D") (Expr.var "node.logarithm"))); let c9:Nat:=c7 (Expr.size (Expr.lit d)); @Exists.intro Env (fun (σ':Env) => And (Run B (first d) σ σ' ((6:Nat))) (c2 σ')) c5 (@And.intro (Run B (first d) σ c5 ((6:Nat))) (c2 c5) (RunStep.mono B (first d) σ c5 (c6 c8 c9) ((6:Nat)) (RunStep.seq B (Com.assign "power.base" (Expr.mul (Expr.var "node.D") (Expr.var "node.logarithm"))) (Com.assign "power.exponent" (Expr.lit d)) σ c4 c5 c8 c9 (RunStep.assign B σ "power.base" (Expr.mul (Expr.var "node.D") (Expr.var "node.logarithm")) c3 (RunStep.eval_mul B σ (Expr.var "node.D") (Expr.var "node.logarithm") (Env.vars σ "node.D") (Env.vars σ "node.logarithm") (RunStep.eval_var B σ "node.D" (?nAX_g9630_0_0_0)) (RunStep.eval_var B σ "node.logarithm" (?nAX_g9630_0_0_1)) ?_)) (RunStep.assign B c4 "power.exponent" (Expr.lit d) d (RunStep.eval_lit B d c4 (?nAX_g9630_0_0_2)))) (?nAX_g9630_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9630_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9630_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9630_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9630_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem second_spec (B C V:ℕ) (hB:C+V+C*V+3< B):
    Spec B (fun σ => σ.vars "power.value"=V) (second C)
      (fun _ τ => NativeNaturalPower.Context 2 (C*V) τ∧ τ.vars "root.exponent"=C*V) 8:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat:=Nat.mul C; let c1:Nat:=c0 V; let c2:Env→ Prop:=NativeNaturalPower.Context ((2:Nat)) c1; let c3:Env→ Prop:=(fun (x τ:Env) => And (c2 τ) (@Eq Nat (Env.vars τ "root.exponent") c1)) σ; let c4:Nat:=c0 (Env.vars σ "power.value"); let c5:Env:=Env.setVar σ "root.exponent" c4; let c6:Env:=Env.setVar c5 "power.base" ((2:Nat)); let c7:Nat:=Env.vars c6 "root.exponent"; let c8:Env:=Env.setVar c6 "power.exponent" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat:=c10 (Expr.size (Expr.mul (Expr.lit C) (Expr.var "power.value"))); let c12:Nat:=c10 (Expr.size (Expr.lit ((2:Nat)))); let c13:Nat:=c10 (Expr.size (Expr.var "root.exponent")); let c14:Nat:=c9 c12 c13; let c15:Com:=Com.assign "power.base" (Expr.lit ((2:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (second C) σ σ' ((8:Nat))) (c3 σ')) c8 (@And.intro (Run B (second C) σ c8 ((8:Nat))) (c3 c8) (RunStep.mono B (second C) σ c8 (c9 c11 c14) ((8:Nat)) (RunStep.seq B (Com.assign "root.exponent" (Expr.mul (Expr.lit C) (Expr.var "power.value"))) (Com.seq c15 (Com.assign "power.exponent" (Expr.var "root.exponent"))) σ c5 c8 c11 c14 (RunStep.assign B σ "root.exponent" (Expr.mul (Expr.lit C) (Expr.var "power.value")) c4 (RunStep.eval_mul B σ (Expr.lit C) (Expr.var "power.value") C (Env.vars σ "power.value") (RunStep.eval_lit B C σ (?nAX_g9631_0_0_0)) (RunStep.eval_var B σ "power.value" (?nAX_g9631_0_0_1)) ?_)) (RunStep.seq B c15 (Com.assign "power.exponent" (Expr.var "root.exponent")) c5 c6 c8 c12 c13 (RunStep.assign B c5 "power.base" (Expr.lit ((2:Nat))) ((2:Nat)) (RunStep.eval_lit B ((2:Nat)) c5 (?nAX_g9631_0_0_2))) (RunStep.assign B c6 "power.exponent" (Expr.var "root.exponent") c7 (RunStep.eval_var B c6 "root.exponent" ?_)))) (?nAX_g9631_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9631_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9631_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9631_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9631_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem third_spec (B e R:ℕ) (hB:e+R+3< B):
    Spec B (fun σ => σ.vars "power.value"=R) (third e)
      (fun _ τ => NativeNaturalPower.Context (R+1) e τ∧ τ.vars "algorithm.resource"=R) 8:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=NativeNaturalPower.Context (c0 R ((1:Nat))) e; let c2:Env→ Prop:=(fun (x τ:Env) => And (c1 τ) (@Eq Nat (Env.vars τ "algorithm.resource") R)) σ; let c3:Nat:=Env.vars (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) "power.value"; let c4:Nat:=c0 c3 ((1:Nat)); let c5:Env:=Env.setVar (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) "power.base" c4; let c6:Env:=Env.setVar c5 "power.exponent" e; let c7:Nat→ Nat:=c0 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.var "power.value")); let c9:Expr:=Expr.add (Expr.var "power.value") (Expr.lit ((1:Nat))); let c10:Nat:=c7 (Expr.size c9); let c11:Nat:=c7 (Expr.size (Expr.lit e)); let c12:Nat:=c0 c10 c11; let c13:Com:=Com.assign "power.base" c9; @Exists.intro Env (fun (σ':Env) => And (Run B (third e) σ σ' ((8:Nat))) (c2 σ')) c6 (@And.intro (Run B (third e) σ c6 ((8:Nat))) (c2 c6) (RunStep.mono B (third e) σ c6 (c0 c8 c12) ((8:Nat)) (RunStep.seq B (Com.assign "algorithm.resource" (Expr.var "power.value")) (Com.seq c13 (Com.assign "power.exponent" (Expr.lit e))) σ (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) c6 c8 c12 (RunStep.assign B σ "algorithm.resource" (Expr.var "power.value") (Env.vars σ "power.value") (RunStep.eval_var B σ "power.value" (?nAX_g9632_0_0_0))) (RunStep.seq B c13 (Com.assign "power.exponent" (Expr.lit e)) (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) c5 c6 c10 c11 (RunStep.assign B (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) "power.base" c9 c4 (RunStep.eval_add B (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) (Expr.var "power.value") (Expr.lit ((1:Nat))) c3 ((1:Nat)) (RunStep.eval_var B (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) "power.value" (?nAX_g9632_0_0_1)) (RunStep.eval_lit B ((1:Nat)) (Env.setVar σ "algorithm.resource" (Env.vars σ "power.value")) (?nAX_g9632_0_0_2)) (?nAX_g9632_0_0_3))) (RunStep.assign B c5 "power.exponent" (Expr.lit e) e (RunStep.eval_lit B e c5 (?nAX_g9632_0_0_4))))) (?nAX_g9632_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9632_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9632_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9632_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9632_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9632_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9632_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem finish_spec (B Q V:ℕ) (hB:Q+V+Q*V+2*(Q*V+1)+3< B):
    Spec B (fun σ => σ.vars "power.value"=V) (finish Q)
      (fun _ τ => τ.vars "algorithm.roundWidth"=Q*V∧ τ.vars "recursion.stride"=2*(Q*V+1)) 10:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat:=c0 Q; let c2:Nat:=c1 V; let c3:Nat→ Nat:=c0 ((2:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c3 (c4 c2 ((1:Nat))); let c6:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "algorithm.roundWidth") c2) (@Eq Nat (Env.vars τ "recursion.stride") c5)) σ; let c7:Nat:=c1 (Env.vars σ "power.value"); let c8:Env:=Env.setVar σ "algorithm.roundWidth" c7; let c9:Nat:=Env.vars c8 "algorithm.roundWidth"; let c10:Nat:=c4 c9 ((1:Nat)); let c11:Nat:=c3 c10; let c12:Env:=Env.setVar c8 "recursion.stride" c11; let c13:Nat→ Nat:=c4 ((1:Nat)); let c14:Nat:=c13 (Expr.size (Expr.mul (Expr.lit Q) (Expr.var "power.value"))); let c15:Expr:=Expr.add (Expr.var "algorithm.roundWidth") (Expr.lit ((1:Nat))); let c16:Expr:=Expr.mul (Expr.lit ((2:Nat))) c15; let c17:Nat:=c13 (Expr.size c16); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B (finish Q) σ σ' ((10:Nat))) (c6 σ')) c12 (@And.intro (Run B (finish Q) σ c12 ((10:Nat))) (c6 c12) (RunStep.mono B (finish Q) σ c12 (c4 c14 c17) ((10:Nat)) (RunStep.seq B (Com.assign "algorithm.roundWidth" (Expr.mul (Expr.lit Q) (Expr.var "power.value"))) (Com.assign "recursion.stride" c16) σ c8 c12 c14 c17 (RunStep.assign B σ "algorithm.roundWidth" (Expr.mul (Expr.lit Q) (Expr.var "power.value")) c7 (RunStep.eval_mul B σ (Expr.lit Q) (Expr.var "power.value") Q (Env.vars σ "power.value") (RunStep.eval_lit B Q σ (?nAX_g9633_0_0_0)) (RunStep.eval_var B σ "power.value" (?nAX_g9633_0_0_1)) ?_)) (RunStep.assign B c8 "recursion.stride" c16 c11 (RunStep.eval_mul B c8 (Expr.lit ((2:Nat))) c15 ((2:Nat)) c10 (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g9633_0_0_2)) (RunStep.eval_add B c8 (Expr.var "algorithm.roundWidth") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c8 "algorithm.roundWidth" ?_) (RunStep.eval_lit B ((1:Nat)) c8 (?nAX_g9633_0_0_3)) ?_) ?_))) (?nAX_g9633_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9633_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9633_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9633_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9633_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9633_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem command_spec (B C d Q e n D:ℕ) (hn:0< n) (hD:0< D)
    (hB:guard C d Q e n D< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "node.D"=D) (command C d Q e)
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.D"=D∧
        τ.vars "algorithm.resource"=envelope C d n D∧
        τ.vars "algorithm.roundWidth"=budget Q e C d n D∧
        τ.vars "recursion.stride"=2*(budget Q e C d n D+1))
      (12*n.size+12*(2*n).size+12*d+12*(C*(D*logarithm n)^d)+12*e+78):=by
  let X:=D*logarithm n
  let H:=C*X^d
  let R:=envelope C d n D
  have hX:1≤ X:=by
    have hp:0< X:=by dsimp [X,logarithm]; positivity
    omega
  have hg:=hB
  dsimp only [guard,budget] at hg
  rintro σ ⟨horder,hden⟩
  obtain ⟨σ₁,r0,p0⟩:=NativeLogarithms.command_spec B n hn (by omega) σ horder
  obtain ⟨σ₂,r1,p1⟩:=first_spec B d D (logarithm n) (by omega) σ₁
    ⟨(r0.frame_var _ (by decide)).trans hden,p0.2.2⟩
  obtain ⟨σ₃,r2,p2⟩:=NativeNaturalPower.command_spec B X d hX (by dsimp [X]; omega) σ₂ p1
  obtain ⟨σ₄,r3,p3⟩:=second_spec B C (X^d) (by dsimp [X]; omega) σ₃ p2.2
  obtain ⟨σ₅,r4,p4⟩:=NativeNaturalPower.command_spec B 2 H (by decide) (by
    change 2+H+R+3< B
    dsimp only [H,R,X]
    omega) σ₄ p3.1
  obtain ⟨σ₆,r5,p5⟩:=third_spec B e R (by dsimp [R]; omega) σ₅ p4.2
  obtain ⟨σ₇,r6,p6⟩:=NativeNaturalPower.command_spec B (R+1) e (by omega) (by dsimp [R]; omega) σ₆ p5.1
  obtain ⟨τ,r7,p7⟩:=finish_spec B Q ((R+1)^e) (by dsimp [R]; omega) σ₇ p6.2
  have rr:=r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7))))))
  refine ⟨τ,rr.mono (by dsimp only [H,X]; omega),?_,?_,?_,p7⟩
  · exact (rr.frame_var "graph.n" (by
      change "graph.n"∉(command 0 0 0 0).wvars
      decide)).trans horder
  · exact (rr.frame_var "node.D" (by
      change "node.D"∉(command 0 0 0 0).wvars
      decide)).trans hden
  · exact ((r6.seq r7).frame_var "algorithm.resource" (by
      simp [NativeNaturalPower.command,NativeNaturalPower.step,finish,Com.wvars])).trans p5.2

end Lax263307Proofs.NativeRootBudget

end

theorem solution:∀ (B C d Q e n D:Nat),
  Nat.lt ((0:Nat)) n→
    Nat.lt ((0:Nat)) D→
      Nat.lt (Lax263307Proofs.NativeRootBudget.guard C d Q e n D) B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "graph.n") n) (@Eq Nat (σ.vars "node.D") D))
          (Lax263307Proofs.NativeRootBudget.command C d Q e)
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And (@Eq Nat (τ.vars "node.D") D)
                (And (@Eq Nat (τ.vars "algorithm.resource") (Lax263307Proofs.NativeRootResource.envelope C d n D))
                  (And (@Eq Nat (τ.vars "algorithm.roundWidth") (Lax263307Proofs.NativeRootResource.budget Q e C d n D))
                    (@Eq Nat (τ.vars "recursion.stride")
                      (Nat.mul
                        ((2:Nat))
                        (Nat.add
                          (Lax263307Proofs.NativeRootResource.budget Q e C d n D)
                          ((1:Nat)))))))))
          (Nat.add
            (Nat.add
              (Nat.add
                (Nat.add
                  (Nat.add
                    (Nat.mul
                      ((12:Nat)) n.size)
                    (Nat.mul
                      ((12:Nat))
                      (Nat.mul
                          ((2:Nat)) n).size))
                  (Nat.mul
                    ((12:Nat)) d))
                (Nat.mul
                  ((12:Nat))
                  (Nat.mul C
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (Nat.mul D (Lax263307.AlgorithmParameters.logarithm n))
                      d))))
              (Nat.mul
                ((12:Nat)) e))
            ((78:Nat))):= @Lax263307Proofs.NativeRootBudget.command_spec
