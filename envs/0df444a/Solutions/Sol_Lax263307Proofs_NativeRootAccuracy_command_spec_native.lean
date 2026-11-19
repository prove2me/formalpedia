-- Prove2me | solution 1 for Lax263307Proofs.NativeRootAccuracy.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:02:00.214409+00:00
-- url     : https://prove2.me/submissions/a5564681-519f-4d73-97bf-14c64d34b2b8

import Mathlib.Tactic
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

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

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

namespace Lax263307Proofs.NativeRecursionDepth

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.RecursionDepth

def Invariant (n:ℕ) (σ:Env):Prop:=
  σ.vars "depth.value"≤ n∧ σ.vars "depth.count"+depth (σ.vars "depth.value")=depth n

theorem command_spec (B n:ℕ) (hB:2*n+depth n+10< B):
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "depth.count"=depth n) (14*depth n+8):=by
  have hlo:Spec B (fun σ => σ.vars "depth.value"=n∧ σ.vars "depth.count"=0) loop
      (fun _ τ => Invariant n τ∧ (Cond.lt (.lit 1) (.var "depth.value")).evalB B τ=some false)
      (14*depth n+4):=by
    apply Spec.while_count (Invariant n) (fun σ => depth (σ.vars "depth.value")) 10
    · intro σ hs
      exact ⟨_,evalB_condLt (evalB_lit (show 1< B by omega)) (evalB_var (hs.1.trans_lt (by omega)))⟩
    · rintro σ ⟨hs,hcond⟩
      have hvB:σ.vars "depth.value"< B:=hs.1.trans_lt (by omega)
      have hval:1<σ.vars "depth.value" :=by
        rw [evalB_condLt (evalB_lit (show 1< B by omega)) (evalB_var hvB)] at hcond
        simpa using hcond
      have hd:depth (σ.vars "depth.value")=1+depth (2*σ.vars "depth.value"/3):=by
        rw [depth,if_neg (by omega)]
      have hcB:σ.vars "depth.count"+1< B:=by have hh:=hs.2; omega
      have hmB:2*σ.vars "depth.value"< B:=by have hh:=hs.1; omega
      have hnext:2*σ.vars "depth.value"/3≤ n:=by have hh:=hs.1; omega
      (expose_names;
        (refine let c0:Env→ Prop:=(fun (σ_1 σ':Env) => And (Invariant n σ') (Nat.lt (depth (Env.vars σ' "depth.value")) (depth (Env.vars σ_1 "depth.value")))) σ; let c1:Nat:=Nat.mul ((2:Nat)) (Env.vars σ "depth.value"); let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c1 ((3:Nat)); let c3:Env:=Env.setVar σ "depth.value" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=Env.vars c3 "depth.count"; let c6:Nat:=c4 c5 ((1:Nat)); let c7:Env:=Env.setVar c3 "depth.count" c6; let c8:Nat→ Nat:=c4 ((1:Nat)); let c9:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "depth.value"); let c10:Expr:=Expr.div c9 (Expr.lit ((3:Nat))); let c11:Nat:=c8 (Expr.size c10); let c12:Expr:=Expr.add (Expr.var "depth.count") (Expr.lit ((1:Nat))); let c13:Nat:=c8 (Expr.size c12); @Exists.intro Env (fun (σ':Env) => And (Run B step σ σ' ((10:Nat))) (c0 σ')) c7 (@And.intro (Run B step σ c7 ((10:Nat))) (c0 c7) (RunStep.mono B step σ c7 (c4 c11 c13) ((10:Nat)) (RunStep.seq B (Com.assign "depth.value" c10) (Com.assign "depth.count" c12) σ c3 c7 c11 c13 (RunStep.assign B σ "depth.value" c10 c2 (RunStep.eval_div B σ c9 (Expr.lit ((3:Nat))) c1 ((3:Nat)) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "depth.value") ((2:Nat)) (Env.vars σ "depth.value") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g9616_0_0_0)) (RunStep.eval_var B σ "depth.value" hvB) hmB) (RunStep.eval_lit B ((3:Nat)) σ (?nAX_g9616_0_0_1)) (?nAX_g9616_0_0_2))) (RunStep.assign B c3 "depth.count" c12 c6 (RunStep.eval_add B c3 (Expr.var "depth.count") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c3 "depth.count" (?nAX_g9616_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c3 (?nAX_g9616_0_0_4)) (?nAX_g9616_0_0_5)))) (?nAX_g9616_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9616_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9616_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Invariant,Env.setVar]
      all_goals omega
    · rintro σ ⟨hv,hc⟩
      simp [Invariant,hv,hc]
    · rintro σ ⟨hv,_⟩
      simp [hv]
  have hfinish:Spec B (fun σ => σ.vars "depth.value"=n∧ σ.vars "depth.count"=0) loop
      (fun _ τ => τ.vars "depth.count"=depth n) (14*depth n+4):=hlo.post (by
    rintro σ τ _ ⟨hs,hcond⟩
    have hvB:τ.vars "depth.value"< B:=hs.1.trans_lt (by omega)
    have hsmall:τ.vars "depth.value"≤1:=by
      rw [evalB_condLt (evalB_lit (show 1< B by omega)) (evalB_var hvB)] at hcond
      have hh:¬1<τ.vars "depth.value" :=by simpa using hcond
      omega
    have hz:depth (τ.vars "depth.value")=0:=by rw [depth,if_pos hsmall]
    simpa only [hz,Nat.add_zero] using hs.2)
  intro σ hs
  let ν:=σ.setVar "depth.value" n
  have r1:Run B (.assign "depth.value" (.var "graph.n")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (by omega)⟩)
  let μ:=ν.setVar "depth.count" 0
  have r2:Run B (.assign "depth.count" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (show 0< B by omega))
  obtain ⟨τ,r3,p3⟩:=hfinish μ ⟨by simp [μ,ν],by rfl⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    ((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,p3⟩

end Lax263307Proofs.NativeRecursionDepth

end

section

namespace Lax263307Proofs.NativeRootAccuracy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RecursionDepth

theorem ceil_div (n d:ℕ) (hn:0< n) (hd:0< d):
    ⌈((n:ℚ)/d)⌉₊=(n+d-1)/d:=by
  let k:=(n+d-1)/d
  have hsum:n+d-1+1=n+d:=by omega
  have hk:1≤ k:=(Nat.le_div_iff_mul_le hd).mpr (by simp; omega)
  have hlo:k*d≤ n+d-1:=Nat.div_mul_le_self (n+d-1) d
  have hhi:n+d-1<(k+1)*d:=(Nat.div_lt_iff_lt_mul hd).mp (by change k< k+1; omega)
  have hkstep:k=k-1+1:=by omega
  have hu:n≤ k*d:=by nlinarith only [hhi,hsum]
  have hl:(k-1)*d< n:=by nlinarith only [hlo,hsum,hkstep]
  have hdq:0<(d:ℚ):=by exact_mod_cast hd
  apply (Nat.ceil_eq_iff (by omega:k≠0)).mpr
  constructor
  · apply (lt_div_iff₀ hdq).mpr
    exact_mod_cast hl
  · apply (div_le_iff₀ hdq).mpr
    exact_mod_cast hu

theorem inverse_half (ε:ℚ) (hε:0<ε):
    (ε/2)⁻¹=((2*ε.den:ℕ):ℚ)/(ε.num.natAbs:ℚ):=by
  have hnum:(ε.num.natAbs:ℚ)=(ε.num:ℚ):=by
    have he:(ε.num.natAbs:ℤ)=ε.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hε.le)
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) he
  have hvalue:(ε.num.natAbs:ℚ)/(ε.den:ℚ)=ε:=by rw [hnum,ε.num_div_den]
  have he:ε⁻¹=(ε.den:ℚ)/(ε.num.natAbs:ℚ):=by
    calc
      _=((ε.num.natAbs:ℚ)/(ε.den:ℚ))⁻¹:=congrArg Inv.inv hvalue.symm
      _=_:=inv_div _ _
  calc
    _=(2:ℚ)*ε⁻¹:=by rw [inv_div,div_eq_mul_inv]
    _=_:=by rw [he]; push_cast; ring

theorem finish_spec (B M n:ℕ) (ε:ℚ) (hε:0<ε) (hM:NativeSignedArithmetic.Bounded M ε)
    (hB:3*M+8*(depth n+1)*M+2*n+depth n+40< B):
    Spec B (fun σ => σ.vars "accuracy.n"=ε.num.natAbs∧ σ.vars "accuracy.d"=ε.den∧
      σ.vars "depth.count"=depth n) finish
      (fun _ τ => τ.vars "algorithm.E"=⌈(ε/2)⁻¹⌉₊∧
        τ.vars "node.D"=RecursiveAlgorithm.accuracyDenominator n (ε/2)∧
        τ.vars "recursion.fuel"=depth n) 20:=by
  have hnum:0<ε.num.natAbs:=by
    by_contra hh
    have hz:ε.num=0:=Int.natAbs_eq_zero.mp (by omega)
    have he:ε=0:=by rw [←ε.num_div_den,hz]; simp
    linarith
  have hc:(2*ε.den+ε.num.natAbs-1)/ε.num.natAbs=⌈(ε/2)⁻¹⌉₊:=by
    rw [inverse_half ε hε]
    exact (ceil_div (2*ε.den) ε.num.natAbs (by have hh:=ε.den_pos; omega) hnum).symm
  have he:⌈(ε/2)⁻¹⌉₊≤2*M:=by
    rw [inverse_half ε hε]
    apply (Nat.ceil_le.mpr (div_le_self (by positivity) (by exact_mod_cast (show 1≤ε.num.natAbs by omega)))).trans
    exact Nat.mul_le_mul_left 2 hM.2
  have hdenBudget:4*(depth n+1)*⌈(ε/2)⁻¹⌉₊≤8*(depth n+1)*M:=by
    have hh:=Nat.mul_le_mul_left (4*(depth n+1)) he
    nlinarith only [hh]
  have htop:2*ε.den+ε.num.natAbs-1≤3*M:=by have h1:=hM.1; have h2:=hM.2; omega
  have hMpos:1≤ M:=ε.den_pos.trans_le hM.2
  have hprod:4*(depth n+1)≤8*(depth n+1)*M:=by
    have hh:=Nat.mul_le_mul_left (4*(depth n+1)) hMpos
    nlinarith only [hh]
  intro σ hs
  (expose_names;
    (refine let c0:Rat:= @HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))); let c1:Nat:= @Nat.ceil Rat Rat.semiring Rat.instPartialOrder (@FloorRing.toFloorSemiring Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder Rat.instFloorRing) (@Inv.inv Rat Rat.instInv c0); let c2:Nat:=RecursiveAlgorithm.accuracyDenominator n c0; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "algorithm.E") c1) (And (@Eq Nat (Env.vars τ "node.D") c2) (@Eq Nat (Env.vars τ "recursion.fuel") (depth n)))) σ; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat→ Nat:=Nat.mul; let c6:Nat:=c5 ((2:Nat)) (Env.vars σ "accuracy.d"); let c7:Nat:=c4 c6 (Env.vars σ "accuracy.n"); let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 ((1:Nat)); let c9:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c8 (Env.vars σ "accuracy.n"); let c10:Env:=Env.setVar σ "algorithm.E" c9; let c11:String→ Nat:=Env.vars c10; let c12:Nat:=c11 "depth.count"; let c13:Nat:=c4 c12 ((1:Nat)); let c14:Nat:=c5 ((4:Nat)) c13; let c15:Nat:=c11 "algorithm.E"; let c16:Nat:=c5 c14 c15; let c17:Env:=Env.setVar c10 "node.D" c16; let c18:Nat:=Env.vars c17 "depth.count"; let c19:Env:=Env.setVar c17 "recursion.fuel" c18; let c20:Nat→ Nat:=c4 ((1:Nat)); let c21:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "accuracy.d"); let c22:Expr:=Expr.add c21 (Expr.var "accuracy.n"); let c23:Expr:=Expr.sub c22 (Expr.lit ((1:Nat))); let c24:Expr:=Expr.div c23 (Expr.var "accuracy.n"); let c25:Nat:=c20 (Expr.size c24); let c26:Expr:=Expr.add (Expr.var "depth.count") (Expr.lit ((1:Nat))); let c27:Expr:=Expr.mul (Expr.lit ((4:Nat))) c26; let c28:Expr:=Expr.mul c27 (Expr.var "algorithm.E"); let c29:Nat:=c20 (Expr.size c28); let c30:Nat:=c20 (Expr.size (Expr.var "depth.count")); let c31:Nat:=c4 c29 c30; let c32:Com:=Com.assign "node.D" c28; let c33:String→ Nat:=Env.vars c19; @Exists.intro Env (fun (σ':Env) => And (Run B finish σ σ' ((20:Nat))) (c3 σ')) c19 (@And.intro (Run B finish σ c19 ((20:Nat))) (c3 c19) (RunStep.mono B finish σ c19 (c4 c25 c31) ((20:Nat)) (RunStep.seq B (Com.assign "algorithm.E" c24) (Com.seq c32 (Com.assign "recursion.fuel" (Expr.var "depth.count"))) σ c10 c19 c25 c31 (RunStep.assign B σ "algorithm.E" c24 c9 (RunStep.eval_div B σ c23 (Expr.var "accuracy.n") c8 (Env.vars σ "accuracy.n") (RunStep.eval_sub B σ c22 (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_add B σ c21 (Expr.var "accuracy.n") c6 (Env.vars σ "accuracy.n") (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "accuracy.d") ((2:Nat)) (Env.vars σ "accuracy.d") (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g9621_0_0_0)) (RunStep.eval_var B σ "accuracy.d" (?nAX_g9621_0_0_1)) (?nAX_g9621_0_0_2)) (RunStep.eval_var B σ "accuracy.n" (?nAX_g9621_0_0_3)) (?nAX_g9621_0_0_4)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g9621_0_0_5)) (?nAX_g9621_0_0_6)) (RunStep.eval_var B σ "accuracy.n" (?nAX_g9621_0_0_7)) ?_)) (RunStep.seq B c32 (Com.assign "recursion.fuel" (Expr.var "depth.count")) c10 c17 c19 c29 c30 (RunStep.assign B c10 "node.D" c28 c16 (RunStep.eval_mul B c10 c27 (Expr.var "algorithm.E") c14 c15 (RunStep.eval_mul B c10 (Expr.lit ((4:Nat))) c26 ((4:Nat)) c13 (RunStep.eval_lit B ((4:Nat)) c10 (?nAX_g9621_0_0_8)) (RunStep.eval_add B c10 (Expr.var "depth.count") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c10 "depth.count" (?nAX_g9621_0_0_9)) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g9621_0_0_10)) (?nAX_g9621_0_0_11)) (?nAX_g9621_0_0_12)) (RunStep.eval_var B c10 "algorithm.E" ?_) ?_)) (RunStep.assign B c17 "recursion.fuel" (Expr.var "depth.count") c18 (RunStep.eval_var B c17 "depth.count" (?nAX_g9621_0_0_13))))) (?nAX_g9621_0_0_14)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g9621_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g9621_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,RecursiveAlgorithm.accuracyDenominator]
  all_goals nlinarith [hM.1,hM.2]

theorem command_spec (B M n:ℕ) (ε:ℚ) (hε:0<ε) (hM:NativeSignedArithmetic.Bounded M ε)
    (hB:3*M+8*(depth n+1)*M+2*n+depth n+40< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "accuracy.n"=ε.num.natAbs∧ σ.vars "accuracy.d"=ε.den)
      command (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "algorithm.E"=⌈(ε/2)⁻¹⌉₊∧
        τ.vars "node.D"=RecursiveAlgorithm.accuracyDenominator n (ε/2)∧ τ.vars "recursion.fuel"=depth n)
      (14*depth n+28):=by
  rintro σ ⟨hn,hnε,hdε⟩
  obtain ⟨ν,r1,p1⟩:=NativeRecursionDepth.command_spec B n (by omega) σ hn
  obtain ⟨τ,r2,p2⟩:=finish_spec B M n ε hε hM hB ν
    ⟨(r1.frame_var "accuracy.n" (by decide)).trans hnε,(r1.frame_var "accuracy.d" (by decide)).trans hdε,p1.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),(r2.frame_var "graph.n" (by decide)).trans p1.1,p2⟩

end Lax263307Proofs.NativeRootAccuracy

end

theorem solution:∀ (B M n:Nat) (ε:Rat),
  @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
    Lax263307Proofs.NativeSignedArithmetic.Bounded M ε→
      Nat.lt
          (Nat.add
            (Nat.add
              (Nat.add
                (Nat.add
                  (Nat.mul
                    ((3:Nat)) M)
                  (Nat.mul
                    (Nat.mul
                      ((8:Nat))
                      (Nat.add (Lax263307.RecursionDepth.depth n)
                        ((1:Nat))))
                    M))
                (Nat.mul
                  ((2:Nat)) n))
              (Lax263307.RecursionDepth.depth n))
            ((40:Nat)))
          B→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ.vars "graph.n") n)
              (And (@Eq Nat (σ.vars "accuracy.n") ε.num.natAbs) (@Eq Nat (σ.vars "accuracy.d") ε.den)))
          Lax263307Proofs.NativeRootAccuracy.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (τ.vars "graph.n") n)
              (And
                (@Eq Nat (τ.vars "algorithm.E")
                  (@Nat.ceil Rat Rat.semiring Rat.instPartialOrder
                    (@FloorRing.toFloorSemiring Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.linearOrder
                      Rat.instFloorRing)
                    (@Inv.inv Rat Rat.instInv
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))))))
                (And
                  (@Eq Nat (τ.vars "node.D")
                    (Lax263307.RecursiveAlgorithm.accuracyDenominator n
                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) ε
                        (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))))
                  (@Eq Nat (τ.vars "recursion.fuel") (Lax263307.RecursionDepth.depth n)))))
          (Nat.add
            (Nat.mul
              ((14:Nat)) (Lax263307.RecursionDepth.depth n))
            ((28:Nat))):= @Lax263307Proofs.NativeRootAccuracy.command_spec
