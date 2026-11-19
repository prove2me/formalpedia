-- Prove2me | solution 1 for Lax109476Proofs.RamPairSelector.selectEntry_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:44:45.546202+00:00
-- url     : https://prove2.me/submissions/2e73527f-b1d3-4591-b1c1-aa29206fecae

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
import Theorems.Thm_Lax109476Proofs_RamCertificateLoad_matrix_spec_native

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

namespace Lax109476Proofs.RamCertificateLoad
end Lax109476Proofs.RamCertificateLoad
theorem Lax109476Proofs.RamCertificateLoad.matrix_spec:∀ (B M m n:Nat) (P:Lax109476.LinearProgram.Program Int m n) (i:Fin m) (j:Fin n),
  LE.le ((1:Nat)) M→
    LT.lt M B→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd (HMul.hMul m n)
                m)
              n)
            ((4:Nat)))
          B→
        LE.le (@Lax109476.LinearProgram.Program.A Int m n P i j).natAbs M→
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ:Lax808846Proofs.Imp.Env) =>
              And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                (And (@Eq Nat (σ.vars "query.a.row") (@Fin.val m i)) (@Eq Nat (σ.vars "query.a.col") (@Fin.val n j))))
            Lax109476Proofs.RamCertificateLoad.matrix
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                (Lax109476Proofs.RamRational.FractionOutput
                  (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.A Int m n P i j)) τ))
            ((21:Nat)):= @Lax109476Proofs.RamCertificateLoad.matrix_spec_native

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

variable {B:ℕ} {P P':Env→ Prop} {Q Q' R:Env→ Env→ Prop} {c d:Com} {K K':ℕ}

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
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

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
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds

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
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

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
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + (n + 2))) (j:Fin (n + m))
    (hM:1≤ M) (hMB:M < B) (hB:m * n + 2 * m + 2 * n + 8 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M) (hb:∀ r, (P.b r).natAbs≤ M)
    (hc:∀ s, (P.c s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.pairEntry P i j:ℚ) τ) 72:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hmn:m + n < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hisub:i.val - m < B:=(Nat.sub_le _ _).trans_lt hiB
  have hjsub:j.val - n < B:=(Nat.sub_le _ _).trans_lt hjB
  have hz:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => FractionOutput (CertificateFamilyEntries.pairEntry P i j:ℚ) τ) 72:=by
    intro σ hs
    have hσm:=hs.1.2.2.2.1
    have hσn:=hs.1.2.2.2.2
    have hσrow:=hs.2.1
    have hσcol:=hs.2.2
    have testRow:(Cond.lt (.var "query.row") (.var "source.m")).evalB B σ=some (decide (i.val < m)):=by
      simp [Cond.evalB,Expr.evalB,fit,hσrow,hσm,hiB,hm]
    have testCol:(Cond.lt (.var "query.col") (.var "source.n")).evalB B σ=some (decide (j.val < n)):=by
      simp [Cond.evalB,Expr.evalB,fit,hσcol,hσn,hjB,hn]
    have testDual:(Cond.lt (.var "query.row") (.add (.var "source.m") (.var "source.n"))).evalB B σ=some (decide (i.val < m+n)):=by
      simp [Cond.evalB,Expr.evalB,Expr.add,fit,hσrow,hσm,hσn,hiB,hm,hn,hmn,Bop.apply]
    have testGap:(Cond.eq (.var "query.row") (.add (.var "source.m") (.var "source.n"))).evalB B σ=some (decide (i.val=m+n)):=by
      simp [Cond.evalB,Expr.evalB,Expr.add,fit,hσrow,hσm,hσn,hiB,hm,hn,hmn,Bop.apply]
      exact Bool.beq_eq_decide_eq _ _
    by_cases hi:i.val < m
    · by_cases hj:j.val < n
      · let ii:Fin m:= ⟨i.val,hi⟩
        let jj:Fin n:= ⟨j.val,hj⟩
        let σ₁:=σ.setVar "query.a.row" i.val
        let σ₂:=σ₁.setVar "query.a.col" j.val
        have r₁:Run B (.assign "query.a.row" (.var "query.row")) σ σ₁ 2:=Run.assign (by simp [Expr.evalB,fit,hσrow,hiB])
        have r₂:Run B (.assign "query.a.col" (.var "query.col")) σ₁ σ₂ 2:=Run.assign (by simp [σ₁,Expr.evalB,fit,vars_setVar,hσcol,hjB])
        obtain ⟨τ,rr,po⟩:=RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj) σ₂ (by simpa [σ₁,σ₂,Data,Represents,vars_setVar,arrs_setVar] using And.intro hs.1 (by simp [ii,jj]))
        refine ⟨τ,?_,?_⟩
        · refine Run.mono (K:=33) ?_ (by decide)
          change Run B (.ite _ _ _) σ τ 33
          apply Run.ite_true (K:=29) (by simpa [hi] using testRow)
          change Run B (.ite _ _ _) σ τ 29
          apply Run.ite_true (K:=25) (by simpa [hj] using testCol)
          exact r₁.seq (r₂.seq rr)
        · simpa [CertificateFamilyEntries.pairEntry,hi,hj,ii,jj] using po.2
      · obtain ⟨τ,rr,po⟩:=hz σ trivial
        refine ⟨τ,?_,?_⟩
        · refine Run.mono (K:=14) ?_ (by decide)
          change Run B (.ite _ _ _) σ τ 14
          apply Run.ite_true (K:=10) (by simpa [hi] using testRow)
          change Run B (.ite _ _ _) σ τ 10
          exact Run.ite_false (by simpa [hj] using testCol) rr
        · simpa [CertificateFamilyEntries.pairEntry,hi,hj] using po
    · by_cases hir:i.val < m+n
      · by_cases hj:j.val < n
        · obtain ⟨τ,rr,po⟩:=hz σ trivial
          refine ⟨τ,?_,?_⟩
          · refine Run.mono (K:=20) ?_ (by decide)
            change Run B (.ite _ _ _) σ τ 20
            apply Run.ite_false (K:=16) (by simpa [hi] using testRow)
            change Run B (.ite _ _ _) σ τ 16
            apply Run.ite_true (K:=10) (by simpa [hir] using testDual)
            change Run B (.ite _ _ _) σ τ 10
            exact Run.ite_true (by simpa [hj] using testCol) rr
          · simpa [CertificateFamilyEntries.pairEntry,hi,hir,hj] using po
        · let ii:Fin m:= ⟨j.val-n,by omega⟩
          let jj:Fin n:= ⟨i.val-m,by omega⟩
          let σ₁:=σ.setVar "query.a.row" (j.val-n)
          let σ₂:=σ₁.setVar "query.a.col" (i.val-m)
          have r₁:Run B (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n"))) σ σ₁ 4:=Run.assign (by simp [Expr.evalB,Expr.sub,fit,hσcol,hσn,hjB,hn,hjsub,Bop.apply])
          have r₂:Run B (.assign "query.a.col" (.sub (.var "query.row") (.var "source.m"))) σ₁ σ₂ 4:=Run.assign (by simp [σ₁,Expr.evalB,Expr.sub,fit,vars_setVar,hσrow,hσm,hiB,hm,hisub,Bop.apply])
          obtain ⟨ν,rr,po⟩:=RamCertificateLoad.matrix_spec B M m n P ii jj hM hMB (by omega) (hA ii jj) σ₂ (by simpa [σ₁,σ₂,Data,Represents,vars_setVar,arrs_setVar] using And.intro hs.1 (by simp [ii,jj]))
          obtain ⟨τ,rn,pn⟩:=RamResultNegation.negateResult_spec B (P.A ii jj:ℚ) h1 ν po.2
          refine ⟨τ,?_,?_⟩
          · refine Run.mono (K:=47) ?_ (by decide)
            change Run B (.ite _ _ _) σ τ 47
            apply Run.ite_false (K:=43) (by simpa [hi] using testRow)
            change Run B (.ite _ _ _) σ τ 43
            apply Run.ite_true (K:=37) (by simpa [hir] using testDual)
            change Run B (.ite _ _ _) σ τ 37
            apply Run.ite_false (K:=33) (by simpa [hj] using testCol)
            exact r₁.seq (r₂.seq (rr.seq rn))
          · simpa [CertificateFamilyEntries.pairEntry,hi,hir,hj,ii,jj] using pn
      · have gap:∃ ν,Run B gapEntry σ ν 29∧ FractionOutput
            (if hj:j.val<n then (P.c ⟨j.val,hj⟩:ℚ) else -(P.b ⟨j.val-n,by omega⟩:ℚ)) ν:=by
          by_cases hj:j.val<n
          · let jj:Fin n:= ⟨j.val,hj⟩
            let σ₁:=σ.setVar "query.a.row" j.val
            have ra:Run B (.assign "query.a.row" (.var "query.col")) σ σ₁ 2:=Run.assign (by simp [Expr.evalB,fit,hσcol,hjB])
            obtain ⟨ν,rr,po⟩:=RamCertificateLoad.objective_spec B m n P jj h1 (by omega) ((hc jj).trans_lt hMB) σ₁ (by
              constructor
              · simpa [σ₁,Data,Represents,vars_setVar,arrs_setVar] using hs.1
              · simp [σ₁,vars_setVar,jj])
            refine ⟨ν,?_,by simpa [hj,jj] using po.2⟩
            refine Run.mono (K:=23) ?_ (by decide)
            change Run B (.ite _ _ _) σ ν 23
            exact Run.ite_true (by simpa [hj] using testCol) (ra.seq rr)
          · let jj:Fin m:= ⟨j.val-n,by omega⟩
            let σ₁:=σ.setVar "query.a.row" (j.val-n)
            have ra:Run B (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n"))) σ σ₁ 4:=Run.assign (by simp [Expr.evalB,Expr.sub,fit,hσcol,hσn,hjB,hn,hjsub,Bop.apply])
            obtain ⟨ν,rr,po⟩:=RamCertificateLoad.bound_spec B m n P jj h1 (by omega) ((hb jj).trans_lt hMB) σ₁ (by
              constructor
              · simpa [σ₁,Data,Represents,vars_setVar,arrs_setVar] using hs.1
              · simp [σ₁,vars_setVar,jj])
            obtain ⟨τ,rn,pn⟩:=RamResultNegation.negateResult_spec B (P.b jj:ℚ) h1 ν po.2
            refine ⟨τ,?_,by simpa [hj,jj] using pn⟩
            change Run B (.ite _ _ _) σ τ 29
            exact Run.ite_false (by simpa [hj] using testCol) (ra.seq (rr.seq rn))
        obtain ⟨ν,rr,po⟩:=gap
        by_cases he:i.val=m+n
        · refine ⟨ν,?_,?_⟩
          · refine Run.mono (K:=45) ?_ (by decide)
            change Run B (.ite _ _ _) σ ν 45
            apply Run.ite_false (K:=41) (by simpa [hi] using testRow)
            change Run B (.ite _ _ _) σ ν 41
            apply Run.ite_false (K:=35) (by simpa [hir] using testDual)
            change Run B (.ite _ _ _) σ ν 35
            exact Run.ite_true (by simpa [he] using testGap) rr
          · split_ifs at po with hj <;> simpa [CertificateFamilyEntries.pairEntry,hi,hir,he,hj] using po
        · obtain ⟨τ,rn,pn⟩:=RamResultNegation.negateResult_spec B _ h1 ν po
          refine ⟨τ,?_,?_⟩
          · refine Run.mono (K:=49) ?_ (by decide)
            change Run B (.ite _ _ _) σ τ 49
            apply Run.ite_false (K:=45) (by simpa [hi] using testRow)
            change Run B (.ite _ _ _) σ τ 45
            apply Run.ite_false (K:=39) (by simpa [hir] using testDual)
            change Run B (.ite _ _ _) σ τ 39
            exact Run.ite_false (by simpa [he] using testGap) (rr.seq rn)
          · split_ifs at pn with hj <;> simpa [CertificateFamilyEntries.pairEntry,hi,hir,he,hj] using pn
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
          ((2:Nat)))))
  (j:Fin (Nat.add n m)),
  Nat.le ((1:Nat)) M→
    Nat.lt M B→
      Nat.lt
          (Nat.add
            (Nat.add
              (Nat.add (Nat.mul m n)
                (Nat.mul
                  ((2:Nat)) m))
              (Nat.mul
                ((2:Nat)) n))
            ((8:Nat)))
          B→
        (∀ (r:Fin m) (s:Fin n),Nat.le (@Lax109476.LinearProgram.Program.A Int m n P r s).natAbs M)→
          (∀ (r:Fin m),Nat.le (@Lax109476.LinearProgram.Program.b Int m n P r).natAbs M)→
            (∀ (s:Fin n),Nat.le (@Lax109476.LinearProgram.Program.c Int m n P s).natAbs M)→
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                    (And
                      (@Eq Nat (σ.vars "query.row")
                        (@Fin.val
                          (Nat.add m
                            (Nat.add n
                              ((2:Nat))))
                          i))
                      (@Eq Nat (σ.vars "query.col")
                        (@Fin.val (Nat.add n m) j))))
                Lax109476Proofs.RamPairSelector.selectEntry
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                    (Lax109476Proofs.RamRational.FractionOutput
                      (@Int.cast Rat Rat.instIntCast (@Lax109476Proofs.CertificateFamilyEntries.pairEntry m n P i j))
                      τ))
                ((72:Nat)):= @Lax109476Proofs.RamPairSelector.selectEntry_spec
