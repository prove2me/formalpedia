-- Prove2me | solution 1 for Lax109476Proofs.RamRational.addFraction_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:55:14.33175+00:00
-- url     : https://prove2.me/submissions/c93bd234-c163-484a-8a67-e4288b8d6f21

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native

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

namespace Lax109476Proofs.RamArithmetic
end Lax109476Proofs.RamArithmetic
theorem Lax109476Proofs.RamArithmetic.normalizeFraction_spec:∀ (B n d:Nat),
  Nat.lt n B→
    Nat.lt d B→
      Nat.lt ((0:Nat)) d→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "rat.n") n) (@Eq Nat (σ.vars "rat.d") d))
          Lax109476Proofs.RamArithmetic.normalizeFraction
          (fun (x σ':Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ'.vars "rat.n") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (n.gcd d)))
              (@Eq Nat (σ'.vars "rat.d") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) d (n.gcd d))))
          (HAdd.hAdd
            (HMul.hMul
              ((36:Nat)) d.size)
            ((16:Nat))):= @Lax109476Proofs.RamArithmetic.normalizeFraction_spec_native

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

namespace Lax109476Proofs.RamRational

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

def sumNumerator (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then n₁ * d₂ + n₂ * d₁
  else if n₁ * d₂ < n₂ * d₁ then n₂ * d₁ - n₁ * d₂ else n₁ * d₂ - n₂ * d₁

def sumSign (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then s₁ else if n₁ * d₂ < n₂ * d₁ then s₂ else s₁

theorem fractionValue_sum (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    fractionValue (sumSign s₁ n₁ d₁ s₂ n₂ d₂) (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂:=by
  have hd₁q:(d₁:ℚ) ≠ 0:=by positivity
  have hd₂q:(d₂:ℚ) ≠ 0:=by positivity
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
    by_cases h:n₁ * d₂ < n₂ * d₁
  all_goals first
    | (have hu:n₁ * d₂≤ n₂ * d₁:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hu]
       field_simp <;> ring)
    | (have hv:n₂ * d₁≤ n₁ * d₂:=by omega
       simp [sumSign,sumNumerator,fractionValue,h,Nat.cast_sub hv]
       field_simp <;> ring)

set_option maxHeartbeats 0 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96):=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have hu:n₁ * d₂≤ M * M:=Nat.mul_le_mul hn₁ hd₂
  have hv:n₂ * d₁≤ M * M:=Nat.mul_le_mul hn₂ hd₁
  have huB:n₁ * d₂ < B:=hu.trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=hv.trans_lt (by nlinarith)
  have huvB:n₁ * d₂ + n₂ * d₁ < B:=by nlinarith
  have hdd:d₁ * d₂ < B:=(Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have hnB:sumNumerator s₁ n₁ d₁ s₂ n₂ d₂ < B:=by
    unfold sumNumerator
    split_ifs <;> omega
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  have hss:sumSign s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by unfold sumSign; split_ifs <;> omega
  have hn:=normalizeFraction_output_spec B (sumSign s₁ n₁ d₁ s₂ n₂ d₂)
    (sumNumerator s₁ n₁ d₁ s₂ n₂ d₂) (d₁ * d₂) hss hnB hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  have hsum:=fractionValue_sum s₁ n₁ d₁ s₂ n₂ d₂ hs₁ hs₂ hd₁pos hd₂pos
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "sum.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "sum.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.d"; let c10:Nat:=c8 "right.d"; let c11:Nat:=c0 c9 c10; let c12:Env:=Env.setVar c7 "rat.d" c11; let c13:String→ Nat:=Env.vars c12; let c14:Nat:=c13 "left.s"; let c15:Nat:=c13 "right.s"; let c16:Prop:= @Eq Nat c14 c15; let c17:Prop:=Not c16; let c18:Nat→ Nat→ Nat:=Nat.add; let c19:Nat:=c0 d₁ d₂; let c20:Nat→ Nat:=c18 (c0 ((36:Nat)) (Nat.size c19)); let c21:Nat:=c20 ((96:Nat)); let c22:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (fractionValue s₁ n₁ d₁) (fractionValue s₂ n₂ d₂)); let c23:Env→ Prop:=(fun (x σ':Env) => c22 σ') σ; let c24:Env→ Prop:=fun (σ':Env) => And (Run B addFraction σ σ' c21) (c23 σ'); let c25:Prop:= @Exists Env c24; let c26:Nat→ Env:=Env.setVar c12 "rat.n"; let c27:Nat:=c13 "sum.u"; let c28:Nat:=c13 "sum.v"; let c29:Nat:=c18 c27 c28; let c30:Env:=c26 c29; let c31:Nat:=Env.vars c30 "left.s"; let c32:Env:=Env.setVar c30 "rat.s" c31; let c33:Env→ Nat→ Prop:=Run B normalizeFraction c32; let c34:Nat:=c20 ((16:Nat)); let c35:Nat:=sumSign s₁ n₁ d₁ s₂ n₂ d₂; let c36:Nat:=sumNumerator s₁ n₁ d₁ s₂ n₂ d₂; let c37:Env→ Prop:=FractionOutput (fractionValue c35 c36 c19); let c38:Env→ Prop:=fun (σ':Env) => And (c33 σ' c34) (c37 σ'); let c39:String→ Nat:=Env.vars c32; let c40:Nat→ Nat:=c18 ((1:Nat)); let c41:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c42:Nat→ Nat:=c18 c41; let c43:Nat:=c40 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c44:Nat→ Nat:=c18 c43; let c45:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.d") (Expr.var "right.d"))); let c46:Nat→ Nat:=c18 c45; let c47:Nat→ Nat:=c18 (c40 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c48:Nat:=c40 (Expr.size (Expr.add (Expr.var "sum.u") (Expr.var "sum.v"))); let c49:Nat:=c40 (Expr.size (Expr.var "left.s")); let c50:Nat:=c18 c48 c49; let c51:Nat:=c47 c50; let c52:Nat:=c18 c51 c34; let c53:Nat:=c46 c52; let c54:Nat:=c44 c53; let c55:Com:=Com.assign "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c56:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")); let c57:Com:=Com.assign "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")); let c58:Com:=Com.seq c57 (Com.assign "rat.s" (Expr.var "left.s")); let c59:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")); let c60:Com:=Com.seq c59 (Com.assign "rat.s" (Expr.var "right.s")); let c61:Com:=Com.assign "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")); let c62:Com:=Com.seq c61 (Com.assign "rat.s" (Expr.var "left.s")); let c63:Com:=Com.ite (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62; let c64:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63; let c65:Com:=Com.seq c64 normalizeFraction; let c66:Com:=Com.seq c56 c65; let c67:Nat→ Prop:=Nat.lt c27; let c68:Prop:=c67 c28; let c69:Prop:=Not c68; let c70:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c71:Nat:=c70 c28 c27; let c72:Env:=c26 c71; let c73:Nat:=Env.vars c72 "right.s"; let c74:Env:=Env.setVar c72 "rat.s" c73; let c75:Env→ Nat→ Prop:=Run B normalizeFraction c74; let c76:Env→ Prop:=fun (σ':Env) => And (c75 σ' c34) (c37 σ'); let c77:String→ Nat:=Env.vars c74; let c78:Nat→ Nat:=c18 (c40 (Cond.size (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")))); let c79:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u"))); let c80:Nat:=c40 (Expr.size (Expr.var "right.s")); let c81:Nat:=c18 c79 c80; let c82:Nat:=c78 c81; let c83:Nat:=c47 c82; let c84:Nat:=c18 c83 c34; let c85:Nat:=c46 c84; let c86:Nat:=c44 c85; let c87:Nat:=c70 c27 c28; let c88:Env:=c26 c87; let c89:Nat:=Env.vars c88 "left.s"; let c90:Env:=Env.setVar c88 "rat.s" c89; let c91:Env→ Nat→ Prop:=Run B normalizeFraction c90; let c92:Env→ Prop:=fun (σ':Env) => And (c91 σ' c34) (c37 σ'); let c93:String→ Nat:=Env.vars c90; let c94:Nat:=c40 (Expr.size (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v"))); let c95:Nat:=c18 c94 c49; let c96:Nat:=c78 c95; let c97:Nat:=c47 c96; let c98:Nat:=c18 c97 c34; let c99:Nat:=c46 c98; let c100:Nat:=c44 c99; @Or.casesOn c16 c17 (fun (x:Or c16 c17) => c25) (Classical.em c16) (fun (hcase:c16) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c32 ?_) fun (w:Env) (h:And (c33 w c34) (c37 w)) => @And.casesOn (c33 w c34) (c37 w) (fun (x:And (c33 w c34) (c37 w)) => c25) h fun (left:c33 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c54) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c54 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_1)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c53 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_3)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c52 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_4)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_5)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c32 w c51 c34 (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c32 c50 (RunStep.cond_eq_true B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_6)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_7)) hcase) (RunStep.seq B c57 (Com.assign "rat.s" (Expr.var "left.s")) c12 c30 c32 c48 c49 (RunStep.assign B c12 "rat.n" (Expr.add (Expr.var "sum.u") (Expr.var "sum.v")) c29 (RunStep.eval_add B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c30 "rat.s" (Expr.var "left.s") c31 (RunStep.eval_var B c30 "left.s" (?nAX_g3899_0_0_8))))) left)))) (?nAX_g3899_0_0_9)) ?_)) fun (hcase:c17) => @Or.casesOn c68 c69 (fun (x:Or c68 c69) => c25) (Classical.em c68) (fun (hcase_1:c68) => @Exists.casesOn Env c76 (fun (x:@Exists Env c76) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c74 ?_) fun (w:Env) (h:And (c75 w c34) (c37 w)) => @And.casesOn (c75 w c34) (c37 w) (fun (x:And (c75 w c34) (c37 w)) => c25) h fun (left:c75 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c86) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c86 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_10)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_11)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c85 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_12)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_13)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c84 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_14)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_15)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c74 w c83 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c74 c82 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_16)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_17)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c74 c81 (RunStep.cond_lt_true B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c59 (Com.assign "rat.s" (Expr.var "right.s")) c12 c72 c74 c79 c80 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.v") (Expr.var "sum.u")) c71 (RunStep.eval_sub B c12 (Expr.var "sum.v") (Expr.var "sum.u") c28 c27 (RunStep.eval_var B c12 "sum.v" ?_) (RunStep.eval_var B c12 "sum.u" ?_) ?_)) (RunStep.assign B c72 "rat.s" (Expr.var "right.s") c73 (RunStep.eval_var B c72 "right.s" (?nAX_g3899_0_0_18)))))) left)))) (?nAX_g3899_0_0_19)) ?_)) fun (hcase_1:c69) => @Exists.casesOn Env c92 (fun (x:@Exists Env c92) => c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c36) (And (@Eq Nat (Env.vars σ_1 "rat.d") c19) (@Eq Nat (Env.vars σ_1 "rat.s") c35))) normalizeFraction (fun (x σ':Env) => c37 σ') c34 hn c90 ?_) fun (w:Env) (h:And (c91 w c34) (c37 w)) => @And.casesOn (c91 w c34) (c37 w) (fun (x:And (c91 w c34) (c37 w)) => c25) h fun (left:c91 w c34) (right:c37 w) => @Exists.intro Env c24 w (@And.intro (Run B addFraction σ w c21) (c23 w) (RunStep.mono B addFraction σ w (c42 c100) c21 (RunStep.seq B (Com.assign "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c55 c66) σ c2 w c41 c100 (RunStep.assign B σ "sum.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3899_0_0_20)) (RunStep.eval_var B σ "right.d" (?nAX_g3899_0_0_21)) ?_)) (RunStep.seq B c55 c66 c2 c7 w c43 c99 (RunStep.assign B c2 "sum.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3899_0_0_22)) (RunStep.eval_var B c2 "left.d" (?nAX_g3899_0_0_23)) ?_)) (RunStep.seq B c56 c65 c7 c12 w c45 c98 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c11 (RunStep.eval_mul B c7 (Expr.var "left.d") (Expr.var "right.d") c9 c10 (RunStep.eval_var B c7 "left.d" (?nAX_g3899_0_0_24)) (RunStep.eval_var B c7 "right.d" (?nAX_g3899_0_0_25)) ?_)) (RunStep.seq B c64 normalizeFraction c12 c90 w c97 c34 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c58 c63 c12 c90 c96 (RunStep.cond_eq_false B c12 (Expr.var "left.s") (Expr.var "right.s") c14 c15 (RunStep.eval_var B c12 "left.s" (?nAX_g3899_0_0_26)) (RunStep.eval_var B c12 "right.s" (?nAX_g3899_0_0_27)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "sum.u") (Expr.var "sum.v")) c60 c62 c12 c90 c95 (RunStep.cond_lt_false B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) hcase_1) (RunStep.seq B c61 (Com.assign "rat.s" (Expr.var "left.s")) c12 c88 c90 c94 c49 (RunStep.assign B c12 "rat.n" (Expr.sub (Expr.var "sum.u") (Expr.var "sum.v")) c87 (RunStep.eval_sub B c12 (Expr.var "sum.u") (Expr.var "sum.v") c27 c28 (RunStep.eval_var B c12 "sum.u" ?_) (RunStep.eval_var B c12 "sum.v" ?_) ?_)) (RunStep.assign B c88 "rat.s" (Expr.var "left.s") c89 (RunStep.eval_var B c88 "left.s" (?nAX_g3899_0_0_28)))))) left)))) (?nAX_g3899_0_0_29)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3899_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3899_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [sumNumerator,sumSign]
  all_goals try omega

end Lax109476Proofs.RamRational

end

theorem solution:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  Nat.lt
      (Nat.add
        (Nat.mul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    Nat.le s₁ ((1:Nat))→
      Nat.le s₂ ((1:Nat))→
        Nat.le n₁ M→
          Nat.le d₁ M→
            Nat.le n₂ M→
              Nat.le d₂ M→
                Nat.lt ((0:Nat)) d₁→
                  Nat.lt ((0:Nat)) d₂→
                    Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamRational.fractionInputs s₁ n₁ d₁ s₂ n₂ d₂)
                      Lax109476Proofs.RamRational.addFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (Nat.add
                        (Nat.mul
                          ((36:Nat))
                          (Nat.mul d₁ d₂).size)
                        ((96:Nat))):= @Lax109476Proofs.RamRational.addFraction_spec
