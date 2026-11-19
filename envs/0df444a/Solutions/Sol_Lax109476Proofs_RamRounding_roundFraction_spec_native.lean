-- Prove2me | solution 1 for Lax109476Proofs.RamRounding.roundFraction_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:54:50.570211+00:00
-- url     : https://prove2.me/submissions/da4707ca-5d80-48d2-ae98-ee3d8589366c

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

end Lax109476Proofs.RamRational

end

section

namespace Lax109476Proofs.RamRounding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic RationalRounding

theorem ceilQuotient_int (n d:ℕ) (hd:0 < d):
    Int.ceil ((n:ℚ) / d)=(ceilQuotient n d:ℤ):=by
  have hdq:(0:ℚ) < d:=by exact_mod_cast hd
  have hrem:((n % d:ℕ):ℚ) < d:=by exact_mod_cast Nat.mod_lt n hd
  have heq:(d:ℚ) * (n / d:ℕ) + (n % d:ℕ)=n:=by
    exact_mod_cast Nat.div_add_mod n d
  apply Int.ceil_eq_iff.mpr
  rw [lt_div_iff₀ hdq,div_le_iff₀ hdq]
  by_cases hz:n % d=0
  · rw [hz,Nat.cast_zero,add_zero] at heq
    simp only [ceilQuotient,if_pos hz,add_zero,Int.cast_natCast]
    constructor <;> nlinarith
  · have hrpos:(0:ℚ) < ((n % d:ℕ):ℚ):=by exact_mod_cast Nat.pos_of_ne_zero hz
    simp only [ceilQuotient,if_neg hz,Int.cast_add,Int.cast_natCast,Int.cast_one,
      Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith

def roundMagnitude (s n d D:ℕ):ℕ:=
  if s=1 then ceilQuotient (n * D) d else (n * D) / d

theorem roundMagnitude_correct (s n d D:ℕ) (hd:0 < d):
    fractionValue s (roundMagnitude s n d D) D=roundDown (fractionValue s n d) D:=by
  have hpos:(n:ℚ) / d * D=((n * D:ℕ):ℚ) / d:=by push_cast; ring
  have hneg:-(n:ℚ) / d * D=-(((n * D:ℕ):ℚ) / d):=by push_cast; ring
  unfold fractionValue roundMagnitude roundDown
  by_cases hs:s=1
  · simp only [if_pos hs,hneg,Int.floor_neg,ceilQuotient_int (n * D) d hd,
      Int.cast_neg,Int.cast_natCast]
  · simp only [if_neg hs,hpos,Rat.floor_natCast_div_natCast]
    rw [← Int.natCast_ediv,Int.cast_natCast]

set_option maxHeartbeats 0 in
theorem roundFraction_spec (B M s n d D:ℕ) (hB:2 * M ^ 2 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) roundFraction
      (fun _ σ' => FractionOutput (roundDown (fractionValue s n d) D) σ')
      (36 * D.size + 96):=by
  have hM:M < B:=by nlinarith
  have hnB:=hn.trans_lt hM
  have hdB:=hd.trans_lt hM
  have hDB:=hD.trans_lt hM
  have ha:n * D≤ M * M:=Nat.mul_le_mul hn hD
  have haB:n * D < B:=ha.trans_lt (by nlinarith)
  have hqB:n * D / d < B:=(Nat.div_le_self _ _).trans_lt haB
  have hqdB:n * D / d * d < B:=(Nat.div_mul_le_self _ _).trans_lt haB
  have hrB:n * D - n * D / d * d < B:=(Nat.sub_le _ _).trans_lt haB
  have hq1B:n * D / d + 1 < B:=by have hq:=Nat.div_le_self (n * D) d; nlinarith
  have h1:1 < B:=by nlinarith
  have hsB:=hs.trans_lt h1
  have hmB:roundMagnitude s n d D < B:=by
    unfold roundMagnitude ceilQuotient
    split_ifs <;> omega
  have hnorm:=normalizeFraction_output_spec B s (roundMagnitude s n d D) D
    hs hmB hDB hDpos
  have hc:=roundMagnitude_correct s n d D hdpos
  have hmod:n * D - n * D / d * d=n * D % d:=by
    simpa only [Nat.mul_comm] using (Nat.mod_def (n * D) d).symm
  rintro σ ⟨hσs,hσn,hσd,hσD⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "grid.D"); let c2:Env:=Env.setVar σ "round.a" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "round.a"; let c5:Nat:=c3 "left.d"; let c6:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c4 c5; let c7:Env:=Env.setVar c2 "round.q" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "round.a"; let c10:Nat:=c8 "round.q"; let c11:Nat:=c8 "left.d"; let c12:Nat:=c0 c10 c11; let c13:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c9 c12; let c14:Env:=Env.setVar c7 "round.r" c13; let c15:Nat:=Env.vars c14 "round.q"; let c16:Env:=Env.setVar c14 "rat.n" c15; let c17:String→ Nat:=Env.vars c16; let c18:Nat:=c17 "left.s"; let c19:Prop:= @Eq Nat c18 ((1:Nat)); let c20:Prop:=Not c19; let c21:Nat→ Nat→ Nat:=Nat.add; let c22:Nat→ Nat:=c21 (c0 ((36:Nat)) (Nat.size D)); let c23:Nat:=c22 ((96:Nat)); let c24:Env→ Prop:=FractionOutput (roundDown (fractionValue s n d) D); let c25:Env→ Prop:=(fun (x σ':Env) => c24 σ') σ; let c26:Env→ Prop:=fun (σ':Env) => And (Run B roundFraction σ σ' c23) (c25 σ'); let c27:Prop:= @Exists Env c26; let c28:Nat:=c17 "round.r"; let c29:Prop:= @Eq Nat c28 ((0:Nat)); let c30:Prop:=Not c29; let c31:String→ Nat→ Env:=Env.setVar c16; let c32:Env:=c31 "rat.s" c18; let c33:Nat:=Env.vars c32 "grid.D"; let c34:Env:=Env.setVar c32 "rat.d" c33; let c35:Env→ Nat→ Prop:=Run B normalizeFraction c34; let c36:Nat:=c22 ((16:Nat)); let c37:Env→ Prop:=FractionOutput (fractionValue s (roundMagnitude s n d D) D); let c38:Env→ Prop:=fun (σ':Env) => And (c35 σ' c36) (c37 σ'); let c39:String→ Nat:=Env.vars c34; let c40:Nat→ Nat:=c21 ((1:Nat)); let c41:Nat:=c40 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))); let c42:Nat→ Nat:=c21 c41; let c43:Nat:=c40 (Expr.size (Expr.div (Expr.var "round.a") (Expr.var "left.d"))); let c44:Nat→ Nat:=c21 c43; let c45:Expr:=Expr.sub (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")); let c46:Nat:=c40 (Expr.size c45); let c47:Nat→ Nat:=c21 c46; let c48:Nat:=c40 (Expr.size (Expr.var "round.q")); let c49:Nat→ Nat:=c21 c48; let c50:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c51:Nat→ Nat:=c21 (c40 (Cond.size c50)); let c52:Cond:=Cond.eq (Expr.var "round.r") (Expr.lit ((0:Nat))); let c53:Nat→ Nat:=c21 (c40 (Cond.size c52)); let c54:Nat:=c53 ((1:Nat)); let c55:Nat:=c51 c54; let c56:Nat:=c40 (Expr.size (Expr.var "left.s")); let c57:Nat:=c40 (Expr.size (Expr.var "grid.D")); let c58:Nat:=c21 c57 c36; let c59:Nat:=c21 c56 c58; let c60:Nat:=c21 c55 c59; let c61:Nat:=c49 c60; let c62:Nat:=c47 c61; let c63:Nat:=c44 c62; let c64:Com:=Com.assign "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")); let c65:Com:=Com.assign "round.r" c45; let c66:Expr:=Expr.add (Expr.var "rat.n") (Expr.lit ((1:Nat))); let c67:Com:=Com.assign "rat.n" c66; let c68:Com:=Com.ite c52 Com.skip c67; let c69:Com:=Com.ite c50 c68 Com.skip; let c70:Com:=Com.seq (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction); let c71:Com:=Com.seq c69 c70; let c72:Com:=Com.seq (Com.assign "rat.n" (Expr.var "round.q")) c71; let c73:Com:=Com.seq c65 c72; let c74:Nat:=c17 "rat.n"; let c75:Nat:=c21 c74 ((1:Nat)); let c76:Env:=c31 "rat.n" c75; let c77:Nat:=Env.vars c76 "left.s"; let c78:Env:=Env.setVar c76 "rat.s" c77; let c79:Nat:=Env.vars c78 "grid.D"; let c80:Env:=Env.setVar c78 "rat.d" c79; let c81:Env→ Nat→ Prop:=Run B normalizeFraction c80; let c82:Env→ Prop:=fun (σ':Env) => And (c81 σ' c36) (c37 σ'); let c83:String→ Nat:=Env.vars c80; let c84:Nat:=c40 (Expr.size c66); let c85:Nat:=c53 c84; let c86:Nat:=c51 c85; let c87:Nat:=c21 c86 c59; let c88:Nat:=c49 c87; let c89:Nat:=c47 c88; let c90:Nat:=c44 c89; let c91:Nat:=c51 ((1:Nat)); let c92:Nat:=c21 c91 c59; let c93:Nat:=c49 c92; let c94:Nat:=c47 c93; let c95:Nat:=c44 c94; @Or.casesOn c19 c20 (fun (x:Or c19 c20) => c27) (Classical.em c19) (fun (hcase:c19) => @Or.casesOn c29 c30 (fun (x:Or c29 c30) => c27) (Classical.em c29) (fun (hcase_1:c29) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c34 ?_) fun (w:Env) (h:And (c35 w c36) (c37 w)) => @And.casesOn (c35 w c36) (c37 w) (fun (x:And (c35 w c36) (c37 w)) => c27) h fun (left:c35 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c63) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c63 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_0)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_1)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c62 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_2)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c61 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_3)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c60 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c16 w c55 c59 (RunStep.ite_true B c50 c68 Com.skip c16 c16 c54 (RunStep.cond_eq_true B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_4)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.ite_true B c52 Com.skip c67 c16 c16 ((1:Nat)) (RunStep.cond_eq_true B c16 (Expr.var "round.r") (Expr.lit ((0:Nat))) c28 ((0:Nat)) (RunStep.eval_var B c16 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c16 (?nAX_g3913_0_0_5)) hcase_1) (RunStep.skip B c16))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c16 c32 w c56 c58 (RunStep.assign B c16 "rat.s" (Expr.var "left.s") c18 (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_6))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c32 c34 w c57 c36 (RunStep.assign B c32 "rat.d" (Expr.var "grid.D") c33 (RunStep.eval_var B c32 "grid.D" (?nAX_g3913_0_0_7))) left))))))) (?nAX_g3913_0_0_8)) ?_)) fun (hcase_1:c30) => @Exists.casesOn Env c82 (fun (x:@Exists Env c82) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c80 ?_) fun (w:Env) (h:And (c81 w c36) (c37 w)) => @And.casesOn (c81 w c36) (c37 w) (fun (x:And (c81 w c36) (c37 w)) => c27) h fun (left:c81 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c90) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c90 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_9)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_10)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c89 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_11)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c88 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_12)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c87 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c76 w c86 c59 (RunStep.ite_true B c50 c68 Com.skip c16 c76 c85 (RunStep.cond_eq_true B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_13)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.ite_false B c52 Com.skip c67 c16 c76 c84 (RunStep.cond_eq_false B c16 (Expr.var "round.r") (Expr.lit ((0:Nat))) c28 ((0:Nat)) (RunStep.eval_var B c16 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c16 (?nAX_g3913_0_0_14)) hcase_1) (RunStep.assign B c16 "rat.n" c66 c75 (RunStep.eval_add B c16 (Expr.var "rat.n") (Expr.lit ((1:Nat))) c74 ((1:Nat)) (RunStep.eval_var B c16 "rat.n" ?_) (RunStep.eval_lit B ((1:Nat)) c16 h1) ?_)))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c76 c78 w c56 c58 (RunStep.assign B c76 "rat.s" (Expr.var "left.s") c77 (RunStep.eval_var B c76 "left.s" (?nAX_g3913_0_0_15))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c78 c80 w c57 c36 (RunStep.assign B c78 "rat.d" (Expr.var "grid.D") c79 (RunStep.eval_var B c78 "grid.D" (?nAX_g3913_0_0_16))) left))))))) (?nAX_g3913_0_0_17)) ?_)) fun (hcase:c20) => @Exists.casesOn Env c38 (fun (x:@Exists Env c38) => c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (roundMagnitude s n d D)) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => c37 σ') c36 hnorm c34 ?_) fun (w:Env) (h:And (c35 w c36) (c37 w)) => @And.casesOn (c35 w c36) (c37 w) (fun (x:And (c35 w c36) (c37 w)) => c27) h fun (left:c35 w c36) (right:c37 w) => @Exists.intro Env c26 w (@And.intro (Run B roundFraction σ w c23) (c25 w) (RunStep.mono B roundFraction σ w (c42 c95) c23 (RunStep.seq B (Com.assign "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D"))) (Com.seq c64 c73) σ c2 w c41 c95 (RunStep.assign B σ "round.a" (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3913_0_0_18)) (RunStep.eval_var B σ "grid.D" (?nAX_g3913_0_0_19)) ?_)) (RunStep.seq B c64 c73 c2 c7 w c43 c94 (RunStep.assign B c2 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c6 (RunStep.eval_div B c2 (Expr.var "round.a") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "round.a" ?_) (RunStep.eval_var B c2 "left.d" (?nAX_g3913_0_0_20)) ?_)) (RunStep.seq B c65 c72 c7 c14 w c46 c93 (RunStep.assign B c7 "round.r" c45 c13 (RunStep.eval_sub B c7 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c9 c12 (RunStep.eval_var B c7 "round.a" ?_) (RunStep.eval_mul B c7 (Expr.var "round.q") (Expr.var "left.d") c10 c11 (RunStep.eval_var B c7 "round.q" ?_) (RunStep.eval_var B c7 "left.d" (?nAX_g3913_0_0_21)) ?_) ?_)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "round.q")) c71 c14 c16 w c48 c92 (RunStep.assign B c14 "rat.n" (Expr.var "round.q") c15 (RunStep.eval_var B c14 "round.q" ?_)) (RunStep.seq B c69 c70 c16 c16 w c91 c59 (RunStep.ite_false B c50 c68 Com.skip c16 c16 ((1:Nat)) (RunStep.cond_eq_false B c16 (Expr.var "left.s") (Expr.lit ((1:Nat))) c18 ((1:Nat)) (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_22)) (RunStep.eval_lit B ((1:Nat)) c16 h1) hcase) (RunStep.skip B c16)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c16 c32 w c56 c58 (RunStep.assign B c16 "rat.s" (Expr.var "left.s") c18 (RunStep.eval_var B c16 "left.s" (?nAX_g3913_0_0_23))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c32 c34 w c57 c36 (RunStep.assign B c32 "rat.d" (Expr.var "grid.D") c33 (RunStep.eval_var B c32 "grid.D" (?nAX_g3913_0_0_24))) left))))))) (?nAX_g3913_0_0_25)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3913_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3913_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [roundMagnitude,ceilQuotient]

end Lax109476Proofs.RamRounding

end

theorem solution:∀ (B M s n d D:Nat),
  Nat.lt
      (Nat.add
        (Nat.mul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    Nat.le s ((1:Nat))→
      Nat.le n M→
        Nat.le d M→
          Nat.le D M→
            Nat.lt ((0:Nat)) d→
              Nat.lt ((0:Nat)) D→
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                    And (@Eq Nat (σ.vars "left.s") s)
                      (And (@Eq Nat (σ.vars "left.n") n)
                        (And (@Eq Nat (σ.vars "left.d") d) (@Eq Nat (σ.vars "grid.D") D))))
                  Lax109476Proofs.RamRounding.roundFraction
                  (fun (x σ':Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamRational.FractionOutput
                      (Lax109476Proofs.RationalRounding.roundDown (Lax109476Proofs.RamRational.fractionValue s n d) D)
                      σ')
                  (Nat.add
                    (Nat.mul
                      ((36:Nat)) D.size)
                    ((96:Nat))):= @Lax109476Proofs.RamRounding.roundFraction_spec
