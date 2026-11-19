-- Prove2me | solution 1 for Lax109476Proofs.RamRounding.upperRootFraction_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:55:58.748302+00:00
-- url     : https://prove2.me/submissions/f674ce0b-8f36-435d-a473-623420f6b272

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Sqrt
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

namespace Lax109476Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

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

end Lax109476Proofs.RamArithmetic

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

namespace Lax109476Proofs.RamSquareRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

theorem sqrtStep_spec (B N l u:ℕ) (hB:(2 * (N + 1) + 1) ^ 2 < B)
    (hlu:l < u) (hu:u≤ N + 1) (hwide:1 < u - l)
    (hl:l * l≤ N) (hun:N < u * u):
    Spec B (fun σ => σ.vars "sqrt.n"=N∧ σ.vars "sqrt.lo"=l∧ σ.vars "sqrt.hi"=u)
      sqrtStep (fun _ σ' => σ'.vars "sqrt.n"=N∧
        σ'.vars "sqrt.lo" < σ'.vars "sqrt.hi" ∧ σ'.vars "sqrt.hi" ≤ N + 1∧
        σ'.vars "sqrt.lo" * σ'.vars "sqrt.lo" ≤ N∧
        N < σ'.vars "sqrt.hi" * σ'.vars "sqrt.hi" ∧
        (σ'.vars "sqrt.hi" - σ'.vars "sqrt.lo" - 1).size < (u - l - 1).size) 20:=by
  let m:=(l + u) / 2
  have hquot:=Nat.div_add_mod (l + u) 2
  have hrem:(l + u) % 2 < 2:=Nat.mod_lt _ (by decide)
  have hm:l < m∧ m < u:=by dsimp [m]; omega
  have hN:N < B:=by nlinarith
  have hlB:l < B:=by nlinarith
  have huB:u < B:=by nlinarith
  have hsum:l + u < B:=by nlinarith
  have hmB:m < B:=hm.2.trans huB
  have hmSq:m * m < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  have hdropLeft:m - l - 1≤ (u - l - 1) / 2:=by dsimp [m]; omega
  have hdropRight:u - m - 1≤ (u - l - 1) / 2:=by dsimp [m]; omega
  have hgap:0 < u - l - 1:=by omega
  have hsLeft:=(Nat.size_le_size hdropLeft).trans_lt (size_half_lt _ hgap)
  have hsRight:=(Nat.size_le_size hdropRight).trans_lt (size_half_lt _ hgap)
  rintro σ ⟨hσn,hσl,hσu⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "sqrt.lo") (Env.vars σ "sqrt.hi"); let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c1 ((2:Nat)); let c3:Env:=Env.setVar σ "sqrt.mid" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "sqrt.n"; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c4 "sqrt.mid"; let c8:Nat:=c6 c7 c7; let c9:Prop:=Nat.lt c5 c8; let c10:Prop:=Not c9; let c11:Nat:=c0 N ((1:Nat)); let c12:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c13:Nat:=Nat.size (c12 (c12 u l) ((1:Nat))); let c14:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "sqrt.n") N) (And (Nat.lt (Env.vars σ' "sqrt.lo") (Env.vars σ' "sqrt.hi")) (And (Nat.le (Env.vars σ' "sqrt.hi") c11) (And (Nat.le (c6 (Env.vars σ' "sqrt.lo") (Env.vars σ' "sqrt.lo")) N) (And (Nat.lt N (c6 (Env.vars σ' "sqrt.hi") (Env.vars σ' "sqrt.hi"))) (Nat.lt (Nat.size (c12 (c12 (Env.vars σ' "sqrt.hi") (Env.vars σ' "sqrt.lo")) ((1:Nat)))) c13)))))) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B sqrtStep σ σ' ((20:Nat))) (c14 σ'); let c16:String→ Nat→ Env:=Env.setVar c3; let c17:Env:=c16 "sqrt.hi" c7; let c18:Nat→ Nat:=c0 ((1:Nat)); let c19:Expr:=Expr.div (Expr.add (Expr.var "sqrt.lo") (Expr.var "sqrt.hi")) (Expr.lit ((2:Nat))); let c20:Nat:=c18 (Expr.size c19); let c21:Cond:=Cond.lt (Expr.var "sqrt.n") (Expr.mul (Expr.var "sqrt.mid") (Expr.var "sqrt.mid")); let c22:Nat:=c18 (Expr.size (Expr.var "sqrt.mid")); let c23:Nat:=c0 (c18 (Cond.size c21)) c22; let c24:Nat:=c0 c20 c23; let c25:String→ Nat:=Env.vars c17; let c26:Nat:=c25 "sqrt.lo"; let c27:Nat:=c25 "sqrt.hi"; let c28:Env:=c16 "sqrt.lo" c7; let c29:String→ Nat:=Env.vars c28; let c30:Nat:=c29 "sqrt.lo"; let c31:Nat:=c29 "sqrt.hi"; @Or.casesOn c9 c10 (fun (x:Or c9 c10) => @Exists Env c15) (Classical.em c9) (fun (hcase:c9) => @Exists.intro Env c15 c17 (@And.intro (Run B sqrtStep σ c17 ((20:Nat))) (c14 c17) (RunStep.mono B sqrtStep σ c17 c24 ((20:Nat)) (RunStep.seq B (Com.assign "sqrt.mid" c19) (Com.ite c21 (Com.assign "sqrt.hi" (Expr.var "sqrt.mid")) (Com.assign "sqrt.lo" (Expr.var "sqrt.mid"))) σ c3 c17 c20 c23 (RunStep.assign B σ "sqrt.mid" c19 c2 (RunStep.eval_div B σ (Expr.add (Expr.var "sqrt.lo") (Expr.var "sqrt.hi")) (Expr.lit ((2:Nat))) c1 ((2:Nat)) (RunStep.eval_add B σ (Expr.var "sqrt.lo") (Expr.var "sqrt.hi") (Env.vars σ "sqrt.lo") (Env.vars σ "sqrt.hi") (RunStep.eval_var B σ "sqrt.lo" (?nAX_g3903_0_0_0)) (RunStep.eval_var B σ "sqrt.hi" (?nAX_g3903_0_0_1)) (?nAX_g3903_0_0_2)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g3903_0_0_3))) (RunStep.ite_true B c21 (Com.assign "sqrt.hi" (Expr.var "sqrt.mid")) (Com.assign "sqrt.lo" (Expr.var "sqrt.mid")) c3 c17 c22 (RunStep.cond_lt_true B c3 (Expr.var "sqrt.n") (Expr.mul (Expr.var "sqrt.mid") (Expr.var "sqrt.mid")) c5 c8 (RunStep.eval_var B c3 "sqrt.n" (?nAX_g3903_0_0_4)) (RunStep.eval_mul B c3 (Expr.var "sqrt.mid") (Expr.var "sqrt.mid") c7 c7 (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_5)) (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_6)) ?_) hcase) (RunStep.assign B c3 "sqrt.hi" (Expr.var "sqrt.mid") c7 (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_7))))) (?nAX_g3903_0_0_8)) ?_)) fun (hcase:c10) => @Exists.intro Env c15 c28 (@And.intro (Run B sqrtStep σ c28 ((20:Nat))) (c14 c28) (RunStep.mono B sqrtStep σ c28 c24 ((20:Nat)) (RunStep.seq B (Com.assign "sqrt.mid" c19) (Com.ite c21 (Com.assign "sqrt.hi" (Expr.var "sqrt.mid")) (Com.assign "sqrt.lo" (Expr.var "sqrt.mid"))) σ c3 c28 c20 c23 (RunStep.assign B σ "sqrt.mid" c19 c2 (RunStep.eval_div B σ (Expr.add (Expr.var "sqrt.lo") (Expr.var "sqrt.hi")) (Expr.lit ((2:Nat))) c1 ((2:Nat)) (RunStep.eval_add B σ (Expr.var "sqrt.lo") (Expr.var "sqrt.hi") (Env.vars σ "sqrt.lo") (Env.vars σ "sqrt.hi") (RunStep.eval_var B σ "sqrt.lo" (?nAX_g3903_0_0_9)) (RunStep.eval_var B σ "sqrt.hi" (?nAX_g3903_0_0_10)) (?nAX_g3903_0_0_11)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g3903_0_0_12))) (RunStep.ite_false B c21 (Com.assign "sqrt.hi" (Expr.var "sqrt.mid")) (Com.assign "sqrt.lo" (Expr.var "sqrt.mid")) c3 c28 c22 (RunStep.cond_lt_false B c3 (Expr.var "sqrt.n") (Expr.mul (Expr.var "sqrt.mid") (Expr.var "sqrt.mid")) c5 c8 (RunStep.eval_var B c3 "sqrt.n" (?nAX_g3903_0_0_13)) (RunStep.eval_mul B c3 (Expr.var "sqrt.mid") (Expr.var "sqrt.mid") c7 c7 (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_14)) (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_15)) ?_) hcase) (RunStep.assign B c3 "sqrt.lo" (Expr.var "sqrt.mid") c7 (RunStep.eval_var B c3 "sqrt.mid" (?nAX_g3903_0_0_16))))) (?nAX_g3903_0_0_17)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3903_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3903_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [m]
  all_goals omega

def SqrtInvariant (N:ℕ) (σ:Env):Prop:=
  σ.vars "sqrt.n"=N∧ σ.vars "sqrt.lo" < σ.vars "sqrt.hi" ∧
    σ.vars "sqrt.hi" ≤ N + 1∧
    σ.vars "sqrt.lo" * σ.vars "sqrt.lo" ≤ N∧
    N < σ.vars "sqrt.hi" * σ.vars "sqrt.hi"

theorem sqrtLoop_spec (B N l u:ℕ) (hB:(2 * (N + 1) + 1) ^ 2 < B)
    (hlu:l < u) (hu:u≤ N + 1) (hl:l * l≤ N) (hun:N < u * u):
    Spec B (fun σ => σ.vars "sqrt.n"=N∧ σ.vars "sqrt.lo"=l∧ σ.vars "sqrt.hi"=u)
      sqrtLoop (fun _ σ' => σ'.vars "sqrt.n"=N∧
        σ'.vars "sqrt.lo"=Nat.sqrt N∧ σ'.vars "sqrt.hi"=Nat.sqrt N + 1)
      (26 * (u - l - 1).size + 6):=by
  have h1:1 < B:=by nlinarith
  have huB:N + 1 < B:=by nlinarith
  have hdef (σ:Env) (hI:SqrtInvariant N σ):
      ∃ v, (Cond.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))).evalB B σ=some v:=by
    have hhi:=hI.2.2.1.trans_lt huB
    have hlo:=hI.2.1.trans hhi
    exact ⟨_,evalB_condLt (evalB_lit h1)
      (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))⟩
  have hloop:Spec B
      (fun σ => σ.vars "sqrt.n"=N∧ σ.vars "sqrt.lo"=l∧ σ.vars "sqrt.hi"=u)
      sqrtLoop (fun _ σ' => SqrtInvariant N σ'∧
        (Cond.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))).evalB B σ'=some false)
      (26 * (u - l - 1).size + 6):=by
    apply Spec.while_count (SqrtInvariant N)
      (fun σ => (σ.vars "sqrt.hi" - σ.vars "sqrt.lo" - 1).size) 20 hdef
    · rintro σ ⟨hI,hc⟩
      have hhi:=hI.2.2.1.trans_lt huB
      have hlo:=hI.2.1.trans hhi
      have hwide:1 < σ.vars "sqrt.hi" - σ.vars "sqrt.lo" :=by
        rw [evalB_condLt (evalB_lit h1)
          (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))] at hc
        exact of_decide_eq_true (Option.some.inj hc)
      obtain ⟨τ,hr,hτ⟩:=sqrtStep_spec B N _ _ hB hI.2.1 hI.2.2.1 hwide
        hI.2.2.2.1 hI.2.2.2.2 σ ⟨hI.1,rfl,rfl⟩
      exact ⟨τ,hr, ⟨hτ.1,hτ.2.1,hτ.2.2.1,hτ.2.2.2.1,hτ.2.2.2.2.1⟩,
        hτ.2.2.2.2.2⟩
    · rintro σ ⟨hσn,hσl,hσu⟩
      simp only [SqrtInvariant,hσn,hσl,hσu]
      exact ⟨True.intro,hlu,hu,hl,hun⟩
    · rintro σ ⟨_,hσl,hσu⟩
      simp [hσl,hσu]
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hhi:=hI.2.2.1.trans_lt huB
  have hlo:=hI.2.1.trans hhi
  have hnarrow:τ.vars "sqrt.hi" - τ.vars "sqrt.lo" ≤ 1:=by
    rw [evalB_condLt (evalB_lit h1)
      (evalB_bin (evalB_var hhi) (evalB_var hlo) ((Nat.sub_le _ _).trans_lt hhi))] at hc
    have hn:=of_decide_eq_false (Option.some.inj hc)
    change ¬1 < τ.vars "sqrt.hi" - τ.vars "sqrt.lo" at hn
    omega
  have he:τ.vars "sqrt.hi"=τ.vars "sqrt.lo" + 1:=by have:=hI.2.1; omega
  have hs:τ.vars "sqrt.lo"=Nat.sqrt N:=Nat.eq_sqrt.mpr
    ⟨hI.2.2.2.1,by simpa only [he] using hI.2.2.2.2⟩
  exact ⟨hI.1,hs,by rw [he,hs]⟩

theorem squareRoot_spec (B N:ℕ) (hB:(2 * (N + 1) + 1) ^ 2 < B):
    Spec B (fun σ => σ.vars "sqrt.n"=N) squareRoot
      (fun _ σ' => σ'.vars "sqrt.lo"=Nat.sqrt N) (26 * N.size + 12):=by
  have hN:N < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hNp:N + 1 < B:=by nlinarith
  have hs:=sqrtLoop_spec B N 0 (N + 1) hB (by omega) le_rfl
    (by simp) (by nlinarith)
  intro σ hσ
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "sqrt.lo" ((0:Nat)); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=Env.vars c0 "sqrt.n"; let c3:Nat:=c1 c2 ((1:Nat)); let c4:Env:=Env.setVar c0 "sqrt.hi" c3; let c5:Env→ Nat→ Prop:=Run B sqrtLoop c4; let c6:Nat→ Nat:=Nat.mul ((26:Nat)); let c7:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c8:Nat:=c1 N ((1:Nat)); let c9:Nat:=c1 (c6 (Nat.size (c7 (c7 c8 ((0:Nat))) ((1:Nat))))) ((6:Nat)); let c10:Nat:=c1 (Nat.sqrt N) ((1:Nat)); let c11:Env→ Prop:=fun (σ':Env) => And (c5 σ' c9) (And (@Eq Nat (Env.vars σ' "sqrt.n") N) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt N)) (@Eq Nat (Env.vars σ' "sqrt.hi") c10))); let c12:Nat:=c1 (c6 (Nat.size N)) ((12:Nat)); let c13:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt N)) σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B squareRoot σ σ' c12) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:String→ Nat:=Env.vars c4; let c17:Nat→ Nat:=c1 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.lit ((0:Nat)))); let c19:Expr:=Expr.add (Expr.var "sqrt.n") (Expr.lit ((1:Nat))); let c20:Nat:=c17 (Expr.size c19); let c21:Nat:=c1 c20 c9; let c22:Com:=Com.assign "sqrt.hi" c19; @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c15) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "sqrt.n") N) (And (@Eq Nat (Env.vars σ_1 "sqrt.lo") ((0:Nat))) (@Eq Nat (Env.vars σ_1 "sqrt.hi") c8))) sqrtLoop (fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "sqrt.n") N) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt N)) (@Eq Nat (Env.vars σ' "sqrt.hi") c10))) c9 hs c4 ?_) fun (w:Env) (h:And (c5 w c9) (And (@Eq Nat (Env.vars w "sqrt.n") N) (And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt N)) (@Eq Nat (Env.vars w "sqrt.hi") c10)))) => let c0_1:Prop:= @Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt N); let c1_1:Prop:=And (@Eq Nat (Env.vars w "sqrt.n") N) (And c0_1 (@Eq Nat (Env.vars w "sqrt.hi") c10)); @And.casesOn (c5 w c9) c1_1 (fun (x:And (c5 w c9) c1_1) => c15) h fun (left:c5 w c9) (right:c1_1) => @Exists.intro Env c14 w (@And.intro (Run B squareRoot σ w c12) (c13 w) (RunStep.mono B squareRoot σ w (c1 c18 c21) c12 (RunStep.seq B (Com.assign "sqrt.lo" (Expr.lit ((0:Nat)))) (Com.seq c22 sqrtLoop) σ c0 w c18 c21 (RunStep.assign B σ "sqrt.lo" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3906_0_0_0))) (RunStep.seq B c22 sqrtLoop c0 c4 w c20 c9 (RunStep.assign B c0 "sqrt.hi" c19 c3 (RunStep.eval_add B c0 (Expr.var "sqrt.n") (Expr.lit ((1:Nat))) c2 ((1:Nat)) (RunStep.eval_var B c0 "sqrt.n" (?nAX_g3906_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c0 h1) (?nAX_g3906_0_0_2))) left)) (?nAX_g3906_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3906_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3906_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3906_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3906_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

end Lax109476Proofs.RamSquareRoot

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

theorem ceilQuotient_nat (n d:ℕ) (hd:0 < d):
    Nat.ceil ((n:ℚ) / d)=ceilQuotient n d:=by
  apply Int.ofNat_inj.mp
  rw [Int.natCast_ceil_eq_ceil (by positivity),ceilQuotient_int n d hd]

theorem upperMagnitude_correct (s n d D:ℕ) (hd:0 < d):
    upperMagnitude s n d D=Nat.ceil (fractionValue s n d * (D:ℚ) ^ 2):=by
  by_cases hs:s=1
  · have hq:fractionValue s n d * (D:ℚ) ^ 2≤ 0:=by
      simp only [fractionValue,if_pos hs,neg_div]
      have hp:(0:ℚ)≤ (n:ℚ) / d * (D:ℚ) ^ 2:=by positivity
      nlinarith
    rw [upperMagnitude,if_pos hs]
    exact (Nat.ceil_eq_zero.mpr hq).symm
  · have he:fractionValue s n d * (D:ℚ) ^ 2=((n * D ^ 2:ℕ):ℚ) / d:=by
      simp only [fractionValue,if_neg hs,Nat.cast_mul,Nat.cast_pow]
      ring
    rw [he,ceilQuotient_nat _ _ hd]
    simp [upperMagnitude,hs]

theorem squareRoot_grid_spec (B N D:ℕ) (hB:(2 * (N + 1) + 1) ^ 2 < B):
    Spec B (fun σ => σ.vars "sqrt.n"=N∧ σ.vars "grid.D"=D) RamSquareRoot.squareRoot
      (fun _ τ => τ.vars "sqrt.lo"=Nat.sqrt N∧ τ.vars "grid.D"=D)
      (26 * N.size + 12):=by
  rintro σ ⟨hσn,hσD⟩
  obtain ⟨τ,hr,hτ⟩:=RamSquareRoot.squareRoot_spec B N hB σ hσn
  exact ⟨τ,hr,hτ, (hr.frame_var "grid.D" (by decide)).trans hσD⟩

set_option maxHeartbeats 0 in
theorem upperRootFraction_spec (B M s n d D:ℕ)
    (hB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) upperRootFraction
      (fun _ σ' => FractionOutput (sqrtUpper (fractionValue s n d) D) σ')
      (26 * (upperMagnitude s n d D).size + 36 * D.size + 128):=by
  have hMpos:1≤ M:=hDpos.trans_le hD
  have hMpow:M≤ M ^ 3:=le_self_pow hMpos (by decide)
  have hM:M < B:=by nlinarith
  have hnB:=hn.trans_lt hM
  have hdB:=hd.trans_lt hM
  have hDB:=hD.trans_lt hM
  have ha:n * D * D≤ M ^ 3:=by
    simpa only [pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hn hD) hD
  have haB:n * D * D < B:=ha.trans_lt (by nlinarith)
  have hpartial:n * D < B:=(Nat.le_mul_of_pos_right _ hDpos).trans_lt haB
  have hqB:n * D * D / d < B:=(Nat.div_le_self _ _).trans_lt haB
  have hqdB:n * D * D / d * d < B:=(Nat.div_mul_le_self _ _).trans_lt haB
  have hrB:n * D * D - n * D * D / d * d < B:=(Nat.sub_le _ _).trans_lt haB
  have hq1B:n * D * D / d + 1 < B:=by
    have hq:=Nat.div_le_self (n * D * D) d
    nlinarith
  have h1:1 < B:=by nlinarith
  have hsB:=hs.trans_lt h1
  have hN:upperMagnitude s n d D≤ M ^ 3 + 1:=by
    have hq:=Nat.div_le_self (n * D ^ 2) d
    have ha':n * D ^ 2≤ M ^ 3:=by simpa only [pow_two,Nat.mul_assoc] using ha
    unfold upperMagnitude ceilQuotient
    split_ifs <;> omega
  have hrootB:(2 * (upperMagnitude s n d D + 1) + 1) ^ 2 < B:=by
    have hp:=Nat.pow_le_pow_left (by omega:
      2 * (upperMagnitude s n d D + 1) + 1≤ 2 * (M ^ 3 + 2) + 1) 2
    omega
  have hnumB:Nat.sqrt (upperMagnitude s n d D) + 1 < B:=by
    have hr:=Nat.sqrt_le_self (upperMagnitude s n d D)
    nlinarith
  have hroot:=squareRoot_grid_spec B (upperMagnitude s n d D) D hrootB
  have hnorm:=normalizeFraction_output_spec B 0
    (Nat.sqrt (upperMagnitude s n d D) + 1) D (by omega) hnumB hDB hDpos
  have hc:fractionValue 0 (Nat.sqrt (upperMagnitude s n d D) + 1) D =
      sqrtUpper (fractionValue s n d) D:=by
    simp only [fractionValue,if_neg (by decide:¬ (0:ℕ)=1),sqrtUpper,
      upperMagnitude_correct s n d D hdpos]
  have hmod:n * D * D - n * D * D / d * d=n * D * D % d:=by
    simpa only [Nat.mul_comm] using (Nat.mod_def (n * D * D) d).symm
  rintro σ ⟨hσs,hσn,hσd,hσD⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "grid.D"); let c2:Nat:=c0 c1 (Env.vars σ "grid.D"); let c3:Env:=Env.setVar σ "round.a" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "round.a"; let c6:Nat:=c4 "left.d"; let c7:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c5 c6; let c8:Env:=Env.setVar c3 "round.q" c7; let c9:String→ Nat:=Env.vars c8; let c10:Nat:=c9 "round.a"; let c11:Nat:=c9 "round.q"; let c12:Nat:=c9 "left.d"; let c13:Nat:=c0 c11 c12; let c14:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c10 c13; let c15:Env:=Env.setVar c8 "round.r" c14; let c16:Nat:=Env.vars c15 "round.q"; let c17:Env:=Env.setVar c15 "sqrt.n" c16; let c18:String→ Nat:=Env.vars c17; let c19:Nat:=c18 "round.r"; let c20:Prop:= @Eq Nat c19 ((0:Nat)); let c21:Prop:=Not c20; let c22:Nat→ Nat→ Nat:=Nat.add; let c23:Nat→ Nat:=c22 (c0 ((26:Nat)) (Nat.size (upperMagnitude s n d D))); let c24:Nat:=c0 ((36:Nat)) (Nat.size D); let c25:Nat:=c22 (c23 c24) ((128:Nat)); let c26:Env→ Prop:=FractionOutput (sqrtUpper (fractionValue s n d) D); let c27:Env→ Prop:=(fun (x σ':Env) => c26 σ') σ; let c28:Env→ Prop:=fun (σ':Env) => And (Run B upperRootFraction σ σ' c25) (c27 σ'); let c29:Prop:= @Exists Env c28; let c30:Nat:=c18 "left.s"; let c31:Prop:= @Eq Nat c30 ((1:Nat)); let c32:Prop:=Not c31; let c33:Nat→ Env:=Env.setVar c17 "sqrt.n"; let c34:Env:=c33 ((0:Nat)); let c35:Env→ Nat→ Prop:=Run B RamSquareRoot.squareRoot c34; let c36:Nat:=c23 ((12:Nat)); let c37:Env→ Prop:=fun (σ':Env) => And (c35 σ' c36) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars σ' "grid.D") D)); let c38:String→ Nat:=Env.vars c34; let c39:Nat:=c22 c24 ((16:Nat)); let c40:Nat:=c22 (Nat.sqrt (upperMagnitude s n d D)) ((1:Nat)); let c41:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) c40 D); let c42:Nat→ Nat:=c22 ((1:Nat)); let c43:Expr:=Expr.mul (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) (Expr.var "grid.D"); let c44:Nat:=c42 (Expr.size c43); let c45:Nat→ Nat:=c22 c44; let c46:Nat:=c42 (Expr.size (Expr.div (Expr.var "round.a") (Expr.var "left.d"))); let c47:Nat→ Nat:=c22 c46; let c48:Expr:=Expr.sub (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")); let c49:Nat:=c42 (Expr.size c48); let c50:Nat→ Nat:=c22 c49; let c51:Nat:=c42 (Expr.size (Expr.var "round.q")); let c52:Nat→ Nat:=c22 c51; let c53:Cond:=Cond.eq (Expr.var "round.r") (Expr.lit ((0:Nat))); let c54:Nat→ Nat:=c22 (c42 (Cond.size c53)); let c55:Nat:=c54 ((1:Nat)); let c56:Nat→ Nat:=c22 c55; let c57:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c58:Nat→ Nat:=c22 (c42 (Cond.size c57)); let c59:Nat:=c42 (Expr.size (Expr.lit ((0:Nat)))); let c60:Nat:=c58 c59; let c61:Expr:=Expr.add (Expr.var "sqrt.lo") (Expr.lit ((1:Nat))); let c62:Nat:=c42 (Expr.size c61); let c63:Nat:=c42 (Expr.size (Expr.var "grid.D")); let c64:Nat:=c22 c63 c39; let c65:Nat:=c22 c59 c64; let c66:Nat:=c22 c62 c65; let c67:Nat:=c22 c36 c66; let c68:Nat:=c22 c60 c67; let c69:Nat:=c56 c68; let c70:Nat:=c52 c69; let c71:Nat:=c50 c70; let c72:Nat:=c47 c71; let c73:Com:=Com.assign "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")); let c74:Com:=Com.assign "round.r" c48; let c75:Expr:=Expr.add (Expr.var "sqrt.n") (Expr.lit ((1:Nat))); let c76:Com:=Com.assign "sqrt.n" c75; let c77:Com:=Com.ite c53 Com.skip c76; let c78:Com:=Com.assign "sqrt.n" (Expr.lit ((0:Nat))); let c79:Com:=Com.ite c57 c78 Com.skip; let c80:Com:=Com.assign "rat.n" c61; let c81:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c82:Com:=Com.seq c81 (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction); let c83:Com:=Com.seq c80 c82; let c84:Com:=Com.seq RamSquareRoot.squareRoot c83; let c85:Com:=Com.seq c79 c84; let c86:Com:=Com.seq c77 c85; let c87:Com:=Com.seq (Com.assign "sqrt.n" (Expr.var "round.q")) c86; let c88:Com:=Com.seq c74 c87; let c89:Env→ Nat→ Prop:=Run B RamSquareRoot.squareRoot c17; let c90:Env→ Prop:=fun (σ':Env) => And (c89 σ' c36) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars σ' "grid.D") D)); let c91:Nat:=c18 "sqrt.n"; let c92:Nat:=c58 ((1:Nat)); let c93:Nat:=c22 c92 c67; let c94:Nat:=c56 c93; let c95:Nat:=c52 c94; let c96:Nat:=c50 c95; let c97:Nat:=c47 c96; let c98:Nat:=c22 c91 ((1:Nat)); let c99:Env:=c33 c98; let c100:String→ Nat:=Env.vars c99; let c101:Nat:=c100 "left.s"; let c102:Prop:= @Eq Nat c101 ((1:Nat)); let c103:Prop:=Not c102; let c104:Env:=Env.setVar c99 "sqrt.n" ((0:Nat)); let c105:Env→ Nat→ Prop:=Run B RamSquareRoot.squareRoot c104; let c106:Env→ Prop:=fun (σ':Env) => And (c105 σ' c36) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars σ' "grid.D") D)); let c107:String→ Nat:=Env.vars c104; let c108:Nat:=c42 (Expr.size c75); let c109:Nat:=c54 c108; let c110:Nat→ Nat:=c22 c109; let c111:Nat:=c110 c68; let c112:Nat:=c52 c111; let c113:Nat:=c50 c112; let c114:Nat:=c47 c113; let c115:Env→ Nat→ Prop:=Run B RamSquareRoot.squareRoot c99; let c116:Env→ Prop:=fun (σ':Env) => And (c115 σ' c36) (And (@Eq Nat (Env.vars σ' "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars σ' "grid.D") D)); let c117:Nat:=c110 c93; let c118:Nat:=c52 c117; let c119:Nat:=c50 c118; let c120:Nat:=c47 c119; @Or.casesOn c20 c21 (fun (x:Or c20 c21) => c29) (Classical.em c20) (fun (hcase:c20) => @Or.casesOn c31 c32 (fun (x:Or c31 c32) => c29) (Classical.em c31) (fun (hcase_1:c31) => @Exists.casesOn Env c37 (fun (x:@Exists Env c37) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "sqrt.n") (upperMagnitude s n d D)) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamSquareRoot.squareRoot (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars τ "grid.D") D)) c36 hroot c34 ?_) fun (w:Env) (h:And (c35 w c36) (And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D); let c1_1:Nat:=c22 (Env.vars w "sqrt.lo") ((1:Nat)); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:Env:=Env.setVar c2_1 "rat.s" ((0:Nat)); let c4_1:Nat:=Env.vars c3_1 "grid.D"; let c5_1:Env:=Env.setVar c3_1 "rat.d" c4_1; let c6_1:Env→ Nat→ Prop:=Run B normalizeFraction c5_1; let c7_1:Env→ Prop:=fun (σ':Env) => And (c6_1 σ' c39) (c41 σ'); let c8_1:String→ Nat:=Env.vars c5_1; @And.casesOn (c35 w c36) c0_1 (fun (x:And (c35 w c36) c0_1) => c29) h fun (left:c35 w c36) (right:c0_1) => @Exists.casesOn Env c7_1 (fun (x:@Exists Env c7_1) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c40) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c41 σ') c39 hnorm c5_1 ?_) fun (w_1:Env) (h_1:And (c6_1 w_1 c39) (c41 w_1)) => @And.casesOn (c6_1 w_1 c39) (c41 w_1) (fun (x:And (c6_1 w_1 c39) (c41 w_1)) => c29) h_1 fun (left_1:c6_1 w_1 c39) (right_1:c41 w_1) => @Exists.intro Env c28 w_1 (@And.intro (Run B upperRootFraction σ w_1 c25) (c27 w_1) (RunStep.mono B upperRootFraction σ w_1 (c45 c72) c25 (RunStep.seq B (Com.assign "round.a" c43) (Com.seq c73 c88) σ c3 w_1 c44 c72 (RunStep.assign B σ "round.a" c43 c2 (RunStep.eval_mul B σ (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) (Expr.var "grid.D") c1 (Env.vars σ "grid.D") (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3918_0_0_0)) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_1)) ?_) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_2)) ?_)) (RunStep.seq B c73 c88 c3 c8 w_1 c46 c71 (RunStep.assign B c3 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c7 (RunStep.eval_div B c3 (Expr.var "round.a") (Expr.var "left.d") c5 c6 (RunStep.eval_var B c3 "round.a" ?_) (RunStep.eval_var B c3 "left.d" (?nAX_g3918_0_0_3)) ?_)) (RunStep.seq B c74 c87 c8 c15 w_1 c49 c70 (RunStep.assign B c8 "round.r" c48 c14 (RunStep.eval_sub B c8 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c10 c13 (RunStep.eval_var B c8 "round.a" ?_) (RunStep.eval_mul B c8 (Expr.var "round.q") (Expr.var "left.d") c11 c12 (RunStep.eval_var B c8 "round.q" ?_) (RunStep.eval_var B c8 "left.d" (?nAX_g3918_0_0_4)) ?_) ?_)) (RunStep.seq B (Com.assign "sqrt.n" (Expr.var "round.q")) c86 c15 c17 w_1 c51 c69 (RunStep.assign B c15 "sqrt.n" (Expr.var "round.q") c16 (RunStep.eval_var B c15 "round.q" ?_)) (RunStep.seq B c77 c85 c17 c17 w_1 c55 c68 (RunStep.ite_true B c53 Com.skip c76 c17 c17 ((1:Nat)) (RunStep.cond_eq_true B c17 (Expr.var "round.r") (Expr.lit ((0:Nat))) c19 ((0:Nat)) (RunStep.eval_var B c17 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c17 (?nAX_g3918_0_0_5)) hcase) (RunStep.skip B c17)) (RunStep.seq B c79 c84 c17 c34 w_1 c60 c67 (RunStep.ite_true B c57 c78 Com.skip c17 c34 c59 (RunStep.cond_eq_true B c17 (Expr.var "left.s") (Expr.lit ((1:Nat))) c30 ((1:Nat)) (RunStep.eval_var B c17 "left.s" (?nAX_g3918_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c17 h1) hcase_1) (RunStep.assign B c17 "sqrt.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c17 (?nAX_g3918_0_0_7)))) (RunStep.seq B RamSquareRoot.squareRoot c83 c34 w w_1 c36 c66 left (RunStep.seq B c80 c82 w c2_1 w_1 c62 c65 (RunStep.assign B w "rat.n" c61 c1_1 (RunStep.eval_add B w (Expr.var "sqrt.lo") (Expr.lit ((1:Nat))) (Env.vars w "sqrt.lo") ((1:Nat)) (RunStep.eval_var B w "sqrt.lo" (?nAX_g3918_0_0_8)) (RunStep.eval_lit B ((1:Nat)) w h1) (?nAX_g3918_0_0_9))) (RunStep.seq B c81 (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c2_1 c3_1 w_1 c59 c64 (RunStep.assign B c2_1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2_1 (?nAX_g3918_0_0_10))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c3_1 c5_1 w_1 c63 c39 (RunStep.assign B c3_1 "rat.d" (Expr.var "grid.D") c4_1 (RunStep.eval_var B c3_1 "grid.D" (?nAX_g3918_0_0_11))) left_1)))))))))) (?nAX_g3918_0_0_12)) ?_)) fun (hcase_1:c32) => @Exists.casesOn Env c90 (fun (x:@Exists Env c90) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "sqrt.n") (upperMagnitude s n d D)) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamSquareRoot.squareRoot (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars τ "grid.D") D)) c36 hroot c17 ?_) fun (w:Env) (h:And (c89 w c36) (And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D); let c1_1:Nat:=c22 (Env.vars w "sqrt.lo") ((1:Nat)); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:Env:=Env.setVar c2_1 "rat.s" ((0:Nat)); let c4_1:Nat:=Env.vars c3_1 "grid.D"; let c5_1:Env:=Env.setVar c3_1 "rat.d" c4_1; let c6_1:Env→ Nat→ Prop:=Run B normalizeFraction c5_1; let c7_1:Env→ Prop:=fun (σ':Env) => And (c6_1 σ' c39) (c41 σ'); let c8_1:String→ Nat:=Env.vars c5_1; @And.casesOn (c89 w c36) c0_1 (fun (x:And (c89 w c36) c0_1) => c29) h fun (left:c89 w c36) (right:c0_1) => @Exists.casesOn Env c7_1 (fun (x:@Exists Env c7_1) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c40) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c41 σ') c39 hnorm c5_1 ?_) fun (w_1:Env) (h_1:And (c6_1 w_1 c39) (c41 w_1)) => @And.casesOn (c6_1 w_1 c39) (c41 w_1) (fun (x:And (c6_1 w_1 c39) (c41 w_1)) => c29) h_1 fun (left_1:c6_1 w_1 c39) (right_1:c41 w_1) => @Exists.intro Env c28 w_1 (@And.intro (Run B upperRootFraction σ w_1 c25) (c27 w_1) (RunStep.mono B upperRootFraction σ w_1 (c45 c97) c25 (RunStep.seq B (Com.assign "round.a" c43) (Com.seq c73 c88) σ c3 w_1 c44 c97 (RunStep.assign B σ "round.a" c43 c2 (RunStep.eval_mul B σ (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) (Expr.var "grid.D") c1 (Env.vars σ "grid.D") (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3918_0_0_13)) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_14)) ?_) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_15)) ?_)) (RunStep.seq B c73 c88 c3 c8 w_1 c46 c96 (RunStep.assign B c3 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c7 (RunStep.eval_div B c3 (Expr.var "round.a") (Expr.var "left.d") c5 c6 (RunStep.eval_var B c3 "round.a" ?_) (RunStep.eval_var B c3 "left.d" (?nAX_g3918_0_0_16)) ?_)) (RunStep.seq B c74 c87 c8 c15 w_1 c49 c95 (RunStep.assign B c8 "round.r" c48 c14 (RunStep.eval_sub B c8 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c10 c13 (RunStep.eval_var B c8 "round.a" ?_) (RunStep.eval_mul B c8 (Expr.var "round.q") (Expr.var "left.d") c11 c12 (RunStep.eval_var B c8 "round.q" ?_) (RunStep.eval_var B c8 "left.d" (?nAX_g3918_0_0_17)) ?_) ?_)) (RunStep.seq B (Com.assign "sqrt.n" (Expr.var "round.q")) c86 c15 c17 w_1 c51 c94 (RunStep.assign B c15 "sqrt.n" (Expr.var "round.q") c16 (RunStep.eval_var B c15 "round.q" ?_)) (RunStep.seq B c77 c85 c17 c17 w_1 c55 c93 (RunStep.ite_true B c53 Com.skip c76 c17 c17 ((1:Nat)) (RunStep.cond_eq_true B c17 (Expr.var "round.r") (Expr.lit ((0:Nat))) c19 ((0:Nat)) (RunStep.eval_var B c17 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c17 (?nAX_g3918_0_0_18)) hcase) (RunStep.skip B c17)) (RunStep.seq B c79 c84 c17 c17 w_1 c92 c67 (RunStep.ite_false B c57 c78 Com.skip c17 c17 ((1:Nat)) (RunStep.cond_eq_false B c17 (Expr.var "left.s") (Expr.lit ((1:Nat))) c30 ((1:Nat)) (RunStep.eval_var B c17 "left.s" (?nAX_g3918_0_0_19)) (RunStep.eval_lit B ((1:Nat)) c17 h1) hcase_1) (RunStep.skip B c17)) (RunStep.seq B RamSquareRoot.squareRoot c83 c17 w w_1 c36 c66 left (RunStep.seq B c80 c82 w c2_1 w_1 c62 c65 (RunStep.assign B w "rat.n" c61 c1_1 (RunStep.eval_add B w (Expr.var "sqrt.lo") (Expr.lit ((1:Nat))) (Env.vars w "sqrt.lo") ((1:Nat)) (RunStep.eval_var B w "sqrt.lo" (?nAX_g3918_0_0_20)) (RunStep.eval_lit B ((1:Nat)) w h1) (?nAX_g3918_0_0_21))) (RunStep.seq B c81 (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c2_1 c3_1 w_1 c59 c64 (RunStep.assign B c2_1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2_1 (?nAX_g3918_0_0_22))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c3_1 c5_1 w_1 c63 c39 (RunStep.assign B c3_1 "rat.d" (Expr.var "grid.D") c4_1 (RunStep.eval_var B c3_1 "grid.D" (?nAX_g3918_0_0_23))) left_1)))))))))) (?nAX_g3918_0_0_24)) ?_)) fun (hcase:c21) => @Or.casesOn c102 c103 (fun (x:Or c102 c103) => c29) (Classical.em c102) (fun (hcase_1:c102) => @Exists.casesOn Env c106 (fun (x:@Exists Env c106) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "sqrt.n") (upperMagnitude s n d D)) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamSquareRoot.squareRoot (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars τ "grid.D") D)) c36 hroot c104 ?_) fun (w:Env) (h:And (c105 w c36) (And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D); let c1_1:Nat:=c22 (Env.vars w "sqrt.lo") ((1:Nat)); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:Env:=Env.setVar c2_1 "rat.s" ((0:Nat)); let c4_1:Nat:=Env.vars c3_1 "grid.D"; let c5_1:Env:=Env.setVar c3_1 "rat.d" c4_1; let c6_1:Env→ Nat→ Prop:=Run B normalizeFraction c5_1; let c7_1:Env→ Prop:=fun (σ':Env) => And (c6_1 σ' c39) (c41 σ'); let c8_1:String→ Nat:=Env.vars c5_1; @And.casesOn (c105 w c36) c0_1 (fun (x:And (c105 w c36) c0_1) => c29) h fun (left:c105 w c36) (right:c0_1) => @Exists.casesOn Env c7_1 (fun (x:@Exists Env c7_1) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c40) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c41 σ') c39 hnorm c5_1 ?_) fun (w_1:Env) (h_1:And (c6_1 w_1 c39) (c41 w_1)) => @And.casesOn (c6_1 w_1 c39) (c41 w_1) (fun (x:And (c6_1 w_1 c39) (c41 w_1)) => c29) h_1 fun (left_1:c6_1 w_1 c39) (right_1:c41 w_1) => @Exists.intro Env c28 w_1 (@And.intro (Run B upperRootFraction σ w_1 c25) (c27 w_1) (RunStep.mono B upperRootFraction σ w_1 (c45 c114) c25 (RunStep.seq B (Com.assign "round.a" c43) (Com.seq c73 c88) σ c3 w_1 c44 c114 (RunStep.assign B σ "round.a" c43 c2 (RunStep.eval_mul B σ (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) (Expr.var "grid.D") c1 (Env.vars σ "grid.D") (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3918_0_0_25)) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_26)) ?_) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_27)) ?_)) (RunStep.seq B c73 c88 c3 c8 w_1 c46 c113 (RunStep.assign B c3 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c7 (RunStep.eval_div B c3 (Expr.var "round.a") (Expr.var "left.d") c5 c6 (RunStep.eval_var B c3 "round.a" ?_) (RunStep.eval_var B c3 "left.d" (?nAX_g3918_0_0_28)) ?_)) (RunStep.seq B c74 c87 c8 c15 w_1 c49 c112 (RunStep.assign B c8 "round.r" c48 c14 (RunStep.eval_sub B c8 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c10 c13 (RunStep.eval_var B c8 "round.a" ?_) (RunStep.eval_mul B c8 (Expr.var "round.q") (Expr.var "left.d") c11 c12 (RunStep.eval_var B c8 "round.q" ?_) (RunStep.eval_var B c8 "left.d" (?nAX_g3918_0_0_29)) ?_) ?_)) (RunStep.seq B (Com.assign "sqrt.n" (Expr.var "round.q")) c86 c15 c17 w_1 c51 c111 (RunStep.assign B c15 "sqrt.n" (Expr.var "round.q") c16 (RunStep.eval_var B c15 "round.q" ?_)) (RunStep.seq B c77 c85 c17 c99 w_1 c109 c68 (RunStep.ite_false B c53 Com.skip c76 c17 c99 c108 (RunStep.cond_eq_false B c17 (Expr.var "round.r") (Expr.lit ((0:Nat))) c19 ((0:Nat)) (RunStep.eval_var B c17 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c17 (?nAX_g3918_0_0_30)) hcase) (RunStep.assign B c17 "sqrt.n" c75 c98 (RunStep.eval_add B c17 (Expr.var "sqrt.n") (Expr.lit ((1:Nat))) c91 ((1:Nat)) (RunStep.eval_var B c17 "sqrt.n" ?_) (RunStep.eval_lit B ((1:Nat)) c17 h1) ?_))) (RunStep.seq B c79 c84 c99 c104 w_1 c60 c67 (RunStep.ite_true B c57 c78 Com.skip c99 c104 c59 (RunStep.cond_eq_true B c99 (Expr.var "left.s") (Expr.lit ((1:Nat))) c101 ((1:Nat)) (RunStep.eval_var B c99 "left.s" (?nAX_g3918_0_0_31)) (RunStep.eval_lit B ((1:Nat)) c99 h1) hcase_1) (RunStep.assign B c99 "sqrt.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c99 (?nAX_g3918_0_0_32)))) (RunStep.seq B RamSquareRoot.squareRoot c83 c104 w w_1 c36 c66 left (RunStep.seq B c80 c82 w c2_1 w_1 c62 c65 (RunStep.assign B w "rat.n" c61 c1_1 (RunStep.eval_add B w (Expr.var "sqrt.lo") (Expr.lit ((1:Nat))) (Env.vars w "sqrt.lo") ((1:Nat)) (RunStep.eval_var B w "sqrt.lo" (?nAX_g3918_0_0_33)) (RunStep.eval_lit B ((1:Nat)) w h1) (?nAX_g3918_0_0_34))) (RunStep.seq B c81 (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c2_1 c3_1 w_1 c59 c64 (RunStep.assign B c2_1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2_1 (?nAX_g3918_0_0_35))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c3_1 c5_1 w_1 c63 c39 (RunStep.assign B c3_1 "rat.d" (Expr.var "grid.D") c4_1 (RunStep.eval_var B c3_1 "grid.D" (?nAX_g3918_0_0_36))) left_1)))))))))) (?nAX_g3918_0_0_37)) ?_)) fun (hcase_1:c103) => @Exists.casesOn Env c116 (fun (x:@Exists Env c116) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "sqrt.n") (upperMagnitude s n d D)) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamSquareRoot.squareRoot (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars τ "grid.D") D)) c36 hroot c99 ?_) fun (w:Env) (h:And (c115 w c36) (And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "sqrt.lo") (Nat.sqrt (upperMagnitude s n d D))) (@Eq Nat (Env.vars w "grid.D") D); let c1_1:Nat:=c22 (Env.vars w "sqrt.lo") ((1:Nat)); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:Env:=Env.setVar c2_1 "rat.s" ((0:Nat)); let c4_1:Nat:=Env.vars c3_1 "grid.D"; let c5_1:Env:=Env.setVar c3_1 "rat.d" c4_1; let c6_1:Env→ Nat→ Prop:=Run B normalizeFraction c5_1; let c7_1:Env→ Prop:=fun (σ':Env) => And (c6_1 σ' c39) (c41 σ'); let c8_1:String→ Nat:=Env.vars c5_1; @And.casesOn (c115 w c36) c0_1 (fun (x:And (c115 w c36) c0_1) => c29) h fun (left:c115 w c36) (right:c0_1) => @Exists.casesOn Env c7_1 (fun (x:@Exists Env c7_1) => c29) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c40) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c41 σ') c39 hnorm c5_1 ?_) fun (w_1:Env) (h_1:And (c6_1 w_1 c39) (c41 w_1)) => @And.casesOn (c6_1 w_1 c39) (c41 w_1) (fun (x:And (c6_1 w_1 c39) (c41 w_1)) => c29) h_1 fun (left_1:c6_1 w_1 c39) (right_1:c41 w_1) => @Exists.intro Env c28 w_1 (@And.intro (Run B upperRootFraction σ w_1 c25) (c27 w_1) (RunStep.mono B upperRootFraction σ w_1 (c45 c120) c25 (RunStep.seq B (Com.assign "round.a" c43) (Com.seq c73 c88) σ c3 w_1 c44 c120 (RunStep.assign B σ "round.a" c43 c2 (RunStep.eval_mul B σ (Expr.mul (Expr.var "left.n") (Expr.var "grid.D")) (Expr.var "grid.D") c1 (Env.vars σ "grid.D") (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "grid.D") (Env.vars σ "left.n") (Env.vars σ "grid.D") (RunStep.eval_var B σ "left.n" (?nAX_g3918_0_0_38)) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_39)) ?_) (RunStep.eval_var B σ "grid.D" (?nAX_g3918_0_0_40)) ?_)) (RunStep.seq B c73 c88 c3 c8 w_1 c46 c119 (RunStep.assign B c3 "round.q" (Expr.div (Expr.var "round.a") (Expr.var "left.d")) c7 (RunStep.eval_div B c3 (Expr.var "round.a") (Expr.var "left.d") c5 c6 (RunStep.eval_var B c3 "round.a" ?_) (RunStep.eval_var B c3 "left.d" (?nAX_g3918_0_0_41)) ?_)) (RunStep.seq B c74 c87 c8 c15 w_1 c49 c118 (RunStep.assign B c8 "round.r" c48 c14 (RunStep.eval_sub B c8 (Expr.var "round.a") (Expr.mul (Expr.var "round.q") (Expr.var "left.d")) c10 c13 (RunStep.eval_var B c8 "round.a" ?_) (RunStep.eval_mul B c8 (Expr.var "round.q") (Expr.var "left.d") c11 c12 (RunStep.eval_var B c8 "round.q" ?_) (RunStep.eval_var B c8 "left.d" (?nAX_g3918_0_0_42)) ?_) ?_)) (RunStep.seq B (Com.assign "sqrt.n" (Expr.var "round.q")) c86 c15 c17 w_1 c51 c117 (RunStep.assign B c15 "sqrt.n" (Expr.var "round.q") c16 (RunStep.eval_var B c15 "round.q" ?_)) (RunStep.seq B c77 c85 c17 c99 w_1 c109 c93 (RunStep.ite_false B c53 Com.skip c76 c17 c99 c108 (RunStep.cond_eq_false B c17 (Expr.var "round.r") (Expr.lit ((0:Nat))) c19 ((0:Nat)) (RunStep.eval_var B c17 "round.r" ?_) (RunStep.eval_lit B ((0:Nat)) c17 (?nAX_g3918_0_0_43)) hcase) (RunStep.assign B c17 "sqrt.n" c75 c98 (RunStep.eval_add B c17 (Expr.var "sqrt.n") (Expr.lit ((1:Nat))) c91 ((1:Nat)) (RunStep.eval_var B c17 "sqrt.n" ?_) (RunStep.eval_lit B ((1:Nat)) c17 h1) ?_))) (RunStep.seq B c79 c84 c99 c99 w_1 c92 c67 (RunStep.ite_false B c57 c78 Com.skip c99 c99 ((1:Nat)) (RunStep.cond_eq_false B c99 (Expr.var "left.s") (Expr.lit ((1:Nat))) c101 ((1:Nat)) (RunStep.eval_var B c99 "left.s" (?nAX_g3918_0_0_44)) (RunStep.eval_lit B ((1:Nat)) c99 h1) hcase_1) (RunStep.skip B c99)) (RunStep.seq B RamSquareRoot.squareRoot c83 c99 w w_1 c36 c66 left (RunStep.seq B c80 c82 w c2_1 w_1 c62 c65 (RunStep.assign B w "rat.n" c61 c1_1 (RunStep.eval_add B w (Expr.var "sqrt.lo") (Expr.lit ((1:Nat))) (Env.vars w "sqrt.lo") ((1:Nat)) (RunStep.eval_var B w "sqrt.lo" (?nAX_g3918_0_0_45)) (RunStep.eval_lit B ((1:Nat)) w h1) (?nAX_g3918_0_0_46))) (RunStep.seq B c81 (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c2_1 c3_1 w_1 c59 c64 (RunStep.assign B c2_1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2_1 (?nAX_g3918_0_0_47))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c3_1 c5_1 w_1 c63 c39 (RunStep.assign B c3_1 "rat.d" (Expr.var "grid.D") c4_1 (RunStep.eval_var B c3_1 "grid.D" (?nAX_g3918_0_0_48))) left_1)))))))))) (?nAX_g3918_0_0_49)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3918_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3918_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals simp_all [upperMagnitude,ceilQuotient,pow_two,Nat.mul_assoc]

end Lax109476Proofs.RamRounding

end

theorem solution:∀ (B M s n d D:Nat),
  Nat.lt
      (Nat.add
        (Nat.add
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (Nat.add
              (Nat.mul
                ((2:Nat))
                (Nat.add
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                    ((3:Nat)))
                  ((2:Nat))))
              ((1:Nat)))
            ((2:Nat)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((3:Nat))))
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
                  Lax109476Proofs.RamRounding.upperRootFraction
                  (fun (x σ':Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamRational.FractionOutput
                      (Lax109476Proofs.RationalRounding.sqrtUpper (Lax109476Proofs.RamRational.fractionValue s n d) D)
                      σ')
                  (Nat.add
                    (Nat.add
                      (Nat.mul
                        ((26:Nat))
                        (Lax109476Proofs.RamRounding.upperMagnitude s n d D).size)
                      (Nat.mul
                        ((36:Nat)) D.size))
                    ((128:Nat))):= @Lax109476Proofs.RamRounding.upperRootFraction_spec
