-- Prove2me | solution 1 for Lax263307Proofs.NativeCollectionContext.light_iteration_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:27:39.506202+00:00
-- url     : https://prove2.me/submissions/5e9649c4-718b-4581-89e5-7ea89f826f0c

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native

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

namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.addFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    LE.le s₁ ((1:Nat))→
      LE.le s₂ ((1:Nat))→
        LE.le n₁ M→
          LE.le d₁ M→
            LE.le n₂ M→
              LE.le d₂ M→
                LT.lt ((0:Nat)) d₁→
                  LT.lt ((0:Nat)) d₂→
                    Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamRational.fractionInputs s₁ n₁ d₁ s₂ n₂ d₂)
                      Lax109476Proofs.RamRational.addFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (HAdd.hAdd
                        (HMul.hMul
                          ((36:Nat))
                          (HMul.hMul d₁ d₂).size)
                        ((96:Nat))):= @Lax109476Proofs.RamRational.addFraction_spec_native

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

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

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

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

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
      (36 * (d₁ * d₂).size + 96)  :=by
  exact Lax109476Proofs.RamRational.addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

end Lax455465Proofs.RamRational

end

section

namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational

theorem save_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".s"≠"rat.n" ∧ name++".s"≠"rat.d" ∧ name++".n"≠"rat.d"):
    Spec B (FractionOutput q) (save name) (fun _ τ => Stored name q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars "rat.s"< B:=hs.trans_lt h1
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".s"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.s"); let c4:String:=c1 ".n"; let c5:Nat:=Env.vars c3 "rat.n"; let c6:Env:=Env.setVar c3 c4 c5; let c7:String:=c1 ".d"; let c8:Nat:=Env.vars c6 "rat.d"; let c9:Env:=Env.setVar c6 c7 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "rat.s")); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c4 (Expr.var "rat.n"); let c17:Com:=Com.assign c7 (Expr.var "rat.d"); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((6:Nat))) (c0 σ')) c9 (@And.intro (Run B (save name) σ c9 ((6:Nat))) (c0 c9) (RunStep.mono B (save name) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.s")) (Com.seq c16 c17) σ c3 c9 c12 c15 (RunStep.assign B σ c2 (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B c16 c17 c3 c6 c9 c13 c14 (RunStep.assign B c3 c4 (Expr.var "rat.n") c5 (RunStep.eval_var B c3 "rat.n" ?_)) (RunStep.assign B c6 c7 (Expr.var "rat.d") c8 (RunStep.eval_var B c6 "rat.d" ?_)))) (?nAX_g5443_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5443_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem load_spec (B:ℕ) (name:String) (q:ℚ) (h1:1< B)
    (hn:q.num.natAbs< B) (hd:q.den< B)
    (hfresh:name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB:σ.vars (name++".s")< B:=hs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "rat.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "rat.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "rat.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "rat.n" c14; let c20:Com:=Com.assign "rat.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c9 (@And.intro (Run B (load name) σ c9 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c9) (RunStep.mono B (load name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "rat.s" c12 c2 (RunStep.eval_var B σ c1 hsB)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "rat.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "rat.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g5444_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

def Operands (a b:ℚ) (σ:Env):Prop:=Stored "left" a σ∧ Stored "right" b σ

theorem add_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (Operands a b) addFraction (fun _ τ => FractionOutput (a+b) τ)
      (36*(a.den*b.den).size+96):=by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩:=addFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl:fractionValue (σ.vars "left.s") a.num.natAbs a.den=a:=by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr:fractionValue (σ.vars "right.s") b.num.natAbs b.den=b:=by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

end Lax263307Proofs.NativeSignedArithmetic

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

theorem keep_scalar {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (h:Spec B P c Q K) (x:String) (v:ℕ) (hx:x∉ c.wvars):
    Spec B (fun σ => P σ∧ σ.vars x=v) c (fun σ τ => Q σ τ∧ τ.vars x=v) K:=by
  rintro σ ⟨hp,hv⟩
  obtain ⟨τ,hr,hq⟩:=h σ hp
  exact ⟨τ,hr,hq, (hr.frame_var x hx).trans hv⟩

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

namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

theorem canonical_sign (q:ℚ) (σ:Env) (h:FractionOutput q σ):
    (if σ.vars "rat.n"=0 then 0 else σ.vars "rat.s")=if q.num < 0 then 1 else 0:=by
  by_cases hn:σ.vars "rat.n"=0
  · have hnum:q.num=0:=by
      have he:q.num.natAbs=0:=h.2.1.symm.trans hn
      exact Int.natAbs_eq_zero.mp he
    simp [hn,hnum]
  · have hs:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by have:=h.2.2.2; omega
    rcases hs with hs | hs
    · have hnonneg:0≤ q:=by
        rw [← h.1]
        simp only [fractionValue,hs,show ¬(0:ℕ)=1 by decide,if_false]
        positivity
      have hnum:=Rat.num_nonneg.mpr hnonneg
      simp [hn,hs,not_lt.mpr hnum]
    · have hnpos:(0:ℚ) < σ.vars "rat.n" :=by exact_mod_cast (show 0 < σ.vars "rat.n" by omega)
      have hdpos:(0:ℚ) < σ.vars "rat.d" :=by
        rw [h.2.2.1]
        exact_mod_cast q.den_pos
      have hneg:q < 0:=by
        rw [← h.1]
        simp only [fractionValue,hs,if_true]
        exact div_neg_of_neg_of_pos (by linarith) hdpos
      have hnum:q.num < 0:=by
        by_contra hnum
        have hq:=Rat.num_nonneg.mp (show 0≤ q.num by omega)
        linarith
      simp [hn,hs,hnum]

theorem sign_spec (B:ℕ) (q:ℚ) (h1:1 < B) (hn:q.num.natAbs < B):
    Spec B (FractionOutput q) sign
      (fun _ τ => τ.vars "emit.s"=if q.num < 0 then 1 else 0) 6:=by
  intro σ h
  have hvalue:=h.2.1
  have hsign:=h.2.2.2
  have hcanonical:=canonical_sign q σ h
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LT.lt Int Int.instLTInt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Int.decLt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "emit.s") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B sign σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "emit.s" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "emit.s" (Expr.lit ((0:Nat))); let c12:Nat:=c7 (Expr.size (Expr.var "rat.s")); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B sign σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B sign σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_1)) hcase) (RunStep.assign B σ "emit.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_2)))) (?nAX_g5889_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (@And.intro (Run B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) ((6:Nat))) (c3 (Env.setVar σ "emit.s" (Env.vars σ "rat.s"))) (RunStep.mono B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (c9 c12) ((6:Nat)) (RunStep.ite_false B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) c12 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_5)) hcase) (RunStep.assign B σ "emit.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5889_0_0_6)))) (?nAX_g5889_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5889_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem emit_spec (B:ℕ) (q:ℚ) (words:List ℕ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hlen:words.length + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ Prefix words "lp.word" σ∧
      σ.vars "lp.position"=words.length∧ words.length + 2 < (σ.arrs "lp.word").length) emit
      (fun _ τ => Prefix (words ++ Lax109476.RationalEncoding.encodeRational q) "lp.word" τ∧
        τ.vars "lp.position"=words.length + 3) 27:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  let tag:=if q.num < 0 then 1 else 0
  have htag:tag < B:=by dsimp only [tag]; split_ifs <;> omega
  obtain ⟨ν,hsign,htagν⟩:=sign_spec B q h1 hn σ hf
  have hnumν:=(hsign.frame_var "rat.n" (by simp [sign,Com.wvars])).trans hf.2.1
  have hdenν:=(hsign.frame_var "rat.d" (by simp [sign,Com.wvars])).trans hf.2.2.1
  have hposν:=(hsign.frame_var "lp.position" (by simp [sign,Com.wvars])).trans hpos
  have hpν:Prefix words "lp.word" ν:=by
    simpa only [Prefix,hsign.frame_arr "lp.word" (by simp [sign,Com.warrs])] using hp
  have hroomν:words.length + 2 < (ν.arrs "lp.word").length:=by
    rwa [RamFrames.run_array_length hsign "lp.word"]
  have hnum:=RamFrames.keep_scalar (RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" words tag (.var "emit.s") h1 (by omega))
    "rat.n" q.num.natAbs (by simp [RamWordBuffer.append,Com.wvars]))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨μ,hfirst,hfirstPost⟩:=hnum ν ⟨⟨⟨hpν,hposν,by omega,
    by rw [evalB_var_iff]; exact ⟨htagν.symm,htagν ▸ htag⟩⟩,hnumν⟩,hdenν⟩
  have hroomμ:(words ++ [tag]).length + 1 < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hfirst "lp.word",List.length_append,List.length_singleton]
    exact hroomν
  have hden:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" (words ++ [tag]) q.num.natAbs (.var "rat.n") h1
      (by simp only [List.length_append,List.length_singleton]; omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨ρ,hsecond,hsecondPost⟩:=hden μ ⟨⟨hfirstPost.1.1.1,
    by simpa only [List.length_append,List.length_singleton] using hfirstPost.1.1.2,
    by omega,by rw [evalB_var_iff]; exact ⟨hfirstPost.1.2.symm,hfirstPost.1.2 ▸ hn⟩⟩,hfirstPost.2⟩
  have hroomρ:((words ++ [tag]) ++ [q.num.natAbs]).length < (ρ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hsecond "lp.word",List.length_append,List.length_singleton]
    exact hroomμ
  obtain ⟨τ,hthird,hthirdPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position"
    ((words ++ [tag]) ++ [q.num.natAbs]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ρ
    ⟨hsecondPost.1.1,by simpa only [List.length_append,List.length_singleton] using hsecondPost.1.2,
      hroomρ,by rw [evalB_var_iff]; exact ⟨hsecondPost.2.symm,hsecondPost.2 ▸ hd⟩⟩
  refine ⟨τ, (hsign.seq (hfirst.seq (hsecond.seq hthird))).mono (by simp [Expr.size]), ?_⟩
  simpa only [Lax109476.RationalEncoding.encodeRational,tag,List.append_assoc,
    List.cons_append,List.nil_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc]
    using hthirdPost

end Lax455465Proofs.RamFractionEncoding

end

section

namespace Lax455465Proofs.RamVectorEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding

def encode (qs:List ℚ):List ℕ:=qs.flatMap encodeRational

@[simp] theorem length_encode (qs:List ℚ):(encode qs).length=3*qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ) (words:List ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ encode (qs.take (σ.vars index))) "lp.word" σ∧
    σ.vars "lp.position"=words.length+3*σ.vars index∧
    words.length+3*qs.length < (σ.arrs "lp.word").length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+3*qs.length+3 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num.natAbs < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput qs[i] τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:"lp.position" ∉ body.wvars)
    (hbodyArray:"lp.word" ∉ body.warrs)
    (hemitIndex:index∉ RamFractionEncoding.emit.wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B RamFractionEncoding.emit σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ "lp.position"):
    Spec B (fun σ => R σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*qs.length < (σ.arrs "lp.word").length) (command index limit body)
      (fun _ τ => R τ∧ Prefix (words ++ encode qs) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*qs.length) ((K+35)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs words τ∧ τ.vars index=σ.vars index+1)
      (K+31):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ encode (qs.take i)).length=words.length+3*i:=by
      simp only [List.length_append,length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars "lp.position"=words.length+3*i:=
      (hproduce.frame_var "lp.position" hbodyPosition).trans hpos
    have hpν:Prefix (words ++ encode (qs.take i)) "lp.word" ν:=by
      simpa only [Prefix,hproduce.frame_arr "lp.word" hbodyArray] using hp
    have hroomν:words.length+3*qs.length < (ν.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hproduce "lp.word"]
    obtain ⟨μ,hemit,hemitted⟩:=RamFractionEncoding.emit_spec B qs[i] (words ++ encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+3*qs.length < (μ.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hemit "lp.word"]
    have hpμ:Prefix (words ++ encode (qs.take (i+1))) "lp.word" μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars "lp.position"=words.length+3*(i+1):=by rw [hpLen] at hemitted; omega
    have hnext:i+1 < B:=by omega
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) hnext)
    refine ⟨μ.setVar index (i+1),hproduce.seq (hemit.seq hinc),?_,?_⟩
    · refine ⟨hset μ (i+1) hRμ,by simp; omega,?_,?_,?_⟩
      · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hpμ
      · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true] using hposμ
      · simpa only [arrs_setVar] using hroomμ
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words) qs.length (K+31)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def sign (q:ℚ):ℕ:=if q.num < 0 then 1 else 0

theorem value_eq (q:ℚ):fractionValue (sign q) q.num.natAbs q.den=q:=by
  have hnum:(if q.num < 0 then -((q.num.natAbs:ℕ):ℚ) else ((q.num.natAbs:ℕ):ℚ))=(q.num:ℚ):=by
    generalize q.num=z
    cases z <;> simp
  by_cases h:q.num < 0
  · simp only [if_pos h] at hnum
    simpa only [fractionValue,sign,if_pos h,if_true,hnum] using q.num_div_den
  · simp only [if_neg h] at hnum
    simpa only [fractionValue,sign,if_neg h,show ¬(0:ℕ)=1 by decide,if_false,hnum] using q.num_div_den

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

theorem command_spec (B:ℕ) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front ++ (encodeRational q ++ tail)) "vm.output" σ∧
      σ.vars "cert.cursor"=front.length) command
      (fun _ τ => FractionOutput q τ∧ τ.vars "cert.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front ++ (encodeRational q ++ tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs "vm.output").length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "cert.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ "vm.output") (Env.vars σ "cert.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "cert.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 "vm.output") c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "cert.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 "vm.output") c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "cert.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "cert.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get "vm.output" (Expr.var "cert.cursor"))); let c18:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get "vm.output" c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get "vm.output" c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "cert.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B command σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B command σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor")) c3 (RunStep.eval_get B σ "vm.output" (Expr.var "cert.cursor") (Env.vars σ "cert.cursor") (RunStep.eval_var B σ "cert.cursor" (?nAX_g6135_0_0_0)) (?nAX_g6135_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 "vm.output" c18 c6 (RunStep.eval_add B c4 (Expr.var "cert.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "cert.cursor" (?nAX_g6135_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g6135_0_0_3)) (?nAX_g6135_0_0_4)) (?nAX_g6135_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 "vm.output" c21 c10 (RunStep.eval_add B c8 (Expr.var "cert.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "cert.cursor" (?nAX_g6135_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g6135_0_0_7)) (?nAX_g6135_0_0_8)) (?nAX_g6135_0_0_9) ?_)) (RunStep.assign B c12 "cert.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "cert.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "cert.cursor" (?nAX_g6135_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g6135_0_0_11)))))) (?nAX_g6135_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6135_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.NativeRationalBounds

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem add (M:ℕ) (a b:ℚ) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^2) (a+b):=by
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn:sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*M^2:=by
    have hleft:=Nat.mul_le_mul ha.1 hb.2
    have hright:=Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd:a.den*b.den≤2*M^2:=by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd:=fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

end Lax263307Proofs.NativeRationalBounds

end

section

namespace Lax263307Proofs.NativeSumHeight

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem weaken {A B:ℕ} {q:ℚ} (h:A≤ B) (hq:Bounded A q):Bounded B q:=
  ⟨hq.1.trans h,hq.2.trans h⟩

theorem add (A C:ℕ) (a b:ℚ) (ha:Bounded A a) (hb:Bounded C b):
    Bounded (2*A*C) (a+b):=by
  have hs (q:ℚ):sign q≤1:=by unfold sign; split_ifs <;> omega
  have he:=fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn:sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*A*C:=by
    have hleft:=Nat.mul_le_mul ha.1 hb.2
    have hright:=Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd:a.den*b.den≤2*A*C:=by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd:=fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

theorem sum (M:ℕ) (xs:List ℚ) (hx:∀ x∈xs,Bounded M x):
    Bounded ((2*M)^xs.length) xs.sum:=by
  induction xs with
  | nil => simp [Bounded]
  | cons x xs ih =>
    have hh:=add M ((2*M)^xs.length) x xs.sum (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))
    simpa only [List.sum_cons,List.length_cons,pow_succ,Nat.mul_comm,Nat.mul_assoc] using hh

theorem sum_bits (h:ℕ) (xs:List ℚ) (hx:∀ x∈xs,Bounded (2^h) x):
    Bounded (2^((h+1)*xs.length)) xs.sum:=by
  have hh:(2*(2^h))^xs.length=2^((h+1)*xs.length):=by
    rw [pow_mul,pow_succ]
    congr 1
    exact Nat.mul_comm _ _
  simpa only [hh] using sum (2^h) xs hx

theorem uniform_entry (M:ℕ) (xs:List ℚ) (hM:1≤ M) (hx:∀ x∈xs,Bounded M x)
    (x:ℚ) (hmem:x∈xs):Bounded ((2*M)^(xs.length+1)) x:=by
  apply weaken _ (hx x hmem)
  calc
    M≤ 2*M:=by omega
    _=(2*M)^1:=(pow_one _).symm
    _≤ (2*M)^(xs.length+1):=Nat.pow_le_pow_right (by omega) (by omega)

theorem uniform_partial (M:ℕ) (xs:List ℚ) (hM:1≤ M) (hx:∀ x∈xs,Bounded M x)
    (i:ℕ):Bounded ((2*M)^(xs.length+1)) (xs.take i).sum:=by
  apply weaken _ (sum M (xs.take i) (fun x h => hx x (List.mem_of_mem_take h)))
  apply Nat.pow_le_pow_right (by omega)
  simp only [List.length_take]
  omega

end Lax263307Proofs.NativeSumHeight

end

section

namespace Lax263307Proofs.NativeSignedAccumulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational NativeSignedArithmetic

theorem command_spec (B M:ℕ) (a b:ℚ) (hB:2*M^2+3< B)
    (ha:Bounded M a) (hb:Bounded M b):
    Spec B (fun σ => Stored "sum.value" a σ∧ FractionOutput b σ) command
      (fun _ τ => Stored "sum.value" (a+b) τ∧ FractionOutput (a+b) τ)
      (36*(M^2).size+120):=by
  have h1:1< B:=by nlinarith
  have hM:M< B:=by nlinarith
  rintro σ ⟨hs,hbσ⟩
  obtain ⟨ν,r1,p1⟩:=save_spec B "right" b h1
    (hb.1.trans_lt hM) (hb.2.trans_lt hM) (by decide) σ hbσ
  have hsν:Stored "sum.value" a ν:=by
    simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
      r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hs
  obtain ⟨μ,r2,p2⟩:=load_spec B "sum.value" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) ν hsν
  obtain ⟨ξ,r3,p3⟩:=save_spec B "left" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) μ p2
  have hbξ:Stored "right" b ξ:=by
    simpa only [Stored,String.reduceAppend,(r2.seq r3).frame_var "right.s" (by decide),
      (r2.seq r3).frame_var "right.n" (by decide),(r2.seq r3).frame_var "right.d" (by decide)] using p1
  obtain ⟨υ,r4,p4⟩:=add_spec B M a b hB ha hb ξ ⟨p3,hbξ⟩
  have hab:=NativeRationalBounds.add M a b ha hb
  obtain ⟨τ,r5,p5⟩:=save_spec B "sum.value" (a+b) h1
    (hab.1.trans_lt (by omega)) (hab.2.trans_lt (by omega)) (by decide) υ p4
  have hden:(a.den*b.den).size≤(M^2).size:=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul ha.2 hb.2])
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono (by omega),p5,?_⟩
  simpa only [FractionOutput,r5.frame_var "rat.s" (by decide),
    r5.frame_var "rat.n" (by decide),r5.frame_var "rat.d" (by decide)] using p4

end Lax263307Proofs.NativeSignedAccumulate

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

namespace Lax263307Proofs.NativeRationalTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def words (xs:List ℚ):List ℕ:=xs.flatMap encodeRational

theorem words_length (xs:List ℚ):(words xs).length=3*xs.length:=by
  induction xs with
  | nil => simp [words]
  | cons x xs ih => simp only [words,List.flatMap_cons,List.length_append,encodeRational,List.length_cons,List.length_nil] at ih ⊢; omega

end Lax263307Proofs.NativeRationalTabulate

end

section

namespace Lax263307Proofs.NativeRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax455465Proofs.RamLpRationalRead

theorem command_spec (B:ℕ) (array:String) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front++(encodeRational q++tail)) array σ∧ σ.vars "read.cursor"=front.length)
      (command array) (fun _ τ => FractionOutput q τ∧ τ.vars "read.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front++(encodeRational q++tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs array).length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "read.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ array) (Env.vars σ "read.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "read.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 array) c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "read.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 array) c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "read.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "read.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get array (Expr.var "read.cursor"))); let c18:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get array c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "read.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "read.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B (command array) σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B (command array) σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B (command array) σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get array (Expr.var "read.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get array (Expr.var "read.cursor")) c3 (RunStep.eval_get B σ array (Expr.var "read.cursor") (Env.vars σ "read.cursor") (RunStep.eval_var B σ "read.cursor" (?nAX_g8234_0_0_0)) (?nAX_g8234_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 array c18 c6 (RunStep.eval_add B c4 (Expr.var "read.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "read.cursor" (?nAX_g8234_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g8234_0_0_3)) (?nAX_g8234_0_0_4)) (?nAX_g8234_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 array c21 c10 (RunStep.eval_add B c8 (Expr.var "read.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "read.cursor" (?nAX_g8234_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g8234_0_0_7)) (?nAX_g8234_0_0_8)) (?nAX_g8234_0_0_9) ?_)) (RunStep.assign B c12 "read.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "read.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "read.cursor" (?nAX_g8234_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g8234_0_0_11)))))) (?nAX_g8234_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8234_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8234_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

theorem vector_entry_spec (B:ℕ) (array:String) (front tail:List ℕ) (qs:List ℚ)
    (i:ℕ) (hi:i < qs.length) (h3:3 < B) (hlen:front.length+3*i+3 < B)
    (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Prefix (front++(NativeRationalTabulate.words qs++tail)) array σ∧
      σ.vars "read.cursor"=front.length+3*i) (command array)
      (fun _ τ => FractionOutput qs[i] τ∧ τ.vars "read.cursor"=front.length+3*i+3) 17:=by
  have he:qs=qs.take i++qs[i]::qs.drop (i+1):=by
    rw [←List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hlen':(front++NativeRationalTabulate.words (qs.take i)).length=front.length+3*i:=by
    rw [List.length_append,NativeRationalTabulate.words_length,List.length_take,Nat.min_eq_left hi.le]
  have hew:front++(NativeRationalTabulate.words qs++tail)=
      (front++NativeRationalTabulate.words (qs.take i))++
        (encodeRational qs[i]++(NativeRationalTabulate.words (qs.drop (i+1))++tail)):=by
    conv_lhs => rw [he]
    simp only [NativeRationalTabulate.words,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  have hh:=command_spec B array qs[i] (front++NativeRationalTabulate.words (qs.take i))
    (NativeRationalTabulate.words (qs.drop (i+1))++tail) h3 (by rwa [hlen']) hn hd
  simpa only [hlen',←hew] using hh

end Lax263307Proofs.NativeRationalRead

end

section

namespace Lax263307Proofs.NativeSignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

def partialSum (xs:List ℚ) (i:ℕ):ℚ:=(xs.take i).sum

theorem partial_step (xs:List ℚ) (i:ℕ) (hi:i< xs.length):
    partialSum xs (i+1)=partialSum xs i+xs[i]:=by
  simp only [partialSum,List.take_succ_eq_append_getElem hi,List.sum_append,List.sum_singleton]

def Context (xs:List ℚ) (σ:Env):Prop:=
  Prefix (NativeRationalTabulate.words xs) "sum.input" σ∧ σ.vars "sum.count"=xs.length

def Invariant (xs:List ℚ) (σ:Env):Prop:=
  Context xs σ∧ σ.vars "sum.i"≤ xs.length∧ Stored "sum.value" (partialSum xs (σ.vars "sum.i")) σ

theorem setup_spec (B:ℕ) (h1:1< B):
    Spec B (fun _ => True) setup (fun _ τ => Stored "sum.value" 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=Stored "sum.value" (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "sum.value.s" ((0:Nat)); let c3:Env:=Env.setVar c2 "sum.value.n" ((0:Nat)); let c4:Env:=Env.setVar c3 "sum.value.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c8:Nat→ Nat:=c5 c7; let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c8 c9; let c11:Com:=Com.assign "sum.value.n" (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "sum.value.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c1 σ')) c4 (@And.intro (Run B setup σ c4 ((6:Nat))) (c1 c4) (RunStep.mono B setup σ c4 (c8 c10) ((6:Nat)) (RunStep.seq B (Com.assign "sum.value.s" (Expr.lit ((0:Nat)))) (Com.seq c11 c12) σ c2 c4 c7 c10 (RunStep.assign B σ "sum.value.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8245_0_0_0))) (RunStep.seq B c11 c12 c2 c3 c4 c7 c9 (RunStep.assign B c2 "sum.value.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g8245_0_0_1))) (RunStep.assign B c3 "sum.value.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g8245_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8245_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8245_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8245_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,fractionValue]

theorem read_spec (B H:ℕ) (xs:List ℚ) (i:ℕ) (hi:i< xs.length)
    (hs:3*xs.length+10< B) (hH:H< B) (hx:∀ x∈xs,Bounded H x):
    Spec B (fun σ => Context xs σ∧ σ.vars "sum.i"=i) read
      (fun _ τ => FractionOutput xs[i] τ) 21:=by
  rintro σ ⟨hc,hiσ⟩
  let ν:=σ.setVar "read.cursor" (3*i)
  have r1:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "sum.i"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega:3< B))
      (by rw [evalB_var_iff]; exact ⟨hiσ.symm,hiσ ▸ (by omega:i< B)⟩)
      (by change 3*i< B; omega))
  have hxi:=hx xs[i] (List.getElem_mem hi)
  obtain ⟨τ,r2,p2⟩:=NativeRationalRead.vector_entry_spec B "sum.input" [] [] xs i hi (by omega)
    (by simp; omega) (hxi.1.trans_lt hH) (hxi.2.trans_lt hH) ν
    ⟨by simpa only [List.nil_append,List.append_nil,Prefix,ν,arrs_setVar] using hc.1,by simp [ν]⟩
  exact ⟨τ,r1.seq r2,p2.1⟩

theorem command_spec (B H:ℕ) (xs:List ℚ) (hB:2*H^2+3< B)
    (hs:3*xs.length+10< B) (hx:∀ x∈xs,Bounded H x)
    (hp:∀ i≤ xs.length,Bounded H (partialSum xs i)):
    Spec B (Context xs) command (fun _ τ => Context xs τ∧ FractionOutput xs.sum τ)
      ((36*(H^2).size+149)*xs.length+18):=by
  have h1:1< B:=by nlinarith
  have hH:H< B:=by nlinarith
  have hbody:Spec B (fun σ => Invariant xs σ∧ σ.vars "sum.i"< xs.length) body
      (fun σ τ => Invariant xs τ∧ τ.vars "sum.i"=σ.vars "sum.i"+1)
      (36*(H^2).size+145):=by
    rintro σ ⟨⟨hc,hle,hacc⟩,hlt⟩
    let i:=σ.vars "sum.i"
    obtain ⟨ν,r1,p1⟩:=read_spec B H xs i hlt hs hH hx σ ⟨hc,rfl⟩
    have haccν:Stored "sum.value" (partialSum xs i) ν:=by
      simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
        r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hacc
    obtain ⟨μ,r2,p2⟩:=NativeSignedAccumulate.command_spec B H (partialSum xs i) xs[i] hB
      (hp i hle) (hx xs[i] (List.getElem_mem hlt)) ν ⟨haccν,p1⟩
    have hiμ:μ.vars "sum.i"=i:=(r1.seq r2).frame_var "sum.i" (by decide)
    let τ:=μ.setVar "sum.i" (i+1)
    have r3:Run B advance μ τ 4:=Run.assign
      (evalB_bin (op:=.add)
        (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i< B)⟩)
        (evalB_lit h1) (by change i+1< B; omega))
    have ht:τ.vars "sum.i"=i+1:=by simp [τ]
    have rr:=r1.seq (r2.seq r3)
    refine ⟨τ,rr.mono (by omega),⟨?_,by rw [ht]; omega,?_⟩,ht⟩
    · simpa only [Context,Prefix,rr.frame_arr "sum.input" (by decide),
        rr.frame_var "sum.count" (by decide)] using hc
    · rw [ht,partial_step xs i hlt]
      simpa only [Stored,String.reduceAppend,r3.frame_var "sum.value.s" (by decide),
        r3.frame_var "sum.value.n" (by decide),r3.frame_var "sum.value.d" (by decide)] using p2.1
  have hloop:=Spec.forRangeZero "sum.i" "sum.count" (Invariant xs) xs.length
    (36*(H^2).size+145) (by omega) (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  obtain ⟨ν,r1,p1⟩:=setup_spec B h1 σ trivial
  have hcν:Context xs ν:=by
    simpa only [Context,Prefix,r1.frame_arr "sum.input" (by decide),
      r1.frame_var "sum.count" (by decide)] using hc
  have hinit:Invariant xs (ν.setVar "sum.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hcν
    · simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false,if_true,
        partialSum,List.take_zero,List.sum_nil] using p1
  obtain ⟨μ,r2,p2⟩:=hloop ν hinit
  have hsum:Bounded H xs.sum:=by simpa only [partialSum,List.take_length] using hp xs.length le_rfl
  have hstored:Stored "sum.value" xs.sum μ:=by
    simpa only [p2.2,partialSum,List.take_length] using p2.1.2.2
  obtain ⟨τ,r3,p3⟩:=load_spec B "sum.value" xs.sum h1
    (hsum.1.trans_lt hH) (hsum.2.trans_lt hH) (by decide) μ hstored
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),?_,p3⟩
  simpa only [Context,Prefix,r3.frame_arr "sum.input" (by decide),
    r3.frame_var "sum.count" (by decide)] using p2.1.1

end Lax263307Proofs.NativeSignedSum

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

namespace Lax263307Proofs.NativeRestrictionOrder

open Lax263307

def vertices {n:ℕ} (R:Finset (Fin n)):List (Fin n):=
  (List.finRange n).filter fun v => v∈R

theorem vertices_sort {n:ℕ} (R:Finset (Fin n)):vertices R=R.sort (·≤·):=by
  exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.eq_of_mem_iff R.sortedLT_sort (by simp [vertices])

theorem vertices_labels {n:ℕ} (R:Finset (Fin n)):
    vertices R=List.ofFn (ComputedSeparators.label R):=by
  rw [vertices_sort]
  simpa only [List.finRange,List.map_ofFn,Function.comp_def,ComputedSeparators.label] using
    (Finset.listMap_orderEmbOfFin_finRange R rfl).symm

def selectedPrefix {n:ℕ} (R:Finset (Fin n)) (i:ℕ):List ℕ:=
  (((List.finRange n).take i).filter fun v => v∈R).map Fin.val

theorem prefix_zero {n:ℕ} (R:Finset (Fin n)):selectedPrefix R 0=[]:=by simp [selectedPrefix]

theorem prefix_length {n:ℕ} (R:Finset (Fin n)) (i:ℕ):(selectedPrefix R i).length≤ i:=by
  dsimp [selectedPrefix]
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp only [List.length_take]; omega)

theorem prefix_full {n:ℕ} (R:Finset (Fin n)):selectedPrefix R n=words R:=by
  unfold selectedPrefix
  rw [List.take_of_length_le (by simp)]
  change (vertices R).map Fin.val=words R
  rw [vertices_labels,List.map_ofFn]
  rfl

theorem prefix_step {n:ℕ} (R:Finset (Fin n)) (i:ℕ) (hi:i< n):
    selectedPrefix R (i+1)=if (⟨i,hi⟩:Fin n)∈R then selectedPrefix R i++[i] else selectedPrefix R i:=by
  unfold selectedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.filter_append,List.map_append]
  simp only [List.getElem_finRange,Fin.cast_mk]
  split_ifs <;> simp_all

end Lax263307Proofs.NativeRestrictionOrder

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeSelectedVertices

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeRestrictionOrder

def Context {n:ℕ} (R:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ Prefix (encodeOutput R) "subset.bits" σ∧ n≤(σ.arrs "restrict.vertices").length

def Invariant {n:ℕ} (R:Finset (Fin n)) (σ:Env):Prop:=
  Context R σ∧ σ.vars "restrict.i"≤ n∧
    Prefix (selectedPrefix R (σ.vars "restrict.i")) "restrict.vertices" σ∧
    σ.vars "restrict.count"=(selectedPrefix R (σ.vars "restrict.i")).length

theorem step_spec (B n:ℕ) (R:Finset (Fin n)) (hB:n+2< B):
    Spec B (fun σ => Invariant R σ∧ σ.vars "restrict.i"< n) step
      (fun σ τ => Invariant R τ∧ τ.vars "restrict.i"=σ.vars "restrict.i"+1) 18:=by
  rintro σ ⟨⟨⟨hn,hsource,hroom⟩,hle,hprefix,hcount⟩,hlt⟩
  let i:=σ.vars "restrict.i"
  let bit:=if (⟨i,hlt⟩:Fin n)∈R then 1 else 0
  have hbitB:bit< B:=by dsimp [bit]; split_ifs <;> omega
  have hilen:i<(encodeOutput R).length:=by simpa only [encodeOutput,List.length_ofFn] using hlt
  have hg:=hsource i hilen
  have he:(encodeOutput R)[i]=bit:=by simp only [encodeOutput,List.getElem_ofFn]; rfl
  rw [he] at hg
  let ν:=σ.setVar "restrict.bit" bit
  have r1:Run B (.assign "restrict.bit" (.get "subset.bits" (.var "restrict.i"))) σ ν 3:=
    Run.assign (evalB_get (evalB_var (by omega:σ.vars "restrict.i"< B)) hg hbitB)
  have hlen:=prefix_length R i
  have htest:(Cond.eq (.var "restrict.bit") (.lit 1)).evalB B ν=some (decide (bit=1)):=
    evalB_condEq (by rw [evalB_var_iff]; simp [ν,hbitB]) (evalB_lit (by omega))
  have hc:∃ μ,Run B choose ν μ 11∧ Prefix (selectedPrefix R (i+1)) "restrict.vertices" μ∧
      μ.vars "restrict.count"=(selectedPrefix R (i+1)).length:=by
    by_cases hmem:(⟨i,hlt⟩:Fin n)∈R
    · obtain ⟨μ,rr,pp⟩:=RamWordBuffer.append_spec B "restrict.vertices" "restrict.count" (selectedPrefix R i) i
        (.var "restrict.i") (by omega) (by omega) ν
        ⟨by simpa only [Prefix,ν,arrs_setVar] using hprefix,
          by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcount,
          by simpa only [ν,arrs_setVar] using (show (selectedPrefix R i).length<(σ.arrs "restrict.vertices").length by omega),
          by rw [evalB_var_iff]; simp only [ν,vars_setVar,String.reduceEq,if_false]; exact ⟨rfl,by omega⟩⟩
      have hh:Run B choose ν μ 11:=(Run.ite_true (d:=.skip) (by simpa [bit,hmem] using htest) rr).mono (by decide)
      exact ⟨μ,hh,by simpa only [prefix_step R i hlt,if_pos hmem] using pp.1,
        by simpa only [prefix_step R i hlt,if_pos hmem,List.length_append,List.length_singleton] using pp.2⟩
    · have hh:Run B choose ν ν 11:=
        (Run.ite_false (c:=RamWordBuffer.append "restrict.vertices" "restrict.count" (.var "restrict.i"))
          (by simpa [bit,hmem] using htest) Run.skip).mono (by decide)
      exact ⟨ν,hh,by simpa only [prefix_step R i hlt,if_neg hmem,Prefix,ν,arrs_setVar] using hprefix,
        by simpa only [prefix_step R i hlt,if_neg hmem,ν,vars_setVar,String.reduceEq,if_false] using hcount⟩
  obtain ⟨μ,r2,hp2,hc2⟩:=hc
  have hiμ:μ.vars "restrict.i"=i:=(r1.seq r2).frame_var "restrict.i" (by decide)
  let τ:=μ.setVar "restrict.i" (i+1)
  have r3:Run B (.assign "restrict.i" (.add (.var "restrict.i") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i< B)⟩)
      (evalB_lit (by omega)) (by change i+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr,?_,by simp [τ,i]⟩
  refine ⟨⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩,by simp [τ]; omega,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hsource
  · rwa [RamFrames.run_array_length rr]
  · simpa only [τ,vars_setVar,if_true,Prefix,arrs_setVar] using hp2
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,if_true] using hc2

theorem command_spec (B n:ℕ) (R:Finset (Fin n)) (hB:n+2< B):
    Spec B (Context R) command
      (fun _ τ => Context R τ∧ Prefix (words R) "restrict.vertices" τ∧ τ.vars "restrict.count"=R.card)
      (22*n+8):=by
  have hloop:=Spec.forRangeZero "restrict.i" "graph.n" (Invariant R) n 18 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (step_spec B n R hB)
  intro σ hc
  let ν:=σ.setVar "restrict.count" 0
  have r1:Run B (.assign "restrict.count" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant R (ν.setVar "restrict.i" 0):=by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [Prefix,prefix_zero]
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,ht⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),ht.1.1,?_,?_⟩
  · simpa only [ht.2,prefix_full] using ht.1.2.2.1
  · simpa only [ht.2,prefix_full,words,List.length_ofFn] using ht.1.2.2.2

end Lax263307Proofs.NativeSelectedVertices

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

theorem cost_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i:Fin R.card) (hB:3*n+10< B) (hM:M< B)
    (hx:∀ v,Bounded M (x v)):
    Spec B (fun σ => Data G x R σ∧ σ.vars "restrict.row"=i.val) costRead
      (fun _ τ => Data G x R τ∧ RamRational.FractionOutput (x (ComputedSeparators.label R i)) τ) 24:=by
  let u:=ComputedSeparators.label R i
  have hiB:i.val< B:=i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB:u.val< B:=u.isLt.trans (by omega)
  rintro σ ⟨hd,hi⟩
  let ν:=σ.setVar "restrict.u" u.val
  have r1:Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ:=ν.setVar "read.cursor" (3*u.val)
  have r2:Run B (.assign "read.cursor" (.mul (.lit 3) (.var "restrict.u"))) ν μ 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simp [ν,huB]) (by change 3*u.val< B; have hh:=u.isLt; omega))
  obtain ⟨τ,r3,p3⟩:=NativeRationalRead.vector_entry_spec B "near.costs" [] [] (List.ofFn x) u.val
    (by simpa only [List.length_ofFn] using u.isLt) (by omega) (by have hh:=u.isLt; simp; omega)
    (by simpa only [List.getElem_ofFn] using (hx u).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (hx u).2.trans_lt hM) μ
    ⟨by simpa only [NativeRationalTabulate.words,encodeVector,List.nil_append,List.append_nil,Prefix,
        (r1.seq r2).frame_arr "near.costs" (by decide)] using hd.costs,by simp [μ]⟩
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simpa only [List.getElem_ofFn] using p3.1⟩

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

namespace Lax263307Proofs.NativeUniformWordGuards

theorem scalar (v w:ℕ) (h:v≤ w):v<2^w:=h.trans_lt Nat.lt_two_pow_self

theorem virtual (u w:ℕ) (h:2*u+4≤ w):2*(2^u)^2+3<2^w:=by
  have hpow:2^(u*2+4)≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_add] at hpow
  norm_num at hpow
  rw [←pow_mul]
  have hp:=Nat.two_pow_pos (u*2)
  nlinarith only [hpow,hp]

end Lax263307Proofs.NativeUniformWordGuards

end

section

namespace Lax263307Proofs.NativeComponentCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

theorem read_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (i:Fin R.card) (hB:3*n+10< B)
    (hM:M< B) (hx:∀ v,Bounded M (x v)):
    Spec B (fun σ => Data G x R σ∧ σ.vars "component.vertex"=i.val) read
      (fun _ τ => Data G x R τ∧ RamRational.FractionOutput (x (label R i)) τ) 26:=by
  have hr:=NativeMaskUnpack.card_bound R
  have hiB:i.val< B:=i.isLt.trans_le hr |>.trans (by omega)
  rintro σ ⟨hd,hi⟩
  let ν:=σ.setVar "restrict.row" i.val
  have r1:Run B (.assign "restrict.row" (.var "component.vertex")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
  obtain ⟨τ,r2,p2⟩:=cost_spec B M n G x R i hB hM hx ν
    ⟨frame r1 hd (by decide) (by decide),by simp [ν]⟩
  exact ⟨τ,r1.seq r2,p2⟩

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (hB:3*n+10< B) (hM:M< B)
    (hx:∀ v,Bounded M (x v)):
    Spec B (fun σ => Data G x R σ∧ 3*R.card<(σ.arrs "lp.word").length) command
      (fun _ τ => Data G x R τ∧ Prefix (encodeVector (fun i => x (label R i))) "lp.word" τ∧
        τ.vars "lp.position"=3*R.card) (61*R.card+8):=by
  let qs:=List.ofFn (fun i:Fin R.card => x (label R i))
  have hr:=NativeMaskUnpack.card_bound R
  have hv:=RamVectorEncoding.command_spec B 26 (Data G x R) "component.vertex" "restrict.count" qs [] read
    (by omega) (by simp [qs]; omega)
    (by intro i hi; simp only [qs,List.getElem_ofFn]; exact (hx _).1.trans_lt hM)
    (by intro i hi; simp only [qs,List.getElem_ofFn]; exact (hx _).2.trans_lt hM)
    (fun _ hd => by simpa only [qs,List.length_ofFn] using hd.count)
    (by
      intro σ k hd
      exact ⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩)
    (by
      intro i hi
      simpa only [qs,List.getElem_ofFn] using read_spec B M n G x R ⟨i,by simpa [qs] using hi⟩ hB hM hx)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hroom⟩
  let ν:=σ.setVar "lp.position" 0
  have r1:Run B (.assign "lp.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (show 0< B by omega))
  obtain ⟨τ,r2,p2⟩:=hv ν ⟨frame r1 hd (by decide) (by decide),by simp [Prefix],by simp [ν],
    by simpa only [List.length_nil,qs,List.length_ofFn,Nat.zero_add,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [qs,List.length_ofFn]; omega),p2.1,
    by simpa only [List.nil_append,RamVectorEncoding.encode,qs,encodeVector] using p2.2.1,
    by simpa only [List.length_nil,qs,List.length_ofFn,Nat.zero_add] using p2.2.2⟩

end Lax263307Proofs.NativeComponentCosts

end

section

namespace Lax263307Proofs.NativeComponentSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

theorem setup_spec (B r:ℕ) (hB:3*r+10< B):
    Spec B (fun σ => σ.vars "restrict.count"=r∧ σ.vars "lp.position"=3*r) setup
      (fun _ τ => τ.vars "sum.count"=r∧ τ.vars "fill.length"=3*r∧ τ.vars "slice.start"=0) 6:=by
  rintro σ ⟨hc,hp⟩
  (expose_names;
    (refine let c0:Nat:=Nat.mul ((3:Nat)) r; let c1:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "sum.count") r) (And (@Eq Nat (Env.vars τ "fill.length") c0) (@Eq Nat (Env.vars τ "slice.start") ((0:Nat))))) σ; let c2:Nat:=Env.vars (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) "lp.position"; let c3:Env:=Env.setVar (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) "fill.length" c2; let c4:Env:=Env.setVar c3 "slice.start" ((0:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "restrict.count")); let c8:Nat:=c6 (Expr.size (Expr.var "lp.position")); let c9:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c10:Nat:=c5 c8 c9; let c11:Com:=Com.assign "slice.start" (Expr.lit ((0:Nat))); let c12:String→ Nat:=Env.vars c4; @Exists.intro Env (fun (σ':Env) => And (Run B setup σ σ' ((6:Nat))) (c1 σ')) c4 (@And.intro (Run B setup σ c4 ((6:Nat))) (c1 c4) (RunStep.mono B setup σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "sum.count" (Expr.var "restrict.count")) (Com.seq (Com.assign "fill.length" (Expr.var "lp.position")) c11) σ (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) c4 c7 c10 (RunStep.assign B σ "sum.count" (Expr.var "restrict.count") (Env.vars σ "restrict.count") (RunStep.eval_var B σ "restrict.count" (?nAX_g8919_0_0_0))) (RunStep.seq B (Com.assign "fill.length" (Expr.var "lp.position")) c11 (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) c3 c4 c8 c9 (RunStep.assign B (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) "fill.length" (Expr.var "lp.position") c2 (RunStep.eval_var B (Env.setVar σ "sum.count" (Env.vars σ "restrict.count")) "lp.position" (?nAX_g8919_0_0_1))) (RunStep.assign B c3 "slice.start" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c3 (?nAX_g8919_0_0_2))))) (?nAX_g8919_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8919_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8919_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8919_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8919_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]

theorem sum_labels {n:ℕ} (R:Finset (Fin n)) (x:Fin n→ ℚ):
    (List.ofFn (fun i:Fin R.card => x (label R i))).sum=∑ v∈R,x v:=by
  have him:(Finset.univ:Finset (Fin R.card)).image (label R)=R:=
    Finset.image_orderEmbOfFin_univ R rfl
  calc
    _=∑ i:Fin R.card,x (label R i):=by simp [List.sum_ofFn]
    _=∑ v∈(Finset.univ:Finset (Fin R.card)).image (label R),x v:=
      (Finset.sum_image (by intro i hi j hj h; exact (label R).injective h)).symm
    _=∑ v∈R,x v:=by rw [him]

theorem command_spec (B M n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (R:Finset (Fin n)) (hM:1≤ M) (hN:3*n+10< B)
    (hB:2*((2*M)^(R.card+1))^2+3< B) (hx:∀ v,Bounded M (x v)):
    Spec B (fun σ => Data G x R σ∧ 3*R.card<(σ.arrs "lp.word").length∧
      3*R.card≤(σ.arrs "sum.input").length) command
      (fun _ τ => Data G x R τ∧ RamRational.FractionOutput (∑ v∈R,x v) τ)
      ((36*(((2*M)^(R.card+1))^2).size+258)*R.card+38):=by
  let qs:=List.ofFn (fun i:Fin R.card => x (label R i))
  let H:=(2*M)^(R.card+1)
  have hlen:qs.length=R.card:=by simp [qs]
  have hr:=NativeMaskUnpack.card_bound R
  have hHM:M≤ H:=by
    calc
      M≤2*M:=by omega
      _=(2*M)^1:=(pow_one _).symm
      _≤ H:=Nat.pow_le_pow_right (by omega) (by omega)
  have hHH:2*H^2+3< B:=hB
  have hHB:H< B:=by nlinarith only [hHH,Nat.le_mul_self H]
  have hMB:M< B:=hHM.trans_lt hHB
  have hqs:∀ q∈qs,Bounded M q:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact hx _
  have hwords:∀ z∈NativeRationalTabulate.words qs,z< B:=by
    intro z hz
    obtain ⟨q,hq,hz⟩:=List.mem_flatMap.mp hz
    simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact (hqs q hq).1.trans_lt hMB
    · exact (hqs q hq).2.trans_lt hMB
  rintro σ ⟨hd,hwordroom,hsumroom⟩
  obtain ⟨ν,r1,p1⟩:=NativeComponentCosts.command_spec B M n G x R hN hMB hx σ ⟨hd,hwordroom⟩
  obtain ⟨μ,r2,p2⟩:=setup_spec B R.card (by omega) ν ⟨p1.1.count,p1.2.2⟩
  have hp2:Prefix (NativeRationalTabulate.words qs) "lp.word" μ:=by
    simpa only [qs,NativeRationalTabulate.words,encodeVector,Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  obtain ⟨ρ,r3,p3⟩:=NativeSlice.command_spec B "lp.word" "sum.input" [] (NativeRationalTabulate.words qs) [] (by decide)
    (by simp only [List.length_nil,NativeRationalTabulate.words_length,hlen,Nat.zero_add]; omega) hwords μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil] using hp2,by simpa only [List.length_nil] using p2.2.2⟩,
      by simpa only [NativeRationalTabulate.words_length,hlen] using p2.2.1,
      by simpa only [NativeRationalTabulate.words_length,hlen,RamFrames.run_array_length r2,RamFrames.run_array_length r1] using hsumroom⟩
  obtain ⟨τ,r4,p4⟩:=NativeSignedSum.command_spec B H qs hB (by rw [hlen]; omega)
    (fun q hq => by simpa only [hlen] using NativeSumHeight.uniform_entry M qs hM hqs q hq)
    (fun i _ => by simpa only [hlen,NativeSignedSum.partialSum] using NativeSumHeight.uniform_partial M qs hM hqs i) ρ
    ⟨p3.2,by simpa only [hlen] using (r3.frame_var "sum.count" (by decide)).trans p2.1⟩
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono ?_,frame rr hd (by decide) (by decide),?_⟩
  · simp only [NativeRationalTabulate.words_length,hlen]
    dsimp only [H]
    nlinarith only []
  · simpa only [qs,sum_labels] using p4.2

end Lax263307Proofs.NativeComponentSum

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeComponentTarget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational

def numerator (D:ℕ) (q:ℚ):ℕ:=(D-1)*q.num.natAbs
def denominator (D:ℕ) (q:ℚ):ℕ:=D*q.den
def left (n D:ℕ) (q:ℚ):ℕ:=4*n*D*q.num.natAbs
def right (k:ℕ) (q:ℚ):ℕ:=k*q.den
def value (D:ℕ) (q:ℚ):ℕ:=numerator D q/denominator D q+1

def resource (n D k:ℕ) (q:ℚ):ℕ:=
  n+D+k+q.num.natAbs+q.den+4*n+4*n*D+left n D q+right k q+
    2*numerator D q+denominator D q+20

theorem nonnegative_encoding (q:ℚ) (hq:0≤ q):
    (q.num.natAbs:ℚ)/(q.den:ℚ)=q:=by
  have he:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hc:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) he
  rw [hc,q.num_div_den]

theorem target_eq (D:ℕ) (q:ℚ) (hD:0< D) (hq:0≤ q):
    Lax263307.ComputedRounding.target (1/(D:ℚ)) q=value D q:=by
  have hDc:(D:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hqc:(q.den:ℚ)≠0:=by exact_mod_cast q.den_ne_zero
  have he:(1-1/(D:ℚ))*q=(numerator D q:ℚ)/(denominator D q:ℚ):=by
    calc
      _=(1-1/(D:ℚ))*((q.num.natAbs:ℚ)/(q.den:ℚ)):=
        congrArg (fun z:ℚ => (1-1/(D:ℚ))*z) (nonnegative_encoding q hq).symm
      _=_:=by
        simp only [numerator,denominator,Nat.cast_mul,Nat.cast_sub (show 1≤ D by omega),Nat.cast_one]
        field_simp [hDc,hqc]
        <;> ring
  unfold Lax263307.ComputedRounding.target value
  rw [he,Rat.natFloor_natCast_div_natCast]

theorem heavy_iff (n D k:ℕ) (q:ℚ) (hn:0< n) (hD:0< D) (hq:0≤ q):
    right k q< left n D q↔ (1/(D:ℚ))*k/(4*(n:ℚ))< q:=by
  have hDc:(D:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hnc:(n:ℚ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  have hqc:0<(q.den:ℚ):=by exact_mod_cast q.den_pos
  have hprod:0<4*(n:ℚ)*D:=by positivity
  have he:(1/(D:ℚ))*k/(4*(n:ℚ))=(k:ℚ)/(4*n*D):=by field_simp [hDc,hnc] <;> ring
  rw [he]
  have hc:(k*q.den:ℚ)<(q.num.natAbs:ℚ)*(4*n*D)↔ k*q.den<4*n*D*q.num.natAbs:=by
    norm_cast <;> ring_nf
  have hcross:(k:ℚ)/(4*n*D)<(q.num.natAbs:ℚ)/(q.den:ℚ)↔ right k q< left n D q:=by
    rw [div_lt_div_iff₀ hprod hqc]
    exact hc
  have hencode:(k:ℚ)/(4*n*D)< q↔ (k:ℚ)/(4*n*D)<(q.num.natAbs:ℚ)/(q.den:ℚ):=by
    rw [nonnegative_encoding q hq]
  exact (hencode.trans hcross).symm

theorem command_spec (B n D k:ℕ) (q:ℚ) (hn:0< n) (hD:0< D) (hq:0≤ q)
    (hB:resource n D k q< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "algorithm.D"=D∧
      σ.vars "conditioning.k"=k∧ FractionOutput q σ) command
      (fun _ τ => τ.vars "component.target"=Lax263307.ComputedRounding.target (1/(D:ℚ)) q∧
        τ.vars "component.active"=if (1/(D:ℚ))*k/(4*(n:ℚ))< q then 1 else 0) 34:=by
  have hg:=hB
  dsimp [resource,numerator,denominator,left,right] at hg
  have hnB:numerator D q+2< B:=by dsimp [numerator]; omega
  have hdB:denominator D q< B:=by dsimp [denominator]; omega
  have hlB:left n D q< B:=by dsimp [left]; omega
  have hrB:right k q< B:=by dsimp [right]; omega
  have hp:Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "algorithm.D"=D∧
      σ.vars "conditioning.k"=k∧ FractionOutput q σ) products
      (fun _ τ => τ.vars "component.numerator"=numerator D q∧
        τ.vars "component.denominator"=denominator D q∧ τ.vars "component.left"=left n D q∧
        τ.vars "component.right"=right k q) 22:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (And (@Eq Nat (Env.vars σ "algorithm.D") D) (And (@Eq Nat (Env.vars σ "conditioning.k") k) (FractionOutput q σ)))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "conditioning.k") k) (FractionOutput q σ); let c1:Prop:=And (@Eq Nat (Env.vars σ "algorithm.D") D) c0; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "component.numerator") (numerator D q)) (And (@Eq Nat (Env.vars τ "component.denominator") (denominator D q)) (And (@Eq Nat (Env.vars τ "component.left") (left n D q)) (@Eq Nat (Env.vars τ "component.right") (right k q))))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B products σ σ' ((22:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Nat→ Nat→ Nat:=Nat.mul; let c6:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "algorithm.D") ((1:Nat)); let c7:Nat:=c5 c6 (Env.vars σ "rat.n"); let c8:Env:=Env.setVar σ "component.numerator" c7; let c9:String→ Nat:=Env.vars c8; let c10:Nat:=c9 "algorithm.D"; let c11:Nat:=c9 "rat.d"; let c12:Nat:=c5 c10 c11; let c13:Env:=Env.setVar c8 "component.denominator" c12; let c14:String→ Nat:=Env.vars c13; let c15:Nat:=c14 "graph.n"; let c16:Nat:=c5 ((4:Nat)) c15; let c17:Nat:=c14 "algorithm.D"; let c18:Nat:=c5 c16 c17; let c19:Nat:=c14 "rat.n"; let c20:Nat:=c5 c18 c19; let c21:Env:=Env.setVar c13 "component.left" c20; let c22:String→ Nat:=Env.vars c21; let c23:Nat:=c22 "conditioning.k"; let c24:Nat:=c22 "rat.d"; let c25:Nat:=c5 c23 c24; let c26:Env:=Env.setVar c21 "component.right" c25; let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Expr:=Expr.sub (Expr.var "algorithm.D") (Expr.lit ((1:Nat))); let c30:Expr:=Expr.mul c29 (Expr.var "rat.n"); let c31:Nat:=c28 (Expr.size c30); let c32:Nat:=c28 (Expr.size (Expr.mul (Expr.var "algorithm.D") (Expr.var "rat.d"))); let c33:Expr:=Expr.mul (Expr.lit ((4:Nat))) (Expr.var "graph.n"); let c34:Expr:=Expr.mul c33 (Expr.var "algorithm.D"); let c35:Expr:=Expr.mul c34 (Expr.var "rat.n"); let c36:Nat:=c28 (Expr.size c35); let c37:Nat:=c28 (Expr.size (Expr.mul (Expr.var "conditioning.k") (Expr.var "rat.d"))); let c38:Nat:=c27 c36 c37; let c39:Nat:=c27 c32 c38; let c40:Com:=Com.assign "component.denominator" (Expr.mul (Expr.var "algorithm.D") (Expr.var "rat.d")); let c41:Com:=Com.assign "component.left" c35; let c42:Com:=Com.assign "component.right" (Expr.mul (Expr.var "conditioning.k") (Expr.var "rat.d")); let c43:Com:=Com.seq c41 c42; let c44:String→ Nat:=Env.vars c26; @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c1 (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c1) => c4) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c1) => @And.casesOn (@Eq Nat (Env.vars σ "algorithm.D") D) c0 (fun (x:c1) => c4) right fun (left_1:@Eq Nat (Env.vars σ "algorithm.D") D) (right_1:c0) => @And.casesOn (@Eq Nat (Env.vars σ "conditioning.k") k) (FractionOutput q σ) (fun (x:c0) => c4) right_1 fun (left_2:@Eq Nat (Env.vars σ "conditioning.k") k) (right_2:FractionOutput q σ) => @Exists.intro Env c3 c26 (@And.intro (Run B products σ c26 ((22:Nat))) (c2 c26) (RunStep.mono B products σ c26 (c27 c31 c39) ((22:Nat)) (RunStep.seq B (Com.assign "component.numerator" c30) (Com.seq c40 c43) σ c8 c26 c31 c39 (RunStep.assign B σ "component.numerator" c30 c7 (RunStep.eval_mul B σ c29 (Expr.var "rat.n") c6 (Env.vars σ "rat.n") (RunStep.eval_sub B σ (Expr.var "algorithm.D") (Expr.lit ((1:Nat))) (Env.vars σ "algorithm.D") ((1:Nat)) (RunStep.eval_var B σ "algorithm.D" (?nAX_g8934_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8934_0_0_1)) (?nAX_g8934_0_0_2)) (RunStep.eval_var B σ "rat.n" ?_) ?_)) (RunStep.seq B c40 c43 c8 c13 c26 c32 c38 (RunStep.assign B c8 "component.denominator" (Expr.mul (Expr.var "algorithm.D") (Expr.var "rat.d")) c12 (RunStep.eval_mul B c8 (Expr.var "algorithm.D") (Expr.var "rat.d") c10 c11 (RunStep.eval_var B c8 "algorithm.D" (?nAX_g8934_0_0_3)) (RunStep.eval_var B c8 "rat.d" ?_) ?_)) (RunStep.seq B c41 c42 c13 c21 c26 c36 c37 (RunStep.assign B c13 "component.left" c35 c20 (RunStep.eval_mul B c13 c34 (Expr.var "rat.n") c18 c19 (RunStep.eval_mul B c13 c33 (Expr.var "algorithm.D") c16 c17 (RunStep.eval_mul B c13 (Expr.lit ((4:Nat))) (Expr.var "graph.n") ((4:Nat)) c15 (RunStep.eval_lit B ((4:Nat)) c13 (?nAX_g8934_0_0_4)) (RunStep.eval_var B c13 "graph.n" (?nAX_g8934_0_0_5)) (?nAX_g8934_0_0_6)) (RunStep.eval_var B c13 "algorithm.D" (?nAX_g8934_0_0_7)) ?_) (RunStep.eval_var B c13 "rat.n" ?_) ?_)) (RunStep.assign B c21 "component.right" (Expr.mul (Expr.var "conditioning.k") (Expr.var "rat.d")) c25 (RunStep.eval_mul B c21 (Expr.var "conditioning.k") (Expr.var "rat.d") c23 c24 (RunStep.eval_var B c21 "conditioning.k" (?nAX_g8934_0_0_8)) (RunStep.eval_var B c21 "rat.d" ?_) ?_))))) (?nAX_g8934_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8934_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8934_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [FractionOutput,_root_.Lax263307Proofs.NativeComponentTarget.numerator,_root_.Lax263307Proofs.NativeComponentTarget.denominator,_root_.Lax263307Proofs.NativeComponentTarget.left,_root_.Lax263307Proofs.NativeComponentTarget.right]
    all_goals omega
  have htB:value D q< B:=by
    have hh:=Nat.div_le_self (numerator D q) (denominator D q)
    dsimp only [value]
    omega
  rintro σ hs
  obtain ⟨ν,r1,p1⟩:=hp σ hs
  let μ:=ν.setVar "component.target" (value D q)
  have r2:Run B (.assign "component.target" (.add (.div (.var "component.numerator") (.var "component.denominator")) (.lit 1))) ν μ 6:=Run.assign
    (evalB_bin (op:=.add)
      (evalB_bin (op:=.div)
        (by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ (by omega:numerator D q< B)⟩)
        (by rw [evalB_var_iff]; exact ⟨p1.2.1.symm,p1.2.1 ▸ (by omega:denominator D q< B)⟩)
        (by change numerator D q/denominator D q< B; have hh:=Nat.div_le_self (numerator D q) (denominator D q); omega))
      (evalB_lit (show 1< B by omega)) htB)
  have hleft:=(r2.frame_var "component.left" (by decide)).trans p1.2.2.1
  have hright:=(r2.frame_var "component.right" (by decide)).trans p1.2.2.2
  have hc:(Cond.lt (.var "component.right") (.var "component.left")).evalB B μ=
      some (decide (right k q< left n D q)):=evalB_condLt
    (by rw [evalB_var_iff]; exact ⟨hright.symm,hright ▸ (by omega:right k q< B)⟩)
    (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ (by omega:left n D q< B)⟩)
  by_cases h:right k q< left n D q
  · let τ:=μ.setVar "component.active" 1
    have r3:Run B (.assign "component.active" (.lit 1)) μ τ 2:=Run.assign (evalB_lit (show 1< B by omega))
    have rb:=Run.ite_true (d:=.assign "component.active" (.lit 0)) (by simpa only [h,decide_true] using hc) r3
    refine ⟨τ,(r1.seq (r2.seq rb)).mono (by simp [Cond.size,Expr.size]),
      by simpa only [τ,μ,vars_setVar,String.reduceEq,if_false,if_true] using (target_eq D q hD hq).symm,
      ?_⟩
    rw [if_pos ((heavy_iff n D k q hn hD hq).mp h)]
    simp only [τ,vars_setVar,if_true]
  · let τ:=μ.setVar "component.active" 0
    have r3:Run B (.assign "component.active" (.lit 0)) μ τ 2:=Run.assign (evalB_lit (show 0< B by omega))
    have rb:=Run.ite_false (c:=.assign "component.active" (.lit 1)) (by simpa only [h,decide_false] using hc) r3
    refine ⟨τ,(r1.seq (r2.seq rb)).mono (by simp [Cond.size,Expr.size]),
      by simpa only [τ,μ,vars_setVar,String.reduceEq,if_false,if_true] using (target_eq D q hD hq).symm,
      ?_⟩
    rw [if_neg (mt (heavy_iff n D k q hn hD hq).mpr h)]
    simp only [τ,vars_setVar,if_true]

end Lax263307Proofs.NativeComponentTarget

end

section

namespace Lax263307Proofs.NativeComponentResources

open Lax263307Proofs.NativeSignedArithmetic

theorem numeric_bound (n D k M:ℕ) (q:ℚ) (hM:1≤ M) (hq:Bounded M q):
    NativeComponentTarget.resource n D k q≤20*(span n D k)^2*M:=by
  let S:=span n D k
  have hS:1≤ S:=by dsimp [S,span]; omega
  have hn:n≤ S:=by dsimp [S,span]; omega
  have hD:D≤ S:=by dsimp [S,span]; omega
  have hk:k≤ S:=by dsimp [S,span]; omega
  have h4n:4*n≤4*S:=Nat.mul_le_mul_left 4 hn
  have hnD:4*n*D≤4*S^2:=by nlinarith only [Nat.mul_le_mul hn hD]
  have hnum:(D-1)*q.num.natAbs≤ S*M:=Nat.mul_le_mul ((Nat.sub_le D 1).trans hD) hq.1
  have hden:D*q.den≤ S*M:=Nat.mul_le_mul hD hq.2
  have hleft:4*n*D*q.num.natAbs≤4*S^2*M:=Nat.mul_le_mul hnD hq.1
  have hright:k*q.den≤ S*M:=Nat.mul_le_mul hk hq.2
  have hp:S≤ S^2:=by simpa only [pow_two] using Nat.le_mul_self S
  have hpS:S^2≤ S^2*M:=Nat.le_mul_of_pos_right _ (by omega)
  have hSM:S*M≤ S^2*M:=Nat.mul_le_mul_right M hp
  have hSM0:S≤ S^2*M:=hp.trans hpS
  have hMM:M≤ S^2*M:=Nat.le_mul_of_pos_left _ (by positivity)
  have hbase:n+D+k+20=S:=rfl
  calc
    NativeComponentTarget.resource n D k q≤ S+2*M+4*S+4*S^2+4*S^2*M+4*S*M:=by
      dsimp [NativeComponentTarget.resource,NativeComponentTarget.left,NativeComponentTarget.right,
        NativeComponentTarget.numerator,NativeComponentTarget.denominator]
      nlinarith only [hbase,hq.1,hq.2,h4n,hnD,hnum,hden,hleft,hright]
    _≤20*S^2*M:=by nlinarith only [hpS,hSM,hSM0,hMM]

theorem word_bound (n D k h w:ℕ) (q:ℚ) (hq:Bounded (2^h) q)
    (hw:h+2*span n D k+6≤ w):NativeComponentTarget.resource n D k q<2^w:=by
  let S:=span n D k
  have hb:=numeric_bound n D k (2^h) q (Nat.one_le_pow _ _ (by decide)) hq
  have hs:S≤2^S:=Nat.lt_two_pow_self.le
  have hsq:S^2≤(2^S)^2:=Nat.pow_le_pow_left hs 2
  have hprod:20*S^2*2^h≤2^5*(2^S)^2*2^h:=Nat.mul_le_mul_right _
    (Nat.mul_le_mul (by decide:20≤2^5) hsq)
  have he:2^5*(2^S)^2*2^h=2^(h+2*S+5):=by
    rw [← pow_mul,← pow_add,← pow_add]
    congr 1
    omega
  have ht:2^(h+2*S+5)<2^w:=Nat.pow_lt_pow_right (by decide) (by dsimp only [S] at *; omega)
  exact hb.trans_lt ((hprod.trans_eq he).trans_lt ht)

end Lax263307Proofs.NativeComponentResources

end

section

namespace Lax263307Proofs.NativeComponentDecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead
open scoped NNRat

theorem command_spec (n D k h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (hn:0< n) (hD:0< D) (hx:∀ v,Bounded (2^h) (x v:ℚ))
    (w:ℕ) (hw:wordHeight n D k h≤ w) (R:Finset (Fin n)):
    Spec (2^w) (fun σ => Data G (fun v => (x v:ℚ)) R σ∧
      σ.vars "algorithm.D"=D∧ σ.vars "conditioning.k"=k∧
      3*n<(σ.arrs "lp.word").length∧ 3*n≤(σ.arrs "sum.input").length)
      command (fun _ τ => Data G (fun v => (x v:ℚ)) R τ∧
        τ.vars "component.target"=Lax263307.ComputedRounding.target (1/(D:ℚ)) (∑ v∈R,(x v:ℚ))∧
        τ.vars "component.active"=if (1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈R,(x v:ℚ)) then 1 else 0)
      (timeBound n h):=by
  let L:=(h+1)*(n+1)
  have hr:=NativeMaskUnpack.card_bound R
  have hH:(2*(2^h))^(R.card+1)=2^((h+1)*(R.card+1)):=by
    have he:2*2^h=2^(h+1):=by rw [pow_succ]; exact Nat.mul_comm _ _
    rw [he,pow_mul]
  have hHn:(2*(2^h))^(R.card+1)≤ height n h:=by
    rw [hH]
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left _ (by omega)
  have hword:=hw
  dsimp only [wordHeight] at hword
  have hWL:2*L+4*NativeComponentResources.span n D k+20≤ w:=hw
  have hspan:n+20≤ NativeComponentResources.span n D k:=by dsimp [NativeComponentResources.span]; omega
  have hB:2*(height n h)^2+3<2^w:=NativeUniformWordGuards.virtual L w (by omega)
  have hN:3*n+10<2^w:=NativeUniformWordGuards.scalar _ w (by omega)
  have hBR:2*((2*(2^h))^(R.card+1))^2+3<2^w:=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hHn 2)) 3).trans_lt hB
  let qs:=List.ofFn (fun i:Fin R.card => (x (label R i):ℚ))
  have hqs:∀ q∈qs,Bounded (2^h) q:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact hx _
  have hsum:Bounded (height n h) (∑ v∈R,(x v:ℚ)):=by
    have hb:=NativeSumHeight.sum_bits h qs hqs
    have hle:2^((h+1)*qs.length)≤ height n h:=Nat.pow_le_pow_right (by decide)
      (by simp only [qs,List.length_ofFn]; exact Nat.mul_le_mul_left _ (by omega))
    have he:qs.sum=∑ v∈R,(x v:ℚ):=NativeComponentSum.sum_labels R (fun v => (x v:ℚ))
    rw [he] at hb
    exact NativeSumHeight.weaken hle hb
  have hq:0≤∑ v∈R,(x v:ℚ):=Finset.sum_nonneg (fun v _ => (x v).coe_nonneg)
  have htB:NativeComponentTarget.resource n D k (∑ v∈R,(x v:ℚ))<2^w:=
    NativeComponentResources.word_bound n D k L w _ hsum (by omega)
  rintro σ ⟨hd,hDσ,hkσ,hwordroom,hsumroom⟩
  obtain ⟨ν,r1,p1⟩:=NativeComponentSum.command_spec (2^w) (2^h) n G (fun v => (x v:ℚ)) R
    (Nat.one_le_pow _ _ (by decide)) hN hBR hx σ ⟨hd,by omega,by omega⟩
  obtain ⟨τ,r2,p2⟩:=NativeComponentTarget.command_spec (2^w) n D k _ hn hD hq htB ν
    ⟨p1.1.order,(r1.frame_var "algorithm.D" (by decide)).trans hDσ,
      (r1.frame_var "conditioning.k" (by decide)).trans hkσ,p1.2⟩
  have hsize:(((2*(2^h))^(R.card+1))^2).size≤((height n h)^2).size:=
    Nat.size_le_size (Nat.pow_le_pow_left hHn 2)
  have hcost:(36*(((2*(2^h))^(R.card+1))^2).size+258)*R.card≤
      (36*((height n h)^2).size+258)*n:=Nat.mul_le_mul (by omega) hr
  exact ⟨τ,(r1.seq r2).mono (by dsimp only [timeBound]; omega),
    frame r2 p1.1 (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeComponentDecision

end

section

namespace Lax263307Proofs.NativeComponentLoad

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeMasks NativeSignedArithmetic
open scoped NNRat

theorem prepare_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ) (parts:List (Finset (Fin n))) (i:ℕ) (hi:i< parts.length)
    (hB:n+parts.length+3< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
      Prefix (encodeVector x) "near.costs" σ∧ σ.vars "component.i"=i∧
      Prefix (parts.map mask) "separator.pieces" σ∧ n≤(σ.arrs "subset.bits").length∧
      n≤(σ.arrs "restrict.vertices").length) prepare
      (fun _ τ => NativeRestrictionRead.Data G x parts[i] τ∧ τ.vars "component.mask"=mask parts[i]∧
        τ.vars "component.i"=i) (43*n+21):=by
  rintro σ ⟨hn,hgraph,hcosts,hidx,hparts,hbits,hlabels⟩
  have hget:=hparts i (by simpa using hi)
  simp only [List.getElem_map] at hget
  let ν:=σ.setVar "component.mask" (mask parts[i])
  have r0:Run B (.assign "component.mask" (.get "separator.pieces" (.var "component.i"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ (by omega)⟩)
      hget ((mask_bound _).trans hm))
  let μ:=ν.setVar "unpack.mask" (mask parts[i])
  have r1:Run B (.assign "unpack.mask" (.var "component.mask")) ν μ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨by simp [ν],by simp [ν]; exact (mask_bound _).trans hm⟩)
  obtain ⟨ρ,r2,p2⟩:=NativeMaskUnpack.command_spec B parts[i] (by omega) hm μ
    ⟨((r0.seq r1).frame_var _ (by decide)).trans hn,by simp [μ],
      by rw [RamFrames.run_array_length (r0.seq r1)]; exact hbits⟩
  have pre:=r0.seq (r1.seq r2)
  obtain ⟨τ,r3,p3⟩:=NativeSelectedVertices.command_spec B n parts[i] (by omega) ρ
    ⟨(pre.frame_var _ (by decide)).trans hn,p2.1,
      by rw [RamFrames.run_array_length pre]; exact hlabels⟩
  have rr:=r0.seq (r1.seq (r2.seq r3))
  refine ⟨τ,rr.mono (by omega),⟨p3.2.1,?_,?_,p3.2.2,p3.1.1⟩,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hgraph
  · simpa only [Prefix,rr.frame_arr "near.costs" (by decide)] using hcosts
  · exact ((r1.seq (r2.seq r3)).frame_var _ (by decide)).trans (by simp [ν])
  · exact (rr.frame_var _ (by decide)).trans hidx

theorem command_spec (n D k h:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (hn:0< n) (hD:0< D) (hx:∀ v,Bounded (2^h) (x v:ℚ))
    (w:ℕ) (hw:NativeComponentDecision.wordHeight n D k h≤ w)
    (parts:List (Finset (Fin n))) (hparts:parts.length≤ n+1) (i:ℕ) (hi:i< parts.length):
    Spec (2^w) (fun σ => σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
      Prefix (encodeVector (fun v => (x v:ℚ))) "near.costs" σ∧ σ.vars "component.i"=i∧
      Prefix (parts.map mask) "separator.pieces" σ∧ n≤(σ.arrs "subset.bits").length∧
      n≤(σ.arrs "restrict.vertices").length∧ σ.vars "algorithm.D"=D∧ σ.vars "conditioning.k"=k∧
      3*n<(σ.arrs "lp.word").length∧ 3*n≤(σ.arrs "sum.input").length) command
      (fun _ τ => NativeRestrictionRead.Data G (fun v => (x v:ℚ)) parts[i] τ∧
        τ.vars "component.mask"=mask parts[i]∧ τ.vars "component.i"=i∧
        τ.vars "component.target"=ComputedRounding.target (1/(D:ℚ)) (∑ v∈parts[i],(x v:ℚ))∧
        τ.vars "component.active"=if (1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈parts[i],(x v:ℚ)) then 1 else 0)
      (43*n+21+NativeComponentDecision.timeBound n h):=by
  have hwidth:=hw
  dsimp only [NativeComponentDecision.wordHeight,NativeComponentResources.span] at hwidth
  have hB:n+parts.length+3<2^w:=NativeUniformWordGuards.scalar _ w (by omega)
  have hm:2^n<2^w:=Nat.pow_lt_pow_right (by decide) (by omega)
  rintro σ ⟨horder,hgraph,hcosts,hidx,hpieces,hbits,hlabels,hDσ,hk,hlp,hsum⟩
  obtain ⟨ν,r1,p1⟩:=prepare_spec (2^w) G (fun v => (x v:ℚ)) parts i hi hB hm σ
    ⟨horder,hgraph,hcosts,hidx,hpieces,hbits,hlabels⟩
  obtain ⟨τ,r2,p2⟩:=NativeComponentDecision.command_spec n D k h G x hn hD hx w hw parts[i] ν
    ⟨p1.1,(r1.frame_var _ (by decide)).trans hDσ,(r1.frame_var _ (by decide)).trans hk,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,r1.seq r2,p2.1,(r2.frame_var _ (by decide)).trans p1.2.1,
    (r2.frame_var _ (by decide)).trans p1.2.2,p2.2⟩

end Lax263307Proofs.NativeComponentLoad

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

end Lax263307Proofs.NativeComponentControl

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

namespace Lax263307Proofs.NativeComponentTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic NativeMasks

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem load_segment (n D k h:ℕ) (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x:Fin n→ ℚ≥0) (hn:0< n) (hD:0< D) (hx:∀ v,Bounded (2^h) (x v:ℚ))
    (w:ℕ) (hw:NativeComponentDecision.wordHeight n D k h≤ w)
    (parts:List (Finset (Fin n))) (hparts:parts.length≤ n+1) (i:ℕ) (hi:i< parts.length)
    (hB:i+parts.length+12<2^w) (σ:Env)
    (hin:σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
      Prefix (encodeVector (fun v => (x v:ℚ))) "near.costs" σ∧ σ.vars "component.i"=i∧
      Prefix (parts.map mask) "separator.pieces" σ∧ n≤(σ.arrs "subset.bits").length∧
      n≤(σ.arrs "restrict.vertices").length∧ σ.vars "algorithm.D"=D∧ σ.vars "conditioning.k"=k∧
      3*n<(σ.arrs "lp.word").length∧ 3*n≤(σ.arrs "sum.input").length)
    (hcount:σ.vars "component.count"=parts.length)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=9):
    ∃ τ,Segment (2^w) (phases cfg) 1 (43*n+27+NativeComponentDecision.timeBound n h) σ τ∧
      NativeRestrictionRead.Data G (fun v => (x v:ℚ)) parts[i] τ∧
      τ.vars "component.mask"=mask parts[i]∧ τ.vars "component.i"=i∧
      τ.vars "component.target"=ComputedRounding.target (1/(D:ℚ)) (∑ v∈parts[i],(x v:ℚ))∧
      τ.vars "component.active"=(if (1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈parts[i],(x v:ℚ)) then 1 else 0)∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=10:=by
  obtain ⟨μ,r1,p1⟩:=NativeComponentLoad.command_spec n D k h G x hn hD hx w hw parts hparts i hi σ hin
  let τ:=μ.setVar "machine.phase" 10
  have r2:Run (2^w) (go 10) μ τ 2:=Run.assign (evalB_lit (show 10<2^w by omega))
  have ht:(Cond.lt (.var "component.i") (.var "component.count")).evalB (2^w) σ=some true:=by
    have hh:=evalB_condLt (value hin.2.2.2.1 (show i<2^w by omega)) (value hcount (show parts.length<2^w by omega))
    simpa only [hi,decide_true] using hh
  have run:Run (2^w) component σ τ (43*n+27+NativeComponentDecision.timeBound n h):=
    (Run.ite_true (d:=NativeComponentControl.finish 14) ht (r1.seq r2)).mono
      (by simp [Cond.size,Expr.size]; omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨9,by change 9<16; decide⟩ hp run,?_,?_,?_,?_,?_,
    (run.frame_var _ (by decide)).trans hr,by simp [τ]⟩
  · exact NativeRestrictionRead.frame r2 p1.1 (by intro s hs; simp [go,Com.warrs])
      (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl|rfl <;> decide)
  · simpa [τ] using p1.2.1
  · simpa [τ] using p1.2.2.1
  · simpa [τ] using p1.2.2.2.1
  · simpa [τ] using p1.2.2.2.2

theorem light_segment (B i:ℕ) (cfg:Config) (hB:i+12< B) (σ:Env)
    (ha:σ.vars "component.active"=0) (hi:σ.vars "component.i"=i)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=10):
    ∃ τ,Segment B (phases cfg) 1 10 σ τ∧ τ.vars "component.i"=i+1∧
      τ.vars "machine.running"=1∧ τ.vars "machine.phase"=9:=by
  obtain ⟨τ,rr,po⟩:=NativeComponentControl.advance_spec B i 9 hB σ hi
  have ht:(Cond.eq (.var "component.active") (.lit 1)).evalB B σ=some false:=
    evalB_condEq (value ha (by omega)) (evalB_lit (show 1< B by omega))
  have run:Run B (.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)) σ τ 10:=
    (Run.ite_false ht rr).mono (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨10,by change 10<16; decide⟩ hp run,po.1,
    (rr.frame_var _ (by decide)).trans hr,po.2⟩

end Lax263307Proofs.NativeComponentTrace

end

section

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

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

theorem light_iteration (n D k r fuel stride h:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (x:Fin n→ ℚ≥0)
    (parts:List (Finset (Fin n))) (A:Finset (Fin n))
    (extent:String→ ℕ) (front:List ℕ)
    (hn:0< n) (hD:0< D) (hx:∀ v,NativeSignedArithmetic.Bounded (2^h) (x v:ℚ))
    (w:ℕ) (hw:NativeComponentDecision.wordHeight n D k h≤ w)
    (hparts:parts.length≤ n+1) (i:ℕ) (hi:i< parts.length)
    (hB:i+parts.length+12<2^w)
    (hbits:n≤ extent "subset.bits") (hlabels:n≤ extent "restrict.vertices")
    (hlp:3*n< extent "lp.word") (hsum:3*n≤ extent "sum.input")
    (light:¬(1/(D:ℚ))*k/(4*(n:ℚ))<(∑ v∈parts[i],(x v:ℚ)))
    (U:Finset (Fin n)) (σ:Env)
    (hin:NativeCollectionTrace.At (Context (2^w) D k r fuel stride G x parts A extent front) i U σ):
    ∃ τ,Segment (2^w) (phases cfg) 2 (43*n+37+NativeComponentDecision.timeBound n h) σ τ∧
      NativeCollectionTrace.At (Context (2^w) D k r fuel stride G x parts A extent front) (i+1) U τ∧ NativeCollectionAnchor.Anchor σ τ:=by
  let hc:=hin.1
  obtain ⟨ν,load,hd,hm,hiν,ht,active,hr,hp⟩:=
    NativeComponentTrace.load_segment n D k h cfg G x hn hD hx w hw parts hparts i hi hB σ
      ⟨hc.order,hc.graph,hc.costs,hin.2.1,hc.pieces,
        by rw [hc.lengths]; exact hbits,by rw [hc.lengths]; exact hlabels,
        hc.denominator,hc.target,by rw [hc.lengths]; exact hlp,by rw [hc.lengths]; exact hsum⟩
      hc.count hin.2.2.2.1 hin.2.2.2.2
  have runLoad:=NativeMachineFrame.single_run load ⟨9,by change 9<16; decide⟩ hin.2.2.2.2
  change Run (2^w) component σ ν _ at runLoad
  have cν:=frame runLoad hc (by decide) (by decide)
  have unionν:ν.vars "component.union"=mask U:=
    (runLoad.frame_var _ (by decide)).trans hin.2.2.1
  have active0:ν.vars "component.active"=0:=by simpa only [if_neg light] using active
  obtain ⟨τ,advance,idx,running,phase⟩:=NativeComponentTrace.light_segment (2^w) i cfg (by omega) ν
    active0 hiν hr hp
  have runAdvance:=NativeMachineFrame.single_run advance ⟨10,by change 10<16; decide⟩ hp
  change Run (2^w) (.ite (.eq (.var "component.active") (.lit 1)) (go 11)
    (NativeComponentControl.advance 9)) ν τ _ at runAdvance
  have totalEq:(43*n+27+NativeComponentDecision.timeBound n h)+10=
    43*n+37+NativeComponentDecision.timeBound n h:=by omega
  refine ⟨τ,by simpa only [totalEq,Nat.reduceAdd] using NativeMachineSegment.append load advance,
    ⟨frame runAdvance cν (by decide) (by decide),idx,
      (runAdvance.frame_var _ (by decide)).trans unionν,running,phase⟩,
    NativeCollectionAnchor.frame (runLoad.seq runAdvance) (NativeCollectionAnchor.refl σ) (by decide) (by decide)⟩

end Lax263307Proofs.NativeCollectionContext

end

theorem solution:∀ (n D k r fuel stride h:Nat) (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (x:Fin n→ NNRat)
  (parts:List (Finset (Fin n))) (A:Finset (Fin n)) (extent:String→ Nat) (front:List Nat),
  Nat.lt ((0:Nat)) n→
    Nat.lt ((0:Nat)) D→
      (∀ (v:Fin n),
          Lax263307Proofs.NativeSignedArithmetic.Bounded
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) h)
            (@NNRat.cast Rat Rat.instNNRatCast (x v)))→
        ∀ (w:Nat),
          Nat.le (Lax263307Proofs.NativeComponentDecision.wordHeight n D k h) w→
            Nat.le (@List.length (Finset (Fin n)) parts)
                (Nat.add n
                  ((1:Nat)))→
              ∀ (i:Nat) (hi:Nat.lt i (@List.length (Finset (Fin n)) parts)),
                Nat.lt
                    (Nat.add
                      (Nat.add i (@List.length (Finset (Fin n)) parts))
                      ((12:Nat)))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  Nat.le n (extent "subset.bits")→
                    Nat.le n (extent "restrict.vertices")→
                      Nat.lt
                          (Nat.mul
                            ((3:Nat)) n)
                          (extent "lp.word")→
                        Nat.le
                            (Nat.mul
                              ((3:Nat)) n)
                            (extent "sum.input")→
                          Not
                              (@LT.lt Rat Rat.instLT
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                    (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                      (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                      (@Nat.cast Rat Rat.instNatCast D))
                                    (@Nat.cast Rat Rat.instNatCast k))
                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                    (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                    (@Nat.cast Rat Rat.instNatCast n)))
                                (∑
                                  v∈
                                    @GetElem.getElem (List (Finset (Fin n))) Nat (Finset (Fin n))
                                      (fun (as:List (Finset (Fin n))) (i:Nat) =>
                                        Nat.lt i (@List.length (Finset (Fin n)) as))
                                      (@List.instGetElemNatLtLength (Finset (Fin n))) parts i hi,
                                  @NNRat.cast Rat Rat.instNNRatCast (x v)))→
                            ∀ (U:Finset (Fin n)) (σ:Lax808846Proofs.Imp.Env),
                              @Lax263307Proofs.NativeCollectionTrace.At n
                                  (@Lax263307Proofs.NativeCollectionContext.Context n
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      ((2:Nat)) w)
                                    D k r fuel stride G inst x parts A extent front)
                                  i U σ→
                                ∃ (τ:Lax808846Proofs.Imp.Env),
                                  And
                                    (Lax263307Proofs.NativeMachineSegment.Segment
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        ((2:Nat)) w)
                                      (Lax263307Proofs.NativeCoreMachine.phases cfg)
                                      ((2:Nat))
                                      (Nat.add
                                        (Nat.add
                                          (Nat.mul
                                            ((43:Nat)) n)
                                          ((37:Nat)))
                                        (Lax263307Proofs.NativeComponentDecision.timeBound n h))
                                      σ τ)
                                    (And
                                      (@Lax263307Proofs.NativeCollectionTrace.At n
                                        (@Lax263307Proofs.NativeCollectionContext.Context n
                                          (@HPow.hPow Nat Nat Nat
                                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                            ((2:Nat)) w)
                                          D k r fuel stride G inst x parts A extent front)
                                        (Nat.add i
                                          ((1:Nat)))
                                        U τ)
                                      (Lax263307Proofs.NativeCollectionAnchor.Anchor σ τ)):= @Lax263307Proofs.NativeCollectionContext.light_iteration
