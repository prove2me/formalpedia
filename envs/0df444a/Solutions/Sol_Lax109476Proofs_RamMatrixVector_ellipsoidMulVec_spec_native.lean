-- Prove2me | solution 1 for Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:54:27.731202+00:00
-- url     : https://prove2.me/submissions/239c04b5-ca71-4c75-b06a-5c797e0d6293

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
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
theorem Lax109476Proofs.RamRational.multiplyFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  Nat.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
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
                      Lax109476Proofs.RamRational.multiplyFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (HAdd.hAdd
                        (HMul.hMul
                          ((36:Nat))
                          (HMul.hMul d₁ d₂).size)
                        ((64:Nat))):= @Lax109476Proofs.RamRational.multiplyFraction_spec_native
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.addFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  Nat.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
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

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.DeterminantBounds

theorem integer_ratio_num_den_bound (a b:ℤ) (hb:b ≠ 0):
    ((a:ℚ) / b).num.natAbs≤ a.natAbs∧
      ((a:ℚ) / b).den≤ b.natAbs:=by
  obtain ⟨c,hn,hd⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den a (d:=b) hb
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hd
    exact hb hd
  have hcpos:=Int.natAbs_pos.mpr hc
  have hna:a.natAbs=c.natAbs * ((a:ℚ) / b).num.natAbs:=by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hn
  have hda:b.natAbs=c.natAbs * ((a:ℚ) / b).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs hd
  constructor
  · rw [hna]
    exact Nat.le_mul_of_pos_left _ hcpos
  · rw [hda]
    exact Nat.le_mul_of_pos_left _ hcpos

end Lax109476Proofs.DeterminantBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem size_mul_le (a b:ℕ):Nat.size (a * b)≤ Nat.size a + Nat.size b:=by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

end Lax109476Proofs.RationalSizeBounds

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

theorem height_mul (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q * r) (B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q * r=((q.num * r.num:ℤ):ℚ) / ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    ring
  rw [he]
  simp only [Int.cast_mul,Int.cast_natCast]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.num) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn hd'
  exact ⟨hn.trans (Nat.mul_le_mul hq.1 hr.1),hd'.trans (Nat.mul_le_mul hq.2 hr.2)⟩

theorem height_add (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q + r) (2 * B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q + r=((q.num * r.den + r.num * q.den:ℤ):ℚ) /
      ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    field_simp
  rw [he]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.den + r.num * q.den) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  have hb:(q.num * r.den + r.num * q.den:ℤ).natAbs≤ 2 * B * C:=by
    calc
      _≤ (q.num * r.den:ℤ).natAbs + (r.num * q.den:ℤ).natAbs:=Int.natAbs_add_le _ _
      _=q.num.natAbs * r.den + r.num.natAbs * q.den:=by simp [Int.natAbs_mul]
      _≤ B * C + C * B:=Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _=_:=by ring
  refine ⟨hn.trans hb, ?_⟩
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hd'
  exact hd'.trans ((Nat.mul_le_mul hq.2 hr.2).trans (by nlinarith))

theorem height_sum {ι:Type*} (s:Finset ι) (f:ι→ ℚ) (B:ℕ)
    (hf:∀ i∈ s,Height (f i) B):
    Height (∑ i∈ s,f i) ((2 * B) ^ s.card):=by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using height_zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,pow_succ]
    have h:=height_add (f i) (∑ j∈ s,f j) B ((2 * B) ^ s.card)
      (hf i (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    convert h using 1
    ring

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem multiplyFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 64):=by
  apply (multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  change 36 * (d₁ * d₂).size + _ ≤ _
  omega

theorem addFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 96):=by
  apply (addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  change 36 * (d₁ * d₂).size + _ ≤ _
  omega

end Lax109476Proofs.RamPrimitiveBounds

end

section

namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding

theorem fractionValue_sign (s n d:ℕ) (hs:s≤ 1) (hd:0 < d):
    (if (fractionValue s n d).num < 0 then 1 else 0:ℕ) =
      if n=0 then 0 else s:=by
  have hscases:s=0∨ s=1:=by omega
  rcases hscases with rfl | rfl
  · have hq:0≤ fractionValue 0 n d:=by change (0:ℚ)≤ (n:ℚ) / d; positivity
    have hnum:=Rat.num_nonneg.mpr hq
    simp [not_lt.mpr hnum]
  · by_cases hz:n=0
    · simp [fractionValue,hz]
    · have hq:fractionValue 1 n d < 0:=by
        change -(n:ℚ) / d < 0
        have hp:(0:ℚ) < (n:ℚ) / d:=by positivity
        rw [neg_div]
        linarith
      have hnum:(fractionValue 1 n d).num < 0:=by
        rw [← not_le,Rat.num_nonneg]
        exact not_le_of_gt hq
      simp [hz,hnum]

end Lax109476Proofs.RamEncoding

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

def RightOutput (q:ℚ) (σ:Env):Prop:=
  σ.vars "right.s"=rationalSign q∧ σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den

theorem loadRight_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadRight a)
      (fun _ τ => RightOutput qs[i] τ) 9:=by
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
    (refine let c0:Env→ Prop:=RightOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat:= @List.getD Nat (Env.arrs σ c3) (Env.vars σ "vec.i") ((0:Nat)); let c5:Env:=Env.setVar σ "right.s" c4; let c6:String:=c2 ".n"; let c7:Nat:=Env.vars c5 "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs c5 c6) c7 ((0:Nat)); let c9:Env:=Env.setVar c5 "right.n" c8; let c10:String:=c2 ".d"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "right.d" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Expr:=Expr.get c3 (Expr.var "vec.i"); let c17:Nat:=c15 (Expr.size c16); let c18:Expr:=Expr.get c6 (Expr.var "vec.i"); let c19:Nat:=c15 (Expr.size c18); let c20:Expr:=Expr.get c10 (Expr.var "vec.i"); let c21:Nat:=c15 (Expr.size c20); let c22:Nat:=c14 c19 c21; let c23:Com:=Com.assign "right.n" c18; let c24:Com:=Com.assign "right.d" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (loadRight a) σ σ' ((9:Nat))) (c1 σ')) c13 (@And.intro (Run B (loadRight a) σ c13 ((9:Nat))) (c1 c13) (RunStep.mono B (loadRight a) σ c13 (c14 c17 c22) ((9:Nat)) (RunStep.seq B (Com.assign "right.s" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "right.s" c16 c4 (RunStep.eval_get B σ c3 (Expr.var "vec.i") (Env.vars σ "vec.i") (RunStep.eval_var B σ "vec.i" (?nAX_g3959_0_0_0)) (?nAX_g3959_0_0_1) ?_)) (RunStep.seq B c23 c24 c5 c9 c13 c19 c21 (RunStep.assign B c5 "right.n" c18 c8 (RunStep.eval_get B c5 c6 (Expr.var "vec.i") c7 (RunStep.eval_var B c5 "vec.i" (?nAX_g3959_0_0_2)) (?nAX_g3959_0_0_3) ?_)) (RunStep.assign B c9 "right.d" c20 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g3959_0_0_4)) (?nAX_g3959_0_0_5) ?_)))) (?nAX_g3959_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3959_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3959_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightOutput]

theorem loadRight_frame_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadRight a)
      (fun σ τ => RightOutput qs[i] τ∧ τ.vars "vec.i"=i∧ τ.arrs=σ.arrs∧
        τ.vars "left.s"=σ.vars "left.s" ∧ τ.vars "left.n"=σ.vars "left.n" ∧
        τ.vars "left.d"=σ.vars "left.d") 9:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=loadRight_spec B a qs i hi hB hiB hn hd σ hσ
  refine ⟨τ,hr,hτ, (hr.frame_var "vec.i" (by simp [loadRight,Com.wvars])).trans hσ.2,
    ?_,hr.frame_var "left.s" (by simp [loadRight,Com.wvars]),
    hr.frame_var "left.n" (by simp [loadRight,Com.wvars]),
    hr.frame_var "left.d" (by simp [loadRight,Com.wvars])⟩
  funext b
  exact hr.frame_arr b (by simp [loadRight,Com.warrs])

theorem storeReduced_spec (B:ℕ) (a:String) (qs:List ℚ) (q:ℚ) (i:ℕ)
    (hi:i < qs.length) (hB:1 < B) (hiB:i < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i∧ FractionOutput q σ)
      (storeReduced a) (fun _ τ => Represents a (qs.set i q) τ) 13:=by
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσi,hv,hratn,hratd,hrats⟩
  have hnB:σ.vars "rat.n" < B:=hratn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hratd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hrats.trans_lt hB
  have hsl:i < (σ.arrs (a ++ ".s")).length:=by rw [hσs,List.length_map]; exact hi
  have hnl:i < (σ.arrs (a ++ ".n")).length:=by rw [hσn,List.length_map]; exact hi
  have hdl:i < (σ.arrs (a ++ ".d")).length:=by rw [hσd,List.length_map]; exact hi
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  have hns:=Ne.symm hsn
  have hds:=Ne.symm hsd
  have hdn:=Ne.symm hnd
  have hsign:=RamEncoding.fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hrats (hratd ▸ q.den_pos)
  rw [hv] at hsign
  change rationalSign q=_ at hsign
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=Represents a (@List.set Rat qs i q); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced a) σ σ' ((13:Nat))) (c3 σ'); let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c6:String:=c5 ".s"; let c7:Nat→ Env:=Env.setArr σ c6 (Env.vars σ "vec.i"); let c8:Env:=c7 ((0:Nat)); let c9:String:=c5 ".n"; let c10:String→ Nat:=Env.vars c8; let c11:Nat:=c10 "vec.i"; let c12:Nat:=c10 "rat.n"; let c13:Env:=Env.setArr c8 c9 c11 c12; let c14:String:=c5 ".d"; let c15:String→ Nat:=Env.vars c13; let c16:Nat:=c15 "vec.i"; let c17:Nat:=c15 "rat.d"; let c18:Env:=Env.setArr c13 c14 c16 c17; let c19:Nat→ Nat→ Nat:=Nat.add; let c20:Nat→ Nat:=c19 ((1:Nat)); let c21:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c22:Nat→ Nat:=c19 (c20 (Cond.size c21)); let c23:Nat→ Nat:=c19 (c20 (Expr.size (Expr.var "vec.i"))); let c24:Nat:=c23 (Expr.size (Expr.lit ((0:Nat)))); let c25:Nat:=c22 c24; let c26:Nat:=c23 (Expr.size (Expr.var "rat.n")); let c27:Nat:=c23 (Expr.size (Expr.var "rat.d")); let c28:Nat:=c19 c26 c27; let c29:Expr→ Com:=Com.store c6 (Expr.var "vec.i"); let c30:Com:=c29 (Expr.lit ((0:Nat))); let c31:Com:=c29 (Expr.var "rat.s"); let c32:Com:=Com.store c9 (Expr.var "vec.i") (Expr.var "rat.n"); let c33:Com:=Com.store c14 (Expr.var "vec.i") (Expr.var "rat.d"); let c34:Env:=c7 (Env.vars σ "rat.s"); let c35:String→ Nat:=Env.vars c34; let c36:Nat:=c35 "vec.i"; let c37:Nat:=c35 "rat.n"; let c38:Env:=Env.setArr c34 c9 c36 c37; let c39:String→ Nat:=Env.vars c38; let c40:Nat:=c39 "vec.i"; let c41:Nat:=c39 "rat.d"; let c42:Env:=Env.setArr c38 c14 c40 c41; let c43:Nat:=c23 (Expr.size (Expr.var "rat.s")); let c44:Nat:=c22 c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c18 (@And.intro (Run B (storeReduced a) σ c18 ((13:Nat))) (c3 c18) (RunStep.mono B (storeReduced a) σ c18 (c19 c25 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c8 c18 c25 c28 (RunStep.ite_true B c21 c30 c31 σ c8 c24 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_0)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.lit ((0:Nat))) (Env.vars σ "vec.i") ((0:Nat)) (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_2)) (?nAX_g3962_0_0_3))) (RunStep.seq B c32 c33 c8 c13 c18 c26 c27 (RunStep.store B c8 c9 (Expr.var "vec.i") (Expr.var "rat.n") c11 c12 (RunStep.eval_var B c8 "vec.i" (?nAX_g3962_0_0_4)) (RunStep.eval_var B c8 "rat.n" (?nAX_g3962_0_0_5)) (?nAX_g3962_0_0_6)) (RunStep.store B c13 c14 (Expr.var "vec.i") (Expr.var "rat.d") c16 c17 (RunStep.eval_var B c13 "vec.i" (?nAX_g3962_0_0_7)) (RunStep.eval_var B c13 "rat.d" (?nAX_g3962_0_0_8)) (?nAX_g3962_0_0_9)))) (?nAX_g3962_0_0_10)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c42 (@And.intro (Run B (storeReduced a) σ c42 ((13:Nat))) (c3 c42) (RunStep.mono B (storeReduced a) σ c42 (c19 c44 c28) ((13:Nat)) (RunStep.seq B (Com.ite c21 c30 c31) (Com.seq c32 c33) σ c34 c42 c44 c28 (RunStep.ite_false B c21 c30 c31 σ c34 c43 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3962_0_0_11)) hcase) (RunStep.store B σ c6 (Expr.var "vec.i") (Expr.var "rat.s") (Env.vars σ "vec.i") (Env.vars σ "rat.s") (RunStep.eval_var B σ "vec.i" (?nAX_g3962_0_0_12)) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g3962_0_0_13))) (RunStep.seq B c32 c33 c34 c38 c42 c26 c27 (RunStep.store B c34 c9 (Expr.var "vec.i") (Expr.var "rat.n") c36 c37 (RunStep.eval_var B c34 "vec.i" (?nAX_g3962_0_0_14)) (RunStep.eval_var B c34 "rat.n" (?nAX_g3962_0_0_15)) (?nAX_g3962_0_0_16)) (RunStep.store B c38 c14 (Expr.var "vec.i") (Expr.var "rat.d") c40 c41 (RunStep.eval_var B c38 "vec.i" (?nAX_g3962_0_0_17)) (RunStep.eval_var B c38 "rat.d" (?nAX_g3962_0_0_18)) (?nAX_g3962_0_0_19)))) (?nAX_g3962_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3962_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3962_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Represents,Env.setArr,List.map_set]

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem spec_with_fields {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars) (ha:c.warrs=[]):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  refine ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx), ?_⟩
  funext a
  exact hr.frame_arr a (by simp [ha])

end Lax109476Proofs.RamFrame

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamPrimitiveBounds RamFrame RationalArithmeticBounds

def prefixValue (xs ys:List ℚ) (k:ℕ):ℚ:=
  ∑ i∈ Finset.range k,xs.getD i 0 * ys.getD i 0

theorem prefix_zero (xs ys:List ℚ):prefixValue xs ys 0=0:=by simp [prefixValue]

theorem prefix_succ (xs ys:List ℚ) (k:ℕ):
    prefixValue xs ys (k + 1)=prefixValue xs ys k + xs.getD k 0 * ys.getD k 0:=by
  simp [prefixValue,Finset.sum_range_succ]

theorem cap_ge (n H:ℕ) (hH:1≤ H):H * H≤ cap n H∧ H≤ cap n H:=by
  have hb:1≤ 2 * (H * H):=by nlinarith
  have hp:=le_self_pow hb (by omega:n + 1 ≠ 0)
  change H * H≤ (2 * (H * H)) ^ (n + 1)∧ H≤ (2 * (H * H)) ^ (n + 1)
  constructor <;> nlinarith

theorem prefix_height (xs ys:List ℚ) (n H k:ℕ) (hH:1≤ H)
    (hx:xs.length=n) (hy:ys.length=n) (hk:k≤ n)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H):
    Height (prefixValue xs ys k) (cap n H):=by
  have hf:∀ i∈ Finset.range k,Height (xs.getD i 0 * ys.getD i 0) (H * H):=by
    intro i hi
    have hix:i < xs.length:=by have h:=Finset.mem_range.mp hi; omega
    have hiy:i < ys.length:=by have h:=Finset.mem_range.mp hi; omega
    have hxq:xs.getD i 0=xs[i]:=by simp [List.getD_eq_getElem?_getD,hix]
    have hyq:ys.getD i 0=ys[i]:=by simp [List.getD_eq_getElem?_getD,hiy]
    rw [hxq,hyq]
    exact height_mul _ _ H H (hxs _ (List.getElem_mem hix)) (hys _ (List.getElem_mem hiy))
  have hs:=height_sum (Finset.range k) (fun i => xs.getD i 0 * ys.getD i 0) (H * H) hf
  simp only [Finset.card_range] at hs
  exact height_mono _ hs (Nat.pow_le_pow_right (by nlinarith) (by omega))

def DotOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "dot.s") (σ.vars "dot.n") (σ.vars "dot.d")=q∧
    σ.vars "dot.n"=q.num.natAbs∧ σ.vars "dot.d"=q.den∧ σ.vars "dot.s" ≤ 1

set_option maxHeartbeats 0 in
theorem addToAccumulator_spec (B M i:ℕ) (q r:ℚ)
    (hB:2 * M ^ 2 + 3 < B) (hq:Height q M) (hr:Height r M)
    (hi:i + 1 < B):
    Spec B (fun σ => DotOutput q σ∧ FractionOutput r σ∧ σ.vars "vec.i"=i)
      addToAccumulator
      (fun σ τ => DotOutput (q + r) τ∧ τ.vars "vec.i"=i + 1∧
        τ.vars "vec.n"=σ.vars "vec.n" ∧ τ.arrs=σ.arrs)
      (72 * M.size + 128):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hqσ,hrσ,hiσ⟩
  have hqval:=hqσ.1
  have hrval:=hrσ.1
  have hadd:=addFraction_uniform_spec B M (σ.vars "dot.s") q.num.natAbs q.den
    (σ.vars "rat.s") r.num.natAbs r.den hB hqσ.2.2.2 hrσ.2.2.2
    hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
  have hframe:=spec_with_fields ["vec.i", "vec.n"] hadd
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
        simp [addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
          RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
    (by simp [addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
          RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  have hqnum:=hqσ.2.1
  have hqden:=hqσ.2.2.1
  have hrnum:=hrσ.2.1
  have hrden:=hrσ.2.2.1
  have hqs:=hqσ.2.2.2.trans_lt h1
  have hrs:=hrσ.2.2.2.trans_lt h1
  have hqn:=hq.1.trans_lt hM
  have hqd:=hq.2.trans_lt hM
  have hrn:=hr.1.trans_lt hM
  have hrd:=hr.2.trans_lt hM
  have hsum:=height_add q r M M hq hr
  have hsumN:(q + r).num.natAbs < B:=hsum.1.trans_lt (by nlinarith)
  have hsumD:(q + r).den < B:=hsum.2.trans_lt (by nlinarith)
  clear hadd
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "right.d" c2; let c4:Nat:=Env.vars c3 "dot.s"; let c5:Env:=Env.setVar c3 "left.s" c4; let c6:Nat:=Env.vars c5 "dot.n"; let c7:Env:=Env.setVar c5 "left.n" c6; let c8:Nat:=Env.vars c7 "dot.d"; let c9:Env:=Env.setVar c7 "left.d" c8; let c10:Env→ Nat→ Prop:=Run B addFraction c9; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 (Nat.mul ((72:Nat)) (Nat.size M)); let c13:Nat:=c12 ((96:Nat)); let c14:Rat→ Rat→ Rat:= @HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd); let c15:Env→ Prop:=FractionOutput (c14 (fractionValue (Env.vars σ "dot.s") (Int.natAbs (Rat.num q)) (Rat.den q)) (fractionValue (Env.vars σ "rat.s") (Int.natAbs (Rat.num r)) (Rat.den r))); let c16:Env→ Env→ Prop:=FieldsAgree (@List.cons String "vec.i" (@List.cons String "vec.n" (@List.nil String))); let c17:Env→ Prop:=c16 c9; let c18:String→ List Nat:=Env.arrs c9; let c19:Env→ Prop:=fun (σ':Env) => And (c10 σ' c13) (And (c15 σ') (And (c17 σ') (@Eq (String→ List Nat) (Env.arrs σ') c18))); let c20:Nat:=c12 ((128:Nat)); let c21:Env→ Prop:=DotOutput (c14 q r); let c22:Nat:=c11 i ((1:Nat)); let c23:Env→ Prop:=(fun (σ_1 τ:Env) => And (c21 τ) (And (@Eq Nat (Env.vars τ "vec.i") c22) (And (@Eq Nat (Env.vars τ "vec.n") (Env.vars σ_1 "vec.n")) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))))) σ; let c24:Env→ Prop:=fun (σ':Env) => And (Run B addToAccumulator σ σ' c20) (c23 σ'); let c25:Env→ Prop:=fractionInputs (Env.vars σ "dot.s") (Int.natAbs (Rat.num q)) (Rat.den q) (Env.vars σ "rat.s") (Int.natAbs (Rat.num r)) (Rat.den r); let c26:Nat→ Nat:=c11 ((1:Nat)); let c27:Nat:=c26 (Expr.size (Expr.var "rat.s")); let c28:Nat→ Nat:=c11 c27; let c29:Nat:=c26 (Expr.size (Expr.var "rat.n")); let c30:Nat→ Nat:=c11 c29; let c31:Nat:=c26 (Expr.size (Expr.var "rat.d")); let c32:Nat→ Nat:=c11 c31; let c33:Nat:=c26 (Expr.size (Expr.var "dot.s")); let c34:Nat:=c26 (Expr.size (Expr.var "dot.n")); let c35:Nat:=c26 (Expr.size (Expr.var "dot.d")); let c36:Expr:=Expr.add (Expr.var "vec.i") (Expr.lit ((1:Nat))); let c37:Nat:=c26 (Expr.size c36); let c38:Nat:=c32 c37; let c39:Nat:=c30 c38; let c40:Nat:=c28 c39; let c41:Nat:=c11 c13 c40; let c42:Nat:=c11 c35 c41; let c43:Nat:=c11 c34 c42; let c44:Nat:=c11 c33 c43; let c45:Nat:=c32 c44; let c46:Nat:=c30 c45; let c47:Com:=Com.assign "vec.i" c36; let c48:Com:=Com.seq (Com.assign "dot.d" (Expr.var "rat.d")) c47; let c49:Com:=Com.seq (Com.assign "dot.n" (Expr.var "rat.n")) c48; let c50:Com:=Com.seq (Com.assign "dot.s" (Expr.var "rat.s")) c49; let c51:Com:=Com.seq addFraction c50; let c52:Com:=Com.seq (Com.assign "left.d" (Expr.var "dot.d")) c51; let c53:Com:=Com.seq (Com.assign "left.n" (Expr.var "dot.n")) c52; let c54:Com:=Com.seq (Com.assign "left.s" (Expr.var "dot.s")) c53; let c55:Com:=Com.seq (Com.assign "right.d" (Expr.var "rat.d")) c54; @Exists.casesOn Env c19 (fun (x:@Exists Env c19) => @Exists Env c24) (RunStep.use B c25 addFraction (fun (σ_1 τ:Env) => And (c15 τ) (And (c16 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c13 hframe c9 ?_) fun (w:Env) (h:And (c10 w c13) (And (c15 w) (And (c17 w) (@Eq (String→ List Nat) (Env.arrs w) c18)))) => let c0_1:Prop:=And (c15 w) (And (c17 w) (@Eq (String→ List Nat) (Env.arrs w) c18)); let c1_1:Nat:=Env.vars (Env.setVar w "dot.s" (Env.vars w "rat.s")) "rat.n"; let c2_1:Env:=Env.setVar (Env.setVar w "dot.s" (Env.vars w "rat.s")) "dot.n" c1_1; let c3_1:Nat:=Env.vars c2_1 "rat.d"; let c4_1:Env:=Env.setVar c2_1 "dot.d" c3_1; let c5_1:Nat:=Env.vars c4_1 "vec.i"; let c6_1:Nat:=c11 c5_1 ((1:Nat)); let c7_1:Env:=Env.setVar c4_1 "vec.i" c6_1; let c8_1:String→ Nat:=Env.vars c7_1; @And.casesOn (c10 w c13) c0_1 (fun (x:And (c10 w c13) c0_1) => @Exists Env c24) h fun (left:c10 w c13) (right:c0_1) => @Exists.intro Env c24 c7_1 (@And.intro (Run B addToAccumulator σ c7_1 c20) (c23 c7_1) (RunStep.mono B addToAccumulator σ c7_1 (c28 c46) c20 (RunStep.seq B (Com.assign "right.s" (Expr.var "rat.s")) (Com.seq (Com.assign "right.n" (Expr.var "rat.n")) c55) σ (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c7_1 c27 c46 (RunStep.assign B σ "right.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hrs)) (RunStep.seq B (Com.assign "right.n" (Expr.var "rat.n")) c55 (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c1 c7_1 c29 c45 (RunStep.assign B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g4176_0_0_0))) (RunStep.seq B (Com.assign "right.d" (Expr.var "rat.d")) c54 c1 c3 c7_1 c31 c44 (RunStep.assign B c1 "right.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g4176_0_0_1))) (RunStep.seq B (Com.assign "left.s" (Expr.var "dot.s")) c53 c3 c5 c7_1 c33 c43 (RunStep.assign B c3 "left.s" (Expr.var "dot.s") c4 (RunStep.eval_var B c3 "dot.s" (?nAX_g4176_0_0_2))) (RunStep.seq B (Com.assign "left.n" (Expr.var "dot.n")) c52 c5 c7 c7_1 c34 c42 (RunStep.assign B c5 "left.n" (Expr.var "dot.n") c6 (RunStep.eval_var B c5 "dot.n" (?nAX_g4176_0_0_3))) (RunStep.seq B (Com.assign "left.d" (Expr.var "dot.d")) c51 c7 c9 c7_1 c35 c41 (RunStep.assign B c7 "left.d" (Expr.var "dot.d") c8 (RunStep.eval_var B c7 "dot.d" (?nAX_g4176_0_0_4))) (RunStep.seq B addFraction c50 c9 w c7_1 c13 c40 left (RunStep.seq B (Com.assign "dot.s" (Expr.var "rat.s")) c49 w (Env.setVar w "dot.s" (Env.vars w "rat.s")) c7_1 c27 c39 (RunStep.assign B w "dot.s" (Expr.var "rat.s") (Env.vars w "rat.s") (RunStep.eval_var B w "rat.s" ?_)) (RunStep.seq B (Com.assign "dot.n" (Expr.var "rat.n")) c48 (Env.setVar w "dot.s" (Env.vars w "rat.s")) c2_1 c7_1 c29 c38 (RunStep.assign B (Env.setVar w "dot.s" (Env.vars w "rat.s")) "dot.n" (Expr.var "rat.n") c1_1 (RunStep.eval_var B (Env.setVar w "dot.s" (Env.vars w "rat.s")) "rat.n" ?_)) (RunStep.seq B (Com.assign "dot.d" (Expr.var "rat.d")) c47 c2_1 c4_1 c7_1 c31 c37 (RunStep.assign B c2_1 "dot.d" (Expr.var "rat.d") c3_1 (RunStep.eval_var B c2_1 "rat.d" ?_)) (RunStep.assign B c4_1 "vec.i" c36 c6_1 (RunStep.eval_add B c4_1 (Expr.var "vec.i") (Expr.lit ((1:Nat))) c5_1 ((1:Nat)) (RunStep.eval_var B c4_1 "vec.i" ?_) (RunStep.eval_lit B ((1:Nat)) c4_1 h1) ?_)))))))))))) (?nAX_g4176_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4176_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4176_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4176_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4176_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4176_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4176_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hframe
  all_goals simp_all [DotOutput,FractionOutput,FieldsAgree,fractionInputs]
  all_goals first | omega | aesop

theorem prefix_ofFn (n:ℕ) (x y:Fin n→ ℚ):
    prefixValue (List.ofFn x) (List.ofFn y) n=∑ i,x i * y i:=by
  rw [Finset.sum_fin_eq_sum_range]
  unfold prefixValue
  apply Finset.sum_congr rfl
  intro i hi
  have hin:=Finset.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD,hin]

end Lax109476Proofs.RamDotProduct

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamMatrixRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamRational RamPrimitiveBounds RamDotProduct RationalArithmeticBounds

theorem loadRowLeft_spec (B base i:ℕ) (a:String) (qs:List ℚ) (hi:i < qs.length)
    (hB:1 < B) (hiB:base + i < B)
    (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Slice a qs base σ∧ σ.vars "row.base"=base∧ σ.vars "vec.i"=i)
      (loadRowLeft a) (fun _ τ => LeftOutput qs[i] τ) 15:=by
  rintro σ ⟨⟨hsl,hnl,hdl,hsg,hng,hdg⟩,hbase,hidx⟩
  have hsB:=(rationalSign_le_one qs[i]).trans_lt hB
  have hbaseB:base < B:=by omega
  have hidxB:i < B:=by omega
  have hsl':base + i < (σ.arrs (a ++ ".s")).length:=by omega
  have hnl':base + i < (σ.arrs (a ++ ".n")).length:=by omega
  have hdl':base + i < (σ.arrs (a ++ ".d")).length:=by omega
  have hs:=hsg i hi
  have hn':=hng i hi
  have hd':=hdg i hi
  clear hsg hng hdg
  (expose_names;
    (refine let c0:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) qs i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a; let c3:String:=c2 ".s"; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 (Env.vars σ "row.base") (Env.vars σ "vec.i"); let c6:Nat:= @List.getD Nat (Env.arrs σ c3) c5 ((0:Nat)); let c7:Env:=Env.setVar σ "left.s" c6; let c8:String:=c2 ".n"; let c9:String→ Nat:=Env.vars c7; let c10:Nat:=c9 "row.base"; let c11:Nat:=c9 "vec.i"; let c12:Nat:=c4 c10 c11; let c13:Nat:= @List.getD Nat (Env.arrs c7 c8) c12 ((0:Nat)); let c14:Env:=Env.setVar c7 "left.n" c13; let c15:String:=c2 ".d"; let c16:String→ Nat:=Env.vars c14; let c17:Nat:=c16 "row.base"; let c18:Nat:=c16 "vec.i"; let c19:Nat:=c4 c17 c18; let c20:Nat:= @List.getD Nat (Env.arrs c14 c15) c19 ((0:Nat)); let c21:Env:=Env.setVar c14 "left.d" c20; let c22:Nat→ Nat:=c4 ((1:Nat)); let c23:Expr:=Expr.get c3 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")); let c24:Nat:=c22 (Expr.size c23); let c25:Expr:=Expr.get c8 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")); let c26:Nat:=c22 (Expr.size c25); let c27:Expr:=Expr.get c15 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")); let c28:Nat:=c22 (Expr.size c27); let c29:Nat:=c4 c26 c28; let c30:Com:=Com.assign "left.n" c25; let c31:Com:=Com.assign "left.d" c27; @Exists.intro Env (fun (σ':Env) => And (Run B (loadRowLeft a) σ σ' ((15:Nat))) (c1 σ')) c21 (@And.intro (Run B (loadRowLeft a) σ c21 ((15:Nat))) (c1 c21) (RunStep.mono B (loadRowLeft a) σ c21 (c4 c24 c29) ((15:Nat)) (RunStep.seq B (Com.assign "left.s" c23) (Com.seq c30 c31) σ c7 c21 c24 c29 (RunStep.assign B σ "left.s" c23 c6 (RunStep.eval_get B σ c3 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")) c5 (RunStep.eval_add B σ (Expr.var "row.base") (Expr.var "vec.i") (Env.vars σ "row.base") (Env.vars σ "vec.i") (RunStep.eval_var B σ "row.base" (?nAX_g4188_0_0_0)) (RunStep.eval_var B σ "vec.i" (?nAX_g4188_0_0_1)) (?nAX_g4188_0_0_2)) (?nAX_g4188_0_0_3) ?_)) (RunStep.seq B c30 c31 c7 c14 c21 c26 c28 (RunStep.assign B c7 "left.n" c25 c13 (RunStep.eval_get B c7 c8 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")) c12 (RunStep.eval_add B c7 (Expr.var "row.base") (Expr.var "vec.i") c10 c11 (RunStep.eval_var B c7 "row.base" (?nAX_g4188_0_0_4)) (RunStep.eval_var B c7 "vec.i" (?nAX_g4188_0_0_5)) (?nAX_g4188_0_0_6)) (?nAX_g4188_0_0_7) ?_)) (RunStep.assign B c14 "left.d" c27 c20 (RunStep.eval_get B c14 c15 (Expr.add (Expr.var "row.base") (Expr.var "vec.i")) c19 (RunStep.eval_add B c14 (Expr.var "row.base") (Expr.var "vec.i") c17 c18 (RunStep.eval_var B c14 "row.base" (?nAX_g4188_0_0_8)) (RunStep.eval_var B c14 "vec.i" (?nAX_g4188_0_0_9)) (?nAX_g4188_0_0_10)) (?nAX_g4188_0_0_11) ?_)))) (?nAX_g4188_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4188_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4188_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftOutput]

theorem multiplyRowAt_spec (B M base i:ℕ) (a b:String) (xs ys:List ℚ)
    (hix:i < xs.length) (hiy:i < ys.length) (hiB:base + i < B)
    (hB:2 * M ^ 2 + 3 < B) (hx:Height xs[i] M) (hy:Height ys[i] M):
    Spec B (fun σ => Slice a xs base σ∧ Represents b ys σ∧
        σ.vars "row.base"=base∧ σ.vars "vec.i"=i)
      (multiplyRowAt a b) (fun _ τ => FractionOutput (xs[i] * ys[i]) τ)
      (72 * M.size + 88):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hii:i < B:=by omega
  rintro σ ⟨hσx,hσy,hσbase,hσi⟩
  have hload:=spec_with_fields ["vec.i"]
    (loadRowLeft_spec B base i a xs hix h1 hiB (hx.1.trans_lt hM) (hx.2.trans_lt hM))
    (by intro x hx; simp at hx; subst x; simp [loadRowLeft,Com.wvars])
    (by simp [loadRowLeft,Com.warrs])
  obtain ⟨τ,hr₁,hτx,hτf,hτa⟩:=hload σ ⟨hσx,hσbase,hσi⟩
  have hτy:Represents b ys τ:=by simpa only [Represents,hτa] using hσy
  have hτi:τ.vars "vec.i"=i:=(hτf _ (by simp)).trans hσi
  obtain ⟨υ,hr₂,hυy,hυi,hυa,hυs,hυn,hυd⟩:=loadRight_frame_spec B b ys i hiy h1 hii
    (hy.1.trans_lt hM) (hy.2.trans_lt hM) τ ⟨hτy,hτi⟩
  have hυx:LeftOutput xs[i] υ:=by simpa only [LeftOutput,hυs,hυn,hυd] using hτx
  obtain ⟨ρ,hr₃,hρ⟩:=multiplyFraction_uniform_spec B M
    (rationalSign xs[i]) xs[i].num.natAbs xs[i].den
    (rationalSign ys[i]) ys[i].num.natAbs ys[i].den hB
    (rationalSign_le_one _) (rationalSign_le_one _) hx.1 hx.2 hy.1 hy.2 xs[i].den_pos ys[i].den_pos
    υ ⟨hυx.1,hυx.2.1,hυx.2.2,hυy.1,hυy.2.1,hυy.2.2⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  simpa only [canonical_fractionValue] using hρ

def rowFields:List String:= ["dot.s", "dot.n", "dot.d", "vec.i", "vec.n", "row.base"]

theorem multiplyRowAt_frame_spec (B M base i:ℕ) (a b:String) (xs ys:List ℚ)
    (hix:i < xs.length) (hiy:i < ys.length) (hiB:base + i < B)
    (hB:2 * M ^ 2 + 3 < B) (hx:Height xs[i] M) (hy:Height ys[i] M):
    Spec B (fun σ => Slice a xs base σ∧ Represents b ys σ∧
        σ.vars "row.base"=base∧ σ.vars "vec.i"=i)
      (multiplyRowAt a b) (fun σ τ => FractionOutput (xs[i] * ys[i]) τ∧
        FieldsAgree rowFields σ τ∧ τ.arrs=σ.arrs) (72 * M.size + 88):=by
  apply spec_with_fields rowFields
    (multiplyRowAt_spec B M base i a b xs ys hix hiy hiB hB hx hy)
  · intro x hx
    simp [rowFields] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [multiplyRowAt,loadRowLeft,loadRight,multiplyFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars]
  · simp [multiplyRowAt,loadRowLeft,loadRight,multiplyFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs]

def RowInvariant (a b:String) (xs ys:List ℚ) (base n:ℕ) (σ:Env):Prop:=
  Slice a xs base σ∧ Represents b ys σ∧ σ.vars "vec.i" ≤ n∧
    σ.vars "vec.n"=n∧ σ.vars "row.base"=base∧
    DotOutput (prefixValue xs ys (σ.vars "vec.i")) σ

theorem rowDotStep_spec (B base n H:ℕ) (a b:String) (xs ys:List ℚ)
    (hx:xs.length=n) (hy:ys.length=n) (hH:1≤ H)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H)
    (hnB:base + n < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => RowInvariant a b xs ys base n σ∧ σ.vars "vec.i" < n)
      (rowDotStep a b)
      (fun σ τ => RowInvariant a b xs ys base n τ∧ τ.vars "vec.i"=σ.vars "vec.i" + 1)
      (144 * (cap n H).size + 216):=by
  rintro σ ⟨⟨hσx,hσy,hσin,hσn,hσbase,hσq⟩,hσi⟩
  let i:=σ.vars "vec.i"
  have hix:i < xs.length:=by dsimp [i]; omega
  have hiy:i < ys.length:=by dsimp [i]; omega
  have hcap:=cap_ge n H hH
  have hxq:=hxs _ (List.getElem_mem hix)
  have hyq:=hys _ (List.getElem_mem hiy)
  have hprefix:=prefix_height xs ys n H i hH hx hy hσin hxs hys
  have hproduct:=height_mono _ (height_mul _ _ H H hxq hyq) hcap.1
  obtain ⟨τ,hr₁,hτp,hτf,hτa⟩:=multiplyRowAt_frame_spec B (cap n H) base i a b xs ys hix hiy
    (by dsimp [i]; omega) hB (height_mono _ hxq hcap.2) (height_mono _ hyq hcap.2)
    σ ⟨hσx,hσy,hσbase,rfl⟩
  have hτi:τ.vars "vec.i"=i:=hτf _ (by simp [rowFields])
  have hτn:τ.vars "vec.n"=σ.vars "vec.n" :=hτf _ (by simp [rowFields])
  have hτbase:τ.vars "row.base"=base:=(hτf _ (by simp [rowFields])).trans hσbase
  have hτq:DotOutput (prefixValue xs ys i) τ:=by
    simpa only [DotOutput,hτf "dot.s" (by simp [rowFields]),
      hτf "dot.n" (by simp [rowFields]),hτf "dot.d" (by simp [rowFields])] using hσq
  obtain ⟨υ,hr₂,hυq,hυi,hυn,hυa⟩:=addToAccumulator_spec B (cap n H) i
    (prefixValue xs ys i) (xs[i] * ys[i]) hB hprefix hproduct
    (by dsimp [i]; omega) τ ⟨hτq,hτp,hτi⟩
  have hυbase:υ.vars "row.base"=base:=
    (hr₂.frame_var "row.base" (by
      simp [addToAccumulator,addFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])).trans hτbase
  have hsum:prefixValue xs ys (i + 1)=prefixValue xs ys i + xs[i] * ys[i]:=by
    rw [prefix_succ]
    simp [List.getD_eq_getElem?_getD,hix,hiy]
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_,hυbase, ?_⟩,hυi⟩
  · simpa only [Slice,hυa,hτa] using hσx
  · simpa only [Represents,hυa,hτa] using hσy
  · rw [hυi]; dsimp [i]; omega
  · rw [hυn,hτn,hσn]
  · rw [hυi,hsum]; exact hυq

theorem rowDotProduct_spec (B base n H:ℕ) (a b:String) (xs ys:List ℚ)
    (hx:xs.length=n) (hy:ys.length=n) (hH:1≤ H)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H)
    (hnB:base + n < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => Slice a xs base σ∧ Represents b ys σ∧
        σ.vars "row.base"=base∧ σ.vars "vec.n"=n)
      (rowDotProduct a b)
      (fun _ τ => DotOutput (prefixValue xs ys n) τ∧ Slice a xs base τ∧
        Represents b ys τ∧ τ.vars "vec.i"=n∧ τ.vars "vec.n"=n∧
        τ.vars "row.base"=base)
      ((144 * (cap n H).size + 216 + 4) * n + 12):=by
  have hn:n < B:=by omega
  have hlo:=Spec.forRangeZero "vec.i" "vec.n" (RowInvariant a b xs ys base n) n
    (144 * (cap n H).size + 216) hn
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (rowDotStep_spec B base n H a b xs ys hx hy hH hxs hys hnB hB)
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσx,hσy,hσbase,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "vec.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "vec.i") (Expr.var "vec.n")) (rowDotStep a b)); let c1:Env:=Env.setVar σ "dot.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "dot.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "dot.d" ((1:Nat)); let c4:Env→ Nat→ Prop:=Run B c0 c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat→ Nat:=c5 (c6 (c5 (c5 (c6 ((144:Nat)) (Nat.size (cap n H))) ((216:Nat))) ((4:Nat))) n); let c8:Nat:=c7 ((6:Nat)); let c9:Env→ Prop:=RowInvariant a b xs ys base n; let c10:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (c9 σ') (@Eq Nat (Env.vars σ' "vec.i") n)); let c11:Nat:=c7 ((12:Nat)); let c12:Env→ Prop:=(fun (x τ:Env) => And (DotOutput (prefixValue xs ys n) τ) (And (Slice a xs base τ) (And (Represents b ys τ) (And (@Eq Nat (Env.vars τ "vec.i") n) (And (@Eq Nat (Env.vars τ "vec.n") n) (@Eq Nat (Env.vars τ "row.base") base)))))) σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B (rowDotProduct a b) σ σ' c11) (c12 σ'); let c14:Prop:= @Exists Env c13; let c15:Nat→ Nat:=c5 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat→ Nat:=c5 c16; let c18:Nat:=c15 (Expr.size (Expr.lit ((1:Nat)))); let c19:Nat:=c5 c18 c8; let c20:Nat:=c17 c19; let c21:Com:=Com.assign "dot.n" (Expr.lit ((0:Nat))); let c22:Com:=Com.assign "dot.d" (Expr.lit ((1:Nat))); let c23:Com:=Com.seq c22 c0; @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c14) (RunStep.use B (fun (σ_1:Env) => c9 (Env.setVar σ_1 "vec.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (c9 σ') (@Eq Nat (Env.vars σ' "vec.i") n)) c8 hlo c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (c9 w) (@Eq Nat (Env.vars w "vec.i") n))) => let c0_1:Prop:=And (c9 w) (@Eq Nat (Env.vars w "vec.i") n); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c14) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c13 w (@And.intro (Run B (rowDotProduct a b) σ w c11) (c12 w) (RunStep.mono B (rowDotProduct a b) σ w (c17 c20) c11 (RunStep.seq B (Com.assign "dot.s" (Expr.lit ((0:Nat)))) (Com.seq c21 c23) σ c1 w c16 c20 (RunStep.assign B σ "dot.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4198_0_0_0))) (RunStep.seq B c21 c23 c1 c2 w c16 c19 (RunStep.assign B c1 "dot.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g4198_0_0_1))) (RunStep.seq B c22 c0 c2 c3 w c18 c8 (RunStep.assign B c2 "dot.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) left))) (?nAX_g4198_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4198_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4198_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4198_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [RowInvariant,DotOutput,Slice,Represents,prefix_zero,fractionValue]
  all_goals first | omega | aesop

theorem rowDotProduct_frame_spec (B base n H:ℕ) (a b:String) (xs ys:List ℚ)
    (hx:xs.length=n) (hy:ys.length=n) (hH:1≤ H)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H)
    (hnB:base + n < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => Slice a xs base σ∧ Represents b ys σ∧
        σ.vars "row.base"=base∧ σ.vars "vec.n"=n)
      (rowDotProduct a b)
      (fun σ τ => DotOutput (prefixValue xs ys n) τ∧ τ.arrs=σ.arrs)
      ((144 * (cap n H).size + 216 + 4) * n + 12):=by
  have h:=spec_with_fields []
    (rowDotProduct_spec B base n H a b xs ys hx hy hH hxs hys hnB hB)
    (by simp) (by
      simp [rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,loadRight,addToAccumulator,
        addFraction,multiplyFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  intro σ hσ
  obtain ⟨τ,hr,hq,_,ha⟩:=h σ hσ
  exact ⟨τ,hr,hq.1,ha⟩

theorem matrixRowDot_spec (B m n H:ℕ) (a b:String)
    (A:Matrix (Fin m) (Fin n) ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H)
    (hdims:m + n + m * n + 1 < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows a A σ∧ Represents b (List.ofFn c) σ∧
        σ.vars "row.i"=i.val∧ σ.vars "vec.n"=n)
      (matrixRowDot a b)
      (fun σ τ => DotOutput (∑ j,A i j * c j) τ∧ τ.arrs=σ.arrs)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12)):=by
  have hindex:i.val * n + n < B:=by
    have hmul:=Nat.mul_le_mul_right n (by omega:i.val + 1≤ m)
    nlinarith
  have hiB:i.val < B:=by have:=i.isLt; omega
  have hnB:n < B:=by omega
  have hbaseB:i.val * n < B:=by omega
  have hxs:∀ q∈ List.ofFn (A i),Height q H:=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨j,rfl⟩:=hq
    exact hA i j
  have hys:∀ q∈ List.ofFn c,Height q H:=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨j,rfl⟩:=hq
    exact hc j
  have hrow:=rowDotProduct_frame_spec B (i.val * n) n H a b (List.ofFn (A i))
    (List.ofFn c) (by simp) (by simp) hH hxs hys hindex hB
  rintro σ ⟨hσA,hσc,hσi,hσn⟩
  have hslice:=hσA i
  clear hσA
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "row.i") (Env.vars σ "vec.n"); let c2:Env:=Env.setVar σ "row.base" c1; let c3:Env→ Nat→ Prop:=Run B (rowDotProduct a b) c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 (c0 (c4 (c4 (c0 ((144:Nat)) (Nat.size (cap n H))) ((216:Nat))) ((4:Nat))) n) ((12:Nat)); let c6:Env→ Prop:=DotOutput (prefixValue (@List.ofFn Rat n (A i)) (@List.ofFn Rat n c) n); let c7:String→ List Nat:=Env.arrs c2; let c8:Env→ Prop:=fun (σ':Env) => And (c3 σ' c5) (And (c6 σ') (@Eq (String→ List Nat) (Env.arrs σ') c7)); let c9:Nat:=c4 ((4:Nat)) c5; let c10:Env→ Prop:=DotOutput (∑ j:Fin n, @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (A i j) (c j)); let c11:Env→ Prop:=(fun (σ_1 τ:Env) => And (c10 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B (matrixRowDot a b) σ σ' c9) (c11 σ'); let c13:Nat:=c0 (@Fin.val m i) n; let c14:Env→ Prop:=Slice a (@List.ofFn Rat n (A i)) c13; let c15:String→ Nat:=Env.vars c2; let c16:Nat:=c4 ((1:Nat)) (Expr.size (Expr.mul (Expr.var "row.i") (Expr.var "vec.n"))); @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => @Exists Env c12) (RunStep.use B (fun (σ_1:Env) => And (c14 σ_1) (And (Represents b (@List.ofFn Rat n c) σ_1) (And (@Eq Nat (Env.vars σ_1 "row.base") c13) (@Eq Nat (Env.vars σ_1 "vec.n") n)))) (rowDotProduct a b) (fun (σ_1 τ:Env) => And (c6 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))) c5 hrow c2 ?_) fun (w:Env) (h:And (c3 w c5) (And (c6 w) (@Eq (String→ List Nat) (Env.arrs w) c7))) => let c0_1:Prop:=And (c6 w) (@Eq (String→ List Nat) (Env.arrs w) c7); @And.casesOn (c3 w c5) c0_1 (fun (x:And (c3 w c5) c0_1) => @Exists Env c12) h fun (left:c3 w c5) (right:c0_1) => @Exists.intro Env c12 w (@And.intro (Run B (matrixRowDot a b) σ w c9) (c11 w) (RunStep.mono B (matrixRowDot a b) σ w (c4 c16 c5) c9 (RunStep.seq B (Com.assign "row.base" (Expr.mul (Expr.var "row.i") (Expr.var "vec.n"))) (rowDotProduct a b) σ c2 w c16 c5 (RunStep.assign B σ "row.base" (Expr.mul (Expr.var "row.i") (Expr.var "vec.n")) c1 (RunStep.eval_mul B σ (Expr.var "row.i") (Expr.var "vec.n") (Env.vars σ "row.i") (Env.vars σ "vec.n") (RunStep.eval_var B σ "row.i" (?nAX_g4202_0_0_0)) (RunStep.eval_var B σ "vec.n" (?nAX_g4202_0_0_1)) ?_)) left) (?nAX_g4202_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4202_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4202_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4202_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hrow
  all_goals simp_all [prefix_ofFn,Slice]
  all_goals first | omega | aesop

end Lax109476Proofs.RamMatrixRows

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

theorem storeDotAtRow_basic_spec (B i:ℕ) (a:String) (qs:List ℚ) (q:ℚ)
    (hi:i < qs.length) (hiB:i < B) (hB:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ DotOutput q σ∧ σ.vars "row.i"=i)
      (storeDotAtRow a) (fun _ τ => Represents a (qs.set i q) τ) 21:=by
  rintro σ ⟨hσa,hσq,hσi⟩
  have hsB:=hσq.2.2.2.trans_lt hB
  have hnum:=hσq.2.1
  have hden:=hσq.2.2.1
  have hstore:=storeReduced_spec B a qs q i hi hB hiB hn hd
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) "dot.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "dot.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat:=Env.vars c3 "row.i"; let c5:Env:=Env.setVar c3 "vec.i" c4; let c6:Env→ Nat→ Prop:=Run B (storeReduced a) c5; let c7:Env→ Prop:=Represents a (@List.set Rat qs i q); let c8:Env→ Prop:=fun (σ':Env) => And (c6 σ' ((13:Nat))) (c7 σ'); let c9:Env→ Env→ Prop:=fun (x τ:Env) => c7 τ; let c10:Env→ Prop:=c9 σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B (storeDotAtRow a) σ σ' ((21:Nat))) (c10 σ'); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat:=c13 (Expr.size (Expr.var "dot.s")); let c15:Nat:=c13 (Expr.size (Expr.var "dot.n")); let c16:Nat:=c13 (Expr.size (Expr.var "dot.d")); let c17:Nat:=c13 (Expr.size (Expr.var "row.i")); let c18:Nat:=c12 c17 ((13:Nat)); let c19:Nat:=c12 c16 c18; let c20:Nat:=c12 c15 c19; let c21:Com:=Com.seq (Com.assign "vec.i" (Expr.var "row.i")) (storeReduced a); let c22:Com:=Com.seq (Com.assign "rat.d" (Expr.var "dot.d")) c21; @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => @Exists Env c11) (RunStep.use B (fun (σ_1:Env) => And (Represents a qs σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (FractionOutput q σ_1))) (storeReduced a) c9 ((13:Nat)) hstore c5 ?_) fun (w:Env) (h:And (c6 w ((13:Nat))) (c7 w)) => let c0_1:Prop:=c6 w ((13:Nat)); @And.casesOn c0_1 (c7 w) (fun (x:And c0_1 (c7 w)) => @Exists Env c11) h fun (left:c0_1) (right:c7 w) => @Exists.intro Env c11 w (@And.intro (Run B (storeDotAtRow a) σ w ((21:Nat))) (c10 w) (RunStep.mono B (storeDotAtRow a) σ w (c12 c14 c20) ((21:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "dot.s")) (Com.seq (Com.assign "rat.n" (Expr.var "dot.n")) c22) σ (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) w c14 c20 (RunStep.assign B σ "rat.s" (Expr.var "dot.s") (Env.vars σ "dot.s") (RunStep.eval_var B σ "dot.s" hsB)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "dot.n")) c22 (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) c1 w c15 c19 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) "rat.n" (Expr.var "dot.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "dot.s")) "dot.n" (?nAX_g4252_0_0_0))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "dot.d")) c21 c1 c3 w c16 c18 (RunStep.assign B c1 "rat.d" (Expr.var "dot.d") c2 (RunStep.eval_var B c1 "dot.d" (?nAX_g4252_0_0_1))) (RunStep.seq B (Com.assign "vec.i" (Expr.var "row.i")) (storeReduced a) c3 c5 w c17 ((13:Nat)) (RunStep.assign B c3 "vec.i" (Expr.var "row.i") c4 (RunStep.eval_var B c3 "row.i" (?nAX_g4252_0_0_2))) left)))) (?nAX_g4252_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4252_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4252_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4252_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4252_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hstore
  all_goals simp_all [Represents,FractionOutput,DotOutput]

theorem storeDotAtRow_spec (B i:ℕ) (a:String) (qs:List ℚ) (q:ℚ)
    (hi:i < qs.length) (hiB:i < B) (hB:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents a qs σ∧ DotOutput q σ∧ σ.vars "row.i"=i)
      (storeDotAtRow a)
      (fun σ τ => Represents a (qs.set i q) τ∧
        FieldsAgree ["row.i", "row.m", "vec.n"] σ τ∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b) 21:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=storeDotAtRow_basic_spec B i a qs q hi hiB hB hn hd σ hσ
  refine ⟨τ,hr,hτ, ?_, ?_⟩
  · intro x hx
    apply hr.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl <;> simp [storeDotAtRow,storeReduced,Com.wvars]
  · intro b hb
    apply hr.frame_arr
    simpa [storeDotAtRow,storeReduced,Com.warrs] using hb

def filled {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (c:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun i => if i.val < k then ∑ j,A i j * c j else 0)

theorem filled_zero {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (c:Fin n→ ℚ):
    filled A c 0=List.replicate m 0:=by simp [filled]

theorem filled_done {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (c:Fin n→ ℚ):
    filled A c m=List.ofFn (A *ᵥ c):=by
  unfold filled
  congr 1
  funext i
  simp [i.isLt,Matrix.mulVec,_root_.dotProduct]

theorem filled_step {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (c:Fin n→ ℚ) (i:Fin m):
    (filled A c i.val).set i.val (∑ j,A i j * c j)=filled A c (i.val + 1):=by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkm:k < m:=by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki:i.val=k
    · have hfin:i=(⟨k,hkm⟩:Fin m):=Fin.ext hki
      simp [filled,hfin]
    · have hnext:k < i.val + 1↔ k < i.val:=by omega
      simp only [hki, ↓reduceIte,filled,List.getElem_ofFn]
      change (if k < i.val then ∑ j,A ⟨k,hkm⟩ j * c j else 0) =
        (if k < i.val + 1 then ∑ j,A ⟨k,hkm⟩ j * c j else 0)
      simp only [hnext]

def VectorInvariant (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ) (σ:Env):Prop:=
  MatrixRows "ell.shape" A σ∧ Represents "ell.normal" (List.ofFn c) σ∧
    Represents "ell.u" (filled A c (σ.vars "row.i")) σ∧ σ.vars "row.i" ≤ n∧
    σ.vars "row.m"=n∧ σ.vars "vec.n"=n

theorem matrixVectorStep_spec (B n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H)
    (hdims:n + n + n * n + 1 < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => VectorInvariant n A c σ∧ σ.vars "row.i" < n)
      matrixVectorStep
      (fun σ τ => VectorInvariant n A c τ∧ τ.vars "row.i"=σ.vars "row.i" + 1)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4):=by
  rintro σ ⟨⟨hσA,hσc,hσu,hσin,hσm,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "row.i",hσi⟩
  have hrow:=spec_with_fields ["row.i", "row.m", "vec.n"]
    (matrixRowDot_spec B n n H "ell.shape" "ell.normal" A c i hH hA hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;>
      simp [matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,loadRight,
        addToAccumulator,addFraction,multiplyFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
    (by simp [matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,loadRight,
        addToAccumulator,addFraction,multiplyFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  obtain ⟨τ,hr₁, ⟨hτq,hτa⟩,hτfields,_⟩:=hrow σ ⟨hσA,hσc,rfl,hσn⟩
  have hτu:Represents "ell.u" (filled A c i.val) τ:=by
    simpa only [Represents,hτa] using hσu
  have hτi:τ.vars "row.i"=i.val:=hτfields _ (by simp)
  have hsum:Height (∑ j,A i j * c j) (cap n H):=by
    rw [← prefix_ofFn]
    apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hA i j
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hc j
  have hcapB:cap n H < B:=by nlinarith
  have hiB:i.val < B:=by have:=i.isLt; omega
  have h1:1 < B:=by nlinarith
  obtain ⟨υ,hr₂,hυu,hυfields,hυarr⟩:=storeDotAtRow_spec B i.val "ell.u"
    (filled A c i.val) (∑ j,A i j * c j) (by simp [filled]) hiB h1
    (hsum.1.trans_lt hcapB) (hsum.2.trans_lt hcapB) τ ⟨hτu,hτq,hτi⟩
  have hυi:υ.vars "row.i"=i.val:=(hυfields _ (by simp)).trans hτi
  have hnB:n < B:=by omega
  have hi1B:i.val + 1 < B:=lt_of_le_of_lt (by have:=i.isLt; omega) hnB
  have hυiB:υ.vars "row.i" < B:=hυi ▸ hiB
  have hsumB:Bop.add.apply (υ.vars "row.i") 1 < B:=by simpa [Bop.apply,hυi] using hi1B
  have hr₃:Run B (.assign "row.i" (.add (.var "row.i") (.lit 1))) υ
      (υ.setVar "row.i" (i.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hυi] using
      (evalB_bin (evalB_var hυiB) (evalB_lit h1) hsumB))
  have hυA:MatrixRows "ell.shape" A υ:=by
    simpa only [MatrixRows,Slice,hυarr ("ell.shape" ++ ".s") (by decide),
      hυarr ("ell.shape" ++ ".n") (by decide),hυarr ("ell.shape" ++ ".d") (by decide),hτa] using hσA
  have hυc:Represents "ell.normal" (List.ofFn c) υ:=by
    simpa only [Represents,hυarr ("ell.normal" ++ ".s") (by decide),
      hυarr ("ell.normal" ++ ".n") (by decide),hυarr ("ell.normal" ++ ".d") (by decide),hτa] using hσc
  have hυm:υ.vars "row.m"=n:=
    (hυfields _ (by simp)).trans ((hτfields _ (by simp)).trans hσm)
  have hυn:υ.vars "vec.n"=n:=
    (hυfields _ (by simp)).trans ((hτfields _ (by simp)).trans hσn)
  refine ⟨_, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [MatrixRows,Slice,arrs_setVar] using hυA
  · simpa only [Represents,arrs_setVar] using hυc
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true,filled_step] using hυu
  · change i.val + 1≤ n
    exact i.isLt
  · simpa using hυm
  · simpa using hυn
  · simp [i]

theorem ellipsoidMulVec_spec (B n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H)
    (hdims:n + n + n * n + 1 < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows "ell.shape" A σ∧ Represents "ell.normal" (List.ofFn c) σ∧
        Represents "ell.u" (List.replicate n 0) σ∧ σ.vars "vec.n"=n)
      ellipsoidMulVec
      (fun _ τ => Represents "ell.u" (List.ofFn (A *ᵥ c)) τ∧ MatrixRows "ell.shape" A τ∧
        Represents "ell.normal" (List.ofFn c) τ∧ τ.vars "vec.n"=n)
      (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8):=by
  have hnB:n < B:=by omega
  have hlo:=Spec.forRangeZero "row.i" "row.m" (VectorInvariant n A c) n
    (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) hnB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2.1)
    (matrixVectorStep_spec B n H A c hH hA hc hdims hB)
  rintro σ ⟨hσA,hσc,hσu,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "row.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "row.i") (Expr.var "row.m")) matrixVectorStep); let c1:Env→ Nat→ Prop:=Run B c0 (Env.setVar σ "row.m" (Env.vars σ "vec.n")); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c2 (c3 (c2 (c2 (c2 (c2 ((4:Nat)) (c2 (c3 (c2 (c2 (c3 ((144:Nat)) (Nat.size (cap n H))) ((216:Nat))) ((4:Nat))) n) ((12:Nat)))) ((21:Nat))) ((4:Nat))) ((4:Nat))) n); let c5:Nat:=c4 ((6:Nat)); let c6:Env→ Prop:=fun (σ':Env) => And (c1 σ' c5) (And (VectorInvariant n A c σ') (@Eq Nat (Env.vars σ' "row.i") n)); let c7:Nat:=c4 ((8:Nat)); let c8:Env→ Prop:=Represents "ell.u" (@List.ofFn Rat n (@Matrix.mulVec (Fin n) (Fin n) Rat (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat (@CommRing.toNonUnitalCommRing Rat Rat.commRing)))) (Fin.fintype n) A c)); let c9:Env→ Prop:=(fun (x τ:Env) => And (c8 τ) (And (@MatrixRows n n "ell.shape" A τ) (And (Represents "ell.normal" (@List.ofFn Rat n c) τ) (@Eq Nat (Env.vars τ "vec.n") n)))) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B ellipsoidMulVec σ σ' c7) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.var "vec.n")); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c11) (RunStep.use B (fun (σ_1:Env) => VectorInvariant n A c (Env.setVar σ_1 "row.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (VectorInvariant n A c σ') (@Eq Nat (Env.vars σ' "row.i") n)) c5 hlo (Env.setVar σ "row.m" (Env.vars σ "vec.n")) ?_) fun (w:Env) (h:And (c1 w c5) (And (VectorInvariant n A c w) (@Eq Nat (Env.vars w "row.i") n))) => let c0_1:Prop:=And (VectorInvariant n A c w) (@Eq Nat (Env.vars w "row.i") n); @And.casesOn (c1 w c5) c0_1 (fun (x:And (c1 w c5) c0_1) => c11) h fun (left:c1 w c5) (right:c0_1) => @Exists.intro Env c10 w (@And.intro (Run B ellipsoidMulVec σ w c7) (c9 w) (RunStep.mono B ellipsoidMulVec σ w (c2 c12 c5) c7 (RunStep.seq B (Com.assign "row.m" (Expr.var "vec.n")) c0 σ (Env.setVar σ "row.m" (Env.vars σ "vec.n")) w c12 c5 (RunStep.assign B σ "row.m" (Expr.var "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4262_0_0_0))) left) (?nAX_g4262_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try clear h left); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4262_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4262_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [VectorInvariant,MatrixRows,Slice,Represents,filled_zero,filled_done]

end Lax109476Proofs.RamMatrixVector

end

theorem solution:∀ (B n H:Nat) (A:Matrix (Fin n) (Fin n) Rat) (c:Fin n→ Rat),
  Nat.le ((1:Nat)) H→
    (∀ (k j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (A k j) H)→
      (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (c j) H)→
        Nat.lt
            (Nat.add
              (Nat.add (Nat.add n n)
                (Nat.mul n n))
              ((1:Nat)))
            B→
          Nat.lt
              (Nat.add
                (Nat.mul
                  ((2:Nat))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (Lax109476Proofs.RamDotProduct.cap n H) ((2:Nat))))
                ((3:Nat)))
              B→
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamMatrixRows.MatrixRows n n "ell.shape" A σ)
                  (And (Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (@List.ofFn Rat n c) σ)
                    (And
                      (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                        (@List.replicate Rat n (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) σ)
                      (@Eq Nat (σ.vars "vec.n") n))))
              Lax109476Proofs.RamMatrixVector.ellipsoidMulVec
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And
                  (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                    (@List.ofFn Rat n
                      (@Matrix.mulVec (Fin n) (Fin n) Rat
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                              (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                        (Fin.fintype n) A c))
                    τ)
                  (And (@Lax109476Proofs.RamMatrixRows.MatrixRows n n "ell.shape" A τ)
                    (And (Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (@List.ofFn Rat n c) τ)
                      (@Eq Nat (τ.vars "vec.n") n))))
              (Nat.add
                (Nat.mul
                  (Nat.add
                    (Nat.add
                      (Nat.add
                        (Nat.add
                          ((4:Nat))
                          (Nat.add
                            (Nat.mul
                              (Nat.add
                                (Nat.add
                                  (Nat.mul
                                    ((144:Nat))
                                    (Lax109476Proofs.RamDotProduct.cap n H).size)
                                  ((216:Nat)))
                                ((4:Nat)))
                              n)
                            ((12:Nat))))
                        ((21:Nat)))
                      ((4:Nat)))
                    ((4:Nat)))
                  n)
                ((8:Nat))):= @Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec
