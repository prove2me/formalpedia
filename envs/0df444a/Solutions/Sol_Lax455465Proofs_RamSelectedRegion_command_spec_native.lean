-- Prove2me | solution 1 for Lax455465Proofs.RamSelectedRegion.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:29:42.973488+00:00
-- url     : https://prove2.me/submissions/d4f3e89e-dcb6-479a-a931-9aa54d8b291c

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.NNRat.BigOperators
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
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

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

theorem multiplyFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 64)  :=by
  exact Lax109476Proofs.RamRational.multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

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

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def leFlag (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then
    if s₁=1 then (if n₁ * d₂ < n₂ * d₁ then 0 else 1)
    else (if n₂ * d₁ < n₁ * d₂ then 0 else 1)
  else if s₁=1 then 1
  else if n₁=0 then (if n₂=0 then 1 else 0) else 0

theorem leFlag_le_one (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):leFlag s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by
  unfold leFlag
  split_ifs <;> omega

theorem leFlag_correct (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    leFlag s₁ n₁ d₁ s₂ n₂ d₂=1↔
      fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂:=by
  have hd₁q:(0:ℚ) < d₁:=by exact_mod_cast hd₁
  have hd₂q:(0:ℚ) < d₂:=by exact_mod_cast hd₂
  have hpos₁:(0:ℚ)≤ (n₁:ℚ) / d₁:=by positivity
  have hpos₂:(0:ℚ)≤ (n₂:ℚ) / d₂:=by positivity
  have hcross:(n₁:ℚ) / d₁≤ (n₂:ℚ) / d₂↔ n₁ * d₂≤ n₂ * d₁:=by
    rw [div_le_div_iff₀ hd₁q hd₂q]
    exact_mod_cast Iff.rfl
  have hcrossRev:(n₂:ℚ) / d₂≤ (n₁:ℚ) / d₁↔ n₂ * d₁≤ n₁ * d₂:=by
    rw [div_le_div_iff₀ hd₂q hd₁q]
    exact_mod_cast Iff.rfl
  have hzero:(n₁:ℚ) / d₁≤ -((n₂:ℚ) / d₂)↔ n₁=0∧ n₂=0:=by
    constructor
    · intro h
      have hz₁:(n₁:ℚ) / d₁=0:=by linarith
      have hz₂:(n₂:ℚ) / d₂=0:=by linarith
      simpa [div_eq_zero_iff,ne_of_gt hd₁q,ne_of_gt hd₂q] using And.intro hz₁ hz₂
    · rintro ⟨rfl,rfl⟩; simp
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl
  · simp [leFlag,fractionValue,hcross]
  · simp [leFlag,fractionValue,neg_div,hzero]
    split_ifs <;> simp_all
  · simp [leFlag,fractionValue,neg_div]
    linarith
  · simp [leFlag,fractionValue,neg_div,hcrossRev]

set_option maxHeartbeats 0 in
theorem compareFraction_flag_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le"=leFlag s₁ n₁ d₁ s₂ n₂ d₂) 40:=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have huB:n₁ * d₂ < B:=(Nat.mul_le_mul hn₁ hd₂).trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=(Nat.mul_le_mul hn₂ hd₁).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "cmp.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "cmp.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat→ Prop:= @Eq Nat c9; let c11:Nat:=c8 "right.s"; let c12:Prop:=c10 c11; let c13:Prop:=Not c12; let c14:Nat:=leFlag s₁ n₁ d₁ s₂ n₂ d₂; let c15:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "cmp.le") c14) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction σ σ' ((40:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Prop:=c10 ((1:Nat)); let c19:Prop:=Not c18; let c20:Nat:=c8 "cmp.u"; let c21:Nat→ Prop:=Nat.lt c20; let c22:Nat:=c8 "cmp.v"; let c23:Prop:=c21 c22; let c24:Prop:=Not c23; let c25:Nat→ Env:=Env.setVar c7 "cmp.le"; let c26:Env:=c25 ((0:Nat)); let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Nat:=c28 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c30:Nat→ Nat:=c27 c29; let c31:Nat:=c28 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c32:Nat→ Nat:=c27 c31; let c33:Nat→ Nat:=c27 (c28 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c34:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c35:Nat→ Nat:=c27 (c28 (Cond.size c34)); let c36:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")))); let c37:Nat:=c28 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat:=c36 c37; let c39:Nat:=c35 c38; let c40:Nat:=c33 c39; let c41:Nat:=c32 c40; let c42:Com:=Com.assign "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c43:Com→ Com→ Com:=Com.ite c34; let c44:Com:=Com.assign "cmp.le" (Expr.lit ((0:Nat))); let c45:Com:=Com.assign "cmp.le" (Expr.lit ((1:Nat))); let c46:Com:=Com.ite (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45; let c47:Com:=Com.ite (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45; let c48:Com:=c43 c46 c47; let c49:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c50:Cond:=Cond.eq (Expr.var "right.n") (Expr.lit ((0:Nat))); let c51:Com:=Com.ite c50 c45 c44; let c52:Com:=Com.ite c49 c51 c44; let c53:Com:=c43 c45 c52; let c54:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53; let c55:Nat→ Prop:=Nat.lt c22; let c56:Env:=c25 ((1:Nat)); let c57:Nat:=c28 (Expr.size (Expr.lit ((1:Nat)))); let c58:Nat:=c36 c57; let c59:Nat:=c35 c58; let c60:Nat:=c33 c59; let c61:Nat:=c32 c60; let c62:Prop:=c55 c20; let c63:Prop:=Not c62; let c64:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")))); let c65:Nat:=c64 c37; let c66:Nat:=c35 c65; let c67:Nat:=c33 c66; let c68:Nat:=c32 c67; let c69:Nat:=c64 c57; let c70:Nat:=c35 c69; let c71:Nat:=c33 c70; let c72:Nat:=c32 c71; let c73:Nat:=c35 c57; let c74:Nat:=c33 c73; let c75:Nat:=c32 c74; let c76:Nat:=c8 "left.n"; let c77:Prop:= @Eq Nat c76 ((0:Nat)); let c78:Prop:=Not c77; let c79:Nat:=c8 "right.n"; let c80:Prop:= @Eq Nat c79 ((0:Nat)); let c81:Prop:=Not c80; let c82:Nat→ Nat:=c27 (c28 (Cond.size c49)); let c83:Nat→ Nat:=c27 (c28 (Cond.size c50)); let c84:Nat:=c83 c57; let c85:Nat:=c82 c84; let c86:Nat:=c35 c85; let c87:Nat:=c33 c86; let c88:Nat:=c32 c87; let c89:Nat:=c83 c37; let c90:Nat:=c82 c89; let c91:Nat:=c35 c90; let c92:Nat:=c33 c91; let c93:Nat:=c32 c92; let c94:Nat:=c82 c37; let c95:Nat:=c35 c94; let c96:Nat:=c33 c95; let c97:Nat:=c32 c96; @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c17) (Classical.em c12) (fun (hcase:c12) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c17) (Classical.em c23) (fun (hcase_2:c23) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c41) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c41 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_1)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c40 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_3)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c39 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_5)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c26 c38 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_7)))))))) (?nAX_g5438_0_0_8)) ?_)) fun (hcase_2:c24) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c61) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c61 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_9)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_10)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c60 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_11)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_12)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c59 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_13)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_14)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c56 c58 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_15)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_16)) ?_)) fun (hcase_1:c19) => @Or.casesOn c62 c63 (fun (x:Or c62 c63) => c17) (Classical.em c62) (fun (hcase_2:c62) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c68) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c68 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_17)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_18)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c67 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_19)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_20)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c66 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_21)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_22)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c26 c65 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_23)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_24)))))))) (?nAX_g5438_0_0_25)) ?_)) fun (hcase_2:c63) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c72) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c72 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_26)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_27)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c71 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_28)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_29)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c70 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_30)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_31)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c56 c69 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_33)) ?_)) fun (hcase:c13) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c75) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c75 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_34)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_35)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c74 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_36)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_37)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c73 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_38)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_39)) hcase) (RunStep.ite_true B c34 c45 c52 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))) (?nAX_g5438_0_0_41)) ?_)) fun (hcase_1:c19) => @Or.casesOn c77 c78 (fun (x:Or c77 c78) => c17) (Classical.em c77) (fun (hcase_2:c77) => @Or.casesOn c80 c81 (fun (x:Or c80 c81) => c17) (Classical.em c80) (fun (hcase_3:c80) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c88) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c88 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_42)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_43)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c87 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_44)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_45)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c86 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_46)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_47)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c56 c85 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_48)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c56 c84 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_49)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_50)) hcase_2) (RunStep.ite_true B c50 c45 c44 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_51)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_52)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))))) (?nAX_g5438_0_0_53)) ?_)) fun (hcase_3:c81) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c93) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c93 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_54)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_55)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c92 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_56)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_57)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c91 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_58)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_59)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c90 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_60)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c26 c89 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_61)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_62)) hcase_2) (RunStep.ite_false B c50 c45 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_63)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_64)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_65))))))))) (?nAX_g5438_0_0_66)) ?_)) fun (hcase_2:c78) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c97) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c97 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_67)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_68)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c96 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_69)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_70)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c95 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_71)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_72)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c94 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_73)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B c49 c51 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_74)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_75)) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_76)))))))) (?nAX_g5438_0_0_77)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5438_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [leFlag]

theorem compareFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" ≤ 1∧
        (σ'.vars "cmp.le"=1↔ fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂)) 40:=by
  apply (compareFraction_flag_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂).post
  intro σ τ _ ht
  rw [ht]
  exact ⟨leFlag_le_one _ _ _ _ _ _,leFlag_correct _ _ _ _ _ _ hs₁ hs₂ hd₁pos hd₂pos⟩

end Lax455465Proofs.RamComparison

end

section

namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

@[simp] theorem length_encode (qs:List ℚ≥0):(encode qs).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

theorem numerator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i]?=some qs[i].num:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)=Nat.succ (Nat.succ (2*i)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem denominator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i+1]?=some qs[i].den:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)+1=Nat.succ (Nat.succ (2*i+1)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem read_spec (B:ℕ) (array index:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s"):
    Spec B (fun σ => Prefix (encode qs) array σ∧ σ.vars index=i) (read array index)
      (fun _ τ => FractionOutput (qs[i]:ℚ) τ∧ τ.vars "rat.s"=0) 14:=by
  have hnum:=numerator_at qs i hi
  have hden:=denominator_at qs i hi
  rintro σ ⟨hp,hv⟩
  have hni:2*i < (encode qs).length:=by simp only [length_encode]; omega
  have hdi:2*i+1 < (encode qs).length:=by simp only [length_encode]; omega
  have hnumval:(encode qs)[2*i]=qs[i].num:=by simpa only [List.getElem?_eq_getElem hni,Option.some.injEq] using hnum
  have hdenval:(encode qs)[2*i+1]=qs[i].den:=by simpa only [List.getElem?_eq_getElem hdi,Option.some.injEq] using hden
  have hgN:=(hp (2*i) hni).trans (congrArg some hnumval)
  have hgD:=(hp (2*i+1) hdi).trans (congrArg some hdenval)
  have hN:2*i < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgN; cases hgN
  have hD:2*i+1 < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgD; cases hgD
  have hni':i < B:=by omega
  have hmul:2*i < B:=by omega
  have hvalue:fractionValue 0 qs[i].num qs[i].den=(qs[i]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den qs[i])
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (@getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i_1:Nat) => Nat.lt i_1 (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) qs i hi)); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (@Eq Nat (Env.vars τ "rat.s") ((0:Nat)))) σ; let c2:Nat→ Nat:=Nat.mul ((2:Nat)); let c3:Nat:=c2 (Env.vars σ index); let c4:Nat:= @List.getD Nat (Env.arrs σ array) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "rat.n" c4; let c6:List Nat:=Env.arrs c5 array; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c5 index; let c9:Nat:=c2 c8; let c10:Nat:=c7 c9 ((1:Nat)); let c11:Nat:= @List.getD Nat c6 c10 ((0:Nat)); let c12:Env:=Env.setVar c5 "rat.d" c11; let c13:Env:=Env.setVar c12 "rat.s" ((0:Nat)); let c14:Nat→ Nat:=c7 ((1:Nat)); let c15:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var index); let c16:Expr:=Expr.get array c15; let c17:Nat:=c14 (Expr.size c16); let c18:Expr:=Expr.add c15 (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c14 (Expr.size c19); let c21:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c22:Nat:=c7 c20 c21; let c23:Com:=Com.assign "rat.d" c19; let c24:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c25:Nat→ Prop:=Nat.lt c10; @Exists.intro Env (fun (σ':Env) => And (Run B (read array index) σ σ' ((14:Nat))) (c1 σ')) c13 (@And.intro (Run B (read array index) σ c13 ((14:Nat))) (c1 c13) (RunStep.mono B (read array index) σ c13 (c7 c17 c22) ((14:Nat)) (RunStep.seq B (Com.assign "rat.n" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "rat.n" c16 c4 (RunStep.eval_get B σ array c15 c3 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) (Env.vars σ index) (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_var B σ index (?nAX_g5778_0_0_0)) (?nAX_g5778_0_0_1)) (?nAX_g5778_0_0_2) ?_)) (RunStep.seq B c23 c24 c5 c12 c13 c20 c21 (RunStep.assign B c5 "rat.d" c19 c11 (RunStep.eval_get B c5 array c18 c10 (RunStep.eval_add B c5 c15 (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_mul B c5 (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) c8 (RunStep.eval_lit B ((2:Nat)) c5 h2) (RunStep.eval_var B c5 index ?_) ?_) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g5778_0_0_3)) ?_) ?_ ?_)) (RunStep.assign B c12 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c12 (?nAX_g5778_0_0_4))))) (?nAX_g5778_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5778_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

end Lax455465Proofs.RamUnsignedBuffer

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

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem zero_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zero σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zero σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5825_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5825_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5825_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5825_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem one_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) one (fun _ τ => FractionOutput 1 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((1:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c8:Nat:=c4 c7 c7; let c9:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B one σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B one σ c3 (c4 c6 c8) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c9 c10) σ c1 c3 c6 c8 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5826_0_0_0))) (RunStep.seq B c9 c10 c1 c2 c3 c7 c7 (RunStep.assign B c1 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c1 h1)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5826_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5826_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5826_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax455465Proofs.RamFractionPrimitives

end

section

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val=s.val * n + t.val:=by
  simp [edgeIndex,finProdFinEquiv]
  ring

private theorem code_div (a b n:ℕ) (hn:0 < n) (hb:b < n):
    (a * n + b) / n=a:=by
  rw [Nat.add_comm,Nat.add_mul_div_right b a hn,Nat.div_eq_of_lt hb,Nat.zero_add]

private theorem code_mod (a b n:ℕ) (hb:b < n):(a * n + b) % n=b:=by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem edge_div {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val / n=s.val:=by
  rw [edge_value]
  exact code_div _ _ _ ((Nat.zero_le t.val).trans_lt t.isLt) t.isLt

theorem edge_mod {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val % n=t.val:=by
  rw [edge_value]
  exact code_mod _ _ _ t.isLt

end Lax455465Proofs.FlowLpIndices

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

namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B:ℕ) (array cursor:String) (q:ℚ≥0) (words:List ℕ) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B) (hlen:words.length+2 < B) (hfresh:cursor ≠ "rat.d"):
    Spec B (fun σ => FractionOutput (q:ℚ) σ∧ Prefix words array σ∧
      σ.vars cursor=words.length∧ words.length+1 < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (words ++ Lax455465.RationalEncoding.encodeRational q) array τ∧
        τ.vars cursor=words.length+2) 14:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  have hnum:σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hf.2.1
  have hden:σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hf.2.2.1
  have hfirst:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B array cursor words q.num (.var "rat.n") h1 (by omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars,Ne.symm hfresh])
  obtain ⟨ν,hrn,hnPost⟩:=hfirst σ ⟨⟨hp,hpos,by omega,
    by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩⟩,hden⟩
  have hroomν:(words ++ [q.num]).length < (ν.arrs array).length:=by
    rw [RamFrames.run_array_length hrn array,List.length_append,List.length_singleton]; exact hroom
  obtain ⟨τ,hrd,hdPost⟩:=RamWordBuffer.append_spec B array cursor (words ++ [q.num]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ν
      ⟨hnPost.1.1,by simpa only [List.length_append,List.length_singleton] using hnPost.1.2,hroomν,
        by rw [evalB_var_iff]; exact ⟨hnPost.2.symm,hnPost.2 ▸ hd⟩⟩
  refine ⟨τ,hrn.seq hrd,?_,?_⟩
  · simpa only [Lax455465.RationalEncoding.encodeRational,List.append_assoc,List.cons_append,List.nil_append] using hdPost.1
  · simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hdPost.2

end Lax455465Proofs.RamUnsignedEncoding

end

section

namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (words:List ℕ) (array cursor:String) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ RamUnsignedBuffer.encode (qs.take (σ.vars index))) array σ∧
    σ.vars cursor=words.length+2*σ.vars index∧
    words.length+2*qs.length < (σ.arrs array).length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit array cursor:String)
    (qs:List ℚ≥0) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+2*qs.length+2 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput (qs[i]:ℚ) τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:cursor∉ body.wvars)
    (hbodyArray:array∉ body.warrs)
    (hemitIndex:index∉ (RamUnsignedEncoding.command array cursor).wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B (RamUnsignedEncoding.command array cursor) σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ cursor) (hcursorDen:cursor ≠ "rat.d"):
    Spec B (fun σ => R σ∧ Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length+2*qs.length < (σ.arrs array).length) (command index limit array cursor body)
      (fun _ τ => R τ∧ Prefix (words ++ RamUnsignedBuffer.encode qs) array τ∧
        τ.vars cursor=words.length+2*qs.length) ((K+22)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words array cursor σ∧ σ.vars index < qs.length)
      (step index array cursor body) (fun σ τ => Invariant R index qs words array cursor τ∧ τ.vars index=σ.vars index+1)
      (K+18):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ RamUnsignedBuffer.encode (qs.take i)).length=words.length+2*i:=by
      simp only [List.length_append,RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars cursor=words.length+2*i:=
      (hproduce.frame_var cursor hbodyPosition).trans hpos
    have hpν:Prefix (words ++ RamUnsignedBuffer.encode (qs.take i)) array ν:=by
      simpa only [Prefix,hproduce.frame_arr array hbodyArray] using hp
    have hroomν:words.length+2*qs.length < (ν.arrs array).length:=by
      rwa [RamFrames.run_array_length hproduce array]
    obtain ⟨μ,hemit,hemitted⟩:=RamUnsignedEncoding.command_spec B array cursor qs[i] (words ++ RamUnsignedBuffer.encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) hcursorDen ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+2*qs.length < (μ.arrs array).length:=by
      rwa [RamFrames.run_array_length hemit array]
    have hpμ:Prefix (words ++ RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars cursor=words.length+2*(i+1):=by rw [hpLen] at hemitted; omega
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
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words array cursor) qs.length (K+18)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words array cursor (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamUnsignedVector

end

section

namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

@[simp] theorem length_values {n:ℕ} (d:Matrix n):(values d).length=n*n:=List.length_ofFn

theorem value_at {n:ℕ} (d:Matrix n) (u v:Fin n):
    (values d)[(edgeIndex n (u,v)).val]'(by simpa only [length_values] using (edgeIndex n (u,v)).isLt)=d u v:=by
  simp only [values,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

end Lax455465Proofs.MetricMatrix

end

section

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

theorem indices_spec (B:ℕ) {n:ℕ} (u v:Fin n) (hn:n < B) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "metric.u"=u.val∧ τ.vars "metric.v"=v.val) 10:=by
  have he:(edgeIndex n (u,v)).val < B:=(edgeIndex n (u,v)).isLt.trans hn2
  have hu:u.val < B:=u.isLt.trans hn
  have hv:v.val < B:=v.isLt.trans hn
  have hmul:u.val*n < B:=by rw [FlowLpIndices.edge_value] at he; omega
  have hdiv:=FlowLpIndices.edge_div u v
  have hmod:=FlowLpIndices.edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,heσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "metric.u") (@Fin.val n u)) (@Eq Nat (Env.vars τ "metric.v") (@Fin.val n v))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "metric.entry") (Env.vars σ "metric.n"); let c2:Env:=Env.setVar σ "metric.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "metric.entry"; let c5:Nat:=c3 "metric.u"; let c6:Nat:=c3 "metric.n"; let c7:Nat:=Nat.mul c5 c6; let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c4 c7; let c9:Env:=Env.setVar c2 "metric.v" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))); let c13:Expr:=Expr.sub (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")); let c14:Nat:=c11 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B indices σ σ' ((10:Nat))) (c0 σ')) c9 (@And.intro (Run B indices σ c9 ((10:Nat))) (c0 c9) (RunStep.mono B indices σ c9 (c10 c12 c14) ((10:Nat)) (RunStep.seq B (Com.assign "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))) (Com.assign "metric.v" c13) σ c2 c9 c12 c14 (RunStep.assign B σ "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n")) c1 (RunStep.eval_div B σ (Expr.var "metric.entry") (Expr.var "metric.n") (Env.vars σ "metric.entry") (Env.vars σ "metric.n") (RunStep.eval_var B σ "metric.entry" (?nAX_g6217_0_0_0)) (RunStep.eval_var B σ "metric.n" (?nAX_g6217_0_0_1)) ?_)) (RunStep.assign B c2 "metric.v" c13 c8 (RunStep.eval_sub B c2 (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) c4 c7 (RunStep.eval_var B c2 "metric.entry" (?nAX_g6217_0_0_2)) (RunStep.eval_mul B c2 (Expr.var "metric.u") (Expr.var "metric.n") c5 c6 (RunStep.eval_var B c2 "metric.u" ?_) (RunStep.eval_var B c2 "metric.n" (?nAX_g6217_0_0_3)) ?_) (?nAX_g6217_0_0_4)))) (?nAX_g6217_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6217_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FlowLpIndices.edge_value]

end Lax455465Proofs.RamDualDistancesInit

end

section

namespace Lax455465Proofs.RamUnsignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem copy_spec (B:ℕ) (q:ℚ≥0) (side:String) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:side ++ ".s" ≠ "rat.n" ∧ side ++ ".s" ≠ "rat.d" ∧ side ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (copy side)
      (fun _ τ => τ.vars (side ++ ".s")=0∧ τ.vars (side ++ ".n")=q.num∧
        τ.vars (side ++ ".d")=q.den) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) side; let c1:String:=c0 ".s"; let c2:String:=c0 ".n"; let c3:String:=c0 ".d"; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ c1) ((0:Nat))) (And (@Eq Nat (Env.vars τ c2) (NNRat.num q)) (@Eq Nat (Env.vars τ c3) (NNRat.den q)))) σ; let c5:Env:=Env.setVar σ c1 ((0:Nat)); let c6:Nat:=Env.vars c5 "rat.n"; let c7:Env:=Env.setVar c5 c2 c6; let c8:Nat:=Env.vars c7 "rat.d"; let c9:Env:=Env.setVar c7 c3 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c2 (Expr.var "rat.n"); let c17:Com:=Com.assign c3 (Expr.var "rat.d"); let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B (copy side) σ σ' ((6:Nat))) (c4 σ')) c9 (@And.intro (Run B (copy side) σ c9 ((6:Nat))) (c4 c9) (RunStep.mono B (copy side) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c1 (Expr.lit ((0:Nat)))) (Com.seq c16 c17) σ c5 c9 c12 c15 (RunStep.assign B σ c1 (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6226_0_0_0))) (RunStep.seq B c16 c17 c5 c7 c9 c13 c14 (RunStep.assign B c5 c2 (Expr.var "rat.n") c6 (RunStep.eval_var B c5 "rat.n" ?_)) (RunStep.assign B c7 c3 (Expr.var "rat.d") c8 (RunStep.eval_var B c7 "rat.d" ?_)))) (?nAX_g6226_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6226_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6226_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem value (q:ℚ≥0):fractionValue 0 q.num q.den=(q:ℚ):=by
  simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
  exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)

theorem add_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) addFraction
      (fun _ τ => FractionOutput ((a+b:ℚ≥0):ℚ) τ) (36*(a.den*b.den).size+96):=by
  simpa only [value,NNRat.coe_add] using addFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos

end Lax455465Proofs.RamUnsignedArithmetic

end

section

namespace Lax455465Proofs.RamMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem left_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (fun σ => σ.vars "left.s"=0∧ σ.vars "left.n"=q.num∧ σ.vars "left.d"=q.den)
      left (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  have hvalue:fractionValue 0 q.num q.den=(q:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)
  rintro σ ⟨hs,hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c2:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c1; let c3:Nat:=Env.vars c2 "left.d"; let c4:Env:=Env.setVar c2 "rat.d" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "left.s")); let c8:Nat:=c6 (Expr.size (Expr.var "left.n")); let c9:Nat:=c6 (Expr.size (Expr.var "left.d")); let c10:Nat:=c5 c8 c9; @Exists.intro Env (fun (σ':Env) => And (Run B left σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B left σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B left σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c4 c7 c10 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" (?nAX_g6232_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c1 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g6232_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.var "left.d") c3 (RunStep.eval_var B c2 "left.d" (?nAX_g6232_0_0_2))))) (?nAX_g6232_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6232_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem right_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (fun σ => σ.vars "right.s"=0∧ σ.vars "right.n"=q.num∧ σ.vars "right.d"=q.den)
      right (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  have hvalue:fractionValue 0 q.num q.den=(q:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)
  rintro σ ⟨hs,hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "right.n"; let c2:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "rat.n" c1; let c3:Nat:=Env.vars c2 "right.d"; let c4:Env:=Env.setVar c2 "rat.d" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "right.s")); let c8:Nat:=c6 (Expr.size (Expr.var "right.n")); let c9:Nat:=c6 (Expr.size (Expr.var "right.d")); let c10:Nat:=c5 c8 c9; @Exists.intro Env (fun (σ':Env) => And (Run B right σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B right σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B right σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "right.s")) (Com.seq (Com.assign "rat.n" (Expr.var "right.n")) (Com.assign "rat.d" (Expr.var "right.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "right.s")) c4 c7 c10 (RunStep.assign B σ "rat.s" (Expr.var "right.s") (Env.vars σ "right.s") (RunStep.eval_var B σ "right.s" (?nAX_g6233_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "right.n")) (Com.assign "rat.d" (Expr.var "right.d")) (Env.setVar σ "rat.s" (Env.vars σ "right.s")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "rat.n" (Expr.var "right.n") c1 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "right.n" (?nAX_g6233_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.var "right.d") c3 (RunStep.eval_var B c2 "right.d" (?nAX_g6233_0_0_2))))) (?nAX_g6233_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6233_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (min (a:ℚ) (b:ℚ)) τ) 50:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have ha:fractionValue 0 a.num a.den=(a:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den a)
  have hb:fractionValue 0 b.num b.den=(b:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den b)
  rintro σ hinputs
  obtain ⟨ν,hcompare,hpost⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den
    hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos σ hinputs
  have hinputsν:fractionInputs 0 a.num a.den 0 b.num b.den ν:=by
    simpa only [fractionInputs,hcompare.frame_var "left.s" (by decide),hcompare.frame_var "left.n" (by decide),
      hcompare.frame_var "left.d" (by decide),hcompare.frame_var "right.s" (by decide),
      hcompare.frame_var "right.n" (by decide),hcompare.frame_var "right.d" (by decide)] using hinputs
  have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some (decide (ν.vars "cmp.le"=1)):=by
    rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1)]
    congr 1
  by_cases hab:(a:ℚ)≤ (b:ℚ)
  · have hflag:ν.vars "cmp.le"=1:=hpost.2.mpr (by rwa [ha,hb])
    obtain ⟨τ,hr,ht⟩:=left_spec B a h1 (han.trans_lt hM) (had.trans_lt hM) ν
      ⟨hinputsν.1,hinputsν.2.1,hinputsν.2.2.1⟩
    refine ⟨τ,hcompare.seq (Run.ite_true (by simpa only [hflag,decide_true] using hc) hr),?_⟩
    simpa only [min_eq_left hab] using ht
  · have hflag:¬ν.vars "cmp.le"=1:=fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    obtain ⟨τ,hr,ht⟩:=right_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hinputsν.2.2.2
    refine ⟨τ,hcompare.seq (Run.ite_false (by simpa only [hflag,decide_false] using hc) hr),?_⟩
    simpa only [min_eq_right (le_of_not_ge hab)] using ht

end Lax455465Proofs.RamMinimum

end

section

namespace Lax455465Proofs.RamUnsignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def Stored (q:ℚ≥0) (σ:Env):Prop:=σ.vars "fold.n"=q.num∧ σ.vars "fold.d"=q.den

theorem load_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) load (fun _ τ => τ.vars "right.s"=0∧ τ.vars "right.n"=q.num∧ τ.vars "right.d"=q.den) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "right.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "right.n") (NNRat.num q)) (@Eq Nat (Env.vars τ "right.d") (NNRat.den q)))) σ; let c1:Env:=Env.setVar σ "right.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "right.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "right.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; let c12:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B load σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B load σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B load σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6296_0_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "right.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6296_0_0_1))) (RunStep.assign B c3 "right.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6296_0_0_2))))) (?nAX_g6296_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6296_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem save_spec (B:ℕ) (q:ℚ≥0) (hn:q.num < B) (hd:q.den < B):
    Spec B (FractionOutput (q:ℚ)) save (fun _ τ => Stored q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 ((1:Nat)); let c4:Nat:=c3 (Expr.size (Expr.var "rat.n")); let c5:Nat:=c3 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B save σ σ' ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ σ')) c1 (@And.intro (Run B save σ c1 ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ c1) (RunStep.mono B save σ c1 (c2 c4 c5) ((4:Nat)) (RunStep.seq B (Com.assign "fold.n" (Expr.var "rat.n")) (Com.assign "fold.d" (Expr.var "rat.d")) σ (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) c1 c4 c5 (RunStep.assign B σ "fold.n" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6297_0_0_0))) (RunStep.assign B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d" (?nAX_g6297_0_0_1)))) (?nAX_g6297_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6297_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem finish_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) finish (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "rat.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "rat.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; @Exists.intro Env (fun (σ':Env) => And (Run B finish σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B finish σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B finish σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6298_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "rat.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6298_0_0_1))) (RunStep.assign B c3 "rat.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6298_0_0_2))))) (?nAX_g6298_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6298_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem combine_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hsn:(a+b).num < B) (hsd:(a+b).den < B):
    Spec B (fun σ => FractionOutput (a:ℚ) σ∧ Stored b σ) combine
      (fun _ τ => Stored (a+b) τ) (36*(M^2).size+112):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) σ ha
  have hbν:Stored b ν:=by
    simpa only [Stored,rleft.frame_var "fold.n" (by decide),rleft.frame_var "fold.d" (by decide)] using hb
  obtain ⟨μ,rright,pright⟩:=load_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hbν
  have paμ:μ.vars "left.s"=0∧ μ.vars "left.n"=a.num∧ μ.vars "left.d"=a.den:=by
    simpa only [rright.frame_var "left.s" (by decide),rright.frame_var "left.n" (by decide),rright.frame_var "left.d" (by decide),String.reduceAppend] using pleft
  obtain ⟨ξ,radd,padd⟩:=RamUnsignedArithmetic.add_spec B M a b hB han had hbn hbd μ
    ⟨paμ.1,paμ.2.1,paμ.2.2,pright⟩
  obtain ⟨τ,rsave,psave⟩:=save_spec B (a+b) hsn hsd ξ padd
  refine ⟨τ,(rleft.seq (rright.seq (radd.seq rsave))).mono ?_,psave⟩
  have hprod:a.den*b.den≤ M^2:=by nlinarith [Nat.mul_le_mul had hbd]
  have hsize:=Nat.size_le_size hprod
  omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧ Stored (qs.take (σ.vars index)).sum σ

set_option maxHeartbeats 0 in

theorem command_spec (B M K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ≥0) (body:Com) (hB:2*M^2+3 < B) (hlen:qs.length < B)
    (hnum:∀ q∈ qs,q.num≤ M) (hden:∀ q∈ qs,q.den≤ M)
    (hprefixNum:∀ i, (qs.take i).sum.num≤ M) (hprefixDen:∀ i, (qs.take i).sum.den≤ M)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k name,R σ→ name=index∨ name="fold.n" ∨ name="fold.d" → R (σ.setVar name k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ FractionOutput (qs[i]:ℚ) τ) K)
    (hfresh:index ≠ "fold.n" ∧ index ≠ "fold.d" ∧ index∉ combine.wvars)
    (hbodyIndex:index∉ body.wvars) (hbodySum:"fold.n" ∉ body.wvars∧ "fold.d" ∉ body.wvars)
    (hcombineFrame:∀ {σ τ:Env} {k:ℕ},Run B combine σ τ k→ R σ→ R τ)
    (hfinishFrame:∀ {σ τ:Env} {k:ℕ},Run B finish σ τ k→ R σ→ R τ):
    Spec B R (command index limit body)
      (fun _ τ => R τ∧ FractionOutput ((qs.sum:ℚ≥0):ℚ) τ)
      ((K+36*(M^2).size+120)*qs.length+16):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hstep:Spec B (fun σ => Invariant R index qs σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs τ∧ τ.vars index=σ.vars index+1)
      (K+36*(M^2).size+116):=by
    rintro σ ⟨⟨hR,hi,hstored⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    obtain ⟨ν,rbody,pbody⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(rbody.frame_var index hbodyIndex).trans rfl
    have hstoredν:Stored (qs.take i).sum ν:=by
      simpa only [Stored,rbody.frame_var "fold.n" hbodySum.1,rbody.frame_var "fold.d" hbodySum.2] using hstored
    have hq:qs[i]∈ qs:=List.getElem_mem hi'
    have hsum:qs[i]+(qs.take i).sum=(qs.take (i+1)).sum:=by
      rw [List.take_succ_eq_append_getElem hi',List.sum_append,List.sum_singleton,add_comm]
    obtain ⟨μ,rcombine,pcombine⟩:=combine_spec B M qs[i] (qs.take i).sum hB
      (hnum _ hq) (hden _ hq) (hprefixNum i) (hprefixDen i)
      (by rw [hsum]; exact (hprefixNum (i+1)).trans_lt hM)
      (by rw [hsum]; exact (hprefixDen (i+1)).trans_lt hM) ν ⟨pbody.2,hstoredν⟩
    have hiμ:μ.vars index=i:=(rcombine.frame_var index hfresh.2.2).trans hiν
    have hRμ:=hcombineFrame rcombine pbody.1
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨μ.setVar index (i+1),(rbody.seq (rcombine.seq hinc)).mono (by omega),?_,?_⟩
    · refine ⟨hset μ (i+1) index hRμ (Or.inl rfl),by simp; omega,?_⟩
      simpa only [Stored,vars_setVar,if_neg (Ne.symm hfresh.1),if_neg (Ne.symm hfresh.2.1),if_pos rfl,if_true,hsum] using pcombine
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs) qs.length
    (K+36*(M^2).size+116) hlen (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "fold.n" 0).setVar "fold.d" 1
  have rinit:Run B init σ ν 4:=by
    exact (Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit h1))
  have hRν:R ν:=hset _ 1 "fold.d" (hset σ 0 "fold.n" hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have hinvariant:Invariant R index qs (ν.setVar index 0):=by
    refine ⟨hset ν 0 index hRν (Or.inl rfl),by simp,?_⟩
    simp [Stored,ν,Ne.symm hfresh.1,Ne.symm hfresh.2.1]
  obtain ⟨μ,rscan,pscan⟩:=hscan ν hinvariant
  have hstoredμ:Stored qs.sum μ:=by simpa only [pscan.2,List.take_length] using pscan.1.2.2
  have hfinalNum:qs.sum.num≤ M:=by simpa only [List.take_length] using hprefixNum qs.length
  have hfinalDen:qs.sum.den≤ M:=by simpa only [List.take_length] using hprefixDen qs.length
  obtain ⟨τ,rfinish,pfinish⟩:=finish_spec B qs.sum h1 (hfinalNum.trans_lt hM) (hfinalDen.trans_lt hM) μ hstoredμ
  refine ⟨τ,(rinit.seq (rscan.seq rfinish)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hfinishFrame rfinish pscan.1.1,pfinish⟩

end Lax455465Proofs.RamUnsignedSum

end

section

namespace Lax455465Proofs.RamUnsignedScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem load_spec (B:ℕ) (name:String) (q:ℚ≥0) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:name ++ ".n" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  have hns:=Ne.symm hfresh.1
  have hds:=Ne.symm hfresh.2.1
  have hdn:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c3:String:=c2 ".n"; let c4:Nat:=Env.vars c1 c3; let c5:Env:=Env.setVar c1 "rat.n" c4; let c6:String:=c2 ".d"; let c7:Nat:=Env.vars c5 c6; let c8:Env:=Env.setVar c5 "rat.d" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c12:Expr:=Expr.var c3; let c13:Nat:=c10 (Expr.size c12); let c14:Expr:=Expr.var c6; let c15:Nat:=c10 (Expr.size c14); let c16:Nat:=c9 c13 c15; let c17:Com:=Com.assign "rat.n" c12; let c18:Com:=Com.assign "rat.d" c14; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) (c0 σ')) c8 (@And.intro (Run B (load name) σ c8 ((6:Nat))) (c0 c8) (RunStep.mono B (load name) σ c8 (c9 c11 c16) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c17 c18) σ c1 c8 c11 c16 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6578_0_0_0))) (RunStep.seq B c17 c18 c1 c5 c8 c13 c15 (RunStep.assign B c1 "rat.n" c12 c4 (RunStep.eval_var B c1 c3 ?_)) (RunStep.assign B c5 "rat.d" c14 c7 (RunStep.eval_var B c5 c6 ?_)))) (?nAX_g6578_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6578_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6578_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem save_spec (B:ℕ) (name:String) (q:ℚ≥0)
    (hn:q.num < B) (hd:q.den < B) (hfresh:name ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (save name) (fun _ τ => Stored name q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hdn:=Ne.symm hfresh
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".n"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.n"); let c4:String:=c1 ".d"; let c5:Nat:=Env.vars c3 "rat.d"; let c6:Env:=Env.setVar c3 c4 c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.var "rat.n")); let c10:Nat:=c8 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((4:Nat))) (c0 σ')) c6 (@And.intro (Run B (save name) σ c6 ((4:Nat))) (c0 c6) (RunStep.mono B (save name) σ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.n")) (Com.assign c4 (Expr.var "rat.d")) σ c3 c6 c9 c10 (RunStep.assign B σ c2 (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6579_0_0_0))) (RunStep.assign B c3 c4 (Expr.var "rat.d") c5 (RunStep.eval_var B c3 "rat.d" ?_))) (?nAX_g6579_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6579_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6579_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

end Lax455465Proofs.RamUnsignedScalar

end

section

namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B:ℕ) (mode:Option Bool) (a b:Bool) (h1:1 < B):
    Spec B (fractionInputs 0 (bit a).num 1 0 (bit b).num 1) (command mode)
      (fun _ τ => FractionOutput (bit (flag mode a b):ℚ) τ) 10:=by
  cases mode with
  | none =>
    cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega
  | some mode =>
    cases mode <;> cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                               )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega

end Lax455465Proofs.RamBooleanArithmetic

end

section

namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

@[simp] theorem length_coefficients (qs ms:List ℚ≥0):(coefficients qs ms).length=qs.length:=List.length_ofFn

def Context (source mask:String) (qs ms:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=qs.length∧ Prefix (RamUnsignedBuffer.encode qs) source σ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem coefficient_at (qs ms:List ℚ≥0) (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length):
    (coefficients qs ms)[i]'(by simpa only [coefficients,List.length_ofFn] using hi) =
      if (ms[i]'(by omega)).num=1 then qs[i] else 0:=by
  simp only [coefficients,List.getElem_ofFn,List.getD_eq_get ms 0 (⟨i,by omega⟩:Fin ms.length)]
  rfl

theorem entry_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length) (hB:2*M^2+3 < B)
    (hindex:2*i+1 < B) (hqn:qs[i].num≤ M) (hqd:qs[i].den≤ M)
    (hmn:(ms[i]'(by omega)).num≤ M) (hmd:(ms[i]'(by omega)).den≤ M):
    Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]'(by simpa only [length_coefficients] using hi):ℚ) τ) 32:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hmi:i < ms.length:=by omega
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rm,pm⟩:=RamUnsignedBuffer.read_spec B mask "sum.i" ms i hmi (by nlinarith) hindex
    (hmn.trans_lt hM) (hmd.trans_lt hM) (by decide) σ ⟨hctx.2.2,hidx⟩
  have hnum:ν.vars "rat.n"=ms[i].num:=by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  have hctxν:Context source mask qs ms ν:=by
    simpa only [Context,Prefix,rm.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rm.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
      rm.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctx
  have hidxν:ν.vars "sum.i"=i:=(rm.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hidx
  have hc:(Cond.eq (.var "rat.n") (.lit 1)).evalB B ν=some (decide (ms[i].num=1)):=by
    rw [evalB_condEq (evalB_var (hnum ▸ hmn.trans_lt hM)) (evalB_lit h1),hnum]
    congr 1
  by_cases hm:ms[i].num=1
  · obtain ⟨τ,rq,pq⟩:=RamUnsignedBuffer.read_spec B source "sum.i" qs i hi (by nlinarith) hindex
      (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ν ⟨hctxν.2.1,hidxν⟩
    have rr:=rm.seq (Run.ite_true (d:=RamFractionPrimitives.zero) (by simpa only [hm,decide_true] using hc) rq)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rq.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
        rq.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
        rq.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_pos hm] using pq.1
  · obtain ⟨τ,rz,pz⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    have rr:=rm.seq (Run.ite_false (c:=RamUnsignedBuffer.read source "sum.i") (by simpa only [hm,decide_false] using hc) rz)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rz.frame_var "sum.count" (by decide),rz.frame_arr source (by change source∉ ([]:List String); simp),
        rz.frame_arr mask (by change mask∉ ([]:List String); simp)] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_neg hm,NNRat.coe_zero] using pz

theorem command_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (hB:2*M^2+3 < B) (hindex:2*qs.length+2 < B)
    (hqn:∀ q∈ qs,q.num≤ M) (hqd:∀ q∈ qs,q.den≤ M)
    (hmn:∀ q∈ ms,q.num≤ M) (hmd:∀ q∈ ms,q.den≤ M)
    (hprefixNum:∀ i, ((coefficients qs ms).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((coefficients qs ms).take i).sum.den≤ M):
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput (((coefficients qs ms).sum:ℚ≥0):ℚ) τ)
      ((36*(M^2).size+152)*qs.length+16):=by
  have hM1:1≤ M:=by simpa only [List.take_zero,List.sum_nil,NNRat.den_zero] using hprefixDen 0
  have hnum:∀ q∈ coefficients qs ms,q.num≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqn _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.num_zero] using Nat.zero_le M
  have hden:∀ q∈ coefficients qs ms,q.den≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqd _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.den_zero] using hM1
  have hbody:∀ i, ∀ hi:i < (coefficients qs ms).length,
      Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
        (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]:ℚ) τ) 32:=by
    intro i hi
    have hq:i < qs.length:=by simpa only [length_coefficients] using hi
    have hm:i < ms.length:=by omega
    exact entry_spec B M source mask qs ms hlen i hq hB (by omega)
      (hqn _ (List.getElem_mem hq)) (hqd _ (List.getElem_mem hq))
      (hmn _ (List.getElem_mem hm)) (hmd _ (List.getElem_mem hm))
  have hf:=RamUnsignedSum.command_spec B M 32 (Context source mask qs ms)
    "sum.i" "sum.count" (coefficients qs ms) (entry source mask) hB
    (by rw [length_coefficients]; omega) hnum hden hprefixNum hprefixDen
    (fun _ h => by simpa only [length_coefficients] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
  unfold command
  rw [length_coefficients] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamMaskedSum

end

section

namespace Lax455465Proofs.MaskedMassData

open LpInputSize
open scoped BigOperators NNRat

theorem coefficients_ofFn {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    RamMaskedSum.coefficients (List.ofFn weights) (flags mask) =
      List.ofFn (fun v => if mask v then weights v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,List.length_ofFn]
  · intro i hi hj
    have hn:i < n:=by simpa only [RamMaskedSum.length_coefficients,List.length_ofFn] using hi
    rw [RamMaskedSum.coefficient_at (List.ofFn weights) (flags mask) (by simp [flags]) i (by simpa using hn)]
    simp only [flags,List.getElem_ofFn]
    cases h:mask ⟨i,hn⟩ <;> simp [h]

theorem coe_sum {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    (((RamMaskedSum.coefficients (List.ofFn weights) (flags mask)).sum:ℚ≥0):ℚ) =
      ∑ v,if mask v then (weights v:ℚ) else 0:=by
  rw [coefficients_ofFn,List.sum_ofFn,NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  cases mask v <;> rfl

end Lax455465Proofs.MaskedMassData

end

section

namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def Context {n:ℕ} (source:String) (mask:Fin n→ Bool) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags mask)) source σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {source:String} {mask:Fin n→ Bool} (h:Context source mask σ)
    (ha:source∉ cmd.warrs) (hx:∀ x∈ ["metric.n","metric.n2"],x∉ cmd.wvars):
    Context source mask τ:=by
  simpa only [Context,Prefix,hr.frame_arr source ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

theorem coefficient_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source:String)
    (mask:Fin n→ Bool) (u v:Fin n) (h2:2 < B) (hn:n < B) (hn2:n*n < B)
    (hindex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val)
      (coefficient mode source)
      (fun _ τ => Context source mask τ∧ FractionOutput ((matrix mode mask u v:ℚ≥0):ℚ) τ) 60:=by
  let qs:=MaskedMassData.flags mask
  have hlen:qs.length=n:=List.length_ofFn
  have hvalue (t:Fin n):qs[t.val]=RamBooleanArithmetic.bit (mask t):=by
    simp only [qs,MaskedMassData.flags,List.getElem_ofFn,RamBooleanArithmetic.bit]
  have hnum (t:Fin n):qs[t.val].num < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hden (t:Fin n):qs[t.val].den < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨σ₁,r₁,p₁⟩:=RamDualDistancesInit.indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctx₁:=frame r₁ hctx (by simp [RamDualDistancesInit.indices,Com.warrs]) (by decide)
  obtain ⟨σ₂,r₂,p₂⟩:=RamUnsignedBuffer.read_spec B source "metric.u" qs u.val
    (by simpa only [hlen] using u.isLt) h2 (by omega) (hnum u) (hden u) (by decide) σ₁ ⟨hctx₁.2.2,p₁.1⟩
  obtain ⟨σ₃,r₃,p₃⟩:=RamUnsignedArithmetic.copy_spec B qs[u.val] "left" (by omega)
    (hnum u) (hden u) (by decide) σ₂ p₂.1
  have hctx₃:=frame r₃ (frame r₂ hctx₁ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hv₃:σ₃.vars "metric.v"=v.val:=
    (r₃.frame_var _ (by decide)).trans ((r₂.frame_var _ (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)).trans p₁.2)
  obtain ⟨σ₄,r₄,p₄⟩:=RamUnsignedBuffer.read_spec B source "metric.v" qs v.val
    (by simpa only [hlen] using v.isLt) h2 (by omega) (hnum v) (hden v) (by decide) σ₃ ⟨hctx₃.2.2,hv₃⟩
  obtain ⟨σ₅,r₅,p₅⟩:=RamUnsignedArithmetic.copy_spec B qs[v.val] "right" (by omega)
    (hnum v) (hden v) (by decide) σ₄ p₄.1
  have hctx₅:=frame r₅ (frame r₄ hctx₃ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hleft:σ₅.vars "left.s"=0∧ σ₅.vars "left.n"=(RamBooleanArithmetic.bit (mask u)).num∧ σ₅.vars "left.d"=1:=by
    rw [r₅.frame_var "left.s" (by decide),r₅.frame_var "left.n" (by decide),r₅.frame_var "left.d" (by decide),
      r₄.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)]
    have hp:=p₃
    rw [hvalue u] at hp
    cases hu:mask u <;> simpa [RamBooleanArithmetic.bit,hu] using hp
  have hright:σ₅.vars "right.s"=0∧ σ₅.vars "right.n"=(RamBooleanArithmetic.bit (mask v)).num∧ σ₅.vars "right.d"=1:=by
    have hp:=p₅
    rw [hvalue v] at hp
    cases hv:mask v <;> simpa [RamBooleanArithmetic.bit,hv] using hp
  obtain ⟨τ,r₆,p₆⟩:=RamBooleanArithmetic.command_spec B mode (mask u) (mask v) (by omega) σ₅
    ⟨hleft.1,hleft.2.1,hleft.2.2,hright.1,hright.2.1,hright.2.2⟩
  refine ⟨τ,r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))),
    frame r₆ hctx₅ (by cases mode with | none => simp [RamBooleanArithmetic.command,Com.warrs] | some b => cases b <;> simp [RamBooleanArithmetic.command,Com.warrs])
      (by cases mode with | none => decide | some b => cases b <;> decide),p₆⟩

theorem command_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source target:String)
    (mask:Fin n→ Bool) (hneq:source ≠ target) (h2:2 < B) (hn:n < B)
    (hn2:n*n < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ 2*(n*n) < (σ.arrs target).length)
      (command mode source target)
      (fun _ τ => Context source mask τ∧ Prefix (RamUnsignedBuffer.encode (values (matrix mode mask))) target τ)
      (82*(n*n)+8):=by
  let qs:=values (matrix mode mask)
  have hlen:qs.length=n*n:=length_values _
  have hwords:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    simp only [qs,values,matrix,List.getElem_ofFn]
    cases RamBooleanArithmetic.flag mode (mask _) (mask _) <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=i)
        (coefficient mode source) (fun _ τ => Context source mask τ∧ FractionOutput (qs[i]:ℚ) τ) 60:=by
    intro i hi
    have he:i < n*n:=by rwa [hlen] at hi
    let uv:=(edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
    have hidx:edgeIndex n uv=(⟨i,he⟩:Fin (n*n)):=(edgeIndex n).apply_symm_apply _
    simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
      coefficient_spec B mode source mask uv.1 uv.2 h2 hn hn2 hvertex
  have hfresh (x:String) (h:x∈ ["metric.entry","mask.position"]):
      x∉ (coefficient mode source).wvars:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
  have hloop:=RamUnsignedVector.command_spec B 60 (Context source mask)
    "metric.entry" "metric.n2" target "mask.position" qs [] (coefficient mode source) (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (hfresh _ (by simp)) (hfresh _ (by simp))
    (by cases mode with
      | none => simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs]
      | some b => cases b <;> simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs])
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => frame rr h (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])
      (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "mask.position" 0
  have rzero:Run B (.assign "mask.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:=frame rzero hctx (by simp [Com.warrs]) (by decide)
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamArcMask

end

section

namespace Lax455465Proofs.RamBallMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def Context (array:String) (qs:List ℚ≥0) (radius:ℚ≥0) (σ:Env):Prop:=
  σ.vars "ball.count"=qs.length∧ Stored "region.radius" radius σ∧
    Prefix (RamUnsignedBuffer.encode qs) array σ

theorem entry_spec (B M:ℕ) (array:String) (qs:List ℚ≥0) (radius:ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (hB:2*M^2+3 < B) (hindex:2*qs.length+2 < B)
    (hrn:radius.num≤ M) (hrd:radius.den≤ M) (hqn:qs[i].num≤ M) (hqd:qs[i].den≤ M):
    Spec B (fun σ => Context array qs radius σ∧ σ.vars "ball.i"=i) (entry array)
      (fun _ τ => Context array qs radius τ∧ FractionOutput (flag qs[i] radius:ℚ) τ) 82:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rload,pload⟩:=load_spec B "region.radius" radius h1 (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ hctx.2.1
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B radius "left" h1
    (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) ν pload
  have hpμ:Prefix (RamUnsignedBuffer.encode qs) array μ:=by
    have rr:=rload.seq rl
    simpa only [Prefix,rr.frame_arr array (by change array∉ ([]:List String); simp)] using hctx.2.2
  have hiμ:μ.vars "ball.i"=i:=by
    have rr:=rload.seq rl
    exact (rr.frame_var "ball.i" (by decide)).trans hidx
  obtain ⟨ξ,rq,pq⟩:=RamUnsignedBuffer.read_spec B array "ball.i" qs i hi (by nlinarith) (by omega)
    (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) μ ⟨hpμ,hiμ⟩
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B qs[i] "right" h1
    (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ξ pq.1
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=radius.num∧ η.vars "left.d"=radius.den:=by
    have r:=rq.seq rr
    simpa only [r.frame_var "left.s" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.d" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨ζ,rc,pc⟩:=RamComparison.compareFraction_spec B M 0 radius.num radius.den 0 qs[i].num qs[i].den
    hB (by omega) (by omega) hrn hrd hqn hqd radius.den_pos qs[i].den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  have hflag:ζ.vars "cmp.le"=1↔ (radius:ℚ)≤ (qs[i]:ℚ):=by
    simpa only [RamUnsignedArithmetic.value] using pc.2
  have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ζ=some (decide (ζ.vars "cmp.le"=1)):=by
    rw [evalB_condEq (evalB_var (pc.1.trans_lt h1)) (evalB_lit h1)]
    congr 1
  have preserve:∀ {τ:Env} {c:Com} {k:ℕ},Run B c σ τ k→
      array∉ c.warrs→ (∀ x∈ ["ball.count","region.radius.n","region.radius.d"],x∉ c.wvars)→ Context array qs radius τ:=by
    intro τ c k r ha hv
    simpa only [Context,Stored,Prefix,r.frame_arr array ha,
      r.frame_var "ball.count" (hv _ (by simp)),r.frame_var "region.radius.n" (hv _ (by simp)),
      r.frame_var "region.radius.d" (hv _ (by simp)),String.reduceAppend] using hctx
  by_cases hq:(qs[i]:ℚ) < (radius:ℚ)
  · have hf:¬ζ.vars "cmp.le"=1:=fun h => (not_le_of_gt hq) (hflag.mp h)
    obtain ⟨τ,rone,pone⟩:=RamFractionPrimitives.one_spec B h1 ζ trivial
    have branchRun:=Run.ite_false (c:=RamFractionPrimitives.zero) (by simpa only [hf,decide_false] using hc) rone
    have r:=rload.seq (rl.seq (rq.seq (rr.seq (rc.seq branchRun))))
    refine ⟨τ,r.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · exact preserve r (by change array∉ ([]:List String); simp) (by
        dsimp [Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    · simpa only [flag,if_pos hq,NNRat.coe_one] using pone
  · have hf:=hflag.mpr (le_of_not_gt hq)
    obtain ⟨τ,rzero,pzero⟩:=RamFractionPrimitives.zero_spec B h1 ζ trivial
    have branchRun:=Run.ite_true (d:=RamFractionPrimitives.one) (by simpa only [hf,decide_true] using hc) rzero
    have r:=rload.seq (rl.seq (rq.seq (rr.seq (rc.seq branchRun))))
    refine ⟨τ,r.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · exact preserve r (by change array∉ ([]:List String); simp) (by
        dsimp [Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    · simpa only [flag,if_neg hq,NNRat.coe_zero] using pzero

theorem command_spec (B M:ℕ) (source target:String) (qs:List ℚ≥0) (radius:ℚ≥0)
    (hneq:source ≠ target) (hB:2*M^2+3 < B) (hindex:2*qs.length+2 < B)
    (hrn:radius.num≤ M) (hrd:radius.den≤ M)
    (hnum:∀ q∈ qs,q.num≤ M) (hden:∀ q∈ qs,q.den≤ M):
    Spec B (fun σ => Context source qs radius σ∧ 2*qs.length < (σ.arrs target).length)
      (command source target) (fun _ τ => Context source qs radius τ∧
        Prefix (RamUnsignedBuffer.encode (qs.map (fun q => flag q radius))) target τ)
      (104*qs.length+8):=by
  have h1:1 < B:=by nlinarith
  let flags:=qs.map (fun q => flag q radius)
  have hlen:flags.length=qs.length:=by simp [flags]
  have hvalues:∀ i, ∀ hi:i < flags.length,flags[i].num < B∧ flags[i].den < B:=by
    intro i hi
    have hq:i < qs.length:=by omega
    have he:flags[i]=flag qs[i] radius:=by simp only [flags,List.getElem_map]
    rw [he]
    unfold flag
    split_ifs <;> norm_num <;> omega
  have hf:=RamUnsignedVector.command_spec B 82 (Context source qs radius)
    "ball.i" "ball.count" target "ball.pos" flags [] (entry source) h1
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hvalues i hi).1) (fun i hi => (hvalues i hi).2)
    (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false,String.reduceAppend] using h)
    (fun i hi => by
      have hq:i < qs.length:=by omega
      have hm:=List.getElem_mem hq
      simpa only [flags,List.getElem_map] using entry_spec B M source qs radius i hq hB hindex
        hrn hrd (hnum _ hm) (hden _ hm))
    (by dsimp [entry,Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    (by dsimp [entry,Com.wvars,load,RamUnsignedArithmetic.copy,RamUnsignedBuffer.read]; decide)
    (by change target∉ ([]:List String); simp)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "ball.count" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_var "region.radius.n" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_var "region.radius.d" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr source (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])] using h)
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "ball.pos" 0
  have rzero:Run B (.assign "ball.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:Context source qs radius ν:=by
    simpa only [Context,Stored,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false,String.reduceAppend] using hctx
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by rw [hlen]; omega),pr.1,by simpa only [flags,List.nil_append] using pr.2.1⟩

end Lax455465Proofs.RamBallMask

end

section

namespace Lax455465Proofs.BallMassData

open scoped BigOperators NNRat

theorem mask_eq {n:ℕ} (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    mask distance radius=MaskedMassData.flags (fun v => decide ((distance v:ℚ) < (radius:ℚ))):=by
  simp only [mask,List.map_ofFn,MaskedMassData.flags]
  congr 1
  funext v
  simp [RamBallMask.flag]

theorem coe_mass {n:ℕ} (weights distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    (mass weights distance radius:ℚ) =
      RegionSelection.ballMass (fun v => (weights v:ℚ)) (fun v => (distance v:ℚ)) radius:=by
  unfold mass
  rw [mask_eq,MaskedMassData.coe_sum]
  simp only [RegionSelection.ballMass,RegionCharging.ball,Finset.sum_filter,decide_eq_true_eq]

end Lax455465Proofs.BallMassData

end

section

namespace Lax455465Proofs.BoundaryData

open MetricMatrix
open scoped BigOperators NNRat

theorem masked_matrix {n:ℕ} (capacity flags:Matrix n):
    RamMaskedSum.coefficients (values capacity) (values flags) =
      values (fun u v => if (flags u v).num=1 then capacity u v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,length_values]
  · intro i hi hj
    have he:i < n*n:=by simpa only [RamMaskedSum.length_coefficients,length_values] using hi
    rw [RamMaskedSum.coefficient_at (values capacity) (values flags) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

theorem arc_condition {n:ℕ} (outward:Bool) (distance:Fin n→ ℚ≥0)
    (radius:ℚ≥0) (u v:Fin n):
    (arcs outward distance radius u v).num=1↔
      if outward then (distance u:ℚ)< radius∧ (radius:ℚ)≤ distance v
      else (distance v:ℚ)< radius∧ (radius:ℚ)≤ distance u:=by
  unfold arcs RamArcMask.matrix RamBooleanArithmetic.bit RamBooleanArithmetic.flag vertices
  cases outward <;> by_cases hu:(distance u:ℚ)< radius <;> by_cases hv:(distance v:ℚ)< radius <;>
    simp [hu,hv,le_of_not_gt] <;> exact_mod_cast (by assumption)

theorem coe_value {n:ℕ} (outward:Bool) (capacity:Matrix n)
    (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    (value outward capacity distance radius:ℚ) =
      RegionVolume.boundary (if outward then rational capacity else (fun u v => (capacity v u:ℚ)))
        (fun v => (distance v:ℚ)) (radius:ℚ):=by
  unfold value
  rw [masked_matrix]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,NNRat.cast_sum]
  cases outward with
  | true =>
    simp only [RegionVolume.boundary]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    simp only [arc_condition,if_true,Bool.false_eq_true,if_false]
    split_ifs <;> rfl
  | false =>
    simp only [Bool.false_eq_true,if_false,RegionVolume.boundary]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    simp only [arc_condition,if_true,Bool.false_eq_true,if_false]
    split_ifs <;> rfl

end Lax455465Proofs.BoundaryData

end

section

namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (value a b:ℚ) τ) (36*(a.den*b.den).size+142):=by
  have h1:1 < B:=by nlinarith
  have ha:=RamUnsignedArithmetic.value a
  have hb:=RamUnsignedArithmetic.value b
  rintro σ hinputs
  obtain ⟨ν,hcompare,hpost⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den
    hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos σ hinputs
  have hinputsν:fractionInputs 0 a.num a.den 0 b.num b.den ν:=by
    simpa only [fractionInputs,hcompare.frame_var "left.s" (by decide),hcompare.frame_var "left.n" (by decide),
      hcompare.frame_var "left.d" (by decide),hcompare.frame_var "right.s" (by decide),
      hcompare.frame_var "right.n" (by decide),hcompare.frame_var "right.d" (by decide)] using hinputs
  have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some (decide (ν.vars "cmp.le"=1)):=by
    rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1)]
    congr 1
  by_cases hab:(a:ℚ)≤ (b:ℚ)
  · have hflag:ν.vars "cmp.le"=1:=hpost.2.mpr (by rwa [ha,hb])
    obtain ⟨τ,hr,ht⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    refine ⟨τ,(hcompare.seq (Run.ite_true (d:=difference) (by simpa only [hflag,decide_true] using hc) hr)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simpa only [value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr hab)] using ht
  · have hflag:¬ν.vars "cmp.le"=1:=fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    let μ:=ν.setVar "right.s" 1
    have hr:Run B (.assign "right.s" (.lit 1)) ν μ 2:=Run.assign (evalB_lit h1)
    have hμ:fractionInputs 0 a.num a.den 1 b.num b.den μ:=by
      simpa [μ,fractionInputs,vars_setVar] using
        And.intro hinputsν.1 (And.intro hinputsν.2.1 (And.intro hinputsν.2.2.1 (And.intro (rfl:(1:ℕ)=1) hinputsν.2.2.2.2)))
    obtain ⟨τ,haRun,haPost⟩:=addFraction_spec B M 0 a.num a.den 1 b.num b.den hB
      (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos μ hμ
    have hdifference:Run B difference ν τ (36*(a.den*b.den).size+98):=by
      have hh:=hr.seq haRun
      unfold difference
      convert hh using 1 <;> omega
    refine ⟨τ,(hcompare.seq (Run.ite_false (c:=RamFractionPrimitives.zero) (by simpa only [hflag,decide_false] using hc) hdifference)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    have hnegative:fractionValue 1 b.num b.den=-(b:ℚ):=by
      simpa [fractionValue,neg_div] using congrArg Neg.neg hb
    change FractionOutput (max ((a:ℚ)-(b:ℚ)) 0) τ
    rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hab)),sub_eq_add_neg]
    simpa only [ha,hnegative] using haPost

end Lax455465Proofs.RamTruncatedSubtract

end

section

namespace Lax455465Proofs.RamScalarBinary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M K:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (operation:Com) (q:ℚ) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (hop:Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) operation
      (fun _ τ => FractionOutput q τ) K):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName operation) (fun _ τ => FractionOutput q τ) (K+24):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rleft
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,
      rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rright,pright⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1
    (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have pleftη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have rr:=rb.seq rright
    simpa only [rr.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),rr.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      rr.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pleft
  obtain ⟨τ,rop,pop⟩:=hop η ⟨pleftη.1,pleftη.2.1,pleftη.2.2,by simpa only [String.reduceAppend] using pright⟩
  refine ⟨τ,(ra.seq (rleft.seq (rb.seq (rright.seq rop)))).mono (by omega),pop⟩

end Lax455465Proofs.RamScalarBinary

end

section

namespace Lax455465Proofs.RamEdgePortion

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem coe_value (length base radius:ℚ≥0):
    (value length base radius:ℚ)=RegionVolume.edgePortion (length:ℚ) base radius:=by
  rfl

theorem command_spec (B M:ℕ) (length base radius:ℚ≥0) (hB:2*M^2+3 < B)
    (hlN:length.num≤ M) (hlD:length.den≤ M)
    (hbN:base.num≤ M) (hbD:base.den≤ M)
    (hrN:radius.num≤ M) (hrD:radius.den≤ M)
    (hdN:(RamTruncatedSubtract.value radius base).num≤ M)
    (hdD:(RamTruncatedSubtract.value radius base).den≤ M):
    Spec B (fun σ => Stored "portion.length" length σ∧ Stored "portion.base" base σ∧ Stored "portion.radius" radius σ)
      command (fun _ τ => FractionOutput (value length base radius:ℚ) τ)
      (36*(radius.den*base.den).size+244):=by
  have hM:M < B:=by nlinarith
  rintro σ ⟨hl,hb,hr⟩
  obtain ⟨ν,rd,pd⟩:=RamScalarBinary.command_spec B M (36*(radius.den*base.den).size+142)
    radius base "portion.radius" "portion.base" RamTruncatedSubtract.command (RamTruncatedSubtract.value radius base:ℚ)
    hB hrN hrD hbN hbD (by decide) (by decide) (by decide)
    (RamTruncatedSubtract.command_spec B M radius base hB hrN hrD hbN hbD) σ ⟨hr,hb⟩
  obtain ⟨μ,rs,ps⟩:=save_spec B "portion.diff" (RamTruncatedSubtract.value radius base)
    (hdN.trans_lt hM) (hdD.trans_lt hM) (by decide) ν pd
  have hlμ:Stored "portion.length" length μ:=by
    have rr:=rd.seq rs
    simpa only [Stored,rr.frame_var "portion.length.n" (by decide),rr.frame_var "portion.length.d" (by decide),String.reduceAppend] using hl
  obtain ⟨τ,rm,pm⟩:=RamScalarBinary.command_spec B M 50 length (RamTruncatedSubtract.value radius base)
    "portion.length" "portion.diff" RamMinimum.command (min (length:ℚ) (RamTruncatedSubtract.value radius base:ℚ))
    hB hlN hlD hdN hdD (by decide) (by decide) (by decide)
    (RamMinimum.command_spec B M length (RamTruncatedSubtract.value radius base) hB hlN hlD hdN hdD) μ ⟨hlμ,ps⟩
  refine ⟨τ,(rd.seq (rs.seq rm)).mono (by omega),?_⟩
  exact pm

end Lax455465Proofs.RamEdgePortion

end

section

namespace Lax455465Proofs.VolumeData

open MetricMatrix LpInputSize
open scoped BigOperators NNRat

theorem coe_value {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (seed radius:ℚ≥0):
    (value outward capacity length distance seed radius:ℚ) =
      RegionVolume.volume (if outward then rational capacity else fun u v => (capacity v u:ℚ))
        (if outward then rational length else fun u v => (length v u:ℚ))
        (fun v => (distance v:ℚ)) seed radius:=by
  unfold value coefficients
  simp only [values,List.sum_ofFn,NNRat.coe_add,NNRat.cast_sum,NNRat.coe_mul,RamEdgePortion.coe_value]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type]
  cases outward with
  | true => rfl
  | false =>
    simp only [base,Bool.false_eq_true,if_false,RegionVolume.volume]
    rw [Finset.sum_comm]

end Lax455465Proofs.VolumeData

end

section

namespace Lax455465Proofs.RegionQueryData

open MetricMatrix
open scoped NNRat

theorem coe_boundary {n:ℕ} (q:Query n):
    (boundary q:ℚ)=RegionSearch.selectedBoundary (rational q.capacity)
      (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) (direction q) q.radius:=by
  rw [boundary,boundaryAt,BoundaryData.coe_value]
  unfold RegionSearch.selectedBoundary distance
  cases direction q q.radius <;> rfl

theorem coe_volume {n:ℕ} (q:Query n):
    (volume q:ℚ)=RegionSearch.selectedVolume (rational q.capacity) (rational q.length)
      (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) q.seed (direction q) q.radius:=by
  rw [volume,volumeAt,VolumeData.coe_value]
  unfold RegionSearch.selectedVolume distance
  cases direction q q.radius <;> rfl

theorem accepted_eq {n:ℕ} (q:Query n):
    accepted q=decide (0 < q.radius.num∧ (boundary q:ℚ)≤ (bound q:ℚ)):=by
  unfold accepted bound
  simp only [NNRat.coe_mul,coe_boundary,coe_volume,RegionSearch.Good]
  congr 1
  apply propext
  constructor
  · rintro ⟨hr,hb⟩
    refine ⟨?_,hb⟩
    exact NNRat.num_pos.mpr (by exact_mod_cast hr)
  · rintro ⟨hr,hb⟩
    refine ⟨?_,hb⟩
    exact_mod_cast NNRat.num_pos.mp hr

end Lax455465Proofs.RegionQueryData

end

section

namespace Lax455465Proofs.RamArrayScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

theorem command_spec (B:ℕ) (array index name:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s")
    (hname:name ++ ".n" ≠ "rat.d"):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) array σ∧ σ.vars index=i)
      (command array index name) (fun _ τ => Stored name qs[i] τ) 18:=by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamUnsignedBuffer.read_spec B array index qs i hi h2 hindex hn hd hfresh σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B name qs[i] hn hd hname ν pr.1
  exact ⟨τ,rr.seq rs,ps⟩

end Lax455465Proofs.RamArrayScalar

end

section

namespace Lax455465Proofs.RamVolumeCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix DirectedFlowLP
open scoped NNRat

def Context {n:ℕ} (outward:Bool) (capacity length:Matrix n) (distance:Fin n→ ℚ≥0)
    (radius:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧ Stored "portion.radius" radius σ∧
    Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ∧
    Prefix (RamUnsignedBuffer.encode (values length)) "metric.old" σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {outward:Bool} {capacity length:Matrix n} {distance:Fin n→ ℚ≥0}
    {radius:ℚ≥0} (h:Context outward capacity length distance radius σ)
    (hx:∀ x∈ ["metric.n","metric.n2","portion.radius.n","portion.radius.d"],x∉ cmd.wvars)
    (ha:∀ a∈ ["region.capacities","metric.old",RamRootDistances.array outward],a∉ cmd.warrs):
    Context outward capacity length distance radius τ:=by
  simpa only [Context,Stored,Prefix,String.reduceAppend,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp)),
    hr.frame_var "portion.radius.n" (hx _ (by simp)),hr.frame_var "portion.radius.d" (hx _ (by simp)),
    hr.frame_arr "region.capacities" (ha _ (by simp)),hr.frame_arr "metric.old" (ha _ (by simp)),
    hr.frame_arr (RamRootDistances.array outward) (ha _ (by simp))] using h

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (radius:ℚ≥0) (u v:Fin n)
    (hB:2*M^2+3 < B) (hn:n < B) (hn2:n*n < B)
    (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hcn:(capacity u v).num≤ M) (hcd:(capacity u v).den≤ M)
    (hln:(length u v).num≤ M) (hld:(length u v).den≤ M)
    (hdn:(VolumeData.base outward distance u v).num≤ M) (hdd:(VolumeData.base outward distance u v).den≤ M)
    (hrn:radius.num≤ M) (hrd:radius.den≤ M)
    (htn:(RamTruncatedSubtract.value radius (VolumeData.base outward distance u v)).num≤ M)
    (htd:(RamTruncatedSubtract.value radius (VolumeData.base outward distance u v)).den≤ M)
    (hpn:(RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).num≤ M)
    (hpd:(RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).den≤ M):
    Spec B (fun σ => Context outward capacity length distance radius σ∧ σ.vars "sum.i"=(edgeIndex n (u,v)).val)
      (command outward) (fun _ τ => Context outward capacity length distance radius τ∧
        FractionOutput ((capacity u v * RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius:ℚ≥0):ℚ) τ)
      (72*(M^2).size+382):=by
  have hM:M < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  let idx:=(edgeIndex n (u,v)).val
  let base:=VolumeData.base outward distance u v
  let portion:=RamEdgePortion.value (length u v) base radius
  let t:=if outward then u else v
  have hbase:(List.ofFn distance)[t.val]=base:=by
    simp only [List.getElem_ofFn,base,t,VolumeData.base]
    cases outward <;> rfl
  have hi:idx < n*n:=(edgeIndex n (u,v)).isLt
  rintro σ ⟨hctx,hentry⟩
  let σ₁:=σ.setVar "metric.entry" idx
  have r₁:Run B (.assign "metric.entry" (.var "sum.i")) σ σ₁ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hentry.symm,hentry ▸ hi.trans hn2⟩)
  have hctx₁:=frame r₁ hctx (by decide) (by simp [Com.warrs])
  obtain ⟨σ₂,r₂,p₂⟩:=RamDualDistancesInit.indices_spec B u v hn hn2 σ₁ ⟨hctx₁.1,by simp [σ₁,idx]⟩
  have hctx₂:=frame r₂ hctx₁ (by decide) (by simp [RamDualDistancesInit.indices,Com.warrs])
  have hi₂:σ₂.vars "sum.i"=idx:=(r₂.frame_var _ (by decide)).trans ((r₁.frame_var _ (by decide)).trans hentry)
  obtain ⟨σ₃,r₃,p₃⟩:=RamArrayScalar.command_spec B "metric.old" "sum.i" "portion.length" (values length) idx
    (by simpa only [length_values] using hi) h2 (by omega)
    (by rw [value_at]; exact hln.trans_lt hM) (by rw [value_at]; exact hld.trans_lt hM)
    (by decide) (by decide) σ₂ ⟨hctx₂.2.2.2.2.1,hi₂⟩
  have hctx₃:=frame r₃ hctx₂ (by decide) (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have ht₃:σ₃.vars (baseIndex outward)=t.val:=by
    have hx:σ₂.vars (baseIndex outward)=t.val:=by
      cases outward with
      | false => exact p₂.2
      | true => exact p₂.1
    exact (r₃.frame_var _ (by cases outward <;> decide)).trans hx
  obtain ⟨σ₄,r₄,p₄⟩:=RamArrayScalar.command_spec B (RamRootDistances.array outward) (baseIndex outward) "portion.base"
    (List.ofFn distance) t.val (by simpa only [List.length_ofFn] using t.isLt) h2 (by omega)
    (by rw [hbase]; exact hdn.trans_lt hM) (by rw [hbase]; exact hdd.trans_lt hM)
    (by cases outward <;> decide) (by decide) σ₃ ⟨hctx₃.2.2.2.2.2,ht₃⟩
  have hctx₄:=frame r₄ hctx₃
    (by cases outward <;> decide)
    (by cases outward <;> simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have hlength:Stored "portion.length" (length u v) σ₄:=by
    simpa only [idx,value_at,Stored,String.reduceAppend,r₄.frame_var "portion.length.n" (by cases outward <;> decide),
      r₄.frame_var "portion.length.d" (by cases outward <;> decide)] using p₃
  obtain ⟨σ₅,r₅,p₅⟩:=RamEdgePortion.command_spec B M (length u v) base radius hB hln hld hdn hdd hrn hrd htn htd σ₄
    ⟨hlength,by simpa only [hbase] using p₄,hctx₄.2.2.1⟩
  have hctx₅:=frame r₅ hctx₄ (by decide) (by intro a ha; change a∉ ([]:List String); simp)
  obtain ⟨σ₆,r₆,p₆⟩:=RamUnsignedArithmetic.copy_spec B portion "left" (by omega) (hpn.trans_lt hM) (hpd.trans_lt hM) (by decide) σ₅ p₅
  have hctx₆:=frame r₆ hctx₅ (by decide) (by simp [RamUnsignedArithmetic.copy,Com.warrs])
  have hi₆:σ₆.vars "sum.i"=idx:=by
    have rr:=r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))
    exact (rr.frame_var _ (by cases outward <;> decide)).trans hentry
  obtain ⟨σ₇,r₇,p₇⟩:=RamUnsignedBuffer.read_spec B "region.capacities" "sum.i" (values capacity) idx
    (by simpa only [length_values] using hi) h2 (by omega)
    (by rw [value_at]; exact hcn.trans_lt hM) (by rw [value_at]; exact hcd.trans_lt hM) (by decide) σ₆ ⟨hctx₆.2.2.2.1,hi₆⟩
  obtain ⟨σ₈,r₈,p₈⟩:=RamUnsignedArithmetic.copy_spec B (capacity u v) "right" (by omega)
    (hcn.trans_lt hM) (hcd.trans_lt hM) (by decide) σ₇ (by simpa only [idx,value_at] using p₇.1)
  have hleft:σ₈.vars "left.s"=0∧ σ₈.vars "left.n"=portion.num∧ σ₈.vars "left.d"=portion.den:=by
    have rr:=r₇.seq r₈
    simpa only [rr.frame_var "left.s" (by decide),rr.frame_var "left.n" (by decide),rr.frame_var "left.d" (by decide),String.reduceAppend] using p₆
  obtain ⟨τ,r₉,p₉⟩:=multiplyFraction_spec B M 0 portion.num portion.den 0 (capacity u v).num (capacity u v).den
    hB (by omega) (by omega) hpn hpd hcn hcd portion.den_pos (capacity u v).den_pos σ₈
    ⟨hleft.1,hleft.2.1,hleft.2.2,by simpa only [String.reduceAppend] using p₈⟩
  have rr:=r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq (r₈.seq r₉)))))))
  refine ⟨τ,rr.mono ?_,frame rr hctx (by cases outward <;> decide) (by cases outward <;> decide),?_⟩
  · have ha:(radius.den*base.den).size≤ (M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul hrd hdd])
    have hb:(portion.den*(capacity u v).den).size≤ (M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul hpd hcd])
    omega
  · simpa only [RamUnsignedArithmetic.value,portion,base,NNRat.coe_mul,mul_comm] using p₉

end Lax455465Proofs.RamVolumeCoefficient

end

section

namespace Lax455465Proofs.RamVolume

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat

def Context {n:ℕ} (outward:Bool) (capacity length:Matrix n) (distance:Fin n→ ℚ≥0)
    (seed radius:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧ Stored "region.radius" radius σ∧
    Stored "round.seed" seed σ∧ Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ∧
    Prefix (RamUnsignedBuffer.encode (values length)) "metric.old" σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

def SumContext {n:ℕ} (outward:Bool) (capacity length:Matrix n) (distance:Fin n→ ℚ≥0)
    (seed radius:ℚ≥0) (σ:Env):Prop:=
  RamVolumeCoefficient.Context outward capacity length distance radius σ∧
    σ.vars "sum.count"=n*n∧ Stored "round.seed" seed σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outward:Bool) (capacity length:Matrix n)
    (distance:Fin n→ ℚ≥0) (seed radius:ℚ≥0) (hB:2*M^2+3 < B)
    (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hcn:∀ u v, (capacity u v).num≤ M) (hcd:∀ u v, (capacity u v).den≤ M)
    (hln:∀ u v, (length u v).num≤ M) (hld:∀ u v, (length u v).den≤ M)
    (hdn:∀ v, (distance v).num≤ M) (hdd:∀ v, (distance v).den≤ M)
    (hsn:seed.num≤ M) (hsd:seed.den≤ M) (hrn:radius.num≤ M) (hrd:radius.den≤ M)
    (htn:∀ v, (RamTruncatedSubtract.value radius (distance v)).num≤ M)
    (htd:∀ v, (RamTruncatedSubtract.value radius (distance v)).den≤ M)
    (hpn:∀ u v, (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).num≤ M)
    (hpd:∀ u v, (RamEdgePortion.value (length u v) (VolumeData.base outward distance u v) radius).den≤ M)
    (hqn:∀ q∈ VolumeData.coefficients outward capacity length distance radius,q.num≤ M)
    (hqd:∀ q∈ VolumeData.coefficients outward capacity length distance radius,q.den≤ M)
    (hprefixNum:∀ i, ((VolumeData.coefficients outward capacity length distance radius).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((VolumeData.coefficients outward capacity length distance radius).take i).sum.den≤ M)
    (hvn:(VolumeData.value outward capacity length distance seed radius).num≤ M)
    (hvd:(VolumeData.value outward capacity length distance seed radius).den≤ M):
    Spec B (Context outward capacity length distance seed radius) (command outward)
      (fun _ τ => Context outward capacity length distance seed radius τ∧
        Stored "region.volume" (VolumeData.value outward capacity length distance seed radius) τ)
      ((108*(M^2).size+502)*(n*n)+36*(M^2).size+156):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  let qs:=VolumeData.coefficients outward capacity length distance radius
  have hlen:qs.length=n*n:=length_values _
  have hfinalN:qs.sum.num≤ M:=by simpa only [qs,List.take_length] using hprefixNum qs.length
  have hfinalD:qs.sum.den≤ M:=by simpa only [qs,List.take_length] using hprefixDen qs.length
  have hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => SumContext outward capacity length distance seed radius σ∧ σ.vars "sum.i"=i)
        (RamVolumeCoefficient.command outward)
        (fun _ τ => SumContext outward capacity length distance seed radius τ∧ FractionOutput (qs[i]:ℚ) τ)
        (72*(M^2).size+382):=by
    intro i hi σ hσ
    have he:i < n*n:=by rwa [hlen] at hi
    let uv:=(DirectedFlowLP.edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
    have hidx:DirectedFlowLP.edgeIndex n uv=(⟨i,he⟩:Fin (n*n)):=(DirectedFlowLP.edgeIndex n).apply_symm_apply _
    have hdn':(VolumeData.base outward distance uv.1 uv.2).num≤ M:=by cases outward <;> exact hdn _
    have hdd':(VolumeData.base outward distance uv.1 uv.2).den≤ M:=by cases outward <;> exact hdd _
    have htn':(RamTruncatedSubtract.value radius (VolumeData.base outward distance uv.1 uv.2)).num≤ M:=by cases outward <;> exact htn _
    have htd':(RamTruncatedSubtract.value radius (VolumeData.base outward distance uv.1 uv.2)).den≤ M:=by cases outward <;> exact htd _
    obtain ⟨τ,rr,pr⟩:=RamVolumeCoefficient.command_spec B M outward capacity length distance radius uv.1 uv.2 hB
      (by omega) (by omega) hindex hvertex (hcn _ _) (hcd _ _) (hln _ _) (hld _ _)
      hdn' hdd' hrn hrd htn' htd' (hpn _ _) (hpd _ _) σ ⟨hσ.1.1,by simpa only [hidx] using hσ.2⟩
    refine ⟨τ,rr,⟨pr.1,?_,?_⟩,?_⟩
    · exact (rr.frame_var "sum.count" (by cases outward <;> decide)).trans hσ.1.2.1
    · simpa only [Stored,String.reduceAppend,rr.frame_var "round.seed.n" (by cases outward <;> decide),
        rr.frame_var "round.seed.d" (by cases outward <;> decide)] using hσ.1.2.2
    · simpa only [qs,VolumeData.coefficients,values,List.getElem_ofFn,uv,Fin.eta] using pr.2
  have hset:∀ σ k name,SumContext outward capacity length distance seed radius σ→
      name="sum.i" ∨ name="fold.n" ∨ name="fold.d" → SumContext outward capacity length distance seed radius (σ.setVar name k):=by
    intro σ k name hσ hname
    rcases hname with rfl|rfl|rfl <;>
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using hσ
  have hfold:=RamUnsignedSum.command_spec B M (72*(M^2).size+382)
    (SumContext outward capacity length distance seed radius) "sum.i" "sum.count" qs (RamVolumeCoefficient.command outward)
    hB (by omega) hqn hqd hprefixNum hprefixDen (fun _ h => by simpa only [hlen] using h.2.1)
    hset hbody (by decide) (by cases outward <;> decide) (by cases outward <;> decide)
    (fun rr h => by
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),rr.frame_var "portion.radius.n" (by decide),
        rr.frame_var "portion.radius.d" (by decide),rr.frame_var "sum.count" (by decide),
        rr.frame_var "round.seed.n" (by decide),rr.frame_var "round.seed.d" (by decide),
        rr.frame_arr "region.capacities" (by decide),rr.frame_arr "metric.old" (by decide),
        rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [SumContext,RamVolumeCoefficient.Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),rr.frame_var "portion.radius.n" (by decide),
        rr.frame_var "portion.radius.d" (by decide),rr.frame_var "sum.count" (by decide),
        rr.frame_var "round.seed.n" (by decide),rr.frame_var "round.seed.d" (by decide),
        rr.frame_arr "region.capacities" (by decide),rr.frame_arr "metric.old" (by decide),
        rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward∉ ([]:List String); simp)] using h)
  intro σ hctx
  obtain ⟨σ₁,r₁,p₁⟩:=load_spec B "region.radius" radius h1 (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ hctx.2.2.1
  obtain ⟨σ₂,r₂,p₂⟩:=save_spec B "portion.radius" radius (hrn.trans_lt hM) (hrd.trans_lt hM) (by decide) σ₁ p₁
  have hn2₂:σ₂.vars "metric.n2"=n*n:=by
    have rr:=r₁.seq r₂
    exact (rr.frame_var _ (by decide)).trans hctx.2.1
  let σ₃:=σ₂.setVar "sum.count" (n*n)
  have r₃:Run B (.assign "sum.count" (.var "metric.n2")) σ₂ σ₃ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn2₂.symm,hn2₂ ▸ (by omega:n*n < B)⟩)
  have rsetup:=r₁.seq (r₂.seq r₃)
  have hsumCtx:SumContext outward capacity length distance seed radius σ₃:=by
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,by simp [σ₃],?_⟩
    · exact (rsetup.frame_var _ (by decide)).trans hctx.1
    · exact (rsetup.frame_var _ (by decide)).trans hctx.2.1
    · simpa only [Stored,String.reduceAppend,r₃.frame_var "portion.radius.n" (by decide),r₃.frame_var "portion.radius.d" (by decide)] using p₂
    · simpa only [Prefix,rsetup.frame_arr "region.capacities" (by decide)] using hctx.2.2.2.2.1
    · simpa only [Prefix,rsetup.frame_arr "metric.old" (by decide)] using hctx.2.2.2.2.2.1
    · simpa only [Prefix,rsetup.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward∉ ([]:List String); simp)] using hctx.2.2.2.2.2.2
    · simpa only [Stored,String.reduceAppend,rsetup.frame_var "round.seed.n" (by decide),rsetup.frame_var "round.seed.d" (by decide)] using hctx.2.2.2.1
  obtain ⟨σ₄,r₄,p₄⟩:=hfold σ₃ hsumCtx
  obtain ⟨σ₅,r₅,p₅⟩:=save_spec B "volume.sum" qs.sum (hfinalN.trans_lt hM) (hfinalD.trans_lt hM) (by decide) σ₄ p₄.2
  have hseed:Stored "round.seed" seed σ₅:=by
    simpa only [Stored,String.reduceAppend,r₅.frame_var "round.seed.n" (by decide),r₅.frame_var "round.seed.d" (by decide)] using p₄.1.2.2
  obtain ⟨σ₆,r₆,p₆⟩:=RamScalarBinary.command_spec B M (36*(M^2).size+96) seed qs.sum "round.seed" "volume.sum" addFraction
    ((seed+qs.sum:ℚ≥0):ℚ) hB hsn hsd hfinalN hfinalD (by decide) (by decide) (by decide)
    (fun σ h => by
      obtain ⟨τ,rr,pr⟩:=RamUnsignedArithmetic.add_spec B M seed qs.sum hB hsn hsd hfinalN hfinalD σ h
      have hcost:(seed.den*qs.sum.den).size≤ (M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul hsd hfinalD])
      exact ⟨τ,rr.mono (by omega),pr⟩) σ₅ ⟨hseed,p₅⟩
  obtain ⟨τ,r₇,p₇⟩:=save_spec B "region.volume" (VolumeData.value outward capacity length distance seed radius)
    (hvn.trans_lt hM) (hvd.trans_lt hM) (by decide) σ₆ p₆
  have rr:=rsetup.seq (r₄.seq (r₅.seq (r₆.seq r₇)))
  refine ⟨τ,rr.mono ?_,?_,p₇⟩
  · simp only [hlen,Nat.add_assoc]
    ring_nf; omega
  · simpa only [Context,Stored,Prefix,String.reduceAppend,
      rr.frame_var "metric.n" (by cases outward <;> decide),rr.frame_var "metric.n2" (by cases outward <;> decide),
      rr.frame_var "region.radius.n" (by cases outward <;> decide),rr.frame_var "region.radius.d" (by cases outward <;> decide),
      rr.frame_var "round.seed.n" (by cases outward <;> decide),rr.frame_var "round.seed.d" (by cases outward <;> decide),
      rr.frame_arr "region.capacities" (by cases outward <;> decide),rr.frame_arr "metric.old" (by cases outward <;> decide),
      rr.frame_arr (RamRootDistances.array outward) (by cases outward <;> decide)] using hctx

end Lax455465Proofs.RamVolume

end

section

namespace Lax455465Proofs.RamBallMass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def Context {n:ℕ} (outward:Bool) (weights distance:Fin n→ ℚ≥0) (radius:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Stored "region.radius" radius σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outward:Bool) (weights distance:Fin n→ ℚ≥0) (radius:ℚ≥0)
    (hB:2*M^2+3 < B) (hindex:2*n+2 < B)
    (hrn:radius.num≤ M) (hrd:radius.den≤ M)
    (hwn:∀ v, (weights v).num≤ M) (hwd:∀ v, (weights v).den≤ M)
    (hdn:∀ v, (distance v).num≤ M) (hdd:∀ v, (distance v).den≤ M)
    (hprefixNum:∀ i, ((RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).take i).sum.den≤ M):
    Spec B (fun σ => Context outward weights distance radius σ∧ 2*n < (σ.arrs (maskArray outward)).length)
      (command outward) (fun _ τ => Context outward weights distance radius τ∧
        Prefix (RamUnsignedBuffer.encode (BallMassData.mask distance radius)) (maskArray outward) τ∧
        Stored (massName outward) (BallMassData.mass weights distance radius) τ)
      ((36*(M^2).size+256)*n+32):=by
  have hM:M < B:=by nlinarith
  have hM1:1≤ M:=radius.den_pos.trans_le hrd
  let qs:=List.ofFn weights
  let ds:=List.ofFn distance
  let ms:=BallMassData.mask distance radius
  have hqLen:qs.length=n:=List.length_ofFn
  have hdLen:ds.length=n:=List.length_ofFn
  have hmLen:ms.length=n:=by simp [ms,BallMassData.mask]
  have hwN:∀ q∈ qs,q.num≤ M:=by
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hwn v
  have hwD:∀ q∈ qs,q.den≤ M:=by
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hwd v
  have hdN:∀ q∈ ds,q.num≤ M:=by
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hdn v
  have hdD:∀ q∈ ds,q.den≤ M:=by
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact hdd v
  have hmN:∀ q∈ ms,q.num≤ M:=by
    intro q hq
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
    unfold RamBallMask.flag
    split_ifs <;> norm_num <;> omega
  have hmD:∀ q∈ ms,q.den≤ M:=by
    intro q hq
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hq
    unfold RamBallMask.flag
    split_ifs <;> norm_num <;> omega
  have hfinal:(BallMassData.mass weights distance radius).num≤ M∧
      (BallMassData.mass weights distance radius).den≤ M:=by
    simpa only [BallMassData.mass,List.take_length] using
      And.intro (hprefixNum (RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).length)
        (hprefixDen (RamMaskedSum.coefficients (List.ofFn weights) (BallMassData.mask distance radius)).length)
  rintro σ ⟨hctx,hroom⟩
  let ρ:=σ.setVar "ball.count" n
  have rstart:Run B (.assign "ball.count" (.var "metric.n")) σ ρ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ (by omega:n < B)⟩)
  have hmaskCtx:RamBallMask.Context (RamRootDistances.array outward) ds radius ρ:=by
    refine ⟨by simp [ρ,hdLen],?_,?_⟩
    · simpa only [Stored,ρ,vars_setVar,String.reduceEq,if_false,String.reduceAppend] using hctx.2.1
    · simpa only [ds,Prefix,ρ,arrs_setVar] using hctx.2.2.2
  obtain ⟨ν,rmask,pmask⟩:=RamBallMask.command_spec B M (RamRootDistances.array outward) (maskArray outward) ds radius
    (by cases outward <;> decide) hB (by rwa [hdLen]) hrn hrd hdN hdD ρ
    ⟨hmaskCtx,by simpa only [ρ,arrs_setVar,hdLen] using hroom⟩
  have hνcount:ν.vars "ball.count"=n:=by simpa only [hdLen] using pmask.1.1
  let ξ:=ν.setVar "sum.count" n
  have rcount:Run B (.assign "sum.count" (.var "ball.count")) ν ξ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hνcount.symm,hνcount ▸ (by omega:n < B)⟩)
  have hsumCtx:RamMaskedSum.Context "region.weights" (maskArray outward) qs ms ξ:=by
    refine ⟨by simp [ξ,hqLen],?_,?_⟩
    · have rr:=rstart.seq rmask
      simpa only [Prefix,ξ,arrs_setVar,qs,rr.frame_arr "region.weights" (by cases outward <;> decide)] using hctx.2.2.1
    · simpa only [Prefix,ξ,arrs_setVar,ms,BallMassData.mask,ds] using pmask.2
  obtain ⟨μ,rsum,psum⟩:=RamMaskedSum.command_spec B M "region.weights" (maskArray outward) qs ms
    (by omega) hB (by rwa [hqLen]) hwN hwD hmN hmD hprefixNum hprefixDen ξ hsumCtx
  obtain ⟨τ,rsave,psave⟩:=save_spec B (massName outward) (BallMassData.mass weights distance radius)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by cases outward <;> decide) μ psum.2
  have rr:=rstart.seq (rmask.seq (rcount.seq (rsum.seq rsave)))
  refine ⟨τ,rr.mono ?_,?_,?_,psave⟩
  · simp only [hdLen,hqLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf
    omega
  · simpa only [Context,Stored,Prefix,String.reduceAppend,
      rr.frame_var "metric.n" (by cases outward <;> decide),
      rr.frame_var "region.radius.n" (by cases outward <;> decide),
      rr.frame_var "region.radius.d" (by cases outward <;> decide),
      rr.frame_arr "region.weights" (by cases outward <;> decide),
      rr.frame_arr (RamRootDistances.array outward) (by cases outward <;> decide)] using hctx
  · have rafter:=rcount.seq (rsum.seq rsave)
    simpa only [Prefix,ms,BallMassData.mask,ds,
      rafter.frame_arr (maskArray outward) (by cases outward <;> decide)] using pmask.2

end Lax455465Proofs.RamBallMass

end

section

namespace Lax455465Proofs.RamBoundary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat

def Context {n:ℕ} (outward:Bool) (capacity:Matrix n) (distance:Fin n→ ℚ≥0)
    (radius:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (values capacity)) "region.capacities" σ∧
    Prefix (RamUnsignedBuffer.encode (BallMassData.mask distance radius)) (RamBallMass.maskArray outward) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outward:Bool) (capacity:Matrix n)
    (distance:Fin n→ ℚ≥0) (radius:ℚ≥0) (hM1:1≤ M)
    (hB:2*M^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hcn:∀ u v, (capacity u v).num≤ M) (hcd:∀ u v, (capacity u v).den≤ M)
    (hprefixNum:∀ i, ((RamMaskedSum.coefficients (values capacity) (values (BoundaryData.arcs outward distance radius))).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((RamMaskedSum.coefficients (values capacity) (values (BoundaryData.arcs outward distance radius))).take i).sum.den≤ M):
    Spec B (fun σ => Context outward capacity distance radius σ∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      (command outward) (fun _ τ => Context outward capacity distance radius τ∧
        Prefix (RamUnsignedBuffer.encode (values (BoundaryData.arcs outward distance radius))) "region.crossing" τ∧
        Stored "region.boundary" (BoundaryData.value outward capacity distance radius) τ)
      ((36*(M^2).size+234)*(n*n)+30):=by
  have hM:M < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  let cs:=values capacity
  let ms:=values (BoundaryData.arcs outward distance radius)
  have hcLen:cs.length=n*n:=length_values _
  have hmLen:ms.length=n*n:=length_values _
  have hcN:∀ q∈ cs,q.num≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact hcn _ _
  have hcD:∀ q∈ cs,q.den≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    exact hcd _ _
  have hmN:∀ q∈ ms,q.num≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [BoundaryData.arcs,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some outward) (BoundaryData.vertices distance radius _) (BoundaryData.vertices distance radius _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hmD:∀ q∈ ms,q.den≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [BoundaryData.arcs,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some outward) (BoundaryData.vertices distance radius _) (BoundaryData.vertices distance radius _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hfinal:(BoundaryData.value outward capacity distance radius).num≤ M∧
      (BoundaryData.value outward capacity distance radius).den≤ M:=by
    simpa only [ms,BoundaryData.value,List.take_length] using
      And.intro (hprefixNum (RamMaskedSum.coefficients (values capacity) ms).length)
        (hprefixDen (RamMaskedSum.coefficients (values capacity) ms).length)
  rintro σ ⟨hctx,hroom⟩
  have haCtx:RamArcMask.Context (RamBallMass.maskArray outward) (BoundaryData.vertices distance radius) σ:=by
    refine ⟨hctx.1,hctx.2.1,?_⟩
    change Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun v => decide ((distance v:ℚ) < (radius:ℚ))))) (RamBallMass.maskArray outward) σ
    rw [← BallMassData.mask_eq]
    exact hctx.2.2.2
  obtain ⟨ν,rmask,pmask⟩:=RamArcMask.command_spec B (some outward) (RamBallMass.maskArray outward) "region.crossing"
    (BoundaryData.vertices distance radius) (by cases outward <;> decide) h2 (by omega) (by omega) hindex hvertex σ ⟨haCtx,hroom⟩
  let ξ:=ν.setVar "sum.count" (n*n)
  have rcount:Run B (.assign "sum.count" (.var "metric.n2")) ν ξ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pmask.1.2.1.symm,pmask.1.2.1 ▸ (by omega:n*n < B)⟩)
  have hsumCtx:RamMaskedSum.Context "region.capacities" "region.crossing" cs ms ξ:=by
    refine ⟨by simp [ξ,hcLen],?_,?_⟩
    · simpa only [Prefix,ξ,arrs_setVar,cs,rmask.frame_arr "region.capacities" (by cases outward <;> decide)] using hctx.2.2.1
    · simpa only [Prefix,ξ,arrs_setVar,ms,BoundaryData.arcs] using pmask.2
  obtain ⟨μ,rsum,psum⟩:=RamMaskedSum.command_spec B M "region.capacities" "region.crossing" cs ms
    (by omega) hB (by rwa [hcLen]) hcN hcD hmN hmD hprefixNum hprefixDen ξ hsumCtx
  obtain ⟨τ,rsave,psave⟩:=save_spec B "region.boundary" (BoundaryData.value outward capacity distance radius)
    (hfinal.1.trans_lt hM) (hfinal.2.trans_lt hM) (by decide) μ psum.2
  have rr:=rmask.seq (rcount.seq (rsum.seq rsave))
  refine ⟨τ,rr.mono ?_,?_,?_,psave⟩
  · simp only [hcLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf
    omega
  · simpa only [Context,Prefix,
      rr.frame_var "metric.n" (by cases outward <;> decide),
      rr.frame_var "metric.n2" (by cases outward <;> decide),
      rr.frame_arr "region.capacities" (by cases outward <;> decide),
      rr.frame_arr (RamBallMass.maskArray outward) (by cases outward <;> decide)] using hctx
  · have rafter:=rcount.seq (rsum.seq rsave)
    simpa only [Prefix,ms,BoundaryData.arcs,rafter.frame_arr "region.crossing" (by decide)] using pmask.2

end Lax455465Proofs.RamBoundary

end

section

namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def sourceVariables:List String:= ["metric.n","metric.n2","region.radius.n","region.radius.d",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d"]
def arrays:List String:= ["region.weights","region.capacities","metric.old","region.out","region.in"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {q:Query n} (h:Input q σ)
    (hx:∀ x∈ sourceVariables,x∉ cmd.wvars) (ha:∀ a∈ arrays,a∉ cmd.warrs):Input q τ:=by
  refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.nValue,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.n2Value,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "region.radius.n" (hx _ (by simp [sourceVariables])),hr.frame_var "region.radius.d" (hx _ (by simp [sourceVariables]))] using h.radiusData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using h.seedData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using h.betaData
  · simpa only [Prefix,hr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,hr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.inData

theorem Input.ballContext {n:ℕ} {q:Query n} {σ:Env} (h:Input q σ) (b:Bool):
    RamBallMass.Context b q.weights (distance q b) q.radius σ:=by
  refine ⟨h.nValue,h.radiusData,h.weightsData,?_⟩
  cases b with
  | false => exact h.inData
  | true => exact h.outData

theorem Input.volumeContext {n:ℕ} {q:Query n} {σ:Env} (h:Input q σ) (b:Bool):
    RamVolume.Context b q.capacity q.length (distance q b) q.seed q.radius σ:=by
  refine ⟨h.nValue,h.n2Value,h.radiusData,h.seedData,h.capacityData,h.lengthData,?_⟩
  cases b with
  | false => exact h.inData
  | true => exact h.outData

theorem Masks.boundaryContext {n:ℕ} {q:Query n} {σ:Env} (h:Masks q σ) (b:Bool):
    RamBoundary.Context b q.capacity (distance q b) q.radius σ:=by
  refine ⟨h.input.nValue,h.input.n2Value,h.input.capacityData,?_⟩
  cases b with
  | false => exact h.inMask
  | true => exact h.outMask

theorem num_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.num≤ M:=by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.den≤ M:=by
  simpa only [NNRat.den_coe] using h.2

theorem mass_height {n:ℕ} (q:Query n) (H:ℕ) (hb:RegionQueryHeight.Bounds q H) (b:Bool):
    LpInputSize.Height (2^H) (BallMassData.mass q.weights (distance q b) q.radius:ℚ):=by
  have hh:=hb.massPrefixBound b (RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).length
  simpa only [List.take_length,BallMassData.mass] using hh

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem first_succ (predicate:ℕ→ Bool) (i:ℕ):
    first predicate (i+1)=match first predicate i with
      | some j => some j
      | none => if predicate i then some i else none:=by
  simp only [first,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  cases h:(List.range i).find? predicate <;> cases predicate i <;> rfl

def Invariant (R:Env→ Prop) (predicate:ℕ→ Bool) (count:ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars "find.i" ≤ count∧ Matches (first predicate (σ.vars "find.i")) σ

set_option maxHeartbeats 0 in

theorem command_spec (B count K:ℕ) (R:Env→ Prop) (predicate:ℕ→ Bool) (body:Com)
    (h1:1 < B) (hcount:count < B)
    (hlimit:∀ σ,R σ→ σ.vars "find.count"=count)
    (hset:∀ σ k name,R σ→ name∈ ["find.i","find.found","find.result"]→ R (σ.setVar name k))
    (hbody:∀ i,i < count→ Spec B (fun σ => R σ∧ σ.vars "find.i"=i) body
      (fun _ τ => R τ∧ τ.vars "find.ok"=if predicate i then 1 else 0) K)
    (hfresh:"find.i" ∉ body.wvars∧ "find.found" ∉ body.wvars∧ "find.result" ∉ body.wvars):
    Spec B R (command body) (fun _ τ => R τ∧ Matches (first predicate count) τ)
      ((K+20)*count+10):=by
  have hprocess:∀ i,i < count→
      Spec B (fun σ => R σ∧ σ.vars "find.i"=i∧ Matches (first predicate i) σ)
        (process body) (fun _ τ => R τ∧ τ.vars "find.i"=i∧ Matches (first predicate (i+1)) τ) (K+12):=by
    intro i hi σ ⟨hR,hindex,hmatch⟩
    have hiB:i < B:=hi.trans hcount
    cases hs:first predicate i with
    | some j =>
      have hm:σ.vars "find.found"=1∧ σ.vars "find.result"=j:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some false:=by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit (by omega)),hm.1]
        rfl
      refine ⟨σ,(Run.ite_false (c:=.seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hR,hindex,?_⟩
      rw [first_succ,hs]
      exact hm
    | none =>
      have hm:σ.vars "find.found"=0:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some true:=by
        rw [evalB_condEq (evalB_var (hm ▸ (by omega:0 < B))) (evalB_lit (by omega)),hm]
        rfl
      obtain ⟨ν,rb,pb⟩:=hbody i hi σ ⟨hR,hindex⟩
      have hiν:ν.vars "find.i"=i:=(rb.frame_var "find.i" hfresh.1).trans hindex
      have hmν:ν.vars "find.found"=0:=(rb.frame_var "find.found" hfresh.2.1).trans hm
      cases hp:predicate i with
      | false =>
        have hok:ν.vars "find.ok"=0:=by simpa only [hp,Bool.false_eq_true,if_false] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some false:=by
          rw [evalB_condEq (evalB_var (hok ▸ (by omega:0 < B))) (evalB_lit h1),hok]
          rfl
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_false (c:=record) hcok Run.skip))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pb.1,hiν,?_⟩
        rw [first_succ,hs,hp]
        exact hmν
      | true =>
        have hok:ν.vars "find.ok"=1:=by simpa only [hp,if_true] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some true:=by
          rw [evalB_condEq (evalB_var (hok ▸ h1)) (evalB_lit h1),hok]
          rfl
        let τ:=(ν.setVar "find.found" 1).setVar "find.result" i
        have rrecord:Run B record ν τ 4:=(Run.assign (evalB_lit h1)).seq
          (Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hiν.symm,
            by simpa only [vars_setVar,String.reduceEq,if_false] using hiν ▸ hiB⟩))
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_true (d:=Com.skip) hcok rrecord))
        refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_,?_⟩
        · exact hset _ i "find.result" (hset ν 1 "find.found" pb.1 (by simp)) (by simp)
        · simpa only [τ,vars_setVar,String.reduceEq,if_false] using hiν
        · rw [first_succ,hs,hp]
          simp [Matches,τ]
  have hstep:Spec B (fun σ => Invariant R predicate count σ∧ σ.vars "find.i" < count)
      (step body) (fun σ τ => Invariant R predicate count τ∧ τ.vars "find.i"=σ.vars "find.i"+1) (K+16):=by
    rintro σ ⟨⟨hR,hi,hmatch⟩,hlt⟩
    let i:=σ.vars "find.i"
    obtain ⟨ν,rr,pr⟩:=hprocess i hlt σ ⟨hR,rfl,hmatch⟩
    have hiν:ν.vars "find.i"=i:=pr.2.1
    have rinc:Run B (.assign "find.i" (.add (.var "find.i") (.lit 1))) ν (ν.setVar "find.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨ν.setVar "find.i" (i+1),(rr.seq rinc).mono (by omega),?_,by simp [i]⟩
    refine ⟨hset ν (i+1) "find.i" pr.1 (by simp),by simp; omega,?_⟩
    change Matches (first predicate (i+1)) (ν.setVar "find.i" (i+1))
    cases h:first predicate (i+1) <;>
      simpa only [h,Matches,vars_setVar,String.reduceEq,if_false] using pr.2.2
  have hscan:=Spec.forRangeZero "find.i" "find.count" (Invariant R predicate count) count (K+16)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "find.found" 0).setVar "find.result" 0
  have rinit:Run B init σ ν 4:=(Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit (by omega)))
  have hRν:R ν:=hset _ 0 "find.result" (hset σ 0 "find.found" hR (by simp)) (by simp)
  have hinvariant:Invariant R predicate count (ν.setVar "find.i" 0):=by
    refine ⟨hset ν 0 "find.i" hRν (by simp),by simp,?_⟩
    simp [first,Matches,ν]
  obtain ⟨τ,rr,pr⟩:=hscan ν hinvariant
  refine ⟨τ,(rinit.seq rr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,?_⟩
  simpa only [pr.2] using pr.1.2.2

theorem first_some (predicate:ℕ→ Bool) (count i:ℕ) (h:first predicate count=some i):
    i < count∧ predicate i=true:=by
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),List.find?_some h⟩

end Lax455465Proofs.RamFind

end

section

namespace Lax455465Proofs.RamScalarComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (hB:2*M^2+3 < B) (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName) (fun _ τ => τ.vars "cmp.le"=if (a:ℚ)≤ (b:ℚ) then 1 else 0) 64:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1 (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rl
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1 (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have r:=rb.seq rr
    simpa only [r.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),r.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rc,pc⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,ra.seq (rl.seq (rb.seq (rr.seq rc))),?_⟩
  have hp:τ.vars "cmp.le"=1↔ (a:ℚ)≤(b:ℚ):=by simpa only [RamUnsignedArithmetic.value] using pc.2
  by_cases h:(a:ℚ)≤(b:ℚ)
  · simpa only [if_pos h] using hp.mpr h
  · have hz:τ.vars "cmp.le"=0:=by have hn:=mt hp.mp h; omega
    simpa only [if_neg h] using hz

end Lax455465Proofs.RamScalarComparison

end

section

namespace Lax455465Proofs.RamRegionDirection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) {n:ℕ} (weights outDistance inDistance:Fin n→ ℚ≥0)
    (radius:ℚ≥0) (hB:2*M^2+3 < B)
    (hon:(BallMassData.mass weights outDistance radius).num≤ M)
    (hod:(BallMassData.mass weights outDistance radius).den≤ M)
    (hin:(BallMassData.mass weights inDistance radius).num≤ M)
    (hid:(BallMassData.mass weights inDistance radius).den≤ M):
    Spec B (fun σ => Stored "region.outMass" (BallMassData.mass weights outDistance radius) σ∧
      Stored "region.inMass" (BallMassData.mass weights inDistance radius) σ)
      command (fun _ τ => Stored "region.outMass" (BallMassData.mass weights outDistance radius) τ∧
        Stored "region.inMass" (BallMassData.mass weights inDistance radius) τ∧
        τ.vars "region.outward"=if RegionSelection.direction (fun v => (weights v:ℚ))
          (fun v => (outDistance v:ℚ)) (fun v => (inDistance v:ℚ)) radius then 1 else 0) 66:=by
  intro σ hσ
  obtain ⟨ν,rc,pc⟩:=RamScalarComparison.command_spec B M (BallMassData.mass weights outDistance radius)
    (BallMassData.mass weights inDistance radius) "region.outMass" "region.inMass" hB hon hod hin hid
    (by decide) (by decide) (by decide) σ hσ
  let flag:=if (BallMassData.mass weights outDistance radius:ℚ)≤ (BallMassData.mass weights inDistance radius:ℚ) then 1 else 0
  have hf:ν.vars "cmp.le" < B:=by rw [pc]; split_ifs <;> nlinarith
  have rsave:Run B (.assign "region.outward" (.var "cmp.le")) ν (ν.setVar "region.outward" flag) 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pc.symm,hf⟩)
  have rr:=rc.seq rsave
  refine ⟨ν.setVar "region.outward" flag,rr,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,rr.frame_var "region.outMass.n" (by decide),rr.frame_var "region.outMass.d" (by decide)] using hσ.1
  · simpa only [Stored,String.reduceAppend,rr.frame_var "region.inMass.n" (by decide),rr.frame_var "region.inMass.d" (by decide)] using hσ.2
  · simp only [vars_setVar,if_true,flag,RegionSelection.direction,decide_eq_true_eq,←BallMassData.coe_mass]

end Lax455465Proofs.RamRegionDirection

end

section

namespace Lax455465Proofs.RamRegionMasses

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamUnsignedScalar RamVirtualState
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (hb:RegionQueryHeight.Bounds q H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*n+2 < B):
    Spec B (fun σ => Input q σ∧ 2*n < (σ.arrs "region.outMask").length∧ 2*n < (σ.arrs "region.inMask").length)
      command (fun _ τ => Masks q τ∧
        Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) τ∧
        Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) τ)
      ((144*H+584)*n+130):=by
  have hball (b:Bool):Spec B (fun σ => Input q σ∧ 2*n < (σ.arrs (RamBallMass.maskArray b)).length)
      (RamBallMass.command b) (fun _ τ => Input q τ∧
        Prefix (RamUnsignedBuffer.encode (BallMassData.mask (distance q b) q.radius)) (RamBallMass.maskArray b) τ∧
        Stored (RamBallMass.massName b) (BallMassData.mass q.weights (distance q b) q.radius) τ)
      ((36*((2^H)^2).size+256)*n+32):=by
    rintro σ ⟨hctx,hroom⟩
    obtain ⟨τ,rr,pr⟩:=RamBallMass.command_spec B (2^H) b q.weights (distance q b) q.radius hB hindex
      (num_bound hb.radiusBound) (den_bound hb.radiusBound)
      (fun v => num_bound (hb.weightsBound v)) (fun v => den_bound (hb.weightsBound v))
      (fun v => num_bound (hb.distanceBound b v)) (fun v => den_bound (hb.distanceBound b v))
      (fun i => num_bound (hb.massPrefixBound b i)) (fun i => den_bound (hb.massPrefixBound b i)) σ ⟨hctx.ballContext b,hroom⟩
    refine ⟨τ,rr,Input.frame rr hctx (by cases b <;> dsimp [sourceVariables] <;> decide)
      (by cases b <;> dsimp [arrays] <;> decide),pr.2⟩
  rintro σ ⟨hctx,hoRoom,hiRoom⟩
  obtain ⟨ν,ro,po⟩:=hball true σ ⟨hctx,hoRoom⟩
  obtain ⟨μ,ri,pi⟩:=hball false ν ⟨po.1,by change 2*n < (ν.arrs "region.inMask").length; rwa [RamFrames.run_array_length ro "region.inMask"]⟩
  have hoMass:Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) μ:=by
    simpa only [distance,RamBallMass.massName,if_true,Stored,String.reduceAppend,ri.frame_var "region.outMass.n" (by decide),
      ri.frame_var "region.outMass.d" (by decide)] using po.2.2
  have hiMass:Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) μ:=pi.2.2
  obtain ⟨τ,rd,pd⟩:=RamRegionDirection.command_spec B (2^H) q.weights q.outDistance q.inDistance q.radius hB
    (num_bound (mass_height q H hb true)) (den_bound (mass_height q H hb true))
    (num_bound (mass_height q H hb false)) (den_bound (mass_height q H hb false)) μ ⟨hoMass,hiMass⟩
  have rr:=ro.seq (ri.seq rd)
  refine ⟨τ,rr.mono ?_,⟨Input.frame rr hctx (by dsimp [sourceVariables]; decide) (by dsimp [arrays]; decide),?_,?_,pd.2.2⟩,pd.1,pd.2.1⟩
  · rw [←Nat.pow_mul,Nat.size_pow]
    ring_nf; omega
  · have ra:=ri.seq rd
    simpa only [distance,RamBallMass.maskArray,if_true,Prefix,ra.frame_arr "region.outMask" (by decide)] using po.2.1
  · simpa only [distance,RamBallMass.maskArray,Bool.false_eq_true,if_false,Prefix,rd.frame_arr "region.inMask" (by decide)] using pi.2.1

end Lax455465Proofs.RamRegionMasses

end

section

namespace Lax455465Proofs.RamRegionMeasures

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

theorem masks_frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {q:Query n} (h:Masks q σ)
    (hx:∀ x∈ sourceVariables,x∉ cmd.wvars) (ha:∀ a∈ arrays,a∉ cmd.warrs)
    (hout:"region.outMask" ∉ cmd.warrs) (hin:"region.inMask" ∉ cmd.warrs)
    (hdir:"region.outward" ∉ cmd.wvars):Masks q τ:=by
  refine ⟨Input.frame hr h.input hx ha,?_,?_,(hr.frame_var _ hdir).trans h.directionValue⟩
  · simpa only [Prefix,hr.frame_arr "region.outMask" hout] using h.outMask
  · simpa only [Prefix,hr.frame_arr "region.inMask" hin] using h.inMask

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (hb:RegionQueryHeight.Bounds q H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B):
    Spec B (fun σ => Masks q σ∧ 2*(n*n) < (σ.arrs "region.crossing").length) command
      (fun _ τ => Masks q τ∧ Stored "region.boundary" (boundary q) τ∧ Stored "region.volume" (volume q) τ)
      ((288*H+880)*(n*n)+72*H+226):=by
  have hM1:1≤ 2^H:=by have:=Nat.two_pow_pos H; omega
  have hM:2^H < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have horiented (b:Bool):Spec B (fun σ => Masks q σ∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      (oriented b) (fun _ τ => Masks q τ∧ Stored "region.boundary" (boundaryAt q b) τ∧ Stored "region.volume" (volumeAt q b) τ)
      ((144*((2^H)^2).size+736)*(n*n)+36*((2^H)^2).size+186):=by
    rintro σ ⟨hctx,hroom⟩
    obtain ⟨ν,rb,pb⟩:=RamBoundary.command_spec B (2^H) b q.capacity (distance q b) q.radius hM1 hB hindex hvertex
      (fun u v => num_bound (hb.capacityBound u v)) (fun u v => den_bound (hb.capacityBound u v))
      (fun i => num_bound (hb.boundaryPrefixBound b i)) (fun i => den_bound (hb.boundaryPrefixBound b i)) σ ⟨hctx.boundaryContext b,hroom⟩
    have hmν:=masks_frame rb hctx (by cases b <;> dsimp [sourceVariables] <;> decide)
      (by cases b <;> dsimp [arrays] <;> decide) (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide)
    have hvb:=hb.volumeBounds b
    obtain ⟨τ,rv,pv⟩:=RamVolume.command_spec B (2^H) b q.capacity q.length (distance q b) q.seed q.radius hB hindex hvertex
      (fun u v => num_bound (hvb.capacityBound u v)) (fun u v => den_bound (hvb.capacityBound u v))
      (fun u v => num_bound (hvb.lengthBound u v)) (fun u v => den_bound (hvb.lengthBound u v))
      (fun v => num_bound (hvb.distanceBound v)) (fun v => den_bound (hvb.distanceBound v))
      (num_bound hvb.seedBound) (den_bound hvb.seedBound) (num_bound hvb.radiusBound) (den_bound hvb.radiusBound)
      (fun v => num_bound (hvb.differenceBound v)) (fun v => den_bound (hvb.differenceBound v))
      (fun u v => num_bound (hvb.portionBound u v)) (fun u v => den_bound (hvb.portionBound u v))
      (fun a ha => num_bound (hvb.coefficientBound a ha)) (fun a ha => den_bound (hvb.coefficientBound a ha))
      (fun i => num_bound (hvb.prefixBound i)) (fun i => den_bound (hvb.prefixBound i))
      (num_bound hvb.valueBound) (den_bound hvb.valueBound) ν (hmν.input.volumeContext b)
    refine ⟨τ,(rb.seq rv).mono (by ring_nf; omega),masks_frame rv hmν
      (by cases b <;> dsimp [sourceVariables] <;> decide) (by cases b <;> dsimp [arrays] <;> decide)
      (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide),?_,pv.2⟩
    simpa only [boundaryAt,Stored,String.reduceAppend,rv.frame_var "region.boundary.n" (by cases b <;> decide),
      rv.frame_var "region.boundary.d" (by cases b <;> decide)] using pb.2.2
  rintro σ ⟨hctx,hroom⟩
  have hdir:σ.vars "region.outward" < B:=by rw [hctx.directionValue]; split_ifs <;> omega
  have hc:(Cond.eq (.var "region.outward") (.lit 1)).evalB B σ=some (direction q q.radius):=by
    rw [evalB_condEq (evalB_var hdir) (evalB_lit h1),hctx.directionValue]
    cases direction q q.radius <;> rfl
  cases hd:direction q q.radius with
  | true =>
    obtain ⟨τ,rr,pr⟩:=horiented true σ ⟨hctx,hroom⟩
    have rb:=Run.ite_true (d:=oriented false) (by simpa only [hd] using hc) rr
    refine ⟨τ,rb.mono ?_,pr.1,?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · simpa only [boundary,hd] using pr.2.1
    · simpa only [volume,hd] using pr.2.2
  | false =>
    obtain ⟨τ,rr,pr⟩:=horiented false σ ⟨hctx,hroom⟩
    have rb:=Run.ite_false (c:=oriented true) (by simpa only [hd] using hc) rr
    refine ⟨τ,rb.mono ?_,pr.1,?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · simpa only [boundary,hd] using pr.2.1
    · simpa only [volume,hd] using pr.2.2

end Lax455465Proofs.RamRegionMeasures

end

section

namespace Lax455465Proofs.RamRegionAcceptance

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (hb:RegionQueryHeight.Bounds q H)
    (hB:2*(2^H)^2+3 < B):
    Spec B (fun σ => Masks q σ∧ Stored "region.boundary" (boundary q) σ∧ Stored "region.volume" (volume q) σ)
      command (fun _ τ => Masks q τ∧ Stored "query.bound" (bound q) τ∧
        τ.vars "find.ok"=if accepted q then 1 else 0) (72*H+198):=by
  have hM:2^H < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hv:LpInputSize.Height (2^H) (volume q:ℚ):=(hb.volumeBounds (direction q q.radius)).valueBound
  have hbc:LpInputSize.Height (2^H) (boundary q:ℚ):=by
    have hh:=hb.boundaryPrefixBound (direction q q.radius)
      (RamMaskedSum.coefficients (MetricMatrix.values q.capacity) (MetricMatrix.values (BoundaryData.arcs (direction q q.radius) (distance q (direction q q.radius)) q.radius))).length
    simpa only [boundary,boundaryAt,BoundaryData.value,List.take_length] using hh
  have hp:=hb.boundBound
  rintro σ ⟨hctx,hboundary,hvolume⟩
  obtain ⟨ν,rp,pp⟩:=RamScalarBinary.command_spec B (2^H) (36*((2^H)^2).size+64)
    q.beta (volume q) "round.slope" "region.volume" multiplyFraction (bound q:ℚ) hB
    (num_bound hb.betaBound) (den_bound hb.betaBound) (num_bound hv) (den_bound hv) (by decide) (by decide) (by decide)
    (fun σ h => by
      obtain ⟨τ,rr,pr⟩:=multiplyFraction_spec B (2^H) 0 q.beta.num q.beta.den 0 (volume q).num (volume q).den hB
        (by omega) (by omega) (num_bound hb.betaBound) (den_bound hb.betaBound) (num_bound hv) (den_bound hv)
        q.beta.den_pos (volume q).den_pos σ h
      have hsize:(q.beta.den*(volume q).den).size≤ ((2^H)^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound hb.betaBound) (den_bound hv)])
      exact ⟨τ,rr.mono (by omega),by simpa only [bound,NNRat.coe_mul,RamUnsignedArithmetic.value] using pr⟩) σ ⟨hctx.input.betaData,hvolume⟩
  obtain ⟨μ,rs,ps⟩:=save_spec B "query.bound" (bound q) ((num_bound hp).trans_lt hM) ((den_bound hp).trans_lt hM) (by decide) ν pp
  have hboundaryμ:Stored "region.boundary" (boundary q) μ:=by
    have rr:=rp.seq rs
    simpa only [Stored,String.reduceAppend,rr.frame_var "region.boundary.n" (by decide),rr.frame_var "region.boundary.d" (by decide)] using hboundary
  obtain ⟨ξ,rc,pc⟩:=RamScalarComparison.command_spec B (2^H) (boundary q) (bound q) "region.boundary" "query.bound" hB
    (num_bound hbc) (den_bound hbc) (num_bound hp) (den_bound hp) (by decide) (by decide) (by decide) μ ⟨hboundaryμ,ps⟩
  have rprior:=rp.seq (rs.seq rc)
  have hradius:ξ.vars "region.radius.n"=q.radius.num:=
    (rprior.frame_var _ (by decide)).trans hctx.input.radiusData.1
  have hc:(Cond.eq (.var "region.radius.n") (.lit 0)).evalB B ξ=some (decide (q.radius.num=0)):=by
    rw [evalB_condEq (evalB_var (hradius ▸ (num_bound hb.radiusBound).trans_lt hM)) (evalB_lit (by omega)),hradius]
    rfl
  have preserve {τ:Env} {c:Com} {k:ℕ} (rr:Run B c σ τ k)
      (hx:∀ x∈ sourceVariables,x∉ c.wvars) (hd:"region.outward" ∉ c.wvars)
      (ha:∀ a∈ arrays,a∉ c.warrs) (ho:"region.outMask" ∉ c.warrs) (hi:"region.inMask" ∉ c.warrs):Masks q τ:=by
    exact ⟨Input.frame rr hctx.input hx ha,
      by simpa only [Prefix,rr.frame_arr "region.outMask" ho] using hctx.outMask,
      by simpa only [Prefix,rr.frame_arr "region.inMask" hi] using hctx.inMask,
      (rr.frame_var _ hd).trans hctx.directionValue⟩
  by_cases hz:q.radius.num=0
  · have rb:Run B (.assign "find.ok" (.lit 0)) ξ (ξ.setVar "find.ok" 0) 2:=Run.assign (evalB_lit (by omega))
    have rrecord:=Run.ite_true (d:=.assign "find.ok" (.var "cmp.le")) (by simpa only [hz,decide_true] using hc) rb
    have rr:=rp.seq (rs.seq (rc.seq rrecord))
    refine ⟨ξ.setVar "find.ok" 0,rr.mono ?_,preserve rr (by dsimp [sourceVariables]; decide) (by decide)
      (by intro a ha; change a∉ ([]:List String); simp) (by decide) (by decide),?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · have ra:=rc.seq rrecord
      simpa only [Stored,String.reduceAppend,ra.frame_var "query.bound.n" (by decide),ra.frame_var "query.bound.d" (by decide)] using ps
    · simp [accepted_eq,hz]
  · let flag:ℕ:=if (boundary q:ℚ)≤(bound q:ℚ) then 1 else 0
    have hflag:ξ.vars "cmp.le" < B:=by rw [pc]; split_ifs <;> omega
    have rb:Run B (.assign "find.ok" (.var "cmp.le")) ξ (ξ.setVar "find.ok" flag) 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨pc.symm,hflag⟩)
    have rrecord:=Run.ite_false (c:=.assign "find.ok" (.lit 0)) (by simpa only [hz,decide_false] using hc) rb
    have rr:=rp.seq (rs.seq (rc.seq rrecord))
    refine ⟨ξ.setVar "find.ok" flag,rr.mono ?_,preserve rr (by dsimp [sourceVariables]; decide) (by decide)
      (by intro a ha; change a∉ ([]:List String); simp) (by decide) (by decide),?_,?_⟩
    · dsimp only [Cond.size,Expr.size]
      rw [←Nat.pow_mul,Nat.size_pow]
      ring_nf; omega
    · have ra:=rc.seq rrecord
      simpa only [Stored,String.reduceAppend,ra.frame_var "query.bound.n" (by decide),ra.frame_var "query.bound.d" (by decide)] using ps
    · simp [accepted_eq,flag,Nat.pos_of_ne_zero hz]

end Lax455465Proofs.RamRegionAcceptance

end

section

set_option maxRecDepth 30000

namespace Lax455465Proofs.RamRegionQuery

open RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (hb:RegionQueryHeight.Bounds q H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B):
    Spec B (fun σ => Input q σ∧ 2*n < (σ.arrs "region.outMask").length∧
      2*n < (σ.arrs "region.inMask").length∧ 2*(n*n) < (σ.arrs "region.crossing").length)
      command (fun _ τ => Masks q τ∧
        Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) τ∧
        Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) τ∧
        Stored "region.boundary" (boundary q) τ∧ Stored "region.volume" (volume q) τ∧
        Stored "query.bound" (bound q) τ∧ τ.vars "find.ok"=if accepted q then 1 else 0)
      ((288*H+880)*(n*n)+(144*H+584)*n+144*H+554):=by
  rintro σ ⟨hctx,hoRoom,hiRoom,hcRoom⟩
  obtain ⟨ν,rm,pm⟩:=RamRegionMasses.command_spec B H q hb hB hvertex σ ⟨hctx,hoRoom,hiRoom⟩
  obtain ⟨μ,rv,pv⟩:=RamRegionMeasures.command_spec B H q hb hB hindex hvertex ν
    ⟨pm.1,by rwa [RamFrames.run_array_length rm "region.crossing"]⟩
  obtain ⟨τ,ra,pa⟩:=RamRegionAcceptance.command_spec B H q hb hB μ pv
  have rr:=rm.seq (rv.seq ra)
  refine ⟨τ,rr.mono (by ring_nf; omega),pa.1,?_,?_,?_,?_,pa.2⟩
  · have rafter:=rv.seq ra
    simpa only [Stored,String.reduceAppend,rafter.frame_var "region.outMass.n" (by decide),rafter.frame_var "region.outMass.d" (by decide)] using pm.2.1
  · have rafter:=rv.seq ra
    simpa only [Stored,String.reduceAppend,rafter.frame_var "region.inMass.n" (by decide),rafter.frame_var "region.inMass.d" (by decide)] using pm.2.2
  · simpa only [Stored,String.reduceAppend,ra.frame_var "region.boundary.n" (by decide),ra.frame_var "region.boundary.d" (by decide)] using pv.2.1
  · simpa only [Stored,String.reduceAppend,ra.frame_var "region.volume.n" (by decide),ra.frame_var "region.volume.d" (by decide)] using pv.2.2

end Lax455465Proofs.RamRegionQuery

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRadiusSearch
open RadiusSearchData RegionQueryData RamRegionContext Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def sourceVariables:List String:= ["metric.n","metric.n2","round.seed.n","round.seed.d","round.slope.n","round.slope.d","find.count"]
def sourceArrays:List String:=RamRegionContext.arrays ++ ["region.radii"]

theorem replaceRadius {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {q:Query n} {radii:List ℚ≥0} {r:ℚ≥0} (h:Context q radii σ)
    (hstore:Stored "region.radius" r τ)
    (hx:∀ x∈ sourceVariables,x∉ cmd.wvars) (ha:∀ a∈ sourceArrays,a∉ cmd.warrs):
    Context q radii τ:=by
  obtain ⟨s,hs⟩:=h.input
  have hi:Input (atRadius q r) τ:=by
    refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans hs.nValue,
      (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans hs.n2Value,hstore,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [atRadius,Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using hs.seedData
    · simpa only [atRadius,Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using hs.betaData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.weights" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.weightsData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.capacityData
    · simpa only [atRadius,Prefix,hr.frame_arr "metric.old" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.lengthData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.out" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.outData
    · simpa only [atRadius,Prefix,hr.frame_arr "region.in" (ha _ (by simp [sourceArrays,RamRegionContext.arrays]))] using hs.inData
  exact ⟨⟨r,hi⟩,by simpa only [Prefix,hr.frame_arr "region.radii" (ha _ (by simp [sourceArrays]))] using h.radiusData,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.count,
    by rw [RamFrames.run_array_length hr "region.outMask"]; exact h.outRoom,
    by rw [RamFrames.run_array_length hr "region.inMask"]; exact h.inRoom,
    by rw [RamFrames.run_array_length hr "region.crossing"]; exact h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem test_answer_spec (B H:ℕ) {n:ℕ} (q:Query n) (radii:List ℚ≥0)
    (i:ℕ) (hi:i< radii.length) (hb:RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hposition:2*i+1 < B):
    Spec B (fun σ => Context q radii σ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context q radii τ∧ Answer (atRadius q radii[i]) τ)
      (queryCost n H+18):=by
  have hn:radii[i].num< B:=(num_bound hb.radiusBound).trans_lt (by nlinarith [(Nat.one_le_two_pow:1≤2^H)])
  have hd:radii[i].den< B:=(den_bound hb.radiusBound).trans_lt (by nlinarith [(Nat.one_le_two_pow:1≤2^H)])
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rr,pr⟩:=RamArrayScalar.command_spec B "region.radii" "find.i" "region.radius" radii i hi
    (by omega) hposition hn hd (by decide) (by decide) σ ⟨hctx.radiusData,hidx⟩
  have hν:=replaceRadius rr hctx pr (by dsimp [sourceVariables]; decide) (by dsimp [sourceArrays,RamRegionContext.arrays]; decide)
  obtain ⟨s,hs⟩:=hctx.input
  have hiν:Input (atRadius q radii[i]) ν:=by

    obtain ⟨r,hr⟩:=hν.input
    refine ⟨hr.nValue,hr.n2Value,pr,hr.seedData,hr.betaData,hr.weightsData,hr.capacityData,hr.lengthData,hr.outData,hr.inData⟩
  obtain ⟨τ,rq,pq⟩:=RamRegionQuery.command_spec B H (atRadius q radii[i]) hb hB hindex hvertex ν
    ⟨hiν,hν.outRoom,hν.inRoom,hν.crossingRoom⟩
  have hτ:=replaceRadius rq hν pq.1.input.radiusData (by dsimp [sourceVariables]; decide) (by dsimp [sourceArrays,RamRegionContext.arrays]; decide)
  exact ⟨τ,(rr.seq rq).mono (by dsimp [queryCost]; omega),hτ,pq⟩

theorem test_spec (B H:ℕ) {n:ℕ} (q:Query n) (radii:List ℚ≥0)
    (i:ℕ) (hi:i< radii.length) (hb:RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hposition:2*i+1 < B):
    Spec B (fun σ => Context q radii σ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context q radii τ∧ τ.vars "find.ok"=if predicate q radii i then 1 else 0)
      (queryCost n H+18):=by
  rintro σ hσ
  obtain ⟨τ,rr,pr⟩:=test_answer_spec B H q radii i hi hb hB hindex hvertex hposition σ hσ
  refine ⟨τ,rr,pr.1,?_⟩
  simpa only [RadiusSearchData.predicate,List.getD_eq_get radii 0 (⟨i,hi⟩:Fin radii.length),List.get_eq_getElem] using pr.2.2.2.2.2.2.2

theorem setFinder {n:ℕ} {q:Query n} {radii:List ℚ≥0} {σ:Env}
    (h:Context q radii σ) (k:ℕ) (name:String)
    (hname:name∈ ["find.i","find.found","find.result"]):Context q radii (σ.setVar name k):=by
  obtain ⟨r,hr⟩:=h.input
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
  rcases hname with rfl|rfl|rfl
  all_goals
    refine ⟨⟨r,?_⟩,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact (by simpa only [Prefix,arrs_setVar] using h.radiusData)
    | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using h.count)
    | exact (by simpa only [arrs_setVar] using h.outRoom)
    | exact (by simpa only [arrs_setVar] using h.inRoom)
    | exact (by simpa only [arrs_setVar] using h.crossingRoom)
    | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
       all_goals first
         | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using hr.nValue)
         | exact (by simpa only [vars_setVar,String.reduceEq,if_false] using hr.n2Value)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.radiusData)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.seedData)
         | exact (by simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hr.betaData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.weightsData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.capacityData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.lengthData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.outData)
         | exact (by simpa only [Prefix,arrs_setVar] using hr.inData))

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (radii:List ℚ≥0)
    (hb:∀ i, ∀ hi:i< radii.length,RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hposition:2*radii.length+2 < B):
    Spec B (Context q radii) command
      (fun _ τ => Context q radii τ∧ RamFind.Matches
        (RamFind.first (predicate q radii) radii.length) τ)
      ((queryCost n H+38)*radii.length+10):=by
  apply RamFind.command_spec B radii.length (queryCost n H+18) (Context q radii) (predicate q radii) test
    (by omega) (by omega) (fun _ h => h.count) (fun _ k name h hn => setFinder h k name hn)
  · intro i hi
    exact test_spec B H q radii i hi (hb i hi) hB hindex hvertex (by omega)
  · decide

end Lax455465Proofs.RamRadiusSearch

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamSelectedRegion
open RadiusSearchData RamRadiusSearch RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (radii:List ℚ≥0)
    (hb:∀ i, ∀ hi:i< radii.length,RegionQueryHeight.Bounds (atRadius q radii[i]) H)
    (hB:2*(2^H)^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hposition:2*radii.length+2 < B):
    Spec B (Context q radii) command
      (fun _ τ => Context q radii τ∧ RamFind.Matches
        (RamFind.first (predicate q radii) radii.length) τ∧ Selected q radii τ)
      ((queryCost n H+38)*radii.length+queryCost n H+40):=by
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩:=RamRadiusSearch.command_spec B H q radii hb hB hindex hvertex hposition σ hσ
  cases hs:RamFind.first (predicate q radii) radii.length with
  | none =>
    have hm:ν.vars "find.found"=0:=by simpa only [hs,RamFind.Matches] using ps.2
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B ν=some false:=by
      rw [evalB_condEq (evalB_var (hm ▸ (by omega:0< B))) (evalB_lit (by omega)),hm]
      rfl
    refine ⟨ν,(rs.seq (Run.ite_false (c:=restore) hc Run.skip)).mono (by dsimp [Cond.size,Expr.size]; omega),ps.1,by simpa only [hs] using ps.2,?_⟩
    simp only [Selected,hs]
  | some i =>
    have hi:=(RamFind.first_some (predicate q radii) radii.length i hs).1
    have hm:ν.vars "find.found"=1∧ ν.vars "find.result"=i:=by simpa only [hs,RamFind.Matches] using ps.2
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B ν=some true:=by
      rw [evalB_condEq (evalB_var (hm.1 ▸ (by omega:1< B))) (evalB_lit (by omega)),hm.1]
      rfl
    let μ:=ν.setVar "find.i" i
    have ra:Run B (.assign "find.i" (.var "find.result")) ν μ 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ (by omega:i< B)⟩)
    obtain ⟨τ,rq,pq⟩:=test_answer_spec B H q radii i hi (hb i hi) hB hindex hvertex (by omega) μ
      ⟨setFinder ps.1 i "find.i" (by simp),by simp [μ]⟩
    have rr:=ra.seq rq
    refine ⟨τ,(rs.seq (Run.ite_true (d:=Com.skip) hc rr)).mono (by dsimp [Cond.size,Expr.size]; omega),pq.1,?_,?_⟩
    · simpa only [hs,RamFind.Matches,rr.frame_var "find.found" (by decide),rr.frame_var "find.result" (by decide)] using hm
    · simpa only [Selected,hs,List.getD_eq_get radii 0 (⟨i,hi⟩:Fin radii.length),List.get_eq_getElem] using pq.2

end Lax455465Proofs.RamSelectedRegion

end

theorem solution:∀ (B H:Nat) {n:Nat} (q:Lax455465Proofs.RegionQueryData.Query n) (radii:List NNRat),
  (∀ (i:Nat) (hi:Nat.lt i (@List.length NNRat radii)),
      @Lax455465Proofs.RegionQueryHeight.Bounds n
        (@Lax455465Proofs.RadiusSearchData.atRadius n q
          (@GetElem.getElem (List NNRat) Nat NNRat
            (fun (as:List NNRat) (i:Nat) => Nat.lt i (@List.length NNRat as))
            (@List.instGetElemNatLtLength NNRat) radii i hi))
        H)→
    Nat.lt
        (Nat.add
          (Nat.mul ((2:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) H)
              ((2:Nat))))
          ((3:Nat)))
        B→
      Nat.lt
          (Nat.add
            (Nat.mul ((2:Nat))
              (Nat.mul n n))
            ((2:Nat)))
          B→
        Nat.lt
            (Nat.add
              (Nat.mul
                ((2:Nat)) n)
              ((2:Nat)))
            B→
          Nat.lt
              (Nat.add
                (Nat.mul
                  ((2:Nat)) (@List.length NNRat radii))
                ((2:Nat)))
              B→
            Lax808846Proofs.Reasoning.Spec B (@Lax455465Proofs.RamRadiusSearch.Context n q radii)
              Lax455465Proofs.RamSelectedRegion.command
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax455465Proofs.RamRadiusSearch.Context n q radii τ)
                  (And
                    (Lax455465Proofs.RamFind.Matches
                      (Lax455465Proofs.RamFind.first (@Lax455465Proofs.RadiusSearchData.predicate n q radii)
                        (@List.length NNRat radii))
                      τ)
                    (@Lax455465Proofs.RamSelectedRegion.Selected n q radii τ)))
              (Nat.add
                (Nat.add
                  (Nat.mul
                    (Nat.add (Lax455465Proofs.RamRadiusSearch.queryCost n H)
                      ((38:Nat)))
                    (@List.length NNRat radii))
                  (Lax455465Proofs.RamRadiusSearch.queryCost n H))
                ((40:Nat))):= @Lax455465Proofs.RamSelectedRegion.command_spec
