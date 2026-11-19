-- Prove2me | solution 1 for Lax109476Proofs.RamRationalReconstruction.reconstruct_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:55.46625+00:00
-- url     : https://prove2.me/submissions/1a48e40b-670a-4c6e-9d75-74a21588bf8b

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
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

namespace Lax109476Proofs.RamArithmetic
end Lax109476Proofs.RamArithmetic
theorem Lax109476Proofs.RamArithmetic.normalizeFraction_spec:∀ (B n d:Nat),
  LT.lt n B→
    LT.lt d B→
      LT.lt ((0:Nat)) d→
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

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

end Lax109476Proofs.RationalSizeBounds

end

section

namespace Lax109476Proofs.RationalReconstruction

def tail (q:ℚ):ℚ:=(Int.fract q)⁻¹

end Lax109476Proofs.RationalReconstruction

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

theorem Spec.pre (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ):Spec B P' c Q K:=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

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

theorem fractionValue_inv (s n d:ℕ):fractionValue s d n=(fractionValue s n d)⁻¹:=by
  unfold fractionValue
  split_ifs <;> simp [inv_div,neg_div]

theorem invertFraction_spec (B s n d:ℕ) (h1:1 < B) (hs:s≤ 1)
    (hn:n < B) (hd:d < B):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧ σ.vars "left.d"=d)
      invertFraction (fun _ σ' => FractionOutput (fractionValue s n d)⁻¹ σ')
      (36 * n.size + 40):=by
  have hsB:=hs.trans_lt h1
  by_cases hz:n=0
  · subst n
    have hzero:Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
        (fun _ σ' => FractionOutput 0 σ') 6:=by
      (expose_names;
        (refine fun (σ:Env) (a:True) => let c0:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c1:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c2:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c3:Com:=Com.seq c1 c2; let c4:Com:=Com.seq c0 c3; let c5:Env→ Nat→ Prop:=Run B c4 σ; let c6:Env→ Prop:=(fun (x σ':Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ') σ; let c7:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat)); let c9:Env:=Env.setVar c8 "rat.s" ((0:Nat)); let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.lit ((1:Nat)))); let c14:Nat:=c10 c13 c12; @Exists.intro Env (fun (σ':Env) => And (c5 σ' ((6:Nat))) (c6 σ')) c9 (@And.intro (c5 c9 ((6:Nat))) (c6 c9) (RunStep.mono B c4 σ c9 (c10 c12 c14) ((6:Nat)) (RunStep.seq B c0 c3 σ c7 c9 c12 c14 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hn)) (RunStep.seq B c1 c2 c7 c8 c9 c13 c12 (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)) (RunStep.assign B c8 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c8 hn)))) (?nAX_g3891_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3891_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp [FractionOutput,fractionValue]
    rintro σ ⟨hσs,hσn,hσd⟩
    have hc:(Cond.eq (.var "left.n") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hσn ▸ hn)) (evalB_lit (by omega)),hσn]
      rfl
    obtain ⟨τ,hr,hτ⟩:=hzero σ True.intro
    exact ⟨τ, (Run.ite_true hc hr).mono (by simp [Nat.size]),
      by simpa [fractionValue] using hτ⟩
  · have hnorm:=normalizeFraction_output_spec B s d n hs hd hn (Nat.pos_of_ne_zero hz)
    have hv:=fractionValue_inv s n d
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "left.s") s) (And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat:=c1 (Nat.mul ((36:Nat)) (Nat.size n)); let c3:Nat:=c2 ((40:Nat)); let c4:Env→ Prop:=FractionOutput (@Inv.inv Rat Rat.instInv (fractionValue s n d)); let c5:Env→ Prop:=(fun (x σ':Env) => c4 σ') σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B invertFraction σ σ' c3) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:= @Eq Nat (Env.vars σ "left.n") ((0:Nat)); let c9:Prop:=Not c8; let c10:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c11:Env:=Env.setVar c10 "rat.d" ((1:Nat)); let c12:Env:=Env.setVar c11 "rat.s" ((0:Nat)); let c13:Nat→ Nat:=c1 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c15:Nat→ Nat:=c1 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c18:Nat:=c1 c17 c16; let c19:Nat:=c1 c16 c18; let c20:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c22:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c23:Com:=Com.seq c21 c22; let c24:Com:=Com.seq c20 c23; let c25:Com:=Com.seq (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction); let c26:Com:=Com.seq (Com.assign "rat.n" (Expr.var "left.d")) c25; let c27:Nat:=Env.vars (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n"; let c28:Env:=Env.setVar (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" c27; let c29:Nat:=Env.vars c28 "left.s"; let c30:Env:=Env.setVar c28 "rat.s" c29; let c31:Env→ Nat→ Prop:=Run B normalizeFraction c30; let c32:Nat:=c2 ((16:Nat)); let c33:Env→ Prop:=fun (σ':Env) => And (c31 σ' c32) (FractionOutput (fractionValue s d n) σ'); let c34:String→ Nat:=Env.vars c30; let c35:Nat:=c13 (Expr.size (Expr.var "left.d")); let c36:Nat:=c13 (Expr.size (Expr.var "left.n")); let c37:Nat:=c13 (Expr.size (Expr.var "left.s")); let c38:Nat:=c1 c37 c32; let c39:Nat:=c1 c36 c38; let c40:Nat:=c1 c35 c39; @And.casesOn (@Eq Nat (Env.vars σ "left.s") s) c0 (fun (x:And (@Eq Nat (Env.vars σ "left.s") s) c0) => c7) a fun (left:@Eq Nat (Env.vars σ "left.s") s) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d) (fun (x:c0) => c7) right fun (left_1:@Eq Nat (Env.vars σ "left.n") n) (right_1:@Eq Nat (Env.vars σ "left.d") d) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c7) (Classical.em c8) (fun (hcase:c8) => @Exists.intro Env c6 c12 (@And.intro (Run B invertFraction σ c12 c3) (c5 c12) (RunStep.mono B invertFraction σ c12 (c15 c19) c3 (RunStep.ite_true B c14 c24 c26 σ c12 c19 (RunStep.cond_eq_true B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g3891_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3891_1_0_1)) hcase) (RunStep.seq B c20 c23 σ c10 c12 c16 c18 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3891_1_0_2))) (RunStep.seq B c21 c22 c10 c11 c12 c17 c16 (RunStep.assign B c10 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c10 h1)) (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g3891_1_0_3)))))) (?nAX_g3891_1_0_4)) ?_)) fun (hcase:c9) => @Exists.casesOn Env c33 (fun (x:@Exists Env c33) => c7) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") d) (And (@Eq Nat (Env.vars σ_1 "rat.d") n) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => FractionOutput (fractionValue s d n) σ') c32 hnorm c30 ?_) fun (w:Env) (h:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => @And.casesOn (c31 w c32) (FractionOutput (fractionValue s d n) w) (fun (x:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => c7) h fun (left_2:c31 w c32) (right_2:FractionOutput (fractionValue s d n) w) => @Exists.intro Env c6 w (@And.intro (Run B invertFraction σ w c3) (c5 w) (RunStep.mono B invertFraction σ w (c15 c40) c3 (RunStep.ite_false B c14 c24 c26 σ w c40 (RunStep.cond_eq_false B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g3891_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3891_1_0_6)) hcase) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.d")) c25 σ (Env.setVar σ "rat.n" (Env.vars σ "left.d")) w c35 c39 (RunStep.assign B σ "rat.n" (Expr.var "left.d") (Env.vars σ "left.d") (RunStep.eval_var B σ "left.d" (?nAX_g3891_1_0_7))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction) (Env.setVar σ "rat.n" (Env.vars σ "left.d")) c28 w c36 c38 (RunStep.assign B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" (Expr.var "left.n") c27 (RunStep.eval_var B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n" (?nAX_g3891_1_0_8))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction c28 c30 w c37 c32 (RunStep.assign B c28 "rat.s" (Expr.var "left.s") c29 (RunStep.eval_var B c28 "left.s" (?nAX_g3891_1_0_9))) left_2)))) (?nAX_g3891_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3891_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3891_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_2))
    all_goals simp_all

end Lax109476Proofs.RamRational

end

section

namespace Lax109476Proofs.RamComparison

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
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "cmp.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "cmp.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat→ Prop:= @Eq Nat c9; let c11:Nat:=c8 "right.s"; let c12:Prop:=c10 c11; let c13:Prop:=Not c12; let c14:Nat:=leFlag s₁ n₁ d₁ s₂ n₂ d₂; let c15:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "cmp.le") c14) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction σ σ' ((40:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Prop:=c10 ((1:Nat)); let c19:Prop:=Not c18; let c20:Nat:=c8 "cmp.u"; let c21:Nat→ Prop:=Nat.lt c20; let c22:Nat:=c8 "cmp.v"; let c23:Prop:=c21 c22; let c24:Prop:=Not c23; let c25:Nat→ Env:=Env.setVar c7 "cmp.le"; let c26:Env:=c25 ((0:Nat)); let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Nat:=c28 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c30:Nat→ Nat:=c27 c29; let c31:Nat:=c28 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c32:Nat→ Nat:=c27 c31; let c33:Nat→ Nat:=c27 (c28 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c34:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c35:Nat→ Nat:=c27 (c28 (Cond.size c34)); let c36:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")))); let c37:Nat:=c28 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat:=c36 c37; let c39:Nat:=c35 c38; let c40:Nat:=c33 c39; let c41:Nat:=c32 c40; let c42:Com:=Com.assign "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c43:Com→ Com→ Com:=Com.ite c34; let c44:Com:=Com.assign "cmp.le" (Expr.lit ((0:Nat))); let c45:Com:=Com.assign "cmp.le" (Expr.lit ((1:Nat))); let c46:Com:=Com.ite (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45; let c47:Com:=Com.ite (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45; let c48:Com:=c43 c46 c47; let c49:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c50:Cond:=Cond.eq (Expr.var "right.n") (Expr.lit ((0:Nat))); let c51:Com:=Com.ite c50 c45 c44; let c52:Com:=Com.ite c49 c51 c44; let c53:Com:=c43 c45 c52; let c54:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53; let c55:Nat→ Prop:=Nat.lt c22; let c56:Env:=c25 ((1:Nat)); let c57:Nat:=c28 (Expr.size (Expr.lit ((1:Nat)))); let c58:Nat:=c36 c57; let c59:Nat:=c35 c58; let c60:Nat:=c33 c59; let c61:Nat:=c32 c60; let c62:Prop:=c55 c20; let c63:Prop:=Not c62; let c64:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")))); let c65:Nat:=c64 c37; let c66:Nat:=c35 c65; let c67:Nat:=c33 c66; let c68:Nat:=c32 c67; let c69:Nat:=c64 c57; let c70:Nat:=c35 c69; let c71:Nat:=c33 c70; let c72:Nat:=c32 c71; let c73:Nat:=c35 c57; let c74:Nat:=c33 c73; let c75:Nat:=c32 c74; let c76:Nat:=c8 "left.n"; let c77:Prop:= @Eq Nat c76 ((0:Nat)); let c78:Prop:=Not c77; let c79:Nat:=c8 "right.n"; let c80:Prop:= @Eq Nat c79 ((0:Nat)); let c81:Prop:=Not c80; let c82:Nat→ Nat:=c27 (c28 (Cond.size c49)); let c83:Nat→ Nat:=c27 (c28 (Cond.size c50)); let c84:Nat:=c83 c57; let c85:Nat:=c82 c84; let c86:Nat:=c35 c85; let c87:Nat:=c33 c86; let c88:Nat:=c32 c87; let c89:Nat:=c83 c37; let c90:Nat:=c82 c89; let c91:Nat:=c35 c90; let c92:Nat:=c33 c91; let c93:Nat:=c32 c92; let c94:Nat:=c82 c37; let c95:Nat:=c35 c94; let c96:Nat:=c33 c95; let c97:Nat:=c32 c96; @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c17) (Classical.em c12) (fun (hcase:c12) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c17) (Classical.em c23) (fun (hcase_2:c23) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c41) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c41 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_1)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c40 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_3)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c39 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_5)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c26 c38 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_7)))))))) (?nAX_g3923_0_0_8)) ?_)) fun (hcase_2:c24) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c61) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c61 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_9)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_10)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c60 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_11)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_12)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c59 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_13)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_14)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c56 c58 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_15)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g3923_0_0_16)) ?_)) fun (hcase_1:c19) => @Or.casesOn c62 c63 (fun (x:Or c62 c63) => c17) (Classical.em c62) (fun (hcase_2:c62) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c68) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c68 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_17)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_18)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c67 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_19)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_20)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c66 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_21)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_22)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c26 c65 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_23)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_24)))))))) (?nAX_g3923_0_0_25)) ?_)) fun (hcase_2:c63) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c72) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c72 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_26)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_27)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c71 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_28)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_29)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c70 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_30)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_31)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c56 c69 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g3923_0_0_33)) ?_)) fun (hcase:c13) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c75) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c75 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_34)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_35)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c74 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_36)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_37)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c73 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_38)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_39)) hcase) (RunStep.ite_true B c34 c45 c52 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))) (?nAX_g3923_0_0_41)) ?_)) fun (hcase_1:c19) => @Or.casesOn c77 c78 (fun (x:Or c77 c78) => c17) (Classical.em c77) (fun (hcase_2:c77) => @Or.casesOn c80 c81 (fun (x:Or c80 c81) => c17) (Classical.em c80) (fun (hcase_3:c80) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c88) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c88 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_42)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_43)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c87 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_44)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_45)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c86 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_46)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_47)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c56 c85 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_48)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c56 c84 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g3923_0_0_49)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_50)) hcase_2) (RunStep.ite_true B c50 c45 c44 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g3923_0_0_51)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_52)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))))) (?nAX_g3923_0_0_53)) ?_)) fun (hcase_3:c81) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c93) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c93 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_54)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_55)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c92 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_56)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_57)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c91 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_58)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_59)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c90 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_60)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c26 c89 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g3923_0_0_61)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_62)) hcase_2) (RunStep.ite_false B c50 c45 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g3923_0_0_63)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_64)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_65))))))))) (?nAX_g3923_0_0_66)) ?_)) fun (hcase_2:c78) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c97) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c97 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g3923_0_0_67)) (RunStep.eval_var B σ "right.d" (?nAX_g3923_0_0_68)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c96 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g3923_0_0_69)) (RunStep.eval_var B c2 "left.d" (?nAX_g3923_0_0_70)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c95 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_71)) (RunStep.eval_var B c7 "right.s" (?nAX_g3923_0_0_72)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c94 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g3923_0_0_73)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B c49 c51 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g3923_0_0_74)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_75)) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g3923_0_0_76)))))))) (?nAX_g3923_0_0_77)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3923_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3923_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all))
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

end Lax109476Proofs.RamComparison

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

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

theorem height_inv (q:ℚ) (B:ℕ) (hq:Height q B):Height q⁻¹ B:=by
  have hB:1≤ B:=le_trans q.den_pos hq.2
  by_cases hz:q=0
  · subst q
    simpa using height_mono 0 height_zero hB
  · have hnum:(q⁻¹).num.natAbs≤ q.den:=by
      rw [Rat.num_inv,Int.natAbs_mul]
      have hs:q.num.sign.natAbs≤ 1:=by
        have hsign:=Int.sign_trichotomy q.num
        rcases hsign with h | h | h <;> rw [h] <;> norm_num
      simpa using Nat.mul_le_mul_right q.den hs
    exact ⟨hnum.trans hq.2,by rw [Rat.den_inv_of_ne_zero hz]; exact hq.1⟩

theorem height_nat (v B:ℕ) (hv:v≤ B) (hB:1≤ B):Height (v:ℚ) B:=by
  simpa [Height] using And.intro hv hB

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem fractionValue_height (s n d M:ℕ) (hn:n≤ M) (hd:d≤ M) (hdpos:0 < d):
    Height (fractionValue s n d) M:=by
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hnum]; exact (Nat.div_le_self _ _).trans hn,
    by rw [hden]; exact (Nat.div_le_self _ _).trans hd⟩

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

namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

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

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamPrimitiveBounds RamRationalArrays RamRounding RationalArithmeticBounds

def LeftValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "left.s") (σ.vars "left.n") (σ.vars "left.d")=q∧
    σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den∧ σ.vars "left.s" ≤ 1

def RightValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d")=q∧
    σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den∧ σ.vars "right.s" ≤ 1

theorem add_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) addFraction
      (fun _ τ => FractionOutput (q + r) τ) (72 * M.size + 96):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=addFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

theorem resultToLeft_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) resultToLeft (fun _ τ => LeftValue q τ) 6:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "left.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "rat.s")); let c7:Nat:=c5 (Expr.size (Expr.var "rat.n")); let c8:Nat:=c5 (Expr.size (Expr.var "rat.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B resultToLeft σ σ' ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ σ')) c3 (@And.intro (Run B resultToLeft σ c3 ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ c3) (RunStep.mono B resultToLeft σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.var "rat.s")) (Com.seq (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d"))) σ (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c3 c6 c9 (RunStep.assign B σ "left.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d")) (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g3972_0_0_0))) (RunStep.assign B c1 "left.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g3972_0_0_1))))) (?nAX_g3972_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3972_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftValue]

theorem resultToRight_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) resultToRight (fun _ τ => RightValue q τ) 6:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "right.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "rat.s")); let c7:Nat:=c5 (Expr.size (Expr.var "rat.n")); let c8:Nat:=c5 (Expr.size (Expr.var "rat.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B resultToRight σ σ' ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ σ')) c3 (@And.intro (Run B resultToRight σ c3 ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ c3) (RunStep.mono B resultToRight σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.var "rat.s")) (Com.seq (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d"))) σ (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c3 c6 c9 (RunStep.assign B σ "right.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d")) (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g3973_0_0_0))) (RunStep.assign B c1 "right.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g3973_0_0_1))))) (?nAX_g3973_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3973_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3973_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3973_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue]

theorem invert_spec (B M:ℕ) (q:ℚ) (h1:1 < B) (hMB:M < B) (hq:Height q M):
    Spec B (LeftValue q) invertFraction (fun _ τ => FractionOutput q⁻¹ τ) (36 * M.size + 40):=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  rw [hqn,hqd] at hqval
  obtain ⟨τ,hrun,hτ⟩:=invertFraction_spec B (σ.vars "left.s") q.num.natAbs q.den h1 hqs
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) σ ⟨rfl,hqn,hqd⟩
  refine ⟨τ,hrun.mono ?_, ?_⟩
  · have hs:=Nat.size_le_size hq.1; omega
  · simpa only [hqval] using hτ

theorem compare_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) RamComparison.compareFraction
      (fun _ τ => τ.vars "cmp.le" ≤ 1∧ (τ.vars "cmp.le"=1↔ q≤ r)) 40:=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=RamComparison.compareFraction_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

end Lax109476Proofs.RamFractionInterface

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem spec_with_write_frame {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧
      ∀ a∉ c.warrs,τ.arrs a=σ.arrs a) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  exact ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx),
    fun a ha => hr.frame_arr a ha⟩

end Lax109476Proofs.RamFrame

end

section

namespace Lax109476Proofs.RamRationalScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalArrays

theorem readLeft_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hname:RamCopy.Disjoint name "left"):
    Spec B (Value name q) (readLeft name) (fun _ τ => LeftValue q τ) 6:=by
  have hsn:name ++ ".n" ≠ "left.s" :=hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:name ++ ".d" ≠ "left.s" :=hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:name ++ ".d" ≠ "left.n" :=hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "left.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "left.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "left.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "left.n" c14; let c20:Com:=Com.assign "left.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (readLeft name) σ σ' ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ σ')) c9 (@And.intro (Run B (readLeft name) σ c9 ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ c9) (RunStep.mono B (readLeft name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "left.s" c12 c2 (RunStep.eval_var B σ c1 hs)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "left.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "left.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g4095_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4095_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,LeftValue]

theorem readRight_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hname:RamCopy.Disjoint name "right"):
    Spec B (Value name q) (readRight name) (fun _ τ => RightValue q τ) 6:=by
  have hsn:name ++ ".n" ≠ "right.s" :=hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:name ++ ".d" ≠ "right.s" :=hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:name ++ ".d" ≠ "right.n" :=hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "right.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "right.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "right.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "right.n" c14; let c20:Com:=Com.assign "right.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (readRight name) σ σ' ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ σ')) c9 (@And.intro (Run B (readRight name) σ c9 ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ c9) (RunStep.mono B (readRight name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "right.s" c12 c2 (RunStep.eval_var B σ c1 hs)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "right.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "right.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g4096_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4096_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,RightValue]

theorem save_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B)
    (hname:∀ s∈ [".s", ".n", ".d"], ∀ t∈ [".s", ".n", ".d"],name ++ s ≠ "rat" ++ t):
    Spec B (FractionOutput q) (save name) (fun _ τ => Value name q τ) 6:=by
  have hsn:name ++ ".s" ≠ "rat.n" :=hname ".s" (by simp) ".n" (by simp)
  have hsd:name ++ ".s" ≠ "rat.d" :=hname ".s" (by simp) ".d" (by simp)
  have hnd:name ++ ".n" ≠ "rat.d" :=hname ".n" (by simp) ".d" (by simp)
  have hsn':name ++ ".s" ≠ name ++ ".n" :=by simp
  have hsd':name ++ ".s" ≠ name ++ ".d" :=by simp
  have hnd':name ++ ".n" ≠ name ++ ".d" :=by simp
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Value name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".s"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.s"); let c4:String:=c1 ".n"; let c5:Nat:=Env.vars c3 "rat.n"; let c6:Env:=Env.setVar c3 c4 c5; let c7:String:=c1 ".d"; let c8:Nat:=Env.vars c6 "rat.d"; let c9:Env:=Env.setVar c6 c7 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "rat.s")); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c4 (Expr.var "rat.n"); let c17:Com:=Com.assign c7 (Expr.var "rat.d"); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((6:Nat))) (c0 σ')) c9 (@And.intro (Run B (save name) σ c9 ((6:Nat))) (c0 c9) (RunStep.mono B (save name) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.s")) (Com.seq c16 c17) σ c3 c9 c12 c15 (RunStep.assign B σ c2 (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hs)) (RunStep.seq B c16 c17 c3 c6 c9 c13 c14 (RunStep.assign B c3 c4 (Expr.var "rat.n") c5 (RunStep.eval_var B c3 "rat.n" ?_)) (RunStep.assign B c6 c7 (Expr.var "rat.d") c8 (RunStep.eval_var B c6 "rat.d" ?_)))) (?nAX_g4097_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4097_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,FractionOutput,Ne.symm hsn,Ne.symm hsd,Ne.symm hnd,
    Ne.symm hsn',Ne.symm hsd',Ne.symm hnd']

end Lax109476Proofs.RamRationalScalars

end

section

namespace Lax109476Proofs.RamScalarFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem value_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (q:ℚ) (h:Value name q σ)
    (hs:name ++ ".s" ∉ c.wvars) (hn:name ++ ".n" ∉ c.wvars)
    (hd:name ++ ".d" ∉ c.wvars):Value name q τ:=by
  simpa only [Value,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

theorem fraction_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (q:ℚ) (h:FractionOutput q σ)
    (hs:"rat.s" ∉ c.wvars) (hn:"rat.n" ∉ c.wvars)
    (hd:"rat.d" ∉ c.wvars):FractionOutput q τ:=by
  simpa only [FractionOutput,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

theorem left_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (q:ℚ) (h:LeftValue q σ)
    (hs:"left.s" ∉ c.wvars) (hn:"left.n" ∉ c.wvars)
    (hd:"left.d" ∉ c.wvars):LeftValue q τ:=by
  simpa only [LeftValue,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

end Lax109476Proofs.RamScalarFrame

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamEllipsoidWordBounds RamEllipsoidStoredBounds RamMatrixStorage

theorem array_length_of_bigStep {c:Com} {σ τ:Env} {K:ℕ}
    (hr:BigStep c σ τ K) (b:String):(τ.arrs b).length=(σ.arrs b).length:=by
  induction hr with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamBitLength

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem size_half_succ (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h _ =>
    rw [Nat.bit_div_two,Nat.size_bit (Nat.bit_ne_zero_iff.mpr h)]

theorem bitLengthStep_spec (B v k:ℕ) (hB:2 < B) (hv:v < B)
    (hk:k + 1 < B):
    Spec B (fun σ => σ.vars "bits.v"=v∧ σ.vars "bits.k"=k) bitLengthStep
      (fun _ σ' => σ'.vars "bits.v"=v / 2∧ σ'.vars "bits.k"=k + 1) 8:=by
  have hdiv:v / 2 < B:=(Nat.div_le_self _ _).trans_lt hv
  rintro σ ⟨hσv,hσk⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 v ((2:Nat)); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 k ((1:Nat)); let c4:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "bits.v") c1) (@Eq Nat (Env.vars σ' "bits.k") c3)) σ; let c5:Nat:=c0 (Env.vars σ "bits.v") ((2:Nat)); let c6:Env:=Env.setVar σ "bits.v" c5; let c7:Nat:=Env.vars c6 "bits.k"; let c8:Nat:=c2 c7 ((1:Nat)); let c9:Env:=Env.setVar c6 "bits.k" c8; let c10:Nat→ Nat:=c2 ((1:Nat)); let c11:Expr:=Expr.div (Expr.var "bits.v") (Expr.lit ((2:Nat))); let c12:Nat:=c10 (Expr.size c11); let c13:Expr:=Expr.add (Expr.var "bits.k") (Expr.lit ((1:Nat))); let c14:Nat:=c10 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B bitLengthStep σ σ' ((8:Nat))) (c4 σ')) c9 (@And.intro (Run B bitLengthStep σ c9 ((8:Nat))) (c4 c9) (RunStep.mono B bitLengthStep σ c9 (c2 c12 c14) ((8:Nat)) (RunStep.seq B (Com.assign "bits.v" c11) (Com.assign "bits.k" c13) σ c6 c9 c12 c14 (RunStep.assign B σ "bits.v" c11 c5 (RunStep.eval_div B σ (Expr.var "bits.v") (Expr.lit ((2:Nat))) (Env.vars σ "bits.v") ((2:Nat)) (RunStep.eval_var B σ "bits.v" (?nAX_g4666_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ hB) (?nAX_g4666_0_0_1))) (RunStep.assign B c6 "bits.k" c13 c8 (RunStep.eval_add B c6 (Expr.var "bits.k") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "bits.k" (?nAX_g4666_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g4666_0_0_3)) (?nAX_g4666_0_0_4)))) (?nAX_g4666_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4666_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem bitLengthLoop_spec (B n:ℕ) (hB:2 < B) (hn:n < B):
    Spec B (fun σ => σ.vars "bits.v"=n∧ σ.vars "bits.k"=0) bitLengthLoop
      (fun _ σ' => σ'.vars "bits.v"=0∧ σ'.vars "bits.k"=n.size)
      (12 * n.size + 4):=by
  let I:=fun σ:Env => σ.vars "bits.v" ≤ n∧
    σ.vars "bits.k" + (σ.vars "bits.v").size=n.size
  have hloop:Spec B (fun σ => σ.vars "bits.v"=n∧ σ.vars "bits.k"=0)
      bitLengthLoop (fun _ σ' => I σ'∧
        (Cond.lt (.lit 0) (.var "bits.v")).evalB B σ'=some false)
      (12 * n.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "bits.v").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))⟩
    · rintro σ ⟨hI,hc⟩
      have hvpos:0 < σ.vars "bits.v" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
        simpa using hc
      have hs:=size_half_succ (σ.vars "bits.v") hvpos
      have hsize:=RationalSizeBounds.size_le_self n
      have hk:σ.vars "bits.k" + 1 < B:=by
        have hp:=Nat.size_pos.mpr hvpos
        dsimp [I] at hI
        omega
      obtain ⟨τ,hr,hτv,hτk⟩:=bitLengthStep_spec B _ _ hB (hI.1.trans_lt hn) hk
        σ ⟨rfl,rfl⟩
      refine ⟨τ,hr, ?_, ?_⟩
      · dsimp [I] at hI ⊢
        rw [hτv,hτk]
        exact ⟨(Nat.div_le_self _ _).trans hI.1,by omega⟩
      · rw [hτv]; omega
    · rintro σ ⟨hσv,hσk⟩
      simp [I,hσv,hσk]
    · rintro σ ⟨hσv,_⟩
      simp only [hσv,Cond.size,Expr.size]
      omega
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hz:τ.vars "bits.v"=0:=by
    rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
    have h:¬ 0 < τ.vars "bits.v" :=of_decide_eq_false (Option.some.inj hc)
    omega
  exact ⟨hz,by simpa [I,hz] using hI.2⟩

theorem bitLength_spec (B n:ℕ) (hB:2 < B) (hn:n < B):
    Spec B (fun σ => σ.vars "bits.v"=n) bitLength
      (fun _ σ' => σ'.vars "bits.v"=0∧ σ'.vars "bits.k"=n.size)
      (12 * n.size + 6):=by
  have hl:=bitLengthLoop_spec B n hB hn
  (expose_names;
    (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "bits.v") n) => let c0:Env:=Env.setVar σ "bits.k" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B bitLengthLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size n)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size n))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size n)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B bitLength σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "bits.v") n) (@Eq Nat (Env.vars σ_1 "bits.k") ((0:Nat)))) bitLengthLoop c7 c4 hl c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size n)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size n)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B bitLength σ w c6) (c8 w) (RunStep.mono B bitLength σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "bits.k" (Expr.lit ((0:Nat)))) bitLengthLoop σ c0 w c12 c4 (RunStep.assign B σ "bits.k" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4668_0_0_0))) left) (?nAX_g4668_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4668_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4668_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

end Lax109476Proofs.RamBitLength

end

section

namespace Lax109476Proofs.RamSolverFrontEnd

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem clearing_word_guard (L w:ℕ) (hw:RamDecoder.wordWidth L≤ w):
    2 * (2 ^ L) ^ 2 + 3 < 2 ^ w:=by
  have he:2 * L + 3≤ w:=by unfold RamDecoder.wordWidth at hw; omega
  have hp:1≤ 2 ^ (2 * L):=Nat.one_le_pow _ _ (by decide)
  have hlarge:2 * (2 ^ L) ^ 2 + 3 < 2 ^ (2 * L + 3):=by
    rw [← pow_mul,Nat.mul_comm L 2,pow_add]
    norm_num
    omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) he)

end Lax109476Proofs.RamSolverFrontEnd

end

section

namespace Lax109476Proofs.RamContinuedFractionStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamFractionInterface RationalReconstruction

theorem nonnegative_tail (n d:ℕ) (hd:0 < d):
    tail (fractionValue 0 n d)=fractionValue 0 d (n % d):=by
  have hdQ:(d:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt hd
  have hsum:(d:ℚ) * (n / d:ℕ) + (n % d:ℕ)=n:=by exact_mod_cast Nat.div_add_mod n d
  have hfrac:Int.fract ((n:ℚ) / d)=((n % d:ℕ):ℚ) / d:=by
    simp only [Int.fract,Rat.floor_natCast_div_natCast, ← Int.natCast_ediv,Int.cast_natCast]
    field_simp
    nlinarith
  simp only [tail,fractionValue,if_neg (by decide:¬ (0:ℕ)=1),hfrac,inv_div]

set_option maxHeartbeats 0 in
theorem step_spec (B M n d:ℕ) (h1:1 < B) (hMB:M < B)
    (hn:n≤ M) (hd:d≤ M) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "left.n"=n∧ σ.vars "left.d"=d) step
      (fun _ τ => τ.vars "cf.a"=n / d∧ FractionOutput (tail (fractionValue 0 n d)) τ)
      (36 * M.size + 96):=by
  have hnB:=hn.trans_lt hMB
  have hdB:=hd.trans_lt hMB
  have hquotB:n / d < B:=(Nat.div_le_self _ _).trans_lt hnB
  have hprodB:n / d * d < B:=(Nat.div_mul_le_self _ _).trans_lt hnB
  have hremB:n - n / d * d < B:=(Nat.sub_le _ _).trans_lt hnB
  have hmod:n - n / d * d=n % d:=by simpa only [Nat.mul_comm] using (Nat.mod_def n d).symm
  have hds:=Nat.size_le_size hd
  have hp:Spec B (fun σ => σ.vars "left.n"=n∧ σ.vars "left.d"=d) quotientRemainder
      (fun _ τ => τ.vars "cf.a"=n / d∧ τ.vars "cf.r"=n % d∧
        τ.vars "left.d"=d∧ τ.vars "rat.s"=0) 12:=by
    rintro σ ⟨hσn,hσd⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 n d; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n d; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "cf.a") c1) (And (@Eq Nat (Env.vars τ "cf.r") c2) (And (@Eq Nat (Env.vars τ "left.d") d) (@Eq Nat (Env.vars τ "rat.s") ((0:Nat)))))) σ; let c4:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "left.d"); let c5:Env:=Env.setVar σ "cf.a" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "left.n"; let c8:Nat:=c6 "cf.a"; let c9:Nat:=c6 "left.d"; let c10:Nat:=Nat.mul c8 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10; let c12:Env:=Env.setVar c5 "cf.r" c11; let c13:Env:=Env.setVar c12 "rat.s" ((0:Nat)); let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.div (Expr.var "left.n") (Expr.var "left.d"))); let c17:Expr:=Expr.sub (Expr.var "left.n") (Expr.mul (Expr.var "cf.a") (Expr.var "left.d")); let c18:Nat:=c15 (Expr.size c17); let c19:Nat:=c15 (Expr.size (Expr.lit ((0:Nat)))); let c20:Nat:=c14 c18 c19; let c21:Com:=Com.assign "cf.r" c17; let c22:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c23:String→ Nat:=Env.vars c13; @Exists.intro Env (fun (σ':Env) => And (Run B quotientRemainder σ σ' ((12:Nat))) (c3 σ')) c13 (@And.intro (Run B quotientRemainder σ c13 ((12:Nat))) (c3 c13) (RunStep.mono B quotientRemainder σ c13 (c14 c16 c20) ((12:Nat)) (RunStep.seq B (Com.assign "cf.a" (Expr.div (Expr.var "left.n") (Expr.var "left.d"))) (Com.seq c21 c22) σ c5 c13 c16 c20 (RunStep.assign B σ "cf.a" (Expr.div (Expr.var "left.n") (Expr.var "left.d")) c4 (RunStep.eval_div B σ (Expr.var "left.n") (Expr.var "left.d") (Env.vars σ "left.n") (Env.vars σ "left.d") (RunStep.eval_var B σ "left.n" (?nAX_g4903_0_0_0)) (RunStep.eval_var B σ "left.d" (?nAX_g4903_0_0_1)) ?_)) (RunStep.seq B c21 c22 c5 c12 c13 c18 c19 (RunStep.assign B c5 "cf.r" c17 c11 (RunStep.eval_sub B c5 (Expr.var "left.n") (Expr.mul (Expr.var "cf.a") (Expr.var "left.d")) c7 c10 (RunStep.eval_var B c5 "left.n" (?nAX_g4903_0_0_2)) (RunStep.eval_mul B c5 (Expr.var "cf.a") (Expr.var "left.d") c8 c9 (RunStep.eval_var B c5 "cf.a" ?_) (RunStep.eval_var B c5 "left.d" (?nAX_g4903_0_0_3)) ?_) (?nAX_g4903_0_0_4))) (RunStep.assign B c12 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c12 (?nAX_g4903_0_0_5))))) (?nAX_g4903_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4903_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ,hr₁,hτa,hτr,hτd,hτs⟩:=hp σ hσ
  have hrB:n % d < B:=(Nat.mod_lt _ hdpos).trans hdB
  have hcond:=evalB_condEq
    (evalB_var (B:=B) (σ:=τ) (x:= "cf.r") (hτr ▸ hrB)) (evalB_lit (by omega:0 < B))
  simp only [hτr] at hcond
  by_cases hz:n % d=0
  · have hzero:Spec B (fun υ => υ.vars "rat.s"=0)
        (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
        (fun _ υ => FractionOutput 0 υ∧ υ.vars "rat.s"=τ.vars "rat.s") 4:=by
      intro υ hυs
      (expose_names;
        (refine let c0:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c1:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c2:Com:=Com.seq c0 c1; let c3:Env→ Nat→ Prop:=Run B c2 υ; let c4:Env→ Prop:=(fun (x υ_1:Env) => And (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) υ_1) (@Eq Nat (Env.vars υ_1 "rat.s") (Env.vars τ "rat.s"))) υ; let c5:Env:=Env.setVar υ "rat.n" ((0:Nat)); let c6:Env:=Env.setVar c5 "rat.d" ((1:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Nat:=c8 (Expr.size (Expr.lit ((1:Nat)))); @Exists.intro Env (fun (σ':Env) => And (c3 σ' ((4:Nat))) (c4 σ')) c6 (@And.intro (c3 c6 ((4:Nat))) (c4 c6) (RunStep.mono B c2 υ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B c0 c1 υ c5 c6 c9 c10 (RunStep.assign B υ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) υ (?nAX_g4903_1_0_0))) (RunStep.assign B c5 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 h1))) (?nAX_g4903_1_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4903_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear hr₁))
      all_goals simp_all [FractionOutput,fractionValue]
    obtain ⟨υ,hr₂,hυ,hυs⟩:=hzero τ hτs
    have hfinal:FractionOutput 0 υ:=hυ
    have hυa:=(hr₂.frame_var "cf.a" (by decide)).trans hτa
    refine ⟨υ, (hr₁.seq (Run.ite_true (by simpa [hz] using hcond) hr₂)).mono (by simp only [Cond.size,Expr.size]; omega),hυa, ?_⟩
    rw [nonnegative_tail n d hdpos]
    simpa only [hz,fractionValue,if_neg (by decide:¬ (0:ℕ)=1),Nat.cast_zero,div_zero] using hfinal
  · have hnorm:=RamFrame.spec_with_write_frame ["cf.a"]
      (normalizeFraction_output_spec B 0 d (n % d) (by decide) hdB hrB (Nat.pos_of_ne_zero hz))
      (by intro x hx; simp at hx; subst x; decide)
    have hfinish:Spec B
        (fun υ => υ.vars "left.d"=d∧ υ.vars "cf.r"=n % d∧ υ.vars "rat.s"=0)
        (.seq (.assign "rat.n" (.var "left.d"))
          (.seq (.assign "rat.d" (.var "cf.r")) normalizeFraction))
        (fun υ ρ => FractionOutput (fractionValue 0 d (n % d)) ρ∧ ρ.vars "cf.a"=υ.vars "cf.a")
        (36 * (n % d).size + 20):=by
      rintro υ ⟨hυd,hυr,hυs⟩
      (expose_names;
        (refine let c0:Nat:=Env.vars (Env.setVar υ "rat.n" (Env.vars υ "left.d")) "cf.r"; let c1:Env:=Env.setVar (Env.setVar υ "rat.n" (Env.vars υ "left.d")) "rat.d" c0; let c2:Env→ Nat→ Prop:=Run B normalizeFraction c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) n d; let c5:Nat→ Nat:=c3 (Nat.mul ((36:Nat)) (Nat.size c4)); let c6:Nat:=c5 ((16:Nat)); let c7:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) d c4); let c8:Env→ Prop:=RamFrame.FieldsAgree (@List.cons String "cf.a" (@List.nil String)) c1; let c9:Env→ Prop:=fun (σ':Env) => And (c2 σ' c6) (And (c7 σ') (And (c8 σ') (∀ a∉ Com.warrs normalizeFraction, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c1 a)))); let c10:Com:=Com.seq (Com.assign "rat.n" (Expr.var "left.d")) (Com.seq (Com.assign "rat.d" (Expr.var "cf.r")) normalizeFraction); let c11:Env→ Nat→ Prop:=Run B c10 υ; let c12:Nat:=c5 ((20:Nat)); let c13:Env→ Prop:=(fun (υ_1 ρ:Env) => And (c7 ρ) (@Eq Nat (Env.vars ρ "cf.a") (Env.vars υ_1 "cf.a"))) υ; let c14:Env→ Prop:=fun (σ':Env) => And (c11 σ' c12) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:String→ Nat:=Env.vars c1; let c17:Nat→ Nat:=c3 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.var "left.d")); let c19:Nat:=c17 (Expr.size (Expr.var "cf.r")); let c20:Nat:=c3 c19 c6; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c15) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") d) (And (@Eq Nat (Env.vars σ_1 "rat.d") c4) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (σ_1 τ_1:Env) => And (c7 τ_1) (And (RamFrame.FieldsAgree (@List.cons String "cf.a" (@List.nil String)) σ_1 τ_1) (∀ a∉ Com.warrs normalizeFraction, @Eq (List Nat) (Env.arrs τ_1 a) (Env.arrs σ_1 a)))) c6 hnorm c1 ?_) fun (w:Env) (h:And (c2 w c6) (And (c7 w) (And (c8 w) (∀ a∉ Com.warrs normalizeFraction, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a))))) => let c0_1:Prop:=And (c7 w) (And (c8 w) (∀ a∉ Com.warrs normalizeFraction, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a))); @And.casesOn (c2 w c6) c0_1 (fun (x:And (c2 w c6) c0_1) => c15) h fun (left:c2 w c6) (right:c0_1) => @Exists.intro Env c14 w (@And.intro (c11 w c12) (c13 w) (RunStep.mono B c10 υ w (c3 c18 c20) c12 (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.d")) (Com.seq (Com.assign "rat.d" (Expr.var "cf.r")) normalizeFraction) υ (Env.setVar υ "rat.n" (Env.vars υ "left.d")) w c18 c20 (RunStep.assign B υ "rat.n" (Expr.var "left.d") (Env.vars υ "left.d") (RunStep.eval_var B υ "left.d" (?nAX_g4903_2_0_0))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "cf.r")) normalizeFraction (Env.setVar υ "rat.n" (Env.vars υ "left.d")) c1 w c19 c6 (RunStep.assign B (Env.setVar υ "rat.n" (Env.vars υ "left.d")) "rat.d" (Expr.var "cf.r") c0 (RunStep.eval_var B (Env.setVar υ "rat.n" (Env.vars υ "left.d")) "cf.r" (?nAX_g4903_2_0_1))) left)) (?nAX_g4903_2_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4903_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4903_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear hr₁); (all_goals try clear h); (all_goals try clear left))
      all_goals clear hnorm
      all_goals simp_all [RamFrame.FieldsAgree]
    obtain ⟨υ,hr₂,hυ,hυa⟩:=hfinish τ ⟨hτd,hτr,hτs⟩
    have hrs:=(Nat.size_le_size (Nat.mod_lt n hdpos).le).trans hds
    refine ⟨υ, (hr₁.seq (Run.ite_false (by simpa [hz] using hcond) hr₂)).mono (by simp only [Cond.size,Expr.size]; omega),hυa.trans hτa, ?_⟩
    rw [nonnegative_tail n d hdpos]
    exact hυ

theorem nonnegative_representation (q:ℚ) (hq:0≤ q):
    fractionValue 0 q.num.natAbs q.den=q:=by
  have hn:0≤ q.num:=Rat.num_nonneg.mpr hq
  have hs:RamRationalArrays.rationalSign q=0:=by
    simp [RamRationalArrays.rationalSign,not_lt.mpr hn]
  simpa only [hs] using RamRationalArrays.canonical_fractionValue q

theorem floor_toNat (q:ℚ) (hq:0≤ q):
    (Int.floor q).toNat=q.num.natAbs / q.den:=by
  conv_lhs =>
    rw [← nonnegative_representation q hq]
    simp only [fractionValue,if_neg (by decide:¬ (0:ℕ)=1),
      Rat.floor_natCast_div_natCast, ← Int.natCast_ediv,Int.toNat_natCast]

theorem step_nonnegative_spec (B M:ℕ) (q:ℚ) (hq:0≤ q)
    (h1:1 < B) (hMB:M < B) (hh:RationalArithmeticBounds.Height q M):
    Spec B (LeftValue q) step
      (fun _ τ => τ.vars "cf.a"=(Int.floor q).toNat∧ FractionOutput (tail q) τ)
      (36 * M.size + 96):=by
  refine (step_spec B M q.num.natAbs q.den h1 hMB hh.1 hh.2 q.den_pos).pre
    (fun _ h => ⟨h.2.1,h.2.2.1⟩) |>.post ?_
  intro σ τ _ hτ
  simpa only [nonnegative_representation q hq,floor_toNat q hq] using hτ

end Lax109476Proofs.RamContinuedFractionStep

end

section

namespace Lax109476Proofs.ContinuedFractionBounds

open RationalArithmeticBounds RationalReconstruction RamContinuedFractionStep

theorem tail_nonneg (q:ℚ):0≤ tail q:=by
  exact inv_nonneg.mpr (Int.fract_nonneg q)

theorem tail_height (q:ℚ) (M:ℕ) (hq:0≤ q) (hh:Height q M):Height (tail q) M:=by
  have hM:1≤ M:=le_trans q.den_pos hh.2
  have hrep:=nonnegative_representation q hq
  rw [← hrep,nonnegative_tail q.num.natAbs q.den q.den_pos]
  by_cases hz:q.num.natAbs % q.den=0
  · simpa [hz,RamRational.fractionValue] using height_mono 0 height_zero hM
  · exact RamPrimitiveBounds.fractionValue_height 0 q.den (q.num.natAbs % q.den) M hh.2
      ((Nat.mod_lt _ q.den_pos).le.trans hh.2) (Nat.pos_of_ne_zero hz)

theorem iterated_tail_height (q:ℚ) (M j:ℕ) (hq:0≤ q) (hh:Height q M):
    0≤ tail^[j] q∧ Height (tail^[j] q) M:=by
  induction j with
  | zero => exact ⟨hq,hh⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨tail_nonneg _,tail_height _ M ih.1 ih.2⟩

theorem floor_height (q:ℚ) (M:ℕ) (hq:0≤ q) (hh:Height q M):Height (Int.floor q:ℚ) M:=by
  have hfloor:(Int.floor q:ℚ)=((Int.floor q).toNat:ℚ):=by
    exact_mod_cast (Int.toNat_of_nonneg (Int.floor_nonneg.mpr hq)).symm
  rw [hfloor]
  exact height_nat _ M ((floor_toNat q hq) ▸ (Nat.div_le_self _ _).trans hh.1) (le_trans q.den_pos hh.2)

theorem convergent_height (q:ℚ) (M k:ℕ) (hq:0≤ q) (hh:Height q M):
    Height (convergent q k) ((2 * M) ^ (k + 1)):=by
  have hM:1≤ M:=le_trans q.den_pos hh.2
  induction k generalizing q with
  | zero =>
    simpa only [convergent,Nat.zero_add,pow_one] using
      height_mono _ (floor_height q M hq hh) (by omega:M≤ 2 * M)
  | succ k ih =>
    have ht:=tail_height q M hq hh
    have hi:=ih (tail q) (tail_nonneg q) ht
    have ha:=height_add (Int.floor q:ℚ) (convergent (tail q) k)⁻¹
      M ((2 * M) ^ (k + 1)) (floor_height q M hq hh) (height_inv _ _ hi)
    simpa only [convergent,tail,pow_succ,Nat.mul_comm] using ha

end Lax109476Proofs.ContinuedFractionBounds

end

section

namespace Lax109476Proofs.RamContinuedFractionStack

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStep ContinuedFractionBounds

def Stack (q:ℚ) (j:ℕ) (σ:Env):Prop:=
  ∀ i < j, (σ.arrs "cf.stack").getD i 0=(Int.floor (tail^[i] q)).toNat

def Invariant (q:ℚ) (N K:ℕ) (σ:Env):Prop:=
  Stack q (σ.vars "cf.i") σ∧ (σ.arrs "cf.stack").length=N∧
    LeftValue (tail^[σ.vars "cf.i"] q) σ∧ σ.vars "cf.i" ≤ K∧ σ.vars "cf.limit"=K

set_option maxHeartbeats 0 in
theorem forwardStep_spec (B M N K:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q M)
    (h1:1 < B) (hMB:M < B) (hKB:K < B) (hKN:K≤ N):
    Spec B (fun σ => Invariant q N K σ∧ σ.vars "cf.i" < K) forwardStep
      (fun σ τ => Invariant q N K τ∧ τ.vars "cf.i"=σ.vars "cf.i" + 1)
      (36 * M.size + 109):=by
  rintro σ ⟨⟨hσstack,hσlen,hσleft,hσi,hσK⟩,hi⟩
  let j:=σ.vars "cf.i"
  let r:=tail^[j] q
  have hr:=iterated_tail_height q M j hq hh
  obtain ⟨τ,hr₁,hτa,hτtail⟩:=step_nonnegative_spec B M r hr.1 h1 hMB hr.2 σ hσleft
  have hτi:τ.vars "cf.i"=j:=hr₁.frame_var _ (by decide)
  have hτlen:(τ.arrs "cf.stack").length=N:=by
    rw [hr₁.frame_arr "cf.stack" (by decide)]
    exact hσlen
  have hτaB:τ.vars "cf.a" < B:=by
    rw [hτa,floor_toNat r hr.1]
    exact ((Nat.div_le_self _ _).trans hr.2.1).trans_lt hMB
  have hjiB:j < B:=hi.trans hKB
  have hjN:j < N:=hi.trans_le hKN
  have hr₂:Run B (.store "cf.stack" (.var "cf.i") (.var "cf.a")) τ
      (τ.setArr "cf.stack" j (Int.floor r).toNat) 3:=by
    apply Run.store
    · simpa only [hτi] using evalB_var (B:=B) (σ:=τ) (x:= "cf.i") (hτi ▸ hjiB)
    · simpa only [hτa] using evalB_var (B:=B) (σ:=τ) (x:= "cf.a") hτaB
    · rw [hτlen]; exact hi.trans_le hKN
  let υ:=τ.setArr "cf.stack" j (Int.floor r).toNat
  have hυtail:FractionOutput (tail r) υ:=hτtail
  have htHeight:=tail_height r M hr.1 hr.2
  obtain ⟨ρ,hr₃,hρleft⟩:=resultToLeft_spec B (tail r) h1
    (htHeight.1.trans_lt hMB) (htHeight.2.trans_lt hMB) υ hυtail
  have hρi:ρ.vars "cf.i"=j:=(hr₃.frame_var _ (by decide)).trans hτi
  have hsumB:Bop.add.apply (ρ.vars "cf.i") 1 < B:=by simpa [hρi] using lt_of_le_of_lt hi hKB
  have hr₄:Run B (.assign "cf.i" (.add (.var "cf.i") (.lit 1))) ρ (ρ.setVar "cf.i" (j + 1)) 4:=
    Run.assign (by simpa only [hρi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=ρ) (x:= "cf.i") (hρi ▸ hjiB)) (evalB_lit h1) hsumB))
  have hstack:Stack q (j + 1) (ρ.setVar "cf.i" (j + 1)):=by
    intro i hii
    change (ρ.arrs "cf.stack").getD i 0=_
    rw [hr₃.frame_arr "cf.stack" (by decide)]
    change ((τ.arrs "cf.stack").set j (Int.floor r).toNat).getD i 0=_
    by_cases hij:i=j
    · subst i
      simp [List.getD_eq_getElem?_getD,List.getElem?_set,hτlen,hjN,r]
    · have hiold:i < j:=by omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_set,Ne.symm hij, ↓reduceIte]
      rw [hr₁.frame_arr "cf.stack" (by decide)]
      simpa only [List.getD_eq_getElem?_getD] using hσstack i hiold
  have hlen:((ρ.setVar "cf.i" (j + 1)).arrs "cf.stack").length=N:=by
    rw [arrs_setVar,hr₃.frame_arr "cf.stack" (by decide)]
    simp only [υ,Env.setArr,ite_true,List.length_set,hτlen]
  have hleft:LeftValue (tail^[j + 1] q) (ρ.setVar "cf.i" (j + 1)):=by
    simpa [LeftValue,vars_setVar,Function.iterate_succ_apply',r] using hρleft
  have hlimit:(ρ.setVar "cf.i" (j + 1)).vars "cf.limit"=K:=
    ((hr₁.seq (hr₂.seq (hr₃.seq hr₄))).frame_var _ (by decide)).trans hσK
  refine ⟨_,hr₁.seq (hr₂.seq (hr₃.seq hr₄)), ⟨hstack,hlen, ?_, ?_,hlimit⟩, ?_⟩
  · simpa only [vars_setVar,ite_true] using hleft
  · change j + 1≤ K; exact hi
  · simp [j]

theorem forward_spec (B M N K:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q M)
    (h1:1 < B) (hMB:M < B) (hKB:K < B) (hKN:K≤ N):
    Spec B (fun σ => (σ.arrs "cf.stack").length=N∧ LeftValue q σ∧ σ.vars "cf.limit"=K)
      forward (fun _ τ => Stack q K τ∧ (τ.arrs "cf.stack").length=N∧
        LeftValue (tail^[K] q) τ∧ τ.vars "cf.i"=K)
      ((36 * M.size + 113) * K + 6):=by
  have hlo:=Spec.forRangeZero "cf.i" "cf.limit" (Invariant q N K) K (36 * M.size + 109) hKB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2)
    (forwardStep_spec B M N K q hq hh h1 hMB hKB hKN)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hlen,hleft,hK⟩
    exact ⟨by intro i hi; simp at hi,hlen,hleft,by simp,hK⟩
  · rintro σ τ _ ⟨hτ,hcounter⟩
    simpa only [hcounter] using And.intro hτ.1 (And.intro hτ.2.1 (And.intro hτ.2.2.1 hcounter))

end Lax109476Proofs.RamContinuedFractionStack

end

section

namespace Lax109476Proofs.ContinuedFractionFold

open RationalArithmeticBounds RationalReconstruction ContinuedFractionBounds

def fold (q:ℚ) (K:ℕ):ℕ→ ℚ
  | 0 => 0
  | t + 1 => (Int.floor (tail^[K - (t + 1)] q):ℚ) + (fold q K t)⁻¹

theorem fold_eq_convergent (q:ℚ) (K t:ℕ) (ht:t < K):
    fold q K (t + 1)=convergent (tail^[K - (t + 1)] q) t:=by
  induction t with
  | zero => simp [fold,convergent]
  | succ t ih =>
    have ht':t < K:=by omega
    have hind:=ih ht'
    have hindex:K - (t + 1)=K - (t + 1 + 1) + 1:=by omega
    rw [fold,hind,hindex,Function.iterate_succ_apply']
    rfl

theorem fold_height (q:ℚ) (M K t:ℕ) (hq:0≤ q) (hh:Height q M) (ht:t≤ K):
    Height (fold q K t) ((2 * M) ^ (K + 1)):=by
  have hM:1≤ M:=le_trans q.den_pos hh.2
  cases t with
  | zero =>
    exact height_mono _ height_zero (Nat.one_le_pow _ _ (by omega))
  | succ t =>
    rw [fold_eq_convergent q K t (by omega)]
    have hr:=iterated_tail_height q M (K - (t + 1)) hq hh
    exact height_mono _ (convergent_height _ M t hr.1 hr.2)
      (Nat.pow_le_pow_right (by omega) (by omega))

theorem fold_complete (q:ℚ) (k:ℕ):fold q (k + 1) (k + 1)=convergent q k:=by
  simpa using fold_eq_convergent q (k + 1) k (by omega)

end Lax109476Proofs.ContinuedFractionFold

end

section

namespace Lax109476Proofs.RamContinuedFractionFoldStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStack ContinuedFractionBounds ContinuedFractionFold

 theorem restoreFloor_spec (B N i a:ℕ) (hi:i < N) (hiB:i < B) (h1:1 < B) (haB:a < B):
    Spec B (fun σ => (σ.arrs "cf.stack").length=N∧
        (σ.arrs "cf.stack").getD i 0=a∧ σ.vars "cf.back"=i)
      restoreFloor (fun _ τ => LeftValue (a:ℚ) τ) 7:=by
  rintro σ ⟨hσlen,hσa,hσi⟩
  have hil:i < (σ.arrs "cf.stack").length:=hσlen ▸ hi
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => LeftValue (@Nat.cast Rat Rat.instNatCast a) τ) σ; let c1:Env:=Env.setVar σ "left.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "cf.back"; let c3:Nat:= @List.getD Nat (Env.arrs c1 "cf.stack") c2 ((0:Nat)); let c4:Env:=Env.setVar c1 "left.n" c3; let c5:Env:=Env.setVar c4 "left.d" ((1:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.get "cf.stack" (Expr.var "cf.back"))); let c10:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c11:Nat:=c6 c9 c10; let c12:Com:=Com.assign "left.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B restoreFloor σ σ' ((7:Nat))) (c0 σ')) c5 (@And.intro (Run B restoreFloor σ c5 ((7:Nat))) (c0 c5) (RunStep.mono B restoreFloor σ c5 (c6 c8 c11) ((7:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "left.n" (Expr.get "cf.stack" (Expr.var "cf.back"))) c12) σ c1 c5 c8 c11 (RunStep.assign B σ "left.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4923_0_0_0))) (RunStep.seq B (Com.assign "left.n" (Expr.get "cf.stack" (Expr.var "cf.back"))) c12 c1 c4 c5 c9 c10 (RunStep.assign B c1 "left.n" (Expr.get "cf.stack" (Expr.var "cf.back")) c3 (RunStep.eval_get B c1 "cf.stack" (Expr.var "cf.back") c2 (RunStep.eval_var B c1 "cf.back" (?nAX_g4923_0_0_1)) (?nAX_g4923_0_0_2) ?_)) (RunStep.assign B c4 "left.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1)))) (?nAX_g4923_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4923_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4923_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4923_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4923_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftValue,fractionValue]

 def Invariant (q:ℚ) (N K:ℕ) (σ:Env):Prop:=
  Stack q K σ∧ (σ.arrs "cf.stack").length=N∧ σ.vars "cf.done" ≤ K∧
    σ.vars "cf.limit"=K∧ FractionOutput (ContinuedFractionFold.fold q K (σ.vars "cf.done")) σ

set_option maxHeartbeats 0 in
theorem foldStep_spec (B M N K:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q M)
    (hKB:K < B) (hKN:K≤ N) (hB:2 * ((2 * M) ^ (K + 1)) ^ 2 + 3 < B):
    Spec B (fun σ => Invariant q N K σ∧ σ.vars "cf.done" < K) foldStep
      (fun σ τ => Invariant q N K τ∧ τ.vars "cf.done"=σ.vars "cf.done" + 1)
      (108 * ((2 * M) ^ (K + 1)).size + 204):=by
  let R:=(2 * M) ^ (K + 1)
  have hM:1≤ M:=le_trans q.den_pos hh.2
  have hR:1≤ R:=Nat.one_le_pow _ _ (by omega)
  have hMR:M≤ R:=(by omega:M≤ 2 * M).trans
    (le_self_pow (by omega:1≤ 2 * M) (by omega:K + 1 ≠ 0))
  have hRB:R < B:=by dsimp only [R] at *; nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨⟨hσstack,hσlen,hσdone,hσK,hσresult⟩,ht⟩
  let t:=σ.vars "cf.done"
  let j:=K - (t + 1)
  let r:=ContinuedFractionFold.fold q K t
  let a:=(Int.floor (tail^[j] q)).toNat
  have hj:j < K:=by dsimp [j,t]; omega
  have hjN:j < N:=hj.trans_le hKN
  have htB:t < B:=ht.trans hKB
  have hjB:j < B:=hj.trans hKB
  have htHeight:=fold_height q M K t hq hh hσdone
  have hrHeight:Height r R:=htHeight
  have hInv:=height_inv r R hrHeight
  have htail:=iterated_tail_height q M j hq hh
  have haM:a≤ M:=by
    dsimp only [a]
    rw [RamContinuedFractionStep.floor_toNat _ htail.1]
    exact (Nat.div_le_self _ _).trans htail.2.1
  have haR:Height (a:ℚ) R:=height_nat _ _ (haM.trans hMR) hR
  have hindex:Spec B (fun υ => υ.vars "cf.limit"=K∧ υ.vars "cf.done"=t)
      (.assign "cf.back" (.sub (.sub (.var "cf.limit") (.var "cf.done")) (.lit 1)))
      (fun _ υ => υ.vars "cf.back"=j) 6:=by
    rintro υ ⟨hυK,hυt⟩
    have hsubB:K - t < B:=(Nat.sub_le _ _).trans_lt hKB
    (expose_names;
      (refine let c0:Expr:=Expr.sub (Expr.sub (Expr.var "cf.limit") (Expr.var "cf.done")) (Expr.lit ((1:Nat))); let c1:Com:=Com.assign "cf.back" c0; let c2:Env→ Nat→ Prop:=Run B c1 υ; let c3:Env→ Prop:=(fun (x υ_1:Env) => @Eq Nat (Env.vars υ_1 "cf.back") j) υ; let c4:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c5:Nat:=c4 (Env.vars υ "cf.limit") (Env.vars υ "cf.done"); let c6:Nat:=c4 c5 ((1:Nat)); let c7:Env:=Env.setVar υ "cf.back" c6; @Exists.intro Env (fun (σ':Env) => And (c2 σ' ((6:Nat))) (c3 σ')) c7 (@And.intro (c2 c7 ((6:Nat))) (c3 c7) (RunStep.mono B c1 υ c7 (Nat.add ((1:Nat)) (Expr.size c0)) ((6:Nat)) (RunStep.assign B υ "cf.back" c0 c6 (RunStep.eval_sub B υ (Expr.sub (Expr.var "cf.limit") (Expr.var "cf.done")) (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_sub B υ (Expr.var "cf.limit") (Expr.var "cf.done") (Env.vars υ "cf.limit") (Env.vars υ "cf.done") (RunStep.eval_var B υ "cf.limit" (?nAX_g4926_0_0_0)) (RunStep.eval_var B υ "cf.done" (?nAX_g4926_0_0_1)) (?nAX_g4926_0_0_2)) (RunStep.eval_lit B ((1:Nat)) υ h1) (?nAX_g4926_0_0_3))) (?nAX_g4926_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4926_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4926_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4926_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4926_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4926_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [j]
    all_goals omega
  obtain ⟨τ,hr₁,hτj⟩:=hindex σ ⟨hσK,rfl⟩
  have hτresult:FractionOutput r τ:=by
    simpa only [FractionOutput,hr₁.frame_var "rat.s" (by decide),
      hr₁.frame_var "rat.n" (by decide),hr₁.frame_var "rat.d" (by decide)] using hσresult
  obtain ⟨υ,hr₂,hυleft⟩:=resultToLeft_spec B r h1
    (hrHeight.1.trans_lt hRB) (hrHeight.2.trans_lt hRB) τ hτresult
  obtain ⟨ρ,hr₃,hρresult⟩:=invert_spec B R r h1 hRB hrHeight υ hυleft
  obtain ⟨χ,hr₄,hχright⟩:=resultToRight_spec B r⁻¹ h1
    (hInv.1.trans_lt hRB) (hInv.2.trans_lt hRB) ρ hρresult
  have hrArithmetic:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hχlen:(χ.arrs "cf.stack").length=N:=by
    rw [hrArithmetic.frame_arr "cf.stack" (by decide)]
    exact hσlen
  have hχj:χ.vars "cf.back"=j:=
    ((hr₂.seq (hr₃.seq hr₄)).frame_var _ (by decide)).trans hτj
  have hχa:(χ.arrs "cf.stack").getD j 0=a:=by
    rw [hrArithmetic.frame_arr "cf.stack" (by decide)]
    exact hσstack j hj
  obtain ⟨ψ,hr₅,hψleft⟩:=restoreFloor_spec B N j a hjN hjB h1 ((haM.trans hMR).trans_lt hRB)
    χ ⟨hχlen,hχa,hχj⟩
  have hψright:RightValue r⁻¹ ψ:=by
    simpa only [RightValue,hr₅.frame_var "right.s" (by decide),
      hr₅.frame_var "right.n" (by decide),hr₅.frame_var "right.d" (by decide)] using hχright
  obtain ⟨ω,hr₆,hωresult⟩:=add_spec B R (a:ℚ) r⁻¹ hB haR hInv ψ ⟨hψleft,hψright⟩
  have hrBefore:=hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq hr₆))))
  have hωt:ω.vars "cf.done"=t:=hrBefore.frame_var _ (by decide)
  have hsumB:Bop.add.apply (ω.vars "cf.done") 1 < B:=by simpa [hωt] using lt_of_le_of_lt ht hKB
  have hr₇:Run B (.assign "cf.done" (.add (.var "cf.done") (.lit 1))) ω (ω.setVar "cf.done" (t + 1)) 4:=
    Run.assign (by simpa only [hωt,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=ω) (x:= "cf.done") (hωt ▸ htB)) (evalB_lit h1) hsumB))
  have hfloor:(a:ℚ)=(Int.floor (tail^[j] q):ℚ):=by
    dsimp only [a]
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr htail.1)
  have hnext:FractionOutput (ContinuedFractionFold.fold q K (t + 1)) ω:=by
    simpa only [ContinuedFractionFold.fold, ← hfloor,j,r] using hωresult
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))
  refine ⟨_,hr.mono (by dsimp only [R]; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [hr.frame_arr "cf.stack" (by decide)]
    exact hσstack i hi
  · rw [hr.frame_arr "cf.stack" (by decide)]
    exact hσlen
  · change t + 1≤ K; exact ht
  · exact (hr.frame_var _ (by decide)).trans hσK
  · simpa [FractionOutput,vars_setVar] using hnext
  · simp [t]

end Lax109476Proofs.RamContinuedFractionFoldStep

end

section

namespace Lax109476Proofs.RamContinuedFractionConvergent

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction
open RamContinuedFractionStack ContinuedFractionBounds ContinuedFractionFold RamContinuedFractionFoldStep

theorem zeroResult_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zeroResult (fun _ τ => FractionOutput 0 τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zeroResult σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zeroResult σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zeroResult σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4929_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g4929_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4929_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4929_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4929_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4929_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,fractionValue]

theorem foldStack_spec (B M N K:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q M)
    (hKB:K < B) (hKN:K≤ N) (hB:2 * ((2 * M) ^ (K + 1)) ^ 2 + 3 < B):
    Spec B (fun σ => Stack q K σ∧ (σ.arrs "cf.stack").length=N∧ σ.vars "cf.limit"=K)
      foldStack (fun _ τ => FractionOutput (ContinuedFractionFold.fold q K K) τ)
      ((108 * ((2 * M) ^ (K + 1)).size + 208) * K + 12):=by
  have h1:1 < B:=by omega
  have hlo:=Spec.forRangeZero "cf.done" "cf.limit" (RamContinuedFractionFoldStep.Invariant q N K) K
    (108 * ((2 * M) ^ (K + 1)).size + 204) hKB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (foldStep_spec B M N K q hq hh hKB hKN hB)
  have hloop:Spec B
      (fun σ => Stack q K σ∧ (σ.arrs "cf.stack").length=N∧ σ.vars "cf.limit"=K∧ FractionOutput 0 σ)
      (.seq (.assign "cf.done" (.lit 0)) (.while (.lt (.var "cf.done") (.var "cf.limit")) foldStep))
      (fun _ τ => FractionOutput (ContinuedFractionFold.fold q K K) τ)
      ((108 * ((2 * M) ^ (K + 1)).size + 208) * K + 6):=by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hstack,hlen,hK,hresult⟩
      refine ⟨?_,hlen,by simp,hK, ?_⟩
      · simpa only [Stack,arrs_setVar] using hstack
      · simpa [FractionOutput,vars_setVar,ContinuedFractionFold.fold] using hresult
    · rintro σ τ _ ⟨hτ,hcounter⟩
      simpa only [hcounter] using hτ.2.2.2.2
  rintro σ ⟨hσstack,hσlen,hσK⟩
  obtain ⟨τ,hr₁,hτresult⟩:=zeroResult_spec B h1 σ trivial
  have hτstack:Stack q K τ:=by
    intro i hi
    rw [hr₁.frame_arr "cf.stack" (by decide)]
    exact hσstack i hi
  have hτlen:(τ.arrs "cf.stack").length=N:=by
    rw [hr₁.frame_arr "cf.stack" (by decide)]; exact hσlen
  have hτK:=(hr₁.frame_var "cf.limit" (by decide)).trans hσK
  obtain ⟨υ,hr₂,hυ⟩:=hloop τ ⟨hτstack,hτlen,hτK,hτresult⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυ⟩

theorem convergent_spec (B M N k:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q M)
    (hKB:k + 1 < B) (hKN:k + 1≤ N) (hB:2 * ((2 * M) ^ (k + 2)) ^ 2 + 3 < B):
    Spec B (fun σ => (σ.arrs "cf.stack").length=N∧ LeftValue q σ∧ σ.vars "cf.depth"=k)
      convergent (fun _ τ => FractionOutput (RationalReconstruction.convergent q k) τ)
      (((36 * M.size + 113) + (108 * ((2 * M) ^ (k + 2)).size + 208)) * (k + 1) + 22):=by
  have hM:1≤ M:=le_trans q.den_pos hh.2
  have hR:M≤ (2 * M) ^ (k + 2):=(by omega:M≤ 2 * M).trans
    (le_self_pow (by omega:1≤ 2 * M) (by omega:k + 2 ≠ 0))
  have hMB:M < B:=by nlinarith
  have h1:1 < B:=by omega
  rintro σ ⟨hσlen,hσleft,hσk⟩
  have hr₁:Run B (.assign "cf.limit" (.add (.var "cf.depth") (.lit 1))) σ
      (σ.setVar "cf.limit" (k + 1)) 4:=by
    apply Run.assign
    simpa only [hσk,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=σ) (x:= "cf.depth") (hσk ▸ (by omega:k < B)))
      (evalB_lit h1) (show Bop.add.apply (σ.vars "cf.depth") 1 < B by simpa [hσk] using hKB))
  obtain ⟨τ,hr₂,hτstack,hτlen,hτleft,hτi⟩:=forward_spec B M N (k + 1) q hq hh h1 hMB hKB hKN
    (σ.setVar "cf.limit" (k + 1)) ⟨hσlen,by simpa [LeftValue,vars_setVar] using hσleft,by simp⟩
  have hτK:τ.vars "cf.limit"=k + 1:=
    (hr₂.frame_var _ (by decide)).trans (by simp)
  obtain ⟨υ,hr₃,hυ⟩:=foldStack_spec B M N (k + 1) q hq hh hKB hKN hB τ ⟨hτstack,hτlen,hτK⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_, ?_⟩
  · simp only [Nat.add_mul,Nat.add_assoc,Nat.reduceAdd]
    omega
  · simpa only [fold_complete] using hυ

end Lax109476Proofs.RamContinuedFractionConvergent

end

section

namespace Lax109476Proofs.RamConvergentBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RationalReconstruction

theorem intermediate_bound (S K k:ℕ) (hk:k≤ K):
    (2 * 2 ^ S) ^ (k + 2)≤ 2 ^ exponent S K:=by
  rw [show 2 * 2 ^ S=2 ^ (S + 1) by rw [pow_succ]; omega, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left (S + 1) (by omega))

theorem convergent_spec (S K N k w:ℕ) (q:ℚ) (hq:0≤ q) (hh:Height q (2 ^ S))
    (hk:k≤ K) (hN:K + 1≤ N) (hw:wordWidth S K≤ w):
    Spec (2 ^ w) (fun σ => (σ.arrs "cf.stack").length=N∧ LeftValue q σ∧ σ.vars "cf.depth"=k)
      RamContinuedFractionConvergent.convergent
      (fun _ τ => FractionOutput (RationalReconstruction.convergent q k) τ)
      (instructionBound S K):=by
  have hwD:RamDecoder.wordWidth (exponent S K)≤ w:=by unfold wordWidth at hw; omega
  have hKB:k + 1 < 2 ^ w:=(by unfold wordWidth at hw; omega:k + 1≤ w).trans_lt (Nat.lt_two_pow_self (n:=w))
  have hR:=intermediate_bound S K k hk
  have hguard:=(Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hR 2)) 3).trans_lt
    (RamSolverFrontEnd.clearing_word_guard (exponent S K) w hwD)
  have hcost:
      (((36 * (2 ^ S).size + 113) + (108 * ((2 * 2 ^ S) ^ (k + 2)).size + 208)) * (k + 1) + 22)≤
        instructionBound S K:=by
    have hs:=Nat.size_le_size hR
    rw [Nat.size_pow] at hs
    rw [Nat.size_pow]
    unfold instructionBound
    gcongr
  exact (RamContinuedFractionConvergent.convergent_spec (2 ^ w) (2 ^ S) N k q hq hh
    hKB (by omega) hguard).mono hcost

end Lax109476Proofs.RamConvergentBounds

end

section

namespace Lax109476Proofs.RamReconstructionCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem finish_spec (B D:ℕ) (l u r:ℚ) (h1:1 < B) (hDB:D < B) (hrd:r.den < B):
    Spec B (fun σ => σ.vars "recon.bound"=D∧ σ.vars "rat.d"=r.den∧
      σ.vars "recon.lower"=(if l≤ r then 1 else 0)∧ σ.vars "cmp.le"=(if r≤ u then 1 else 0))
      finish (fun _ τ => τ.vars "recon.accept"=(if r.den≤ D∧ l≤ r∧ r≤ u then 1 else 0)) 18:=by
  rintro σ ⟨hD,hd,hl,hu⟩
  have hlow:σ.vars "recon.lower" < B:=by rw [hl]; split_ifs <;> omega
  have hupper:σ.vars "cmp.le" < B:=by rw [hu]; split_ifs <;> omega
  (expose_names;
    (refine let c0:Prop:=Nat.lt (Env.vars σ "recon.bound") (Env.vars σ "rat.d"); let c1:Prop:=Not c0; let c2:Prop:=And (@LE.le Rat Rat.instLE l r) (@LE.le Rat Rat.instLE r u); let c3:Nat:= @ite Nat (And (Nat.le (Rat.den r) D) c2) (@instDecidableAnd (Nat.le (Rat.den r) D) c2 (Nat.decLe (Rat.den r) D) (@instDecidableAnd (@LE.le Rat Rat.instLE l r) (@LE.le Rat Rat.instLE r u) (Rat.instDecidableLe l r) (Rat.instDecidableLe r u))) ((1:Nat)) ((0:Nat)); let c4:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "recon.accept") c3) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B finish σ σ' ((18:Nat))) (c4 σ'); let c6:Env:=Env.setVar σ "recon.accept" ((0:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat→ Nat:=c7 (c8 (Cond.size (Cond.lt (Expr.var "recon.bound") (Expr.var "rat.d")))); let c10:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "recon.accept" (Expr.lit ((0:Nat))); let c12:Cond:=Cond.eq (Expr.var "recon.lower") (Expr.lit ((1:Nat))); let c13:Com:=Com.ite c12 (Com.assign "recon.accept" (Expr.var "cmp.le")) c11; let c14:Prop:= @Eq Nat (Env.vars σ "recon.lower") ((1:Nat)); let c15:Prop:=Not c14; let c16:Nat→ Nat:=c7 (c8 (Cond.size c12)); let c17:Nat:=c8 (Expr.size (Expr.var "cmp.le")); let c18:Nat:=c16 c17; let c19:Nat:=c16 c10; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c5 c6 (@And.intro (Run B finish σ c6 ((18:Nat))) (c4 c6) (RunStep.mono B finish σ c6 (c9 c10) ((18:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "recon.bound") (Expr.var "rat.d")) c11 c13 σ c6 c10 (RunStep.cond_lt_true B σ (Expr.var "recon.bound") (Expr.var "rat.d") (Env.vars σ "recon.bound") (Env.vars σ "rat.d") (RunStep.eval_var B σ "recon.bound" (?nAX_g4939_0_0_0)) (RunStep.eval_var B σ "rat.d" (?nAX_g4939_0_0_1)) hcase) (RunStep.assign B σ "recon.accept" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4939_0_0_2)))) (?nAX_g4939_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c14 c15 (fun (x:Or c14 c15) => @Exists Env c5) (Classical.em c14) (fun (hcase_1:c14) => @Exists.intro Env c5 (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le")) (@And.intro (Run B finish σ (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le")) ((18:Nat))) (c4 (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le"))) (RunStep.mono B finish σ (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le")) (c9 c18) ((18:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "recon.bound") (Expr.var "rat.d")) c11 c13 σ (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le")) c18 (RunStep.cond_lt_false B σ (Expr.var "recon.bound") (Expr.var "rat.d") (Env.vars σ "recon.bound") (Env.vars σ "rat.d") (RunStep.eval_var B σ "recon.bound" (?nAX_g4939_0_0_4)) (RunStep.eval_var B σ "rat.d" (?nAX_g4939_0_0_5)) hcase) (RunStep.ite_true B c12 (Com.assign "recon.accept" (Expr.var "cmp.le")) c11 σ (Env.setVar σ "recon.accept" (Env.vars σ "cmp.le")) c17 (RunStep.cond_eq_true B σ (Expr.var "recon.lower") (Expr.lit ((1:Nat))) (Env.vars σ "recon.lower") ((1:Nat)) (RunStep.eval_var B σ "recon.lower" hlow) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase_1) (RunStep.assign B σ "recon.accept" (Expr.var "cmp.le") (Env.vars σ "cmp.le") (RunStep.eval_var B σ "cmp.le" hupper)))) (?nAX_g4939_0_0_6)) ?_)) fun (hcase_1:c15) => @Exists.intro Env c5 c6 (@And.intro (Run B finish σ c6 ((18:Nat))) (c4 c6) (RunStep.mono B finish σ c6 (c9 c19) ((18:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "recon.bound") (Expr.var "rat.d")) c11 c13 σ c6 c19 (RunStep.cond_lt_false B σ (Expr.var "recon.bound") (Expr.var "rat.d") (Env.vars σ "recon.bound") (Env.vars σ "rat.d") (RunStep.eval_var B σ "recon.bound" (?nAX_g4939_0_0_7)) (RunStep.eval_var B σ "rat.d" (?nAX_g4939_0_0_8)) hcase) (RunStep.ite_false B c12 (Com.assign "recon.accept" (Expr.var "cmp.le")) c11 σ c6 c10 (RunStep.cond_eq_false B σ (Expr.var "recon.lower") (Expr.lit ((1:Nat))) (Env.vars σ "recon.lower") ((1:Nat)) (RunStep.eval_var B σ "recon.lower" hlow) (RunStep.eval_lit B ((1:Nat)) σ h1) hcase_1) (RunStep.assign B σ "recon.accept" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4939_0_0_9))))) (?nAX_g4939_0_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4939_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4939_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals split_ifs <;> simp_all <;> omega

theorem flag_eq (v:ℕ) (p:Prop) [Decidable p] (hv:v≤ 1) (he:v=1↔ p):
    v=(if p then 1 else 0):=by split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 0 in
theorem check_spec (B M D:ℕ) (l u r:ℚ) (hB:2 * M ^ 2 + 3 < B) (hDB:D < B)
    (hl:Height l M) (hu:Height u M) (hr:Height r M):
    Spec B (fun σ => Value "recon.lo" l σ∧ Value "recon.hi" u σ∧ FractionOutput r σ∧
      σ.vars "recon.bound"=D) check
      (fun _ τ => τ.vars "recon.accept"=(if r.den≤ D∧ l≤ r∧ r≤ u then 1 else 0)∧
        FractionOutput r τ) 124:=by
  have h1:1 < B:=by omega
  have hMB:M < B:=by nlinarith
  rintro σ ⟨hσl,hσu,hσr,hσD⟩
  obtain ⟨τ,hr₁,hτl⟩:=readLeft_spec B "recon.lo" l h1 (hl.1.trans_lt hMB)
    (hl.2.trans_lt hMB) (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ hσl
  have hτr:=fraction_frame hr₁ r hσr (by decide) (by decide) (by decide)
  obtain ⟨υ,hr₂,hυr⟩:=resultToRight_spec B r h1 (hr.1.trans_lt hMB) (hr.2.trans_lt hMB) τ hτr
  have hυl:=left_frame hr₂ l hτl (by decide) (by decide) (by decide)
  obtain ⟨ρ,hr₃,hρflag⟩:=compare_spec B M l r hB hl hr υ ⟨hυl,hυr⟩
  have hρlo:=flag_eq (ρ.vars "cmp.le") (l≤ r) hρflag.1 hρflag.2
  have hρloB:ρ.vars "cmp.le" < B:=hρflag.1.trans_lt h1
  have hr₄:Run B (.assign "recon.lower" (.var "cmp.le")) ρ
      (ρ.setVar "recon.lower" (ρ.vars "cmp.le")) 2:=Run.assign (evalB_var hρloB)
  let ξ:=ρ.setVar "recon.lower" (ρ.vars "cmp.le")
  have hξr:=fraction_frame (hr₁.seq (hr₂.seq (hr₃.seq hr₄))) r hσr (by decide) (by decide) (by decide)
  obtain ⟨ζ,hr₅,hζr⟩:=resultToLeft_spec B r h1 (hr.1.trans_lt hMB) (hr.2.trans_lt hMB) ξ hξr
  have hζu:=value_frame (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))) "recon.hi" u hσu
    (by decide) (by decide) (by decide)
  obtain ⟨η,hr₆,hηu⟩:=readRight_spec B "recon.hi" u h1 (hu.1.trans_lt hMB)
    (hu.2.trans_lt hMB) (by simp [RamCopy.Disjoint,RamCopy.suffixes]) ζ hζu
  have hηr:=left_frame hr₆ r hζr (by decide) (by decide) (by decide)
  obtain ⟨θ,hr₇,hθflag⟩:=compare_spec B M r u hB hr hu η ⟨hηr,hηu⟩
  have hθupper:=flag_eq (θ.vars "cmp.le") (r≤ u) hθflag.1 hθflag.2
  have hrun:=hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq hr₇)))))
  have hθr:=fraction_frame hrun r hσr (by decide) (by decide) (by decide)
  have hθD:=(hrun.frame_var "recon.bound" (by decide)).trans hσD
  have hθlower:θ.vars "recon.lower"=(if l≤ r then 1 else 0):=by
    rw [(hr₅.seq (hr₆.seq hr₇)).frame_var "recon.lower" (by decide)]
    exact hρlo
  obtain ⟨κ,hr₈,hκ⟩:=finish_spec B D l u r h1 hDB (hr.2.trans_lt hMB) θ
    ⟨hθD,hθr.2.2.1,hθlower,hθupper⟩
  exact ⟨κ, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq (hr₆.seq (hr₇.seq hr₈))))))).mono (by omega),hκ,
    fraction_frame hr₈ r hθr (by decide) (by decide) (by decide)⟩

end Lax109476Proofs.RamReconstructionCandidate

end

section

namespace Lax109476Proofs.RamConvergentCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem testCandidate_spec (S K N j w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hj:j≤ K) (hN:K + 1≤ N)
    (hw:RamConvergentBounds.wordWidth S K≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ∧ Value "recon.hi" u σ∧
      σ.vars "recon.bound"=D∧ σ.vars "recon.i"=j∧ (σ.arrs "cf.stack").length=N)
      testCandidate
      (fun _ τ => τ.vars "recon.accept" =
        (if (RationalReconstruction.convergent u j).den≤ D∧ l≤ RationalReconstruction.convergent u j∧
          RationalReconstruction.convergent u j≤ u then 1 else 0)∧
        FractionOutput (RationalReconstruction.convergent u j) τ)
      (RamConvergentBounds.instructionBound S K + 132):=by
  let E:=RamConvergentBounds.exponent S K
  let R:=2 ^ E
  have hSE:S≤ E:=by dsimp [E,RamConvergentBounds.exponent]; nlinarith
  have hMR:2 ^ S≤ R:=Nat.pow_le_pow_right (by decide) hSE
  have hwD:RamDecoder.wordWidth E≤ w:=by dsimp only [E]; unfold RamConvergentBounds.wordWidth at hw; omega
  have hguard:=RamSolverFrontEnd.clearing_word_guard E w hwD
  have hRB:R < 2 ^ w:=by dsimp only [R]; apply Nat.pow_lt_pow_right (by decide); unfold RamDecoder.wordWidth at hwD; omega
  have h1:1 < 2 ^ w:=by omega
  have hjB:j < 2 ^ w:=(by unfold RamConvergentBounds.wordWidth at hw; omega:j≤ w).trans_lt (Nat.lt_two_pow_self (n:=w))
  have hcr:Height (RationalReconstruction.convergent u j) R:=
    height_mono _ (ContinuedFractionBounds.convergent_height u (2 ^ S) j hu0 hu)
      ((Nat.pow_le_pow_right (by positivity) (show j + 1≤ j + 2 by omega)).trans
        (RamConvergentBounds.intermediate_bound S K j hj))
  rintro σ ⟨hσl,hσu,hσD,hσj,hσN⟩
  obtain ⟨τ,hr₁,hτu⟩:=readLeft_spec (2 ^ w) "recon.hi" u h1
    ((hu.1.trans hMR).trans_lt hRB) ((hu.2.trans hMR).trans_lt hRB)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ hσu
  have hτj:τ.vars "recon.i"=j:=(hr₁.frame_var _ (by decide)).trans hσj
  have hr₂:Run (2 ^ w) (.assign "cf.depth" (.var "recon.i")) τ (τ.setVar "cf.depth" j) 2:=
    Run.assign (by simpa only [hτj] using evalB_var (B:=2 ^ w) (σ:=τ) (x:= "recon.i") (hτj ▸ hjB))
  have hleft:LeftValue u (τ.setVar "cf.depth" j):=by simpa [LeftValue,vars_setVar] using hτu
  have hlen:((τ.setVar "cf.depth" j).arrs "cf.stack").length=N:=by
    rw [arrs_setVar,hr₁.frame_arr _ (by decide)]; exact hσN
  obtain ⟨υ,hr₃,hυ⟩:=RamConvergentBounds.convergent_spec S K N j w u hu0 hu hj hN hw
    (τ.setVar "cf.depth" j) ⟨hlen,hleft,by simp⟩
  have hrPre:=hr₁.seq (hr₂.seq hr₃)
  have hυl:=value_frame hrPre "recon.lo" l hσl (by decide) (by decide) (by decide)
  have hυu:=value_frame hrPre "recon.hi" u hσu (by decide) (by decide) (by decide)
  have hυD:=(hrPre.frame_var _ (by decide)).trans hσD
  obtain ⟨ρ,hr₄,hρ⟩:=RamReconstructionCandidate.check_spec (2 ^ w) R D l u
    (RationalReconstruction.convergent u j) hguard hDB (height_mono _ hl hMR) (height_mono _ hu hMR)
    hcr υ ⟨hυl,hυu,hυ,hυD⟩
  exact ⟨ρ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega),hρ⟩

end Lax109476Proofs.RamConvergentCandidate

end

section

namespace Lax109476Proofs.ReconstructionPrefix

def acceptable (l u:ℚ) (D:ℕ) (q:ℚ):Bool:=decide (q.den≤ D∧ l≤ q∧ q≤ u)

def scan (l u:ℚ) (D j:ℕ):Option ℚ:=
  ((List.range j).map (RationalReconstruction.convergent u)).find? (acceptable l u D)

theorem scan_zero (l u:ℚ) (D:ℕ):scan l u D 0=none:=by simp [scan]

theorem scan_succ (l u:ℚ) (D j:ℕ):
    scan l u D (j + 1)=match scan l u D j with
      | some q => some q
      | none => if acceptable l u D (RationalReconstruction.convergent u j) then
          some (RationalReconstruction.convergent u j) else none:=by
  simp only [scan,List.range_succ,List.map_append,List.map_singleton,List.find?_append,
    List.find?_cons,List.find?_nil]
  cases h:((List.range j).map (RationalReconstruction.convergent u)).find? (acceptable l u D) <;> simp
  cases acceptable l u D (RationalReconstruction.convergent u j) <;> rfl

theorem scan_complete (l u:ℚ) (D:ℕ):
    scan l u D (2 * u.den.size + 1)=RationalReconstruction.reconstruct l u D:=rfl

end Lax109476Proofs.ReconstructionPrefix

end

section

namespace Lax109476Proofs.RamReconstructionRecord

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem record_spec (B:ℕ) (q:ℚ) (h1:1 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) record (fun _ τ => Output (some q) τ) 8:=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=save_spec B "recon.result" q h1 hn hd
    (by simp) σ hσ
  have hr₂:Run B (.assign "recon.found" (.lit 1)) τ (τ.setVar "recon.found" 1) 2:=
    Run.assign (evalB_lit h1)
  exact ⟨_,hr₁.seq hr₂,by simp [Output],value_frame hr₂ "recon.result" q hτ (by decide) (by decide) (by decide)⟩

theorem candidate_spec (S K N j w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hj:j≤ K) (hN:K + 1≤ N)
    (hw:RamConvergentBounds.wordWidth S K≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ∧ Value "recon.hi" u σ∧
      σ.vars "recon.bound"=D∧ σ.vars "recon.i"=j∧ (σ.arrs "cf.stack").length=N∧
      σ.vars "recon.found"=0) candidate
      (fun _ τ => Output (if ReconstructionPrefix.acceptable l u D (RationalReconstruction.convergent u j)
        then some (RationalReconstruction.convergent u j) else none) τ)
      (RamConvergentBounds.instructionBound S K + 144):=by
  let q:=RationalReconstruction.convergent u j
  let E:=RamConvergentBounds.exponent S K
  have hheight:Height q (2 ^ E):=height_mono _
    (ContinuedFractionBounds.convergent_height u (2 ^ S) j hu0 hu)
    ((Nat.pow_le_pow_right (by positivity) (show j + 1≤ j + 2 by omega)).trans
      (RamConvergentBounds.intermediate_bound S K j hj))
  have hwD:RamDecoder.wordWidth E≤ w:=by dsimp only [E]; unfold RamConvergentBounds.wordWidth at hw; omega
  have hRB:2 ^ E < 2 ^ w:=Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwD; omega)
  have h1:1 < 2 ^ w:=(Nat.one_le_pow _ _ (by decide)).trans_lt hRB
  rintro σ ⟨hσl,hσu,hσD,hσj,hσN,hσfound⟩
  obtain ⟨τ,hr₁,hτaccept,hτq⟩:=RamConvergentCandidate.testCandidate_spec S K N j w D l u hu0
    hl hu hj hN hw hDB σ ⟨hσl,hσu,hσD,hσj,hσN⟩
  have hτfound:=(hr₁.frame_var "recon.found" (by decide)).trans hσfound
  have hflag:τ.vars "recon.accept"=if q.den≤ D∧ l≤ q∧ q≤ u then 1 else 0:=hτaccept
  have hflagB:τ.vars "recon.accept" < 2 ^ w:=by rw [hflag]; split_ifs <;> omega
  have hcond:=evalB_condEq (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "recon.accept") hflagB) (evalB_lit h1)
  by_cases hp:q.den≤ D∧ l≤ q∧ q≤ u
  · have ht:(Cond.eq (.var "recon.accept") (.lit 1)).evalB (2 ^ w) τ=some true:=by simpa [hflag,hp] using hcond
    obtain ⟨υ,hr₂,hυ⟩:=record_spec (2 ^ w) q h1 (hheight.1.trans_lt hRB) (hheight.2.trans_lt hRB) τ hτq
    refine ⟨υ, (hr₁.seq (Run.ite_true (d:=.skip) ht hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    change Output (if decide (q.den≤ D∧ l≤ q∧ q≤ u) then some q else none) υ
    simpa [hp] using hυ
  · have ht:(Cond.eq (.var "recon.accept") (.lit 1)).evalB (2 ^ w) τ=some false:=by simpa [hflag,hp] using hcond
    refine ⟨τ, (hr₁.seq (Run.ite_false (c:=record) ht Run.skip)).mono
      (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    change Output (if decide (q.den≤ D∧ l≤ q∧ q≤ u) then some q else none) τ
    simpa [hp,Output] using hτfound

end Lax109476Proofs.RamReconstructionRecord

end

section

namespace Lax109476Proofs.RamReconstructionSearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame
open RamReconstructionRecord ReconstructionPrefix

def Invariant (l u:ℚ) (D N K:ℕ) (σ:Env):Prop:=
  Value "recon.lo" l σ∧ Value "recon.hi" u σ∧ σ.vars "recon.bound"=D∧
    σ.vars "recon.limit"=K∧ (σ.arrs "cf.stack").length=N∧ σ.vars "recon.i" ≤ K∧
    Output (scan l u D (σ.vars "recon.i")) σ

theorem output_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (r:Option ℚ) (h:Output r σ) (hf:"recon.found" ∉ c.wvars)
    (hs:"recon.result.s" ∉ c.wvars) (hn:"recon.result.n" ∉ c.wvars)
    (hd:"recon.result.d" ∉ c.wvars):Output r τ:=by
  cases r with
  | none => exact (hr.frame_var _ hf).trans h
  | some q => exact ⟨(hr.frame_var _ hf).trans h.1,value_frame hr "recon.result" q h.2 hs hn hd⟩

set_option maxHeartbeats 0 in
theorem searchStep_spec (S K N w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hN:K + 1≤ N)
    (hw:RamConvergentBounds.wordWidth S K≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Invariant l u D N K σ∧ σ.vars "recon.i" < K)
      searchStep (fun σ τ => Invariant l u D N K τ∧ τ.vars "recon.i"=σ.vars "recon.i" + 1)
      (RamConvergentBounds.instructionBound S K + 152):=by
  have hKB:K + 1 < 2 ^ w:=(by unfold RamConvergentBounds.wordWidth at hw; omega:K + 1≤ w).trans_lt
    (Nat.lt_two_pow_self (n:=w))
  have h1:1 < 2 ^ w:=by omega
  rintro σ ⟨⟨hσl,hσu,hσD,hσK,hσN,hσi,hσout⟩,hi⟩
  let j:=σ.vars "recon.i"
  have hphase:∃ τ,Run (2 ^ w) (.ite (.eq (.var "recon.found") (.lit 1)) .skip candidate) σ τ
      (RamConvergentBounds.instructionBound S K + 148)∧ Output (scan l u D (j + 1)) τ:=by
    cases hp:scan l u D j with
    | none =>
      have hfound:σ.vars "recon.found"=0:=by
        change Output (scan l u D j) σ at hσout
        simpa only [hp,Output] using hσout
      have hcond:(Cond.eq (.var "recon.found") (.lit 1)).evalB (2 ^ w) σ=some false:=by
        simpa [hfound] using evalB_condEq (evalB_var (B:=2 ^ w) (σ:=σ) (x:= "recon.found") (by rw [hfound]; omega)) (evalB_lit h1)
      obtain ⟨τ,hr,ht⟩:=candidate_spec S K N j w D l u hu0 hl hu hσi hN hw hDB σ
        ⟨hσl,hσu,hσD,rfl,hσN,hfound⟩
      refine ⟨τ, (Run.ite_false (c:=.skip) hcond hr).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simpa only [scan_succ,hp] using ht
    | some q =>
      have hout:σ.vars "recon.found"=1∧ Value "recon.result" q σ:=by
        change Output (scan l u D j) σ at hσout
        simpa only [hp,Output] using hσout
      have hcond:(Cond.eq (.var "recon.found") (.lit 1)).evalB (2 ^ w) σ=some true:=by
        simpa [hout.1] using evalB_condEq (evalB_var (B:=2 ^ w) (σ:=σ) (x:= "recon.found") (by rw [hout.1]; omega)) (evalB_lit h1)
      refine ⟨σ, (Run.ite_true (d:=candidate) hcond Run.skip).mono
        (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simpa only [scan_succ,hp,Output] using hout
  obtain ⟨τ,hr₁,hτout⟩:=hphase
  have hτi:τ.vars "recon.i"=j:=hr₁.frame_var _ (by decide)
  have hjB:j < 2 ^ w:=hi.trans (by omega)
  have hsumB:Bop.add.apply (τ.vars "recon.i") 1 < 2 ^ w:=by
    simpa [hτi] using (show j + 1 < 2 ^ w by dsimp only [j]; omega)
  have hr₂:Run (2 ^ w) (.assign "recon.i" (.add (.var "recon.i") (.lit 1))) τ
      (τ.setVar "recon.i" (j + 1)) 4:=Run.assign (by
        simpa only [hτi,Bop.apply_add] using (evalB_bin
          (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "recon.i") (hτi ▸ hjB)) (evalB_lit h1) hsumB))
  have hr:=hr₁.seq hr₂
  have hout:=output_frame hr₂ (scan l u D (j + 1)) hτout (by decide) (by decide) (by decide) (by decide)
  refine ⟨_,hr, ⟨value_frame hr "recon.lo" l hσl (by decide) (by decide) (by decide),
    value_frame hr "recon.hi" u hσu (by decide) (by decide) (by decide),
    (hr.frame_var _ (by decide)).trans hσD, (hr.frame_var _ (by decide)).trans hσK,
    ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨t,_,ht⟩:=hr.bigStep
    exact (RamAdvanceState.array_length_of_bigStep ht "cf.stack").trans hσN
  · change j + 1≤ K; omega
  · simpa only [vars_setVar,ite_true] using hout
  · simp [j]

theorem search_spec (S K N w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hN:K + 1≤ N)
    (hw:RamConvergentBounds.wordWidth S K≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ∧ Value "recon.hi" u σ∧
      σ.vars "recon.bound"=D∧ σ.vars "recon.limit"=K∧ (σ.arrs "cf.stack").length=N)
      search (fun _ τ => Output (scan l u D K) τ)
      ((RamConvergentBounds.instructionBound S K + 156) * K + 8):=by
  have hKB:K < 2 ^ w:=(by unfold RamConvergentBounds.wordWidth at hw; omega:K≤ w).trans_lt
    (Nat.lt_two_pow_self (n:=w))
  have hlo:=Spec.forRangeZero "recon.i" "recon.limit" (Invariant l u D N K) K
    (RamConvergentBounds.instructionBound S K + 152) hKB
    (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.1)
    (searchStep_spec S K N w D l u hu0 hl hu hN hw hDB)
  rintro σ ⟨hσl,hσu,hσD,hσK,hσN⟩
  have hr₁:Run (2 ^ w) (.assign "recon.found" (.lit 0)) σ (σ.setVar "recon.found" 0) 2:=
    Run.assign (evalB_lit (by omega))
  have hinit:Invariant l u D N K ((σ.setVar "recon.found" 0).setVar "recon.i" 0):=by
    refine ⟨?_, ?_, ?_, ?_,hσN,by simp, ?_⟩
    · simpa [Value,vars_setVar] using hσl
    · simpa [Value,vars_setVar] using hσu
    · simpa using hσD
    · simpa using hσK
    · simp [scan_zero,Output]
  obtain ⟨τ,hr₂,hτ,hcounter⟩:=hlo (σ.setVar "recon.found" 0) hinit
  refine ⟨τ, (hr₁.seq hr₂).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega), ?_⟩
  simpa only [hcounter] using hτ.2.2.2.2.2.2

end Lax109476Proofs.RamReconstructionSearch

end

section

namespace Lax109476Proofs.RamRationalReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem prepare_spec (B:ℕ) (u:ℚ) (h2:2 < B) (hd:u.den < B) (hK:2 * u.den.size + 1 < B):
    Spec B (Value "recon.hi" u) prepare
      (fun _ τ => τ.vars "recon.limit"=2 * u.den.size + 1) (12 * u.den.size + 14):=by
  have hbits:=RationalSizeBounds.size_le_self u.den
  have hb:=RamBitLength.bitLength_spec B u.den h2 hd
  rintro σ ⟨hval,hn,hσd,hs⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B RamBitLength.bitLength (Env.setVar σ "bits.v" (Env.vars σ "recon.hi.d")); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat→ Nat:=c1 (c2 ((12:Nat)) (Nat.size (Rat.den u))); let c4:Nat:=c3 ((6:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' c4) (And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size (Rat.den u)))); let c6:Nat:=c3 ((14:Nat)); let c7:Nat:=c1 (c2 ((2:Nat)) (Nat.size (Rat.den u))) ((1:Nat)); let c8:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "recon.limit") c7) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B prepare σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:Nat→ Nat:=c1 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "recon.hi.d")); let c13:Expr:=Expr.mul (Expr.var "bits.k") (Expr.lit ((2:Nat))); let c14:Expr:=Expr.add c13 (Expr.lit ((1:Nat))); let c15:Nat:=c11 (Expr.size c14); let c16:Nat:=c1 c4 c15; let c17:Com:=Com.assign "recon.limit" c14; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "bits.v") (Rat.den u)) RamBitLength.bitLength (fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size (Rat.den u)))) c4 hb (Env.setVar σ "bits.v" (Env.vars σ "recon.hi.d")) ?_) fun (w:Env) (h:And (c0 w c4) (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size (Rat.den u))))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size (Rat.den u))); let c1_1:Nat:=c2 (Env.vars w "bits.k") ((2:Nat)); let c2_1:Nat:=c1 c1_1 ((1:Nat)); let c3_1:Env:=Env.setVar w "recon.limit" c2_1; @And.casesOn (c0 w c4) c0_1 (fun (x:And (c0 w c4) c0_1) => c10) h fun (left:c0 w c4) (right:c0_1) => @Exists.intro Env c9 c3_1 (@And.intro (Run B prepare σ c3_1 c6) (c8 c3_1) (RunStep.mono B prepare σ c3_1 (c1 c12 c16) c6 (RunStep.seq B (Com.assign "bits.v" (Expr.var "recon.hi.d")) (Com.seq RamBitLength.bitLength c17) σ (Env.setVar σ "bits.v" (Env.vars σ "recon.hi.d")) c3_1 c12 c16 (RunStep.assign B σ "bits.v" (Expr.var "recon.hi.d") (Env.vars σ "recon.hi.d") (RunStep.eval_var B σ "recon.hi.d" ?_)) (RunStep.seq B RamBitLength.bitLength c17 (Env.setVar σ "bits.v" (Env.vars σ "recon.hi.d")) w c3_1 c4 c15 left (RunStep.assign B w "recon.limit" c14 c2_1 (RunStep.eval_add B w c13 (Expr.lit ((1:Nat))) c1_1 ((1:Nat)) (RunStep.eval_mul B w (Expr.var "bits.k") (Expr.lit ((2:Nat))) (Env.vars w "bits.k") ((2:Nat)) (RunStep.eval_var B w "bits.k" (?nAX_g4965_0_0_0)) (RunStep.eval_lit B ((2:Nat)) w h2) (?nAX_g4965_0_0_1)) (RunStep.eval_lit B ((1:Nat)) w (?nAX_g4965_0_0_2)) (?nAX_g4965_0_0_3))))) (?nAX_g4965_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4965_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4965_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4965_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4965_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4965_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [mul_comm]
  all_goals omega

theorem reconstruct_spec (S N w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hN:depthBound S + 1≤ N)
    (hw:wordWidth S≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Value "recon.lo" l σ∧ Value "recon.hi" u σ∧
      σ.vars "recon.bound"=D∧ (σ.arrs "cf.stack").length=N)
      reconstruct (fun _ τ => RamReconstructionRecord.Output (RationalReconstruction.reconstruct l u D) τ)
      (instructionBound S):=by
  let K:=2 * u.den.size + 1
  have hsize:u.den.size≤ S + 1:=by have:=Nat.size_le_size hu.2; rwa [Nat.size_pow] at this
  have hK:K≤ depthBound S:=by dsimp only [K,depthBound]; omega
  have hwK:RamConvergentBounds.wordWidth S K≤ w:=by
    have hm:RamConvergentBounds.wordWidth S K≤ RamConvergentBounds.wordWidth S (depthBound S):=by
      unfold RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
      gcongr
    exact hm.trans hw
  have hKB:K < 2 ^ w:=(by unfold wordWidth RamConvergentBounds.wordWidth at hw; omega:K≤ w).trans_lt
    (Nat.lt_two_pow_self (n:=w))
  have h2:2 < 2 ^ w:=by
    have hp:=Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤ w by
      unfold wordWidth RamConvergentBounds.wordWidth at hw; omega)
    norm_num at hp; omega
  have hHB:2 ^ S < 2 ^ w:=Nat.pow_lt_pow_right (by decide) (by
    unfold wordWidth RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth at hw
    unfold depthBound at hw
    nlinarith)
  rintro σ ⟨hσl,hσu,hσD,hσN⟩
  obtain ⟨τ,hr₁,hτK⟩:=prepare_spec (2 ^ w) u h2 (hu.2.trans_lt hHB) hKB σ hσu
  have hτl:=value_frame hr₁ "recon.lo" l hσl (by decide) (by decide) (by decide)
  have hτu:=value_frame hr₁ "recon.hi" u hσu (by decide) (by decide) (by decide)
  have hτD:=(hr₁.frame_var _ (by decide)).trans hσD
  have hτN:(τ.arrs "cf.stack").length=N:=by rw [hr₁.frame_arr _ (by decide)]; exact hσN
  obtain ⟨υ,hr₂,hυ⟩:=RamReconstructionSearch.search_spec S K N w D l u hu0 hl hu
    (by omega) hwK hDB τ ⟨hτl,hτu,hτD,hτK,hτN⟩
  have hcost:(RamConvergentBounds.instructionBound S K + 156) * K≤
      (RamConvergentBounds.instructionBound S (depthBound S) + 156) * depthBound S:=by
    unfold RamConvergentBounds.instructionBound RamConvergentBounds.exponent
    gcongr
  refine ⟨υ, (hr₁.seq hr₂).mono (by unfold instructionBound; omega), ?_⟩
  simpa only [K,ReconstructionPrefix.scan_complete] using hυ

end Lax109476Proofs.RamRationalReconstruction

end

theorem solution:∀ (S N w D:Nat) (l u:Rat),
  @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) u→
    Lax109476Proofs.RationalArithmeticBounds.Height l
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) S)→
      Lax109476Proofs.RationalArithmeticBounds.Height u
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) S)→
        Nat.le
            (Nat.add (Lax109476Proofs.RamRationalReconstruction.depthBound S)
              ((1:Nat)))
            N→
          Nat.le (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w→
            Nat.lt D
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w)→
              Lax808846Proofs.Reasoning.Spec
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w)
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (Lax109476Proofs.RamRationalScalars.Value "recon.lo" l σ)
                    (And (Lax109476Proofs.RamRationalScalars.Value "recon.hi" u σ)
                      (And (@Eq Nat (σ.vars "recon.bound") D) (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N))))
                Lax109476Proofs.RamRationalReconstruction.reconstruct
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamReconstructionRecord.Output
                    (Lax109476Proofs.RationalReconstruction.reconstruct l u D) τ)
                (Lax109476Proofs.RamRationalReconstruction.instructionBound S):= @Lax109476Proofs.RamRationalReconstruction.reconstruct_spec
