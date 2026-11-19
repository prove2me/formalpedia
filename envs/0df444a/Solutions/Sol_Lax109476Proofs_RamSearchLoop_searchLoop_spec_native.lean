-- Prove2me | solution 1 for Lax109476Proofs.RamSearchLoop.searchLoop_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:56.113891+00:00
-- url     : https://prove2.me/submissions/c246e9ab-4068-435b-8d4f-42cec0432528

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamEllipsoidStep_ellipsoidStep_spec
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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem length_arrOf (n:ℕ) (f:ℕ→ ℕ):(arrOf n f).length=n:=by
  simp [arrOf]

theorem replicate_eq_arrOf (n v:ℕ):List.replicate n v=arrOf n (fun _ => v):=by
  simp [arrOf,List.map_const']

theorem arrOf_congr {n:ℕ} {f g:ℕ→ ℕ} (h:∀ i < n,f i=g i):
    arrOf n f=arrOf n g:=by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf,List.length_map,List.length_range] at h₁
  simp [arrOf,h k h₁]

theorem set_arrOf {n i:ℕ} (f:ℕ→ ℕ) (v:ℕ):
    (arrOf n f).set i v=arrOf n (fun k => if k=i then v else f k):=by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk:k=i
  · subst hk; simp [arrOf]
  · simp [arrOf,hk,Ne.symm hk]

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

theorem _root_.Lax808846Proofs.Imp.BigStep.out_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k):c.NoWrite→ σ'.out=σ.out:=by
  induction h with
  | skip => intro _; rfl
  | assign _ => intro _; rfl
  | store _ _ _ => intro _; rfl
  | seq _ _ ih ih' => intro hc; rw [ih' hc.2,ih hc.1]
  | ite_true _ _ ih => intro hc; exact ih hc.1
  | ite_false _ _ ih => intro hc; exact ih hc.2
  | while_true _ _ _ ih ih' => intro hc; rw [ih' hc,ih hc]
  | while_false _ => intro _; rfl
  | read _ => intro _; rfl
  | write _ => intro hc; exact absurd hc not_false

theorem Run.out_eq {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hc:c.NoWrite):σ'.out=σ.out:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.out_eq hc

end Lax808846Proofs.Reasoning

end

section

namespace Lax109476Proofs.RationalRounding

theorem grid_num_den_bound (k:ℤ) (D:ℕ) (hD:0 < D):
    ((k:ℚ) / D).num.natAbs≤ k.natAbs∧ ((k:ℚ) / D).den≤ D:=by
  obtain ⟨c,hnum,hden⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den k
    (d:=(D:ℤ)) (by exact_mod_cast ne_of_gt hD)
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hden
    have hDn:(D:ℤ) ≠ 0:=by exact_mod_cast ne_of_gt hD
    exact hDn hden
  have hcpos:0 < c.natAbs:=Int.natAbs_pos.mpr hc
  have hnumAbs:k.natAbs=c.natAbs * ((k:ℚ) / D).num.natAbs:=by
    simpa only [Int.natAbs_mul,Int.cast_natCast] using congrArg Int.natAbs hnum
  have hdenAbs:D=c.natAbs * ((k:ℚ) / D).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,Int.cast_natCast] using
      congrArg Int.natAbs hden
  constructor
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).num.natAbs:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hnumAbs.symm
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).den:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hdenAbs.symm

private theorem abs_le_num (q:ℚ):|q|≤ (q.num.natAbs:ℚ):=by
  have hden:(0:ℚ) < q.den:=by exact_mod_cast q.den_pos
  have hden₁:(1:ℚ)≤ q.den:=by exact_mod_cast q.den_pos
  have hnum:(q.num.natAbs:ℚ)=|(q.num:ℚ)|:=by
    rw [Nat.cast_natAbs,Int.cast_abs]
  conv_lhs => rw [← q.num_div_den]
  rw [abs_div,abs_of_nonneg (le_of_lt hden), ← hnum]
  apply (div_le_iff₀ hden).mpr
  simpa using mul_le_mul_of_nonneg_left hden₁ (Nat.cast_nonneg q.num.natAbs)

theorem roundDown_floor_magnitude_bound (q:ℚ) (M D:ℕ) (hq:|q|≤ M):
    (Int.floor (q * D)).natAbs≤ M * D + 1:=by
  let k:=Int.floor (q * D)
  have hab:=abs_le.mp hq
  have hD:(0:ℚ)≤ D:=Nat.cast_nonneg _
  have hupper:=mul_le_mul_of_nonneg_right hab.2 hD
  have hlower:=mul_le_mul_of_nonneg_right hab.1 hD
  have hfloor:(k:ℚ)≤ q * D:=Int.floor_le _
  have hfloor':q * D < (k:ℚ) + 1:=Int.lt_floor_add_one _
  have hk:|(k:ℚ)|≤ (M:ℚ) * D + 1:=by
    apply abs_le.mpr
    constructor <;> linarith
  have hk':(k.natAbs:ℚ)≤ ((M * D + 1:ℕ):ℚ):=by
    simpa only [Nat.cast_natAbs,Int.cast_abs,Nat.cast_add,Nat.cast_mul,
      Nat.cast_one] using hk
  exact Nat.cast_le.mp hk'

theorem roundDown_floor_bound (q:ℚ) (D:ℕ):
    (Int.floor (q * D)).natAbs≤ q.num.natAbs * D + 1:=
  roundDown_floor_magnitude_bound q q.num.natAbs D (abs_le_num q)

theorem roundDown_le (q:ℚ) (D:ℕ) (hD:0 < D):roundDown q D≤ q:=by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q:ℚ) (D:ℕ) (hD:0 < D):
    q < roundDown q D + 1 / D:=by
  have hp:(0:ℚ) < D:=by exact_mod_cast hD
  unfold roundDown
  rw [← add_div,lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem roundDown_error (q:ℚ) (D:ℕ) (hD:0 < D):
    0≤ (q:ℝ) - (roundDown q D:ℝ)∧
      (q:ℝ) - (roundDown q D:ℝ) < 1 / (D:ℝ):=by
  have h₁:(roundDown q D:ℝ)≤ (q:ℝ):=by
    exact_mod_cast roundDown_le q D hD
  have h₂:(q:ℝ) < (roundDown q D:ℝ) + 1 / (D:ℝ):=by
    have h:=(Rat.cast_lt (K:=ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  constructor <;> linarith

theorem sqrtUpper_bounds (q:ℚ) (hq:0≤ q) (D:ℕ) (hD:0 < D):
    Real.sqrt (q:ℝ)≤ (sqrtUpper q D:ℝ)∧
      (sqrtUpper q D:ℝ) < Real.sqrt (q:ℝ) + 2 / (D:ℝ):=by
  let c:=Nat.ceil (q * (D:ℚ) ^ 2)
  let s:=Nat.sqrt c
  have hqR:(0:ℝ)≤ q:=by exact_mod_cast hq
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  have hcl:(q:ℝ) * (D:ℝ) ^ 2≤ c:=by
    have h:q * (D:ℚ) ^ 2≤ (c:ℚ):=Nat.le_ceil _
    have h':=(Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast] using h'
  have hcu:(c:ℝ) < (q:ℝ) * (D:ℝ) ^ 2 + 1:=by
    have h:(c:ℚ) < q * (D:ℚ) ^ 2 + 1:=
      Nat.ceil_lt_add_one (show (0:ℚ)≤ q * (D:ℚ) ^ 2 by positivity)
    have h':=(Rat.cast_lt (K:=ℝ)).mpr h
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl:(s:ℝ) ^ 2≤ c:=by
    have h:s ^ 2≤ c:=Nat.sqrt_le' c
    have h':=(Nat.cast_le (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu:(c:ℝ) < ((s:ℝ) + 1) ^ 2:=by
    have h:c < (s + 1) ^ 2:=Nat.lt_succ_sqrt' c
    have h':=(Nat.cast_lt (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h'
  have hs:(0:ℝ)≤ s:=Nat.cast_nonneg _
  have hroot:=Real.sq_sqrt hqR
  have hrootpos:=Real.sqrt_nonneg (q:ℝ)
  have hsqr:(Real.sqrt (q:ℝ) * (D:ℝ)) ^ 2=(q:ℝ) * (D:ℝ) ^ 2:=by
    rw [mul_pow,hroot]
  have hl:Real.sqrt (q:ℝ) * D≤ (s:ℝ) + 1:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl,hsu,hsqr,ht,hs]
  have hu:(s:ℝ) + 1 < Real.sqrt (q:ℝ) * D + 2:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl,hcu,hsqr,ht,hs,
      sq_nonneg ((s:ℝ) - Real.sqrt (q:ℝ) * D)]
  have heq:(sqrtUpper q D:ℝ)=((s:ℝ) + 1) / D:=by
    simp [sqrtUpper,c,s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q:ℝ) * D + 2) / D:=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _=_:=by field_simp

end Lax109476Proofs.RationalRounding

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

theorem size_pow_le (a k:ℕ):Nat.size (a ^ k)≤ k * Nat.size a + 1:=by
  induction k with
  | zero => simp
  | succ k ih =>
    have h:=size_mul_le (a ^ k) a
    rw [pow_succ,Nat.succ_mul]
    omega

theorem size_add_one_le (a:ℕ):Nat.size (a + 1)≤ Nat.size a + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h:=Nat.lt_size_self a
  have hp:0 < 2 ^ Nat.size a:=by positivity
  omega

theorem size_add_le (a b:ℕ):Nat.size (a + b)≤ Nat.size a + Nat.size b + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ,pow_add]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hpa:0 < 2 ^ Nat.size a:=by positivity
  have hpb:0 < 2 ^ Nat.size b:=by positivity
  have h₁:=Nat.le_mul_of_pos_right (2 ^ Nat.size a) hpb
  have h₂:=Nat.le_mul_of_pos_left (2 ^ Nat.size b) hpa
  omega

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

theorem bitSize_nil:bitSize []=0:=rfl

theorem rational_size_bounds (q:ℚ):
    3≤ bitSize (encodeRational q)∧
      Nat.size q.num.natAbs + Nat.size q.den≤ bitSize (encodeRational q):=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  omega

theorem rational_size_upper (q:ℚ):
    bitSize (encodeRational q)≤ 4 + Nat.size q.num.natAbs + Nat.size q.den:=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

theorem integer_normal_norm {n:ℕ} (a:Fin n→ ℤ) (ha:a ≠ 0):
    1≤ (fun j => (a j:ℝ)) ⬝ᵥ (fun j => (a j:ℝ)):=by
  obtain ⟨j,hj⟩:∃ j,a j ≠ 0:=by
    by_contra! h
    exact ha (funext h)
  have habs:(1:ℝ)≤ |(a j:ℝ)|:=by
    have h:(1:ℕ)≤ (a j).natAbs:=Int.natAbs_pos.mpr hj
    have hh:(1:ℝ)≤ ((a j).natAbs:ℝ):=by exact_mod_cast h
    simpa [Nat.cast_natAbs,Int.cast_abs] using hh
  have hsq:(1:ℝ)≤ (a j:ℝ) * (a j:ℝ):=by nlinarith [sq_abs (a j:ℝ)]
  exact hsq.trans (Finset.single_le_sum (fun k _ => mul_self_nonneg (a k:ℝ))
    (Finset.mem_univ j))

end Lax109476Proofs.RationalSeparation

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

theorem symmetric_form {ι:Type} [Fintype ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (u v:ι→ ℝ):
    u ⬝ᵥ (A *ᵥ v)=v ⬝ᵥ (A *ᵥ u):=by
  have ht:Aᵀ=A:=(Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem quadratic_error_bound {n:ℕ} (E:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (hE:∀ i j, |E i j|≤ ε) (x:Fin n→ ℝ):
    |x ⬝ᵥ (E *ᵥ x)|≤ (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have hcs:(∑ i, |x i|) ^ 2≤ (n:ℝ) * (x ⬝ᵥ x):=by
    have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _:Fin n => (1:ℝ)) (fun i => |x i|)
    simpa [dotProduct,sq_abs,pow_two] using h
  calc
    _=|∑ i, ∑ j,x i * E i j * x j|:=by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _≤ ∑ i, ∑ j, |x i * E i j * x j|:=by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _≤ ∑ i, ∑ j,ε * |x i| * |x j|:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _≤ |x i| * ε * |x j|:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _=_:=by ring
    _=ε * (∑ i, |x i|) ^ 2:=by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤ ε * ((n:ℝ) * (x ⬝ᵥ x)):=mul_le_mul_of_nonneg_left hcs hε
    _=_:=by ring

theorem posDef_of_quadratic_le {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.IsHermitian)
    (hAB:∀ x,x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ (B *ᵥ x)):B.PosDef:=by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos:0 < x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

def realShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ):
    Matrix (Fin n) (Fin n) ℝ:=fun i j => (A i j:ℝ)

theorem enlargement_sandwich {n:ℕ} (A R:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (herr:∀ i j, |R i j - A i j|≤ ε)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)∧
      x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have h:=quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec,dotProduct_sub] at h
  have hh:=abs_le.mp h
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  constructor <;> linarith [hh.1,hh.2]

theorem roundedShape_sandwich {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape A *ᵥ x)≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n:ℝ) / D) * (x ⬝ᵥ x):=by
  let R:Matrix (Fin n) (Fin n) ℝ:=
    fun i j => (RationalRounding.roundDown (A i j) D:ℝ)
  have herr:∀ i j, |R i j - realShape A i j|≤ 1 / (D:ℝ):=by
    intro i j
    have h:=RationalRounding.roundDown_error (A i j) D hD
    dsimp [R,realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid:realShape (roundedShape A D)=R + ((n:ℝ) * (1 / D)) • 1:=by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n:ℚ) / D) * (if i=j then 1 else 0):ℚ):ℝ) =
      (RationalRounding.roundDown (A i j) D:ℝ) +
        ((n:ℝ) * (1 / D)) * (if i=j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

theorem roundedShape_isHermitian {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:A.IsSymm) (D:ℕ):(realShape (roundedShape A D)).IsHermitian:=by
  rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape,roundedShape,hA.apply i j,Matrix.one_apply,eq_comm]

theorem roundedShape_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape A D)).PosDef:=by
  have hsym:A.IsSymm:=by
    apply Matrix.IsSymm.ext
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

theorem roundedShape_relative_bound {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (lowerBound η:ℝ) (hη:0≤ η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ η * lowerBound) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  have hxx:0≤ x ⬝ᵥ x:=by
    simpa using dotProduct_star_self_nonneg x
  have herror:=mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative:=mul_le_mul_of_nonneg_left (hlower x) hη
  have hround:=(roundedShape_sandwich A D hD x).2
  nlinarith only [herror,hrelative,hround]

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

theorem form_cauchy_schwarz {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (a x:ι→ ℝ) (ha:a ≠ 0):
    (x ⬝ᵥ (A *ᵥ a)) ^ 2≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg:0≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid:(q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2):=by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
      dotProduct_sub,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q,t]
    ring
  rw [hid] at hnonneg
  have h:=nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

noncomputable def realCutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ)
    (a:Fin n→ ℝ):Matrix (Fin n) (Fin n) ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) •
    (A - (2 / (((n:ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

theorem realShape_cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    realShape (cutShape n A a)=realCutShape n (realShape A) (fun i => (a i:ℝ)):=by
  ext i j
  simp [realShape,cutShape,realCutShape,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Rat.cast_sum,smul_eq_mul]

theorem realCutShape_sandwich (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x))≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x)≤
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα:0 < α:=by dsimp [α]; apply div_pos <;> nlinarith
  have hβ:0≤ β:=by dsimp [β]; positivity
  have hcs:t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x)):=form_cauchy_schwarz hA a x ha
  have hcs':t ^ 2 / q≤ x ⬝ᵥ (A *ᵥ x):=(div_le_iff₀ hq).mpr (by nlinarith)
  have hterm:0≤ β * (t ^ 2 / q):=by positivity
  have htermUpper:=mul_le_mul_of_nonneg_left hcs' hβ
  have hid:x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)):=by
    simp only [realCutShape,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec,dotProduct_smul,dotProduct_sub,
      smul_eq_mul]
    dsimp [α,β,q,t]
    simp only [dotProduct_comm (A *ᵥ a) x,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hfactor:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h:=mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h:=mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

theorem realCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):(realCutShape n A a).PosDef:=by
  have hsym:(realCutShape n A a).IsHermitian:=by
    rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape,Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec,
      smul_eq_mul,h,mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by positivity
  have hxx:0 < x ⬝ᵥ (A *ᵥ x):=by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

theorem roundedCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape (cutShape n A a) D)).PosDef:=by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

theorem realCutShape_coarse_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    (1 / 4:ℝ) * (x ⬝ᵥ (A *ᵥ x))≤ x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x)≤ 2 * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hxx:0≤ x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp:0 < (n:ℝ) + 1:=by linarith
  have hd:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  have hratio:(1 / 2:ℝ)≤ (n:ℝ) / ((n:ℝ) + 1):=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo:(1 / 4:ℝ)≤ ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    nlinarith
  have hhi:(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)≤ 2:=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h:=realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

theorem dyadic_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (2:ℝ) ^ (l + s + n + 1)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hpow:(0:ℝ) < 2 ^ (l + s + n + 1):=by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add,pow_one]
  have hl:(2:ℝ) ^ l ≠ 0:=by positivity
  have hs:(2:ℝ) ^ s ≠ 0:=by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

theorem cast_direction_form (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ)=realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
  simp [dotProduct,Matrix.mulVec,realShape,realVector,Rat.cast_sum]

theorem realShape_roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):
    realShape (roundedStepShape n A a D η) =
      ((1 + (η:ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D):=by
  ext i j
  simp [realShape,roundedStepShape,Matrix.smul_apply,smul_eq_mul]

theorem roundedStepShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η):(realShape (roundedStepShape n A a D η)).PosDef:=by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  positivity

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

theorem gridDenominator_pos (l s n:ℕ):0 < gridDenominator l s n:=by
  unfold gridDenominator
  positivity

theorem gridDenominator_size (l s n:ℕ):
    Nat.size (gridDenominator l s n)=l + s + n + 4:=by
  unfold gridDenominator
  rw [Nat.size_pow]

theorem grid_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (gridDenominator l s n:ℝ)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hp:(2:ℝ) ^ (l + s + n + 1)≤ (gridDenominator l s n:ℝ):=by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

theorem exactCut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
  have he:((2:ℝ) ^ (l + 2))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _=(1 / 4:ℝ) * (((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)):=by ring
    _≤ (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)):=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

theorem stepAccuracy_pos (n:ℕ):0 < stepAccuracy n:=by
  unfold stepAccuracy
  positivity

theorem stepAccuracy_small (n:ℕ) (hn:2≤ n):
    (stepAccuracy n:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < 8 * (n:ℝ) * ((n:ℝ) + 1):=by positivity
  have h₁:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have h₂:(n:ℝ) + 1≤ (2:ℝ) ^ (n + 1):=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n + 1)).le
  have hprod:=mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he:(2:ℝ) ^ (2 * n + 4)=8 * ((2:ℝ) ^ n * (2:ℝ) ^ (n + 1)):=by
    rw [← pow_add,show 2 * n + 4=(n + (n + 1)) + 3 by omega,pow_add]
    norm_num
    ring
  have hb:8 * (n:ℝ) * ((n:ℝ) + 1)≤ (2:ℝ) ^ (2 * n + 4):=by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

theorem storedShape_relative_bound (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (hD:0 < D) (η:ℚ) (hη:0≤ η)
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + (η:ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
  have hp:(0:ℝ)≤ η:=by exact_mod_cast hη
  have h:=roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  calc
    _≤ (1 + (η:ℝ)) ^ 2 *
        ((1 + (η:ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))):=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_:=by ring

theorem uniform_storedStep_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)) (x:Fin n→ ℝ):
    let P:=realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤ x ⬝ᵥ (P *ᵥ x)∧
      x ⬝ᵥ (P *ᵥ x)≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  let D:=gridDenominator (l + 2) (2 * n + 4) n
  let η:=stepAccuracy n
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hp:(0:ℝ) < η:=by exact_mod_cast stepAccuracy_pos n
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη:(η:ℝ)≤ 1 / 8:=by
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR:=roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg:0≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor:1≤ (1 + (η:ℝ)) ^ 2:=by nlinarith
  have hfactorUpper:(1 + (η:ℝ)) ^ 3≤ 2:=by
    calc
      _≤ (9 / 8:ℝ) ^ 3:=pow_le_pow_left₀ (by positivity) (by linarith) 3
      _≤ _:=by norm_num
  have hprec:2 * (n:ℝ) / D≤ (η:ℝ) * ((2:ℝ) ^ (l + 2))⁻¹:=by
    simpa [η,stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative:=storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse:=realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse':(1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h:=mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h,hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def shapes (n:ℕ) (a:ℕ→ Fin n→ ℚ):ℕ→ Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

def centers (n:ℕ) (a:ℕ→ Fin n→ ℚ) (c₀:Fin n→ ℚ):ℕ→ Fin n→ ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

theorem shapes_invariant (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    (realShape (shapes n a k)).PosDef∧
    ∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)≤ (4:ℝ) ^ k * (x ⬝ᵥ x):=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one,by simp⟩
  | succ k ih =>
      have hne:realVector (a k) ≠ 0:=by
        intro h
        have hh:=ha k
        rw [h,dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs:=uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he:((2:ℝ) ^ (2 * (k + 1)))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ (2 * k))⁻¹:=by
          rw [show 2 * (k + 1)=2 * k + 2 by omega,pow_add]
          norm_num
        constructor
        · rw [he]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0:ℝ)≤ 1 / 4 by norm_num)
          change _≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh,hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)≤ _
          rw [pow_succ]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0:ℝ)≤ 4 by norm_num)
          nlinarith only [hh,hs.2]

theorem sequence_grid_size (n k:ℕ):
    Nat.size (gridDenominator (2 * k + 2) (2 * n + 4) n)=2 * k + 3 * n + 10:=by
  rw [gridDenominator_size]
  omega

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

@[simp] theorem cacheState_eq {n:ℕ}
    (state:Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)):cacheState state=state:=by
  apply Prod.ext
  · funext i j
    simp [cacheState,Vector.get]
    rfl
  · funext i
    simp [cacheState,Vector.get]
    rfl

def normalSchedule {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (k:ℕ):Fin n→ ℚ:=selectedNormal A b (trajectory A b k).2

theorem fallbackNormal_norm (n:ℕ) (hn:0 < n):
    1≤ realVector (fallbackNormal n) ⬝ᵥ realVector (fallbackNormal n):=by
  let a:Fin n→ ℤ:=fun j => if j.val=0 then 1 else 0
  have ha:a ≠ 0:=by
    intro h
    have hz:=congrFun h ⟨0,hn⟩
    simp [a] at hz
  have hc:realVector (fallbackNormal n) =
      (fun j:Fin n => (if j.val=0 then 1 else 0:ℝ)):=by
    funext j
    change ((if j.val=0 then 1 else 0:ℚ):ℝ)=_
    split_ifs <;> norm_num
  rw [hc]
  simpa [a,apply_ite] using integer_normal_norm a ha

theorem selectedNormal_norm {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (hn:0 < n):
    1≤ realVector (selectedNormal A b c) ⬝ᵥ realVector (selectedNormal A b c):=by
  unfold selectedNormal
  split
  · exact fallbackNormal_norm n hn
  · split_ifs with hz
    · exact fallbackNormal_norm n hn
    · change 1≤ (fun j => (A _ j:ℝ)) ⬝ᵥ (fun j => (A _ j:ℝ))
      exact integer_normal_norm _ hz

theorem trajectory_eq_sequences {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (k:ℕ):
    (trajectory A b k).1=shapes n (normalSchedule A b) k∧
      (trajectory A b k).2=centers n (normalSchedule A b) 0 k:=by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [trajectory,nextState,shapes,centers,cacheState_eq]
    have ha:selectedNormal A b (trajectory A b k).2=normalSchedule A b k:=rfl
    rw [ha,ih.1,ih.2]
    exact ⟨rfl,rfl⟩

end Lax109476Proofs.EllipsoidSearch

end

section

namespace Lax808846Proofs.Imp

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

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

theorem _root_.Lax808846Proofs.Imp.BigStep.inp_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) (hr:¬ c.reads):σ'.inp=σ.inp:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads,not_or] at hr
      rw [ih' hr.2,ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr),ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

theorem Run.frame_inp {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hr:¬ c.reads):σ'.inp=σ.inp:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.inp_eq hr

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

theorem Spec.frame (h:Spec B P c Q K):
    Spec B P c (fun σ σ' => Q σ σ'∧
      (∀ y,y∉ c.wvars→ σ'.vars y=σ.vars y)∧
      (∀ a,a∉ c.warrs→ σ'.arrs a=σ.arrs a)∧
      (¬ c.reads→ σ'.inp=σ.inp)∧
      (c.NoWrite→ σ'.out=σ.out)) K:=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr,hq,fun y hy => hr.frame_var y hy,fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc,fun hc => hr.out_eq hc⟩

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

theorem height_neg (q:ℚ) (B:ℕ) (hq:Height q B):Height (-q) B:=by
  simpa only [Height,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

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

theorem height_sub (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q - r) (2 * B * C):=by
  simpa only [sub_eq_add_neg] using height_add q (-r) B C hq (height_neg r C hr)

theorem height_div (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q / r) (B * C):=by
  simpa only [div_eq_mul_inv] using height_mul q r⁻¹ B C hq (height_inv r C hr)

theorem height_pow (q:ℚ) (B k:ℕ) (hq:Height q B):Height (q ^ k) (B ^ k):=by
  induction k with
  | zero => simp [Height]
  | succ k ih => simpa only [pow_succ] using height_mul (q ^ k) q (B ^ k) B ih hq

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidArithmeticBounds

open RationalArithmeticBounds RationalRounding Matrix
open EllipsoidBounds EllipsoidCenter

theorem height_roundDown (q:ℚ) (B D:ℕ) (hq:Height q B) (hD:0 < D):
    Height (roundDown q D) (B * D + 1):=by
  have hb:1≤ B:=q.den_pos.trans_le hq.2
  have hg:=grid_num_den_bound (Int.floor (q * D)) D hD
  have hn:=roundDown_floor_bound q D
  exact ⟨hg.1.trans (hn.trans (Nat.add_le_add_right (Nat.mul_le_mul_right D hq.1) 1)),
    hg.2.trans (by nlinarith)⟩

theorem height_sqrtUpper (q:ℚ) (B D:ℕ) (hq:Height q B) (hD:0 < D):
    Height (sqrtUpper q D) (B * D ^ 2 + 1):=by
  have hb:1≤ B:=q.den_pos.trans_le hq.2
  have hqB:q≤ (B:ℚ):=by
    have hden:(0:ℚ) < q.den:=by positivity
    have hden1:(1:ℚ)≤ q.den:=by exact_mod_cast q.den_pos
    have hn:(q.num:ℚ)≤ B:=by
      have hnabs:q.num≤ (q.num.natAbs:ℤ):=Int.le_natAbs
      have hc':(q.num:ℚ)≤ ((q.num.natAbs:ℤ):ℚ):=Int.cast_le.mpr hnabs
      have hc:(q.num:ℚ)≤ (q.num.natAbs:ℚ):=by simpa only [Int.cast_natCast] using hc'
      exact hc.trans (by exact_mod_cast hq.1)
    rw [← q.num_div_den]
    apply (div_le_iff₀ hden).mpr
    exact hn.trans (by nlinarith)
  have hc:Nat.ceil (q * (D:ℚ) ^ 2)≤ B * D ^ 2:=by
    apply Nat.ceil_le.mpr
    exact_mod_cast mul_le_mul_of_nonneg_right hqB (sq_nonneg (D:ℚ))
  have hs:Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2))≤ B * D ^ 2:=
    (Nat.sqrt_le_self _).trans hc
  have hg:=grid_num_den_bound
    ((Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2)) + 1:ℕ):ℤ) D hD
  simp only [Int.cast_natCast,Int.natAbs_natCast] at hg
  exact ⟨hg.1.trans (Nat.add_le_add_right hs 1),hg.2.trans (by nlinarith)⟩

end Lax109476Proofs.EllipsoidArithmeticBounds

end

section

namespace Lax109476Proofs.RamCenterCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

theorem centerCap_bounds (M:ℕ) (hM:1≤ M):
    M≤ centerCap M∧ M ^ 2≤ centerCap M∧ 2 * M ^ 3≤ centerCap M∧
      2 * M ^ 4 + 1≤ centerCap M:=by
  have hbase:1≤ M + 1:=by omega
  have h₂:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans
    (Nat.pow_le_pow_right hbase (by omega:2≤ 4))
  have h₃:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 3).trans
    (Nat.pow_le_pow_right hbase (by omega:3≤ 4))
  have h₄:=Nat.pow_le_pow_left (by omega:M≤ M + 1) 4
  have hm:=le_self_pow hM (by decide:(2:ℕ) ≠ 0)
  unfold centerCap
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end Lax109476Proofs.RamCenterCoordinate

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram Lax808846Proofs.Machine

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

theorem Fill.arr (h:Fill a x n i g F σ):σ.arrs a=arrOf n g:=h.1

theorem Fill.counter (h:Fill a x n i g F σ):σ.vars x=i:=h.2.1

theorem Fill.le (h:Fill a x n i g F σ):i≤ n:=h.2.2.1

theorem Fill.cell (h:Fill a x n i g F σ) (hj:j < i):g j=F j:=h.2.2.2 j hj

theorem Fill.length (h:Fill a x n i g F σ):(σ.arrs a).length=n:=by
  rw [h.arr,length_arrOf]

@[simp] theorem Fill.setVar_iff (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env)
    (y:String) (v:ℕ) (hy:y ≠ x):
    Fill a x n i g F (σ.setVar y v)↔ Fill a x n i g F σ:=by
  simp [Fill,Ne.symm hy]

theorem Fill.setVar (h:Fill a x n i g F σ) (hy:y ≠ x) (v:ℕ):
    Fill a x n i g F (σ.setVar y v):=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

theorem Fill.setCell (h:Fill a x n i g F σ) (v:ℕ):
    Fill a x n i (upd g i v) F (σ.setArr a i v):=
  ⟨by rw [arrs_setArr,if_pos rfl,h.arr,set_arrOf_eq_upd],by rw [vars_setArr,h.counter],
   h.2.2.1,fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

theorem Fill.bump (h:Fill a x n i g F σ) (hin:i < n) (hgi:g i=F i):
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)):=
  ⟨by rw [arrs_setVar,h.arr],by simp,hin,fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

namespace Fill

def Below (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ:Env):Prop:=
  ∃ g,Fill a x n (σ.vars x) g F σ

theorem Below.le (h:Below a x n F σ):σ.vars x≤ n:=by
  obtain ⟨_,hf⟩:=h; exact hf.le

theorem below_zero (h:σ.arrs a=arrOf n g) (hx:σ.vars x=0):Below a x n F σ:=
  ⟨g,h,rfl,by omega,fun j hj => absurd hj (by omega)⟩

theorem Below.done (h:Below a x n F σ) (hx:σ.vars x=n):
    ∃ g,σ.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j:=by
  obtain ⟨g,hf⟩:=h
  exact ⟨g,hf.arr,fun j hj => hf.cell (by omega)⟩

theorem Below.step (h:Below a x n F σ) (hlt:σ.vars x < n) (hv:v=F (σ.vars x)):
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)):=by
  obtain ⟨g,hf⟩:=h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x=σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

@[simp] theorem wvars_put (a x:String) (e:Expr):(put a x e).wvars=[x]:=by
  simp [put,Com.wvars]

abbrev PutPost (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ σ':Env):Prop:=
  Below a x n F σ'∧ σ'.vars x=σ.vars x + 1

theorem put_spec (B n:ℕ) (a x:String) (e:Expr) (F:ℕ→ ℕ) (P:Env→ Prop)
    (hP:∀ σ,P σ→ Below a x n F σ∧ σ.vars x < n) (hnB:n < B)
    (he:∀ σ,P σ→ e.evalB B σ=some (F (σ.vars x))):
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size):=by
  intro σ hσ
  obtain ⟨hb,hlt⟩:=hP σ hσ
  obtain ⟨g,hf⟩:=hb
  refine ⟨_, (Run.seq (Run.store (idx:=σ.vars x) (v:=F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v:=σ.vars x + 1) ?_)).mono (by simp; omega), ?_,by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g,hf⟩ hlt rfl

theorem loop_spec (B n:ℕ) (a x m:String) (e:Expr) (F:ℕ→ ℕ)
    (hxm:x ≠ m) (hnB:n < B)
    (he:∀ σ,Below a x n F σ→ σ.vars m=n→ σ.vars x < n→
      e.evalB B σ=some (F (σ.vars x))):
    Spec B (fun σ => (∃ g,σ.arrs a=arrOf n g)∧ σ.vars m=n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g,σ'.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j)∧ σ'.vars x=n)
      ((10 + e.size) * n + 6):=by
  have hbody:Spec B (fun σ => (Below a x n F σ∧ σ.vars m=n)∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ'∧ σ'.vars m=n)∧ σ'.vars x=σ.vars x + 1)
      (6 + e.size):=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1,hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1,by rw [hq.2.1 m (by simp [Ne.symm hxm]),hσ.1.2]⟩,hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ∧ σ.vars m=n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g,harr⟩,hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp),by simp [Ne.symm hxm,hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2,hq.2⟩

namespace Demo

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem exists_arrOf (xs:List ℕ) (n:ℕ) (h:xs.length=n):∃ g,xs=arrOf n g:=by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf,List.getD_eq_getElem?_getD,hi]

theorem fillConstant_spec (B n v:ℕ) (a:String) (hnB:n < B) (hvB:v < B):
    Spec B (fun σ => (σ.arrs a).length=n∧ σ.vars "vec.n"=n) (fillConstant a v)
      (fun σ τ => τ.arrs a=List.replicate n v∧ τ.vars "vec.n"=n∧
        ∀ b ≠ a,τ.arrs b=σ.arrs b) (11 * n + 6):=by
  have hfill:=Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ,hr, ⟨g,hτg,hg⟩,_⟩:=hfill σ ⟨exists_arrOf _ _ hσ.1,hσ.2⟩
  refine ⟨τ,hr, ?_, ?_, ?_⟩
  · rw [hτg,replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put,Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put,Com.warrs,hb])

theorem zeroRationalArray_spec (B n:ℕ) (a:String) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ∧ τ.vars "vec.n"=n∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      (33 * n + 18):=by
  have h0:0 < B:=by omega
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  rintro σ ⟨hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτs,hτN,hτa⟩:=fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs,hσN⟩
  have hτn:(τ.arrs (a ++ ".n")).length=n:=by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ,hr₂,hυn,hυN,hυa⟩:=fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn,hτN⟩
  have hυd:(υ.arrs (a ++ ".d")).length=n:=by
    rw [hυa _ hnd.symm,hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ,hr₃,hρd,hρN,hρa⟩:=fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd,hυN⟩
  have hρs:ρ.arrs (a ++ ".s")=List.replicate n 0:=by rw [hρa _ hsd,hυa _ hsn,hτs]
  have hρn:ρ.arrs (a ++ ".n")=List.replicate n 0:=by rw [hρa _ hnd,hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_,hρN, ?_⟩
  · simp [Represents,hρs,hρn,hρd,rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def centerValues {n:ℕ} (u c:Fin n→ ℚ) (gamma:ℚ) (D:ℕ):Fin n→ ℚ:=
  fun j => RationalRounding.roundDown (c j - u j * gamma) D

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n:ℕ} (v:Fin n→ ℚ):filled v 0=List.replicate n 0:=by simp [filled]

theorem filled_done {n:ℕ} (v:Fin n→ ℚ):filled v n=List.ofFn v:=by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

theorem filled_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    (filled v i.val).set i.val (v i)=filled v (i.val + 1):=by
  apply List.ext_getElem
  · simp [filled]
  · intro k hk hk'
    have hkn:k < n:=by simpa [filled] using hk'
    rw [List.getElem_set]
    by_cases hki:i.val=k
    · have hfin:i=(⟨k,hkn⟩:Fin n):=Fin.ext hki
      simp [filled,hfin]
    · have hnext:k < i.val + 1↔ k < i.val:=by omega
      simp only [hki, ↓reduceIte,filled,List.getElem_ofFn]
      change (if k < i.val then v ⟨k,hkn⟩ else 0)=(if k < i.val + 1 then v ⟨k,hkn⟩ else 0)
      simp only [hnext]

theorem centerValues_eq_roundedCenter {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    centerValues (A *ᵥ a) c (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) D =
      EllipsoidCenter.roundedCenter n A a c D:=by
  funext i
  simp only [centerValues,EllipsoidCenter.roundedCenter,EllipsoidCenter.approximateCenter,
    Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  rw [mul_comm]

end Lax109476Proofs.RamCenterUpdate

end

section

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem disjoint_not_mem (a b s:String) (hab:Disjoint a b) (hs:s∈ suffixes):
    a ++ s∉ [b ++ ".s",b ++ ".n",b ++ ".d"]:=by
  intro h
  simp at h
  rcases h with h | h | h
  · exact hab s hs ".s" (by simp [suffixes]) h
  · exact hab s hs ".n" (by simp [suffixes]) h
  · exact hab s hs ".d" (by simp [suffixes]) h

def loopFields:List String:= ["copy.i", "vec.i", "vec.n"]

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "left.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "left.s")); let c7:Nat:=c5 (Expr.size (Expr.var "left.n")); let c8:Nat:=c5 (Expr.size (Expr.var "left.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B leftToResult σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c3 (@And.intro (Run B leftToResult σ c3 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c3) (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4081_0_0_0))) (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2 (RunStep.eval_var B c1 "left.d" (?nAX_g4081_0_0_1))))) (?nAX_g4081_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

set_option maxHeartbeats 0 in
theorem copyCoordinate_spec (B M i:ℕ) (a b:String) (xs ys:List ℚ)
    (hi:i < xs.length) (hiy:i < ys.length) (hiB:i < B) (h1:1 < B)
    (hMB:M < B) (hq:Height xs[i] M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧ σ.vars "copy.i"=i)
      (copyCoordinate a b)
      (fun _ τ => Represents b (ys.set i xs[i]) τ∧ Represents a xs τ) 30:=by
  have hload:=spec_with_fields loopFields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])
  have hresult:=spec_with_fields loopFields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [leftToResult,Com.wvars])
    (by simp [leftToResult,Com.warrs])
  have hstore:=spec_with_write_frame loopFields
    (storeReduced_spec B b ys xs[i] i hiy h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl <;> simp [storeReduced,Com.wvars])
  rintro σ ⟨hσa,hσb,hσi⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (loadLeft a) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c1:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi; let c2:Env→ Prop:=LeftOutput c1; let c3:Env→ Prop:=FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c4:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((9:Nat))) (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4))); let c6:Env→ Prop:=Represents b (@List.set Rat ys i c1); let c7:Env→ Prop:=(fun (x τ:Env) => And (c6 τ) (Represents a xs τ)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B (copyCoordinate a b) σ σ' ((30:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Env→ Prop:=FractionOutput c1; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat:=c11 ((1:Nat)) (Expr.size (Expr.var "copy.i")); let c13:Nat:=c11 ((6:Nat)) ((13:Nat)); let c14:Nat:=c11 ((9:Nat)) c13; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents a xs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadLeft a) (fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) ?_) fun (w:Env) (h:And (c0 w ((9:Nat))) (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)))) => let c0_1:Prop:=c0 w ((9:Nat)); let c1_1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B leftToResult w σ' ((6:Nat))) (And (c10 σ') (And (FieldsAgree loopFields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c9) (RunStep.use B c2 leftToResult (fun (σ_1 τ:Env) => And (c10 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hresult w ?_) fun (w_1:Env) (h_1:And (Run B leftToResult w w_1 ((6:Nat))) (And (c10 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B leftToResult w w_1 ((6:Nat)); let c1_2:Prop:=And (c10 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced b) w_1 σ' ((13:Nat))) (And (c6 σ') (And (FieldsAgree loopFields w_1 σ') (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs σ' a_1) (Env.arrs w_1 a_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c9) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents b ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (c10 σ_1))) (storeReduced b) (fun (σ_1 τ:Env) => And (c6 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs τ a_1) (Env.arrs σ_1 a_1)))) ((13:Nat)) hstore w_1 ?_) fun (w_2:Env) (h_2:And (Run B (storeReduced b) w_1 w_2 ((13:Nat))) (And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))))) => let c0_3:Prop:=Run B (storeReduced b) w_1 w_2 ((13:Nat)); let c1_3:Prop:=And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c9) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.intro Env c8 w_2 (@And.intro (Run B (copyCoordinate a b) σ w_2 ((30:Nat))) (c7 w_2) (RunStep.mono B (copyCoordinate a b) σ w_2 (c11 c12 c14) ((30:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "copy.i")) (Com.seq (loadLeft a) (Com.seq leftToResult (storeReduced b))) σ (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w_2 c12 c14 (RunStep.assign B σ "vec.i" (Expr.var "copy.i") (Env.vars σ "copy.i") (RunStep.eval_var B σ "copy.i" (?nAX_g4083_0_0_0))) (RunStep.seq B (loadLeft a) (Com.seq leftToResult (storeReduced b)) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w w_2 ((9:Nat)) c13 left (RunStep.seq B leftToResult (storeReduced b) w w_1 w_2 ((6:Nat)) ((13:Nat)) left_1 left_2))) (?nAX_g4083_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4083_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4083_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals clear hload hresult hstore
  all_goals simp_all [Disjoint,suffixes,LeftOutput,FractionOutput,Represents,FieldsAgree,loopFields,
    storeReduced,Com.warrs]
  all_goals aesop

def CopyInvariant {n:ℕ} (a b:String) (v:Fin n→ ℚ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧
    Represents b (RamCenterUpdate.filled v (σ.vars "copy.i")) σ∧
    σ.vars "copy.i" ≤ n∧ σ.vars "vec.n"=n

theorem copyStep_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => CopyInvariant a b v σ∧ σ.vars "copy.i" < n) (copyStep a b)
      (fun σ τ => CopyInvariant a b v τ∧ τ.vars "copy.i"=σ.vars "copy.i" + 1) 34:=by
  rintro σ ⟨⟨hσa,hσb,hσiN,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "copy.i",hσi⟩
  have hvi:Height (List.ofFn v)[i.val] M:=by simpa using hv i
  obtain ⟨τ,hr₁,hτb,hτa⟩:=copyCoordinate_spec B M i.val a b (List.ofFn v)
    (RamCenterUpdate.filled v i.val) (by simp) (by simp [RamCenterUpdate.filled])
    (i.isLt.trans hnB) h1 hMB hvi hab σ ⟨hσa,hσb,rfl⟩
  have hτi:τ.vars "copy.i"=i.val:=hr₁.frame_var _ (by
    simp [copyCoordinate,leftToResult,loadLeft,storeReduced,Com.wvars])
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var "vec.n" (by
    simp [copyCoordinate,leftToResult,loadLeft,storeReduced,Com.wvars])).trans hσn
  have hτiB:τ.vars "copy.i" < B:=hτi ▸ i.isLt.trans hnB
  have hsumB:Bop.add.apply (τ.vars "copy.i") 1 < B:=by
    simpa [Bop.apply,hτi] using lt_of_le_of_lt i.isLt hnB
  have hr₂:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) τ
      (τ.setVar "copy.i" (i.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτi] using
      (evalB_bin (evalB_var hτiB) (evalB_lit h1) hsumB))
  have hnext:Represents b (RamCenterUpdate.filled v (i.val + 1)) τ:=by
    rw [← RamCenterUpdate.filled_step]
    simpa only [List.getElem_ofFn,Fin.eta] using hτb
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτa
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change i.val + 1≤ n
    exact i.isLt
  · simpa using hτn
  · simp [i]

theorem copyLoop_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ Represents b (List.replicate n 0) σ∧ σ.vars "vec.n"=n)
      (copyLoop a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n)
      (38 * n + 6):=by
  have hlo:=Spec.forRangeZero "copy.i" "vec.n" (CopyInvariant a b v) n 34 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2) (copyStep_spec B n M a b v h1 hnB hMB hv hab)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσa,hσb,hσn⟩
    simp_all [CopyInvariant,Represents,RamCenterUpdate.filled_zero]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    refine ⟨?_,hτ.1,hτ.2.2.2⟩
    simpa only [hcounter,RamCenterUpdate.filled_done] using hτ.2.1

theorem copyRationalArray_spec (B n M:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hMB:M < B) (hv:∀ i,Height (v i) M) (hab:Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ (σ.arrs (b ++ ".s")).length=n∧
        (σ.arrs (b ++ ".n")).length=n∧ (σ.arrs (b ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (copyRationalArray a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n)
      (71 * n + 24):=by
  rintro σ ⟨hσa,hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτb,hτN,hτarr⟩:=RamZeroArray.zeroRationalArray_spec B n b hnB h1 σ ⟨hσs,hσn,hσd,hσN⟩
  have hτa:Represents a (List.ofFn v) τ:=by
    simpa only [Represents,hτarr (a ++ ".s") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".n") (disjoint_not_mem a b _ hab (by simp [suffixes])),
      hτarr (a ++ ".d") (disjoint_not_mem a b _ hab (by simp [suffixes]))] using hσa
  obtain ⟨υ,hr₂,hυ⟩:=copyLoop_spec B n M a b v h1 hnB hMB hv hab τ ⟨hτa,hτb,hτN⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυ⟩

end Lax109476Proofs.RamCopy

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

namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds

theorem shapeCap_pow (M k:ℕ) (hk:k≤ 8):M ^ k≤ (M + 1) ^ 8:=
  (Nat.pow_le_pow_left (by omega:M≤ M + 1) k).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) hk)

theorem shapeCap_bounds (M:ℕ):
    M≤ shapeCap M∧ M ^ 2≤ shapeCap M∧ M ^ 3≤ shapeCap M∧
      2 * M ^ 4≤ shapeCap M∧ 2 * M ^ 5≤ shapeCap M∧
      2 * M ^ 6 + 1≤ shapeCap M∧ 6 * M ^ 7≤ shapeCap M∧ 6 * M ^ 8≤ shapeCap M:=by
  have hp1:=shapeCap_pow M 1 (by omega)
  have hp2:=shapeCap_pow M 2 (by omega)
  have hp3:=shapeCap_pow M 3 (by omega)
  have hp4:=shapeCap_pow M 4 (by omega)
  have hp5:=shapeCap_pow M 5 (by omega)
  have hp6:=shapeCap_pow M 6 (by omega)
  have hp7:=shapeCap_pow M 7 (by omega)
  have hp8:=shapeCap_pow M 8 (by omega)
  have hbase:1≤ (M + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  simp only [pow_one] at hp1
  unfold shapeCap
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,
    by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

end Lax109476Proofs.RamShapeCoordinate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamShapeUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamShapeCoordinate RamZeroArray RamMatrixStorage

def shapeValues {n:ℕ} (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (D:ℕ):Matrix (Fin n) (Fin n) ℚ:=
  fun i j => gs[3] * (RationalRounding.roundDown
    (gs[0] * (A i j - gs[1] * (u i * u j))) D + if i=j then gs[4] else 0)

theorem shapeCap_size (M:ℕ):(shapeCap M).size≤ 8 * M.size + 13:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 8
  have hm:=RationalSizeBounds.size_mul_le 8 ((M + 1) ^ 8)
  have h8:Nat.size 8=4:=by decide
  unfold shapeCap
  omega

theorem shapeValues_eq_roundedStepShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (gs:List ℚ) (hg:4 < gs.length) (D:ℕ) (η:ℚ)
    (hα:gs[0]=(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1))
    (hβ:gs[1]=2 / (((n:ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))))
    (hρ:gs[3]=(1 + η) ^ 2) (hδ:gs[4]=(n:ℚ) / D):
    shapeValues (A *ᵥ a) A gs hg D=EllipsoidCenter.roundedStepShape n A a D η:=by
  ext i j
  simp only [shapeValues,hα,hβ,hρ,hδ,EllipsoidCenter.roundedStepShape,
    EllipsoidRounding.roundedShape,EllipsoidBounds.cutShape,Matrix.smul_apply,Matrix.add_apply,
    Matrix.sub_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  by_cases hij:i=j <;> simp [Matrix.one_apply,hij]

end Lax109476Proofs.RamShapeUpdate

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

theorem mulVec_height (n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H) (i:Fin n):
    Height ((A *ᵥ c) i) (cap n H):=by
  change Height (∑ j,A i j * c j) (cap n H)
  rw [← prefix_ofFn]
  apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hA i j
  · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hc j

end Lax109476Proofs.RamMatrixVector

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamMatrixVector
open RationalArithmeticBounds

theorem formHeight_ge (n H:ℕ) (hH:1≤ H):cap n H≤ formHeight n H:=by
  have hcap:=(cap_ge n H hH).2
  exact (cap_ge n (cap n H) (hH.trans hcap)).2

end Lax109476Proofs.RamEllipsoidForm

end

section

namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds

theorem coefficients_height (n M D E:ℕ) (q:ℚ) (hq:Height q M)
    (hnM:n≤ M) (hDM:D≤ M) (hEM:E≤ M) (hDpos:0 < D):
    ∀ v∈ coefficients n q D E,Height v (coefficientCap M):=by
  have hM:1≤ M:=le_trans q.den_pos hq.2
  have hn:=height_nat n M hnM hM
  have hD:=height_nat D M hDM hM
  have hE:=height_nat E M hEM hM
  have hone:Height (1:ℚ) 1:=by simp [Height]
  have htwo:Height (2:ℚ) 2:=by simp [Height]
  have hnp:Height ((n:ℚ) + 1) (M + 1):=by
    simpa only [Nat.cast_add,Nat.cast_one] using height_nat (n + 1) (M + 1) (by omega) (by omega)
  have hpow:=height_pow _ M 2 hn
  have hsub:=height_sub _ _ (M ^ 2) 1 hpow hone
  have hα:=height_div _ _ (M ^ 2) (2 * M ^ 2 * 1) hpow hsub
  have hβ:=height_div _ _ 2 ((M + 1) * M) htwo (height_mul _ _ (M + 1) M hnp hq)
  have hroot:Height (RationalRounding.sqrtUpper q D) (M ^ 3 + 1):=by
    apply height_mono _ (EllipsoidArithmeticBounds.height_sqrtUpper q M D hq hDpos)
    calc
      M * D ^ 2 + 1≤ M * M ^ 2 + 1:=Nat.add_le_add_right
        (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hDM 2)) 1
      _=M ^ 3 + 1:=by ring
  have hγ:=height_div _ _ 1 ((M + 1) * (M ^ 3 + 1)) hone
    (height_mul _ _ (M + 1) (M ^ 3 + 1) hnp hroot)
  have hρ:=height_pow _ (2 * M) 2
    (by simpa using height_add _ _ 1 M hone (by simpa only [one_mul] using height_div _ _ 1 M hone hE))
  have hδ:=height_div _ _ M M hn hD
  have hp1:=Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(1:ℕ)≤ 4)
  have hp2:=Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(2:ℕ)≤ 4)
  have hp4:=Nat.pow_le_pow_left (by omega:M≤ M + 1) 4
  have hrootpow:M ^ 3 + 1≤ (M + 1) ^ 3:=by nlinarith only [hM]
  have hγbound:1 * ((M + 1) * (M ^ 3 + 1))≤ coefficientCap M:=by
    calc
      1 * ((M + 1) * (M ^ 3 + 1))≤ (M + 1) * (M + 1) ^ 3:=by
        simpa using Nat.mul_le_mul_left (M + 1) hrootpow
      _=(M + 1) ^ 4:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  intro v hv
  simp only [coefficients,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · apply height_mono _ hα
    calc
      M ^ 2 * (2 * M ^ 2 * 1)=2 * M ^ 4:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · apply height_mono _ hβ
    calc
      2 * ((M + 1) * M)≤ 2 * (M + 1) ^ 2:=by nlinarith only [hM]
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · exact height_mono _ hγ hγbound
  · apply height_mono _ hρ
    have hp:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans hp2
    calc
      (2 * M) ^ 2=4 * M ^ 2:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega
  · apply height_mono _ hδ
    have hp:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 2).trans hp2
    calc
      M * M=M ^ 2:=by ring
      _≤ coefficientCap M:=by unfold coefficientCap; omega

end Lax109476Proofs.RamEllipsoidCoefficients

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamMatrixStorage

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (a:String) (qs:List ℚ) (hσ:Represents a qs σ)
    (hs:a ++ ".s" ∉ c.warrs) (hn:a ++ ".n" ∉ c.warrs) (hd:a ++ ".d" ∉ c.warrs):
    Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") hs,
    hr.frame_arr (a ++ ".n") hn,hr.frame_arr (a ++ ".d") hd] using hσ

theorem roundedUpdate_eq_ellipsoid {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D E:ℕ):
    centerValues (A *ᵥ a) c ((coefficients n (a ⬝ᵥ (A *ᵥ a)) D E)[2]'(by simp [coefficients])) D =
        EllipsoidCenter.roundedCenter n A a c D∧
      shapeValues (A *ᵥ a) A (coefficients n (a ⬝ᵥ (A *ᵥ a)) D E) (by simp [coefficients]) D =
        EllipsoidCenter.roundedStepShape n A a D (1 / (E:ℚ)):=by
  constructor
  · simpa [coefficients] using centerValues_eq_roundedCenter A a c D
  · exact shapeValues_eq_roundedStepShape A a _ (by simp [coefficients]) D (1 / (E:ℚ))
      (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients]) (by simp [coefficients])

end Lax109476Proofs.RamEllipsoidUpdate

end

section

namespace Lax109476Proofs.RamEllipsoidWordBounds

open RamEllipsoidCoefficients RamShapeCoordinate RamCenterCoordinate

theorem coefficientCap_bounds (M:ℕ):
    M≤ coefficientCap M∧ M ^ 3 + 2≤ coefficientCap M∧ 4 * (M + 1)≤ coefficientCap M:=by
  have hp1:M + 1≤ (M + 1) ^ 4:=
    le_self_pow (by omega) (by decide:(4:ℕ) ≠ 0)
  have hp3:=(Nat.pow_le_pow_left (by omega:M≤ M + 1) 3).trans
    (Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(3:ℕ)≤ 4))
  have hone:1≤ (M + 1) ^ 4:=Nat.one_le_pow _ _ (by omega)
  unfold coefficientCap
  omega

theorem shapeCap_linear (N:ℕ):8 * (N + 1)≤ shapeCap N:=by
  exact Nat.mul_le_mul_left 8 (le_self_pow (by omega) (by decide:(8:ℕ) ≠ 0))

theorem centerCap_le_shapeCap (N:ℕ):centerCap N≤ shapeCap N:=by
  have hp:=Nat.pow_le_pow_right (by omega:1≤ N + 1) (by decide:(4:ℕ)≤ 8)
  have hone:1≤ (N + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
  unfold centerCap shapeCap
  omega

theorem rootBound_le_shapeBound (M:ℕ):
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ 2 * (shapeCap (coefficientCap M)) ^ 2 + 3:=by
  let N:=coefficientCap M
  let S:=shapeCap N
  have hM3:M ^ 3 + 2≤ N:=(coefficientCap_bounds M).2.1
  have hS:8 * (N + 1)≤ S:=shapeCap_linear N
  have hbase:2 * (M ^ 3 + 2) + 1≤ 2 * N + 1:=by omega
  have hsq:=Nat.pow_le_pow_left hbase 2
  calc
    (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3≤ (2 * N + 1) ^ 2 + N + 1:=by omega
    _≤ 2 * S ^ 2 + 3:=by nlinarith only [hS]

theorem dimensions_le_coefficientCap (n M:ℕ) (hn:2≤ n) (hnM:n * n≤ M):
    n + n + n * n + 1≤ coefficientCap M:=by
  have hnp:n≤ n * n:=by
    simpa only [pow_two] using le_self_pow (by omega:1≤ n) (by decide:(2:ℕ) ≠ 0)
  have hc:=(coefficientCap_bounds M).2.2
  omega

theorem unified_word_bounds (B M n:ℕ) (hn:2≤ n) (hnM:n * n≤ M)
    (hB:2 * (shapeCap (coefficientCap M)) ^ 2 + 3 < B):
    coefficientCap M < B∧ M < B∧ n ^ 2 < B∧ n < B∧ 5 < B∧
      n + n + n * n + 1 < B∧ 2 * M ^ 2 + 3 < B∧
      (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B∧
      2 * (centerCap (coefficientCap M)) ^ 2 + 3 < B:=by
  have hN:=(coefficientCap_bounds M).1
  have hNS:=(shapeCap_bounds (coefficientCap M)).1
  have hSB:shapeCap (coefficientCap M) < B:=by nlinarith only [hB]
  have hNB:=hNS.trans_lt hSB
  have hMB:=hN.trans_lt hNB
  have hnB:n < B:=lt_of_le_of_lt (by nlinarith only [hn,hnM]) hMB
  have h5B:5 < B:=by
    have hlin:=shapeCap_linear (coefficientCap M)
    omega
  have hdimB:=(dimensions_le_coefficientCap n M hn hnM).trans_lt hNB
  have hMS:=hN.trans hNS
  have hpow:=Nat.pow_le_pow_left hMS 2
  have hprim:2 * M ^ 2 + 3 < B:=lt_of_le_of_lt (by omega) hB
  have hroot:=(rootBound_le_shapeBound M).trans_lt hB
  have hcenter:=Nat.pow_le_pow_left (centerCap_le_shapeCap (coefficientCap M)) 2
  refine ⟨hNB,hMB, ?_,hnB,h5B,hdimB,hprim,hroot, ?_⟩
  · simpa only [pow_two] using hnM.trans_lt hMB
  · exact lt_of_le_of_lt (by omega) hB

end Lax109476Proofs.RamEllipsoidWordBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds
open RamEllipsoidUpdate RamEllipsoidWordBounds RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage

theorem extents_frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (a:String) (n:ℕ) (hσ:Extents a n σ)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Extents a n τ:=by
  intro s hs
  rw [hr.frame_arr _ (ha s hs)]
  exact hσ s hs

theorem form_height (n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ i j,Height (A i j) H) (ha:∀ i,Height (a i) H):
    Height (a ⬝ᵥ (A *ᵥ a)) (formHeight n H):=by
  have hcap:=(cap_ge n H hH).2
  have hna:(List.ofFn a).length=n:=by simp
  have hnu:(List.ofFn (A *ᵥ a)).length=n:=by simp
  have han:∀ q∈ List.ofFn a,Height q (cap n H):=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i,rfl⟩:=hq
    exact height_mono _ (ha i) hcap
  have hun:∀ q∈ List.ofFn (A *ᵥ a),Height q (cap n H):=by
    intro q hq
    simp only [List.mem_ofFn] at hq
    obtain ⟨i,rfl⟩:=hq
    exact mulVec_height n H A a hH hA ha i
  change Height (∑ j,a j * (A *ᵥ a) j) (formHeight n H)
  rw [← prefix_ofFn]
  exact prefix_height _ _ n (cap n H) n (hH.trans hcap) hna hnu le_rfl han hun

theorem coefficientCap_size (M:ℕ):(coefficientCap M).size≤ 4 * M.size + 8:=by
  have hb:=RationalSizeBounds.size_add_one_le M
  have hp:=RationalSizeBounds.size_pow_le (M + 1) 4
  have hm:=RationalSizeBounds.size_mul_le 4 ((M + 1) ^ 4)
  have hfour:Nat.size 4=3:=by decide
  unfold coefficientCap
  omega

theorem form_pos_of_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ) (a:Fin n→ ℚ)
    (hA:(EllipsoidRounding.realShape A).PosDef) (ha:a ≠ 0):0 < a ⬝ᵥ (A *ᵥ a):=by
  have hreal:Lax109476.RationalCertificates.realVector a ≠ 0:=by
    intro h
    apply ha
    funext i
    have hi:=congrFun h i
    change (a i:ℝ)=0 at hi
    exact_mod_cast hi
  have hpos:=hA.dotProduct_mulVec_pos hreal
  have hpos':0 < Lax109476.RationalCertificates.realVector a ⬝ᵥ
      (EllipsoidRounding.realShape A *ᵥ Lax109476.RationalCertificates.realVector a):=by simpa using hpos
  rw [← EllipsoidCenter.cast_direction_form n A a] at hpos'
  exact_mod_cast hpos'

end Lax109476Proofs.RamEllipsoidStep

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCommitState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RationalArithmeticBounds RamCopy RamMatrixStorage RamEllipsoidStep

theorem commitShape_spec (B n M:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (h1:1 < B) (hnB:n < B) (hnnB:n * n < B) (hMB:M < B)
    (hA:∀ i j,Height (A i j) M):
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ∧
        (σ.arrs "ell.shape.s").length=n * n∧ (σ.arrs "ell.shape.n").length=n * n∧
        (σ.arrs "ell.shape.d").length=n * n∧ σ.vars "vec.n"=n)
      commitShape
      (fun _ τ => Represents "ell.shape" (flatten A) τ∧ Represents "ell.nextshape" (flatten A) τ∧
        τ.vars "vec.n"=n)
      (71 * (n * n) + 32):=by
  have hv:∀ k:Fin (n * n),Height (A k.divNat k.modNat) M:=fun k => hA k.divNat k.modNat
  have hcopy:=spec_with_write_frame ["state.savedn"]
    (copyRationalArray_spec B (n * n) M "ell.nextshape" "ell.shape"
      (fun k => A k.divNat k.modNat) h1 hnnB hMB hv (by simp [RamCopy.Disjoint,RamCopy.suffixes]))
    (by intro x hx; simp at hx; subst x; simp [copyRationalArray,copyLoop,copyStep,
      copyCoordinate,leftToResult,loadLeft,RamRationalArrays.storeReduced,
      RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])
  rintro σ ⟨hσA,hσs,hσn,hσd,hσN⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=Env.vars (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) "vec.n"; let c2:Nat:=c0 c1 c1; let c3:Env:=Env.setVar (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) "vec.n" c2; let c4:Env→ Nat→ Prop:=Run B (copyRationalArray "ell.nextshape" "ell.shape") c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c0 n n; let c7:Nat→ Nat:=c5 (c0 ((71:Nat)) c6); let c8:Nat:=c7 ((24:Nat)); let c9:List Rat:= @List.ofFn Rat c6 fun (k:Fin c6) => A (@Fin.divNat n n k) (@Fin.modNat n n k); let c10:Env→ Prop:=Represents "ell.shape" c9; let c11:Env→ Prop:=Represents "ell.nextshape" c9; let c12:Env→ Prop:=FieldsAgree (@List.cons String "state.savedn" (@List.nil String)) c3; let c13:String→ List Nat:=Env.arrs c3; let c14:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (And (c10 σ') (And (c11 σ') (@Eq Nat (Env.vars σ' "vec.n") c6))) (And (c12 σ') (∀ a∉ Com.warrs (copyRationalArray "ell.nextshape" "ell.shape"), @Eq (List Nat) (Env.arrs σ' a) (c13 a)))); let c15:Nat:=c7 ((32:Nat)); let c16:Env→ Prop:=(fun (x τ:Env) => And (Represents "ell.shape" (@flatten n n A) τ) (And (Represents "ell.nextshape" (@flatten n n A) τ) (@Eq Nat (Env.vars τ "vec.n") n))) σ; let c17:Env→ Prop:=fun (σ':Env) => And (Run B commitShape σ σ' c15) (c16 σ'); let c18:Prop:= @Exists Env c17; let c19:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.shape"; let c20:String:=c19 ".s"; let c21:String:=c19 ".n"; let c22:String:=c19 ".d"; let c23:Nat→ Nat:=c5 ((1:Nat)); let c24:Nat:=c23 (Expr.size (Expr.var "vec.n")); let c25:Nat:=c23 (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); let c26:Nat:=c23 (Expr.size (Expr.var "state.savedn")); let c27:Nat:=c5 c8 c26; let c28:Nat:=c5 c25 c27; let c29:Com:=Com.assign "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")); let c30:Com:=Com.seq (copyRationalArray "ell.nextshape" "ell.shape") (Com.assign "vec.n" (Expr.var "state.savedn")); @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => c18) (RunStep.use B (fun (σ_1:Env) => And (c11 σ_1) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c20)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c21)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c22)) c6) (@Eq Nat (Env.vars σ_1 "vec.n") c6))))) (copyRationalArray "ell.nextshape" "ell.shape") (fun (σ_1 τ:Env) => And (And (c10 τ) (And (c11 τ) (@Eq Nat (Env.vars τ "vec.n") c6))) (And (FieldsAgree (@List.cons String "state.savedn" (@List.nil String)) σ_1 τ) (∀ a∉ Com.warrs (copyRationalArray "ell.nextshape" "ell.shape"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c8 hcopy c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (And (c10 w) (And (c11 w) (@Eq Nat (Env.vars w "vec.n") c6))) (And (c12 w) (∀ a∉ Com.warrs (copyRationalArray "ell.nextshape" "ell.shape"), @Eq (List Nat) (Env.arrs w a) (c13 a))))) => let c0_1:Prop:=And (And (c10 w) (And (c11 w) (@Eq Nat (Env.vars w "vec.n") c6))) (And (c12 w) (∀ a∉ Com.warrs (copyRationalArray "ell.nextshape" "ell.shape"), @Eq (List Nat) (Env.arrs w a) (c13 a))); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c18) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c17 (Env.setVar w "vec.n" (Env.vars w "state.savedn")) (@And.intro (Run B commitShape σ (Env.setVar w "vec.n" (Env.vars w "state.savedn")) c15) (c16 (Env.setVar w "vec.n" (Env.vars w "state.savedn"))) (RunStep.mono B commitShape σ (Env.setVar w "vec.n" (Env.vars w "state.savedn")) (c5 c24 c28) c15 (RunStep.seq B (Com.assign "state.savedn" (Expr.var "vec.n")) (Com.seq c29 c30) σ (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) (Env.setVar w "vec.n" (Env.vars w "state.savedn")) c24 c28 (RunStep.assign B σ "state.savedn" (Expr.var "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4352_0_0_0))) (RunStep.seq B c29 c30 (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) c3 (Env.setVar w "vec.n" (Env.vars w "state.savedn")) c25 c27 (RunStep.assign B (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c2 (RunStep.eval_mul B (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) (Expr.var "vec.n") (Expr.var "vec.n") c1 c1 (RunStep.eval_var B (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4352_0_0_1)) (RunStep.eval_var B (Env.setVar σ "state.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4352_0_0_2)) ?_)) (RunStep.seq B (copyRationalArray "ell.nextshape" "ell.shape") (Com.assign "vec.n" (Expr.var "state.savedn")) c3 w (Env.setVar w "vec.n" (Env.vars w "state.savedn")) c8 c26 left (RunStep.assign B w "vec.n" (Expr.var "state.savedn") (Env.vars w "state.savedn") (RunStep.eval_var B w "state.savedn" ?_))))) (?nAX_g4352_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4352_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4352_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4352_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4352_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hcopy
  all_goals simp_all [flatten,Represents,FieldsAgree]
  all_goals aesop

theorem copy_center_no_other_writes (b:String)
    (hb:b∉ ["ell.center.s", "ell.center.n", "ell.center.d"]):
    b∉ (copyRationalArray "ell.nextcenter" "ell.center").warrs:=by
  simp at hb
  simp [copyRationalArray,copyLoop,copyStep,copyCoordinate,leftToResult,loadLeft,
    RamRationalArrays.storeReduced,RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,
    Lib.Fill.put,Com.warrs,hb.1,hb.2.1,hb.2.2]

theorem commit_shape_no_other_writes (b:String)
    (hb:b∉ ["ell.shape.s", "ell.shape.n", "ell.shape.d"]):b∉ commitShape.warrs:=by
  simp at hb
  simp [commitShape,copyRationalArray,copyLoop,copyStep,copyCoordinate,leftToResult,loadLeft,
    RamRationalArrays.storeReduced,RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,
    Lib.Fill.put,Com.warrs,hb.1,hb.2.1,hb.2.2]

theorem commitState_spec (B n M:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (h1:1 < B) (hnB:n < B) (hnnB:n * n < B) (hMB:M < B)
    (hA:∀ i j,Height (A i j) M) (hc:∀ i,Height (c i) M):
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ∧
        Represents "ell.nextcenter" (List.ofFn c) σ∧ Extents "ell.center" n σ∧
        Extents "ell.shape" (n * n) σ∧ σ.vars "vec.n"=n)
      commitState
      (fun _ τ => Represents "ell.shape" (flatten A) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        Represents "ell.nextshape" (flatten A) τ∧ Represents "ell.nextcenter" (List.ofFn c) τ∧
        τ.vars "vec.n"=n)
      (71 * n + 71 * (n * n) + 56):=by
  rintro σ ⟨hσA,hσc,hσcExt,hσAExt,hσn⟩
  obtain ⟨τ,hr₁,hτc,hτnextc,hτn⟩:=copyRationalArray_spec B n M "ell.nextcenter" "ell.center" c
    h1 hnB hMB hc (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ
    ⟨hσc,hσcExt ".s" (by simp),hσcExt ".n" (by simp),hσcExt ".d" (by simp),hσn⟩
  have hτA:=RamEllipsoidUpdate.represents_frame hr₁ "ell.nextshape" _ hσA
    (copy_center_no_other_writes _ (by simp)) (copy_center_no_other_writes _ (by simp))
    (copy_center_no_other_writes _ (by simp))
  have hτAExt:=extents_frame hr₁ "ell.shape" (n * n) hσAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact copy_center_no_other_writes _ (by simp))
  obtain ⟨υ,hr₂,hυA,hυnextA,hυn⟩:=commitShape_spec B n M A h1 hnB hnnB hMB hA
    τ ⟨hτA,hτAExt ".s" (by simp),hτAExt ".n" (by simp),hτAExt ".d" (by simp),hτn⟩
  have hυc:=RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc
    (commit_shape_no_other_writes _ (by simp)) (commit_shape_no_other_writes _ (by simp))
    (commit_shape_no_other_writes _ (by simp))
  have hυnextc:=RamEllipsoidUpdate.represents_frame hr₂ "ell.nextcenter" _ hτnextc
    (commit_shape_no_other_writes _ (by simp)) (commit_shape_no_other_writes _ (by simp))
    (commit_shape_no_other_writes _ (by simp))
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυA,hυc,hυnextA,hυnextc,hυn⟩

end Lax109476Proofs.RamCommitState

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStoredBounds

open RationalArithmeticBounds RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamEllipsoidWordBounds

theorem centerValues_height {n:ℕ} (M D:ℕ) (u c:Fin n→ ℚ) (γ:ℚ)
    (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:∀ i,Height (u i) M) (hc:∀ i,Height (c i) M) (hγ:Height γ M):
    ∀ i,Height (centerValues u c γ D i) (centerCap M):=by
  intro i
  have hp:Height (u i * γ) (M ^ 2):=by simpa [pow_two] using height_mul _ _ M M (hu i) hγ
  have hd:Height (c i - u i * γ) (2 * M ^ 3):=by
    have h:=height_sub _ _ M (M ^ 2) (hc i) hp
    convert h using 1
    ring
  have hr:=EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 3) D hd hDpos
  apply height_mono _ hr
  calc
    2 * M ^ 3 * D + 1≤ 2 * M ^ 3 * M + 1:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
    _=2 * M ^ 4 + 1:=by ring
    _≤ centerCap M:=(centerCap_bounds M hM).2.2.2

set_option maxHeartbeats 0 in
theorem shapeValues_height {n:ℕ} (M D:ℕ) (u:Fin n→ ℚ)
    (A:Matrix (Fin n) (Fin n) ℚ) (gs:List ℚ) (hg:4 < gs.length)
    (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:∀ i,Height (u i) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M):
    ∀ i j,Height (shapeValues u A gs hg D i j) (shapeCap M):=by
  intro i j
  let p:=u i * u j
  let t:=gs[1] * p
  let d:=A i j - t
  let r:=RationalRounding.roundDown (gs[0] * d) D
  have hp:Height p (M ^ 2):=by simpa [p,pow_two] using height_mul _ _ M M (hu i) (hu j)
  have ht:Height t (M ^ 3):=by
    have h:=height_mul _ _ M (M ^ 2) hβ hp
    convert h using 1
    ring
  have hd:Height d (2 * M ^ 4):=by
    have h:=height_sub _ _ M (M ^ 3) (hA i j) ht
    convert h using 1
    ring
  have ha:Height (gs[0] * d) (2 * M ^ 5):=by
    have h:=height_mul _ _ M (2 * M ^ 4) hα hd
    convert h using 1
    ring
  have hr:Height r (2 * M ^ 6 + 1):=by
    apply height_mono _ (EllipsoidArithmeticBounds.height_roundDown _ (2 * M ^ 5) D ha hDpos)
    calc
      2 * M ^ 5 * D + 1≤ 2 * M ^ 5 * M + 1:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
      _=2 * M ^ 6 + 1:=by ring
  have hsum:Height (r + if i=j then gs[4] else 0) (6 * M ^ 7):=by
    by_cases hij:i=j
    · simp only [if_pos hij]
      apply height_mono _ (height_add _ _ (2 * M ^ 6 + 1) M hr hδ)
      have hpM:M≤ M ^ 7:=le_self_pow hM (by decide:(7:ℕ) ≠ 0)
      calc
        2 * (2 * M ^ 6 + 1) * M=4 * M ^ 7 + 2 * M:=by ring
        _≤ 6 * M ^ 7:=by omega
    · simp only [if_neg hij,add_zero]
      apply height_mono _ hr
      have hp67:=Nat.pow_le_pow_right hM (by decide:(6:ℕ)≤ 7)
      have hp1:1≤ M ^ 7:=Nat.one_le_pow _ _ hM
      omega
  have hresult:=height_mul _ _ M (6 * M ^ 7) hρ hsum
  apply height_mono _ hresult
  convert (shapeCap_bounds M).2.2.2.2.2.2.2 using 1
  ring

open RamEllipsoidStep RamEllipsoidForm RamMatrixVector RamDotProduct RamEllipsoidUpdate

theorem _root_.Lax109476Proofs.RamEllipsoidStoredBounds.step_stored_bounds (n H M k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ i j,Height (A i j) H) (ha:∀ i,Height (a i) H)
    (hc:∀ i,Height (c i) H) (hnM:n≤ M) (hFM:formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M):
    (∀ i,Height (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)) i)
        (shapeCap (coefficientCap M)))∧
      (∀ i j,Height (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n) i j) (shapeCap (coefficientCap M))):=by
  let D:=2 ^ (2 * k + 3 * n + 9)
  let E:=2 ^ (2 * n + 4)
  let q:=a ⬝ᵥ (A *ᵥ a)
  let N:=coefficientCap M
  let gs:=coefficients n q D E
  have hcapM:=(formHeight_ge n H hH).trans hFM
  have hHM:=(cap_ge n H hH).2.trans hcapM
  have hM:=hH.trans hHM
  have hMN:M≤ N:=(coefficientCap_bounds M).1
  have hN:1≤ N:=hM.trans hMN
  have hDpos:0 < D:=Nat.pow_pos (by decide)
  have hq:Height q M:=height_mono _ (form_height n H A a hH hA ha) hFM
  have hu:∀ i,Height ((A *ᵥ a) i) N:=fun i =>
    height_mono _ (mulVec_height n H A a hH hA ha i) (hcapM.trans hMN)
  have hAc:∀ i j,Height (A i j) N:=fun i j => height_mono _ (hA i j) (hHM.trans hMN)
  have hcc:∀ i,Height (c i) N:=fun i => height_mono _ (hc i) (hHM.trans hMN)
  have hgs:∀ v∈ gs,Height v N:=coefficients_height n M D E q hq hnM hDM hEM hDpos
  have hg:4 < gs.length:=by simp [gs,coefficients]
  have hα:=hgs gs[0] (by simp [gs,coefficients])
  have hβ:=hgs gs[1] (by simp [gs,coefficients])
  have hγ:=hgs gs[2] (by simp [gs,coefficients])
  have hρ:=hgs gs[3] (by simp [gs,coefficients])
  have hδ:=hgs gs[4] (by simp [gs,coefficients])
  have hcenter:=centerValues_height N D (A *ᵥ a) c gs[2] hN (hDM.trans hMN) hDpos hu hcc hγ
  have hshape:=shapeValues_height N D (A *ᵥ a) A gs hg hN (hDM.trans hMN) hDpos hu hAc hα hβ hρ hδ
  have heq:=roundedUpdate_eq_ellipsoid A a c D E
  have hη:(1 / (E:ℚ))=EllipsoidIteration.stepAccuracy n:=by simp [E,EllipsoidIteration.stepAccuracy]
  change (∀ i,Height (EllipsoidCenter.roundedCenter n A a c D i) (shapeCap N))∧
    (∀ i j,Height (EllipsoidCenter.roundedStepShape n A a D (EllipsoidIteration.stepAccuracy n) i j) (shapeCap N))
  constructor
  · intro i
    have h:=height_mono _ (hcenter i) (centerCap_le_shapeCap N)
    simpa only [gs,q,heq.1] using h
  · intro i j
    simpa only [gs,q,heq.2,hη] using hshape i j

end Lax109476Proofs.RamEllipsoidStoredBounds

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

theorem extents_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (b:String) (n:ℕ) (hσ:Extents b n σ):Extents b n τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  intro s hs
  rw [array_length_of_bigStep hstep]
  exact hσ s hs

theorem workspace_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (n:ℕ) (hσ:Workspace n σ):Workspace n τ:=
  ⟨extents_of_run hr _ _ hσ.1,extents_of_run hr _ _ hσ.2.1,
    extents_of_run hr _ _ hσ.2.2.1,extents_of_run hr _ _ hσ.2.2.2⟩

theorem represents_extents (b:String) (xs:List ℚ) (σ:Env)
    (h:Represents b xs σ):Extents b xs.length σ:=by
  intro s hs
  simp at hs
  rcases hs with rfl | rfl | rfl <;> simp [h.1,h.2.1,h.2.2]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem advanceState_spec (B n H M k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j,Height (A i j) H)
    (ha:∀ i,Height (a i) H) (hc:∀ i,Height (c i) H)
    (hqpos:0 < a ⬝ᵥ (A *ᵥ a)) (hnM:n * n≤ M)
    (hFM:RamEllipsoidForm.formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M)
    (hB:2 * (RamShapeCoordinate.shapeCap (coefficientCap M)) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.shape" (flatten A) σ∧ Represents "ell.normal" (List.ofFn a) σ∧
        Represents "ell.center" (List.ofFn c) σ∧ Workspace n σ∧
        σ.vars "vec.n"=n∧ σ.vars "iter.k"=k)
      advanceState
      (fun _ τ => Represents "ell.center"
          (List.ofFn (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) τ∧
        Represents "ell.shape"
          (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
            (EllipsoidIteration.stepAccuracy n))) τ∧
        Workspace n τ∧ τ.vars "vec.n"=n∧ τ.vars "iter.k"=k + 1)
      (stepCost n H M + 71 * n + 71 * (n * n) + 60):=by
  let S:=RamShapeCoordinate.shapeCap (coefficientCap M)
  let A':=EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
    (EllipsoidIteration.stepAccuracy n)
  let c':=EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))
  have bounds:=unified_word_bounds B M n hn hnM hB
  have h1:1 < B:=by omega
  have hnB:n < B:=bounds.2.2.2.1
  have hnnB:n * n < B:=by simpa only [pow_two] using bounds.2.2.1
  have hnM':n≤ M:=(Nat.le_mul_self n).trans hnM
  have hSpos:1≤ S:=by
    have hp:1≤ (coefficientCap M + 1) ^ 8:=Nat.one_le_pow _ _ (by omega)
    dsimp [S,RamShapeCoordinate.shapeCap]
    omega
  have hSS:S≤ S ^ 2:=le_self_pow hSpos (by decide:(2:ℕ) ≠ 0)
  have hSB:S < B:=by change 2 * S ^ 2 + 3 < B at hB; omega
  have hkB:k + 1 < B:=by
    have hp:2 * k + 3 * n + 9 < 2 ^ (2 * k + 3 * n + 9):=Nat.lt_two_pow_self
    have hMB:M < B:=bounds.2.1
    omega
  have hnew:=_root_.Lax109476Proofs.RamEllipsoidStoredBounds.step_stored_bounds n H M k A a c hH hA ha hc hnM' hFM hDM hEM
  rintro σ ⟨hσA,hσa,hσc,hσw,hσn,hσk⟩
  obtain ⟨τ,hr₁,hτc,hτA,hτoldA,hτoldc,hτn,_⟩:=
    ellipsoidStep_spec B n H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM hB
      σ ⟨hσA,hσa,hσc,hσw,hσn,hσk⟩
  have hτk:τ.vars "iter.k"=k:=(hr₁.frame_var _ (by decide)).trans hσk
  have hτcExt:Extents "ell.center" n τ:=by simpa using represents_extents _ _ _ hτoldc
  have hτAExt:Extents "ell.shape" (n * n) τ:=by
    simpa [flatten] using represents_extents _ _ _ hτoldA
  obtain ⟨υ,hr₂,hυA,hυc,_,_,hυn⟩:=commitState_spec B n S A' c' h1 hnB hnnB hSB
    hnew.2 hnew.1 τ ⟨hτA,hτc,hτcExt,hτAExt,hτn⟩
  have hυk:υ.vars "iter.k"=k:=(hr₂.frame_var _ (by decide)).trans hτk
  have haddB:Bop.add.apply (υ.vars "iter.k") 1 < B:=by simpa [Bop.apply,hυk] using hkB
  have hi:Run B (.assign "iter.k" (.add (.var "iter.k") (.lit 1))) υ
      (υ.setVar "iter.k" (k + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hυk] using
      (evalB_bin (evalB_var (by omega:υ.vars "iter.k" < B)) (evalB_lit h1)
        haddB))
  have hrun:=hr₁.seq (hr₂.seq hi)
  refine ⟨_,hrun.mono (by omega), ?_, ?_,workspace_of_run hrun n hσw, ?_, ?_⟩
  · simpa only [Represents,arrs_setVar] using hυc
  · simpa only [Represents,arrs_setVar] using hυA
  · simpa using hυn
  · simp

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamNonzero

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds

def before {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):Prop:= ∃ j,j.val < k∧ v j ≠ 0

theorem before_zero {n:ℕ} (v:Fin n→ ℚ):¬ before v 0:=by simp [before]

theorem before_succ {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    before v (i.val + 1)↔ before v i.val∨ v i ≠ 0:=by
  constructor
  · rintro ⟨j,hj,hv⟩
    by_cases hji:j.val < i.val
    · exact Or.inl ⟨j,hji,hv⟩
    · have heq:j=i:=Fin.ext (by omega)
      exact Or.inr (heq ▸ hv)
  · rintro (⟨j,hj,hv⟩ | hi)
    · exact ⟨j,by omega,hv⟩
    · exact ⟨i,by omega,hi⟩

def Invariant {n:ℕ} (a:String) (v:Fin n→ ℚ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧ σ.vars "nonzero.flag" ≤ 1∧
    (σ.vars "nonzero.flag"=1↔ before v (σ.vars "nonzero.i"))∧
    σ.vars "nonzero.i" ≤ n∧ σ.vars "vec.n"=n

set_option maxHeartbeats 0 in
theorem scanStep_spec (B n M:ℕ) (a:String) (v:Fin n→ ℚ)
    (hnB:n < B) (h1:1 < B) (hMB:M < B) (hv:∀ i,Height (v i) M):
    Spec B (fun σ => Invariant a v σ∧ σ.vars "nonzero.i" < n) (scanStep a)
      (fun σ τ => Invariant a v τ∧ τ.vars "nonzero.i"=σ.vars "nonzero.i" + 1) 12:=by
  rintro σ ⟨⟨hσv,hσflag,hσbefore,hσiN,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "nonzero.i",hσi⟩
  have hiB:σ.vars "nonzero.i" < B:=hσi.trans hnB
  have hi1B:σ.vars "nonzero.i" + 1 < B:=lt_of_le_of_lt hσi hnB
  have hnumB:(v i).num.natAbs < B:=(hv i).1.trans_lt hMB
  have hlen:σ.vars "nonzero.i" < (σ.arrs (a ++ ".n")).length:=by
    rw [hσv.2.1]
    simpa using hσi
  have hget:(σ.arrs (a ++ ".n")).getD (σ.vars "nonzero.i") 0=(v i).num.natAbs:=by
    rw [hσv.2.1,map_getD _ _ _ (by simpa using hσi)]
    simp [i]
  have hne:0 < (v i).num.natAbs↔ v i ≠ 0:=by
    rw [Nat.pos_iff_ne_zero,Int.natAbs_ne_zero,Rat.num_ne_zero]
  have hnext:=before_succ v i
  have h0:0 < B:=by omega
  (expose_names;
    (refine let c0:String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".n"; let c1:Nat:= @List.getD Nat (Env.arrs σ c0) (Env.vars σ "nonzero.i") ((0:Nat)); let c2:Prop:=Nat.lt ((0:Nat)) c1; let c3:Prop:=Not c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Invariant n a v τ) (@Eq Nat (Env.vars τ "nonzero.i") (c4 (Env.vars σ_1 "nonzero.i") ((1:Nat))))) σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B (scanStep a) σ σ' ((12:Nat))) (c5 σ'); let c7:Env:=Env.setVar σ "nonzero.flag" ((1:Nat)); let c8:Nat:=Env.vars c7 "nonzero.i"; let c9:Nat:=c4 c8 ((1:Nat)); let c10:Env:=Env.setVar c7 "nonzero.i" c9; let c11:Nat→ Nat:=c4 ((1:Nat)); let c12:Expr:=Expr.get c0 (Expr.var "nonzero.i"); let c13:Cond:=Cond.lt (Expr.lit ((0:Nat))) c12; let c14:Nat→ Nat:=c4 (c11 (Cond.size c13)); let c15:Nat:=c11 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat:=c14 c15; let c17:Expr:=Expr.add (Expr.var "nonzero.i") (Expr.lit ((1:Nat))); let c18:Nat:=c11 (Expr.size c17); let c19:Com:=Com.assign "nonzero.flag" (Expr.lit ((1:Nat))); let c20:Nat:=c4 (Env.vars σ "nonzero.i") ((1:Nat)); let c21:Env:=Env.setVar σ "nonzero.i" c20; let c22:Nat:=c14 ((1:Nat)); @Or.casesOn c2 c3 (fun (x:Or c2 c3) => @Exists Env c6) (Classical.em c2) (fun (hcase:c2) => @Exists.intro Env c6 c10 (@And.intro (Run B (scanStep a) σ c10 ((12:Nat))) (c5 c10) (RunStep.mono B (scanStep a) σ c10 (c4 c16 c18) ((12:Nat)) (RunStep.seq B (Com.ite c13 c19 Com.skip) (Com.assign "nonzero.i" c17) σ c7 c10 c16 c18 (RunStep.ite_true B c13 c19 Com.skip σ c7 c15 (RunStep.cond_lt_true B σ (Expr.lit ((0:Nat))) c12 ((0:Nat)) c1 (RunStep.eval_lit B ((0:Nat)) σ h0) (RunStep.eval_get B σ c0 (Expr.var "nonzero.i") (Env.vars σ "nonzero.i") (RunStep.eval_var B σ "nonzero.i" hiB) hlen (?nAX_g4543_0_0_0)) hcase) (RunStep.assign B σ "nonzero.flag" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1))) (RunStep.assign B c7 "nonzero.i" c17 c9 (RunStep.eval_add B c7 (Expr.var "nonzero.i") (Expr.lit ((1:Nat))) c8 ((1:Nat)) (RunStep.eval_var B c7 "nonzero.i" (?nAX_g4543_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c7 h1) (?nAX_g4543_0_0_2)))) (?nAX_g4543_0_0_3)) ?_)) fun (hcase:c3) => @Exists.intro Env c6 c21 (@And.intro (Run B (scanStep a) σ c21 ((12:Nat))) (c5 c21) (RunStep.mono B (scanStep a) σ c21 (c4 c22 c18) ((12:Nat)) (RunStep.seq B (Com.ite c13 c19 Com.skip) (Com.assign "nonzero.i" c17) σ σ c21 c22 c18 (RunStep.ite_false B c13 c19 Com.skip σ σ ((1:Nat)) (RunStep.cond_lt_false B σ (Expr.lit ((0:Nat))) c12 ((0:Nat)) c1 (RunStep.eval_lit B ((0:Nat)) σ h0) (RunStep.eval_get B σ c0 (Expr.var "nonzero.i") (Env.vars σ "nonzero.i") (RunStep.eval_var B σ "nonzero.i" hiB) hlen (?nAX_g4543_0_0_4)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "nonzero.i" c17 c20 (RunStep.eval_add B σ (Expr.var "nonzero.i") (Expr.lit ((1:Nat))) (Env.vars σ "nonzero.i") ((1:Nat)) (RunStep.eval_var B σ "nonzero.i" hiB) (RunStep.eval_lit B ((1:Nat)) σ h1) hi1B))) (?nAX_g4543_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4543_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4543_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4543_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4543_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4543_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4543_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Invariant,Represents,hne,hnext,i]
  all_goals aesop

theorem scan_spec (B n M:ℕ) (a:String) (v:Fin n→ ℚ)
    (hnB:n < B) (h1:1 < B) (hMB:M < B) (hv:∀ i,Height (v i) M):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "vec.n"=n) (scan a)
      (fun _ τ => τ.vars "nonzero.flag" ≤ 1∧ (τ.vars "nonzero.flag"=1↔ v ≠ 0)∧
        Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n) (16 * n + 8):=by
  have hlo:=Spec.forRangeZero "nonzero.i" "vec.n" (Invariant a v) n 12 hnB
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2) (scanStep_spec B n M a v hnB h1 hMB hv)
  have hdone:before v n↔ v ≠ 0:=by
    simp only [before,Fin.isLt,true_and]
    rw [ne_eq,funext_iff]
    push Not
    rfl
  have hloop:Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "vec.n"=n∧
        σ.vars "nonzero.flag"=0)
      (scanLoop a)
      (fun _ τ => τ.vars "nonzero.flag" ≤ 1∧ (τ.vars "nonzero.flag"=1↔ v ≠ 0)∧
        Represents a (List.ofFn v) τ∧ τ.vars "vec.n"=n) (16 * n + 6):=by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hv',hn,hflag⟩
      simp_all [Invariant,Represents,before_zero]
    · rintro σ τ _ ⟨hτ,hi⟩
      exact ⟨hτ.2.1,by simpa only [hi,hdone] using hτ.2.2.1,hτ.1,hτ.2.2.2.2⟩
  rintro σ ⟨hσv,hσn⟩
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "nonzero.flag" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B (scanLoop a) c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((16:Nat)) n); let c4:Nat:=c3 ((6:Nat)); let c5:Prop:= @Ne (Fin n→ Rat) v (@OfNat.ofNat (Fin n→ Rat) (nat_lit 0) (@Zero.toOfNat0 (Fin n→ Rat) (@Pi.instZero (Fin n) (fun (a_1:Fin n) => Rat) fun (i:Fin n) => @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))); let c6:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (Nat.le (Env.vars σ' "nonzero.flag") ((1:Nat))) (And (Iff (@Eq Nat (Env.vars σ' "nonzero.flag") ((1:Nat))) c5) (And (Represents a (@List.ofFn Rat n v) σ') (@Eq Nat (Env.vars σ' "vec.n") n)))); let c7:Nat:=c3 ((8:Nat)); let c8:Env→ Env→ Prop:=fun (x τ:Env) => And (Nat.le (Env.vars τ "nonzero.flag") ((1:Nat))) (And (Iff (@Eq Nat (Env.vars τ "nonzero.flag") ((1:Nat))) c5) (And (Represents a (@List.ofFn Rat n v) τ) (@Eq Nat (Env.vars τ "vec.n") n))); let c9:Env→ Prop:=c8 σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B (scan a) σ σ' c7) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:String→ Nat:=Env.vars c0; let c13:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c11) (RunStep.use B (fun (σ_1:Env) => And (Represents a (@List.ofFn Rat n v) σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.n") n) (@Eq Nat (Env.vars σ_1 "nonzero.flag") ((0:Nat))))) (scanLoop a) c8 c4 hloop c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (Nat.le (Env.vars w "nonzero.flag") ((1:Nat))) (And (Iff (@Eq Nat (Env.vars w "nonzero.flag") ((1:Nat))) c5) (And (Represents a (@List.ofFn Rat n v) w) (@Eq Nat (Env.vars w "vec.n") n))))) => let c0_1:Prop:=And (Nat.le (Env.vars w "nonzero.flag") ((1:Nat))) (And (Iff (@Eq Nat (Env.vars w "nonzero.flag") ((1:Nat))) c5) (And (Represents a (@List.ofFn Rat n v) w) (@Eq Nat (Env.vars w "vec.n") n))); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c11) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c10 w (@And.intro (Run B (scan a) σ w c7) (c9 w) (RunStep.mono B (scan a) σ w (c2 c13 c4) c7 (RunStep.seq B (Com.assign "nonzero.flag" (Expr.lit ((0:Nat)))) (scanLoop a) σ c0 w c13 c4 (RunStep.assign B σ "nonzero.flag" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4546_0_0_0))) left) (?nAX_g4546_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4546_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4546_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hloop hlo
  all_goals simp_all [Represents]

end Lax109476Proofs.RamNonzero

end

section

namespace Lax109476Proofs.RamRowCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamMatrixRows
open RamCopy RamCenterUpdate RamZeroArray

def loopFields:List String:= ["copy.i", "vec.i", "vec.n", "row.base"]

set_option maxHeartbeats 0 in
theorem copyCoordinate_spec (B M base i:ℕ) (a b:String) (xs ys:List ℚ)
    (hi:i < xs.length) (hiy:i < ys.length) (hiB:base + i < B) (h1:1 < B)
    (hMB:M < B) (hq:Height xs[i] M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Slice a xs base σ∧ Represents b ys σ∧
        σ.vars "copy.i"=i∧ σ.vars "row.base"=base)
      (copyCoordinate a b)
      (fun _ τ => Represents b (ys.set i xs[i]) τ∧ Slice a xs base τ) 36:=by
  have hiB':i < B:=by omega
  have hload:=spec_with_fields loopFields
    (loadRowLeft_spec B base i a xs hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [loadRowLeft,Com.wvars]) (by simp [loadRowLeft,Com.warrs])
  have hresult:=spec_with_fields loopFields
    (leftToResult_spec B xs[i] h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [leftToResult,Com.wvars]) (by simp [leftToResult,Com.warrs])
  have hstore:=spec_with_write_frame loopFields
    (storeReduced_spec B b ys xs[i] i hiy h1 hiB' (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [storeReduced,Com.wvars])
  rintro σ ⟨hσa,hσb,hσi,hσbase⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (loadRowLeft a) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c1:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi; let c2:Env→ Prop:=LeftOutput c1; let c3:Env→ Prop:=FieldsAgree loopFields (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c4:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((15:Nat))) (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4))); let c6:Env→ Prop:=Represents b (@List.set Rat ys i c1); let c7:Env→ Prop:=(fun (x τ:Env) => And (c6 τ) (Slice a xs base τ)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B (copyCoordinate a b) σ σ' ((36:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:String→ Nat:=Env.vars (Env.setVar σ "vec.i" (Env.vars σ "copy.i")); let c11:Env→ Prop:=FractionOutput c1; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat:=c12 ((1:Nat)) (Expr.size (Expr.var "copy.i")); let c14:Nat:=c12 ((6:Nat)) ((13:Nat)); let c15:Nat:=c12 ((15:Nat)) c14; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c9) (RunStep.use B (fun (σ_1:Env) => And (Slice a xs base σ_1) (And (@Eq Nat (Env.vars σ_1 "row.base") base) (@Eq Nat (Env.vars σ_1 "vec.i") i))) (loadRowLeft a) (fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((15:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) ?_) fun (w:Env) (h:And (c0 w ((15:Nat))) (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)))) => let c0_1:Prop:=c0 w ((15:Nat)); let c1_1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B leftToResult w σ' ((6:Nat))) (And (c11 σ') (And (FieldsAgree loopFields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c9) (RunStep.use B c2 leftToResult (fun (σ_1 τ:Env) => And (c11 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hresult w ?_) fun (w_1:Env) (h_1:And (Run B leftToResult w w_1 ((6:Nat))) (And (c11 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B leftToResult w w_1 ((6:Nat)); let c1_2:Prop:=And (c11 w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced b) w_1 σ' ((13:Nat))) (And (c6 σ') (And (FieldsAgree loopFields w_1 σ') (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs σ' a_1) (Env.arrs w_1 a_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c9) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents b ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (c11 σ_1))) (storeReduced b) (fun (σ_1 τ:Env) => And (c6 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs τ a_1) (Env.arrs σ_1 a_1)))) ((13:Nat)) hstore w_1 ?_) fun (w_2:Env) (h_2:And (Run B (storeReduced b) w_1 w_2 ((13:Nat))) (And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))))) => let c0_3:Prop:=Run B (storeReduced b) w_1 w_2 ((13:Nat)); let c1_3:Prop:=And (c6 w_2) (And (FieldsAgree loopFields w_1 w_2) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_2 a_1) (Env.arrs w_1 a_1))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c9) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.intro Env c8 w_2 (@And.intro (Run B (copyCoordinate a b) σ w_2 ((36:Nat))) (c7 w_2) (RunStep.mono B (copyCoordinate a b) σ w_2 (c12 c13 c15) ((36:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "copy.i")) (Com.seq (loadRowLeft a) (Com.seq leftToResult (storeReduced b))) σ (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w_2 c13 c15 (RunStep.assign B σ "vec.i" (Expr.var "copy.i") (Env.vars σ "copy.i") (RunStep.eval_var B σ "copy.i" (?nAX_g4549_0_0_0))) (RunStep.seq B (loadRowLeft a) (Com.seq leftToResult (storeReduced b)) (Env.setVar σ "vec.i" (Env.vars σ "copy.i")) w w_2 ((15:Nat)) c14 left (RunStep.seq B leftToResult (storeReduced b) w w_1 w_2 ((6:Nat)) ((13:Nat)) left_1 left_2))) (?nAX_g4549_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4549_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4549_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals clear hload hresult hstore
  all_goals simp_all [RamCopy.Disjoint,suffixes,LeftOutput,FractionOutput,Represents,
    Slice,FieldsAgree,loopFields,storeReduced,Com.warrs]
  all_goals aesop

def CopyInvariant {n:ℕ} (a b:String) (v:Fin n→ ℚ) (base:ℕ) (σ:Env):Prop:=
  Slice a (List.ofFn v) base σ∧ Represents b (filled v (σ.vars "copy.i")) σ∧
    σ.vars "copy.i" ≤ n∧ σ.vars "vec.n"=n∧ σ.vars "row.base"=base

theorem copyStep_spec (B n M base:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:base + n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => CopyInvariant a b v base σ∧ σ.vars "copy.i" < n) (copyStep a b)
      (fun σ τ => CopyInvariant a b v base τ∧ τ.vars "copy.i"=σ.vars "copy.i" + 1) 40:=by
  rintro σ ⟨⟨hσa,hσb,hσiN,hσn,hσbase⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "copy.i",hσi⟩
  have hiB:base + i.val < B:=by have:=i.isLt; omega
  have hvi:Height (List.ofFn v)[i.val] M:=by simpa using hv i
  obtain ⟨τ,hr₁,hτb,hτa⟩:=copyCoordinate_spec B M base i.val a b (List.ofFn v)
    (filled v i.val) (by simp) (by simp [filled]) hiB h1 hMB hvi hab
    σ ⟨hσa,hσb,rfl,hσbase⟩
  have hτi:τ.vars "copy.i"=i.val:=hr₁.frame_var _ (by
    simp [copyCoordinate,loadRowLeft,leftToResult,storeReduced,Com.wvars])
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var _ (by
    simp [copyCoordinate,loadRowLeft,leftToResult,storeReduced,Com.wvars])).trans hσn
  have hτbase:τ.vars "row.base"=base:=(hr₁.frame_var _ (by
    simp [copyCoordinate,loadRowLeft,leftToResult,storeReduced,Com.wvars])).trans hσbase
  have hsumB:Bop.add.apply (τ.vars "copy.i") 1 < B:=by
    simp only [Bop.apply,hτi]
    have:=i.isLt
    omega
  have hiB':i.val < B:=by omega
  have hr₂:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) τ
      (τ.setVar "copy.i" (i.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτi] using
      (evalB_bin (evalB_var (hτi ▸ hiB')) (evalB_lit h1) hsumB))
  have hnext:Represents b (filled v (i.val + 1)) τ:=by
    rw [← filled_step]
    simpa only [List.getElem_ofFn,Fin.eta] using hτb
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Slice,arrs_setVar] using hτa
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change i.val + 1≤ n
    exact i.isLt
  · simpa using hτn
  · simpa using hτbase
  · simp [i]

theorem copyLoop_spec (B n M base:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:base + n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Slice a (List.ofFn v) base σ∧ Represents b (List.replicate n 0) σ∧
        σ.vars "vec.n"=n∧ σ.vars "row.base"=base)
      (copyLoop a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Slice a (List.ofFn v) base τ∧
        τ.vars "vec.n"=n∧ τ.vars "row.base"=base) (44 * n + 6):=by
  have hnB':n < B:=by omega
  have hlo:=Spec.forRangeZero "copy.i" "vec.n" (CopyInvariant a b v base) n 40 hnB'
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (copyStep_spec B n M base a b v h1 hnB hMB hv hab)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨ha,hb,hn,hbase⟩
    simp_all [CopyInvariant,Slice,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hi⟩
    refine ⟨?_,hτ.1,hτ.2.2.2.1,hτ.2.2.2.2⟩
    simpa only [hi,filled_done] using hτ.2.1

theorem copyRow_spec (B n M base:ℕ) (a b:String) (v:Fin n→ ℚ)
    (h1:1 < B) (hnB:base + n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Slice a (List.ofFn v) base σ∧ (σ.arrs (b ++ ".s")).length=n∧
        (σ.arrs (b ++ ".n")).length=n∧ (σ.arrs (b ++ ".d")).length=n∧
        σ.vars "vec.n"=n∧ σ.vars "row.base"=base)
      (copyRow a b)
      (fun _ τ => Represents b (List.ofFn v) τ∧ Slice a (List.ofFn v) base τ∧
        τ.vars "vec.n"=n∧ τ.vars "row.base"=base) (77 * n + 24):=by
  have hnB':n < B:=by omega
  have hz:=spec_with_write_frame ["row.base"] (zeroRationalArray_spec B n b hnB' h1)
    (by intro x hx; simp at hx; subst x; simp [zeroRationalArray,fillConstant,Lib.Fill.put,Com.wvars])
  have hc:=copyLoop_spec B n M base a b v h1 hnB hMB hv hab
  rintro σ ⟨ha,hs,hnum,hd,hn,hbase⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c0 (c1 ((33:Nat)) n) ((18:Nat)); let c3:Env→ Prop:=Represents b (@List.replicate Rat n (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c4:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) b; let c5:String:=c4 ".s"; let c6:String:=c4 ".n"; let c7:String:=c4 ".d"; let c8:Env→ Prop:=FieldsAgree (@List.cons String "row.base" (@List.nil String)) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B (zeroRationalArray b) σ σ' c2) (And (And (c3 σ') (And (@Eq Nat (Env.vars σ' "vec.n") n) (∀ b_1∉ @List.cons String c5 (@List.cons String c6 (@List.cons String c7 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b_1) (Env.arrs σ b_1)))) (And (c8 σ') (∀ a_1∉ Com.warrs (zeroRationalArray b), @Eq (List Nat) (Env.arrs σ' a_1) (Env.arrs σ a_1)))); let c10:Nat:=c0 (c1 ((77:Nat)) n) ((24:Nat)); let c11:Env→ Prop:=Slice a (@List.ofFn Rat n v) base; let c12:Env→ Env→ Prop:=fun (x τ:Env) => And (Represents b (@List.ofFn Rat n v) τ) (And (c11 τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (@Eq Nat (Env.vars τ "row.base") base))); let c13:Env→ Prop:=c12 σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B (copyRow a b) σ σ' c10) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:Nat:=c0 (c1 ((44:Nat)) n) ((6:Nat)); @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c15) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c5)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c6)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c7)) n) (@Eq Nat (Env.vars σ_1 "vec.n") n)))) (zeroRationalArray b) (fun (σ_1 τ:Env) => And (And (c3 τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (∀ b_1∉ @List.cons String c5 (@List.cons String c6 (@List.cons String c7 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b_1) (Env.arrs σ_1 b_1)))) (And (FieldsAgree (@List.cons String "row.base" (@List.nil String)) σ_1 τ) (∀ a_1∉ Com.warrs (zeroRationalArray b), @Eq (List Nat) (Env.arrs τ a_1) (Env.arrs σ_1 a_1)))) c2 hz σ ?_) fun (w:Env) (h:And (Run B (zeroRationalArray b) σ w c2) (And (And (c3 w) (And (@Eq Nat (Env.vars w "vec.n") n) (∀ b_1∉ @List.cons String c5 (@List.cons String c6 (@List.cons String c7 (@List.nil String))), @Eq (List Nat) (Env.arrs w b_1) (Env.arrs σ b_1)))) (And (c8 w) (∀ a_1∉ Com.warrs (zeroRationalArray b), @Eq (List Nat) (Env.arrs w a_1) (Env.arrs σ a_1))))) => let c0_1:Prop:=Run B (zeroRationalArray b) σ w c2; let c1_1:Prop→ Prop:=And (@Eq Nat (Env.vars w "vec.n") n); let c2_1:Prop:=And (And (c3 w) (c1_1 (∀ b_1∉ @List.cons String c5 (@List.cons String c6 (@List.cons String c7 (@List.nil String))), @Eq (List Nat) (Env.arrs w b_1) (Env.arrs σ b_1)))) (And (c8 w) (∀ a_1∉ Com.warrs (zeroRationalArray b), @Eq (List Nat) (Env.arrs w a_1) (Env.arrs σ a_1))); let c3_1:Env→ Prop:=fun (σ':Env) => And (Run B (copyLoop a b) w σ' c16) (And (Represents b (@List.ofFn Rat n v) σ') (And (c11 σ') (And (@Eq Nat (Env.vars σ' "vec.n") n) (@Eq Nat (Env.vars σ' "row.base") base)))); @And.casesOn c0_1 c2_1 (fun (x:And c0_1 c2_1) => c15) h fun (left:c0_1) (right:c2_1) => @Exists.casesOn Env c3_1 (fun (x:@Exists Env c3_1) => c15) (RunStep.use B (fun (σ_1:Env) => And (c11 σ_1) (And (c3 σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.n") n) (@Eq Nat (Env.vars σ_1 "row.base") base)))) (copyLoop a b) c12 c16 hc w ?_) fun (w_1:Env) (h_1:And (Run B (copyLoop a b) w w_1 c16) (And (Represents b (@List.ofFn Rat n v) w_1) (And (c11 w_1) (And (@Eq Nat (Env.vars w_1 "vec.n") n) (@Eq Nat (Env.vars w_1 "row.base") base))))) => let c0_2:Prop:=Run B (copyLoop a b) w w_1 c16; let c1_2:Prop:=And (Represents b (@List.ofFn Rat n v) w_1) (And (c11 w_1) (And (@Eq Nat (Env.vars w_1 "vec.n") n) (@Eq Nat (Env.vars w_1 "row.base") base))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c15) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c14 w_1 (@And.intro (Run B (copyRow a b) σ w_1 c10) (c13 w_1) (RunStep.mono B (copyRow a b) σ w_1 (c0 c2 c16) c10 (RunStep.seq B (zeroRationalArray b) (copyLoop a b) σ w w_1 c2 c16 left left_1) (?nAX_g4556_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4556_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hz hc
  all_goals simp_all [Slice,FieldsAgree,RamCopy.Disjoint,suffixes]
  all_goals aesop

end Lax109476Proofs.RamRowCopy

end

section

namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

theorem cap_two_pow (n h:ℕ):cap n (2 ^ h)=2 ^ ((2 * h + 1) * (n + 1)):=by
  simp only [cap, ← pow_two]
  change (2 ^ 1 * (2 ^ h) ^ 2) ^ (n + 1)=_
  rw [← pow_mul, ← pow_add, ← pow_mul]
  congr 1
  ring

theorem formHeight_two_pow (n h:ℕ):formHeight n (2 ^ h)=2 ^ formExponent n h:=by
  simp only [formHeight,cap_two_pow,formExponent]

theorem guard_size (M:ℕ):
    (2 * (shapeCap (coefficientCap M)) ^ 2 + 3).size≤ 64 * M.size + 160:=by
  have hc:=coefficientCap_size M
  have hs:=shapeCap_size (coefficientCap M)
  have hp:=size_pow_le (shapeCap (coefficientCap M)) 2
  have hm:=size_mul_le 2 ((shapeCap (coefficientCap M)) ^ 2)
  have ha:=size_add_le (2 * (shapeCap (coefficientCap M)) ^ 2) 3
  have htwo:Nat.size 2=2:=by decide
  have hthree:Nat.size 3=2:=by decide
  omega

theorem magnitude_parameters (n h k:ℕ):
    n * n≤ 2 ^ magnitudeExponent n h k∧
      formHeight n (2 ^ h)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * k + 3 * n + 9)≤ 2 ^ magnitudeExponent n h k∧
      2 ^ (2 * n + 4)≤ 2 ^ magnitudeExponent n h k:=by
  have hn:n * n < 2 ^ (n * n):=Nat.lt_two_pow_self
  have hexp:n * n≤ magnitudeExponent n h k:=by unfold magnitudeExponent; omega
  refine ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) hexp), ?_, ?_, ?_⟩
  · rw [formHeight_two_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega
  · apply Nat.pow_le_pow_right (by decide)
    unfold magnitudeExponent
    omega

theorem wordWidth_sufficient (n h k w:ℕ) (hw:wordWidth n h k≤ w):
    2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3 < 2 ^ w:=by
  have hg:=guard_size (2 ^ magnitudeExponent n h k)
  rw [Nat.size_pow] at hg
  have hp:=Nat.lt_size_self (2 * (shapeCap (coefficientCap (2 ^ magnitudeExponent n h k))) ^ 2 + 3)
  apply hp.trans_le
  apply Nat.pow_le_pow_right (by decide)
  unfold wordWidth at hw
  omega

end Lax109476Proofs.RamEllipsoidBitBounds

end

section

open scoped BigOperators

namespace Lax109476Proofs.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding RationalSizeBounds
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding

theorem entry_bound_of_form {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (A *ᵥ x)≤ M * (x ⬝ᵥ x)) (i j:Fin n):
    |A i j|≤ M:=by
  let e:Fin n→ Fin n→ ℝ:=fun k => Pi.single k 1
  have hne:e j ≠ 0:=by
    intro h
    have hh:=congrFun h j
    simp [e] at hh
  have hcs:=form_cauchy_schwarz hA (e j) (e i) hne
  have hi:=hupper (e i)
  have hj:=hupper (e j)
  have hip:=hA.posSemidef.dotProduct_mulVec_nonneg (e i)
  have hjp:=hA.posSemidef.dotProduct_mulVec_nonneg (e j)
  simp [e,Matrix.mulVec,dotProduct,Pi.single_apply] at hcs hi hj hip hjp
  have hp:A j j * A i i≤ M * M:=mul_le_mul hj hi hip hM
  have hs:(A i j) ^ 2≤ M ^ 2:=by nlinarith only [hcs,hp]
  exact (sq_le_sq₀ (abs_nonneg _) hM).mp (by simpa only [sq_abs] using hs)

theorem shapes_entry_magnitude (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k:ℕ) (i j:Fin n):|(shapes n a k i j:ℝ)|≤ (4:ℝ) ^ k:=by
  have h:=shapes_invariant n hn a ha k
  exact entry_bound_of_form h.1 _ (by positivity) (fun x => (h.2 x).2) i j

theorem approximateCenter_displacement (n:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (realShape A *ᵥ x)≤ M ^ 2 * (x ⬝ᵥ x)) (i:Fin n):
    |(approximateCenter n A a c D i:ℝ) - (c i:ℝ)|≤ M:=by
  let q:=realVector a ⬝ᵥ (realShape A *ᵥ realVector a)
  let r:ℝ:=sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D
  let t:=(realShape A *ᵥ realVector a) i
  have hq:0 < q:=hA.dotProduct_mulVec_pos ha
  have hqRat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    apply (Rat.cast_nonneg (K:=ℝ)).mp
    rw [cast_direction_form]
    exact hq.le
  have hr:Real.sqrt q≤ r:=by
    simpa only [cast_direction_form] using (sqrtUpper_bounds _ hqRat D hD).1
  have hrp:0 < r:=(Real.sqrt_pos.mpr hq).trans_le hr
  have hrsq:q≤ r ^ 2:=by nlinarith [Real.sqrt_nonneg q,Real.sq_sqrt hq.le]
  have hcs':=form_cauchy_schwarz hA (realVector a) (Pi.single i 1) ha
  have hii:=hupper (Pi.single i 1)
  simp [single_dotProduct,dotProduct_single] at hcs' hii
  have ht:t ^ 2≤ r ^ 2 * M ^ 2:=by
    have hmul:=mul_le_mul_of_nonneg_left hii hq.le
    have hmul':=mul_le_mul_of_nonneg_right hrsq (sq_nonneg M)
    dsimp [q,t] at *
    nlinarith only [hcs',hmul,hmul']
  have hab:|t|≤ r * M:=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hrp.le hM)).mp (by
      simpa only [sq_abs,mul_pow] using ht)
  have hn:(1:ℝ)≤ (n:ℝ) + 1:=by have:=(Nat.cast_nonneg n:(0:ℝ)≤ n); linarith
  have hden:0 < ((n:ℝ) + 1) * r:=by positivity
  have hb:|t / (((n:ℝ) + 1) * r)|≤ M:=by
    rw [abs_div,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    exact hab.trans (by nlinarith [mul_nonneg hrp.le hM])
  have he:(approximateCenter n A a c D i:ℝ) - (c i:ℝ) =
      -(t / (((n:ℝ) + 1) * r)):=by
    simp [approximateCenter,realShape,realVector,Matrix.mulVec,dotProduct,
      Rat.cast_sum,r,t,smul_eq_mul,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [he,abs_neg]
  exact hb

theorem roundedCenter_displacement (n:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (M:ℝ) (hM:0≤ M)
    (hupper:∀ x,x ⬝ᵥ (realShape A *ᵥ x)≤ M ^ 2 * (x ⬝ᵥ x)) (i:Fin n):
    |(roundedCenter n A a c D i:ℝ) - (c i:ℝ)|≤ M + 1:=by
  have h:=approximateCenter_displacement n A hA a c ha D hD M hM hupper i
  have he:=roundDown_error (approximateCenter n A a c D i) D hD
  have hi:(1:ℝ) / D≤ 1:=by
    apply (div_le_one (by exact_mod_cast hD)).mpr
    exact_mod_cast hD
  have hround:|(roundedCenter n A a c D i:ℝ) -
      (approximateCenter n A a c D i:ℝ)|≤ 1:=by
    change |(roundDown (approximateCenter n A a c D i) D:ℝ) - _|≤ _
    rw [abs_sub_comm,abs_of_nonneg he.1]
    exact he.2.le.trans hi
  calc
    _≤ |(roundedCenter n A a c D i:ℝ) - (approximateCenter n A a c D i:ℝ)| +
      |(approximateCenter n A a c D i:ℝ) - (c i:ℝ)|:=abs_sub_le _ _ _
    _≤ _:=add_le_add hround h |>.trans_eq (add_comm _ _)

theorem centers_magnitude (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k:ℕ) (i:Fin n):|(centers n a 0 k i:ℝ)|≤ (2:ℝ) ^ (k + 2):=by
  induction k with
  | zero => simp [centers]
  | succ k ih =>
    have h:=shapes_invariant n hn a ha k
    have hne:realVector (a k) ≠ 0:=by
      intro he
      have hh:=ha k
      rw [he,dotProduct_zero] at hh
      norm_num at hh
    have hp:(4:ℝ) ^ k=((2:ℝ) ^ k) ^ 2:=by
      rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
    have hd:=roundedCenter_displacement n (shapes n a k) h.1 (a k)
      (centers n a 0 k) hne (gridDenominator (2 * k + 2) (2 * n + 4) n)
      (gridDenominator_pos _ _ _) ((2:ℝ) ^ k)
      (by positivity) (fun x => by rw [← hp]; exact (h.2 x).2) i
    change |(roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i:ℝ)|≤ _
    have hab:=abs_sub_le (roundedCenter n (shapes n a k) (a k) (centers n a 0 k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) i:ℝ)
      (centers n a 0 k i:ℝ) 0
    simp only [sub_zero] at hab
    have hpow:1≤ (2:ℝ) ^ k:=one_le_pow₀ (by norm_num)
    rw [show k + 1 + 2=k + 3 by omega,pow_add]
    rw [show k + 2=k + 2 by rfl,pow_add] at ih
    norm_num only [show (2:ℝ) ^ 2=4 by norm_num,
      show (2:ℝ) ^ 3=8 by norm_num] at *
    linarith

def shapeGrid (n k:ℕ):ℕ:=
  gridDenominator (2 * k + 2) (2 * n + 4) n * (2 ^ (2 * n + 4)) ^ 2

theorem shapeGrid_pos (n k:ℕ):0 < shapeGrid n k:=by
  unfold shapeGrid
  exact Nat.mul_pos (gridDenominator_pos _ _ _) (by positivity)

theorem shapeGrid_size (n k:ℕ):(shapeGrid n k).size=2 * k + 7 * n + 18:=by
  unfold shapeGrid gridDenominator
  rw [← pow_mul, ← pow_add,Nat.size_pow]
  omega

theorem stored_shape_grid (n k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (i j:Fin n):
    ∃ z:ℤ,roundedStepShape n A a
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n) i j =
        (z:ℚ) / (shapeGrid n k:ℕ):=by
  let D:=gridDenominator (2 * k + 2) (2 * n + 4) n
  let S:=2 ^ (2 * n + 4)
  refine ⟨((S:ℤ) + 1) ^ 2 *
    (Int.floor (cutShape n A a i j * D) + if i=j then (n:ℤ) else 0), ?_⟩
  have hD:(D:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt (gridDenominator_pos _ _ _)
  have hS:(S:ℚ) ≠ 0:=by dsimp [S]; positivity
  simp only [roundedStepShape,roundedShape,stepAccuracy,Matrix.smul_apply,
    Matrix.add_apply,Matrix.of_apply,Matrix.one_apply,smul_eq_mul,
    roundDown,Int.cast_mul,Int.cast_pow,Int.cast_add,Int.cast_natCast,
    Int.cast_one,Int.cast_ite,Int.cast_zero,shapeGrid,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_ofNat]
  have hScast:(2:ℚ) ^ (2 * n + 4)=(S:ℚ):=by simp [S]
  rw [hScast]
  change ((1 + 1 / (S:ℚ)) ^ 2) *
    ((Int.floor (cutShape n A a i j * D):ℚ) / D +
      (n:ℚ) / D * (if i=j then 1 else 0)) =
        (((S:ℚ) + 1) ^ 2 *
          ((Int.floor (cutShape n A a i j * D):ℚ) + if i=j then (n:ℚ) else 0)) /
          ((D:ℚ) * (S:ℚ) ^ 2)
  split_ifs <;> field_simp <;> ring

theorem shapes_denominator (n:ℕ) (a:ℕ→ Fin n→ ℚ) (k:ℕ) (i j:Fin n):
    (shapes n a (k + 1) i j).den≤ shapeGrid n k:=by
  obtain ⟨z,hz⟩:=stored_shape_grid n k (shapes n a k) (a k) i j
  change (roundedStepShape n (shapes n a k) (a k) _ _ i j).den≤ _
  rw [hz]
  exact (grid_num_den_bound z _ (shapeGrid_pos n k)).2

theorem numerator_bound_of_magnitude (q:ℚ) (M D:ℕ)
    (hm:|(q:ℝ)|≤ M) (hd:q.den≤ D):q.num.natAbs≤ M * D:=by
  have hnum:(q.num.natAbs:ℝ)=|(q:ℝ)| * (q.den:ℝ):=by
    rw [Nat.cast_natAbs,Int.cast_abs]
    have he:=congrArg (fun r:ℚ => (r:ℝ)) q.mul_den_eq_num
    simp only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_intCast] at he
    rw [← he,abs_mul,abs_of_nonneg (a:=(q.den:ℝ)) (Nat.cast_nonneg _)]
  have hdR:(q.den:ℝ)≤ D:=by exact_mod_cast hd
  have h:=mul_le_mul hm hdR (Nat.cast_nonneg _) (Nat.cast_nonneg M)
  rw [← hnum] at h
  exact_mod_cast h

theorem encoding_bound_of_magnitude (q:ℚ) (M D:ℕ)
    (hm:|(q:ℝ)|≤ M) (hd:q.den≤ D):
    bitSize (encodeRational q)≤ 4 + M.size + 2 * D.size:=by
  have hn:=Nat.size_le_size (numerator_bound_of_magnitude q M D hm hd)
  have hmul:=size_mul_le M D
  have hds:=Nat.size_le_size hd
  have he:=EncodingSize.rational_size_upper q
  omega

theorem shapes_encoding_size (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ) (i j:Fin n):
    bitSize (encodeRational (shapes n a k i j))≤ 60 + 6 * k + 14 * n:=by
  cases k with
  | zero =>
    have h:=EncodingSize.rational_size_upper (shapes n a 0 i j)
    simp only [shapes,Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> norm_num at h <;> omega
  | succ k =>
    have hm:|(shapes n a (k + 1) i j:ℝ)|≤ (4 ^ (k + 1):ℕ):=by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using shapes_entry_magnitude n hn a ha (k + 1) i j
    have he:=encoding_bound_of_magnitude _ _ _ hm (shapes_denominator n a k i j)
    have hsizeM:(4 ^ (k + 1):ℕ).size=2 * (k + 1) + 1:=by
      rw [show (4:ℕ)=2 ^ 2 by decide, ← pow_mul,Nat.size_pow]
    rw [hsizeM,shapeGrid_size] at he
    omega

theorem centers_denominator (n:ℕ) (a:ℕ→ Fin n→ ℚ) (k:ℕ) (i:Fin n):
    (centers n a 0 (k + 1) i).den≤ gridDenominator (2 * k + 2) (2 * n + 4) n:=by
  exact (grid_num_den_bound _ _ (gridDenominator_pos _ _ _)).2

theorem centers_encoding_size (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ) (i:Fin n):
    bitSize (encodeRational (centers n a 0 k i))≤ 60 + 6 * k + 14 * n:=by
  cases k with
  | zero =>
    have h:=EncodingSize.rational_size_upper (centers n a 0 0 i)
    change bitSize (encodeRational 0)≤ _
    norm_num [centers] at h
    omega
  | succ k =>
    have hm:|(centers n a 0 (k + 1) i:ℝ)|≤ (2 ^ (k + 1 + 2):ℕ):=by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using centers_magnitude n hn a ha (k + 1) i
    have he:=encoding_bound_of_magnitude _ _ _ hm (centers_denominator n a k i)
    rw [Nat.size_pow,sequence_grid_size] at he
    omega

end Lax109476Proofs.EllipsoidStateSize

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamTrajectoryBounds

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding Lax109476.RationalCertificates
open RationalArithmeticBounds EncodingSize EllipsoidSearch EllipsoidSequence EllipsoidStateSize
open RamEllipsoidBitBounds RamEllipsoidStep RamAdvanceState RamRationalArrays RamMatrixStorage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem height_of_encoding (q:ℚ) (h:ℕ) (hq:bitSize (encodeRational q)≤ h):
    Height q (2 ^ h):=by
  have hs:=(rational_size_bounds q).2
  have hn:q.num.natAbs < 2 ^ q.num.natAbs.size:=Nat.lt_size_self _
  have hd:q.den < 2 ^ q.den.size:=Nat.lt_size_self _
  exact ⟨hn.le.trans (Nat.pow_le_pow_right (by decide) (by omega)),
    hd.le.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

theorem selectedNormal_height {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (c:Fin n→ ℚ) (H:ℕ) (hH:1≤ H) (hA:∀ i j, (A i j).natAbs≤ H):
    ∀ j,Height (selectedNormal A b c j) H:=by
  intro j
  cases hf:RationalSeparation.firstViolation A b c with
  | none =>
    simp only [selectedNormal,hf]
    unfold fallbackNormal
    split_ifs <;> simp_all [Height]
  | some i =>
    simp only [selectedNormal,hf]
    by_cases hz:A i=0
    · simp only [if_pos hz]
      unfold fallbackNormal
      split_ifs <;> simp_all [Height]
    · simp only [if_neg hz]
      simpa [RationalSeparation.rationalRow,Height] using And.intro (hA i j) hH

theorem trajectory_heights {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (K l k:ℕ) (hk:k≤ K):
    (∀ i j,Height ((trajectory A b k).1 i j) (2 ^ stateBits n K l))∧
      (∀ i,Height ((trajectory A b k).2 i) (2 ^ stateBits n K l)):=by
  have heq:=trajectory_eq_sequences A b k
  have hnorm:=fun t => selectedNormal_norm A b (trajectory A b t).2 (by omega:0 < n)
  constructor
  · intro i j
    apply height_of_encoding
    rw [heq.1]
    exact (shapes_encoding_size n hn (normalSchedule A b) hnorm k i j).trans (by unfold stateBits; omega)
  · intro i
    apply height_of_encoding
    rw [heq.2]
    exact (centers_encoding_size n hn (normalSchedule A b) hnorm k i).trans (by unfold stateBits; omega)

theorem trajectory_posDef {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (k:ℕ):(EllipsoidRounding.realShape (trajectory A b k).1).PosDef:=by
  rw [(trajectory_eq_sequences A b k).1]
  exact (shapes_invariant n hn (normalSchedule A b)
    (fun t => selectedNormal_norm A b (trajectory A b t).2 (by omega)) k).1

theorem selectedNormal_ne_zero {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (c:Fin n→ ℚ) (hn:0 < n):selectedNormal A b c ≠ 0:=by
  intro heq
  have h:=selectedNormal_norm A b c hn
  rw [heq] at h
  have hz:realVector (0:Fin n→ ℚ)=0:=by funext j; simp [realVector]
  rw [hz,dotProduct_zero] at h
  norm_num at h

theorem trajectory_advance_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (K l k w:ℕ) (hk:k≤ K) (hA:∀ i j, (A i j).natAbs≤ 2 ^ l)
    (hw:wordWidth n (stateBits n K l) K≤ w):
    Spec (2 ^ w) (fun σ => Represents "ell.shape" (flatten (trajectory A b k).1) σ∧
        Represents "ell.normal" (List.ofFn (selectedNormal A b (trajectory A b k).2)) σ∧
        Represents "ell.center" (List.ofFn (trajectory A b k).2) σ∧ Workspace n σ∧
        σ.vars "vec.n"=n∧ σ.vars "iter.k"=k)
      advanceState
      (fun _ τ => Represents "ell.center" (List.ofFn (trajectory A b (k + 1)).2) τ∧
        Represents "ell.shape" (flatten (trajectory A b (k + 1)).1) τ∧
        Workspace n τ∧ τ.vars "vec.n"=n∧ τ.vars "iter.k"=k + 1)
      (stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
        71 * n + 71 * (n * n) + 60):=by
  let h:=stateBits n K l
  have hH:1≤ 2 ^ h:=Nat.one_le_pow _ _ (by decide)
  have hstate:=trajectory_heights A b hn K l k hk
  have hnormal:∀ j,Height (selectedNormal A b (trajectory A b k).2 j) (2 ^ h):=by
    intro j
    apply height_mono _ (selectedNormal_height A b _ (2 ^ l) (Nat.one_le_pow _ _ (by decide)) hA j)
    apply Nat.pow_le_pow_right (by decide)
    unfold h stateBits
    omega
  have hq:=form_pos_of_posDef (trajectory A b k).1 (selectedNormal A b (trajectory A b k).2)
    (trajectory_posDef A b hn k) (selectedNormal_ne_zero A b _ (by omega))
  have hparams:=magnitude_parameters n h K
  have hD:2 ^ (2 * k + 3 * n + 9)≤ 2 ^ magnitudeExponent n h K:=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hparams.2.2.1
  have hs:=advanceState_spec (2 ^ w) n (2 ^ h) (2 ^ magnitudeExponent n h K) k
    (trajectory A b k).1 (selectedNormal A b (trajectory A b k).2) (trajectory A b k).2
    hn hH hstate.1 hnormal hstate.2 hq hparams.1 hparams.2.1 hD hparams.2.2.2
    (wordWidth_sufficient n h K w hw)
  apply hs.post
  rintro σ τ _ ⟨hc,hshape,hw',hn',hk'⟩
  refine ⟨?_, ?_,hw',hn',hk'⟩
  · simpa only [trajectory,nextState,cacheState_eq,EllipsoidPrecision.gridDenominator,
      show (2 * k + 2) + (2 * n + 4) + n + 3=2 * k + 3 * n + 9 by omega] using hc
  · simpa only [trajectory,nextState,cacheState_eq,EllipsoidPrecision.gridDenominator,
      show (2 * k + 2) + (2 * n + 4) + n + 3=2 * k + 3 * n + 9 by omega] using hshape

end Lax109476Proofs.RamTrajectoryBounds

end

section

namespace Lax109476Proofs.RamNormalSelection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamZeroArray
open RamEllipsoidStep RamAdvanceState RamMatrixRows EllipsoidSearch

theorem fallback_values (n:ℕ):
    (List.replicate n (0:ℚ)).set 0 1=List.ofFn (EllipsoidSearch.fallbackNormal n):=by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_set]
    simp [EllipsoidSearch.fallbackNormal,List.getElem_replicate,eq_comm]

theorem fallbackNormal_spec (B n:ℕ) (hn:0 < n) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => Extents "ell.normal" n σ∧ σ.vars "vec.n"=n)
      fallbackNormal
      (fun _ τ => Represents "ell.normal" (List.ofFn (EllipsoidSearch.fallbackNormal n)) τ∧
        τ.vars "vec.n"=n) (33 * n + 39):=by
  have hz:=zeroRationalArray_spec B n "ell.normal" hnB h1
  have hs:=spec_with_write_frame ["vec.n"]
    (storeReduced_spec B "ell.normal" (List.replicate n 0) 1 0 (by simpa using hn) h1
      (by omega) (by simpa using h1) (by simpa using h1)) (by decide)
  rintro σ ⟨hσExt,hσn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 (Nat.mul ((33:Nat)) n); let c2:Nat:=c1 ((18:Nat)); let c3:List Rat:= @List.replicate Rat n (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c4:Env→ Prop:=Represents "ell.normal" c3; let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.normal"; let c6:String:=c5 ".s"; let c7:String:=c5 ".n"; let c8:String:=c5 ".d"; let c9:Env→ Prop:=fun (σ':Env) => And (Run B (zeroRationalArray "ell.normal") σ σ' c2) (And (c4 σ') (And (@Eq Nat (Env.vars σ' "vec.n") n) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (Env.arrs σ b)))); let c10:Nat:=c1 ((39:Nat)); let c11:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n (EllipsoidSearch.fallbackNormal n)); let c12:Env→ Prop:=(fun (x τ:Env) => And (c11 τ) (@Eq Nat (Env.vars τ "vec.n") n)) σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B fallbackNormal σ σ' c10) (c12 σ'); let c14:Prop:= @Exists Env c13; let c15:Env→ Prop:=Represents "ell.normal" (@List.set Rat c3 ((0:Nat)) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.lit ((0:Nat)))); let c18:Nat→ Nat:=c0 c17; let c19:Nat:=c16 (Expr.size (Expr.lit ((1:Nat)))); let c20:Nat→ Nat:=c0 c19; let c21:Nat:=c20 ((13:Nat)); let c22:Nat:=c20 c21; let c23:Nat:=c18 c22; let c24:Nat:=c18 c23; let c25:Com:=Com.assign "vec.i" (Expr.lit ((0:Nat))); let c26:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c27:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c28:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c29:Com:=Com.seq c28 (storeReduced "ell.normal"); let c30:Com:=Com.seq c27 c29; let c31:Com:=Com.seq c26 c30; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c14) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c6)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c7)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c8)) n) (@Eq Nat (Env.vars σ_1 "vec.n") n)))) (zeroRationalArray "ell.normal") (fun (σ_1 τ:Env) => And (c4 τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) c2 hz σ ?_) fun (w:Env) (h:And (Run B (zeroRationalArray "ell.normal") σ w c2) (And (c4 w) (And (@Eq Nat (Env.vars w "vec.n") n) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (Env.arrs σ b))))) => let c0_1:Prop:=Run B (zeroRationalArray "ell.normal") σ w c2; let c1_1:Prop:=And (c4 w) (And (@Eq Nat (Env.vars w "vec.n") n) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (Env.arrs σ b))); let c2_1:Env:=Env.setVar w "vec.i" ((0:Nat)); let c3_1:Env:=Env.setVar c2_1 "rat.s" ((0:Nat)); let c4_1:Env:=Env.setVar c3_1 "rat.n" ((1:Nat)); let c5_1:Env:=Env.setVar c4_1 "rat.d" ((1:Nat)); let c6_1:Env→ Nat→ Prop:=Run B (storeReduced "ell.normal") c5_1; let c7_1:Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.nil String)) c5_1; let c8_1:Env→ Prop:=fun (σ':Env) => And (c6_1 σ' ((13:Nat))) (And (c15 σ') (And (c7_1 σ') (∀ a∉ Com.warrs (storeReduced "ell.normal"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c5_1 a)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c14) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c8_1 (fun (x:@Exists Env c8_1) => c14) (RunStep.use B (fun (σ_1:Env) => And (c4 σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") ((0:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) σ_1))) (storeReduced "ell.normal") (fun (σ_1 τ:Env) => And (c15 τ) (And (FieldsAgree (@List.cons String "vec.n" (@List.nil String)) σ_1 τ) (∀ a∉ Com.warrs (storeReduced "ell.normal"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hs c5_1 ?_) fun (w_1:Env) (h_1:And (c6_1 w_1 ((13:Nat))) (And (c15 w_1) (And (c7_1 w_1) (∀ a∉ Com.warrs (storeReduced "ell.normal"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs c5_1 a))))) => let c0_2:Prop:=c6_1 w_1 ((13:Nat)); let c1_2:Prop:=And (c15 w_1) (And (c7_1 w_1) (∀ a∉ Com.warrs (storeReduced "ell.normal"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs c5_1 a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c14) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c13 w_1 (@And.intro (Run B fallbackNormal σ w_1 c10) (c12 w_1) (RunStep.mono B fallbackNormal σ w_1 (c0 c2 c24) c10 (RunStep.seq B (zeroRationalArray "ell.normal") (Com.seq c25 c31) σ w w_1 c2 c24 left (RunStep.seq B c25 c31 w c2_1 w_1 c17 c23 (RunStep.assign B w "vec.i" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) w (?nAX_g4592_0_0_0))) (RunStep.seq B c26 c30 c2_1 c3_1 w_1 c17 c22 (RunStep.assign B c2_1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2_1 (?nAX_g4592_0_0_1))) (RunStep.seq B c27 c29 c3_1 c4_1 w_1 c19 c21 (RunStep.assign B c3_1 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3_1 h1)) (RunStep.seq B c28 (storeReduced "ell.normal") c4_1 c5_1 w_1 c19 ((13:Nat)) (RunStep.assign B c4_1 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4_1 h1)) left_1))))) (?nAX_g4592_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4592_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4592_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4592_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hz hs
  all_goals simp_all [Extents,Represents,FieldsAgree,FractionOutput,fractionValue,fallback_values]
  all_goals first | omega | (exfalso; omega) | aesop

theorem copySelectedRow_spec (B m n H:ℕ) (a:String)
    (A:Matrix (Fin m) (Fin n) ℚ) (i:Fin m) (h1:1 < B)
    (hdims:m + n + m * n + 1 < B) (hHB:H < B)
    (hA:∀ j,Height (A i j) H) (ha:RamCopy.Disjoint a "ell.normal"):
    Spec B (fun σ => MatrixRows a A σ∧ Extents "ell.normal" n σ∧
        σ.vars "vec.n"=n∧ σ.vars "row.first"=i.val)
      (copySelectedRow a)
      (fun _ τ => Represents "ell.normal" (List.ofFn (A i)) τ∧ τ.vars "vec.n"=n)
      (77 * n + 28):=by
  have hib:i.val < B:=by have:=i.isLt; omega
  have hnB:n < B:=by omega
  have hbase:i.val * n + n≤ m * n:=by
    calc
      i.val * n + n=(i.val + 1) * n:=by ring
      _≤ m * n:=Nat.mul_le_mul_right n i.isLt
  have hbaseB:i.val * n + n < B:=by omega
  have hc:=RamRowCopy.copyRow_spec B n H (i.val * n) a "ell.normal" (A i) h1 hbaseB hHB hA ha
  rintro σ ⟨hσrows,hσExt,hσn,hσi⟩
  have hrow:=hσrows i
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "row.first") (Env.vars σ "vec.n"); let c2:Env:=Env.setVar σ "row.base" c1; let c3:Env→ Nat→ Prop:=Run B (RamRowCopy.copyRow a "ell.normal") c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 (c0 ((77:Nat)) n); let c6:Nat:=c5 ((24:Nat)); let c7:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n (A i)); let c8:Nat:=c0 (@Fin.val m i) n; let c9:Env→ Prop:=Slice a (@List.ofFn Rat n (A i)) c8; let c10:Env→ Prop:=fun (σ':Env) => And (c3 σ' c6) (And (c7 σ') (And (c9 σ') (And (@Eq Nat (Env.vars σ' "vec.n") n) (@Eq Nat (Env.vars σ' "row.base") c8)))); let c11:Nat:=c5 ((28:Nat)); let c12:Env→ Prop:=(fun (x τ:Env) => And (c7 τ) (@Eq Nat (Env.vars τ "vec.n") n)) σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B (copySelectedRow a) σ σ' c11) (c12 σ'); let c14:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.normal"; let c15:String:=c14 ".s"; let c16:String:=c14 ".n"; let c17:String:=c14 ".d"; let c18:String→ List Nat:=Env.arrs c2; let c19:String→ Nat:=Env.vars c2; let c20:Nat:=c4 ((1:Nat)) (Expr.size (Expr.mul (Expr.var "row.first") (Expr.var "vec.n"))); @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => @Exists Env c13) (RunStep.use B (fun (σ_1:Env) => And (c9 σ_1) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c15)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c16)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c17)) n) (And (@Eq Nat (Env.vars σ_1 "vec.n") n) (@Eq Nat (Env.vars σ_1 "row.base") c8)))))) (RamRowCopy.copyRow a "ell.normal") (fun (x τ:Env) => And (c7 τ) (And (c9 τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (@Eq Nat (Env.vars τ "row.base") c8)))) c6 hc c2 ?_) fun (w:Env) (h:And (c3 w c6) (And (c7 w) (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") n) (@Eq Nat (Env.vars w "row.base") c8))))) => let c0_1:Prop:=And (c7 w) (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") n) (@Eq Nat (Env.vars w "row.base") c8))); @And.casesOn (c3 w c6) c0_1 (fun (x:And (c3 w c6) c0_1) => @Exists Env c13) h fun (left:c3 w c6) (right:c0_1) => @Exists.intro Env c13 w (@And.intro (Run B (copySelectedRow a) σ w c11) (c12 w) (RunStep.mono B (copySelectedRow a) σ w (c4 c20 c6) c11 (RunStep.seq B (Com.assign "row.base" (Expr.mul (Expr.var "row.first") (Expr.var "vec.n"))) (RamRowCopy.copyRow a "ell.normal") σ c2 w c20 c6 (RunStep.assign B σ "row.base" (Expr.mul (Expr.var "row.first") (Expr.var "vec.n")) c1 (RunStep.eval_mul B σ (Expr.var "row.first") (Expr.var "vec.n") (Env.vars σ "row.first") (Env.vars σ "vec.n") (RunStep.eval_var B σ "row.first" (?nAX_g4594_0_0_0)) (RunStep.eval_var B σ "vec.n" (?nAX_g4594_0_0_1)) ?_)) left) (?nAX_g4594_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4594_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4594_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4594_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hc
  all_goals simp_all [Extents,Slice]
  all_goals first | omega | (exfalso; omega) | aesop

theorem ensureNormal_spec (B n H:ℕ) (v:Fin n→ ℚ) (hn:0 < n) (hnB:n < B)
    (h1:1 < B) (hHB:H < B) (hv:∀ i,Height (v i) H):
    Spec B (fun σ => Represents "ell.normal" (List.ofFn v) σ∧ σ.vars "vec.n"=n)
      ensureNormal
      (fun _ τ => Represents "ell.normal"
          (List.ofFn (if v=0 then EllipsoidSearch.fallbackNormal n else v)) τ∧ τ.vars "vec.n"=n)
      (49 * n + 51):=by
  rintro σ ⟨hσv,hσn⟩
  obtain ⟨τ,hr₁,hflag,hiff,hτv,hτn⟩:=RamNonzero.scan_spec B n H "ell.normal" v
    hnB h1 hHB hv σ ⟨hσv,hσn⟩
  have hflagB:τ.vars "nonzero.flag" < B:=hflag.trans_lt h1
  have h0:0 < B:=by omega
  by_cases hvzero:v=0
  · have hflag0:τ.vars "nonzero.flag"=0:=by
      have hnot:τ.vars "nonzero.flag" ≠ 1:=fun hf => (hiff.mp hf) hvzero
      omega
    have hτExt:Extents "ell.normal" n τ:=by simpa using represents_extents _ _ _ hτv
    obtain ⟨υ,hr₂,hυv,hυn⟩:=fallbackNormal_spec B n hn hnB h1 τ ⟨hτExt,hτn⟩
    have hb:(Cond.eq (.var "nonzero.flag") (.lit 0)).evalB B τ=some true:=by
      simpa [hflag0] using (evalB_condEq (evalB_var hflagB) (evalB_lit h0))
    refine ⟨υ, (hr₁.seq (Run.ite_true hb hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_,hυn⟩
    simpa only [if_pos hvzero] using hυv
  · have hflag1:τ.vars "nonzero.flag"=1:=hiff.mpr hvzero
    have hb:(Cond.eq (.var "nonzero.flag") (.lit 0)).evalB B τ=some false:=by
      simpa [hflag1] using (evalB_condEq (evalB_var hflagB) (evalB_lit h0))
    refine ⟨τ, (hr₁.seq (Run.ite_false hb Run.skip)).mono (by simp only [Cond.size,Expr.size]; omega), ?_,hτn⟩
    simpa only [if_neg hvzero] using hτv

theorem selectNormal_integer_spec (B m n H:ℕ) (a:String)
    (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ) (c:Fin n→ ℚ)
    (hn:0 < n) (h1:1 < B) (hdims:m + n + m * n + 1 < B)
    (hH:1≤ H) (hHB:H < B) (hA:∀ i j, (A i j).natAbs≤ H)
    (ha:RamCopy.Disjoint a "ell.normal"):
    Spec B (fun σ => MatrixRows a (fun i j => (A i j:ℚ)) σ∧ Extents "ell.normal" n σ∧
        σ.vars "vec.n"=n∧ σ.vars "row.m"=m∧ σ.vars "row.first" =
          ((RationalSeparation.firstViolation A b c).map Fin.val).getD m)
      (selectNormal a)
      (fun _ τ => Represents "ell.normal" (List.ofFn (EllipsoidSearch.selectedNormal A b c)) τ∧
        τ.vars "vec.n"=n) (126 * n + 83):=by
  have hnB:n < B:=by omega
  have hmB:m < B:=by omega
  have hfall:=fallbackNormal_spec B n hn hnB h1
  rintro σ ⟨hσrows,hσExt,hσn,hσm,hσfirst⟩
  cases hf:RationalSeparation.firstViolation A b c with
  | none =>
    simp only [hf,Option.map_none,Option.getD_none] at hσfirst
    obtain ⟨τ,hr,hτ,hτn⟩:=hfall σ ⟨hσExt,hσn⟩
    have hb:(Cond.lt (.var "row.first") (.var "row.m")).evalB B σ=some false:=by
      simpa [hσfirst,hσm] using
        (evalB_condLt (evalB_var (by omega:σ.vars "row.first" < B))
          (evalB_var (by omega:σ.vars "row.m" < B)))
    refine ⟨τ, (Run.ite_false hb hr).mono (by simp only [Cond.size,Expr.size]; omega), ?_,hτn⟩
    simpa only [EllipsoidSearch.selectedNormal,hf] using hτ
  | some i =>
    simp only [hf,Option.map_some,Option.getD_some] at hσfirst
    have hib:i.val < B:=i.isLt.trans hmB
    have hrow:∀ j,Height (A i j:ℚ) H:=by
      intro j
      simpa [Height] using And.intro (hA i j) hH
    have hc:=copySelectedRow_spec B m n H a (fun i j => (A i j:ℚ)) i h1 hdims hHB hrow ha
    have he:=ensureNormal_spec B n H (fun j => (A i j:ℚ)) hn hnB h1 hHB hrow
    have hrowzero:(fun j => (A i j:ℚ))=(0:Fin n→ ℚ)↔ A i=0:=by
      simp only [funext_iff,Pi.zero_apply]
      constructor
      · intro h j
        exact_mod_cast h j
      · intro h j
        exact_mod_cast h j
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "row.first") (Env.vars σ "row.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat:=c2 (c3 ((126:Nat)) n) ((83:Nat)); let c5:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n (@selectedNormal m n A b c)); let c6:Env→ Prop:=(fun (x τ:Env) => And (c5 τ) (@Eq Nat (Env.vars τ "vec.n") n)) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B (selectNormal a) σ σ' c4) (c6 σ'); let c8:Nat:=c2 (c3 ((77:Nat)) n) ((28:Nat)); let c9:Fin n→ Rat:=fun (j:Fin n) => @Int.cast Rat Rat.instIntCast (A i j); let c10:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n c9); let c11:Env→ Prop:=fun (σ':Env) => And (Run B (copySelectedRow a) σ σ' c8) (And (c10 σ') (@Eq Nat (Env.vars σ' "vec.n") n)); let c12:Env→ Prop:= @MatrixRows m n a fun (i_1:Fin m) (j:Fin n) => @Int.cast Rat Rat.instIntCast (A i_1 j); let c13:Env→ Prop:=fun (τ:Env) => And (c10 τ) (@Eq Nat (Env.vars τ "vec.n") n); let c14:Nat:=c2 (c3 ((49:Nat)) n) ((51:Nat)); let c15:Fin n→ Rat:= @OfNat.ofNat (Fin n→ Rat) (nat_lit 0) (@Zero.toOfNat0 (Fin n→ Rat) (@Pi.instZero (Fin n) (fun (a_1:Fin n) => Rat) fun (i_1:Fin n) => @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))); let c16:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n (@ite (Fin n→ Rat) (@Eq (Fin n→ Rat) c9 c15) (@Fintype.decidablePiFintype (Fin n) (fun (a_1:Fin n) => Rat) (fun (a_1:Fin n) => instDecidableEqRat) (Fin.fintype n) c9 c15) (EllipsoidSearch.fallbackNormal n) c9)); let c17:Nat→ Nat:=c2 (c2 ((1:Nat)) (Cond.size (Cond.lt (Expr.var "row.first") (Expr.var "row.m")))); let c18:Nat:=c2 c8 c14; let c19:Nat:=c2 (c3 ((33:Nat)) n) ((39:Nat)); let c20:Env→ Prop:=Represents "ell.normal" (@List.ofFn Rat n (EllipsoidSearch.fallbackNormal n)); let c21:Env→ Prop:=fun (σ':Env) => And (Run B fallbackNormal σ σ' c19) (And (c20 σ') (@Eq Nat (Env.vars σ' "vec.n") n)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c7) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => @Exists Env c7) (RunStep.use B (fun (σ_1:Env) => And (c12 σ_1) (And (Extents "ell.normal" n σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.n") n) (@Eq Nat (Env.vars σ_1 "row.first") (@Fin.val m i))))) (copySelectedRow a) (fun (x:Env) => c13) c8 hc σ ?_) fun (w:Env) (h:And (Run B (copySelectedRow a) σ w c8) (And (c10 w) (@Eq Nat (Env.vars w "vec.n") n))) => let c0_1:Prop:=Run B (copySelectedRow a) σ w c8; let c1_1:Prop:=And (c10 w) (@Eq Nat (Env.vars w "vec.n") n); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B ensureNormal w σ' c14) (And (c16 σ') (@Eq Nat (Env.vars σ' "vec.n") n)); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c7) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c7) (RunStep.use B c13 ensureNormal (fun (x τ:Env) => And (c16 τ) (@Eq Nat (Env.vars τ "vec.n") n)) c14 he w ?_) fun (w_1:Env) (h_1:And (Run B ensureNormal w w_1 c14) (And (c16 w_1) (@Eq Nat (Env.vars w_1 "vec.n") n))) => let c0_2:Prop:=And (c16 w_1) (@Eq Nat (Env.vars w_1 "vec.n") n); @And.casesOn (Run B ensureNormal w w_1 c14) c0_2 (fun (x:And (Run B ensureNormal w w_1 c14) c0_2) => @Exists Env c7) h_1 fun (left_1:Run B ensureNormal w w_1 c14) (right_1:c0_2) => @Exists.intro Env c7 w_1 (@And.intro (Run B (selectNormal a) σ w_1 c4) (c6 w_1) (RunStep.mono B (selectNormal a) σ w_1 (c17 c18) c4 (RunStep.ite_true B (Cond.lt (Expr.var "row.first") (Expr.var "row.m")) (Com.seq (copySelectedRow a) ensureNormal) fallbackNormal σ w_1 c18 (RunStep.cond_lt_true B σ (Expr.var "row.first") (Expr.var "row.m") (Env.vars σ "row.first") (Env.vars σ "row.m") (RunStep.eval_var B σ "row.first" (?nAX_g4598_0_0_0)) (RunStep.eval_var B σ "row.m" (?nAX_g4598_0_0_1)) hcase) (RunStep.seq B (copySelectedRow a) ensureNormal σ w w_1 c8 c14 left left_1)) (?nAX_g4598_0_0_2)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c21 (fun (x:@Exists Env c21) => @Exists Env c7) (RunStep.use B (fun (σ_1:Env) => And (Extents "ell.normal" n σ_1) (@Eq Nat (Env.vars σ_1 "vec.n") n)) fallbackNormal (fun (x τ:Env) => And (c20 τ) (@Eq Nat (Env.vars τ "vec.n") n)) c19 hfall σ ?_) fun (w:Env) (h:And (Run B fallbackNormal σ w c19) (And (c20 w) (@Eq Nat (Env.vars w "vec.n") n))) => let c0_1:Prop:=And (c20 w) (@Eq Nat (Env.vars w "vec.n") n); @And.casesOn (Run B fallbackNormal σ w c19) c0_1 (fun (x:And (Run B fallbackNormal σ w c19) c0_1) => @Exists Env c7) h fun (left:Run B fallbackNormal σ w c19) (right:c0_1) => @Exists.intro Env c7 w (@And.intro (Run B (selectNormal a) σ w c4) (c6 w) (RunStep.mono B (selectNormal a) σ w (c17 c19) c4 (RunStep.ite_false B (Cond.lt (Expr.var "row.first") (Expr.var "row.m")) (Com.seq (copySelectedRow a) ensureNormal) fallbackNormal σ w c19 (RunStep.cond_lt_false B σ (Expr.var "row.first") (Expr.var "row.m") (Env.vars σ "row.first") (Env.vars σ "row.m") (RunStep.eval_var B σ "row.first" (?nAX_g4598_0_0_3)) (RunStep.eval_var B σ "row.m" (?nAX_g4598_0_0_4)) hcase) left) (?nAX_g4598_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4598_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4598_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4598_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4598_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4598_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4598_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals clear hc he hfall
    all_goals simp_all [EllipsoidSearch.selectedNormal,RationalSeparation.rationalRow,Extents,hrowzero]
    all_goals aesop

end Lax109476Proofs.RamNormalSelection

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamSeparation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RamComparison RationalArithmeticBounds

set_option maxHeartbeats 0 in
theorem compareRowRhs_spec (B M i n:ℕ) (a:String) (bs:List ℚ) (q:ℚ)
    (hi:i < bs.length) (hiB:i < B) (hnB:n < B)
    (hB:2 * M ^ 2 + 3 < B) (hq:Height q M) (hb:Height bs[i] M):
    Spec B (fun σ => DotOutput q σ∧ Represents a bs σ∧
        σ.vars "row.i"=i∧ σ.vars "vec.n"=n)
      (compareRowRhs a)
      (fun σ τ => τ.vars "cmp.le" ≤ 1∧ (τ.vars "cmp.le"=1↔ q≤ bs[i])∧
        τ.vars "vec.i"=n∧ τ.arrs=σ.arrs) 59:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hqσ,hσb,hσi,hσn⟩
  have hqval:=hqσ.1
  have hqnum:=hqσ.2.1
  have hqden:=hqσ.2.2.1
  have hqs:=hqσ.2.2.2.trans_lt h1
  have hqn:=hq.1.trans_lt hM
  have hqd:=hq.2.trans_lt hM
  have hload:=loadRight_frame_spec B a bs i hi h1 hiB
    (hb.1.trans_lt hM) (hb.2.trans_lt hM)
  have hcmp:=compareFraction_spec B M (σ.vars "dot.s") q.num.natAbs q.den
    (rationalSign bs[i]) bs[i].num.natAbs bs[i].den hB hqσ.2.2.2
    (rationalSign_le_one _) hq.1 hq.2 hb.1 hb.2 q.den_pos bs[i].den_pos
  have hcframe:=spec_with_fields ["vec.n"] hcmp
    (by intro x hx; simp at hx; subst x; simp [compareFraction,Com.wvars])
    (by simp [compareFraction,Com.warrs])
  clear hcmp
  have hlframe:=spec_with_fields ["vec.n"] hload
    (by intro x hx; simp at hx; subst x; simp [loadRight,Com.wvars])
    (by simp [loadRight,Com.warrs])
  clear hload
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "dot.s")) "dot.n"; let c1:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "dot.s")) "left.n" c0; let c2:Nat:=Env.vars c1 "dot.d"; let c3:Env:=Env.setVar c1 "left.d" c2; let c4:Nat:=Env.vars c3 "row.i"; let c5:Env:=Env.setVar c3 "vec.i" c4; let c6:Env→ Nat→ Prop:=Run B (loadRight a) c5; let c7:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) bs i hi; let c8:Env→ Prop:=RightOutput c7; let c9:String→ List Nat:=Env.arrs c5; let c10:String→ Nat:=Env.vars c5; let c11:Nat:=c10 "left.s"; let c12:Nat:=c10 "left.n"; let c13:Nat:=c10 "left.d"; let c14:Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.nil String)) c5; let c15:Env→ Prop:=fun (σ':Env) => let c0_1:Prop:= @Eq (String→ List Nat) (Env.arrs σ') c9; And (c6 σ' ((9:Nat))) (And (And (c8 σ') (And (@Eq Nat (Env.vars σ' "vec.i") i) (And c0_1 (And (@Eq Nat (Env.vars σ' "left.s") c11) (And (@Eq Nat (Env.vars σ' "left.n") c12) (@Eq Nat (Env.vars σ' "left.d") c13)))))) (And (c14 σ') c0_1)); let c16:Prop:= @LE.le Rat Rat.instLE q c7; let c17:Env→ Prop:=(fun (σ_1 τ:Env) => And (Nat.le (Env.vars τ "cmp.le") ((1:Nat))) (And (Iff (@Eq Nat (Env.vars τ "cmp.le") ((1:Nat))) c16) (And (@Eq Nat (Env.vars τ "vec.i") n) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))))) σ; let c18:Env→ Prop:=fun (σ':Env) => And (Run B (compareRowRhs a) σ σ' ((59:Nat))) (c17 σ'); let c19:Nat:=rationalSign c7; let c20:Nat:=Int.natAbs (Rat.num c7); let c21:Nat:=Rat.den c7; let c22:Prop:= @LE.le Rat Rat.instLE (fractionValue (Env.vars σ "dot.s") (Int.natAbs (Rat.num q)) (Rat.den q)) (fractionValue c19 c20 c21); let c23:Env→ Prop:=fractionInputs (Env.vars σ "dot.s") (Int.natAbs (Rat.num q)) (Rat.den q) c19 c20 c21; let c24:Nat→ Nat→ Nat:=Nat.add; let c25:Nat→ Nat:=c24 ((1:Nat)); let c26:Nat:=c25 (Expr.size (Expr.var "dot.s")); let c27:Nat:=c25 (Expr.size (Expr.var "dot.n")); let c28:Nat:=c25 (Expr.size (Expr.var "dot.d")); let c29:Nat:=c25 (Expr.size (Expr.var "row.i")); let c30:Nat:=c25 (Expr.size (Expr.var "vec.n")); let c31:Nat:=c24 ((40:Nat)) c30; let c32:Nat:=c24 ((9:Nat)) c31; let c33:Nat:=c24 c29 c32; let c34:Nat:=c24 c28 c33; let c35:Nat:=c24 c27 c34; let c36:Com:=Com.seq (loadRight a) (Com.seq compareFraction (Com.assign "vec.i" (Expr.var "vec.n"))); let c37:Com:=Com.seq (Com.assign "vec.i" (Expr.var "row.i")) c36; let c38:Com:=Com.seq (Com.assign "left.d" (Expr.var "dot.d")) c37; @Exists.casesOn Env c15 (fun (x:@Exists Env c15) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (Represents a bs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadRight a) (fun (σ_1 τ:Env) => let c0_1:Prop:= @Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1); And (And (c8 τ) (And (@Eq Nat (Env.vars τ "vec.i") i) (And c0_1 (And (@Eq Nat (Env.vars τ "left.s") (Env.vars σ_1 "left.s")) (And (@Eq Nat (Env.vars τ "left.n") (Env.vars σ_1 "left.n")) (@Eq Nat (Env.vars τ "left.d") (Env.vars σ_1 "left.d"))))))) (And (FieldsAgree (@List.cons String "vec.n" (@List.nil String)) σ_1 τ) c0_1)) ((9:Nat)) hlframe c5 ?_) fun (w:Env) (h:And (c6 w ((9:Nat))) (And (And (c8 w) (And (@Eq Nat (Env.vars w "vec.i") i) (And (@Eq (String→ List Nat) (Env.arrs w) c9) (And (@Eq Nat (Env.vars w "left.s") c11) (And (@Eq Nat (Env.vars w "left.n") c12) (@Eq Nat (Env.vars w "left.d") c13)))))) (And (c14 w) (@Eq (String→ List Nat) (Env.arrs w) c9)))) => let c0_1:Prop:=c6 w ((9:Nat)); let c1_1:Prop:= @Eq (String→ List Nat) (Env.arrs w) c9; let c2_1:Prop:=And (And (c8 w) (And (@Eq Nat (Env.vars w "vec.i") i) (And c1_1 (And (@Eq Nat (Env.vars w "left.s") c11) (And (@Eq Nat (Env.vars w "left.n") c12) (@Eq Nat (Env.vars w "left.d") c13)))))) (And (c14 w) c1_1); let c3_1:Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.nil String)) w; let c4_1:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction w σ' ((40:Nat))) (And (And (Nat.le (Env.vars σ' "cmp.le") ((1:Nat))) (Iff (@Eq Nat (Env.vars σ' "cmp.le") ((1:Nat))) c22)) (And (c3_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c2_1 (fun (x:And c0_1 c2_1) => @Exists Env c18) h fun (left:c0_1) (right:c2_1) => @Exists.casesOn Env c4_1 (fun (x:@Exists Env c4_1) => @Exists Env c18) (RunStep.use B c23 compareFraction (fun (σ_1 τ:Env) => And (And (Nat.le (Env.vars τ "cmp.le") ((1:Nat))) (Iff (@Eq Nat (Env.vars τ "cmp.le") ((1:Nat))) c22)) (And (FieldsAgree (@List.cons String "vec.n" (@List.nil String)) σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((40:Nat)) hcframe w ?_) fun (w_1:Env) (h_1:And (Run B compareFraction w w_1 ((40:Nat))) (And (And (Nat.le (Env.vars w_1 "cmp.le") ((1:Nat))) (Iff (@Eq Nat (Env.vars w_1 "cmp.le") ((1:Nat))) c22)) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B compareFraction w w_1 ((40:Nat)); let c1_2:Prop:=And (And (Nat.le (Env.vars w_1 "cmp.le") ((1:Nat))) (Iff (@Eq Nat (Env.vars w_1 "cmp.le") ((1:Nat))) c22)) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:String→ Nat:=Env.vars (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")); let c3_2:Nat:=c2_2 "cmp.le"; @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => @Exists Env c18) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c18 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) (@And.intro (Run B (compareRowRhs a) σ (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) ((59:Nat))) (c17 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n"))) (RunStep.mono B (compareRowRhs a) σ (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) (c24 c26 c35) ((59:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.var "dot.s")) (Com.seq (Com.assign "left.n" (Expr.var "dot.n")) c38) σ (Env.setVar σ "left.s" (Env.vars σ "dot.s")) (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) c26 c35 (RunStep.assign B σ "left.s" (Expr.var "dot.s") (Env.vars σ "dot.s") (RunStep.eval_var B σ "dot.s" hqs)) (RunStep.seq B (Com.assign "left.n" (Expr.var "dot.n")) c38 (Env.setVar σ "left.s" (Env.vars σ "dot.s")) c1 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) c27 c34 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "dot.s")) "left.n" (Expr.var "dot.n") c0 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "dot.s")) "dot.n" (?nAX_g4600_0_0_0))) (RunStep.seq B (Com.assign "left.d" (Expr.var "dot.d")) c37 c1 c3 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) c28 c33 (RunStep.assign B c1 "left.d" (Expr.var "dot.d") c2 (RunStep.eval_var B c1 "dot.d" (?nAX_g4600_0_0_1))) (RunStep.seq B (Com.assign "vec.i" (Expr.var "row.i")) c36 c3 c5 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) c29 c32 (RunStep.assign B c3 "vec.i" (Expr.var "row.i") c4 (RunStep.eval_var B c3 "row.i" (?nAX_g4600_0_0_2))) (RunStep.seq B (loadRight a) (Com.seq compareFraction (Com.assign "vec.i" (Expr.var "vec.n"))) c5 w (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) ((9:Nat)) c31 left (RunStep.seq B compareFraction (Com.assign "vec.i" (Expr.var "vec.n")) w w_1 (Env.setVar w_1 "vec.i" (Env.vars w_1 "vec.n")) ((40:Nat)) c30 left_1 (RunStep.assign B w_1 "vec.i" (Expr.var "vec.n") (Env.vars w_1 "vec.n") (RunStep.eval_var B w_1 "vec.n" ?_)))))))) (?nAX_g4600_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4600_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4600_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4600_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4600_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hlframe hcframe
  all_goals simp_all [DotOutput,Represents,fractionInputs,FieldsAgree,RightOutput,
    canonical_fractionValue]

theorem evaluateRow_spec (B m n H:ℕ) (a point rhs:String)
    (A:Matrix (Fin m) (Fin n) ℚ) (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hb:∀ k,Height (b k) H)
    (hc:∀ j,Height (c j) H) (hdims:m + n + m * n + 1 < B)
    (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows a A σ∧ Represents point (List.ofFn c) σ∧
        Represents rhs (List.ofFn b) σ∧ σ.vars "row.i"=i.val∧ σ.vars "vec.n"=n)
      (evaluateRow a point rhs)
      (fun σ τ => τ.vars "cmp.le" ≤ 1∧
        (τ.vars "cmp.le"=1↔ (∑ j,A i j * c j)≤ b i)∧ τ.arrs=σ.arrs)
      (4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 59):=by
  rintro σ ⟨hσA,hσc,hσb,hσi,hσn⟩
  have hrow:=spec_with_fields ["row.i", "vec.n"]
    (matrixRowDot_spec B m n H a point A c i hH hA hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
      simp [matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,loadRight,
        addToAccumulator,addFraction,multiplyFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
    (by simp [matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,loadRight,
        addToAccumulator,addFraction,multiplyFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  obtain ⟨τ,hr₁, ⟨hτq,hτa⟩,hτf,_⟩:=hrow σ ⟨hσA,hσc,hσi,hσn⟩
  have hτb:Represents rhs (List.ofFn b) τ:=by simpa only [Represents,hτa] using hσb
  have hτi:τ.vars "row.i"=i.val:=(hτf _ (by simp)).trans hσi
  have hτn:τ.vars "vec.n"=n:=(hτf _ (by simp)).trans hσn
  have hsum:Height (∑ j,A i j * c j) (cap n H):=by
    rw [← prefix_ofFn]
    apply prefix_height _ _ n H n hH (by simp) (by simp) le_rfl
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hA i j
    · intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq; exact hc j
  have hib:i.val < B:=by have:=i.isLt; omega
  have hnb:n < B:=by omega
  have hbi:Height (List.ofFn b)[i.val] (cap n H):=by
    simpa using height_mono _ (hb i) (cap_ge n H hH).2
  obtain ⟨υ,hr₂,hυflag,hυq,_,hυa⟩:=compareRowRhs_spec B (cap n H) i.val n rhs
    (List.ofFn b) (∑ j,A i j * c j) (by simp) hib hnb hB hsum hbi
    τ ⟨hτq,hτb,hτi,hτn⟩
  refine ⟨υ,hr₁.seq hr₂,hυflag, ?_,hυa.trans hτa⟩
  simpa using hυq

def foundBefore (p:ℕ→ Bool) (m k:ℕ):ℕ:=((List.range k).find? p).getD m

theorem foundBefore_zero (p:ℕ→ Bool) (m:ℕ):foundBefore p m 0=m:=by
  simp [foundBefore]

theorem foundBefore_le (p:ℕ→ Bool) (m k:ℕ) (hk:k≤ m):foundBefore p m k≤ m:=by
  unfold foundBefore
  cases hf:(List.range k).find? p with
  | none => simp
  | some j =>
    have hj:=List.mem_of_find?_eq_some hf
    simp only [List.mem_range] at hj
    simp only [Option.getD_some]
    omega

theorem foundBefore_succ (p:ℕ→ Bool) (m k:ℕ) (hk:k < m):
    foundBefore p m (k + 1) =
      if foundBefore p m k=m∧ p k=true then k else foundBefore p m k:=by
  unfold foundBefore
  rw [List.range_succ,List.find?_append]
  cases hf:(List.range k).find? p with
  | none => simp; split <;> simp_all
  | some j =>
    have hj:=List.mem_of_find?_eq_some hf
    simp only [List.mem_range] at hj
    have hne:j ≠ m:=by omega
    simp [hne]

def violationPred {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (b:Fin m→ ℚ)
    (c:Fin n→ ℚ) (k:ℕ):Bool:=
  if hk:k < m then decide (b ⟨k,hk⟩ < ∑ j,A ⟨k,hk⟩ j * c j) else false

theorem violationPred_val {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m):
    violationPred A b c i.val=decide (b i < ∑ j,A i j * c j):=by
  simp [violationPred,i.isLt]

theorem finRange_values (m:ℕ):(List.finRange m).map Fin.val=List.range m:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem foundBefore_integer {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ):
    foundBefore (violationPred (fun i j => (A i j:ℚ)) b c) m m =
      ((RationalSeparation.firstViolation A b c).map Fin.val).getD m:=by
  unfold foundBefore
  rw [← finRange_values,List.find?_map]
  congr 1
  congr 1
  unfold RationalSeparation.firstViolation
  congr 1
  funext i
  exact violationPred_val _ _ _ i

theorem recordViolation_spec (B flag first i m:ℕ) (hf:flag≤ 1) (hfirst:first≤ m)
    (hi:i < m) (hmB:m < B) (h1:1 < B):
    Spec B (fun σ => σ.vars "cmp.le"=flag∧ σ.vars "row.first"=first∧
        σ.vars "row.i"=i∧ σ.vars "row.m"=m)
      recordViolation
      (fun _ τ => τ.vars "row.first"=(if flag=0∧ first=m then i else first)∧
        τ.vars "row.i"=i + 1) 16:=by
  have hfB:=hf.trans_lt h1
  have hfirstB:=hfirst.trans_lt hmB
  have hiB:i < B:=hi.trans hmB
  have hi1B:i + 1 < B:=lt_of_le_of_lt (by omega) hmB
  rintro σ ⟨hσf,hσfirst,hσi,hσm⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "cmp.le") ((0:Nat)); let c1:Prop:=Not c0; let c2:Prop:= @Eq Nat flag ((0:Nat)); let c3:Nat:= @ite Nat (And c2 (@Eq Nat first m)) (@instDecidableAnd c2 (@Eq Nat first m) (instDecidableEqNat flag ((0:Nat))) (instDecidableEqNat first m)) i first; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 i ((1:Nat)); let c6:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.first") c3) (@Eq Nat (Env.vars τ "row.i") c5)) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B recordViolation σ σ' ((16:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Prop:= @Eq Nat (Env.vars σ "row.first") (Env.vars σ "row.m"); let c10:Prop:=Not c9; let c11:Nat:=Env.vars (Env.setVar σ "row.first" (Env.vars σ "row.i")) "row.i"; let c12:Nat:=c4 c11 ((1:Nat)); let c13:Env:=Env.setVar (Env.setVar σ "row.first" (Env.vars σ "row.i")) "row.i" c12; let c14:Nat→ Nat:=c4 ((1:Nat)); let c15:Cond:=Cond.eq (Expr.var "cmp.le") (Expr.lit ((0:Nat))); let c16:Nat→ Nat:=c4 (c14 (Cond.size c15)); let c17:Nat→ Nat:=c4 (c14 (Cond.size (Cond.eq (Expr.var "row.first") (Expr.var "row.m")))); let c18:Nat:=c14 (Expr.size (Expr.var "row.i")); let c19:Nat:=c17 c18; let c20:Nat:=c16 c19; let c21:Expr:=Expr.add (Expr.var "row.i") (Expr.lit ((1:Nat))); let c22:Nat:=c14 (Expr.size c21); let c23:Com:=Com.ite (Cond.eq (Expr.var "row.first") (Expr.var "row.m")) (Com.assign "row.first" (Expr.var "row.i")) Com.skip; let c24:String→ Nat:=Env.vars c13; let c25:Nat:=c4 (Env.vars σ "row.i") ((1:Nat)); let c26:Env:=Env.setVar σ "row.i" c25; let c27:Nat:=c17 ((1:Nat)); let c28:Nat:=c16 c27; let c29:String→ Nat:=Env.vars c26; let c30:Nat:=c16 ((1:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c8) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c9 c10 (fun (x:Or c9 c10) => c8) (Classical.em c9) (fun (hcase_1:c9) => @Exists.intro Env c7 c13 (@And.intro (Run B recordViolation σ c13 ((16:Nat))) (c6 c13) (RunStep.mono B recordViolation σ c13 (c4 c20 c22) ((16:Nat)) (RunStep.seq B (Com.ite c15 c23 Com.skip) (Com.assign "row.i" c21) σ (Env.setVar σ "row.first" (Env.vars σ "row.i")) c13 c20 c22 (RunStep.ite_true B c15 c23 Com.skip σ (Env.setVar σ "row.first" (Env.vars σ "row.i")) c19 (RunStep.cond_eq_true B σ (Expr.var "cmp.le") (Expr.lit ((0:Nat))) (Env.vars σ "cmp.le") ((0:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g4612_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4612_0_0_1)) hcase) (RunStep.ite_true B (Cond.eq (Expr.var "row.first") (Expr.var "row.m")) (Com.assign "row.first" (Expr.var "row.i")) Com.skip σ (Env.setVar σ "row.first" (Env.vars σ "row.i")) c18 (RunStep.cond_eq_true B σ (Expr.var "row.first") (Expr.var "row.m") (Env.vars σ "row.first") (Env.vars σ "row.m") (RunStep.eval_var B σ "row.first" (?nAX_g4612_0_0_2)) (RunStep.eval_var B σ "row.m" (?nAX_g4612_0_0_3)) hcase_1) (RunStep.assign B σ "row.first" (Expr.var "row.i") (Env.vars σ "row.i") (RunStep.eval_var B σ "row.i" (?nAX_g4612_0_0_4))))) (RunStep.assign B (Env.setVar σ "row.first" (Env.vars σ "row.i")) "row.i" c21 c12 (RunStep.eval_add B (Env.setVar σ "row.first" (Env.vars σ "row.i")) (Expr.var "row.i") (Expr.lit ((1:Nat))) c11 ((1:Nat)) (RunStep.eval_var B (Env.setVar σ "row.first" (Env.vars σ "row.i")) "row.i" (?nAX_g4612_0_0_5)) (RunStep.eval_lit B ((1:Nat)) (Env.setVar σ "row.first" (Env.vars σ "row.i")) h1) (?nAX_g4612_0_0_6)))) (?nAX_g4612_0_0_7)) ?_)) fun (hcase_1:c10) => @Exists.intro Env c7 c26 (@And.intro (Run B recordViolation σ c26 ((16:Nat))) (c6 c26) (RunStep.mono B recordViolation σ c26 (c4 c28 c22) ((16:Nat)) (RunStep.seq B (Com.ite c15 c23 Com.skip) (Com.assign "row.i" c21) σ σ c26 c28 c22 (RunStep.ite_true B c15 c23 Com.skip σ σ c27 (RunStep.cond_eq_true B σ (Expr.var "cmp.le") (Expr.lit ((0:Nat))) (Env.vars σ "cmp.le") ((0:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g4612_0_0_8)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4612_0_0_9)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "row.first") (Expr.var "row.m")) (Com.assign "row.first" (Expr.var "row.i")) Com.skip σ σ ((1:Nat)) (RunStep.cond_eq_false B σ (Expr.var "row.first") (Expr.var "row.m") (Env.vars σ "row.first") (Env.vars σ "row.m") (RunStep.eval_var B σ "row.first" (?nAX_g4612_0_0_10)) (RunStep.eval_var B σ "row.m" (?nAX_g4612_0_0_11)) hcase_1) (RunStep.skip B σ))) (RunStep.assign B σ "row.i" c21 c25 (RunStep.eval_add B σ (Expr.var "row.i") (Expr.lit ((1:Nat))) (Env.vars σ "row.i") ((1:Nat)) (RunStep.eval_var B σ "row.i" (?nAX_g4612_0_0_12)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g4612_0_0_13)))) (?nAX_g4612_0_0_14)) ?_)) fun (hcase:c1) => @Exists.intro Env c7 c26 (@And.intro (Run B recordViolation σ c26 ((16:Nat))) (c6 c26) (RunStep.mono B recordViolation σ c26 (c4 c30 c22) ((16:Nat)) (RunStep.seq B (Com.ite c15 c23 Com.skip) (Com.assign "row.i" c21) σ σ c26 c30 c22 (RunStep.ite_false B c15 c23 Com.skip σ σ ((1:Nat)) (RunStep.cond_eq_false B σ (Expr.var "cmp.le") (Expr.lit ((0:Nat))) (Env.vars σ "cmp.le") ((0:Nat)) (RunStep.eval_var B σ "cmp.le" (?nAX_g4612_0_0_15)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4612_0_0_16)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "row.i" c21 c25 (RunStep.eval_add B σ (Expr.var "row.i") (Expr.lit ((1:Nat))) (Env.vars σ "row.i") ((1:Nat)) (RunStep.eval_var B σ "row.i" (?nAX_g4612_0_0_17)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g4612_0_0_18)))) (?nAX_g4612_0_0_19)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4612_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4612_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

def ScanInvariant {m n:ℕ} (a point rhs:String) (A:Matrix (Fin m) (Fin n) ℚ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (σ:Env):Prop:=
  MatrixRows a A σ∧ Represents point (List.ofFn c) σ∧ Represents rhs (List.ofFn b) σ∧
    σ.vars "row.i" ≤ m∧ σ.vars "row.m"=m∧ σ.vars "vec.n"=n∧
    σ.vars "row.first"=foundBefore (violationPred A b c) m (σ.vars "row.i")

theorem scanStep_spec (B m n H:ℕ) (a point rhs:String)
    (A:Matrix (Fin m) (Fin n) ℚ) (b:Fin m→ ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hb:∀ k,Height (b k) H)
    (hc:∀ j,Height (c j) H) (hdims:m + n + m * n + 1 < B)
    (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => ScanInvariant a point rhs A b c σ∧ σ.vars "row.i" < m)
      (scanStep a point rhs)
      (fun σ τ => ScanInvariant a point rhs A b c τ∧ τ.vars "row.i"=σ.vars "row.i" + 1)
      (rowCost n H + 16):=by
  rintro σ ⟨⟨hσA,hσc,hσb,hσim,hσm,hσn,hσfirst⟩,hσi⟩
  let i:Fin m:= ⟨σ.vars "row.i",hσi⟩
  have heval:=spec_with_fields ["row.i", "row.m", "vec.n", "row.first"]
    (evaluateRow_spec B m n H a point rhs A b c i hH hA hb hc hdims hB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;>
      simp [evaluateRow,matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,
        loadRight,addToAccumulator,compareRowRhs,compareFraction,addFraction,multiplyFraction,
        RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,
        RamArithmetic.gcdStep,Com.wvars])
    (by simp [evaluateRow,matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,
        loadRight,addToAccumulator,compareRowRhs,compareFraction,addFraction,multiplyFraction,
        RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,
        RamArithmetic.gcdStep,Com.warrs])
  obtain ⟨τ,hr₁, ⟨hτflag,hτq,hτa⟩,hτfields,_⟩:=
    heval σ ⟨hσA,hσc,hσb,rfl,hσn⟩
  have hτi:τ.vars "row.i"=i.val:=hτfields _ (by simp)
  have hτm:τ.vars "row.m"=m:=(hτfields _ (by simp)).trans hσm
  have hτn:τ.vars "vec.n"=n:=(hτfields _ (by simp)).trans hσn
  have hτfirst:τ.vars "row.first"=foundBefore (violationPred A b c) m i.val:=
    (hτfields _ (by simp)).trans hσfirst
  have hmB:m < B:=by omega
  have h1:1 < B:=by nlinarith
  have hfirst:=foundBefore_le (violationPred A b c) m i.val i.isLt.le
  have hrec:=spec_with_fields ["row.m", "vec.n"]
    (recordViolation_spec B (τ.vars "cmp.le") (foundBefore (violationPred A b c) m i.val)
      i.val m hτflag hfirst i.isLt hmB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
      simp [recordViolation,Com.wvars]) (by simp [recordViolation,Com.warrs])
  obtain ⟨υ,hr₂, ⟨hυfirst,hυi⟩,hυfields,hυa⟩:=hrec τ ⟨rfl,hτfirst,hτi,hτm⟩
  have hflag:τ.vars "cmp.le"=0↔ violationPred A b c i.val=true:=by
    rw [violationPred_val,decide_eq_true_eq]
    constructor
    · intro hf
      by_contra h
      have hh:=hτq.mpr (le_of_not_gt h)
      omega
    · intro hv
      by_contra h
      have hh:τ.vars "cmp.le"=1:=by omega
      exact (not_lt_of_ge (hτq.mp hh)) hv
  have hnew:υ.vars "row.first"=foundBefore (violationPred A b c) m (i.val + 1):=by
    rw [hυfirst,foundBefore_succ _ _ _ i.isLt]
    simp only [hflag,and_comm]
  refine ⟨υ,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,hυi⟩
  · simpa only [MatrixRows,Slice,hυa,hτa] using hσA
  · simpa only [Represents,hυa,hτa] using hσc
  · simpa only [Represents,hυa,hτa] using hσb
  · rw [hυi]; exact i.isLt
  · exact (hυfields _ (by simp)).trans hτm
  · exact (hυfields _ (by simp)).trans hτn
  · rw [hυi]; exact hnew

theorem separateRows_spec (B m n H:ℕ) (a point rhs:String)
    (A:Matrix (Fin m) (Fin n) ℚ) (b:Fin m→ ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hb:∀ k,Height (b k) H)
    (hc:∀ j,Height (c j) H) (hdims:m + n + m * n + 1 < B)
    (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows a A σ∧ Represents point (List.ofFn c) σ∧
        Represents rhs (List.ofFn b) σ∧ σ.vars "row.m"=m∧ σ.vars "vec.n"=n)
      (separateRows a point rhs)
      (fun _ τ => τ.vars "row.first"=foundBefore (violationPred A b c) m m∧
        MatrixRows a A τ∧ Represents point (List.ofFn c) τ∧ Represents rhs (List.ofFn b) τ)
      ((rowCost n H + 16 + 4) * m + 8):=by
  have hmB:m < B:=by omega
  have hlo:=Spec.forRangeZero "row.i" "row.m" (ScanInvariant a point rhs A b c) m
    (rowCost n H + 16) hmB (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2.1)
    (scanStep_spec B m n H a point rhs A b c hH hA hb hc hdims hB)
  rintro σ ⟨hσA,hσc,hσb,hσm,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "row.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "row.i") (Expr.var "row.m")) (scanStep a point rhs)); let c1:Env→ Nat→ Prop:=Run B c0 (Env.setVar σ "row.first" (Env.vars σ "row.m")); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul (c2 (c2 (rowCost n H) ((16:Nat))) ((4:Nat))) m); let c4:Nat:=c3 ((6:Nat)); let c5:Env→ Prop:= @ScanInvariant m n a point rhs A b c; let c6:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (c5 σ') (@Eq Nat (Env.vars σ' "row.i") m)); let c7:Env→ Nat→ Prop:=Run B (separateRows a point rhs) σ; let c8:Nat:=c3 ((8:Nat)); let c9:Nat:=foundBefore (@violationPred m n A b c) m m; let c10:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.first") c9) (And (@MatrixRows m n a A τ) (And (Represents point (@List.ofFn Rat n c) τ) (Represents rhs (@List.ofFn Rat m b) τ)))) σ; let c11:Env→ Prop:=fun (σ':Env) => And (c7 σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Nat:=c2 ((1:Nat)) (Expr.size (Expr.var "row.m")); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c12) (RunStep.use B (fun (σ_1:Env) => c5 (Env.setVar σ_1 "row.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (c5 σ') (@Eq Nat (Env.vars σ' "row.i") m)) c4 hlo (Env.setVar σ "row.first" (Env.vars σ "row.m")) ?_) fun (w:Env) (h:And (c1 w c4) (And (c5 w) (@Eq Nat (Env.vars w "row.i") m))) => let c0_1:Prop:=And (c5 w) (@Eq Nat (Env.vars w "row.i") m); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c12) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c11 w (@And.intro (c7 w c8) (c10 w) (RunStep.mono B (separateRows a point rhs) σ w (c2 c13 c4) c8 (RunStep.seq B (Com.assign "row.first" (Expr.var "row.m")) c0 σ (Env.setVar σ "row.first" (Env.vars σ "row.m")) w c13 c4 (RunStep.assign B σ "row.first" (Expr.var "row.m") (Env.vars σ "row.m") (RunStep.eval_var B σ "row.m" (?nAX_g4618_0_0_0))) left) (?nAX_g4618_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4618_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4618_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [ScanInvariant,foundBefore_zero,MatrixRows,Slice,Represents]

theorem separateRows_integer_spec (B m n H:ℕ) (a point rhs:String)
    (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j, (A k j).natAbs≤ H) (hb:∀ k,Height (b k) H)
    (hc:∀ j,Height (c j) H) (hdims:m + n + m * n + 1 < B)
    (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows a (fun i j => (A i j:ℚ)) σ∧
        Represents point (List.ofFn c) σ∧ Represents rhs (List.ofFn b) σ∧
        σ.vars "row.m"=m∧ σ.vars "vec.n"=n)
      (separateRows a point rhs)
      (fun σ τ => τ.vars "row.first" =
        ((RationalSeparation.firstViolation A b c).map Fin.val).getD m∧ τ.arrs=σ.arrs)
      ((rowCost n H + 16 + 4) * m + 8):=by
  have hAH:∀ k j,Height (A k j:ℚ) H:=by
    intro k j
    simpa [Height] using And.intro (hA k j) hH
  have hsep:=spec_with_fields []
    (separateRows_spec B m n H a point rhs (fun i j => (A i j:ℚ)) b c
      hH hAH hb hc hdims hB) (by simp) (by
      simp [separateRows,scanStep,recordViolation,evaluateRow,matrixRowDot,rowDotProduct,
        rowDotStep,multiplyRowAt,loadRowLeft,loadRight,addToAccumulator,compareRowRhs,
        compareFraction,addFraction,multiplyFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  intro σ hσ
  obtain ⟨τ,hr,hτ,_,ha⟩:=hsep σ hσ
  refine ⟨τ,hr, ?_,ha⟩
  rw [hτ.1,foundBefore_integer]

end Lax109476Proofs.RamSeparation

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState EllipsoidSearch RationalArithmeticBounds

theorem matrixRows_frame {B K:ℕ} {d:Com} {σ τ:Env} (hr:Run B d σ τ K)
    {m n:ℕ} (a:String) (A:Matrix (Fin m) (Fin n) ℚ) (hσ:MatrixRows a A σ)
    (hs:a ++ ".s" ∉ d.warrs) (hn:a ++ ".n" ∉ d.warrs) (hd:a ++ ".d" ∉ d.warrs):
    MatrixRows a A τ:=by
  intro i
  simpa only [Slice,hr.frame_arr _ hs,hr.frame_arr _ hn,hr.frame_arr _ hd] using hσ i

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem searchStep_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (K l k N w:ℕ) (hk:k < N) (hNK:N≤ K)
    (hA:∀ i j, (A i j).natAbs≤ 2 ^ l) (hb:∀ i,Height (b i) (2 ^ l))
    (hw:wordWidth n (stateBits n K l) K≤ w)
    (hdims:m + n + m * n + 1 < 2 ^ w)
    (hsep:2 * (RamDotProduct.cap n (2 ^ stateBits n K l)) ^ 2 + 3 < 2 ^ w):
    Spec (2 ^ w) (fun σ => State A b k σ∧ σ.vars "search.limit"=N∧ σ.vars "search.found"=0)
      searchStep
      (fun _ τ => if RationalSeparation.firstViolation A b (trajectory A b k).2=none then
          State A b k τ∧ τ.vars "search.limit"=k∧ τ.vars "search.found"=1
        else State A b (k + 1) τ∧ τ.vars "search.limit"=N∧ τ.vars "search.found"=0)
      (cost m n K l):=by
  let H:=2 ^ stateBits n K l
  change 2 * (RamDotProduct.cap n H) ^ 2 + 3 < 2 ^ w at hsep
  have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have h1:1 < 2 ^ w:=by omega
  have hHB:H < 2 ^ w:=by
    have hh:=(RamDotProduct.cap_ge n H hH).2
    have hp:RamDotProduct.cap n H≤ (RamDotProduct.cap n H) ^ 2:=
      le_self_pow (hH.trans hh) (by decide:(2:ℕ) ≠ 0)
    omega
  have hinput:2 ^ l≤ H:=Nat.pow_le_pow_right (by decide) (by unfold stateBits; omega)
  have hAH:∀ i j, (A i j).natAbs≤ H:=fun i j => (hA i j).trans hinput
  have hbH:∀ i,Height (b i) H:=fun i => height_mono _ (hb i) hinput
  have hkK:k≤ K:=by omega
  have hstate:=trajectory_heights A b hn K l k hkK
  have hs:=RamFrame.spec_with_write_frame ["search.limit", "search.found", "iter.k", "row.m", "vec.n"]
    (separateRows_integer_spec (2 ^ w) m n H "search.rows" "ell.center" "search.rhs" A b
      (trajectory A b k).2 hH hAH hbH hstate.2 hdims hsep)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨⟨hσA,hσc,hσwork,hσnormal,hσrows,hσrhs,hσn,hσm,hσk⟩,hσlimit,hσfound⟩
  obtain ⟨τ,hr₁, ⟨hτfirst,hτarr⟩,hτvars,_⟩:=hs σ ⟨hσrows,hσc,hσrhs,hσm,hσn⟩
  clear hs
  have hτA:Represents "ell.shape" (RamMatrixStorage.flatten (trajectory A b k).1) τ:=by
    simpa only [Represents,hτarr] using hσA
  have hτc:Represents "ell.center" (List.ofFn (trajectory A b k).2) τ:=by
    simpa only [Represents,hτarr] using hσc
  have hτrows:MatrixRows "search.rows" (fun i j => (A i j:ℚ)) τ:=by
    simpa only [MatrixRows,Slice,hτarr] using hσrows
  have hτrhs:Represents "search.rhs" (List.ofFn b) τ:=by simpa only [Represents,hτarr] using hσrhs
  have hτwork:=workspace_of_run hr₁ n hσwork
  have hτnormal:=extents_of_run hr₁ "ell.normal" n hσnormal
  have hτn:τ.vars "vec.n"=n:=(hτvars _ (by simp)).trans hσn
  have hτm:τ.vars "row.m"=m:=(hτvars _ (by simp)).trans hσm
  have hτk:τ.vars "iter.k"=k:=(hτvars _ (by simp)).trans hσk
  have hτlimit:τ.vars "search.limit"=N:=(hτvars _ (by simp)).trans hσlimit
  have hτfound:τ.vars "search.found"=0:=(hτvars _ (by simp)).trans hσfound
  have hmB:m < 2 ^ w:=by omega
  have hτmB:τ.vars "row.m" < 2 ^ w:=by omega
  have hfirstB:τ.vars "row.first" < 2 ^ w:=by
    rw [hτfirst]
    cases hf:RationalSeparation.firstViolation A b (trajectory A b k).2 with
    | none => simpa using hmB
    | some i => simpa using i.isLt.trans hmB
  cases hf:RationalSeparation.firstViolation A b (trajectory A b k).2 with
  | none =>
    have hτfirst':τ.vars "row.first"=m:=by simpa only [hf,Option.map_none,Option.getD_none] using hτfirst
    have hcond:(Cond.lt (.var "row.first") (.var "row.m")).evalB (2 ^ w) τ=some false:=by
      simpa [hτfirst',hτm] using (evalB_condLt (evalB_var hfirstB) (evalB_var hτmB))
    have hkB:k < 2 ^ w:=by
      have hp:=(magnitude_parameters n (stateBits n K l) K).1
      have hguard:=wordWidth_sufficient n (stateBits n K l) K w hw
      have hparams:=RamEllipsoidWordBounds.unified_word_bounds _ _ n hn hp hguard
      have hpow:K < 2 ^ (2 * K + 3 * n + 9):=by
        have:=Nat.lt_two_pow_self (n:=2 * K + 3 * n + 9)
        omega
      exact (Nat.lt_of_le_of_lt hkK hpow).trans_le
        ((magnitude_parameters n (stateBits n K l) K).2.2.1.trans hparams.2.1.le)
    have hf₁:Run (2 ^ w) (.assign "search.found" (.lit 1)) τ (τ.setVar "search.found" 1) 2:=
      Run.assign (evalB_lit h1)
    have hf₂:Run (2 ^ w) (.assign "search.limit" (.var "iter.k")) (τ.setVar "search.found" 1)
        ((τ.setVar "search.found" 1).setVar "search.limit" k) 2:=
      Run.assign (by simpa [hτk] using (evalB_var (B:=2 ^ w)
        (σ:=τ.setVar "search.found" 1) (x:= "iter.k") (by simpa [hτk] using hkB)))
    have hrun:=hr₁.seq (Run.ite_false
      (c:=.seq (selectNormal "search.rows") advanceKeepingRows) hcond (hf₁.seq hf₂))
    refine ⟨_,hrun.mono ?_, ?_⟩
    · simp only [cost,Cond.size,Expr.size,H,Nat.add_assoc,Nat.reduceAdd]
      omega
    · simp only [hf,if_pos rfl]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      all_goals simp_all [State,Represents,MatrixRows,Slice,Workspace,Extents]
  | some i =>
    have hτfirst':τ.vars "row.first"=i.val:=by simpa only [hf,Option.map_some,Option.getD_some] using hτfirst
    have hcond:(Cond.lt (.var "row.first") (.var "row.m")).evalB (2 ^ w) τ=some true:=by
      simpa [hτfirst',hτm,i.isLt] using (evalB_condLt (evalB_var hfirstB) (evalB_var hτmB))
    obtain ⟨υ,hr₂,hυnormal,hυn⟩:=selectNormal_integer_spec (2 ^ w) m n H "search.rows" A b
      (trajectory A b k).2 (by omega) h1 hdims hH hHB hAH
      (by simp [RamCopy.Disjoint,RamCopy.suffixes]) τ
      ⟨hτrows,hτnormal,hτn,hτm,hτfirst⟩
    have hυA:=RamEllipsoidUpdate.represents_frame hr₂ "ell.shape" _ hτA (by decide) (by decide) (by decide)
    have hυc:=RamEllipsoidUpdate.represents_frame hr₂ "ell.center" _ hτc (by decide) (by decide) (by decide)
    have hυwork:=workspace_of_run hr₂ n hτwork
    have hυk:υ.vars "iter.k"=k:=(hr₂.frame_var _ (by decide)).trans hτk
    have hυm:υ.vars "row.m"=m:=(hr₂.frame_var _ (by decide)).trans hτm
    have hsave:Run (2 ^ w) (.assign "search.savedm" (.var "row.m")) υ (υ.setVar "search.savedm" m) 2:=
      Run.assign (by simpa [hυm] using (evalB_var (B:=2 ^ w) (σ:=υ) (x:= "row.m") (by omega)))
    obtain ⟨ξ,hr₃,hξc,hξA,hξwork,hξn,hξk⟩:=trajectory_advance_spec A b hn K l k w hkK hA hw
      (υ.setVar "search.savedm" m)
      ⟨by simpa only [Represents,arrs_setVar] using hυA,
        by simpa only [Represents,arrs_setVar] using hυnormal,
        by simpa only [Represents,arrs_setVar] using hυc,
        by simpa only [Workspace,Extents,arrs_setVar] using hυwork,
        by simpa using hυn,by simpa using hυk⟩
    have hξsaved:ξ.vars "search.savedm"=m:=by
      simpa using (hr₃.frame_var "search.savedm" (by decide))
    have hrestore:Run (2 ^ w) (.assign "row.m" (.var "search.savedm")) ξ (ξ.setVar "row.m" m) 2:=
      Run.assign (by simpa [hξsaved] using (evalB_var (B:=2 ^ w) (σ:=ξ) (x:= "search.savedm") (by omega)))
    have hadvance:=hsave.seq (hr₃.seq hrestore)
    have hrun:=hr₁.seq (Run.ite_true
      (d:=.seq (.assign "search.found" (.lit 1)) (.assign "search.limit" (.var "iter.k")))
      hcond (hr₂.seq hadvance))
    have hξrows:=matrixRows_frame hrun "search.rows" _ hσrows (by decide) (by decide) (by decide)
    have hξrhs:=RamEllipsoidUpdate.represents_frame hrun "search.rhs" _ hσrhs (by decide) (by decide) (by decide)
    have hξnormal:=extents_of_run hrun "ell.normal" n hσnormal
    have hξlimit:(ξ.setVar "row.m" m).vars "search.limit"=N:=
      ((hr₂.seq hadvance).frame_var _ (by decide)).trans hτlimit
    have hξfound:(ξ.setVar "row.m" m).vars "search.found"=0:=
      ((hr₂.seq hadvance).frame_var _ (by decide)).trans hτfound
    refine ⟨_,hrun.mono ?_, ?_⟩
    · simp only [cost,Cond.size,Expr.size,H,Nat.add_assoc,Nat.reduceAdd]
      omega
    · simp only [hf,reduceCtorEq,if_false]
      refine ⟨⟨?_, ?_, ?_,hξnormal,hξrows,hξrhs, ?_, ?_, ?_⟩,hξlimit,hξfound⟩
      all_goals simp_all [Represents,Workspace,Extents]

end Lax109476Proofs.RamSearchStep

end

section

open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSearchStep EllipsoidSearch

theorem body_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (N l w:ℕ)
    (hA:∀ i j, (A i j).natAbs≤ 2 ^ l)
    (hb:∀ i,RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw:RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N≤ w)
    (hdims:m + n + m * n + 1 < 2 ^ w)
    (hsep:2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w):
    Spec (2 ^ w) (fun σ => Invariant A b N σ∧
        (Cond.lt (.var "iter.k") (.var "search.limit")).evalB (2 ^ w) σ=some true)
      searchStep
      (fun σ τ => Invariant A b N τ∧
        τ.vars "search.limit" - τ.vars "iter.k" < σ.vars "search.limit" - σ.vars "iter.k")
      (cost m n N l):=by
  rintro σ ⟨⟨k,hkN,hσstate,hprior,hstatus⟩,hcond⟩
  have hσk:σ.vars "iter.k"=k:=hσstate.2.2.2.2.2.2.2.2
  have hlt:=lt_of_condLt_true hcond
  have hσfound:σ.vars "search.found"=0:=by
    rcases hstatus with h | h
    · exact h.1
    · omega
  have hσlimit:σ.vars "search.limit"=N:=by
    rcases hstatus with h | h
    · exact h.2
    · omega
  have hk:k < N:=by omega
  obtain ⟨τ,hr,hτ⟩:=searchStep_spec A b hn N l k N w hk le_rfl hA hb hw hdims hsep
    σ ⟨hσstate,hσlimit,hσfound⟩
  by_cases hf:RationalSeparation.firstViolation A b (trajectory A b k).2=none
  · simp only [if_pos hf] at hτ
    have hτk:τ.vars "iter.k"=k:=hτ.1.2.2.2.2.2.2.2.2
    refine ⟨τ,hr, ⟨k,hkN,hτ.1,hprior,Or.inr ⟨hτ.2.2,hτ.2.1,hk,hf⟩⟩, ?_⟩
    omega
  · simp only [if_neg hf] at hτ
    have hτk:τ.vars "iter.k"=k + 1:=hτ.1.2.2.2.2.2.2.2.2
    refine ⟨τ,hr, ⟨k + 1,by omega,hτ.1, ?_,Or.inl ⟨hτ.2.2,hτ.2.1⟩⟩, ?_⟩
    · intro j hj
      by_cases hjk:j < k
      · exact hprior j hjk
      · have heq:j=k:=by omega
        exact heq ▸ hf
    · omega

theorem searchLoop_spec {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (hn:2≤ n) (N l w:ℕ) (hNB:N < 2 ^ w)
    (hA:∀ i j, (A i j).natAbs≤ 2 ^ l)
    (hb:∀ i,RationalArithmeticBounds.Height (b i) (2 ^ l))
    (hw:RamEllipsoidBitBounds.wordWidth n (RamTrajectoryBounds.stateBits n N l) N≤ w)
    (hdims:m + n + m * n + 1 < 2 ^ w)
    (hsep:2 * (RamDotProduct.cap n (2 ^ RamTrajectoryBounds.stateBits n N l)) ^ 2 + 3 < 2 ^ w):
    Spec (2 ^ w) (fun σ => State A b 0 σ∧ σ.vars "search.limit"=N∧ σ.vars "search.found"=0)
      searchLoop
      (fun _ τ => Invariant A b N τ∧
        (Cond.lt (.var "iter.k") (.var "search.limit")).evalB (2 ^ w) τ=some false)
      ((cost m n N l + 4) * N + 4):=by
  apply Spec.while_count (Invariant A b N)
    (fun σ => σ.vars "search.limit" - σ.vars "iter.k") (cost m n N l)
  · rintro σ ⟨k,hkN,hstate,hprior,hstatus⟩
    have hσk:σ.vars "iter.k"=k:=hstate.2.2.2.2.2.2.2.2
    have hkB:σ.vars "iter.k" < 2 ^ w:=by omega
    have hlimitB:σ.vars "search.limit" < 2 ^ w:=by rcases hstatus with h | h <;> omega
    exact evalB_condLt_vars hkB hlimitB
  · exact body_spec A b hn N l w hA hb hw hdims hsep
  · rintro σ ⟨hstate,hlimit,hfound⟩
    exact ⟨0,Nat.zero_le N,hstate,by intro j hj; omega,Or.inl ⟨hfound,hlimit⟩⟩
  · rintro σ ⟨hstate,hlimit,hfound⟩
    have hσk:σ.vars "iter.k"=0:=hstate.2.2.2.2.2.2.2.2
    simp only [Cond.size,Expr.size,hlimit,hσk,Nat.sub_zero]
    rw [show 1 + (1 + 1 + 1) + cost m n N l=cost m n N l + 4 by omega]

end Lax109476Proofs.RamSearchLoop

end

theorem solution:∀ {m n:Nat} (A:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Rat),
  Nat.le ((2:Nat)) n→
    ∀ (N l w:Nat),
      Nat.lt N
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) w)→
        (∀ (i:Fin m) (j:Fin n),
            Nat.le (A i j).natAbs
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) l))→
          (∀ (i:Fin m),
              Lax109476Proofs.RationalArithmeticBounds.Height (b i)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) l))→
            Nat.le
                (Lax109476Proofs.RamEllipsoidBitBounds.wordWidth n (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)
                  N)
                w→
              Nat.lt
                  (Nat.add
                    (Nat.add
                      (Nat.add m n)
                      (Nat.mul m n))
                    ((1:Nat)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w)→
                Nat.lt
                    (Nat.add
                      (Nat.mul
                        ((2:Nat))
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (Lax109476Proofs.RamDotProduct.cap n
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat))
                              (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)))
                          ((2:Nat))))
                      ((3:Nat)))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And
                        (@Lax109476Proofs.RamSearchStep.State m n A b
                          ((0:Nat)) σ)
                        (And (@Eq Nat (σ.vars "search.limit") N)
                          (@Eq Nat (σ.vars "search.found") ((0:Nat)))))
                    Lax109476Proofs.RamSearchLoop.searchLoop
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                        (@Eq (Option Bool)
                          (Lax808846Proofs.Imp.Cond.evalB
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat)) w)
                            (Lax808846Proofs.Imp.Cond.lt (Lax808846Proofs.Imp.Expr.var "iter.k")
                              (Lax808846Proofs.Imp.Expr.var "search.limit"))
                            τ)
                          (@Option.some Bool Bool.false)))
                    (Nat.add
                      (Nat.mul
                        (Nat.add (Lax109476Proofs.RamSearchStep.cost m n N l)
                          ((4:Nat)))
                        N)
                      ((4:Nat))):= @Lax109476Proofs.RamSearchLoop.searchLoop_spec
