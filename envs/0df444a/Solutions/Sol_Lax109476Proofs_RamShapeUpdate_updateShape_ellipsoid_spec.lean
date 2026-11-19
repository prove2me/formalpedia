-- Prove2me | solution 1 for Lax109476Proofs.RamShapeUpdate.updateShape_ellipsoid_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:46:02.894989+00:00
-- url     : https://prove2.me/submissions/f0607ef5-9bec-4f01-8bae-41ec33fb8290

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRounding_roundFraction_spec_native

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
namespace Lax109476Proofs.RamRounding
end Lax109476Proofs.RamRounding
theorem Lax109476Proofs.RamRounding.roundFraction_spec:∀ (B M s n d D:Nat),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    LE.le s ((1:Nat))→
      LE.le n M→
        LE.le d M→
          LE.le D M→
            LT.lt ((0:Nat)) d→
              LT.lt ((0:Nat)) D→
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
                  (HAdd.hAdd
                    (HMul.hMul
                      ((36:Nat)) D.size)
                    ((96:Nat))):= @Lax109476Proofs.RamRounding.roundFraction_spec_native

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

end Lax109476Proofs.RationalSizeBounds

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

theorem height_sub (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q - r) (2 * B * C):=by
  simpa only [sub_eq_add_neg] using height_add q (-r) B C hq (height_neg r C hr)

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

theorem roundFraction_uniform_spec (B M s n d D:ℕ) (hB:2 * M ^ 2 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown (fractionValue s n d) D) τ)
      (36 * M.size + 96):=by
  apply (roundFraction_spec B M s n d D hB hs hn hd hD hdpos hDpos).mono
  have hs:=Nat.size_le_size hD
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

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamPrimitiveBounds RamRationalArrays RamRounding RationalArithmeticBounds

def LeftValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "left.s") (σ.vars "left.n") (σ.vars "left.d")=q∧
    σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den∧ σ.vars "left.s" ≤ 1

def RightValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d")=q∧
    σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den∧ σ.vars "right.s" ≤ 1

theorem leftValue_of_output (q:ℚ) (σ:Env) (h:LeftOutput q σ):LeftValue q σ:=by
  rcases h with ⟨hs,hn,hd⟩
  exact ⟨by rw [hs,hn,hd]; exact canonical_fractionValue q,hn,hd,hs ▸ rationalSign_le_one q⟩

theorem rightValue_of_output (q:ℚ) (σ:Env) (h:RightOutput q σ):RightValue q σ:=by
  rcases h with ⟨hs,hn,hd⟩
  exact ⟨by rw [hs,hn,hd]; exact canonical_fractionValue q,hn,hd,hs ▸ rationalSign_le_one q⟩

theorem multiply_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) multiplyFraction
      (fun _ τ => FractionOutput (q * r) τ) (72 * M.size + 64):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=multiplyFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

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

theorem round_spec (B M D:ℕ) (q:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hD:D≤ M) (hDpos:0 < D):
    Spec B (fun σ => LeftValue q σ∧ σ.vars "grid.D"=D) roundFraction
      (fun _ τ => FractionOutput (RationalRounding.roundDown q D) τ) (36 * M.size + 96):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩,hσD⟩
  rw [hqn,hqd] at hqval
  obtain ⟨τ,hrun,hτ⟩:=roundFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den D
    hB hqs hq.1 hq.2 hD q.den_pos hDpos σ ⟨rfl,hqn,hqd,hσD⟩
  exact ⟨τ,hrun,by simpa only [hqval] using hτ⟩

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

theorem fractionValue_flip (s n d:ℕ) (hs:s≤ 1):
    fractionValue (1 - s) n d=-fractionValue s n d:=by
  interval_cases s <;> simp [fractionValue,neg_div]

theorem negateRight_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (RightValue q) negateRight (fun _ τ => RightValue (-q) τ) 4:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  have hflip:=fractionValue_flip (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d") hqs
  rw [hqval] at hflip
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => RightValue (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "right.s"); let c2:Env:=Env.setVar σ "right.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "right.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negateRight σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negateRight σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negateRight σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "right.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "right.s") ((1:Nat)) (Env.vars σ "right.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "right.s" hsB) (?nAX_g3979_0_0_0))) (?nAX_g3979_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3979_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3979_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue]

theorem subtract_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) subtractFraction
      (fun _ τ => FractionOutput (q - r) τ) (72 * M.size + 100):=by
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσq,hσr⟩
  obtain ⟨τ,hr₁,hτr⟩:=negateRight_spec B r h1 σ hσr
  have hτq:LeftValue q τ:=by
    simpa only [LeftValue,hr₁.frame_var "left.s" (by simp [negateRight,Com.wvars]),
      hr₁.frame_var "left.n" (by simp [negateRight,Com.wvars]),
      hr₁.frame_var "left.d" (by simp [negateRight,Com.wvars])] using hσq
  obtain ⟨υ,hr₂,hυ⟩:=add_spec B M q (-r) hB hq (height_neg _ _ hr) τ ⟨hτq,hτr⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),by simpa only [sub_eq_add_neg] using hυ⟩

end Lax109476Proofs.RamFractionInterface

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

end Lax109476Proofs.EllipsoidArithmeticBounds

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

open Lax808846.Ram

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

end Lax109476Proofs.RamCenterUpdate

end

section

namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

@[simp] theorem flatten_length {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ):
    (flatten A).length=m * n:=by simp [flatten]

end Lax109476Proofs.RamMatrixStorage

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

def loopFields:List String:= ["entry.k", "entry.i", "entry.j", "vec.n", "grid.D"]

theorem arithmetic_frames (c:Com)
    (hc:c∈ [multiplyFraction,subtractFraction,addFraction,resultToRight,
      resultToLeft,RamRounding.roundFraction]):
    (∀ x∈ loopFields,x∉ c.wvars)∧ c.warrs=[]:=by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl)
  all_goals simp [multiplyFraction,subtractFraction,negateRight,resultToRight,resultToLeft,
    RamRounding.roundFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars,Com.warrs]

theorem framed_arithmetic {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (hc:c∈ [multiplyFraction,subtractFraction,addFraction,resultToRight,
      resultToLeft,RamRounding.roundFraction]) (h:Spec B P c Q K):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree loopFields σ τ∧ τ.arrs=σ.arrs) K:=
  spec_with_fields loopFields h (arithmetic_frames c hc).1 (arithmetic_frames c hc).2

theorem framed_loadLeft (B M:ℕ) (a:String) (xs:List ℚ) (i:ℕ)
    (hi:i < xs.length) (h1:1 < B) (hiB:i < B) (hmB:M < B) (hq:Height xs[i] M):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "vec.i"=i) (loadLeft a)
      (fun σ τ => LeftValue xs[i] τ∧
        FieldsAgree (loopFields ++ ["right.s", "right.n", "right.d"]) σ τ∧ τ.arrs=σ.arrs) 9:=
  spec_with_fields _
    ((loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hmB) (hq.2.trans_lt hmB)).post
      (fun _ τ _ h => leftValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])

theorem framed_loadRight (B M:ℕ) (a:String) (xs:List ℚ) (i:ℕ)
    (hi:i < xs.length) (h1:1 < B) (hiB:i < B) (hmB:M < B) (hq:Height xs[i] M):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "vec.i"=i) (loadRight a)
      (fun σ τ => RightValue xs[i] τ∧
        FieldsAgree (loopFields ++ ["left.s", "left.n", "left.d"]) σ τ∧ τ.arrs=σ.arrs) 9:=
  spec_with_fields _
    ((loadRight_spec B a xs i hi h1 hiB (hq.1.trans_lt hmB) (hq.2.trans_lt hmB)).post
      (fun _ τ _ h => rightValue_of_output _ τ h))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [loadRight,Com.wvars])
    (by simp [loadRight,Com.warrs])

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem addDiagonal_spec (B S i j:ℕ) (q:ℚ) (gs:List ℚ)
    (hig:4 < gs.length) (hiB:i < B) (hjB:j < B) (hB:2 * S ^ 2 + 3 < B)
    (hq:Height q S) (hg:Height gs[4] S):
    Spec B (fun σ => FractionOutput q σ∧ Represents "ell.coeff" gs σ∧
        σ.vars "entry.i"=i∧ σ.vars "entry.j"=j)
      addDiagonal
      (fun _ τ => FractionOutput (q + if i=j then gs[4] else 0) τ)
      (72 * S.size + 117):=by
  have hSB:S < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hSpos:1≤ S:=le_trans q.den_pos hq.2
  have h4:4 < B:=by nlinarith
  have hleft:=framed_arithmetic (by simp)
    (resultToLeft_spec B q h1 (hq.1.trans_lt hSB) (hq.2.trans_lt hSB))
  have hload:Spec B (fun σ => Represents "ell.coeff" gs σ∧ σ.vars "vec.i"=4∧ LeftValue q σ)
      (loadRight "ell.coeff") (fun σ τ => RightValue gs[4] τ∧ LeftValue q τ∧ τ.arrs=σ.arrs) 9:=by
    rintro σ ⟨hσg,hσidx,hσq⟩
    obtain ⟨τ,hr,hτg,hfields,harrs⟩:=
      framed_loadRight B S "ell.coeff" gs 4 hig h1 h4 hSB hg σ ⟨hσg,hσidx⟩
    refine ⟨τ,hr,hτg, ?_,harrs⟩
    simpa only [LeftValue,hfields "left.s" (by simp),hfields "left.n" (by simp),
      hfields "left.d" (by simp)] using hσq
  have hadd:=framed_arithmetic (by simp) (add_spec B S q gs[4] hB hq hg)
  rintro σ ⟨hσq,hσg,hσi,hσj⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "entry.i") (Env.vars σ "entry.j"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((72:Nat)) (Nat.size S)); let c4:Nat:=c3 ((117:Nat)); let c5:Rat→ Rat:= @HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) q; let c6:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) gs ((4:Nat)) hig; let c7:Env→ Prop:=FractionOutput (c5 (@ite Rat (@Eq Nat i j) (instDecidableEqNat i j) c6 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))); let c8:Env→ Prop:=(fun (x τ:Env) => c7 τ) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B addDiagonal σ σ' c4) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:Env→ Prop:=fun (σ':Env) => And (Run B resultToLeft σ σ' ((6:Nat))) (And (LeftValue q σ') (And (FieldsAgree loopFields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c12:Env→ Prop:=RightValue c6; let c13:Nat:=c3 ((96:Nat)); let c14:Env→ Prop:=FractionOutput (c5 c6); let c15:Nat→ Nat:=c2 ((1:Nat)); let c16:Nat→ Nat:=c2 (c15 (Cond.size (Cond.eq (Expr.var "entry.i") (Expr.var "entry.j")))); let c17:Nat:=c15 (Expr.size (Expr.lit ((4:Nat)))); let c18:Nat:=c2 ((9:Nat)) c13; let c19:Nat:=c2 c17 c18; let c20:Nat:=c2 ((6:Nat)) c19; let c21:Com:=Com.assign "vec.i" (Expr.lit ((4:Nat))); let c22:Com:=Com.seq c21 (Com.seq (loadRight "ell.coeff") addFraction); let c23:Com:=Com.seq resultToLeft c22; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c10) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c10) (RunStep.use B (FractionOutput q) resultToLeft (fun (σ_1 τ:Env) => And (LeftValue q τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hleft σ ?_) fun (w:Env) (h:And (Run B resultToLeft σ w ((6:Nat))) (And (LeftValue q w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=Run B resultToLeft σ w ((6:Nat)); let c1_1:Prop:=And (LeftValue q w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c2_1:Env:=Env.setVar w "vec.i" ((4:Nat)); let c3_1:Env→ Nat→ Prop:=Run B (loadRight "ell.coeff") c2_1; let c4_1:String→ List Nat:=Env.arrs c2_1; let c5_1:Env→ Prop:=fun (σ':Env) => And (c3_1 σ' ((9:Nat))) (And (c12 σ') (And (LeftValue q σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c10) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c5_1 (fun (x:@Exists Env c5_1) => c10) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") ((4:Nat))) (LeftValue q σ_1))) (loadRight "ell.coeff") (fun (σ_1 τ:Env) => And (c12 τ) (And (LeftValue q τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload c2_1 ?_) fun (w_1:Env) (h_1:And (c3_1 w_1 ((9:Nat))) (And (c12 w_1) (And (LeftValue q w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)))) => let c0_2:Prop:=c3_1 w_1 ((9:Nat)); let c1_2:Prop:=And (c12 w_1) (And (LeftValue q w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B addFraction w_1 σ' c13) (And (c14 σ') (And (FieldsAgree loopFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c10) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c10) (RunStep.use B (fun (σ_1:Env) => And (LeftValue q σ_1) (c12 σ_1)) addFraction (fun (σ_1 τ:Env) => And (c14 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c13 hadd w_1 ?_) fun (w_2:Env) (h_2:And (Run B addFraction w_1 w_2 c13) (And (c14 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (c14 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); @And.casesOn (Run B addFraction w_1 w_2 c13) c0_3 (fun (x:And (Run B addFraction w_1 w_2 c13) c0_3) => c10) h_2 fun (left_2:Run B addFraction w_1 w_2 c13) (right_2:c0_3) => @Exists.intro Env c9 w_2 (@And.intro (Run B addDiagonal σ w_2 c4) (c8 w_2) (RunStep.mono B addDiagonal σ w_2 (c16 c20) c4 (RunStep.ite_true B (Cond.eq (Expr.var "entry.i") (Expr.var "entry.j")) c23 Com.skip σ w_2 c20 (RunStep.cond_eq_true B σ (Expr.var "entry.i") (Expr.var "entry.j") (Env.vars σ "entry.i") (Env.vars σ "entry.j") (RunStep.eval_var B σ "entry.i" (?nAX_g4232_0_0_0)) (RunStep.eval_var B σ "entry.j" (?nAX_g4232_0_0_1)) hcase) (RunStep.seq B resultToLeft c22 σ w w_2 ((6:Nat)) c19 left (RunStep.seq B c21 (Com.seq (loadRight "ell.coeff") addFraction) w c2_1 w_2 c17 c18 (RunStep.assign B w "vec.i" (Expr.lit ((4:Nat))) ((4:Nat)) (RunStep.eval_lit B ((4:Nat)) w h4)) (RunStep.seq B (loadRight "ell.coeff") addFraction c2_1 w_1 w_2 ((9:Nat)) c13 left_1 left_2)))) (?nAX_g4232_0_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c9 σ (@And.intro (Run B addDiagonal σ σ c4) (c8 σ) (RunStep.mono B addDiagonal σ σ (c16 ((1:Nat))) c4 (RunStep.ite_false B (Cond.eq (Expr.var "entry.i") (Expr.var "entry.j")) c23 Com.skip σ σ ((1:Nat)) (RunStep.cond_eq_false B σ (Expr.var "entry.i") (Expr.var "entry.j") (Env.vars σ "entry.i") (Env.vars σ "entry.j") (RunStep.eval_var B σ "entry.i" (?nAX_g4232_0_0_3)) (RunStep.eval_var B σ "entry.j" (?nAX_g4232_0_0_4)) hcase) (RunStep.skip B σ)) (?nAX_g4232_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4232_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4232_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4232_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4232_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4232_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4232_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals clear hleft hload hadd
  all_goals simp_all [Represents,FieldsAgree,loopFields]
  all_goals aesop

theorem addDiagonal_frame (B S i j:ℕ) (q:ℚ) (gs:List ℚ)
    (hig:4 < gs.length) (hiB:i < B) (hjB:j < B) (hB:2 * S ^ 2 + 3 < B)
    (hq:Height q S) (hg:Height gs[4] S):
    Spec B (fun σ => FractionOutput q σ∧ Represents "ell.coeff" gs σ∧
        σ.vars "entry.i"=i∧ σ.vars "entry.j"=j)
      addDiagonal
      (fun σ τ => FractionOutput (q + if i=j then gs[4] else 0) τ∧
        FieldsAgree loopFields σ τ∧ τ.arrs=σ.arrs)
      (72 * S.size + 117):=
  spec_with_fields loopFields (addDiagonal_spec B S i j q gs hig hiB hjB hB hq hg)
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals simp [addDiagonal,resultToLeft,loadRight,addFraction,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
    (by simp [addDiagonal,resultToLeft,loadRight,addFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])

theorem entryIndex_spec (B k n:ℕ) (hk:k < B) (hn:n < B):
    Spec B (fun σ => σ.vars "entry.k"=k∧ σ.vars "vec.n"=n) entryIndex
      (fun σ τ => τ.vars "entry.i"=k / n∧ τ.vars "entry.j"=k % n∧
        τ.vars "entry.k"=k∧ τ.vars "vec.n"=n∧
        τ.vars "grid.D"=σ.vars "grid.D" ∧ τ.arrs=σ.arrs) 10:=by
  have hdiv:k / n < B:=(Nat.div_le_self k n).trans_lt hk
  have hmul:k / n * n < B:=(Nat.div_mul_le_self k n).trans_lt hk
  have hsub:k - k / n * n < B:=(Nat.sub_le k _).trans_lt hk
  rintro σ ⟨hσk,hσn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 k n; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) k n; let c3:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "entry.i") c1) (And (@Eq Nat (Env.vars τ "entry.j") c2) (And (@Eq Nat (Env.vars τ "entry.k") k) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "grid.D") (Env.vars σ_1 "grid.D")) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))))))) σ; let c4:Nat:=c0 (Env.vars σ "entry.k") (Env.vars σ "vec.n"); let c5:Env:=Env.setVar σ "entry.i" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "entry.k"; let c8:Nat:=c6 "entry.i"; let c9:Nat:=c6 "vec.n"; let c10:Nat:=Nat.mul c8 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10; let c12:Env:=Env.setVar c5 "entry.j" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "entry.k") (Expr.var "vec.n"))); let c16:Expr:=Expr.sub (Expr.var "entry.k") (Expr.mul (Expr.var "entry.i") (Expr.var "vec.n")); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B entryIndex σ σ' ((10:Nat))) (c3 σ')) c12 (@And.intro (Run B entryIndex σ c12 ((10:Nat))) (c3 c12) (RunStep.mono B entryIndex σ c12 (c13 c15 c17) ((10:Nat)) (RunStep.seq B (Com.assign "entry.i" (Expr.div (Expr.var "entry.k") (Expr.var "vec.n"))) (Com.assign "entry.j" c16) σ c5 c12 c15 c17 (RunStep.assign B σ "entry.i" (Expr.div (Expr.var "entry.k") (Expr.var "vec.n")) c4 (RunStep.eval_div B σ (Expr.var "entry.k") (Expr.var "vec.n") (Env.vars σ "entry.k") (Env.vars σ "vec.n") (RunStep.eval_var B σ "entry.k" (?nAX_g4234_0_0_0)) (RunStep.eval_var B σ "vec.n" (?nAX_g4234_0_0_1)) ?_)) (RunStep.assign B c5 "entry.j" c16 c11 (RunStep.eval_sub B c5 (Expr.var "entry.k") (Expr.mul (Expr.var "entry.i") (Expr.var "vec.n")) c7 c10 (RunStep.eval_var B c5 "entry.k" (?nAX_g4234_0_0_2)) (RunStep.eval_mul B c5 (Expr.var "entry.i") (Expr.var "vec.n") c8 c9 (RunStep.eval_var B c5 "entry.i" ?_) (RunStep.eval_var B c5 "vec.n" (?nAX_g4234_0_0_3)) ?_) (?nAX_g4234_0_0_4)))) (?nAX_g4234_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4234_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4234_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4234_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4234_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4234_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4234_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem shapeCoordinate_spec (B M D n k:ℕ) (us xs gs next:List ℚ)
    (hkn:k < n * n) (hnM:n * n≤ M) (huLen:us.length=n)
    (hiu:k / n < us.length) (hju:k % n < us.length)
    (hix:k < xs.length) (hig:4 < gs.length) (hin:k < next.length)
    (hM:1≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hu:Height us[k / n] M) (hv:Height us[k % n] M) (hx:Height xs[k] M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M)
    (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hB:2 * (shapeCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" us σ∧ Represents "ell.shape" xs σ∧
        Represents "ell.coeff" gs σ∧ Represents "ell.nextshape" next σ∧
        σ.vars "entry.k"=k∧ σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      shapeCoordinate
      (fun _ τ => Represents "ell.nextshape"
          (next.set k (gs[3] * (RationalRounding.roundDown
            (gs[0] * (xs[k] - gs[1] * (us[k / n] * us[k % n]))) D +
              if k / n=k % n then gs[4] else 0))) τ∧
        Represents "ell.u" us τ∧ Represents "ell.shape" xs τ∧ Represents "ell.coeff" gs τ)
      (468 * (shapeCap M).size + 690):=by
  have hnpos:0 < n:=by
    by_contra h
    have hn:n=0:=by omega
    simp [hn] at hkn
  have hcaps:=shapeCap_bounds M
  have hSB:shapeCap M < B:=by nlinarith only [hB]
  have hmB:M < B:=hcaps.1.trans_lt hSB
  have hkB:k < B:=hkn.trans_le hnM |>.trans hmB
  have hnB:n < B:=(le_self_pow (by omega:1≤ n) (by decide:(2:ℕ) ≠ 0)).trans
    (by simpa [pow_two] using hnM) |>.trans_lt hmB
  have hiB:k / n < B:=(Nat.div_le_self k n).trans_lt hkB
  have hjB:k % n < B:=(Nat.mod_lt k hnpos).trans hnB
  have h1:1 < B:=hM.trans_lt hmB
  have h4:4 < B:=by have hp:=Nat.one_le_pow 8 (M + 1) (by omega); unfold shapeCap at hSB; omega
  let q₁:=us[k / n] * us[k % n]
  let q₂:=gs[1] * q₁
  let q₃:=xs[k] - q₂
  let q₄:=gs[0] * q₃
  let q₅:=RationalRounding.roundDown q₄ D
  let q₆:=q₅ + if k / n=k % n then gs[4] else 0
  have hq₁:Height q₁ (M ^ 2):=by simpa [q₁,pow_two] using height_mul _ _ M M hu hv
  have hq₂:Height q₂ (M ^ 3):=by
    have h:=height_mul _ _ M (M ^ 2) hβ hq₁
    convert h using 1 <;> ring
  have hq₃:Height q₃ (2 * M ^ 4):=by
    have h:=height_sub _ _ M (M ^ 3) hx hq₂
    convert h using 1 <;> ring
  have hq₄:Height q₄ (2 * M ^ 5):=by
    have h:=height_mul _ _ M (2 * M ^ 4) hα hq₃
    convert h using 1 <;> ring
  have hq₅:Height q₅ (2 * M ^ 6 + 1):=by
    apply height_mono _ (EllipsoidArithmeticBounds.height_roundDown q₄ (2 * M ^ 5) D hq₄ hDpos)
    calc
      2 * M ^ 5 * D + 1≤ 2 * M ^ 5 * M + 1:=Nat.add_le_add_right (Nat.mul_le_mul_left _ hD) 1
      _=2 * M ^ 6 + 1:=by ring
  have hq₆:Height q₆ (6 * M ^ 7):=by
    by_cases hij:k / n=k % n
    · have h:=height_add _ _ (2 * M ^ 6 + 1) M hq₅ hδ
      simp only [q₆,if_pos hij]
      apply height_mono _ h
      have hp:M≤ M ^ 7:=le_self_pow hM (by decide:(7:ℕ) ≠ 0)
      calc
        2 * (2 * M ^ 6 + 1) * M=4 * M ^ 7 + 2 * M:=by ring
        _≤ 6 * M ^ 7:=by omega
    · simp only [q₆,if_neg hij,add_zero]
      apply height_mono _ hq₅
      have hp:=Nat.pow_le_pow_right hM (by decide:(6:ℕ)≤ 7)
      have hp1:1≤ M ^ 7:=Nat.one_le_pow _ _ hM
      omega
  have hfinal:Height (gs[3] * q₆) (shapeCap M):=by
    have h:=height_mul _ _ M (6 * M ^ 7) hρ hq₆
    apply height_mono _ h
    convert hcaps.2.2.2.2.2.2.2 using 1 <;> ring
  have huS:=height_mono _ hu hcaps.1
  have hvS:=height_mono _ hv hcaps.1
  have hxS:=height_mono _ hx hcaps.1
  have hαS:=height_mono _ hα hcaps.1
  have hβS:=height_mono _ hβ hcaps.1
  have hρS:=height_mono _ hρ hcaps.1
  have hδS:=height_mono _ hδ hcaps.1
  have hq₁S:=height_mono _ hq₁ hcaps.2.1
  have hq₂S:=height_mono _ hq₂ hcaps.2.2.1
  have hq₃S:=height_mono _ hq₃ hcaps.2.2.2.1
  have hq₄S:=height_mono _ hq₄ hcaps.2.2.2.2.1
  have hq₅S:=height_mono _ hq₅ hcaps.2.2.2.2.2.1
  have hq₆S:=height_mono _ hq₆ hcaps.2.2.2.2.2.2.1
  have hindex:=entryIndex_spec B k n hkB hnB
  have hloadU:=framed_loadLeft B M "ell.u" us (k / n) hiu h1 hiB hmB hu
  have hloadV:=framed_loadRight B M "ell.u" us (k % n) hju h1 hjB hmB hv
  have hmul₁:=framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB huS hvS)
  have hright₁:=framed_arithmetic (by simp) (resultToRight_spec B q₁ h1 (hq₁S.1.trans_lt hSB) (hq₁S.2.trans_lt hSB))
  have hloadβ:=framed_loadLeft B M "ell.coeff" gs 1 (by omega) h1 h1 hmB hβ
  have hmul₂:=framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hβS hq₁S)
  have hright₂:=framed_arithmetic (by simp) (resultToRight_spec B q₂ h1 (hq₂S.1.trans_lt hSB) (hq₂S.2.trans_lt hSB))
  have hloadX:=framed_loadLeft B M "ell.shape" xs k hix h1 hkB hmB hx
  have hsub:=framed_arithmetic (by simp) (subtract_spec B (shapeCap M) _ _ hB hxS hq₂S)
  have hright₃:=framed_arithmetic (by simp) (resultToRight_spec B q₃ h1 (hq₃S.1.trans_lt hSB) (hq₃S.2.trans_lt hSB))
  have hloadα:=framed_loadLeft B M "ell.coeff" gs 0 (by omega) h1 (by omega) hmB hα
  have hmul₃:=framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hαS hq₃S)
  have hleft:=framed_arithmetic (by simp) (resultToLeft_spec B q₄ h1 (hq₄S.1.trans_lt hSB) (hq₄S.2.trans_lt hSB))
  have hround:=framed_arithmetic (by simp) (round_spec B (shapeCap M) D q₄ hB hq₄S (hD.trans hcaps.1) hDpos)
  have hdiag:=addDiagonal_frame B (shapeCap M) (k / n) (k % n) q₅ gs hig hiB hjB hB hq₅S hδS
  have hright₄:=framed_arithmetic (by simp) (resultToRight_spec B q₆ h1 (hq₆S.1.trans_lt hSB) (hq₆S.2.trans_lt hSB))
  have hloadρ:=framed_loadLeft B M "ell.coeff" gs 3 (by omega) h1 (by omega) hmB hρ
  have hmul₄:=framed_arithmetic (by simp) (multiply_spec B (shapeCap M) _ _ hB hρS hq₆S)
  have hstore:=spec_with_write_frame loopFields
    (storeReduced_spec B "ell.nextshape" next (gs[3] * q₆) k hin h1 hkB
      (hfinal.1.trans_lt hSB) (hfinal.2.trans_lt hSB))
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [storeReduced,Com.wvars])
  have hphaseFrames (c:Com) (hc:c∈ [shapeDifference,roundedEntry]):
      (∀ x∈ loopFields,x∉ c.wvars)∧ c.warrs=[]:=by
    simp at hc
    rcases hc with rfl | rfl
    all_goals constructor
    all_goals try (intro x hx; simp [loopFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl)
    all_goals simp [shapeDifference,roundedEntry,multiplyFraction,subtractFraction,negateRight,
      resultToRight,resultToLeft,loadLeft,RamRounding.roundFraction,addFraction,
      RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,
      RamArithmetic.gcdStep,Com.wvars,Com.warrs]
  have hproduct:Spec B (fun σ => Represents "ell.u" us σ∧ σ.vars "entry.k"=k∧ σ.vars "vec.n"=n)
      entryProduct
      (fun σ τ => FractionOutput q₁ τ∧ τ.vars "entry.i"=k / n∧ τ.vars "entry.j"=k % n∧
        τ.vars "entry.k"=k∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=σ.vars "grid.D" ∧ τ.arrs=σ.arrs)
      (72 * (shapeCap M).size + 96):=by
    rintro σ ⟨hσu,hσk,hσn⟩
    (expose_names;
      (refine let c0:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) k n; let c1:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) k n; let c2:Env→ Prop:=fun (σ':Env) => And (Run B entryIndex σ σ' ((10:Nat))) (And (@Eq Nat (Env.vars σ' "entry.i") c0) (And (@Eq Nat (Env.vars σ' "entry.j") c1) (And (@Eq Nat (Env.vars σ' "entry.k") k) (And (@Eq Nat (Env.vars σ' "vec.n") n) (And (@Eq Nat (Env.vars σ' "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ))))))); let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 (Nat.mul ((72:Nat)) (Nat.size (shapeCap M))); let c5:Nat:=c4 ((96:Nat)); let c6:Env→ Prop:=(fun (σ_1 τ:Env) => And (FractionOutput q₁ τ) (And (@Eq Nat (Env.vars τ "entry.i") c0) (And (@Eq Nat (Env.vars τ "entry.j") c1) (And (@Eq Nat (Env.vars τ "entry.k") k) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "grid.D") (Env.vars σ_1 "grid.D")) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))))))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B entryProduct σ σ' c5) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:(i:Nat)→ Nat.lt i (@List.length Rat us)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) us; let c10:Rat:=c9 c0 hiu; let c11:Env→ Prop:=LeftValue c10; let c12:List String→ List String:= @HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) loopFields; let c13:Env→ Env→ Prop:=FieldsAgree (c12 (@List.cons String "right.s" (@List.cons String "right.n" (@List.cons String "right.d" (@List.nil String))))); let c14:Rat:=c9 c1 hju; let c15:Env→ Prop:=RightValue c14; let c16:Env→ Env→ Prop:=FieldsAgree (c12 (@List.cons String "left.s" (@List.cons String "left.n" (@List.cons String "left.d" (@List.nil String))))); let c17:Nat:=c4 ((64:Nat)); let c18:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c10 c14); let c19:Nat→ Nat:=c3 ((1:Nat)); let c20:Nat:=c19 (Expr.size (Expr.var "entry.i")); let c21:Nat→ Nat:=c3 ((9:Nat)); let c22:Nat:=c19 (Expr.size (Expr.var "entry.j")); let c23:Nat:=c21 c17; let c24:Nat:=c3 c22 c23; let c25:Nat:=c21 c24; let c26:Nat:=c3 c20 c25; let c27:Com:=Com.seq (Com.assign "vec.i" (Expr.var "entry.j")) (Com.seq (loadRight "ell.u") multiplyFraction); let c28:Com:=Com.seq (loadLeft "ell.u") c27; @Exists.casesOn Env c2 (fun (x:@Exists Env c2) => c8) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "entry.k") k) (@Eq Nat (Env.vars σ_1 "vec.n") n)) entryIndex (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "entry.i") c0) (And (@Eq Nat (Env.vars τ "entry.j") c1) (And (@Eq Nat (Env.vars τ "entry.k") k) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "grid.D") (Env.vars σ_1 "grid.D")) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))))))) ((10:Nat)) hindex σ ?_) fun (w:Env) (h:And (Run B entryIndex σ w ((10:Nat))) (And (@Eq Nat (Env.vars w "entry.i") c0) (And (@Eq Nat (Env.vars w "entry.j") c1) (And (@Eq Nat (Env.vars w "entry.k") k) (And (@Eq Nat (Env.vars w "vec.n") n) (And (@Eq Nat (Env.vars w "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ)))))))) => let c0_1:Prop:=Run B entryIndex σ w ((10:Nat)); let c1_1:Prop:=And (@Eq Nat (Env.vars w "entry.i") c0) (And (@Eq Nat (Env.vars w "entry.j") c1) (And (@Eq Nat (Env.vars w "entry.k") k) (And (@Eq Nat (Env.vars w "vec.n") n) (And (@Eq Nat (Env.vars w "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ)))))); let c2_1:Env→ Nat→ Prop:=Run B (loadLeft "ell.u") (Env.setVar w "vec.i" (Env.vars w "entry.i")); let c3_1:Env→ Prop:=c13 (Env.setVar w "vec.i" (Env.vars w "entry.i")); let c4_1:String→ List Nat:=Env.arrs (Env.setVar w "vec.i" (Env.vars w "entry.i")); let c5_1:Env→ Prop:=fun (σ':Env) => And (c2_1 σ' ((9:Nat))) (And (c11 σ') (And (c3_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c8) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c5_1 (fun (x:@Exists Env c5_1) => c8) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.u" us σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") c0)) (loadLeft "ell.u") (fun (σ_1 τ:Env) => And (c11 τ) (And (c13 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadU (Env.setVar w "vec.i" (Env.vars w "entry.i")) ?_) fun (w_1:Env) (h_1:And (c2_1 w_1 ((9:Nat))) (And (c11 w_1) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)))) => let c0_2:Prop:=c2_1 w_1 ((9:Nat)); let c1_2:Prop:=And (c11 w_1) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)); let c2_2:Env→ Nat→ Prop:=Run B (loadRight "ell.u") (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")); let c3_2:Env→ Prop:=c16 (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")); let c4_2:String→ List Nat:=Env.arrs (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")); let c5_2:Env→ Prop:=fun (σ':Env) => And (c2_2 σ' ((9:Nat))) (And (c15 σ') (And (c3_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_2))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c8) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c5_2 (fun (x:@Exists Env c5_2) => c8) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.u" us σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") c1)) (loadRight "ell.u") (fun (σ_1 τ:Env) => And (c15 τ) (And (c16 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadV (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")) ?_) fun (w_2:Env) (h_2:And (c2_2 w_2 ((9:Nat))) (And (c15 w_2) (And (c3_2 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) c4_2)))) => let c0_3:Prop:=c2_2 w_2 ((9:Nat)); let c1_3:Prop:=And (c15 w_2) (And (c3_2 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) c4_2)); let c2_3:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_2 σ' c17) (And (c18 σ') (And (FieldsAgree loopFields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c8) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.casesOn Env c2_3 (fun (x:@Exists Env c2_3) => c8) (RunStep.use B (fun (σ_1:Env) => And (c11 σ_1) (c15 σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c18 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c17 hmul₁ w_2 ?_) fun (w_3:Env) (h_3:And (Run B multiplyFraction w_2 w_3 c17) (And (c18 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=And (c18 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); @And.casesOn (Run B multiplyFraction w_2 w_3 c17) c0_4 (fun (x:And (Run B multiplyFraction w_2 w_3 c17) c0_4) => c8) h_3 fun (left_3:Run B multiplyFraction w_2 w_3 c17) (right_3:c0_4) => @Exists.intro Env c7 w_3 (@And.intro (Run B entryProduct σ w_3 c5) (c6 w_3) (RunStep.mono B entryProduct σ w_3 (c3 ((10:Nat)) c26) c5 (RunStep.seq B entryIndex (Com.seq (Com.assign "vec.i" (Expr.var "entry.i")) c28) σ w w_3 ((10:Nat)) c26 left (RunStep.seq B (Com.assign "vec.i" (Expr.var "entry.i")) c28 w (Env.setVar w "vec.i" (Env.vars w "entry.i")) w_3 c20 c25 (RunStep.assign B w "vec.i" (Expr.var "entry.i") (Env.vars w "entry.i") (RunStep.eval_var B w "entry.i" (?nAX_g4235_0_0_0))) (RunStep.seq B (loadLeft "ell.u") c27 (Env.setVar w "vec.i" (Env.vars w "entry.i")) w_1 w_3 ((9:Nat)) c24 left_1 (RunStep.seq B (Com.assign "vec.i" (Expr.var "entry.j")) (Com.seq (loadRight "ell.u") multiplyFraction) w_1 (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")) w_3 c22 c23 (RunStep.assign B w_1 "vec.i" (Expr.var "entry.j") (Env.vars w_1 "entry.j") (RunStep.eval_var B w_1 "entry.j" ?_)) (RunStep.seq B (loadRight "ell.u") multiplyFraction (Env.setVar w_1 "vec.i" (Env.vars w_1 "entry.j")) w_2 w_3 ((9:Nat)) c17 left_2 left_3))))) (?nAX_g4235_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4235_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3))
    all_goals clear hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁,LeftValue,RightValue,FractionOutput,Represents,FieldsAgree,loopFields]
    all_goals aesop
  have hdifferencePlain:Spec B (fun σ => FractionOutput q₁ σ∧ Represents "ell.coeff" gs σ∧
      Represents "ell.shape" xs σ∧ σ.vars "entry.k"=k) shapeDifference
      (fun _ τ => FractionOutput q₃ τ) (144 * (shapeCap M).size + 198):=by
    rintro σ ⟨hσq,hσg,hσx,hσk⟩
    (expose_names;
      (refine let c0:Env→ Prop:=fun (σ':Env) => And (Run B resultToRight σ σ' ((6:Nat))) (And (RightValue q₁ σ') (And (FieldsAgree loopFields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c1 (c2 ((144:Nat)) (Nat.size (shapeCap M))) ((198:Nat)); let c4:Env→ Prop:=fun (σ':Env) => And (Run B shapeDifference σ σ' c3) ((fun (x τ:Env) => FractionOutput q₃ τ) σ σ'); let c5:Prop:= @Exists Env c4; let c6:(xs_1:List Rat)→ (i:Nat)→ Nat.lt i (@List.length Rat xs_1)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat); let c7:Nat.lt ((1:Nat)) (@List.length Rat gs)→ Rat:=c6 gs ((1:Nat)); let c8:Env→ Prop:=LeftValue (c7 (?nAX_g4235_1_0_0)); let c9:Env→ Env→ Prop:=FieldsAgree (@HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) loopFields (@List.cons String "right.s" (@List.cons String "right.n" (@List.cons String "right.d" (@List.nil String))))); let c10:Nat→ Nat:=c1 (c2 ((72:Nat)) (Nat.size (shapeCap M))); let c11:Nat:=c10 ((64:Nat)); let c12:Rat:=c7 (?nAX_g4235_1_0_1); let c13:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c12 q₁); let c14:Env→ Prop:=LeftValue c12; let c15:Rat:=c6 xs k hix; let c16:Env→ Prop:=LeftValue c15; let c17:Nat:=c10 ((100:Nat)); let c18:Env→ Prop:=FractionOutput (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) c15 q₂); let c19:Nat→ Nat:=c1 ((6:Nat)); let c20:Nat→ Nat:=c1 ((1:Nat)); let c21:Nat:=c20 (Expr.size (Expr.lit ((1:Nat)))); let c22:Nat→ Nat:=c1 ((9:Nat)); let c23:Nat:=c20 (Expr.size (Expr.var "entry.k")); let c24:Nat:=c22 c17; let c25:Nat:=c1 c23 c24; let c26:Nat:=c19 c25; let c27:Nat:=c1 c11 c26; let c28:Nat:=c22 c27; let c29:Nat:=c1 c21 c28; let c30:Com:=Com.assign "vec.i" (Expr.lit ((1:Nat))); let c31:Com:=Com.seq (Com.assign "vec.i" (Expr.var "entry.k")) (Com.seq (loadLeft "ell.shape") subtractFraction); let c32:Com:=Com.seq resultToRight c31; let c33:Com:=Com.seq multiplyFraction c32; let c34:Com:=Com.seq (loadLeft "ell.coeff") c33; @Exists.casesOn Env c0 (fun (x:@Exists Env c0) => c5) (RunStep.use B (FractionOutput q₁) resultToRight (fun (σ_1 τ:Env) => And (RightValue q₁ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hright₁ σ ?_) fun (w:Env) (h:And (Run B resultToRight σ w ((6:Nat))) (And (RightValue q₁ w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=Run B resultToRight σ w ((6:Nat)); let c1_1:Prop:=And (RightValue q₁ w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c2_1:Env:=Env.setVar w "vec.i" ((1:Nat)); let c3_1:Env→ Nat→ Prop:=Run B (loadLeft "ell.coeff") c2_1; let c4_1:Env→ Prop:=c9 c2_1; let c5_1:String→ List Nat:=Env.arrs c2_1; let c6_1:Env→ Prop:=fun (σ':Env) => And (c3_1 σ' ((9:Nat))) (And (c8 σ') (And (c4_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c6_1 (fun (x:@Exists Env c6_1) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") ((1:Nat)))) (loadLeft "ell.coeff") (fun (σ_1 τ:Env) => And (c8 τ) (And (c9 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadβ c2_1 ?_) fun (w_1:Env) (h_1:And (c3_1 w_1 ((9:Nat))) (And (c8 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)))) => let c0_2:Prop:=c3_1 w_1 ((9:Nat)); let c1_2:Prop:=And (c8 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_1 σ' c11) (And (c13 σ') (And (FieldsAgree loopFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c5) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c5) (RunStep.use B (fun (σ_1:Env) => And (c14 σ_1) (RightValue q₁ σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c13 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c11 hmul₂ w_1 ?_) fun (w_2:Env) (h_2:And (Run B multiplyFraction w_1 w_2 c11) (And (c13 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (c13 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c1_3:Env→ Prop:=fun (σ':Env) => And (Run B resultToRight w_2 σ' ((6:Nat))) (And (RightValue q₂ σ') (And (FieldsAgree loopFields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn (Run B multiplyFraction w_1 w_2 c11) c0_3 (fun (x:And (Run B multiplyFraction w_1 w_2 c11) c0_3) => c5) h_2 fun (left_2:Run B multiplyFraction w_1 w_2 c11) (right_2:c0_3) => @Exists.casesOn Env c1_3 (fun (x:@Exists Env c1_3) => c5) (RunStep.use B (FractionOutput q₂) resultToRight (fun (σ_1 τ:Env) => And (RightValue q₂ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hright₂ w_2 ?_) fun (w_3:Env) (h_3:And (Run B resultToRight w_2 w_3 ((6:Nat))) (And (RightValue q₂ w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=Run B resultToRight w_2 w_3 ((6:Nat)); let c1_4:Prop:=And (RightValue q₂ w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); let c2_3:Env→ Nat→ Prop:=Run B (loadLeft "ell.shape") (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")); let c3_2:Env→ Prop:=c9 (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")); let c4_2:String→ List Nat:=Env.arrs (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")); let c5_2:Env→ Prop:=fun (σ':Env) => And (c2_3 σ' ((9:Nat))) (And (c16 σ') (And (c3_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_2))); @And.casesOn c0_4 c1_4 (fun (x:And c0_4 c1_4) => c5) h_3 fun (left_3:c0_4) (right_3:c1_4) => @Exists.casesOn Env c5_2 (fun (x:@Exists Env c5_2) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.shape" xs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") k)) (loadLeft "ell.shape") (fun (σ_1 τ:Env) => And (c16 τ) (And (c9 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadX (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) ?_) fun (w_4:Env) (h_4:And (c2_3 w_4 ((9:Nat))) (And (c16 w_4) (And (c3_2 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) c4_2)))) => let c0_5:Prop:=c2_3 w_4 ((9:Nat)); let c1_5:Prop:=And (c16 w_4) (And (c3_2 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) c4_2)); let c2_4:Env→ Prop:=fun (σ':Env) => And (Run B subtractFraction w_4 σ' c17) (And (c18 σ') (And (FieldsAgree loopFields w_4 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_4)))); @And.casesOn c0_5 c1_5 (fun (x:And c0_5 c1_5) => c5) h_4 fun (left_4:c0_5) (right_4:c1_5) => @Exists.casesOn Env c2_4 (fun (x:@Exists Env c2_4) => c5) (RunStep.use B (fun (σ_1:Env) => And (c16 σ_1) (RightValue q₂ σ_1)) subtractFraction (fun (σ_1 τ:Env) => And (c18 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c17 hsub w_4 ?_) fun (w_5:Env) (h_5:And (Run B subtractFraction w_4 w_5 c17) (And (c18 w_5) (And (FieldsAgree loopFields w_4 w_5) (@Eq (String→ List Nat) (Env.arrs w_5) (Env.arrs w_4))))) => let c0_6:Prop:=And (c18 w_5) (And (FieldsAgree loopFields w_4 w_5) (@Eq (String→ List Nat) (Env.arrs w_5) (Env.arrs w_4))); @And.casesOn (Run B subtractFraction w_4 w_5 c17) c0_6 (fun (x:And (Run B subtractFraction w_4 w_5 c17) c0_6) => c5) h_5 fun (left_5:Run B subtractFraction w_4 w_5 c17) (right_5:c0_6) => @Exists.intro Env c4 w_5 (@And.intro (Run B shapeDifference σ w_5 c3) ((fun (x τ:Env) => FractionOutput q₃ τ) σ w_5) (RunStep.mono B shapeDifference σ w_5 (c19 c29) c3 (RunStep.seq B resultToRight (Com.seq c30 c34) σ w w_5 ((6:Nat)) c29 left (RunStep.seq B c30 c34 w c2_1 w_5 c21 c28 (RunStep.assign B w "vec.i" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) w h1)) (RunStep.seq B (loadLeft "ell.coeff") c33 c2_1 w_1 w_5 ((9:Nat)) c27 left_1 (RunStep.seq B multiplyFraction c32 w_1 w_2 w_5 c11 c26 left_2 (RunStep.seq B resultToRight c31 w_2 w_3 w_5 ((6:Nat)) c25 left_3 (RunStep.seq B (Com.assign "vec.i" (Expr.var "entry.k")) (Com.seq (loadLeft "ell.shape") subtractFraction) w_3 (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) w_5 c23 c24 (RunStep.assign B w_3 "vec.i" (Expr.var "entry.k") (Env.vars w_3 "entry.k") (RunStep.eval_var B w_3 "entry.k" ?_)) (RunStep.seq B (loadLeft "ell.shape") subtractFraction (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) w_4 w_5 ((9:Nat)) c17 left_4 left_5))))))) (?nAX_g4235_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4235_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4); (all_goals try clear h_5); (all_goals try clear left_5))
    all_goals clear hproduct hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁,q₂,q₃,LeftValue,RightValue,FractionOutput,Represents,FieldsAgree,loopFields]
    all_goals aesop
  have hdifference:=spec_with_fields loopFields hdifferencePlain
    (hphaseFrames shapeDifference (by simp)).1 (hphaseFrames shapeDifference (by simp)).2
  have hroundedPlain:Spec B (fun σ => FractionOutput q₃ σ∧ Represents "ell.coeff" gs σ∧
      σ.vars "grid.D"=D) roundedEntry
      (fun _ τ => FractionOutput q₅ τ) (108 * (shapeCap M).size + 183):=by
    rintro σ ⟨hσq,hσg,hσD⟩
    (expose_names;
      (refine let c0:Env→ Prop:=fun (σ':Env) => And (Run B resultToRight σ σ' ((6:Nat))) (And (RightValue q₃ σ') (And (FieldsAgree loopFields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c1 (c2 ((108:Nat)) (Nat.size (shapeCap M))) ((183:Nat)); let c4:Env→ Prop:=fun (σ':Env) => And (Run B roundedEntry σ σ' c3) ((fun (x τ:Env) => FractionOutput q₅ τ) σ σ'); let c5:Prop:= @Exists Env c4; let c6:Nat.lt ((0:Nat)) (@List.length Rat gs)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) gs ((0:Nat)); let c7:Env→ Prop:=LeftValue (c6 (?nAX_g4235_2_0_0)); let c8:Env→ Env→ Prop:=FieldsAgree (@HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) loopFields (@List.cons String "right.s" (@List.cons String "right.n" (@List.cons String "right.d" (@List.nil String))))); let c9:Nat:=c1 (c2 ((72:Nat)) (Nat.size (shapeCap M))) ((64:Nat)); let c10:Rat:=c6 (?nAX_g4235_2_0_1); let c11:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c10 q₃); let c12:Env→ Prop:=LeftValue c10; let c13:Nat:=c1 (c2 ((36:Nat)) (Nat.size (shapeCap M))) ((96:Nat)); let c14:Nat→ Nat:=c1 ((6:Nat)); let c15:Nat:=c1 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat:=c14 c13; let c17:Nat:=c1 c9 c16; let c18:Nat:=c1 ((9:Nat)) c17; let c19:Nat:=c1 c15 c18; let c20:Com:=Com.assign "vec.i" (Expr.lit ((0:Nat))); let c21:Com:=Com.seq (loadLeft "ell.coeff") (Com.seq multiplyFraction (Com.seq resultToLeft RamRounding.roundFraction)); @Exists.casesOn Env c0 (fun (x:@Exists Env c0) => c5) (RunStep.use B (FractionOutput q₃) resultToRight (fun (σ_1 τ:Env) => And (RightValue q₃ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hright₃ σ ?_) fun (w:Env) (h:And (Run B resultToRight σ w ((6:Nat))) (And (RightValue q₃ w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=Run B resultToRight σ w ((6:Nat)); let c1_1:Prop:=And (RightValue q₃ w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c2_1:Env:=Env.setVar w "vec.i" ((0:Nat)); let c3_1:Env→ Nat→ Prop:=Run B (loadLeft "ell.coeff") c2_1; let c4_1:Env→ Prop:=c8 c2_1; let c5_1:String→ List Nat:=Env.arrs c2_1; let c6_1:Env→ Prop:=fun (σ':Env) => And (c3_1 σ' ((9:Nat))) (And (c7 σ') (And (c4_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c6_1 (fun (x:@Exists Env c6_1) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") ((0:Nat)))) (loadLeft "ell.coeff") (fun (σ_1 τ:Env) => And (c7 τ) (And (c8 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadα c2_1 ?_) fun (w_1:Env) (h_1:And (c3_1 w_1 ((9:Nat))) (And (c7 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)))) => let c0_2:Prop:=c3_1 w_1 ((9:Nat)); let c1_2:Prop:=And (c7 w_1) (And (c4_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c5_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_1 σ' c9) (And (c11 σ') (And (FieldsAgree loopFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c5) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c5) (RunStep.use B (fun (σ_1:Env) => And (c12 σ_1) (RightValue q₃ σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c11 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c9 hmul₃ w_1 ?_) fun (w_2:Env) (h_2:And (Run B multiplyFraction w_1 w_2 c9) (And (c11 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (c11 w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c1_3:Env→ Prop:=fun (σ':Env) => And (Run B resultToLeft w_2 σ' ((6:Nat))) (And (LeftValue q₄ σ') (And (FieldsAgree loopFields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn (Run B multiplyFraction w_1 w_2 c9) c0_3 (fun (x:And (Run B multiplyFraction w_1 w_2 c9) c0_3) => c5) h_2 fun (left_2:Run B multiplyFraction w_1 w_2 c9) (right_2:c0_3) => @Exists.casesOn Env c1_3 (fun (x:@Exists Env c1_3) => c5) (RunStep.use B (FractionOutput q₄) resultToLeft (fun (σ_1 τ:Env) => And (LeftValue q₄ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hleft w_2 ?_) fun (w_3:Env) (h_3:And (Run B resultToLeft w_2 w_3 ((6:Nat))) (And (LeftValue q₄ w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=Run B resultToLeft w_2 w_3 ((6:Nat)); let c1_4:Prop:=And (LeftValue q₄ w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); let c2_3:Env→ Prop:=fun (σ':Env) => And (Run B RamRounding.roundFraction w_3 σ' c13) (And (FractionOutput (RationalRounding.roundDown q₄ D) σ') (And (FieldsAgree loopFields w_3 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_3)))); @And.casesOn c0_4 c1_4 (fun (x:And c0_4 c1_4) => c5) h_3 fun (left_3:c0_4) (right_3:c1_4) => @Exists.casesOn Env c2_3 (fun (x:@Exists Env c2_3) => c5) (RunStep.use B (fun (σ_1:Env) => And (LeftValue q₄ σ_1) (@Eq Nat (Env.vars σ_1 "grid.D") D)) RamRounding.roundFraction (fun (σ_1 τ:Env) => And (FractionOutput (RationalRounding.roundDown q₄ D) τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c13 hround w_3 ?_) fun (w_4:Env) (h_4:And (Run B RamRounding.roundFraction w_3 w_4 c13) (And (FractionOutput (RationalRounding.roundDown q₄ D) w_4) (And (FieldsAgree loopFields w_3 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) (Env.arrs w_3))))) => let c0_5:Prop:=And (FractionOutput (RationalRounding.roundDown q₄ D) w_4) (And (FieldsAgree loopFields w_3 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) (Env.arrs w_3))); @And.casesOn (Run B RamRounding.roundFraction w_3 w_4 c13) c0_5 (fun (x:And (Run B RamRounding.roundFraction w_3 w_4 c13) c0_5) => c5) h_4 fun (left_4:Run B RamRounding.roundFraction w_3 w_4 c13) (right_4:c0_5) => @Exists.intro Env c4 w_4 (@And.intro (Run B roundedEntry σ w_4 c3) ((fun (x τ:Env) => FractionOutput q₅ τ) σ w_4) (RunStep.mono B roundedEntry σ w_4 (c14 c19) c3 (RunStep.seq B resultToRight (Com.seq c20 c21) σ w w_4 ((6:Nat)) c19 left (RunStep.seq B c20 c21 w c2_1 w_4 c15 c18 (RunStep.assign B w "vec.i" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) w (?nAX_g4235_2_0_2))) (RunStep.seq B (loadLeft "ell.coeff") (Com.seq multiplyFraction (Com.seq resultToLeft RamRounding.roundFraction)) c2_1 w_1 w_4 ((9:Nat)) c17 left_1 (RunStep.seq B multiplyFraction (Com.seq resultToLeft RamRounding.roundFraction) w_1 w_2 w_4 c9 c16 left_2 (RunStep.seq B resultToLeft RamRounding.roundFraction w_2 w_3 w_4 ((6:Nat)) c13 left_3 left_4))))) (?nAX_g4235_2_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4235_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4))
    all_goals clear hproduct hdifferencePlain hdifference hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁,q₂,q₃,q₄,q₅,LeftValue,RightValue,FractionOutput,Represents,FieldsAgree,loopFields]
    all_goals aesop
  have hrounded:=spec_with_fields loopFields hroundedPlain
    (hphaseFrames roundedEntry (by simp)).1 (hphaseFrames roundedEntry (by simp)).2
  have hinflatedPlain:Spec B (fun σ => FractionOutput q₅ σ∧ Represents "ell.coeff" gs σ∧
      Represents "ell.nextshape" next σ∧ σ.vars "entry.i"=k / n∧
      σ.vars "entry.j"=k % n∧ σ.vars "entry.k"=k) inflatedEntry
      (fun _ τ => Represents "ell.nextshape" (next.set k (gs[3] * q₆)) τ)
      (144 * (shapeCap M).size + 213):=by
    rintro σ ⟨hσq,hσg,hσnext,hσi,hσj,hσk⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c0 (c1 ((72:Nat)) (Nat.size (shapeCap M))); let c3:Nat:=c2 ((117:Nat)); let c4:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) k n; let c5:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) k n; let c6:(i:Nat)→ Nat.lt i (@List.length Rat gs)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) gs; let c7:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) q₅ (@ite Rat (@Eq Nat c4 c5) (instDecidableEqNat c4 c5) (c6 ((4:Nat)) hig) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))); let c8:Env→ Prop:=fun (σ':Env) => And (Run B addDiagonal σ σ' c3) (And (c7 σ') (And (FieldsAgree loopFields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c9:Nat:=c0 (c1 ((144:Nat)) (Nat.size (shapeCap M))) ((213:Nat)); let c10:Rat→ Rat→ Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul); let c11:Nat.lt ((3:Nat)) (@List.length Rat gs)→ Rat:=c6 ((3:Nat)); let c12:Rat:=c11 (?nAX_g4235_3_0_0); let c13:Rat:=c10 c12 q₆; let c14:Env→ Prop:=Represents "ell.nextshape" (@List.set Rat next k c13); let c15:Env→ Prop:=(fun (x τ:Env) => c14 τ) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B inflatedEntry σ σ' c9) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Env→ Prop:=LeftValue c12; let c19:Env→ Env→ Prop:=FieldsAgree (@HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) loopFields (@List.cons String "right.s" (@List.cons String "right.n" (@List.cons String "right.d" (@List.nil String))))); let c20:Nat:=c2 ((64:Nat)); let c21:Rat:=c11 (?nAX_g4235_3_0_1); let c22:Env→ Prop:=FractionOutput (c10 c21 q₆); let c23:Env→ Prop:=LeftValue c21; let c24:Env→ Prop:=FractionOutput c13; let c25:Nat→ Nat:=c0 ((1:Nat)); let c26:Nat:=c25 (Expr.size (Expr.lit ((3:Nat)))); let c27:Nat:=c25 (Expr.size (Expr.var "entry.k")); let c28:Nat:=c0 c27 ((13:Nat)); let c29:Nat:=c0 c20 c28; let c30:Nat:=c0 ((9:Nat)) c29; let c31:Nat:=c0 c26 c30; let c32:Nat:=c0 ((6:Nat)) c31; let c33:Com:=Com.assign "vec.i" (Expr.lit ((3:Nat))); let c34:Com:=Com.seq (Com.assign "vec.i" (Expr.var "entry.k")) (storeReduced "ell.nextshape"); let c35:Com:=Com.seq multiplyFraction c34; let c36:Com:=Com.seq (loadLeft "ell.coeff") c35; let c37:Com:=Com.seq c33 c36; @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c17) (RunStep.use B (fun (σ_1:Env) => And (FractionOutput q₅ σ_1) (And (Represents "ell.coeff" gs σ_1) (And (@Eq Nat (Env.vars σ_1 "entry.i") c4) (@Eq Nat (Env.vars σ_1 "entry.j") c5)))) addDiagonal (fun (σ_1 τ:Env) => And (c7 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c3 hdiag σ ?_) fun (w:Env) (h:And (Run B addDiagonal σ w c3) (And (c7 w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=And (c7 w) (And (FieldsAgree loopFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B resultToRight w σ' ((6:Nat))) (And (RightValue q₆ σ') (And (FieldsAgree loopFields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn (Run B addDiagonal σ w c3) c0_1 (fun (x:And (Run B addDiagonal σ w c3) c0_1) => c17) h fun (left:Run B addDiagonal σ w c3) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c17) (RunStep.use B (FractionOutput q₆) resultToRight (fun (σ_1 τ:Env) => And (RightValue q₆ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hright₄ w ?_) fun (w_1:Env) (h_1:And (Run B resultToRight w w_1 ((6:Nat))) (And (RightValue q₆ w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B resultToRight w w_1 ((6:Nat)); let c1_2:Prop:=And (RightValue q₆ w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_1:Env:=Env.setVar w_1 "vec.i" ((3:Nat)); let c3_1:Env→ Nat→ Prop:=Run B (loadLeft "ell.coeff") c2_1; let c4_1:Env→ Prop:=c19 c2_1; let c5_1:String→ List Nat:=Env.arrs c2_1; let c6_1:Env→ Prop:=fun (σ':Env) => And (c3_1 σ' ((9:Nat))) (And (c18 σ') (And (c4_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5_1))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c17) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c6_1 (fun (x:@Exists Env c6_1) => c17) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") ((3:Nat)))) (loadLeft "ell.coeff") (fun (σ_1 τ:Env) => And (c18 τ) (And (c19 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hloadρ c2_1 ?_) fun (w_2:Env) (h_2:And (c3_1 w_2 ((9:Nat))) (And (c18 w_2) (And (c4_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) c5_1)))) => let c0_3:Prop:=c3_1 w_2 ((9:Nat)); let c1_3:Prop:=And (c18 w_2) (And (c4_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) c5_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_2 σ' c20) (And (c22 σ') (And (FieldsAgree loopFields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c17) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c17) (RunStep.use B (fun (σ_1:Env) => And (c23 σ_1) (RightValue q₆ σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c22 τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c20 hmul₄ w_2 ?_) fun (w_3:Env) (h_3:And (Run B multiplyFraction w_2 w_3 c20) (And (c22 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=And (c22 w_3) (And (FieldsAgree loopFields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); let c1_4:Env→ Nat→ Prop:=Run B (storeReduced "ell.nextshape") (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")); let c2_3:Env→ Prop:=FieldsAgree loopFields (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")); let c3_2:Env→ Prop:=fun (σ':Env) => And (c1_4 σ' ((13:Nat))) (And (c14 σ') (And (c2_3 σ') (∀ a∉ Com.warrs (storeReduced "ell.nextshape"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) a)))); @And.casesOn (Run B multiplyFraction w_2 w_3 c20) c0_4 (fun (x:And (Run B multiplyFraction w_2 w_3 c20) c0_4) => c17) h_3 fun (left_3:Run B multiplyFraction w_2 w_3 c20) (right_3:c0_4) => @Exists.casesOn Env c3_2 (fun (x:@Exists Env c3_2) => c17) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.nextshape" next σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") k) (c24 σ_1))) (storeReduced "ell.nextshape") (fun (σ_1 τ:Env) => And (c14 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a∉ Com.warrs (storeReduced "ell.nextshape"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) ?_) fun (w_4:Env) (h_4:And (c1_4 w_4 ((13:Nat))) (And (c14 w_4) (And (c2_3 w_4) (∀ a∉ Com.warrs (storeReduced "ell.nextshape"), @Eq (List Nat) (Env.arrs w_4 a) (Env.arrs (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) a))))) => let c0_5:Prop:=c1_4 w_4 ((13:Nat)); let c1_5:Prop:=And (c14 w_4) (And (c2_3 w_4) (∀ a∉ Com.warrs (storeReduced "ell.nextshape"), @Eq (List Nat) (Env.arrs w_4 a) (Env.arrs (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) a))); @And.casesOn c0_5 c1_5 (fun (x:And c0_5 c1_5) => c17) h_4 fun (left_4:c0_5) (right_4:c1_5) => @Exists.intro Env c16 w_4 (@And.intro (Run B inflatedEntry σ w_4 c9) (c15 w_4) (RunStep.mono B inflatedEntry σ w_4 (c0 c3 c32) c9 (RunStep.seq B addDiagonal (Com.seq resultToRight c37) σ w w_4 c3 c32 left (RunStep.seq B resultToRight c37 w w_1 w_4 ((6:Nat)) c31 left_1 (RunStep.seq B c33 c36 w_1 c2_1 w_4 c26 c30 (RunStep.assign B w_1 "vec.i" (Expr.lit ((3:Nat))) ((3:Nat)) (RunStep.eval_lit B ((3:Nat)) w_1 (?nAX_g4235_3_0_2))) (RunStep.seq B (loadLeft "ell.coeff") c35 c2_1 w_2 w_4 ((9:Nat)) c29 left_2 (RunStep.seq B multiplyFraction c34 w_2 w_3 w_4 c20 c28 left_3 (RunStep.seq B (Com.assign "vec.i" (Expr.var "entry.k")) (storeReduced "ell.nextshape") w_3 (Env.setVar w_3 "vec.i" (Env.vars w_3 "entry.k")) w_4 c27 ((13:Nat)) (RunStep.assign B w_3 "vec.i" (Expr.var "entry.k") (Env.vars w_3 "entry.k") (RunStep.eval_var B w_3 "entry.k" ?_)) left_4)))))) (?nAX_g4235_3_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4235_3_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_3_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_3_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_3_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4))
    all_goals clear hproduct hdifferencePlain hdifference hroundedPlain hrounded hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
    all_goals simp_all [q₁,q₂,q₃,q₄,q₅,q₆,LeftValue,RightValue,FractionOutput,
      Represents,FieldsAgree,loopFields,storeReduced,Com.warrs]
    all_goals aesop
  have hinflated:=spec_with_write_frame loopFields hinflatedPlain
    (by
      intro x hx
      simp [loopFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      all_goals simp [inflatedEntry,addDiagonal,storeReduced,multiplyFraction,addFraction,
        resultToRight,resultToLeft,loadLeft,loadRight,RamArithmetic.normalizeFraction,
        RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
  rintro σ ⟨hσu,hσx,hσg,hσnext,hσk,hσn,hσD⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c0 (c1 ((72:Nat)) (Nat.size (shapeCap M))) ((96:Nat)); let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) k n; let c4:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) k n; let c5:Env→ Prop:=fun (σ':Env) => And (Run B entryProduct σ σ' c2) (And (FractionOutput q₁ σ') (And (@Eq Nat (Env.vars σ' "entry.i") c3) (And (@Eq Nat (Env.vars σ' "entry.j") c4) (And (@Eq Nat (Env.vars σ' "entry.k") k) (And (@Eq Nat (Env.vars σ' "vec.n") n) (And (@Eq Nat (Env.vars σ' "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))))))); let c6:Nat:=c0 (c1 ((468:Nat)) (Nat.size (shapeCap M))) ((690:Nat)); let c7:Rat→ Rat→ Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul); let c8:(xs_1:List Rat)→ (i:Nat)→ Nat.lt i (@List.length Rat xs_1)→ Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i:Nat) => Nat.lt i (@List.length Rat as)) (@List.instGetElemNatLtLength Rat); let c9:(i:Nat)→ Nat.lt i (@List.length Rat gs)→ Rat:=c8 gs; let c10:Rat→ Rat:=c7 (c9 ((3:Nat)) (?nAX_g4235_4_0_0)); let c11:(i:Nat)→ Nat.lt i (@List.length Rat us)→ Rat:=c8 us; let c12:Env→ Prop:=Represents "ell.nextshape" (@List.set Rat next k (c10 (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (RationalRounding.roundDown (c7 (c9 ((0:Nat)) (?nAX_g4235_4_0_1)) (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) (c8 xs k hix) (c7 (c9 ((1:Nat)) (?nAX_g4235_4_0_2)) (c7 (c11 c3 hiu) (c11 c4 hju))))) D) (@ite Rat (@Eq Nat c3 c4) (instDecidableEqNat c3 c4) (c9 ((4:Nat)) hig) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))))); let c13:Env→ Prop:=(fun (x τ:Env) => And (c12 τ) (And (Represents "ell.u" us τ) (And (Represents "ell.shape" xs τ) (Represents "ell.coeff" gs τ)))) σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B shapeCoordinate σ σ' c6) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:Nat→ Nat:=c0 (c1 ((144:Nat)) (Nat.size (shapeCap M))); let c17:Nat:=c16 ((198:Nat)); let c18:Nat:=c0 (c1 ((108:Nat)) (Nat.size (shapeCap M))) ((183:Nat)); let c19:Nat:=c16 ((213:Nat)); let c20:Env→ Prop:=Represents "ell.nextshape" (@List.set Rat next k (c10 q₆)); let c21:Nat:=c0 c18 c19; let c22:Nat:=c0 c17 c21; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c15) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.u" us σ_1) (And (@Eq Nat (Env.vars σ_1 "entry.k") k) (@Eq Nat (Env.vars σ_1 "vec.n") n))) entryProduct (fun (σ_1 τ:Env) => And (FractionOutput q₁ τ) (And (@Eq Nat (Env.vars τ "entry.i") c3) (And (@Eq Nat (Env.vars τ "entry.j") c4) (And (@Eq Nat (Env.vars τ "entry.k") k) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "grid.D") (Env.vars σ_1 "grid.D")) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))))))) c2 hproduct σ ?_) fun (w:Env) (h:And (Run B entryProduct σ w c2) (And (FractionOutput q₁ w) (And (@Eq Nat (Env.vars w "entry.i") c3) (And (@Eq Nat (Env.vars w "entry.j") c4) (And (@Eq Nat (Env.vars w "entry.k") k) (And (@Eq Nat (Env.vars w "vec.n") n) (And (@Eq Nat (Env.vars w "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))))))) => let c0_1:Prop:=And (FractionOutput q₁ w) (And (@Eq Nat (Env.vars w "entry.i") c3) (And (@Eq Nat (Env.vars w "entry.j") c4) (And (@Eq Nat (Env.vars w "entry.k") k) (And (@Eq Nat (Env.vars w "vec.n") n) (And (@Eq Nat (Env.vars w "grid.D") (Env.vars σ "grid.D")) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B shapeDifference w σ' c17) (And (FractionOutput q₃ σ') (And (FieldsAgree loopFields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn (Run B entryProduct σ w c2) c0_1 (fun (x:And (Run B entryProduct σ w c2) c0_1) => c15) h fun (left:Run B entryProduct σ w c2) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c15) (RunStep.use B (fun (σ_1:Env) => And (FractionOutput q₁ σ_1) (And (Represents "ell.coeff" gs σ_1) (And (Represents "ell.shape" xs σ_1) (@Eq Nat (Env.vars σ_1 "entry.k") k)))) shapeDifference (fun (σ_1 τ:Env) => And (FractionOutput q₃ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c17 hdifference w ?_) fun (w_1:Env) (h_1:And (Run B shapeDifference w w_1 c17) (And (FractionOutput q₃ w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=And (FractionOutput q₃ w_1) (And (FieldsAgree loopFields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c1_2:Env→ Prop:=fun (σ':Env) => And (Run B roundedEntry w_1 σ' c18) (And (FractionOutput q₅ σ') (And (FieldsAgree loopFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn (Run B shapeDifference w w_1 c17) c0_2 (fun (x:And (Run B shapeDifference w w_1 c17) c0_2) => c15) h_1 fun (left_1:Run B shapeDifference w w_1 c17) (right_1:c0_2) => @Exists.casesOn Env c1_2 (fun (x:@Exists Env c1_2) => c15) (RunStep.use B (fun (σ_1:Env) => And (FractionOutput q₃ σ_1) (And (Represents "ell.coeff" gs σ_1) (@Eq Nat (Env.vars σ_1 "grid.D") D))) roundedEntry (fun (σ_1 τ:Env) => And (FractionOutput q₅ τ) (And (FieldsAgree loopFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c18 hrounded w_1 ?_) fun (w_2:Env) (h_2:And (Run B roundedEntry w_1 w_2 c18) (And (FractionOutput q₅ w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (FractionOutput q₅ w_2) (And (FieldsAgree loopFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c1_3:Env→ Prop:=fun (σ':Env) => And (Run B inflatedEntry w_2 σ' c19) (And (c20 σ') (And (FieldsAgree loopFields w_2 σ') (∀ a∉ Com.warrs inflatedEntry, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs w_2 a)))); @And.casesOn (Run B roundedEntry w_1 w_2 c18) c0_3 (fun (x:And (Run B roundedEntry w_1 w_2 c18) c0_3) => c15) h_2 fun (left_2:Run B roundedEntry w_1 w_2 c18) (right_2:c0_3) => @Exists.casesOn Env c1_3 (fun (x:@Exists Env c1_3) => c15) (RunStep.use B (fun (σ_1:Env) => And (FractionOutput q₅ σ_1) (And (Represents "ell.coeff" gs σ_1) (And (Represents "ell.nextshape" next σ_1) (And (@Eq Nat (Env.vars σ_1 "entry.i") c3) (And (@Eq Nat (Env.vars σ_1 "entry.j") c4) (@Eq Nat (Env.vars σ_1 "entry.k") k)))))) inflatedEntry (fun (σ_1 τ:Env) => And (c20 τ) (And (FieldsAgree loopFields σ_1 τ) (∀ a∉ Com.warrs inflatedEntry, @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c19 hinflated w_2 ?_) fun (w_3:Env) (h_3:And (Run B inflatedEntry w_2 w_3 c19) (And (c20 w_3) (And (FieldsAgree loopFields w_2 w_3) (∀ a∉ Com.warrs inflatedEntry, @Eq (List Nat) (Env.arrs w_3 a) (Env.arrs w_2 a))))) => let c0_4:Prop:=And (c20 w_3) (And (FieldsAgree loopFields w_2 w_3) (∀ a∉ Com.warrs inflatedEntry, @Eq (List Nat) (Env.arrs w_3 a) (Env.arrs w_2 a))); @And.casesOn (Run B inflatedEntry w_2 w_3 c19) c0_4 (fun (x:And (Run B inflatedEntry w_2 w_3 c19) c0_4) => c15) h_3 fun (left_3:Run B inflatedEntry w_2 w_3 c19) (right_3:c0_4) => @Exists.intro Env c14 w_3 (@And.intro (Run B shapeCoordinate σ w_3 c6) (c13 w_3) (RunStep.mono B shapeCoordinate σ w_3 (c0 c2 c22) c6 (RunStep.seq B entryProduct (Com.seq shapeDifference (Com.seq roundedEntry inflatedEntry)) σ w w_3 c2 c22 left (RunStep.seq B shapeDifference (Com.seq roundedEntry inflatedEntry) w w_1 w_3 c17 c21 left_1 (RunStep.seq B roundedEntry inflatedEntry w_1 w_2 w_3 c18 c19 left_2 left_3))) (?nAX_g4235_4_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4235_4_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_4_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_4_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4235_4_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3))
  all_goals clear hproduct hdifference hrounded hinflated hdifferencePlain hroundedPlain hinflatedPlain hphaseFrames hindex hloadU hloadV hmul₁ hright₁ hloadβ hmul₂ hright₂ hloadX hsub hright₃ hloadα hmul₃ hleft hround hdiag hright₄ hloadρ hmul₄ hstore
  all_goals simp_all [q₁,q₂,q₃,q₄,q₅,q₆,FractionOutput,Represents,FieldsAgree,
    loopFields,inflatedEntry,addDiagonal,storeReduced,multiplyFraction,addFraction,resultToRight,
    resultToLeft,loadLeft,loadRight,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs]
  all_goals aesop

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

def entryValues {n:ℕ} (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (D:ℕ):Fin (n * n)→ ℚ:=
  fun k => shapeValues u A gs hg D k.divNat k.modNat

def ShapeInvariant {n:ℕ} (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (D:ℕ) (hg:4 < gs.length) (σ:Env):Prop:=
  Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.shape" (flatten A) σ∧
    Represents "ell.coeff" gs σ∧
    Represents "ell.nextshape" (RamCenterUpdate.filled (entryValues u A gs hg D) (σ.vars "entry.k")) σ∧
    σ.vars "entry.k" ≤ n * n∧ σ.vars "entry.count"=n * n∧
    σ.vars "vec.n"=n∧ σ.vars "grid.D"=D

set_option maxRecDepth 30000 in
theorem shapeStep_spec (B n M D:ℕ) (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (hM:1≤ M) (hnM:n * n≤ M)
    (hu:∀ j,Height (u j) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hD:D≤ M) (hDpos:0 < D) (hnB:n * n < B)
    (hB:2 * (shapeCap M) ^ 2 + 3 < B):
    Spec B (fun σ => ShapeInvariant u A gs D hg σ∧ σ.vars "entry.k" < n * n) shapeStep
      (fun σ τ => ShapeInvariant u A gs D hg τ∧ τ.vars "entry.k"=σ.vars "entry.k" + 1)
      (468 * (shapeCap M).size + 690 + 4):=by
  rintro σ ⟨⟨hσu,hσA,hσg,hσnext,hσkN,hσcount,hσn,hσD⟩,hσk⟩
  let k:Fin (n * n):= ⟨σ.vars "entry.k",hσk⟩
  have hiu:k.val / n < (List.ofFn u).length:=by simpa using k.divNat.isLt
  have hju:k.val % n < (List.ofFn u).length:=by simpa using k.modNat.isLt
  have huk:Height (List.ofFn u)[k.val / n] M:=by
    simpa [Fin.divNat] using hu k.divNat
  have hvk:Height (List.ofFn u)[k.val % n] M:=by
    simpa [Fin.modNat] using hu k.modNat
  have hAk:Height (flatten A)[k.val] M:=by simpa [flatten] using hA k.divNat k.modNat
  obtain ⟨τ,hr₁,hτnext,hτu,hτA,hτg⟩:=shapeCoordinate_spec B M D n k.val
    (List.ofFn u) (flatten A) gs (RamCenterUpdate.filled (entryValues u A gs hg D) k.val)
    k.isLt hnM (by simp) (by simpa using k.divNat.isLt) (by simpa using k.modNat.isLt) (by simp [flatten]) hg (by simp [RamCenterUpdate.filled])
    hM hD hDpos huk hvk hAk hα hβ hρ hδ hB
    σ ⟨hσu,hσA,hσg,hσnext,rfl,hσn,hσD⟩
  have hfields:FieldsAgree ["entry.k", "entry.count", "vec.n", "grid.D"] σ τ:=by
    intro x hx
    apply hr₁.frame_var
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals simp [shapeCoordinate,entryProduct,shapeDifference,roundedEntry,inflatedEntry,entryIndex,addDiagonal,loadLeft,loadRight,storeReduced,
      multiplyFraction,subtractFraction,negateRight,resultToRight,resultToLeft,
      RamRounding.roundFraction,addFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars]
  have hτk:τ.vars "entry.k"=k.val:=hfields _ (by simp)
  have hτcount:τ.vars "entry.count"=n * n:=(hfields _ (by simp)).trans hσcount
  have hτn:τ.vars "vec.n"=n:=(hfields _ (by simp)).trans hσn
  have hτD:τ.vars "grid.D"=D:=(hfields _ (by simp)).trans hσD
  have h1:1 < B:=by nlinarith
  have hkB:k.val < B:=k.isLt.trans hnB
  have hk1B:k.val + 1 < B:=lt_of_le_of_lt k.isLt hnB
  have hτkB:τ.vars "entry.k" < B:=hτk ▸ hkB
  have hsumB:Bop.add.apply (τ.vars "entry.k") 1 < B:=by simpa [Bop.apply,hτk] using hk1B
  have hr₂:Run B (.assign "entry.k" (.add (.var "entry.k") (.lit 1))) τ
      (τ.setVar "entry.k" (k.val + 1)) 4:=by
    exact Run.assign (by simpa [Bop.apply,hτk] using
      (evalB_bin (evalB_var hτkB) (evalB_lit h1) hsumB))
  have hnext:Represents "ell.nextshape"
      (RamCenterUpdate.filled (entryValues u A gs hg D) (k.val + 1)) τ:=by
    rw [← RamCenterUpdate.filled_step]
    simpa only [entryValues,shapeValues,flatten,List.getElem_ofFn,Fin.eta,
      Fin.divNat,Fin.modNat,Fin.ext_iff] using hτnext
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτu
  · simpa only [Represents,arrs_setVar] using hτA
  · simpa only [Represents,arrs_setVar] using hτg
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change k.val + 1≤ n * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτn
  · simpa using hτD
  · simp [k]

theorem shapeLoop_spec (B n M D:ℕ) (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (hM:1≤ M) (hnM:n * n≤ M)
    (hu:∀ j,Height (u j) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hD:D≤ M) (hDpos:0 < D) (hnB:n * n < B) (hnB':n < B)
    (hB:2 * (shapeCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.shape" (flatten A) σ∧
        Represents "ell.coeff" gs σ∧ Represents "ell.nextshape" (List.replicate (n * n) 0) σ∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      shapeLoop
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ∧
        Represents "ell.u" (List.ofFn u) τ∧ Represents "ell.shape" (flatten A) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10):=by
  have hlo:=Spec.forRangeZero "entry.k" "entry.count" (ShapeInvariant u A gs D hg) (n * n)
    (468 * (shapeCap M).size + 690 + 4) hnB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.1)
    (shapeStep_spec B n M D u A gs hg hM hnM hu hA hα hβ hρ hδ hD hDpos hnB hB)
  have hloop:Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.shape" (flatten A) σ∧
      Represents "ell.coeff" gs σ∧ Represents "ell.nextshape" (List.replicate (n * n) 0) σ∧
      σ.vars "entry.count"=n * n∧ σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      (.seq (.assign "entry.k" (.lit 0)) (.while (.lt (.var "entry.k") (.var "entry.count")) shapeStep))
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ∧
        Represents "ell.u" (List.ofFn u) τ∧ Represents "ell.shape" (flatten A) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 6):=by
    refine (hlo.pre ?_).post ?_
    · rintro σ ⟨hσu,hσA,hσg,hσnext,hσcount,hσn,hσD⟩
      simp_all [ShapeInvariant,Represents,RamCenterUpdate.filled_zero]
    · rintro σ τ _ ⟨hτ,hcounter⟩
      refine ⟨?_,hτ.1,hτ.2.1,hτ.2.2.1,hτ.2.2.2.2.2.2.1,hτ.2.2.2.2.2.2.2⟩
      change Represents "ell.nextshape" (List.ofFn (entryValues u A gs hg D)) τ
      simpa only [hcounter,RamCenterUpdate.filled_done] using hτ.2.2.2.1
  rintro σ ⟨hσu,hσA,hσg,hσnext,hσn,hσD⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "entry.k" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "entry.k") (Expr.var "entry.count")) shapeStep); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c1 (Env.vars σ "vec.n") (Env.vars σ "vec.n"); let c3:Env:=Env.setVar σ "entry.count" c2; let c4:Env→ Nat→ Prop:=Run B c0 c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c1 n n; let c7:Nat→ Nat:=c5 (c1 (c5 (c5 (c5 (c1 ((468:Nat)) (Nat.size (shapeCap M))) ((690:Nat))) ((4:Nat))) ((4:Nat))) c6); let c8:Nat:=c7 ((6:Nat)); let c9:Env→ Prop:=Represents "ell.nextshape" (@flatten n n (@shapeValues n u A gs hg D)); let c10:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (c9 σ') (And (Represents "ell.u" (@List.ofFn Rat n u) σ') (And (Represents "ell.shape" (@flatten n n A) σ') (And (Represents "ell.coeff" gs σ') (And (@Eq Nat (Env.vars σ' "vec.n") n) (@Eq Nat (Env.vars σ' "grid.D") D)))))); let c11:Nat:=c7 ((10:Nat)); let c12:Env→ Env→ Prop:=fun (x τ:Env) => And (c9 τ) (And (Represents "ell.u" (@List.ofFn Rat n u) τ) (And (Represents "ell.shape" (@flatten n n A) τ) (And (Represents "ell.coeff" gs τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (@Eq Nat (Env.vars τ "grid.D") D))))); let c13:Env→ Prop:=c12 σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B shapeLoop σ σ' c11) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:Env→ Prop:=Represents "ell.nextshape" (@List.replicate Rat c6 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c17:String→ Nat:=Env.vars c3; let c18:Nat:=c5 ((1:Nat)) (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c15) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.u" (@List.ofFn Rat n u) σ_1) (And (Represents "ell.shape" (@flatten n n A) σ_1) (And (Represents "ell.coeff" gs σ_1) (And (c16 σ_1) (And (@Eq Nat (Env.vars σ_1 "entry.count") c6) (And (@Eq Nat (Env.vars σ_1 "vec.n") n) (@Eq Nat (Env.vars σ_1 "grid.D") D))))))) c0 c12 c8 hloop c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (c9 w) (And (Represents "ell.u" (@List.ofFn Rat n u) w) (And (Represents "ell.shape" (@flatten n n A) w) (And (Represents "ell.coeff" gs w) (And (@Eq Nat (Env.vars w "vec.n") n) (@Eq Nat (Env.vars w "grid.D") D))))))) => let c0_1:Prop:=And (c9 w) (And (Represents "ell.u" (@List.ofFn Rat n u) w) (And (Represents "ell.shape" (@flatten n n A) w) (And (Represents "ell.coeff" gs w) (And (@Eq Nat (Env.vars w "vec.n") n) (@Eq Nat (Env.vars w "grid.D") D))))); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c15) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c14 w (@And.intro (Run B shapeLoop σ w c11) (c13 w) (RunStep.mono B shapeLoop σ w (c5 c18 c8) c11 (RunStep.seq B (Com.assign "entry.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))) c0 σ c3 w c18 c8 (RunStep.assign B σ "entry.count" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c2 (RunStep.eval_mul B σ (Expr.var "vec.n") (Expr.var "vec.n") (Env.vars σ "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4242_0_0_0)) (RunStep.eval_var B σ "vec.n" (?nAX_g4242_0_0_1)) ?_)) left) (?nAX_g4242_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4242_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4242_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4242_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hloop hlo
  all_goals simp_all [Represents]

theorem initializeShape_spec (B n:ℕ) (hnB:n < B) (hnnB:n * n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs "ell.nextshape.s").length=n * n∧
        (σ.arrs "ell.nextshape.n").length=n * n∧ (σ.arrs "ell.nextshape.d").length=n * n∧
        σ.vars "vec.n"=n)
      initializeShape
      (fun σ τ => Represents "ell.nextshape" (List.replicate (n * n) 0) τ∧
        τ.vars "vec.n"=n∧ τ.vars "grid.D"=σ.vars "grid.D" ∧
        ∀ a∉ ["ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"],τ.arrs a=σ.arrs a)
      (33 * (n * n) + 26):=by
  have hzero:=spec_with_write_frame ["shape.savedn", "grid.D"]
    (zeroRationalArray_spec B (n * n) "ell.nextshape" hnnB h1)
    (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      all_goals simp [zeroRationalArray,fillConstant,Lib.Fill.put,Com.wvars])
  rintro σ ⟨hσs,hσnum,hσd,hσn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=Env.vars (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) "vec.n"; let c2:Nat:=c0 c1 c1; let c3:Env:=Env.setVar (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) "vec.n" c2; let c4:Env→ Nat→ Prop:=Run B (zeroRationalArray "ell.nextshape") c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c0 n n; let c7:Nat→ Nat:=c5 (c0 ((33:Nat)) c6); let c8:Nat:=c7 ((18:Nat)); let c9:Env→ Prop:=Represents "ell.nextshape" (@List.replicate Rat c6 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c10:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.nextshape"; let c11:String:=c10 ".s"; let c12:String:=c10 ".n"; let c13:String:=c10 ".d"; let c14:String→ List Nat:=Env.arrs c3; let c15:Env→ Env→ Prop:=FieldsAgree (@List.cons String "shape.savedn" (@List.cons String "grid.D" (@List.nil String))); let c16:Env→ Prop:=c15 c3; let c17:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (And (c9 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c6) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c14 b)))) (And (c16 σ') (∀ a∉ Com.warrs (zeroRationalArray "ell.nextshape"), @Eq (List Nat) (Env.arrs σ' a) (c14 a)))); let c18:Nat:=c7 ((26:Nat)); let c19:Env→ Prop:=(fun (σ_1 τ:Env) => And (c9 τ) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "grid.D") (Env.vars σ_1 "grid.D")) (∀ a∉ @List.cons String "ell.nextshape.s" (@List.cons String "ell.nextshape.n" (@List.cons String "ell.nextshape.d" (@List.nil String))), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a))))) σ; let c20:Env→ Prop:=fun (σ':Env) => And (Run B initializeShape σ σ' c18) (c19 σ'); let c21:Prop:= @Exists Env c20; let c22:Nat→ Nat:=c5 ((1:Nat)); let c23:Nat:=c22 (Expr.size (Expr.var "vec.n")); let c24:Nat:=c22 (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); let c25:Nat:=c22 (Expr.size (Expr.var "shape.savedn")); let c26:Nat:=c5 c8 c25; let c27:Nat:=c5 c24 c26; let c28:Com:=Com.assign "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")); let c29:Com:=Com.seq (zeroRationalArray "ell.nextshape") (Com.assign "vec.n" (Expr.var "shape.savedn")); @Exists.casesOn Env c17 (fun (x:@Exists Env c17) => c21) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c11)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c12)) c6) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c13)) c6) (@Eq Nat (Env.vars σ_1 "vec.n") c6)))) (zeroRationalArray "ell.nextshape") (fun (σ_1 τ:Env) => And (And (c9 τ) (And (@Eq Nat (Env.vars τ "vec.n") c6) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (c15 σ_1 τ) (∀ a∉ Com.warrs (zeroRationalArray "ell.nextshape"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c8 hzero c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") c6) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c14 b)))) (And (c16 w) (∀ a∉ Com.warrs (zeroRationalArray "ell.nextshape"), @Eq (List Nat) (Env.arrs w a) (c14 a))))) => let c0_1:Prop:=And (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") c6) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c14 b)))) (And (c16 w) (∀ a∉ Com.warrs (zeroRationalArray "ell.nextshape"), @Eq (List Nat) (Env.arrs w a) (c14 a))); let c1_1:String→ Nat:=Env.vars (Env.setVar w "vec.n" (Env.vars w "shape.savedn")); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c21) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c20 (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) (@And.intro (Run B initializeShape σ (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) c18) (c19 (Env.setVar w "vec.n" (Env.vars w "shape.savedn"))) (RunStep.mono B initializeShape σ (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) (c5 c23 c27) c18 (RunStep.seq B (Com.assign "shape.savedn" (Expr.var "vec.n")) (Com.seq c28 c29) σ (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) c23 c27 (RunStep.assign B σ "shape.savedn" (Expr.var "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4244_0_0_0))) (RunStep.seq B c28 c29 (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) c3 (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) c24 c26 (RunStep.assign B (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) "vec.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c2 (RunStep.eval_mul B (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) (Expr.var "vec.n") (Expr.var "vec.n") c1 c1 (RunStep.eval_var B (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4244_0_0_1)) (RunStep.eval_var B (Env.setVar σ "shape.savedn" (Env.vars σ "vec.n")) "vec.n" (?nAX_g4244_0_0_2)) ?_)) (RunStep.seq B (zeroRationalArray "ell.nextshape") (Com.assign "vec.n" (Expr.var "shape.savedn")) c3 w (Env.setVar w "vec.n" (Env.vars w "shape.savedn")) c8 c25 left (RunStep.assign B w "vec.n" (Expr.var "shape.savedn") (Env.vars w "shape.savedn") (RunStep.eval_var B w "shape.savedn" ?_))))) (?nAX_g4244_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4244_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4244_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4244_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4244_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hzero
  all_goals simp_all [Represents,FieldsAgree]

theorem updateShape_spec (B n M D:ℕ) (u:Fin n→ ℚ) (A:Matrix (Fin n) (Fin n) ℚ)
    (gs:List ℚ) (hg:4 < gs.length) (hM:1≤ M) (hnM:n * n≤ M)
    (hu:∀ j,Height (u j) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hD:D≤ M) (hDpos:0 < D) (hnB:n * n < B) (hnB':n < B)
    (hB:2 * (shapeCap M) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.u" (List.ofFn u) σ∧ Represents "ell.shape" (flatten A) σ∧
        Represents "ell.coeff" gs σ∧ (σ.arrs "ell.nextshape.s").length=n * n∧
        (σ.arrs "ell.nextshape.n").length=n * n∧ (σ.arrs "ell.nextshape.d").length=n * n∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      updateShape
      (fun _ τ => Represents "ell.nextshape" (flatten (shapeValues u A gs hg D)) τ∧
        Represents "ell.u" (List.ofFn u) τ∧ Represents "ell.shape" (flatten A) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)):=by
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσu,hσA,hσg,hσs,hσnum,hσd,hσn,hσD⟩
  obtain ⟨τ,hr₁,hτnext,hτn,hτD,hτarr⟩:=initializeShape_spec B n hnB' hnB h1
    σ ⟨hσs,hσnum,hσd,hσn⟩
  have hτu:Represents "ell.u" (List.ofFn u) τ:=by
    simpa only [Represents,hτarr ("ell.u" ++ ".s") (by simp),
      hτarr ("ell.u" ++ ".n") (by simp),hτarr ("ell.u" ++ ".d") (by simp)] using hσu
  have hτA:Represents "ell.shape" (flatten A) τ:=by
    simpa only [Represents,hτarr ("ell.shape" ++ ".s") (by simp),
      hτarr ("ell.shape" ++ ".n") (by simp),hτarr ("ell.shape" ++ ".d") (by simp)] using hσA
  have hτg:Represents "ell.coeff" gs τ:=by
    simpa only [Represents,hτarr ("ell.coeff" ++ ".s") (by simp),
      hτarr ("ell.coeff" ++ ".n") (by simp),hτarr ("ell.coeff" ++ ".d") (by simp)] using hσg
  obtain ⟨υ,hr₂,hυ⟩:=shapeLoop_spec B n M D u A gs hg hM hnM hu hA hα hβ hρ hδ
    hD hDpos hnB hnB' hB τ ⟨hτu,hτA,hτg,hτnext,hτn,hτD.trans hσD⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

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

theorem verifiedShapeUpdate (B n M D:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (gs:List ℚ) (hg:4 < gs.length) (η:ℚ)
    (hM:1≤ M) (hnM:n * n≤ M) (hu:∀ j,Height ((A *ᵥ a) j) M)
    (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hD:D≤ M) (hDpos:0 < D) (hnB:n * n < B) (hnB':n < B)
    (hB:2 * (shapeCap M) ^ 2 + 3 < B)
    (hαValue:gs[0]=(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1))
    (hβValue:gs[1]=2 / (((n:ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a))))
    (hρValue:gs[3]=(1 + η) ^ 2) (hδValue:gs[4]=(n:ℚ) / D):
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ∧ Represents "ell.shape" (flatten A) σ∧
        Represents "ell.coeff" gs σ∧ (σ.arrs "ell.nextshape.s").length=n * n∧
        (σ.arrs "ell.nextshape.n").length=n * n∧ (σ.arrs "ell.nextshape.d").length=n * n∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      updateShape
      (fun _ τ => Represents "ell.nextshape" (flatten (EllipsoidCenter.roundedStepShape n A a D η)) τ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ∧ Represents "ell.shape" (flatten A) τ∧
        Represents "ell.coeff" gs τ∧ τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10)):=by
  have hv:=shapeValues_eq_roundedStepShape A a gs hg D η hαValue hβValue hρValue hδValue
  exact (updateShape_spec B n M D (A *ᵥ a) A gs hg hM hnM hu hA hα hβ hρ hδ hD hDpos hnB hnB' hB).post
    (fun _ _ _ h => by simpa only [hv] using h)

end Lax109476Proofs.RamShapeUpdate

end

theorem solution : ∀ (B n M D : Nat) (A : Matrix (Fin n) (Fin n) Rat) (a : Fin n → Rat) (gs : List Rat)
  (hg : @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length Rat gs)) (η : Rat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) M →
      (∀ (j : Fin n),
          Lax109476Proofs.RationalArithmeticBounds.Height
            (@Matrix.mulVec (Fin n) (Fin n) Rat
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                    (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
              (Fin.fintype n) A a j)
            M) →
        (∀ (i j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (A i j) M) →
          Lax109476Proofs.RationalArithmeticBounds.Height
              (@GetElem.getElem (List Rat) Nat Rat
                (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                (@List.instGetElemNatLtLength Rat) gs (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@Decidable.byContradiction
                  (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length Rat gs))
                  (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length Rat gs))
                  fun
                    (a :
                      Not
                        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@List.length Rat gs))) =>
                  Lax109476Proofs.RamShapeUpdate.shapeStep_spec._proof_1 n M gs hg a))
              M →
            Lax109476Proofs.RationalArithmeticBounds.Height
                (@GetElem.getElem (List Rat) Nat Rat
                  (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                  (@List.instGetElemNatLtLength Rat) gs (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Decidable.byContradiction
                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@List.length Rat gs))
                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (@List.length Rat gs))
                    fun
                      (a :
                        Not
                          (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@List.length Rat gs))) =>
                    Lax109476Proofs.RamShapeUpdate.shapeStep_spec._proof_2 n M gs hg a))
                M →
              Lax109476Proofs.RationalArithmeticBounds.Height
                  (@GetElem.getElem (List Rat) Nat Rat
                    (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                    (@List.instGetElemNatLtLength Rat) gs (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Decidable.byContradiction
                      (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@List.length Rat gs))
                      (Nat.decLt (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length Rat gs))
                      fun
                        (a :
                          Not
                            (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@List.length Rat gs))) =>
                      Lax109476Proofs.RamShapeUpdate.shapeStep_spec._proof_3 n M gs hg a))
                  M →
                Lax109476Proofs.RationalArithmeticBounds.Height
                    (@GetElem.getElem (List Rat) Nat Rat
                      (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                      (@List.instGetElemNatLtLength Rat) gs (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      hg)
                    M →
                  @LE.le Nat instLENat D M →
                    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
                      @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) B →
                        @LT.lt Nat instLTNat n B →
                          @LT.lt Nat instLTNat
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    (Lax109476Proofs.RamShapeCoordinate.shapeCap M)
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              B →
                            @Eq Rat
                                (@GetElem.getElem (List Rat) Nat Rat
                                  (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                                  (@List.instGetElemNatLtLength Rat) gs
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  (@Decidable.byContradiction
                                    (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@List.length Rat gs))
                                    (Nat.decLt (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                      (@List.length Rat gs))
                                    fun
                                      (a :
                                        Not
                                          (@LT.lt Nat instLTNat
                                            (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                            (@List.length Rat gs))) =>
                                    Lax109476Proofs.RamShapeUpdate.verifiedShapeUpdate._proof_1 B n M D gs hg a))
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@HPow.hPow Rat Nat Rat
                                    (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid)))
                                    (@Nat.cast Rat Rat.instNatCast n)
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub)
                                    (@HPow.hPow Rat Nat Rat
                                      (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid)))
                                      (@Nat.cast Rat Rat.instNatCast n)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))) →
                              @Eq Rat
                                  (@GetElem.getElem (List Rat) Nat Rat
                                    (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                                    (@List.instGetElemNatLtLength Rat) gs
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Decidable.byContradiction
                                      (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@List.length Rat gs))
                                      (Nat.decLt (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@List.length Rat gs))
                                      fun
                                        (a :
                                          Not
                                            (@LT.lt Nat instLTNat
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@List.length Rat gs))) =>
                                      Lax109476Proofs.RamShapeUpdate.verifiedShapeUpdate._proof_2 B n M D gs hg
                                        a))
                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                    (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                      (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                        (@Nat.cast Rat Rat.instNatCast n)
                                        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                                      (@dotProduct (Fin n) Rat (Fin.fintype n) Rat.instMul Rat.addCommMonoid a
                                        (@Matrix.mulVec (Fin n) (Fin n) Rat
                                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                                (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                          (Fin.fintype n) A a)))) →
                                @Eq Rat
                                    (@GetElem.getElem (List Rat) Nat Rat
                                      (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                                      (@List.instGetElemNatLtLength Rat) gs
                                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Decidable.byContradiction
                                        (@LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@List.length Rat gs))
                                        (Nat.decLt (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@List.length Rat gs))
                                        fun
                                          (a :
                                            Not
                                              (@LT.lt Nat instLTNat
                                                (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                (@List.length Rat gs))) =>
                                        Lax109476Proofs.RamShapeUpdate.verifiedShapeUpdate._proof_3 B n M D gs hg
                                          a))
                                    (@HPow.hPow Rat Nat Rat
                                      (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid)))
                                      (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                        (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) η)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                  @Eq Rat
                                      (@GetElem.getElem (List Rat) Nat Rat
                                        (fun (as : List Rat) (i : Nat) => @LT.lt Nat instLTNat i (@List.length Rat as))
                                        (@List.instGetElemNatLtLength Rat) gs
                                        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) hg)
                                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                        (@Nat.cast Rat Rat.instNatCast n) (@Nat.cast Rat Rat.instNatCast D)) →
                                    Lax808846Proofs.Reasoning.Spec B
                                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                                        And
                                          (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                                            (@List.ofFn Rat n
                                              (@Matrix.mulVec (Fin n) (Fin n) Rat
                                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                                      (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                                (Fin.fintype n) A a))
                                            σ)
                                          (And
                                            (Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                              (@Lax109476Proofs.RamMatrixStorage.flatten n n A) σ)
                                            (And (Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs σ)
                                              (And
                                                (@Eq Nat (@List.length Nat (σ.arrs "ell.nextshape.s"))
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                                (And
                                                  (@Eq Nat (@List.length Nat (σ.arrs "ell.nextshape.n"))
                                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                                  (And
                                                    (@Eq Nat (@List.length Nat (σ.arrs "ell.nextshape.d"))
                                                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                                    (And (@Eq Nat (σ.vars "vec.n") n)
                                                      (@Eq Nat (σ.vars "grid.D") D))))))))
                                      Lax109476Proofs.RamShapeUpdate.updateShape
                                      (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                        And
                                          (Lax109476Proofs.RamRationalArrays.Represents "ell.nextshape"
                                            (@Lax109476Proofs.RamMatrixStorage.flatten n n
                                              (Lax109476Proofs.EllipsoidCenter.roundedStepShape n A a D η))
                                            τ)
                                          (And
                                            (Lax109476Proofs.RamRationalArrays.Represents "ell.u"
                                              (@List.ofFn Rat n
                                                (@Matrix.mulVec (Fin n) (Fin n) Rat
                                                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Rat
                                                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Rat
                                                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Rat
                                                        (@CommRing.toNonUnitalCommRing Rat Rat.commRing))))
                                                  (Fin.fintype n) A a))
                                              τ)
                                            (And
                                              (Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                                (@Lax109476Proofs.RamMatrixStorage.flatten n n A) τ)
                                              (And (Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" gs τ)
                                                (And (@Eq Nat (τ.vars "vec.n") n) (@Eq Nat (τ.vars "grid.D") D))))))
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33)))
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                          (@OfNat.ofNat Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@OfNat.ofNat Nat (nat_lit 468) (instOfNatNat (nat_lit 468)))
                                                    (Lax109476Proofs.RamShapeCoordinate.shapeCap M).size)
                                                  (@OfNat.ofNat Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
                                                (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                              (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                                          (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) := @Lax109476Proofs.RamShapeUpdate.verifiedShapeUpdate
