-- Prove2me | solution 1 for Lax109476Proofs.RamFeasibilitySetup.setup_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:57.671811+00:00
-- url     : https://prove2.me/submissions/9fc3f715-7fcf-49a4-96f5-add6d5c18bba

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
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

theorem size_factorial_le (k:ℕ):Nat.size k.factorial≤ k * Nat.size k + 1:=
  (Nat.size_le_size (Nat.factorial_le_pow k)).trans (size_pow_le k k)

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

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

theorem certificate_cap_size (K L:ℕ) (hK:K≤ 2 * (L + 1)):
    Nat.size (K.factorial * (K * (2 ^ (2 * L)) ^ 2 + 1) ^ K)≤
      32 * (L + 1) ^ 2:=by
  let H:=2 ^ (2 * L)
  let B:=K * H ^ 2 + 1
  have hH:Nat.size H=2 * L + 1:=Nat.size_pow
  have hmul:=size_mul_le K (H ^ 2)
  have hpow:=size_pow_le H 2
  have hadd:=size_add_one_le (K * H ^ 2)
  have hks:=(size_le_self K).trans hK
  have hbs:Nat.size B≤ 6 * (L + 1):=by
    dsimp [B]
    omega
  have hf:=size_factorial_le K
  have hp:=size_pow_le B K
  have ht:=size_mul_le K.factorial (B ^ K)
  have h₁:K * Nat.size K≤ 4 * (L + 1) ^ 2:=by
    nlinarith [Nat.mul_le_mul hK hks]
  have h₂:K * Nat.size B≤ 12 * (L + 1) ^ 2:=by
    nlinarith [Nat.mul_le_mul hK hbs]
  change Nat.size (K.factorial * B ^ K)≤ _
  nlinarith [sq_nonneg (L:ℤ)]

end Lax109476Proofs.RationalSizeBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

theorem outerScale_pos (n B:ℕ):0 < outerScale n B:=by
  unfold outerScale
  positivity

theorem precisionDenominator_pos (m n H:ℕ):0 < precisionDenominator m n H:=by
  unfold precisionDenominator relaxationDenominator
  positivity

end Lax109476Proofs.NormalizedFeasibility

end

section

namespace Lax109476Proofs.IterationBudget

open RationalSizeBounds IntegerCertificates NormalizedFeasibility EllipsoidSequence

theorem ballExponent_polynomial (m n S:ℕ) (hdim:m + n≤ S):
    ballExponent m n (2 ^ (2 * S))≤ 128 * (S + 1) ^ 2:=by
  let H:=2 ^ (2 * S)
  let B:=coordinateCap m n H
  let G:=m * B + n * m * H * B
  let D:=2 * (G + 1)
  let R:=4 * (n + 1) * (B + 1)
  have hsH:Nat.size H=2 * S + 1:=Nat.size_pow
  have hsB:Nat.size B≤ 32 * (S + 1) ^ 2:=
    certificate_cap_size (2 * (m + n) + 2) S (by omega)
  have hm:=size_le_self m
  have hn:=size_le_self n
  have hmb:=size_mul_le m B
  have hnmhb:=size_mul_le (n * m * H) B
  have hnmh:=size_mul_le (n * m) H
  have hnm:=size_mul_le n m
  have hG:=size_add_le (m * B) (n * m * H * B)
  have hGp:=size_add_one_le G
  have hD:=size_mul_le 2 (G + 1)
  have hNH:=size_add_one_le (n * H)
  have hnH:=size_mul_le n H
  have hR:=size_mul_le (4 * (n + 1)) (B + 1)
  have hRn:=size_mul_le 4 (n + 1)
  have hn1:=size_add_one_le n
  have hB1:=size_add_one_le B
  have hN:=size_mul_le (D * (n * H + 1)) R
  have hND:=size_mul_le D (n * H + 1)
  have hs2:Nat.size 2=2:=rfl
  have hs4:Nat.size 4=3:=rfl
  have hbound:Nat.size (D * (n * H + 1) * R)≤ 3 * Nat.size B + 7 * S + 12:=by
    dsimp only [D,G,R] at *
    omega
  change Nat.size (D * (n * H + 1) * R)≤ _
  nlinarith

theorem thresholdSteps_polynomial (m n S:ℕ) (hdim:m + n≤ S):
    thresholdSteps n (ballExponent m n (2 ^ (2 * S)))≤ 1024 * (S + 1) ^ 4:=by
  have hE:=ballExponent_polynomial m n S hdim
  have hn:n≤ S:=by omega
  have hEn:=Nat.mul_le_mul hE hn
  have hstep:=Nat.mul_le_mul (by omega:4 * (n + 1)≤ 4 * (S + 1))
    (Nat.add_le_add_right hEn 1)
  unfold thresholdSteps
  nlinarith

end Lax109476Proofs.IterationBudget

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

theorem flatten_entry {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℚ) (i:Fin m) (j:Fin n):
    (flatten A)[i.val * n + j.val]'(by simp; exact row_index_lt i j)=A i j:=by
  have hk:(⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  simp only [flatten,List.getElem_ofFn]
  change A ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).1)
    ((finProdFinEquiv.symm (⟨i.val * n + j.val,row_index_lt i j⟩:Fin (m * n))).2)=_
  rw [hk,Equiv.symm_apply_apply]

theorem rows_of_represents {m n:ℕ} (a:String) (A:Matrix (Fin m) (Fin n) ℚ) (σ:Env)
    (h:Represents a (flatten A) σ):MatrixRows a A σ:=by
  rcases h with ⟨hs,hn,hd⟩
  intro i
  have hlen:i.val * n + n≤ m * n:=by
    have hm:=Nat.mul_le_mul_right n i.isLt
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hs] using hlen
  · simpa [hn] using hlen
  · simpa [hd] using hlen
  · intro j hj
    have hjn:j < n:=by simpa using hj
    have hk:i.val * n + j < (flatten A).length:=by
      simpa using row_index_lt i (⟨j,hjn⟩:Fin n)
    rw [hs,map_getD _ _ _ hk,flatten_entry A i ⟨j,hjn⟩]
    simp
  · intro j hj
    have hjn:j < n:=by simpa using hj
    have hk:i.val * n + j < (flatten A).length:=by
      simpa using row_index_lt i (⟨j,hjn⟩:Fin n)
    rw [hn,map_getD _ _ _ hk,flatten_entry A i ⟨j,hjn⟩]
    simp
  · intro j hj
    have hjn:j < n:=by simpa using hj
    have hk:i.val * n + j < (flatten A).length:=by
      simpa using row_index_lt i (⟨j,hjn⟩:Fin n)
    rw [hd,map_getD _ _ _ hk,flatten_entry A i ⟨j,hjn⟩]
    simp

end Lax109476Proofs.RamMatrixStorage

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

end Lax109476Proofs.RamEllipsoidUpdate

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

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax109476Proofs.RamPadSelector

end

section

namespace Lax109476Proofs.RamScaleCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds RamCopy

theorem prepareFactor_spec (B D:ℕ) (h1:1 < B) (hDB:D < B):
    Spec B (fun σ => σ.vars "scale.factor"=D) prepareFactor
      (fun _ τ => RightValue (D:ℚ) τ) 6:=by
  rintro σ hσD
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => RightValue (@Nat.cast Rat Rat.instNatCast D) τ) σ; let c1:Env:=Env.setVar σ "right.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "scale.factor"; let c3:Env:=Env.setVar c1 "right.n" c2; let c4:Env:=Env.setVar c3 "right.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c8:Nat:=c6 (Expr.size (Expr.var "scale.factor")); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c5 c8 c9; let c11:Com:=Com.assign "right.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B prepareFactor σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B prepareFactor σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B prepareFactor σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "scale.factor")) c11) σ c1 c4 c7 c10 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4491_0_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "scale.factor")) c11 c1 c3 c4 c8 c9 (RunStep.assign B c1 "right.n" (Expr.var "scale.factor") c2 (RunStep.eval_var B c1 "scale.factor" (?nAX_g4491_0_0_1))) (RunStep.assign B c3 "right.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g4491_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4491_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4491_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4491_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue,fractionValue]

end Lax109476Proofs.RamScaleCoordinate

end

section

namespace Lax109476Proofs.RamNormalizedEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds
open RamMatrixStorage IntegerEncoding NormalizedFeasibility RamScaleCoordinate

def entry {m n:ℕ} (P:Program ℤ m n) (R:ℕ) (i:Fin (m + n)) (j:Fin n):ℚ:=
  if hi:i.val < m then (P.A ⟨i.val,hi⟩ j:ℚ) * (R:ℚ)
  else if i.val - m=j.val then -(R:ℚ) else 0

theorem entry_eq {m n:ℕ} (P:Program ℤ m n) (R:ℕ) (i:Fin (m + n)) (j:Fin n):
    entry P R i j=(normalizedMatrix P R i j:ℚ):=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [entry,normalizedMatrix,i.isLt,mul_comm]
  · intro k
    simp [entry,normalizedMatrix,Fin.ext_iff,apply_ite]
    split_ifs <;> simp_all

theorem entry_height {m n:ℕ} (P:Program ℤ m n) (R M:ℕ)
    (hM:1≤ M) (hR:R≤ M) (hA:∀ i j, (P.A i j).natAbs≤ M)
    (i:Fin (m + n)) (j:Fin n):Height (entry P R i j) (M ^ 2):=by
  have hMM:M≤ M ^ 2:=by nlinarith
  have hnat:=height_nat R M hR hM
  unfold entry
  split_ifs with hi he
  · have hq:Height (P.A ⟨i.val,hi⟩ j:ℚ) M:=by simpa [Height] using And.intro (hA ⟨i.val,hi⟩ j) hM
    simpa only [pow_two] using height_mul _ _ M M hq hnat
  · exact height_mono _ (height_neg _ M hnat) hMM
  · exact height_mono _ height_zero (hM.trans hMM)

theorem negativeFactor_spec (B R:ℕ) (h1:1 < B) (hRB:R < B):
    Spec B (fun σ => σ.vars "cap.R"=R) negativeFactor
      (fun _ τ => FractionOutput (-(R:ℚ)) τ) 6:=by
  intro σ hσ
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@Nat.cast Rat Rat.instNatCast R)); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c3:Nat:=Env.vars c2 "cap.R"; let c4:Env:=Env.setVar c2 "rat.n" c3; let c5:Env:=Env.setVar c4 "rat.d" ((1:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "cap.R")); let c10:Nat:=c6 c9 c8; let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B negativeFactor σ σ' ((6:Nat))) (c1 σ')) c5 (@And.intro (Run B negativeFactor σ c5 ((6:Nat))) (c1 c5) (RunStep.mono B negativeFactor σ c5 (c6 c8 c10) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "cap.R")) c11) σ c2 c5 c8 c10 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "cap.R")) c11 c2 c4 c5 c9 c8 (RunStep.assign B c2 "rat.n" (Expr.var "cap.R") c3 (RunStep.eval_var B c2 "cap.R" (?nAX_g4499_0_0_0))) (RunStep.assign B c4 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1)))) (?nAX_g4499_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4499_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4499_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,fractionValue]

def fields:List String:= ["query.m", "query.n", "norm.row", "norm.col", "cap.R"]

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n R:ℕ) (P:Program ℤ m n) (i:Fin (m + n)) (j:Fin n)
    (hM:1≤ M) (hR:R≤ M) (hB:2 * M ^ 2 + 3 < B)
    (hdim:(m + n) * n + m + n + 1 < B) (hA:∀ i j, (P.A i j).natAbs≤ M):
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
        σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "norm.row"=i.val∧
        σ.vars "norm.col"=j.val∧ σ.vars "cap.R"=R)
      selectEntry (fun _ τ => FractionOutput (entry P R i j) τ) (72 * M.size + 100):=by
  have hMB:M < B:=by nlinarith
  have hRB:R < B:=hR.trans_lt hMB
  have h1:1 < B:=by nlinarith
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hmB:m < B:=by omega
  have hnB:n < B:=by omega
  have hzero:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hneg:=negativeFactor_spec B R h1 hRB
  have hz:Height (0:ℚ) M:=height_mono 0 height_zero hM
  have hdead:=multiply_spec B M 0 0 hB hz hz
  rintro σ ⟨hσA,hσm,hσn,hσi,hσj,hσR⟩
  by_cases hi:i.val < m
  · let ii:Fin m:= ⟨i.val,hi⟩
    let k:=i.val * n + j.val
    have hk:k < (RamMatrixStorage.flatten (rationalProgram P).A).length:=by
      simpa only [RamMatrixStorage.flatten,List.length_ofFn] using row_index_lt ii j
    have hmn:m * n≤ (m + n) * n:=Nat.mul_le_mul_right n (by omega)
    have hkB:k < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hk:k < m * n).trans (by omega)
    have hmulB:i.val * n < B:=by dsimp [k] at hkB; omega
    have he:(RamMatrixStorage.flatten (rationalProgram P).A)[k]=(P.A ii j:ℚ):=flatten_entry _ ii j
    have hq:Height (P.A ii j:ℚ) M:=by simpa [Height] using And.intro (hA ii j) hM
    have hrq:=height_nat R M hR hM
    have hload:=spec_with_fields fields
      (loadLeft_spec B "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) k hk h1 hkB
        (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    have hfactor:=spec_with_fields ["left.s", "left.n", "left.d"] (prepareFactor_spec B R h1 hRB)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hcanonical:fractionValue (rationalSign (P.A ii j:ℚ)) (P.A ii j).natAbs 1=(P.A ii j:ℚ):=by
      simpa using canonical_fractionValue (P.A ii j:ℚ)
    have hproduct:=multiply_spec B M (P.A ii j:ℚ) (R:ℚ) hB hq hrq
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c2 (c3 ((72:Nat)) (Nat.size M)); let c5:Nat:=c4 ((100:Nat)); let c6:Env→ Prop:=FractionOutput (@entry m n P R i j); let c7:Env→ Prop:=(fun (x τ:Env) => c6 τ) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' c5) (c7 σ'); let c9:Nat:=c3 (Env.vars σ "norm.row") (Env.vars σ "query.n"); let c10:Nat:=c2 c9 (Env.vars σ "norm.col"); let c11:Env:=Env.setVar σ "vec.i" c10; let c12:Env→ Nat→ Prop:=Run B (loadLeft "pad.A") c11; let c13:List Rat:= @flatten m n (@Program.A Rat m n (@rationalProgram m n P)); let c14:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c13 k hk); let c15:Env→ Prop:=FieldsAgree fields c11; let c16:String→ List Nat:=Env.arrs c11; let c17:Env→ Prop:=fun (σ':Env) => And (c12 σ' ((9:Nat))) (And (c14 σ') (And (c15 σ') (@Eq (String→ List Nat) (Env.arrs σ') c16))); let c18:Env→ Prop:=Represents "pad.A" c13; let c19:Env→ Env→ Prop:=FieldsAgree (@List.cons String "left.s" (@List.cons String "left.n" (@List.cons String "left.d" (@List.nil String)))); let c20:Nat:=c4 ((64:Nat)); let c21:Rat:= @Int.cast Rat Rat.instIntCast (@Program.A Int m n P ii j); let c22:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c21 (@Nat.cast Rat Rat.instNatCast R)); let c23:Env→ Prop:=LeftValue c21; let c24:Nat→ Nat:=c2 ((1:Nat)); let c25:Nat→ Nat:=c2 (c24 (Cond.size (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")))); let c26:Expr:=Expr.add (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col"); let c27:Nat:=c24 (Expr.size c26); let c28:Nat:=c24 (Expr.size (Expr.var "cap.R")); let c29:Nat→ Nat:=c2 c28; let c30:Nat:=c2 ((6:Nat)) c20; let c31:Nat:=c29 c30; let c32:Nat:=c2 ((9:Nat)) c31; let c33:Nat:=c2 c27 c32; let c34:Com:=Com.assign "vec.i" c26; let c35:Com:=Com.seq (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction); let c36:Com:=Com.seq (loadLeft "pad.A") c35; let c37:Com:=Com.seq c34 c36; let c38:Cond:=Cond.eq (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col"); let c39:Com:=Com.ite c38 negativeFactor (RamPadSelector.constantFraction ((0:Nat))); let c40:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c41:Prop:= @Eq Nat c40 (Env.vars σ "norm.col"); let c42:Prop:=Not c41; let c43:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c44:Nat:=Env.vars c43 "cap.R"; let c45:Env:=Env.setVar c43 "rat.n" c44; let c46:Env:=Env.setVar c45 "rat.d" ((1:Nat)); let c47:Nat→ Nat:=c2 (c24 (Cond.size c38)); let c48:Nat:=c24 (Expr.size (Expr.lit ((1:Nat)))); let c49:Nat:=c29 c48; let c50:Nat:=c2 c48 c49; let c51:Nat:=c47 c50; let c52:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c53:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c54:Env:=Env.setVar c53 "rat.n" ((0:Nat)); let c55:Env:=Env.setVar c54 "rat.d" ((1:Nat)); let c56:Nat:=c24 (Expr.size (Expr.lit ((0:Nat)))); let c57:Nat→ Nat:=c2 c56; let c58:Nat:=c57 c48; let c59:Nat:=c57 c58; let c60:Nat:=c47 c59; let c61:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c8) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c17 (fun (x:@Exists Env c17) => @Exists Env c8) (RunStep.use B (fun (σ_1:Env) => And (c18 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") k)) (loadLeft "pad.A") (fun (σ_1 τ:Env) => And (c14 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload c11 ?_) fun (w:Env) (h:And (c12 w ((9:Nat))) (And (c14 w) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)))) => let c0_1:Prop:=c12 w ((9:Nat)); let c1_1:Prop:=And (c14 w) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)); let c2_1:Env→ Nat→ Prop:=Run B prepareFactor (Env.setVar w "scale.factor" (Env.vars w "cap.R")); let c3_1:Env→ Prop:=c19 (Env.setVar w "scale.factor" (Env.vars w "cap.R")); let c4_1:String→ List Nat:=Env.arrs (Env.setVar w "scale.factor" (Env.vars w "cap.R")); let c5_1:Env→ Prop:=fun (σ':Env) => And (c2_1 σ' ((6:Nat))) (And (RightValue (@Nat.cast Rat Rat.instNatCast R) σ') (And (c3_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4_1))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c8) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c5_1 (fun (x:@Exists Env c5_1) => @Exists Env c8) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "scale.factor") R) prepareFactor (fun (σ_1 τ:Env) => And (RightValue (@Nat.cast Rat Rat.instNatCast R) τ) (And (c19 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hfactor (Env.setVar w "scale.factor" (Env.vars w "cap.R")) ?_) fun (w_1:Env) (h_1:And (c2_1 w_1 ((6:Nat))) (And (RightValue (@Nat.cast Rat Rat.instNatCast R) w_1) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)))) => let c0_2:Prop:=c2_1 w_1 ((6:Nat)); let c1_2:Prop:=And (RightValue (@Nat.cast Rat Rat.instNatCast R) w_1) (And (c3_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c4_1)); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_1 σ' c20) (c22 σ'); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => @Exists Env c8) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => @Exists Env c8) (RunStep.use B (fun (σ_1:Env) => And (c23 σ_1) (RightValue (@Nat.cast Rat Rat.instNatCast R) σ_1)) multiplyFraction (fun (x τ:Env) => c22 τ) c20 hproduct w_1 ?_) fun (w_2:Env) (h_2:And (Run B multiplyFraction w_1 w_2 c20) (c22 w_2)) => @And.casesOn (Run B multiplyFraction w_1 w_2 c20) (c22 w_2) (fun (x:And (Run B multiplyFraction w_1 w_2 c20) (c22 w_2)) => @Exists Env c8) h_2 fun (left_2:Run B multiplyFraction w_1 w_2 c20) (right_2:c22 w_2) => @Exists.intro Env c8 w_2 (@And.intro (Run B selectEntry σ w_2 c5) (c7 w_2) (RunStep.mono B selectEntry σ w_2 (c25 c33) c5 (RunStep.ite_true B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c37 c39 σ w_2 c33 (RunStep.cond_lt_true B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_0)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_0_0_1)) hcase) (RunStep.seq B c34 c36 σ c11 w_2 c27 c32 (RunStep.assign B σ "vec.i" c26 c10 (RunStep.eval_add B σ (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col") c9 (Env.vars σ "norm.col") (RunStep.eval_mul B σ (Expr.var "norm.row") (Expr.var "query.n") (Env.vars σ "norm.row") (Env.vars σ "query.n") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_2)) (RunStep.eval_var B σ "query.n" (?nAX_g4502_0_0_3)) ?_) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_0_0_4)) ?_)) (RunStep.seq B (loadLeft "pad.A") c35 c11 w w_2 ((9:Nat)) c31 left (RunStep.seq B (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction) w (Env.setVar w "scale.factor" (Env.vars w "cap.R")) w_2 c28 c30 (RunStep.assign B w "scale.factor" (Expr.var "cap.R") (Env.vars w "cap.R") (RunStep.eval_var B w "cap.R" ?_)) (RunStep.seq B prepareFactor multiplyFraction (Env.setVar w "scale.factor" (Env.vars w "cap.R")) w_1 w_2 ((6:Nat)) c20 left_1 left_2))))) (?nAX_g4502_0_0_5)) ?_)) fun (hcase:c1) => @Or.casesOn c41 c42 (fun (x:Or c41 c42) => @Exists Env c8) (Classical.em c41) (fun (hcase_1:c41) => @Exists.intro Env c8 c46 (@And.intro (Run B selectEntry σ c46 c5) (c7 c46) (RunStep.mono B selectEntry σ c46 (c25 c51) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c37 c39 σ c46 c51 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_6)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_0_0_7)) hcase) (RunStep.ite_true B c38 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ c46 c50 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c40 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_8)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_0_0_9)) (?nAX_g4502_0_0_10)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_0_0_11)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "cap.R")) c52) σ c43 c46 c48 c49 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "cap.R")) c52 c43 c45 c46 c28 c48 (RunStep.assign B c43 "rat.n" (Expr.var "cap.R") c44 (RunStep.eval_var B c43 "cap.R" (?nAX_g4502_0_0_12))) (RunStep.assign B c45 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c45 h1)))))) (?nAX_g4502_0_0_13)) ?_)) fun (hcase_1:c42) => @Exists.intro Env c8 c55 (@And.intro (Run B selectEntry σ c55 c5) (c7 c55) (RunStep.mono B selectEntry σ c55 (c25 c60) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c37 c39 σ c55 c60 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_14)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_0_0_15)) hcase) (RunStep.ite_false B c38 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ c55 c59 (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c40 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_0_0_16)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_0_0_17)) (?nAX_g4502_0_0_18)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_0_0_19)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c61 c52) σ c53 c55 c56 c58 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4502_0_0_20))) (RunStep.seq B c61 c52 c53 c54 c55 c56 c48 (RunStep.assign B c53 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c53 (?nAX_g4502_0_0_21))) (RunStep.assign B c54 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c54 h1)))))) (?nAX_g4502_0_0_22)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4502_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
    all_goals clear hload hfactor hproduct
    all_goals simp_all [fields,FieldsAgree,Represents,entry,k,ii,LeftOutput,
      LeftValue,RightValue,hcanonical,rationalSign_le_one]
    all_goals aesop
  · by_cases he:i.val - m=j.val
    · (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c2 (c3 ((72:Nat)) (Nat.size M)); let c5:Nat:=c4 ((100:Nat)); let c6:Env→ Prop:=FractionOutput (@entry m n P R i j); let c7:Env→ Prop:=(fun (x τ:Env) => c6 τ) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' c5) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Nat:=c3 (Env.vars σ "norm.row") (Env.vars σ "query.n"); let c11:Nat:=c2 c10 (Env.vars σ "norm.col"); let c12:Env:=Env.setVar σ "vec.i" c11; let c13:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "pad.A"; let c14:String:=c13 ".s"; let c15:Nat:=Env.vars c12 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c12 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c12 "left.s" c16; let c18:String:=c13 ".n"; let c19:Nat:=Env.vars c17 "vec.i"; let c20:Nat:= @List.getD Nat (Env.arrs c17 c18) c19 ((0:Nat)); let c21:Env:=Env.setVar c17 "left.n" c20; let c22:String:=c13 ".d"; let c23:Nat:=Env.vars c21 "vec.i"; let c24:Nat:= @List.getD Nat (Env.arrs c21 c22) c23 ((0:Nat)); let c25:Env:=Env.setVar c21 "left.d" c24; let c26:Nat:=Env.vars c25 "cap.R"; let c27:Env:=Env.setVar c25 "scale.factor" c26; let c28:Env:=Env.setVar c27 "right.s" ((0:Nat)); let c29:Nat:=Env.vars c28 "scale.factor"; let c30:Env:=Env.setVar c28 "right.n" c29; let c31:Env:=Env.setVar c30 "right.d" ((1:Nat)); let c32:Env→ Nat→ Prop:=Run B multiplyFraction c31; let c33:Nat:=c4 ((64:Nat)); let c34:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c35:Env→ Prop:=fun (σ':Env) => And (c32 σ' c33) (c34 σ'); let c36:Nat→ Nat:=c2 ((1:Nat)); let c37:Nat→ Nat:=c2 (c36 (Cond.size (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")))); let c38:Expr:=Expr.add (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col"); let c39:Nat:=c36 (Expr.size c38); let c40:Expr:=Expr.get c14 (Expr.var "vec.i"); let c41:Nat:=c36 (Expr.size c40); let c42:Expr:=Expr.get c18 (Expr.var "vec.i"); let c43:Nat:=c36 (Expr.size c42); let c44:Expr:=Expr.get c22 (Expr.var "vec.i"); let c45:Nat:=c36 (Expr.size c44); let c46:Nat:=c2 c43 c45; let c47:Nat:=c2 c41 c46; let c48:Nat:=c36 (Expr.size (Expr.var "cap.R")); let c49:Nat:=c36 (Expr.size (Expr.lit ((0:Nat)))); let c50:Nat→ Nat:=c2 c49; let c51:Nat:=c36 (Expr.size (Expr.var "scale.factor")); let c52:Nat:=c36 (Expr.size (Expr.lit ((1:Nat)))); let c53:Nat:=c2 c51 c52; let c54:Nat:=c50 c53; let c55:Nat:=c2 c54 c33; let c56:Nat:=c2 c48 c55; let c57:Nat:=c2 c47 c56; let c58:Nat:=c2 c39 c57; let c59:Com:=Com.assign "vec.i" c38; let c60:Com:=Com.seq (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction); let c61:Com:=Com.seq (loadLeft "pad.A") c60; let c62:Com:=Com.seq c59 c61; let c63:Cond:=Cond.eq (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col"); let c64:Com:=Com.ite c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))); let c65:Com:=Com.assign "left.n" c42; let c66:Com:=Com.assign "left.d" c44; let c67:Com:=Com.assign "right.d" (Expr.lit ((1:Nat))); let c68:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c69:Prop:= @Eq Nat c68 (Env.vars σ "norm.col"); let c70:Prop:=Not c69; let c71:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@Nat.cast Rat Rat.instNatCast R)); let c72:Env→ Prop:=fun (σ':Env) => And (Run B negativeFactor σ σ' ((6:Nat))) (c71 σ'); let c73:Nat→ Nat:=c2 (c36 (Cond.size c63)); let c74:Nat:=c73 ((6:Nat)); let c75:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c76:Env:=Env.setVar c75 "rat.n" ((0:Nat)); let c77:Env:=Env.setVar c76 "rat.d" ((1:Nat)); let c78:Nat:=c50 c52; let c79:Nat:=c50 c78; let c80:Nat:=c73 c79; let c81:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c82:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c9) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c35 (fun (x:@Exists Env c35) => c9) (RunStep.use B (fun (σ_1:Env) => And (LeftValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1) (RightValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1)) multiplyFraction (fun (x τ:Env) => c34 τ) c33 hdead c31 ?_) fun (w:Env) (h:And (c32 w c33) (c34 w)) => @And.casesOn (c32 w c33) (c34 w) (fun (x:And (c32 w c33) (c34 w)) => c9) h fun (left:c32 w c33) (right:c34 w) => @Exists.intro Env c8 w (@And.intro (Run B selectEntry σ w c5) (c7 w) (RunStep.mono B selectEntry σ w (c37 c58) c5 (RunStep.ite_true B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ w c58 (RunStep.cond_lt_true B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_0)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_1_0_1)) hcase) (RunStep.seq B c59 c61 σ c12 w c39 c57 (RunStep.assign B σ "vec.i" c38 c11 (RunStep.eval_add B σ (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col") c10 (Env.vars σ "norm.col") (RunStep.eval_mul B σ (Expr.var "norm.row") (Expr.var "query.n") (Env.vars σ "norm.row") (Env.vars σ "query.n") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_2)) (RunStep.eval_var B σ "query.n" (?nAX_g4502_1_0_3)) (?nAX_g4502_1_0_4)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_1_0_5)) (?nAX_g4502_1_0_6))) (RunStep.seq B (loadLeft "pad.A") c60 c12 c25 w c47 c56 (RunStep.seq B (Com.assign "left.s" c40) (Com.seq c65 c66) c12 c17 c25 c41 c46 (RunStep.assign B c12 "left.s" c40 c16 (RunStep.eval_get B c12 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c12 "vec.i" (?nAX_g4502_1_0_7)) (?nAX_g4502_1_0_8) (?nAX_g4502_1_0_9))) (RunStep.seq B c65 c66 c17 c21 c25 c43 c45 (RunStep.assign B c17 "left.n" c42 c20 (RunStep.eval_get B c17 c18 (Expr.var "vec.i") c19 (RunStep.eval_var B c17 "vec.i" (?nAX_g4502_1_0_10)) (?nAX_g4502_1_0_11) (?nAX_g4502_1_0_12))) (RunStep.assign B c21 "left.d" c44 c24 (RunStep.eval_get B c21 c22 (Expr.var "vec.i") c23 (RunStep.eval_var B c21 "vec.i" (?nAX_g4502_1_0_13)) (?nAX_g4502_1_0_14) (?nAX_g4502_1_0_15))))) (RunStep.seq B (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction) c25 c27 w c48 c55 (RunStep.assign B c25 "scale.factor" (Expr.var "cap.R") c26 (RunStep.eval_var B c25 "cap.R" (?nAX_g4502_1_0_16))) (RunStep.seq B prepareFactor multiplyFraction c27 c31 w c54 c33 (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "scale.factor")) c67) c27 c28 c31 c49 c53 (RunStep.assign B c27 "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c27 (?nAX_g4502_1_0_17))) (RunStep.seq B (Com.assign "right.n" (Expr.var "scale.factor")) c67 c28 c30 c31 c51 c52 (RunStep.assign B c28 "right.n" (Expr.var "scale.factor") c29 (RunStep.eval_var B c28 "scale.factor" (?nAX_g4502_1_0_18))) (RunStep.assign B c30 "right.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c30 h1)))) left))))) (?nAX_g4502_1_0_19)) ?_)) fun (hcase:c1) => @Or.casesOn c69 c70 (fun (x:Or c69 c70) => c9) (Classical.em c69) (fun (hcase_1:c69) => @Exists.casesOn Env c72 (fun (x:@Exists Env c72) => c9) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "cap.R") R) negativeFactor (fun (x τ:Env) => c71 τ) ((6:Nat)) hneg σ ?_) fun (w:Env) (h:And (Run B negativeFactor σ w ((6:Nat))) (c71 w)) => let c0_1:Prop:=Run B negativeFactor σ w ((6:Nat)); @And.casesOn c0_1 (c71 w) (fun (x:And c0_1 (c71 w)) => c9) h fun (left:c0_1) (right:c71 w) => @Exists.intro Env c8 w (@And.intro (Run B selectEntry σ w c5) (c7 w) (RunStep.mono B selectEntry σ w (c37 c74) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ w c74 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_20)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_1_0_21)) hcase) (RunStep.ite_true B c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c68 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_22)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_1_0_23)) (?nAX_g4502_1_0_24)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_1_0_25)) hcase_1) left)) (?nAX_g4502_1_0_26)) ?_)) fun (hcase_1:c70) => @Exists.intro Env c8 c77 (@And.intro (Run B selectEntry σ c77 c5) (c7 c77) (RunStep.mono B selectEntry σ c77 (c37 c80) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ c77 c80 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_27)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_1_0_28)) hcase) (RunStep.ite_false B c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ c77 c79 (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c68 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_1_0_29)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_1_0_30)) (?nAX_g4502_1_0_31)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_1_0_32)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c81 c82) σ c75 c77 c49 c78 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4502_1_0_33))) (RunStep.seq B c81 c82 c75 c76 c77 c49 c52 (RunStep.assign B c75 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c75 (?nAX_g4502_1_0_34))) (RunStep.assign B c76 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c76 h1)))))) (?nAX_g4502_1_0_35)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4502_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals simp_all [entry,Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c2 (c3 ((72:Nat)) (Nat.size M)); let c5:Nat:=c4 ((100:Nat)); let c6:Env→ Prop:=FractionOutput (@entry m n P R i j); let c7:Env→ Prop:=(fun (x τ:Env) => c6 τ) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' c5) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Nat:=c3 (Env.vars σ "norm.row") (Env.vars σ "query.n"); let c11:Nat:=c2 c10 (Env.vars σ "norm.col"); let c12:Env:=Env.setVar σ "vec.i" c11; let c13:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "pad.A"; let c14:String:=c13 ".s"; let c15:Nat:=Env.vars c12 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c12 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c12 "left.s" c16; let c18:String:=c13 ".n"; let c19:Nat:=Env.vars c17 "vec.i"; let c20:Nat:= @List.getD Nat (Env.arrs c17 c18) c19 ((0:Nat)); let c21:Env:=Env.setVar c17 "left.n" c20; let c22:String:=c13 ".d"; let c23:Nat:=Env.vars c21 "vec.i"; let c24:Nat:= @List.getD Nat (Env.arrs c21 c22) c23 ((0:Nat)); let c25:Env:=Env.setVar c21 "left.d" c24; let c26:Nat:=Env.vars c25 "cap.R"; let c27:Env:=Env.setVar c25 "scale.factor" c26; let c28:Env:=Env.setVar c27 "right.s" ((0:Nat)); let c29:Nat:=Env.vars c28 "scale.factor"; let c30:Env:=Env.setVar c28 "right.n" c29; let c31:Env:=Env.setVar c30 "right.d" ((1:Nat)); let c32:Env→ Nat→ Prop:=Run B multiplyFraction c31; let c33:Nat:=c4 ((64:Nat)); let c34:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c35:Env→ Prop:=fun (σ':Env) => And (c32 σ' c33) (c34 σ'); let c36:Nat→ Nat:=c2 ((1:Nat)); let c37:Nat→ Nat:=c2 (c36 (Cond.size (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")))); let c38:Expr:=Expr.add (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col"); let c39:Nat:=c36 (Expr.size c38); let c40:Expr:=Expr.get c14 (Expr.var "vec.i"); let c41:Nat:=c36 (Expr.size c40); let c42:Expr:=Expr.get c18 (Expr.var "vec.i"); let c43:Nat:=c36 (Expr.size c42); let c44:Expr:=Expr.get c22 (Expr.var "vec.i"); let c45:Nat:=c36 (Expr.size c44); let c46:Nat:=c2 c43 c45; let c47:Nat:=c2 c41 c46; let c48:Nat:=c36 (Expr.size (Expr.var "cap.R")); let c49:Nat→ Nat:=c2 c48; let c50:Nat:=c36 (Expr.size (Expr.lit ((0:Nat)))); let c51:Nat:=c36 (Expr.size (Expr.var "scale.factor")); let c52:Nat:=c36 (Expr.size (Expr.lit ((1:Nat)))); let c53:Nat:=c2 c51 c52; let c54:Nat:=c2 c50 c53; let c55:Nat:=c2 c54 c33; let c56:Nat:=c49 c55; let c57:Nat:=c2 c47 c56; let c58:Nat:=c2 c39 c57; let c59:Com:=Com.assign "vec.i" c38; let c60:Com:=Com.seq (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction); let c61:Com:=Com.seq (loadLeft "pad.A") c60; let c62:Com:=Com.seq c59 c61; let c63:Cond:=Cond.eq (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col"); let c64:Com:=Com.ite c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))); let c65:Com:=Com.assign "left.n" c42; let c66:Com:=Com.assign "left.d" c44; let c67:Com:=Com.assign "right.d" (Expr.lit ((1:Nat))); let c68:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "norm.row") (Env.vars σ "query.m"); let c69:Prop:= @Eq Nat c68 (Env.vars σ "norm.col"); let c70:Prop:=Not c69; let c71:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c72:Nat:=Env.vars c71 "cap.R"; let c73:Env:=Env.setVar c71 "rat.n" c72; let c74:Env:=Env.setVar c73 "rat.d" ((1:Nat)); let c75:Nat→ Nat:=c2 (c36 (Cond.size c63)); let c76:Nat:=c49 c52; let c77:Nat:=c2 c52 c76; let c78:Nat:=c75 c77; let c79:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c80:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c81:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c82:Env→ Prop:=fun (σ':Env) => And (c80 σ' ((6:Nat))) (c81 σ'); let c83:Nat:=c75 ((6:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c9) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c35 (fun (x:@Exists Env c35) => c9) (RunStep.use B (fun (σ_1:Env) => And (LeftValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1) (RightValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1)) multiplyFraction (fun (x τ:Env) => c34 τ) c33 hdead c31 ?_) fun (w:Env) (h:And (c32 w c33) (c34 w)) => @And.casesOn (c32 w c33) (c34 w) (fun (x:And (c32 w c33) (c34 w)) => c9) h fun (left:c32 w c33) (right:c34 w) => @Exists.intro Env c8 w (@And.intro (Run B selectEntry σ w c5) (c7 w) (RunStep.mono B selectEntry σ w (c37 c58) c5 (RunStep.ite_true B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ w c58 (RunStep.cond_lt_true B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_0)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_2_0_1)) hcase) (RunStep.seq B c59 c61 σ c12 w c39 c57 (RunStep.assign B σ "vec.i" c38 c11 (RunStep.eval_add B σ (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) (Expr.var "norm.col") c10 (Env.vars σ "norm.col") (RunStep.eval_mul B σ (Expr.var "norm.row") (Expr.var "query.n") (Env.vars σ "norm.row") (Env.vars σ "query.n") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_2)) (RunStep.eval_var B σ "query.n" (?nAX_g4502_2_0_3)) (?nAX_g4502_2_0_4)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_2_0_5)) (?nAX_g4502_2_0_6))) (RunStep.seq B (loadLeft "pad.A") c60 c12 c25 w c47 c56 (RunStep.seq B (Com.assign "left.s" c40) (Com.seq c65 c66) c12 c17 c25 c41 c46 (RunStep.assign B c12 "left.s" c40 c16 (RunStep.eval_get B c12 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c12 "vec.i" (?nAX_g4502_2_0_7)) (?nAX_g4502_2_0_8) (?nAX_g4502_2_0_9))) (RunStep.seq B c65 c66 c17 c21 c25 c43 c45 (RunStep.assign B c17 "left.n" c42 c20 (RunStep.eval_get B c17 c18 (Expr.var "vec.i") c19 (RunStep.eval_var B c17 "vec.i" (?nAX_g4502_2_0_10)) (?nAX_g4502_2_0_11) (?nAX_g4502_2_0_12))) (RunStep.assign B c21 "left.d" c44 c24 (RunStep.eval_get B c21 c22 (Expr.var "vec.i") c23 (RunStep.eval_var B c21 "vec.i" (?nAX_g4502_2_0_13)) (?nAX_g4502_2_0_14) (?nAX_g4502_2_0_15))))) (RunStep.seq B (Com.assign "scale.factor" (Expr.var "cap.R")) (Com.seq prepareFactor multiplyFraction) c25 c27 w c48 c55 (RunStep.assign B c25 "scale.factor" (Expr.var "cap.R") c26 (RunStep.eval_var B c25 "cap.R" (?nAX_g4502_2_0_16))) (RunStep.seq B prepareFactor multiplyFraction c27 c31 w c54 c33 (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "scale.factor")) c67) c27 c28 c31 c50 c53 (RunStep.assign B c27 "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c27 (?nAX_g4502_2_0_17))) (RunStep.seq B (Com.assign "right.n" (Expr.var "scale.factor")) c67 c28 c30 c31 c51 c52 (RunStep.assign B c28 "right.n" (Expr.var "scale.factor") c29 (RunStep.eval_var B c28 "scale.factor" (?nAX_g4502_2_0_18))) (RunStep.assign B c30 "right.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c30 h1)))) left))))) (?nAX_g4502_2_0_19)) ?_)) fun (hcase:c1) => @Or.casesOn c69 c70 (fun (x:Or c69 c70) => c9) (Classical.em c69) (fun (hcase_1:c69) => @Exists.intro Env c8 c74 (@And.intro (Run B selectEntry σ c74 c5) (c7 c74) (RunStep.mono B selectEntry σ c74 (c37 c78) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ c74 c78 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_20)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_2_0_21)) hcase) (RunStep.ite_true B c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ c74 c77 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c68 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_22)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_2_0_23)) (?nAX_g4502_2_0_24)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_2_0_25)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "cap.R")) c79) σ c71 c74 c52 c76 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "cap.R")) c79 c71 c73 c74 c48 c52 (RunStep.assign B c71 "rat.n" (Expr.var "cap.R") c72 (RunStep.eval_var B c71 "cap.R" (?nAX_g4502_2_0_26))) (RunStep.assign B c73 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c73 h1)))))) (?nAX_g4502_2_0_27)) ?_)) fun (hcase_1:c70) => @Exists.casesOn Env c82 (fun (x:@Exists Env c82) => c9) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c81 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c80 w ((6:Nat))) (c81 w)) => let c0_1:Prop:=c80 w ((6:Nat)); @And.casesOn c0_1 (c81 w) (fun (x:And c0_1 (c81 w)) => c9) h fun (left:c0_1) (right:c81 w) => @Exists.intro Env c8 w (@And.intro (Run B selectEntry σ w c5) (c7 w) (RunStep.mono B selectEntry σ w (c37 c83) c5 (RunStep.ite_false B (Cond.lt (Expr.var "norm.row") (Expr.var "query.m")) c62 c64 σ w c83 (RunStep.cond_lt_false B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_28)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_2_0_29)) hcase) (RunStep.ite_false B c63 negativeFactor (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "norm.row") (Expr.var "query.m")) (Expr.var "norm.col") c68 (Env.vars σ "norm.col") (RunStep.eval_sub B σ (Expr.var "norm.row") (Expr.var "query.m") (Env.vars σ "norm.row") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.row" (?nAX_g4502_2_0_30)) (RunStep.eval_var B σ "query.m" (?nAX_g4502_2_0_31)) (?nAX_g4502_2_0_32)) (RunStep.eval_var B σ "norm.col" (?nAX_g4502_2_0_33)) hcase_1) left)) (?nAX_g4502_2_0_34)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4502_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4502_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals simp_all [entry,Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamNormalizedEntry

end

section

namespace Lax109476Proofs.RamNormalizedMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamNormalizedEntry RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def values {m n:ℕ} (P:Program ℤ m n) (R:ℕ):Fin ((m + n) * n)→ ℚ:=
  fun k => RamNormalizedEntry.entry P R k.divNat k.modNat

theorem values_eq {m n:ℕ} (P:Program ℤ m n) (R:ℕ):
    List.ofFn (values P R)=RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j:ℚ)):=by
  unfold values RamMatrixStorage.flatten
  congr 1
  funext k
  exact RamNormalizedEntry.entry_eq P R k.divNat k.modNat

def fields:List String:= ["norm.k", "norm.count", "query.m", "query.n", "cap.R"]

set_option maxHeartbeats 0 in
theorem normalizeCoordinate_spec (B M m n:ℕ) (P:Program ℤ m n) (R:ℕ)
    (k:Fin ((m + n) * n)) (ys:List ℚ) (hy:k.val < ys.length)
    (hM:1≤ M) (hR:R≤ M) (hdim:(m + n) * n + m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M):
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧ Represents "search.rows" ys σ∧
        σ.vars "norm.k"=k.val∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.R"=R)
      normalizeCoordinate
      (fun _ τ => Represents "search.rows" (ys.set k.val (values P R k)) τ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ∧ τ.vars "norm.k"=k.val∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.R"=R) (72 * M.size + 140):=by
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have h1:1 < B:=by omega
  have h2:2 < B:=by nlinarith
  have hmB:m < B:=by omega
  have hnB:n < B:=by omega
  have hmn:m * n≤ (m + n) * n:=Nat.mul_le_mul_right n (by omega)
  have hmnB:m * n < B:=by omega
  have hdivB:k.val / n < B:=(Nat.div_le_self _ _).trans_lt hkB
  have hmulB:(k.val / n) * n < B:=(Nat.div_mul_le_self _ _).trans_lt hkB
  have hmodB:k.val - (k.val / n) * n < B:=(Nat.sub_le _ _).trans_lt hkB
  have hmod:k.val - (k.val / n) * n=k.val % n:=by
    simpa [Nat.mul_comm] using (show k.val % n=k.val - n * (k.val / n)
      from Nat.mod_eq_sub_mul_div).symm
  have hMB:M < B:=by nlinarith
  have hM2B:M ^ 2 < B:=by omega
  have hq:=RamNormalizedEntry.entry_height P R M hM hR hA k.divNat k.modNat
  have hselect:=spec_with_fields fields
    (RamNormalizedEntry.selectEntry_spec B M m n R P k.divNat k.modNat hM hR hB hdim hA)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore:=spec_with_write_frame fields
    (storeReduced_spec B "search.rows" ys (values P R k) k.val hy h1 hkB
      (hq.1.trans_lt hM2B) (hq.2.trans_lt hM2B))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA,hσy,hσk,hσm,hσn,hσR⟩
  (expose_names;
    (refine let c0:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "norm.k") (Env.vars σ "query.n"); let c1:Env:=Env.setVar σ "norm.row" c0; let c2:String→ Nat:=Env.vars c1; let c3:Nat:=c2 "norm.k"; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c2 "norm.row"; let c6:Nat:=c2 "query.n"; let c7:Nat:=c4 c5 c6; let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c3 c7; let c9:Env:=Env.setVar c1 "norm.col" c8; let c10:Env→ Nat→ Prop:=Run B selectEntry c9; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 (c4 ((72:Nat)) (Nat.size M)); let c13:Nat:=c12 ((100:Nat)); let c14:Nat:=c11 m n; let c15:Fin c14:= @Fin.divNat c14 n k; let c16:Fin n:= @Fin.modNat c14 n k; let c17:Env→ Prop:=FractionOutput (@entry m n P R c15 c16); let c18:Env→ Prop:=FieldsAgree fields c9; let c19:String→ List Nat:=Env.arrs c9; let c20:Env→ Prop:=fun (σ':Env) => And (c10 σ' c13) (And (c17 σ') (And (c18 σ') (@Eq (String→ List Nat) (Env.arrs σ') c19))); let c21:Nat:=c12 ((140:Nat)); let c22:Nat:= @Fin.val (c4 c14 n) k; let c23:Env→ Prop:=Represents "search.rows" (@List.set Rat ys c22 (@values m n P R k)); let c24:Env→ Prop:=Represents "pad.A" (@flatten m n (@Program.A Rat m n (@rationalProgram m n P))); let c25:Env→ Prop:=(fun (x τ:Env) => And (c23 τ) (And (c24 τ) (And (@Eq Nat (Env.vars τ "norm.k") c22) (And (@Eq Nat (Env.vars τ "query.m") m) (And (@Eq Nat (Env.vars τ "query.n") n) (@Eq Nat (Env.vars τ "cap.R") R)))))) σ; let c26:Env→ Prop:=fun (σ':Env) => And (Run B normalizeCoordinate σ σ' c21) (c25 σ'); let c27:Prop:= @Exists Env c26; let c28:Nat:= @Fin.val c14 c15; let c29:Nat:= @Fin.val n c16; let c30:String→ Nat:=Env.vars c9; let c31:Env→ Prop:=FractionOutput (@values m n P R k); let c32:Nat→ Nat:=c11 ((1:Nat)); let c33:Nat:=c32 (Expr.size (Expr.div (Expr.var "norm.k") (Expr.var "query.n"))); let c34:Expr:=Expr.sub (Expr.var "norm.k") (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")); let c35:Nat:=c32 (Expr.size c34); let c36:Nat:=c32 (Expr.size (Expr.var "norm.k")); let c37:Nat:=c11 c36 ((13:Nat)); let c38:Nat:=c11 c13 c37; let c39:Nat:=c11 c35 c38; let c40:Com:=Com.assign "norm.col" c34; let c41:Com:=Com.seq (Com.assign "vec.i" (Expr.var "norm.k")) (storeReduced "search.rows"); let c42:Com:=Com.seq selectEntry c41; @Exists.casesOn Env c20 (fun (x:@Exists Env c20) => c27) (RunStep.use B (fun (σ_1:Env) => And (c24 σ_1) (And (@Eq Nat (Env.vars σ_1 "query.m") m) (And (@Eq Nat (Env.vars σ_1 "query.n") n) (And (@Eq Nat (Env.vars σ_1 "norm.row") c28) (And (@Eq Nat (Env.vars σ_1 "norm.col") c29) (@Eq Nat (Env.vars σ_1 "cap.R") R)))))) selectEntry (fun (σ_1 τ:Env) => And (c17 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c13 hselect c9 ?_) fun (w:Env) (h:And (c10 w c13) (And (c17 w) (And (c18 w) (@Eq (String→ List Nat) (Env.arrs w) c19)))) => let c0_1:Prop:=And (c17 w) (And (c18 w) (@Eq (String→ List Nat) (Env.arrs w) c19)); let c1_1:Env→ Nat→ Prop:=Run B (storeReduced "search.rows") (Env.setVar w "vec.i" (Env.vars w "norm.k")); let c2_1:Env→ Prop:=FieldsAgree fields (Env.setVar w "vec.i" (Env.vars w "norm.k")); let c3_1:Env→ Prop:=fun (σ':Env) => And (c1_1 σ' ((13:Nat))) (And (c23 σ') (And (c2_1 σ') (∀ a∉ Com.warrs (storeReduced "search.rows"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a)))); @And.casesOn (c10 w c13) c0_1 (fun (x:And (c10 w c13) c0_1) => c27) h fun (left:c10 w c13) (right:c0_1) => @Exists.casesOn Env c3_1 (fun (x:@Exists Env c3_1) => c27) (RunStep.use B (fun (σ_1:Env) => And (Represents "search.rows" ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") c22) (c31 σ_1))) (storeReduced "search.rows") (fun (σ_1 τ:Env) => And (c23 τ) (And (FieldsAgree fields σ_1 τ) (∀ a∉ Com.warrs (storeReduced "search.rows"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore (Env.setVar w "vec.i" (Env.vars w "norm.k")) ?_) fun (w_1:Env) (h_1:And (c1_1 w_1 ((13:Nat))) (And (c23 w_1) (And (c2_1 w_1) (∀ a∉ Com.warrs (storeReduced "search.rows"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a))))) => let c0_2:Prop:=c1_1 w_1 ((13:Nat)); let c1_2:Prop:=And (c23 w_1) (And (c2_1 w_1) (∀ a∉ Com.warrs (storeReduced "search.rows"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c27) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c26 w_1 (@And.intro (Run B normalizeCoordinate σ w_1 c21) (c25 w_1) (RunStep.mono B normalizeCoordinate σ w_1 (c11 c33 c39) c21 (RunStep.seq B (Com.assign "norm.row" (Expr.div (Expr.var "norm.k") (Expr.var "query.n"))) (Com.seq c40 c42) σ c1 w_1 c33 c39 (RunStep.assign B σ "norm.row" (Expr.div (Expr.var "norm.k") (Expr.var "query.n")) c0 (RunStep.eval_div B σ (Expr.var "norm.k") (Expr.var "query.n") (Env.vars σ "norm.k") (Env.vars σ "query.n") (RunStep.eval_var B σ "norm.k" (?nAX_g4507_0_0_0)) (RunStep.eval_var B σ "query.n" (?nAX_g4507_0_0_1)) ?_)) (RunStep.seq B c40 c42 c1 c9 w_1 c35 c38 (RunStep.assign B c1 "norm.col" c34 c8 (RunStep.eval_sub B c1 (Expr.var "norm.k") (Expr.mul (Expr.var "norm.row") (Expr.var "query.n")) c3 c7 (RunStep.eval_var B c1 "norm.k" (?nAX_g4507_0_0_2)) (RunStep.eval_mul B c1 (Expr.var "norm.row") (Expr.var "query.n") c5 c6 (RunStep.eval_var B c1 "norm.row" ?_) (RunStep.eval_var B c1 "query.n" (?nAX_g4507_0_0_3)) ?_) (?nAX_g4507_0_0_4))) (RunStep.seq B selectEntry c41 c9 w w_1 c13 c37 left (RunStep.seq B (Com.assign "vec.i" (Expr.var "norm.k")) (storeReduced "search.rows") w (Env.setVar w "vec.i" (Env.vars w "norm.k")) w_1 c36 ((13:Nat)) (RunStep.assign B w "vec.i" (Expr.var "norm.k") (Env.vars w "norm.k") (RunStep.eval_var B w "norm.k" ?_)) left_1)))) (?nAX_g4507_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4507_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4507_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4507_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4507_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4507_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4507_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hselect hstore
  all_goals simp_all [fields,FieldsAgree,Represents,values,Fin.divNat,Fin.modNat,
    storeReduced,Com.warrs]
  all_goals aesop

def Invariant {m n:ℕ} (P:Program ℤ m n) (R:ℕ) (σ:Env):Prop:=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
    Represents "search.rows" (filled (values P R) (σ.vars "norm.k")) σ∧
    σ.vars "norm.k" ≤ (m + n) * n∧ σ.vars "norm.count"=(m + n) * n∧
    σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.R"=R

theorem normalizeStep_spec (B M m n:ℕ) (P:Program ℤ m n) (R:ℕ)
    (hM:1≤ M) (hR:R≤ M) (hdim:(m + n) * n + m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M):
    Spec B (fun σ => Invariant P R σ∧ σ.vars "norm.k" < (m + n) * n) normalizeStep
      (fun σ τ => Invariant P R τ∧ τ.vars "norm.k"=σ.vars "norm.k" + 1) (72 * M.size + 144):=by
  rintro σ ⟨⟨hσA,hσp,hσkN,hσcount,hσm,hσn,hσR⟩,hσk⟩
  let k:Fin ((m + n) * n):= ⟨σ.vars "norm.k",hσk⟩
  obtain ⟨τ,hr₁,hτp,hτA,hτk,hτm,hτn,hτR⟩:=normalizeCoordinate_spec B M m n P R k
    (filled (values P R) k.val) (by simpa only [filled,List.length_ofFn] using k.isLt) hM hR hdim hB hA σ ⟨hσA,hσp,rfl,hσm,hσn,hσR⟩
  have hτcount:=(hr₁.frame_var "norm.count" (by decide)).trans hσcount
  have h1:1 < B:=by omega
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have hi1B:k.val + 1 < B:=lt_of_le_of_lt k.isLt (by omega)
  have hr₂:Run B (.assign "norm.k" (.add (.var "norm.k") (.lit 1))) τ
      (τ.setVar "norm.k" (k.val + 1)) 4:=by
    exact Run.assign (by simpa only [hτk,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=τ) (x:= "norm.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "norm.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled:Represents "search.rows" (filled (values P R) (k.val + 1)) τ:=by
    rw [← filled_step]
    exact hτp
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτA
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change k.val + 1≤ (m + n) * n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simpa using hτR
  · simp [k]

theorem normalizeLoop_spec (B M m n:ℕ) (P:Program ℤ m n) (R:ℕ)
    (hM:1≤ M) (hR:R≤ M) (hdim:(m + n) * n + m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M):
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
        Represents "search.rows" (List.replicate ((m + n) * n) 0) σ∧
        σ.vars "norm.count"=(m + n) * n∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.R"=R)
      normalizeLoop
      (fun _ τ => Represents "search.rows" (RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j:ℚ))) τ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ∧ τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.R"=R)
      ((72 * M.size + 148) * ((m + n) * n) + 6):=by
  have hlo:=Spec.forRangeZero "norm.k" "norm.count" (Invariant P R) ((m + n) * n) (72 * M.size + 144)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (normalizeStep_spec B M m n P R hM hR hdim hB hA)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hA,hp,hcount,hm,hn,hR⟩
    simp_all [Invariant,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hk⟩
    refine ⟨?_,hτ.1,hτ.2.2.2.2.1,hτ.2.2.2.2.2.1,hτ.2.2.2.2.2.2⟩
    simpa only [hk,filled_done,values_eq] using hτ.2.1

set_option maxHeartbeats 0 in
theorem normalizeMatrix_spec (B M m n:ℕ) (P:Program ℤ m n) (R:ℕ)
    (hM:1≤ M) (hR:R≤ M) (hdim:(m + n) * n + m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M):
    Spec B (fun σ => Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
        Extents "search.rows" ((m + n) * n) σ∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.R"=R)
      normalizeMatrix
      (fun _ τ => Represents "search.rows" (RamMatrixStorage.flatten (fun i j => (normalizedMatrix P R i j:ℚ))) τ∧
        Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) τ∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.R"=R)
      ((72 * M.size + 181) * ((m + n) * n) + 36):=by
  have h1:1 < B:=by omega
  have h2:2 < B:=by nlinarith
  have hmB:m < B:=by omega
  have hnB:n < B:=by omega
  have hcountB:(m + n) * n < B:=by omega
  have hsumB:m + n < B:=by omega
  have hzero:=spec_with_write_frame ["query.m", "query.n", "norm.count", "cap.R"]
    (RamZeroArray.zeroRationalArray_spec B ((m + n) * n) "search.rows" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  have hlo:=normalizeLoop_spec B M m n P R hM hR hdim hB hA
  rintro σ ⟨hσA,hσpad,hσm,hσn,hσR⟩
  have hs:=hσpad ".s" (by simp)
  have hn:=hσpad ".n" (by simp)
  have hd:=hσpad ".d" (by simp)
  have hcost:(72 * M.size + 181) * ((m + n) * n) =
      33 * ((m + n) * n) + (72 * M.size + 148) * ((m + n) * n):=by
    simp only [Nat.add_mul]
    omega
  rw [hcost]
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 (Env.vars σ "query.m") (Env.vars σ "query.n"); let c3:Nat:=c0 c2 (Env.vars σ "query.n"); let c4:Env:=Env.setVar σ "norm.count" c3; let c5:Nat:=Env.vars c4 "norm.count"; let c6:Env:=Env.setVar c4 "vec.n" c5; let c7:Env→ Nat→ Prop:=Run B (RamZeroArray.zeroRationalArray "search.rows") c6; let c8:Nat:=c1 m n; let c9:Nat:=c0 c8 n; let c10:Nat→ Nat:=c1 (c0 ((33:Nat)) c9); let c11:Nat:=c10 ((18:Nat)); let c12:Env→ Prop:=Represents "search.rows" (@List.replicate Rat c9 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c13:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "search.rows"; let c14:String:=c13 ".s"; let c15:String:=c13 ".n"; let c16:String:=c13 ".d"; let c17:String→ List Nat:=Env.arrs c6; let c18:Env→ Env→ Prop:=FieldsAgree (@List.cons String "query.m" (@List.cons String "query.n" (@List.cons String "norm.count" (@List.cons String "cap.R" (@List.nil String))))); let c19:Env→ Prop:=c18 c6; let c20:Env→ Prop:=fun (σ':Env) => And (c7 σ' c11) (And (And (c12 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c9) (∀ b∉ @List.cons String c14 (@List.cons String c15 (@List.cons String c16 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c17 b)))) (And (c19 σ') (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rows"), @Eq (List Nat) (Env.arrs σ' a) (c17 a)))); let c21:Nat:=c0 (c1 (c0 ((72:Nat)) (Nat.size M)) ((148:Nat))) c9; let c22:Nat:=c1 (c10 c21) ((36:Nat)); let c23:Env→ Prop:=Represents "search.rows" (@flatten c8 n fun (i:Fin c8) (j:Fin n) => @Int.cast Rat Rat.instIntCast (@normalizedMatrix m n P R i j)); let c24:Env→ Prop:=Represents "pad.A" (@flatten m n (@Program.A Rat m n (@rationalProgram m n P))); let c25:Env→ Env→ Prop:=fun (x τ:Env) => And (c23 τ) (And (c24 τ) (And (@Eq Nat (Env.vars τ "query.m") m) (And (@Eq Nat (Env.vars τ "query.n") n) (@Eq Nat (Env.vars τ "cap.R") R)))); let c26:Env→ Prop:=c25 σ; let c27:Env→ Prop:=fun (σ':Env) => And (Run B normalizeMatrix σ σ' c22) (c26 σ'); let c28:Nat:=c1 c21 ((6:Nat)); let c29:Nat→ Nat:=c1 ((1:Nat)); let c30:Expr:=Expr.mul (Expr.add (Expr.var "query.m") (Expr.var "query.n")) (Expr.var "query.n"); let c31:Nat:=c29 (Expr.size c30); let c32:Nat:=c29 (Expr.size (Expr.var "norm.count")); let c33:Nat:=c1 c11 c28; let c34:Nat:=c1 c32 c33; @Exists.casesOn Env c20 (fun (x:@Exists Env c20) => @Exists Env c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c14)) c9) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c15)) c9) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c16)) c9) (@Eq Nat (Env.vars σ_1 "vec.n") c9)))) (RamZeroArray.zeroRationalArray "search.rows") (fun (σ_1 τ:Env) => And (And (c12 τ) (And (@Eq Nat (Env.vars τ "vec.n") c9) (∀ b∉ @List.cons String c14 (@List.cons String c15 (@List.cons String c16 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (c18 σ_1 τ) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rows"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c11 hzero c6 ?_) fun (w:Env) (h:And (c7 w c11) (And (And (c12 w) (And (@Eq Nat (Env.vars w "vec.n") c9) (∀ b∉ @List.cons String c14 (@List.cons String c15 (@List.cons String c16 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c17 b)))) (And (c19 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rows"), @Eq (List Nat) (Env.arrs w a) (c17 a))))) => let c0_1:Prop:=And (And (c12 w) (And (@Eq Nat (Env.vars w "vec.n") c9) (∀ b∉ @List.cons String c14 (@List.cons String c15 (@List.cons String c16 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c17 b)))) (And (c19 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rows"), @Eq (List Nat) (Env.arrs w a) (c17 a))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B normalizeLoop w σ' c28) (And (c23 σ') (And (c24 σ') (And (@Eq Nat (Env.vars σ' "query.m") m) (And (@Eq Nat (Env.vars σ' "query.n") n) (@Eq Nat (Env.vars σ' "cap.R") R))))); @And.casesOn (c7 w c11) c0_1 (fun (x:And (c7 w c11) c0_1) => @Exists Env c27) h fun (left:c7 w c11) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c27) (RunStep.use B (fun (σ_1:Env) => And (c24 σ_1) (And (c12 σ_1) (And (@Eq Nat (Env.vars σ_1 "norm.count") c9) (And (@Eq Nat (Env.vars σ_1 "query.m") m) (And (@Eq Nat (Env.vars σ_1 "query.n") n) (@Eq Nat (Env.vars σ_1 "cap.R") R)))))) normalizeLoop c25 c28 hlo w ?_) fun (w_1:Env) (h_1:And (Run B normalizeLoop w w_1 c28) (And (c23 w_1) (And (c24 w_1) (And (@Eq Nat (Env.vars w_1 "query.m") m) (And (@Eq Nat (Env.vars w_1 "query.n") n) (@Eq Nat (Env.vars w_1 "cap.R") R)))))) => let c0_2:Prop:=And (c23 w_1) (And (c24 w_1) (And (@Eq Nat (Env.vars w_1 "query.m") m) (And (@Eq Nat (Env.vars w_1 "query.n") n) (@Eq Nat (Env.vars w_1 "cap.R") R)))); @And.casesOn (Run B normalizeLoop w w_1 c28) c0_2 (fun (x:And (Run B normalizeLoop w w_1 c28) c0_2) => @Exists Env c27) h_1 fun (left_1:Run B normalizeLoop w w_1 c28) (right_1:c0_2) => @Exists.intro Env c27 w_1 (@And.intro (Run B normalizeMatrix σ w_1 c22) (c26 w_1) (RunStep.mono B normalizeMatrix σ w_1 (c1 c31 c34) c22 (RunStep.seq B (Com.assign "norm.count" c30) (Com.seq (Com.assign "vec.n" (Expr.var "norm.count")) (Com.seq (RamZeroArray.zeroRationalArray "search.rows") normalizeLoop)) σ c4 w_1 c31 c34 (RunStep.assign B σ "norm.count" c30 c3 (RunStep.eval_mul B σ (Expr.add (Expr.var "query.m") (Expr.var "query.n")) (Expr.var "query.n") c2 (Env.vars σ "query.n") (RunStep.eval_add B σ (Expr.var "query.m") (Expr.var "query.n") (Env.vars σ "query.m") (Env.vars σ "query.n") (RunStep.eval_var B σ "query.m" (?nAX_g4514_0_0_0)) (RunStep.eval_var B σ "query.n" (?nAX_g4514_0_0_1)) (?nAX_g4514_0_0_2)) (RunStep.eval_var B σ "query.n" (?nAX_g4514_0_0_3)) ?_)) (RunStep.seq B (Com.assign "vec.n" (Expr.var "norm.count")) (Com.seq (RamZeroArray.zeroRationalArray "search.rows") normalizeLoop) c4 c6 w_1 c32 c33 (RunStep.assign B c4 "vec.n" (Expr.var "norm.count") c5 (RunStep.eval_var B c4 "norm.count" ?_)) (RunStep.seq B (RamZeroArray.zeroRationalArray "search.rows") normalizeLoop c6 w w_1 c11 c28 left left_1))) (?nAX_g4514_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4514_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4514_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4514_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4514_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4514_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree,Represents,Extents]
  all_goals aesop

end Lax109476Proofs.RamNormalizedMatrix

end

section

namespace Lax109476Proofs.RamNormalizedBoundEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds
open IntegerEncoding NormalizedFeasibility

def entry {m n:ℕ} (P:Program ℤ m n) (D:ℕ) (i:Fin (m + n)):ℚ:=
  if hi:i.val < m then (P.b ⟨i.val,hi⟩:ℚ) + 1 / (D:ℚ) else 1 / (D:ℚ)

theorem entry_eq {m n:ℕ} (P:Program ℤ m n) (D:ℕ) (i:Fin (m + n)):
    entry P D i=normalizedBound P (1 / (D:ℚ)) i:=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [entry,normalizedBound,i.isLt]
  · intro i
    simp [entry,normalizedBound]

theorem epsilon_height (D:ℕ) (hD:0 < D):Height (1 / (D:ℚ)) D:=by
  simpa only [one_div] using height_inv (D:ℚ) D (height_nat D D le_rfl hD)

theorem entry_height {m n:ℕ} (P:Program ℤ m n) (D M:ℕ) (hM:1≤ M)
    (hD:0 < D) (hDM:D≤ M) (hb:∀ i, (P.b i).natAbs≤ M) (i:Fin (m + n)):
    Height (entry P D i) (2 * M ^ 2):=by
  have hε:=height_mono _ (epsilon_height D hD) hDM
  unfold entry
  split_ifs with hi
  · have hq:Height (P.b ⟨i.val,hi⟩:ℚ) M:=by simpa [Height] using And.intro (hb ⟨i.val,hi⟩) hM
    simpa only [pow_two,Nat.mul_assoc] using height_add _ _ M M hq hε
  · exact height_mono _ hε (by nlinarith)

theorem prepareEpsilon_spec (B D:ℕ) (h1:1 < B) (hD:0 < D) (hDB:D < B):
    Spec B (fun σ => σ.vars "cap.D"=D) prepareEpsilon
      (fun _ τ => RightValue (1 / (D:ℚ)) τ) 6:=by
  have hn:(1 / (D:ℚ)).num=1:=by simpa only [one_div] using Rat.inv_natCast_num_of_pos hD
  have hd:(1 / (D:ℚ)).den=D:=by simpa only [one_div] using Rat.inv_natCast_den_of_pos hD
  intro σ hσ
  (expose_names;
    (refine let c0:Env→ Prop:=RightValue (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D)); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "right.s" ((0:Nat)); let c3:Env:=Env.setVar c2 "right.n" ((1:Nat)); let c4:Nat:=Env.vars c3 "cap.D"; let c5:Env:=Env.setVar c3 "right.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c7 (Expr.size (Expr.var "cap.D")); let c11:Nat:=c6 c9 c10; let c12:Com:=Com.assign "right.n" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B prepareEpsilon σ σ' ((6:Nat))) (c1 σ')) c5 (@And.intro (Run B prepareEpsilon σ c5 ((6:Nat))) (c1 c5) (RunStep.mono B prepareEpsilon σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq c12 (Com.assign "right.d" (Expr.var "cap.D"))) σ c2 c5 c8 c11 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4520_0_0_0))) (RunStep.seq B c12 (Com.assign "right.d" (Expr.var "cap.D")) c2 c3 c5 c9 c10 (RunStep.assign B c2 "right.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) (RunStep.assign B c3 "right.d" (Expr.var "cap.D") c4 (RunStep.eval_var B c3 "cap.D" (?nAX_g4520_0_0_1))))) (?nAX_g4520_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4520_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4520_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4520_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue,fractionValue]
  all_goals exact (congrArg Int.natAbs (Int.sign_eq_one_iff_pos.mpr
    (show (0:ℤ) < D by exact_mod_cast hD))).symm

theorem epsilonResult_spec (B D:ℕ) (h1:1 < B) (hD:0 < D) (hDB:D < B):
    Spec B (fun σ => σ.vars "cap.D"=D) epsilonResult
      (fun _ τ => FractionOutput (1 / (D:ℚ)) τ) 6:=by
  have hn:(1 / (D:ℚ)).num=1:=by simpa only [one_div] using Rat.inv_natCast_num_of_pos hD
  have hd:(1 / (D:ℚ)).den=D:=by simpa only [one_div] using Rat.inv_natCast_den_of_pos hD
  intro σ hσ
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D)); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.n" ((1:Nat)); let c4:Nat:=Env.vars c3 "cap.D"; let c5:Env:=Env.setVar c3 "rat.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c7 (Expr.size (Expr.var "cap.D")); let c11:Nat:=c6 c9 c10; let c12:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B epsilonResult σ σ' ((6:Nat))) (c1 σ')) c5 (@And.intro (Run B epsilonResult σ c5 ((6:Nat))) (c1 c5) (RunStep.mono B epsilonResult σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c12 (Com.assign "rat.d" (Expr.var "cap.D"))) σ c2 c5 c8 c11 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4522_0_0_0))) (RunStep.seq B c12 (Com.assign "rat.d" (Expr.var "cap.D")) c2 c3 c5 c9 c10 (RunStep.assign B c2 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) (RunStep.assign B c3 "rat.d" (Expr.var "cap.D") c4 (RunStep.eval_var B c3 "cap.D" (?nAX_g4522_0_0_1))))) (?nAX_g4522_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4522_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4522_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4522_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,fractionValue]
  all_goals exact (congrArg Int.natAbs (Int.sign_eq_one_iff_pos.mpr
    (show (0:ℤ) < D by exact_mod_cast hD))).symm

def fields:List String:= ["query.m", "norm.k", "cap.D"]

set_option maxHeartbeats 0 in
theorem selectBound_spec (B M m n D:ℕ) (P:Program ℤ m n) (i:Fin (m + n))
    (hM:1≤ M) (hD:0 < D) (hDM:D≤ M) (hB:2 * M ^ 2 + 3 < B)
    (hdim:m + n + 1 < B) (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧
        σ.vars "query.m"=m∧ σ.vars "norm.k"=i.val∧ σ.vars "cap.D"=D)
      selectBound (fun _ τ => FractionOutput (entry P D i) τ) (72 * M.size + 130):=by
  have hMB:M < B:=by nlinarith
  have hDB:D < B:=hDM.trans_lt hMB
  have h1:1 < B:=by nlinarith
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hmB:m < B:=by omega
  have hresult:=epsilonResult_spec B D h1 hD hDB
  have hz:Height (0:ℚ) M:=height_mono _ height_zero hM
  have hdead:=add_spec B M 0 0 hB hz hz
  rintro σ ⟨hσb,hσm,hσi,hσD⟩
  by_cases hi:i.val < m
  · let ii:Fin m:= ⟨i.val,hi⟩
    have hq:Height (P.b ii:ℚ) M:=by simpa [Height] using And.intro (hb ii) hM
    have hε:=height_mono _ (epsilon_height D hD) hDM
    have hload:=spec_with_fields fields
      (loadLeft_spec B "pad.b" (List.ofFn (rationalProgram P).b) i.val (by simpa using hi)
        h1 hiB (by simpa [ii,rationalProgram] using hq.1.trans_lt hMB)
        (by simpa [ii,rationalProgram] using hq.2.trans_lt hMB))
      (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hprepare:=spec_with_fields ["left.s", "left.n", "left.d"]
      (prepareEpsilon_spec B D h1 hD hDB)
      (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
    have hcanonical:fractionValue (rationalSign (P.b ii:ℚ)) (P.b ii).natAbs 1=(P.b ii:ℚ):=by
      simpa using canonical_fractionValue (P.b ii:ℚ)
    have hadd:=add_spec B M (P.b ii:ℚ) (1 / (D:ℚ)) hB hq hε
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "norm.k") (Env.vars σ "query.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((72:Nat)) (Nat.size M)); let c4:Nat:=c3 ((130:Nat)); let c5:Env→ Prop:=FractionOutput (@entry m n P D i); let c6:Env→ Prop:=(fun (x τ:Env) => c5 τ) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' c4) (c6 σ'); let c8:Env→ Nat→ Prop:=Run B (loadLeft "pad.b") (Env.setVar σ "vec.i" (Env.vars σ "norm.k")); let c9:List Rat:= @List.ofFn Rat m (@Program.b Rat m n (@rationalProgram m n P)); let c10:Nat:= @Fin.val (c2 m n) i; let c11:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c9 c10 (?nAX_g4525_0_0_0)); let c12:Env→ Prop:=FieldsAgree fields (Env.setVar σ "vec.i" (Env.vars σ "norm.k")); let c13:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "norm.k")); let c14:Env→ Prop:=fun (σ':Env) => And (c8 σ' ((9:Nat))) (And (c11 σ') (And (c12 σ') (@Eq (String→ List Nat) (Env.arrs σ') c13))); let c15:Env→ Prop:=Represents "pad.b" c9; let c16:Rat:= @HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D); let c17:Env→ Prop:=RightValue c16; let c18:Env→ Env→ Prop:=FieldsAgree (@List.cons String "left.s" (@List.cons String "left.n" (@List.cons String "left.d" (@List.nil String)))); let c19:Nat:=c3 ((96:Nat)); let c20:Rat:= @Int.cast Rat Rat.instIntCast (@Program.b Int m n P ii); let c21:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) c20 c16); let c22:Env→ Prop:=LeftValue c20; let c23:Nat→ Nat:=c2 ((1:Nat)); let c24:Nat→ Nat:=c2 (c23 (Cond.size (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")))); let c25:Nat:=c23 (Expr.size (Expr.var "norm.k")); let c26:Nat:=c2 ((6:Nat)) c19; let c27:Nat:=c2 ((9:Nat)) c26; let c28:Nat:=c2 c25 c27; let c29:Com:=Com.seq (Com.assign "vec.i" (Expr.var "norm.k")) (Com.seq (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction)); let c30:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c31:Env:=Env.setVar c30 "rat.n" ((1:Nat)); let c32:Nat:=Env.vars c31 "cap.D"; let c33:Env:=Env.setVar c31 "rat.d" c32; let c34:Nat:=c23 (Expr.size (Expr.lit ((0:Nat)))); let c35:Nat:=c23 (Expr.size (Expr.lit ((1:Nat)))); let c36:Nat:=c23 (Expr.size (Expr.var "cap.D")); let c37:Nat:=c2 c35 c36; let c38:Nat:=c2 c34 c37; let c39:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c7) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => @Exists Env c7) (RunStep.use B (fun (σ_1:Env) => And (c15 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") c10)) (loadLeft "pad.b") (fun (σ_1 τ:Env) => And (c11 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) ?_) fun (w:Env) (h:And (c8 w ((9:Nat))) (And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)))) => let c0_1:Prop:=c8 w ((9:Nat)); let c1_1:Prop:=And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B prepareEpsilon w σ' ((6:Nat))) (And (c17 σ') (And (c18 w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c7) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c7) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "cap.D") D) prepareEpsilon (fun (σ_1 τ:Env) => And (c17 τ) (And (c18 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hprepare w ?_) fun (w_1:Env) (h_1:And (Run B prepareEpsilon w w_1 ((6:Nat))) (And (c17 w_1) (And (c18 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B prepareEpsilon w w_1 ((6:Nat)); let c1_2:Prop:=And (c17 w_1) (And (c18 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B addFraction w_1 σ' c19) (c21 σ'); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => @Exists Env c7) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => @Exists Env c7) (RunStep.use B (fun (σ_1:Env) => And (c22 σ_1) (c17 σ_1)) addFraction (fun (x τ:Env) => c21 τ) c19 hadd w_1 ?_) fun (w_2:Env) (h_2:And (Run B addFraction w_1 w_2 c19) (c21 w_2)) => @And.casesOn (Run B addFraction w_1 w_2 c19) (c21 w_2) (fun (x:And (Run B addFraction w_1 w_2 c19) (c21 w_2)) => @Exists Env c7) h_2 fun (left_2:Run B addFraction w_1 w_2 c19) (right_2:c21 w_2) => @Exists.intro Env c7 w_2 (@And.intro (Run B selectBound σ w_2 c4) (c6 w_2) (RunStep.mono B selectBound σ w_2 (c24 c28) c4 (RunStep.ite_true B (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")) c29 epsilonResult σ w_2 c28 (RunStep.cond_lt_true B σ (Expr.var "norm.k") (Expr.var "query.m") (Env.vars σ "norm.k") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_0_0_1)) (RunStep.eval_var B σ "query.m" (?nAX_g4525_0_0_2)) hcase) (RunStep.seq B (Com.assign "vec.i" (Expr.var "norm.k")) (Com.seq (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction)) σ (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) w_2 c25 c27 (RunStep.assign B σ "vec.i" (Expr.var "norm.k") (Env.vars σ "norm.k") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_0_0_3))) (RunStep.seq B (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction) (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) w w_2 ((9:Nat)) c26 left (RunStep.seq B prepareEpsilon addFraction w w_1 w_2 ((6:Nat)) c19 left_1 left_2)))) (?nAX_g4525_0_0_4)) ?_)) fun (hcase:c1) => @Exists.intro Env c7 c33 (@And.intro (Run B selectBound σ c33 c4) (c6 c33) (RunStep.mono B selectBound σ c33 (c24 c38) c4 (RunStep.ite_false B (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")) c29 epsilonResult σ c33 c38 (RunStep.cond_lt_false B σ (Expr.var "norm.k") (Expr.var "query.m") (Env.vars σ "norm.k") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_0_0_5)) (RunStep.eval_var B σ "query.m" (?nAX_g4525_0_0_6)) hcase) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c39 (Com.assign "rat.d" (Expr.var "cap.D"))) σ c30 c33 c34 c37 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4525_0_0_7))) (RunStep.seq B c39 (Com.assign "rat.d" (Expr.var "cap.D")) c30 c31 c33 c35 c36 (RunStep.assign B c30 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c30 h1)) (RunStep.assign B c31 "rat.d" (Expr.var "cap.D") c32 (RunStep.eval_var B c31 "cap.D" (?nAX_g4525_0_0_8)))))) (?nAX_g4525_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4525_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
    all_goals clear hload hprepare hadd
    all_goals simp_all [fields,FieldsAgree,Represents,entry,ii,LeftOutput,LeftValue,
      RightValue,rationalProgram,hcanonical,rationalSign_le_one]
    all_goals aesop
  · (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "norm.k") (Env.vars σ "query.m"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((72:Nat)) (Nat.size M)); let c4:Nat:=c3 ((130:Nat)); let c5:Env→ Prop:=FractionOutput (@entry m n P D i); let c6:Env→ Prop:=(fun (x τ:Env) => c5 τ) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' c4) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "pad.b"; let c10:String:=c9 ".s"; let c11:Nat:=Env.vars (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) c10) c11 ((0:Nat)); let c13:Env:=Env.setVar (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) "left.s" c12; let c14:String:=c9 ".n"; let c15:Nat:=Env.vars c13 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c13 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c13 "left.n" c16; let c18:String:=c9 ".d"; let c19:Nat:=Env.vars c17 "vec.i"; let c20:Nat:= @List.getD Nat (Env.arrs c17 c18) c19 ((0:Nat)); let c21:Env:=Env.setVar c17 "left.d" c20; let c22:Env:=Env.setVar c21 "right.s" ((0:Nat)); let c23:Env:=Env.setVar c22 "right.n" ((1:Nat)); let c24:Nat:=Env.vars c23 "cap.D"; let c25:Env:=Env.setVar c23 "right.d" c24; let c26:Env→ Nat→ Prop:=Run B addFraction c25; let c27:Nat:=c3 ((96:Nat)); let c28:Env→ Prop:=FractionOutput (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c29:Env→ Prop:=fun (σ':Env) => And (c26 σ' c27) (c28 σ'); let c30:Nat→ Nat:=c2 ((1:Nat)); let c31:Nat→ Nat:=c2 (c30 (Cond.size (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")))); let c32:Nat:=c30 (Expr.size (Expr.var "norm.k")); let c33:Expr:=Expr.get c10 (Expr.var "vec.i"); let c34:Nat:=c30 (Expr.size c33); let c35:Expr:=Expr.get c14 (Expr.var "vec.i"); let c36:Nat:=c30 (Expr.size c35); let c37:Expr:=Expr.get c18 (Expr.var "vec.i"); let c38:Nat:=c30 (Expr.size c37); let c39:Nat:=c2 c36 c38; let c40:Nat:=c2 c34 c39; let c41:Nat:=c30 (Expr.size (Expr.lit ((0:Nat)))); let c42:Nat:=c30 (Expr.size (Expr.lit ((1:Nat)))); let c43:Nat:=c30 (Expr.size (Expr.var "cap.D")); let c44:Nat:=c2 c42 c43; let c45:Nat:=c2 c41 c44; let c46:Nat:=c2 c45 c27; let c47:Nat:=c2 c40 c46; let c48:Nat:=c2 c32 c47; let c49:Com:=Com.seq (Com.assign "vec.i" (Expr.var "norm.k")) (Com.seq (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction)); let c50:Com:=Com.assign "left.n" c35; let c51:Com:=Com.assign "left.d" c37; let c52:Com:=Com.assign "right.n" (Expr.lit ((1:Nat))); let c53:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D)); let c54:Env→ Prop:=fun (σ':Env) => And (Run B epsilonResult σ σ' ((6:Nat))) (c53 σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c8) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c29 (fun (x:@Exists Env c29) => c8) (RunStep.use B (fun (σ_1:Env) => And (LeftValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1) (RightValue (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ_1)) addFraction (fun (x τ:Env) => c28 τ) c27 hdead c25 ?_) fun (w:Env) (h:And (c26 w c27) (c28 w)) => @And.casesOn (c26 w c27) (c28 w) (fun (x:And (c26 w c27) (c28 w)) => c8) h fun (left:c26 w c27) (right:c28 w) => @Exists.intro Env c7 w (@And.intro (Run B selectBound σ w c4) (c6 w) (RunStep.mono B selectBound σ w (c31 c48) c4 (RunStep.ite_true B (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")) c49 epsilonResult σ w c48 (RunStep.cond_lt_true B σ (Expr.var "norm.k") (Expr.var "query.m") (Env.vars σ "norm.k") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_1_0_0)) (RunStep.eval_var B σ "query.m" (?nAX_g4525_1_0_1)) hcase) (RunStep.seq B (Com.assign "vec.i" (Expr.var "norm.k")) (Com.seq (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction)) σ (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) w c32 c47 (RunStep.assign B σ "vec.i" (Expr.var "norm.k") (Env.vars σ "norm.k") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_1_0_2))) (RunStep.seq B (loadLeft "pad.b") (Com.seq prepareEpsilon addFraction) (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) c21 w c40 c46 (RunStep.seq B (Com.assign "left.s" c33) (Com.seq c50 c51) (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) c13 c21 c34 c39 (RunStep.assign B (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) "left.s" c33 c12 (RunStep.eval_get B (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) c10 (Expr.var "vec.i") c11 (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "norm.k")) "vec.i" (?nAX_g4525_1_0_3)) (?nAX_g4525_1_0_4) (?nAX_g4525_1_0_5))) (RunStep.seq B c50 c51 c13 c17 c21 c36 c38 (RunStep.assign B c13 "left.n" c35 c16 (RunStep.eval_get B c13 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c13 "vec.i" (?nAX_g4525_1_0_6)) (?nAX_g4525_1_0_7) (?nAX_g4525_1_0_8))) (RunStep.assign B c17 "left.d" c37 c20 (RunStep.eval_get B c17 c18 (Expr.var "vec.i") c19 (RunStep.eval_var B c17 "vec.i" (?nAX_g4525_1_0_9)) (?nAX_g4525_1_0_10) (?nAX_g4525_1_0_11))))) (RunStep.seq B prepareEpsilon addFraction c21 c25 w c45 c27 (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq c52 (Com.assign "right.d" (Expr.var "cap.D"))) c21 c22 c25 c41 c44 (RunStep.assign B c21 "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c21 (?nAX_g4525_1_0_12))) (RunStep.seq B c52 (Com.assign "right.d" (Expr.var "cap.D")) c22 c23 c25 c42 c43 (RunStep.assign B c22 "right.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c22 h1)) (RunStep.assign B c23 "right.d" (Expr.var "cap.D") c24 (RunStep.eval_var B c23 "cap.D" (?nAX_g4525_1_0_13))))) left)))) (?nAX_g4525_1_0_14)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c54 (fun (x:@Exists Env c54) => c8) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "cap.D") D) epsilonResult (fun (x τ:Env) => c53 τ) ((6:Nat)) hresult σ ?_) fun (w:Env) (h:And (Run B epsilonResult σ w ((6:Nat))) (c53 w)) => let c0_1:Prop:=Run B epsilonResult σ w ((6:Nat)); @And.casesOn c0_1 (c53 w) (fun (x:And c0_1 (c53 w)) => c8) h fun (left:c0_1) (right:c53 w) => @Exists.intro Env c7 w (@And.intro (Run B selectBound σ w c4) (c6 w) (RunStep.mono B selectBound σ w (c31 ((6:Nat))) c4 (RunStep.ite_false B (Cond.lt (Expr.var "norm.k") (Expr.var "query.m")) c49 epsilonResult σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "norm.k") (Expr.var "query.m") (Env.vars σ "norm.k") (Env.vars σ "query.m") (RunStep.eval_var B σ "norm.k" (?nAX_g4525_1_0_15)) (RunStep.eval_var B σ "query.m" (?nAX_g4525_1_0_16)) hcase) left) (?nAX_g4525_1_0_17)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4525_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4525_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals simp_all [entry,Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamNormalizedBoundEntry

end

section

namespace Lax109476Proofs.RamNormalizedBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamNormalizedBoundEntry RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def values {m n:ℕ} (P:Program ℤ m n) (D:ℕ):Fin (m + n)→ ℚ:=
  fun k => RamNormalizedBoundEntry.entry P D k

theorem values_eq {m n:ℕ} (P:Program ℤ m n) (D:ℕ):
    List.ofFn (values P D)=List.ofFn (normalizedBound P (1 / (D:ℚ))):=by
  unfold values
  congr 1
  funext k
  exact RamNormalizedBoundEntry.entry_eq P D k

def fields:List String:= ["norm.k", "norm.count", "query.m", "query.n", "cap.D"]

set_option maxHeartbeats 0 in
theorem normalizeCoordinate_spec (B M m n:ℕ) (P:Program ℤ m n) (D:ℕ)
    (k:Fin (m + n)) (ys:List ℚ) (hy:k.val < ys.length)
    (hM:1≤ M) (hD:0 < D) (hDM:D≤ M) (hdim:m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧ Represents "search.rhs" ys σ∧
        σ.vars "norm.k"=k.val∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.D"=D)
      normalizeCoordinate
      (fun _ τ => Represents "search.rhs" (ys.set k.val (values P D k)) τ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ∧ τ.vars "norm.k"=k.val∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.D"=D) (72 * M.size + 148):=by
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have h1:1 < B:=by omega
  have h2:2 < B:=by nlinarith
  have hmB:m < B:=by omega
  have hnB:n < B:=by omega
  have hMB:M < B:=by nlinarith
  have hM2B:2 * M ^ 2 < B:=by omega
  have hq:=RamNormalizedBoundEntry.entry_height P D M hM hD hDM hb k
  have hselect:=spec_with_fields fields
    (RamNormalizedBoundEntry.selectBound_spec B M m n D P k hM hD hDM hB hdim hb)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore:=spec_with_write_frame fields
    (storeReduced_spec B "search.rhs" ys (values P D k) k.val hy h1 hkB
      (hq.1.trans_lt hM2B) (hq.2.trans_lt hM2B))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA,hσy,hσk,hσm,hσn,hσD⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat:=c0 (Nat.mul ((72:Nat)) (Nat.size M)); let c2:Nat:=c1 ((130:Nat)); let c3:Env→ Prop:=FractionOutput (@entry m n P D k); let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' c2) (And (c3 σ') (And (FieldsAgree fields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c5:Nat:=c1 ((148:Nat)); let c6:Nat:= @Fin.val (c0 m n) k; let c7:Env→ Prop:=Represents "search.rhs" (@List.set Rat ys c6 (@values m n P D k)); let c8:Env→ Prop:=Represents "pad.b" (@List.ofFn Rat m (@Program.b Rat m n (@rationalProgram m n P))); let c9:Env→ Prop:=(fun (x τ:Env) => And (c7 τ) (And (c8 τ) (And (@Eq Nat (Env.vars τ "norm.k") c6) (And (@Eq Nat (Env.vars τ "query.m") m) (And (@Eq Nat (Env.vars τ "query.n") n) (@Eq Nat (Env.vars τ "cap.D") D)))))) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B normalizeCoordinate σ σ' c5) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Env→ Prop:=FractionOutput (@values m n P D k); let c13:Nat:=c0 ((1:Nat)) (Expr.size (Expr.var "norm.k")); let c14:Nat:=c0 c13 ((13:Nat)); @Exists.casesOn Env c4 (fun (x:@Exists Env c4) => c11) (RunStep.use B (fun (σ_1:Env) => And (c8 σ_1) (And (@Eq Nat (Env.vars σ_1 "query.m") m) (And (@Eq Nat (Env.vars σ_1 "norm.k") c6) (@Eq Nat (Env.vars σ_1 "cap.D") D)))) selectBound (fun (σ_1 τ:Env) => And (c3 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c2 hselect σ ?_) fun (w:Env) (h:And (Run B selectBound σ w c2) (And (c3 w) (And (FieldsAgree fields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=And (c3 w) (And (FieldsAgree fields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c1_1:Env→ Nat→ Prop:=Run B (storeReduced "search.rhs") (Env.setVar w "vec.i" (Env.vars w "norm.k")); let c2_1:Env→ Prop:=FieldsAgree fields (Env.setVar w "vec.i" (Env.vars w "norm.k")); let c3_1:Env→ Prop:=fun (σ':Env) => And (c1_1 σ' ((13:Nat))) (And (c7 σ') (And (c2_1 σ') (∀ a∉ Com.warrs (storeReduced "search.rhs"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a)))); @And.casesOn (Run B selectBound σ w c2) c0_1 (fun (x:And (Run B selectBound σ w c2) c0_1) => c11) h fun (left:Run B selectBound σ w c2) (right:c0_1) => @Exists.casesOn Env c3_1 (fun (x:@Exists Env c3_1) => c11) (RunStep.use B (fun (σ_1:Env) => And (Represents "search.rhs" ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") c6) (c12 σ_1))) (storeReduced "search.rhs") (fun (σ_1 τ:Env) => And (c7 τ) (And (FieldsAgree fields σ_1 τ) (∀ a∉ Com.warrs (storeReduced "search.rhs"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore (Env.setVar w "vec.i" (Env.vars w "norm.k")) ?_) fun (w_1:Env) (h_1:And (c1_1 w_1 ((13:Nat))) (And (c7 w_1) (And (c2_1 w_1) (∀ a∉ Com.warrs (storeReduced "search.rhs"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a))))) => let c0_2:Prop:=c1_1 w_1 ((13:Nat)); let c1_2:Prop:=And (c7 w_1) (And (c2_1 w_1) (∀ a∉ Com.warrs (storeReduced "search.rhs"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "norm.k")) a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c11) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c10 w_1 (@And.intro (Run B normalizeCoordinate σ w_1 c5) (c9 w_1) (RunStep.mono B normalizeCoordinate σ w_1 (c0 c2 c14) c5 (RunStep.seq B selectBound (Com.seq (Com.assign "vec.i" (Expr.var "norm.k")) (storeReduced "search.rhs")) σ w w_1 c2 c14 left (RunStep.seq B (Com.assign "vec.i" (Expr.var "norm.k")) (storeReduced "search.rhs") w (Env.setVar w "vec.i" (Env.vars w "norm.k")) w_1 c13 ((13:Nat)) (RunStep.assign B w "vec.i" (Expr.var "norm.k") (Env.vars w "norm.k") (RunStep.eval_var B w "norm.k" ?_)) left_1)) (?nAX_g4530_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4530_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hselect hstore
  all_goals simp_all [fields,FieldsAgree,Represents,values,Fin.divNat,Fin.modNat,
    storeReduced,Com.warrs]
  all_goals aesop

def Invariant {m n:ℕ} (P:Program ℤ m n) (D:ℕ) (σ:Env):Prop:=
  Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧
    Represents "search.rhs" (filled (values P D) (σ.vars "norm.k")) σ∧
    σ.vars "norm.k" ≤ m + n∧ σ.vars "norm.count"=m + n∧
    σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.D"=D

theorem normalizeStep_spec (B M m n:ℕ) (P:Program ℤ m n) (D:ℕ)
    (hM:1≤ M) (hD:0 < D) (hDM:D≤ M) (hdim:m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Invariant P D σ∧ σ.vars "norm.k" < m + n) normalizeStep
      (fun σ τ => Invariant P D τ∧ τ.vars "norm.k"=σ.vars "norm.k" + 1) (72 * M.size + 152):=by
  rintro σ ⟨⟨hσA,hσp,hσkN,hσcount,hσm,hσn,hσD⟩,hσk⟩
  let k:Fin (m + n):= ⟨σ.vars "norm.k",hσk⟩
  obtain ⟨τ,hr₁,hτp,hτA,hτk,hτm,hτn,hτD⟩:=normalizeCoordinate_spec B M m n P D k
    (filled (values P D) k.val) (by simpa only [filled,List.length_ofFn] using k.isLt) hM hD hDM hdim hB hb σ ⟨hσA,hσp,rfl,hσm,hσn,hσD⟩
  have hτcount:=(hr₁.frame_var "norm.count" (by decide)).trans hσcount
  have h1:1 < B:=by omega
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have hi1B:k.val + 1 < B:=lt_of_le_of_lt k.isLt (by omega)
  have hr₂:Run B (.assign "norm.k" (.add (.var "norm.k") (.lit 1))) τ
      (τ.setVar "norm.k" (k.val + 1)) 4:=by
    exact Run.assign (by simpa only [hτk,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=τ) (x:= "norm.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "norm.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled:Represents "search.rhs" (filled (values P D) (k.val + 1)) τ:=by
    rw [← filled_step]
    exact hτp
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτA
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change k.val + 1≤ m + n
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simpa using hτD
  · simp [k]

theorem normalizeLoop_spec (B M m n:ℕ) (P:Program ℤ m n) (D:ℕ)
    (hM:1≤ M) (hD:0 < D) (hDM:D≤ M) (hdim:m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧
        Represents "search.rhs" (List.replicate (m + n) 0) σ∧
        σ.vars "norm.count"=m + n∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.D"=D)
      normalizeLoop
      (fun _ τ => Represents "search.rhs" (List.ofFn (normalizedBound P (1 / (D:ℚ)))) τ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ∧ τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.D"=D)
      ((72 * M.size + 156) * (m + n) + 6):=by
  have hlo:=Spec.forRangeZero "norm.k" "norm.count" (Invariant P D) (m + n) (72 * M.size + 152)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (normalizeStep_spec B M m n P D hM hD hDM hdim hB hb)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hb,hp,hcount,hm,hn,hD⟩
    simp_all [Invariant,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hk⟩
    refine ⟨?_,hτ.1,hτ.2.2.2.2.1,hτ.2.2.2.2.2.1,hτ.2.2.2.2.2.2⟩
    simpa only [hk,filled_done,values_eq] using hτ.2.1

set_option maxHeartbeats 0 in
theorem normalizeBound_spec (B M m n:ℕ) (P:Program ℤ m n) (D:ℕ)
    (hM:1≤ M) (hD:0 < D) (hDM:D≤ M) (hdim:m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧
        Extents "search.rhs" (m + n) σ∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.D"=D)
      normalizeBound
      (fun _ τ => Represents "search.rhs" (List.ofFn (normalizedBound P (1 / (D:ℚ)))) τ∧
        Represents "pad.b" (List.ofFn (rationalProgram P).b) τ∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.D"=D)
      ((72 * M.size + 189) * (m + n) + 36):=by
  have h1:1 < B:=by omega
  have h2:2 < B:=by nlinarith
  have hmB:m < B:=by omega
  have hnB:n < B:=by omega
  have hcountB:m + n < B:=by omega
  have hzero:=spec_with_write_frame ["query.m", "query.n", "norm.count", "cap.D"]
    (RamZeroArray.zeroRationalArray_spec B (m + n) "search.rhs" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  have hlo:=normalizeLoop_spec B M m n P D hM hD hDM hdim hB hb
  rintro σ ⟨hσA,hσpad,hσm,hσn,hσD⟩
  have hs:=hσpad ".s" (by simp)
  have hn:=hσpad ".n" (by simp)
  have hd:=hσpad ".d" (by simp)
  have hcost:(72 * M.size + 189) * (m + n) =
      33 * (m + n) + (72 * M.size + 156) * (m + n):=by
    simp only [Nat.add_mul]
    omega
  rw [hcost]
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "query.m") (Env.vars σ "query.n"); let c2:Env:=Env.setVar σ "norm.count" c1; let c3:Nat:=Env.vars c2 "norm.count"; let c4:Env:=Env.setVar c2 "vec.n" c3; let c5:Env→ Nat→ Prop:=Run B (RamZeroArray.zeroRationalArray "search.rhs") c4; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c0 m n; let c8:Nat→ Nat:=c0 (c6 ((33:Nat)) c7); let c9:Nat:=c8 ((18:Nat)); let c10:Env→ Prop:=Represents "search.rhs" (@List.replicate Rat c7 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c11:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "search.rhs"; let c12:String:=c11 ".s"; let c13:String:=c11 ".n"; let c14:String:=c11 ".d"; let c15:String→ List Nat:=Env.arrs c4; let c16:Env→ Env→ Prop:=FieldsAgree (@List.cons String "query.m" (@List.cons String "query.n" (@List.cons String "norm.count" (@List.cons String "cap.D" (@List.nil String))))); let c17:Env→ Prop:=c16 c4; let c18:Env→ Prop:=fun (σ':Env) => And (c5 σ' c9) (And (And (c10 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c7) (∀ b∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c15 b)))) (And (c17 σ') (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rhs"), @Eq (List Nat) (Env.arrs σ' a) (c15 a)))); let c19:Nat:=c6 (c0 (c6 ((72:Nat)) (Nat.size M)) ((156:Nat))) c7; let c20:Nat:=c0 (c8 c19) ((36:Nat)); let c21:Env→ Prop:=Represents "search.rhs" (@List.ofFn Rat c7 (@normalizedBound m n P (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast D)))); let c22:Env→ Prop:=Represents "pad.b" (@List.ofFn Rat m (@Program.b Rat m n (@rationalProgram m n P))); let c23:Env→ Env→ Prop:=fun (x τ:Env) => And (c21 τ) (And (c22 τ) (And (@Eq Nat (Env.vars τ "query.m") m) (And (@Eq Nat (Env.vars τ "query.n") n) (@Eq Nat (Env.vars τ "cap.D") D)))); let c24:Env→ Prop:=c23 σ; let c25:Env→ Prop:=fun (σ':Env) => And (Run B normalizeBound σ σ' c20) (c24 σ'); let c26:Nat:=c0 c19 ((6:Nat)); let c27:Nat→ Nat:=c0 ((1:Nat)); let c28:Nat:=c27 (Expr.size (Expr.add (Expr.var "query.m") (Expr.var "query.n"))); let c29:Nat:=c27 (Expr.size (Expr.var "norm.count")); let c30:Nat:=c0 c9 c26; let c31:Nat:=c0 c29 c30; @Exists.casesOn Env c18 (fun (x:@Exists Env c18) => @Exists Env c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c12)) c7) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c13)) c7) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c14)) c7) (@Eq Nat (Env.vars σ_1 "vec.n") c7)))) (RamZeroArray.zeroRationalArray "search.rhs") (fun (σ_1 τ:Env) => And (And (c10 τ) (And (@Eq Nat (Env.vars τ "vec.n") c7) (∀ b∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (c16 σ_1 τ) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rhs"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c9 hzero c4 ?_) fun (w:Env) (h:And (c5 w c9) (And (And (c10 w) (And (@Eq Nat (Env.vars w "vec.n") c7) (∀ b∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c15 b)))) (And (c17 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rhs"), @Eq (List Nat) (Env.arrs w a) (c15 a))))) => let c0_1:Prop:=And (And (c10 w) (And (@Eq Nat (Env.vars w "vec.n") c7) (∀ b∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c15 b)))) (And (c17 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "search.rhs"), @Eq (List Nat) (Env.arrs w a) (c15 a))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B normalizeLoop w σ' c26) (And (c21 σ') (And (c22 σ') (And (@Eq Nat (Env.vars σ' "query.m") m) (And (@Eq Nat (Env.vars σ' "query.n") n) (@Eq Nat (Env.vars σ' "cap.D") D))))); @And.casesOn (c5 w c9) c0_1 (fun (x:And (c5 w c9) c0_1) => @Exists Env c25) h fun (left:c5 w c9) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c25) (RunStep.use B (fun (σ_1:Env) => And (c22 σ_1) (And (c10 σ_1) (And (@Eq Nat (Env.vars σ_1 "norm.count") c7) (And (@Eq Nat (Env.vars σ_1 "query.m") m) (And (@Eq Nat (Env.vars σ_1 "query.n") n) (@Eq Nat (Env.vars σ_1 "cap.D") D)))))) normalizeLoop c23 c26 hlo w ?_) fun (w_1:Env) (h_1:And (Run B normalizeLoop w w_1 c26) (And (c21 w_1) (And (c22 w_1) (And (@Eq Nat (Env.vars w_1 "query.m") m) (And (@Eq Nat (Env.vars w_1 "query.n") n) (@Eq Nat (Env.vars w_1 "cap.D") D)))))) => let c0_2:Prop:=And (c21 w_1) (And (c22 w_1) (And (@Eq Nat (Env.vars w_1 "query.m") m) (And (@Eq Nat (Env.vars w_1 "query.n") n) (@Eq Nat (Env.vars w_1 "cap.D") D)))); @And.casesOn (Run B normalizeLoop w w_1 c26) c0_2 (fun (x:And (Run B normalizeLoop w w_1 c26) c0_2) => @Exists Env c25) h_1 fun (left_1:Run B normalizeLoop w w_1 c26) (right_1:c0_2) => @Exists.intro Env c25 w_1 (@And.intro (Run B normalizeBound σ w_1 c20) (c24 w_1) (RunStep.mono B normalizeBound σ w_1 (c0 c28 c31) c20 (RunStep.seq B (Com.assign "norm.count" (Expr.add (Expr.var "query.m") (Expr.var "query.n"))) (Com.seq (Com.assign "vec.n" (Expr.var "norm.count")) (Com.seq (RamZeroArray.zeroRationalArray "search.rhs") normalizeLoop)) σ c2 w_1 c28 c31 (RunStep.assign B σ "norm.count" (Expr.add (Expr.var "query.m") (Expr.var "query.n")) c1 (RunStep.eval_add B σ (Expr.var "query.m") (Expr.var "query.n") (Env.vars σ "query.m") (Env.vars σ "query.n") (RunStep.eval_var B σ "query.m" (?nAX_g4537_0_0_0)) (RunStep.eval_var B σ "query.n" (?nAX_g4537_0_0_1)) (?nAX_g4537_0_0_2))) (RunStep.seq B (Com.assign "vec.n" (Expr.var "norm.count")) (Com.seq (RamZeroArray.zeroRationalArray "search.rhs") normalizeLoop) c2 c4 w_1 c29 c30 (RunStep.assign B c2 "vec.n" (Expr.var "norm.count") c3 (RunStep.eval_var B c2 "norm.count" (?nAX_g4537_0_0_3))) (RunStep.seq B (RamZeroArray.zeroRationalArray "search.rhs") normalizeLoop c4 w w_1 c9 c26 left left_1))) (?nAX_g4537_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4537_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4537_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4537_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4537_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4537_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree,Represents,Extents]
  all_goals aesop

end Lax109476Proofs.RamNormalizedBound

end

section

namespace Lax109476Proofs.RamNormalizeQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding NormalizedFeasibility

def Input {m n:ℕ} (P:Program ℤ m n) (R D N:ℕ) (σ:Env):Prop:=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ∧
    Represents "pad.b" (List.ofFn (rationalProgram P).b) σ∧
    Extents "search.rows" ((m + n) * n) σ∧ Extents "search.rhs" (m + n) σ∧
    Extents "ell.center" n σ∧ Extents "ell.shape" (n * n) σ∧ Workspace n σ∧
    Extents "ell.normal" n σ∧ σ.vars "query.m"=m∧ σ.vars "query.n"=n∧
    σ.vars "cap.R"=R∧ σ.vars "cap.D"=D∧ σ.vars "search.budget"=N

theorem normalizeQuery_spec (B M m n R D N:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hR:R≤ M) (hD:0 < D) (hDM:D≤ M)
    (hdim:(m + n) * n + m + n + 1 < B) (hB:2 * M ^ 2 + 3 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (Input P R D N) normalizeQuery
      (fun _ τ => RamSearchBounds.Input (normalizedMatrix P R) (normalizedBound P (1 / (D:ℚ))) N τ)
      ((72 * M.size + 181) * ((m + n) * n) + (72 * M.size + 189) * (m + n) + 78):=by
  rintro σ ⟨hσA,hσb,hσrows,hσrhs,hσcenter,hσshape,hσworkspace,hσnormal,
    hσm,hσn,hσR,hσD,hσN⟩
  obtain ⟨τ,hr₁,hτrows,hτA,hτm,hτn,hτR⟩:=
    RamNormalizedMatrix.normalizeMatrix_spec B M m n P R hM hR hdim hB hA σ
      ⟨hσA,hσrows,hσm,hσn,hσR⟩
  have hτb:=RamEllipsoidUpdate.represents_frame hr₁ "pad.b" _ hσb (by decide) (by decide) (by decide)
  have hτrhs:=RamAdvanceState.extents_of_run hr₁ "search.rhs" (m + n) hσrhs
  have hτD:=(hr₁.frame_var "cap.D" (by decide)).trans hσD
  obtain ⟨υ,hr₂,hυrhs,hυb,hυm,hυn,hυD⟩:=
    RamNormalizedBound.normalizeBound_spec B M m n P D hM hD hDM (by omega) hB hb τ
      ⟨hτb,hτrhs,hτm,hτn,hτD⟩
  have hυrows:=RamEllipsoidUpdate.represents_frame hr₂ "search.rows" _ hτrows
    (by decide) (by decide) (by decide)
  have hnB:n < B:=by omega
  have hmB:m < B:=by omega
  have hsumB:m + n < B:=by omega
  have hr₃:Run B (.assign "vec.n" (.var "query.n")) υ (υ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hυn] using evalB_var (B:=B) (σ:=υ) (x:= "query.n") (hυn ▸ hnB))
  have hr₄:Run B (.assign "row.m" (.add (.var "query.m") (.var "query.n")))
      (υ.setVar "vec.n" n) ((υ.setVar "vec.n" n).setVar "row.m" (m + n)) 4:=by
    apply Run.assign
    simpa [hυm,hυn] using evalB_bin
      (evalB_var (B:=B) (σ:=υ.setVar "vec.n" n) (x:= "query.m") (by simpa [hυm] using hmB))
      (evalB_var (B:=B) (σ:=υ.setVar "vec.n" n) (x:= "query.n") (by simpa [hυn] using hnB))
      (show Bop.add.apply ((υ.setVar "vec.n" n).vars "query.m")
        ((υ.setVar "vec.n" n).vars "query.n") < B by simpa [hυm,hυn] using hsumB)
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hN:=(hr.frame_var "search.budget" (by decide)).trans hσN
  have hrows:=rows_of_represents "search.rows" (fun i j => (normalizedMatrix P R i j:ℚ)) υ hυrows
  refine ⟨_,hr.mono (by omega), ?_, ?_,
    RamAdvanceState.extents_of_run hr "ell.center" n hσcenter,
    RamAdvanceState.extents_of_run hr "ell.shape" (n * n) hσshape,
    RamAdvanceState.workspace_of_run hr n hσworkspace,
    RamAdvanceState.extents_of_run hr "ell.normal" n hσnormal, ?_, ?_,hN⟩
  · simpa only [RamMatrixRows.MatrixRows,RamMatrixRows.Slice,arrs_setVar] using hrows
  · simpa only [Represents,arrs_setVar] using hυrhs
  · simp
  · simp

end Lax109476Proofs.RamNormalizeQuery

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

namespace Lax109476Proofs.RamNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def powerInvariant (a n:ℕ) (σ:Env):Prop:=
  σ.vars "power.base"=a∧ σ.vars "power.exponent"=n∧
    σ.vars "power.i" ≤ n∧ σ.vars "power.value"=a ^ σ.vars "power.i"

theorem powerStep_spec (B a n:ℕ) (ha:1≤ a) (haB:a < B)
    (hnB:n < B) (hpB:a ^ n < B):
    Spec B (fun σ => powerInvariant a n σ∧ σ.vars "power.i" < n) powerStep
      (fun σ τ => powerInvariant a n τ∧ τ.vars "power.i"=σ.vars "power.i" + 1) 8:=by
  rintro σ ⟨⟨hσa,hσn,hσiN,hσp⟩,hσi⟩
  have hiB:σ.vars "power.i" < B:=hσi.trans hnB
  have hnextB:a ^ (σ.vars "power.i" + 1) < B:=
    (Nat.pow_le_pow_right ha hσi).trans_lt hpB
  have hcurB:a ^ σ.vars "power.i" < B:=
    (Nat.pow_le_pow_right ha hσiN).trans_lt hpB
  have hmulB:σ.vars "power.value" * σ.vars "power.base" < B:=by
    rw [hσp,hσa, ← pow_succ]
    exact hnextB
  have h1:1 < B:=ha.trans_lt haB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (powerInvariant a n τ) (@Eq Nat (Env.vars τ "power.i") (c0 (Env.vars σ_1 "power.i") ((1:Nat))))) σ; let c2:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c3:Env:=Env.setVar σ "power.value" c2; let c4:Nat:=Env.vars c3 "power.i"; let c5:Nat:=c0 c4 ((1:Nat)); let c6:Env:=Env.setVar c3 "power.i" c5; let c7:Nat→ Nat:=c0 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c9:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c10:Nat:=c7 (Expr.size c9); @Exists.intro Env (fun (σ':Env) => And (Run B powerStep σ σ' ((8:Nat))) (c1 σ')) c6 (@And.intro (Run B powerStep σ c6 ((8:Nat))) (c1 c6) (RunStep.mono B powerStep σ c6 (c0 c8 c10) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c9) σ c3 c6 c8 c10 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c2 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g4671_0_0_0)) (RunStep.eval_var B σ "power.base" (?nAX_g4671_0_0_1)) hmulB)) (RunStep.assign B c3 "power.i" c9 c5 (RunStep.eval_add B c3 (Expr.var "power.i") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c3 "power.i" (?nAX_g4671_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c3 h1) (?nAX_g4671_0_0_3)))) (?nAX_g4671_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4671_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [powerInvariant,pow_succ]

theorem power_spec (B a n:ℕ) (ha:1≤ a) (haB:a < B)
    (hnB:n < B) (hpB:a ^ n < B):
    Spec B (fun σ => σ.vars "power.base"=a∧ σ.vars "power.exponent"=n) power
      (fun _ τ => τ.vars "power.value"=a ^ n∧
        τ.vars "power.base"=a∧ τ.vars "power.exponent"=n) (12 * n + 8):=by
  have hlo:=Spec.forRangeZero "power.i" "power.exponent" (powerInvariant a n) n 8 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (powerStep_spec B a n ha haB hnB hpB)
  have h1:1 < B:=ha.trans_lt haB
  rintro σ ⟨hσa,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "power.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "power.i") (Expr.var "power.exponent")) powerStep); let c1:Env:=Env.setVar σ "power.value" ((1:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c3 (c4 (c3 ((8:Nat)) ((4:Nat))) n) ((6:Nat)); let c6:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (powerInvariant a n σ') (@Eq Nat (Env.vars σ' "power.i") n)); let c7:Nat:=c3 (c4 ((12:Nat)) n) ((8:Nat)); let c8:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a n; let c9:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "power.value") c8) (And (@Eq Nat (Env.vars τ "power.base") a) (@Eq Nat (Env.vars τ "power.exponent") n))) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B power σ σ' c7) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c11) (RunStep.use B (fun (σ_1:Env) => powerInvariant a n (Env.setVar σ_1 "power.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (powerInvariant a n σ') (@Eq Nat (Env.vars σ' "power.i") n)) c5 hlo c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (powerInvariant a n w) (@Eq Nat (Env.vars w "power.i") n))) => let c0_1:Prop:=And (powerInvariant a n w) (@Eq Nat (Env.vars w "power.i") n); @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c11) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c10 w (@And.intro (Run B power σ w c7) (c9 w) (RunStep.mono B power σ w (c3 c12 c5) c7 (RunStep.seq B (Com.assign "power.value" (Expr.lit ((1:Nat)))) c0 σ c1 w c12 c5 (RunStep.assign B σ "power.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) left) (?nAX_g4673_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4673_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [powerInvariant]

def factorialInvariant (n:ℕ) (σ:Env):Prop:=
  σ.vars "factorial.n"=n∧ σ.vars "factorial.i" ≤ n∧
    σ.vars "factorial.value"=(σ.vars "factorial.i").factorial

theorem factorialStep_spec (B n:ℕ) (hnB:n < B) (hfB:n.factorial < B):
    Spec B (fun σ => factorialInvariant n σ∧ σ.vars "factorial.i" < n) factorialStep
      (fun σ τ => factorialInvariant n τ∧ τ.vars "factorial.i"=σ.vars "factorial.i" + 1) 8:=by
  rintro σ ⟨⟨hσn,hσiN,hσf⟩,hσi⟩
  have h1:1 < B:=lt_of_le_of_lt (Nat.factorial_pos n) hfB
  have hiB:σ.vars "factorial.i" < B:=hσi.trans hnB
  have hi1B:σ.vars "factorial.i" + 1 < B:=lt_of_le_of_lt hσi hnB
  have hcurB:(σ.vars "factorial.i").factorial < B:=(Nat.factorial_le hσiN).trans_lt hfB
  have hnextB:(σ.vars "factorial.i" + 1).factorial < B:=(Nat.factorial_le hσi).trans_lt hfB
  have hmulB:σ.vars "factorial.value" * (σ.vars "factorial.i" + 1) < B:=by
    rw [hσf,Nat.mul_comm, ← Nat.factorial_succ]
    exact hnextB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (factorialInvariant n τ) (@Eq Nat (Env.vars τ "factorial.i") (c0 (Env.vars σ_1 "factorial.i") ((1:Nat))))) σ; let c2:Nat:=c0 (Env.vars σ "factorial.i") ((1:Nat)); let c3:Env:=Env.setVar σ "factorial.i" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "factorial.value"; let c6:Nat:=c4 "factorial.i"; let c7:Nat:=Nat.mul c5 c6; let c8:Env:=Env.setVar c3 "factorial.value" c7; let c9:Nat→ Nat:=c0 ((1:Nat)); let c10:Expr:=Expr.add (Expr.var "factorial.i") (Expr.lit ((1:Nat))); let c11:Nat:=c9 (Expr.size c10); let c12:Nat:=c9 (Expr.size (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i"))); @Exists.intro Env (fun (σ':Env) => And (Run B factorialStep σ σ' ((8:Nat))) (c1 σ')) c8 (@And.intro (Run B factorialStep σ c8 ((8:Nat))) (c1 c8) (RunStep.mono B factorialStep σ c8 (c0 c11 c12) ((8:Nat)) (RunStep.seq B (Com.assign "factorial.i" c10) (Com.assign "factorial.value" (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i"))) σ c3 c8 c11 c12 (RunStep.assign B σ "factorial.i" c10 c2 (RunStep.eval_add B σ (Expr.var "factorial.i") (Expr.lit ((1:Nat))) (Env.vars σ "factorial.i") ((1:Nat)) (RunStep.eval_var B σ "factorial.i" hiB) (RunStep.eval_lit B ((1:Nat)) σ h1) hi1B)) (RunStep.assign B c3 "factorial.value" (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i")) c7 (RunStep.eval_mul B c3 (Expr.var "factorial.value") (Expr.var "factorial.i") c5 c6 (RunStep.eval_var B c3 "factorial.value" (?nAX_g4676_0_0_0)) (RunStep.eval_var B c3 "factorial.i" (?nAX_g4676_0_0_1)) (?nAX_g4676_0_0_2)))) (?nAX_g4676_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4676_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [factorialInvariant,Nat.factorial_succ,Nat.mul_comm]

theorem factorial_spec (B n:ℕ) (hnB:n < B) (hfB:n.factorial < B):
    Spec B (fun σ => σ.vars "factorial.n"=n) factorial
      (fun _ τ => τ.vars "factorial.value"=n.factorial∧ τ.vars "factorial.n"=n)
      (12 * n + 8):=by
  have hlo:=Spec.forRangeZero "factorial.i" "factorial.n" (factorialInvariant n) n 8 hnB
    (fun _ h => h.2.1) (fun _ h => h.1) (factorialStep_spec B n hnB hfB)
  have h1:1 < B:=lt_of_le_of_lt (Nat.factorial_pos n) hfB
  intro σ hσ
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "factorial.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "factorial.i") (Expr.var "factorial.n")) factorialStep); let c1:Env:=Env.setVar σ "factorial.value" ((1:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c3 (c4 (c3 ((8:Nat)) ((4:Nat))) n) ((6:Nat)); let c6:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (factorialInvariant n σ') (@Eq Nat (Env.vars σ' "factorial.i") n)); let c7:Nat:=c3 (c4 ((12:Nat)) n) ((8:Nat)); let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "factorial.value") (Nat.factorial n)) (@Eq Nat (Env.vars τ "factorial.n") n)) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B factorial σ σ' c7) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c10) (RunStep.use B (fun (σ_1:Env) => factorialInvariant n (Env.setVar σ_1 "factorial.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (factorialInvariant n σ') (@Eq Nat (Env.vars σ' "factorial.i") n)) c5 hlo c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (factorialInvariant n w) (@Eq Nat (Env.vars w "factorial.i") n))) => let c0_1:Prop:=And (factorialInvariant n w) (@Eq Nat (Env.vars w "factorial.i") n); @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c10) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B factorial σ w c7) (c8 w) (RunStep.mono B factorial σ w (c3 c11 c5) c7 (RunStep.seq B (Com.assign "factorial.value" (Expr.lit ((1:Nat)))) c0 σ c1 w c11 c5 (RunStep.assign B σ "factorial.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) left) (?nAX_g4678_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4678_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [factorialInvariant]

end Lax109476Proofs.RamNaturalPower

end

section

namespace Lax109476Proofs.RamCoordinateCap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNaturalPower RamFrame IntegerCertificates

def magnitude (m n H:ℕ):ℕ:=
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  m + n + H + K + K * H * H + a + K.factorial + a ^ K + coordinateCap m n H + 10

set_option maxHeartbeats 0 in
theorem prepareCap_spec (B m n H:ℕ) (hB:magnitude m n H < B):
    Spec B (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.H"=H)
      prepareCap
      (fun _ τ => τ.vars "cap.value"=coordinateCap m n H∧ τ.vars "cap.H"=H∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n)
      (24 * (2 * (m + n) + 2) + 42):=by
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  have hmB:m < B:=by dsimp [magnitude] at hB; omega
  have hnB:n < B:=by dsimp [magnitude] at hB; omega
  have hHB:H < B:=by dsimp [magnitude] at hB; omega
  have hKB:K < B:=by dsimp [magnitude,K] at hB ⊢; omega
  have haB:a < B:=by dsimp [magnitude,K,a] at hB ⊢; omega
  have hfB:K.factorial < B:=by dsimp [magnitude,K] at hB ⊢; omega
  have hpB:a ^ K < B:=by dsimp [magnitude,K,a] at hB ⊢; omega
  have hcB:coordinateCap m n H < B:=by dsimp [magnitude] at hB; omega
  have h1:1 < B:=by dsimp [magnitude] at hB; omega
  have h2:2 < B:=by dsimp [magnitude] at hB; omega
  have hsum:m + n < B:=by dsimp [K] at hKB; omega
  have hdouble:2 * (m + n) < B:=by dsimp [K] at hKB; omega
  have hkhh:K * H * H < B:=by dsimp [a] at haB; omega
  have hkh:K * H < B:=by
    by_cases hH:H=0
    · simp [hH]; omega
    · have hm:=Nat.le_mul_of_pos_right (K * H) (by omega:0 < H)
      exact hm.trans_lt hkhh
  have hfactorial:=spec_with_fields ["cap.k", "cap.H", "query.m", "query.n"]
    (factorial_spec B K hKB hfB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hpower:=spec_with_fields ["cap.k", "cap.H", "cap.factorial", "query.m", "query.n"]
    (power_spec B a K (by dsimp [a]; omega) haB hKB hpB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hc:coordinateCap m n H=K.factorial * a ^ K:=by
    simp only [coordinateCap,K,a,pow_two,Nat.mul_assoc]
  rintro σ ⟨hσm,hσn,hσH⟩
  dsimp only [K] at hfactorial hpower hfB hpB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((2:Nat)); let c3:Nat:=c0 (Env.vars σ "query.m") (Env.vars σ "query.n"); let c4:Nat:=c2 c3; let c5:Nat:=c0 c4 ((2:Nat)); let c6:Env:=Env.setVar σ "cap.k" c5; let c7:Nat:=Env.vars c6 "cap.k"; let c8:Env:=Env.setVar c6 "factorial.n" c7; let c9:Env→ Nat→ Prop:=Run B factorial c8; let c10:Nat:=c0 (c2 (c0 m n)) ((2:Nat)); let c11:Nat:=c0 (c1 ((12:Nat)) c10) ((8:Nat)); let c12:Nat:=Nat.factorial c10; let c13:List String:= @List.cons String "query.m" (@List.cons String "query.n" (@List.nil String)); let c14:Env→ Env→ Prop:=FieldsAgree (@List.cons String "cap.k" (@List.cons String "cap.H" c13)); let c15:Env→ Prop:=c14 c8; let c16:String→ List Nat:=Env.arrs c8; let c17:Env→ Prop:=fun (σ':Env) => And (c9 σ' c11) (And (And (@Eq Nat (Env.vars σ' "factorial.value") c12) (@Eq Nat (Env.vars σ' "factorial.n") c10)) (And (c15 σ') (@Eq (String→ List Nat) (Env.arrs σ') c16))); let c18:Nat:=c0 (c1 ((24:Nat)) c10) ((42:Nat)); let c19:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "cap.value") (coordinateCap m n H)) (And (@Eq Nat (Env.vars τ "cap.H") H) (And (@Eq Nat (Env.vars τ "query.m") m) (@Eq Nat (Env.vars τ "query.n") n)))) σ; let c20:Env→ Prop:=fun (σ':Env) => And (Run B prepareCap σ σ' c18) (c19 σ'); let c21:Prop:= @Exists Env c20; let c22:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a c10; let c23:Env→ Env→ Prop:=FieldsAgree (@List.cons String "cap.k" (@List.cons String "cap.H" (@List.cons String "cap.factorial" c13))); let c24:Nat→ Nat:=c0 ((1:Nat)); let c25:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.add (Expr.var "query.m") (Expr.var "query.n")); let c26:Expr:=Expr.add c25 (Expr.lit ((2:Nat))); let c27:Nat:=c24 (Expr.size c26); let c28:Nat:=c24 (Expr.size (Expr.var "cap.k")); let c29:Nat→ Nat:=c0 c28; let c30:Nat→ Nat:=c0 c11; let c31:Nat:=c24 (Expr.size (Expr.var "factorial.value")); let c32:Expr:=Expr.mul (Expr.mul (Expr.var "cap.k") (Expr.var "cap.H")) (Expr.var "cap.H"); let c33:Expr:=Expr.add c32 (Expr.lit ((1:Nat))); let c34:Nat:=c24 (Expr.size c33); let c35:Nat:=c24 (Expr.size (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value"))); let c36:Nat:=c30 c35; let c37:Nat:=c29 c36; let c38:Nat:=c0 c34 c37; let c39:Nat:=c0 c31 c38; let c40:Nat:=c30 c39; let c41:Nat:=c29 c40; let c42:Com:=Com.assign "power.base" c33; let c43:Com:=Com.assign "cap.value" (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value")); let c44:Com:=Com.seq power c43; let c45:Com:=Com.seq (Com.assign "power.exponent" (Expr.var "cap.k")) c44; let c46:Com:=Com.seq c42 c45; let c47:Com:=Com.seq (Com.assign "cap.factorial" (Expr.var "factorial.value")) c46; let c48:Com:=Com.seq factorial c47; @Exists.casesOn Env c17 (fun (x:@Exists Env c17) => c21) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "factorial.n") c10) factorial (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "factorial.value") c12) (@Eq Nat (Env.vars τ "factorial.n") c10)) (And (c14 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c11 hfactorial c8 ?_) fun (w:Env) (h:And (c9 w c11) (And (And (@Eq Nat (Env.vars w "factorial.value") c12) (@Eq Nat (Env.vars w "factorial.n") c10)) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "factorial.value") c12) (@Eq Nat (Env.vars w "factorial.n") c10)) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)); let c1_1:String→ Nat:=Env.vars (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")); let c2_1:Nat:=c1_1 "cap.k"; let c3_1:Nat:=c1_1 "cap.H"; let c4_1:Nat:=c1 c2_1 c3_1; let c5_1:Nat:=c1 c4_1 c3_1; let c6_1:Nat:=c0 c5_1 ((1:Nat)); let c7_1:Env:=Env.setVar (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "power.base" c6_1; let c8_1:Nat:=Env.vars c7_1 "cap.k"; let c9_1:Env:=Env.setVar c7_1 "power.exponent" c8_1; let c10_1:Env→ Nat→ Prop:=Run B power c9_1; let c11_1:Env→ Prop:=c23 c9_1; let c12_1:String→ List Nat:=Env.arrs c9_1; let c13_1:Env→ Prop:=fun (σ':Env) => And (c10_1 σ' c11) (And (And (@Eq Nat (Env.vars σ' "power.value") c22) (And (@Eq Nat (Env.vars σ' "power.base") a) (@Eq Nat (Env.vars σ' "power.exponent") c10))) (And (c11_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c12_1))); let c14_1:String→ Nat:=Env.vars c9_1; @And.casesOn (c9 w c11) c0_1 (fun (x:And (c9 w c11) c0_1) => c21) h fun (left:c9 w c11) (right:c0_1) => @Exists.casesOn Env c13_1 (fun (x:@Exists Env c13_1) => c21) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "power.base") a) (@Eq Nat (Env.vars σ_1 "power.exponent") c10)) power (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "power.value") c22) (And (@Eq Nat (Env.vars τ "power.base") a) (@Eq Nat (Env.vars τ "power.exponent") c10))) (And (c23 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c11 hpower c9_1 ?_) fun (w_1:Env) (h_1:And (c10_1 w_1 c11) (And (And (@Eq Nat (Env.vars w_1 "power.value") c22) (And (@Eq Nat (Env.vars w_1 "power.base") a) (@Eq Nat (Env.vars w_1 "power.exponent") c10))) (And (c11_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c12_1)))) => let c0_2:Prop:=And (And (@Eq Nat (Env.vars w_1 "power.value") c22) (And (@Eq Nat (Env.vars w_1 "power.base") a) (@Eq Nat (Env.vars w_1 "power.exponent") c10))) (And (c11_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c12_1)); let c1_2:Nat:=c1 (Env.vars w_1 "cap.factorial") (Env.vars w_1 "power.value"); let c2_2:Env:=Env.setVar w_1 "cap.value" c1_2; let c3_2:String→ Nat:=Env.vars c2_2; @And.casesOn (c10_1 w_1 c11) c0_2 (fun (x:And (c10_1 w_1 c11) c0_2) => c21) h_1 fun (left_1:c10_1 w_1 c11) (right_1:c0_2) => @Exists.intro Env c20 c2_2 (@And.intro (Run B prepareCap σ c2_2 c18) (c19 c2_2) (RunStep.mono B prepareCap σ c2_2 (c0 c27 c41) c18 (RunStep.seq B (Com.assign "cap.k" c26) (Com.seq (Com.assign "factorial.n" (Expr.var "cap.k")) c48) σ c6 c2_2 c27 c41 (RunStep.assign B σ "cap.k" c26 c5 (RunStep.eval_add B σ c25 (Expr.lit ((2:Nat))) c4 ((2:Nat)) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.add (Expr.var "query.m") (Expr.var "query.n")) ((2:Nat)) c3 (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_add B σ (Expr.var "query.m") (Expr.var "query.n") (Env.vars σ "query.m") (Env.vars σ "query.n") (RunStep.eval_var B σ "query.m" (?nAX_g4681_0_0_0)) (RunStep.eval_var B σ "query.n" (?nAX_g4681_0_0_1)) (?nAX_g4681_0_0_2)) (?nAX_g4681_0_0_3)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4681_0_0_4))) (RunStep.seq B (Com.assign "factorial.n" (Expr.var "cap.k")) c48 c6 c8 c2_2 c28 c40 (RunStep.assign B c6 "factorial.n" (Expr.var "cap.k") c7 (RunStep.eval_var B c6 "cap.k" (?nAX_g4681_0_0_5))) (RunStep.seq B factorial c47 c8 w c2_2 c11 c39 left (RunStep.seq B (Com.assign "cap.factorial" (Expr.var "factorial.value")) c46 w (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c2_2 c31 c38 (RunStep.assign B w "cap.factorial" (Expr.var "factorial.value") (Env.vars w "factorial.value") (RunStep.eval_var B w "factorial.value" (?nAX_g4681_0_0_6))) (RunStep.seq B c42 c45 (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c7_1 c2_2 c34 c37 (RunStep.assign B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "power.base" c33 c6_1 (RunStep.eval_add B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c32 (Expr.lit ((1:Nat))) c5_1 ((1:Nat)) (RunStep.eval_mul B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) (Expr.mul (Expr.var "cap.k") (Expr.var "cap.H")) (Expr.var "cap.H") c4_1 c3_1 (RunStep.eval_mul B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) (Expr.var "cap.k") (Expr.var "cap.H") c2_1 c3_1 (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.k" ?_) (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.H" ?_) ?_) (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.H" ?_) ?_) (RunStep.eval_lit B ((1:Nat)) (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) h1) ?_)) (RunStep.seq B (Com.assign "power.exponent" (Expr.var "cap.k")) c44 c7_1 c9_1 c2_2 c28 c36 (RunStep.assign B c7_1 "power.exponent" (Expr.var "cap.k") c8_1 (RunStep.eval_var B c7_1 "cap.k" ?_)) (RunStep.seq B power c43 c9_1 w_1 c2_2 c11 c35 left_1 (RunStep.assign B w_1 "cap.value" (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value")) c1_2 (RunStep.eval_mul B w_1 (Expr.var "cap.factorial") (Expr.var "power.value") (Env.vars w_1 "cap.factorial") (Env.vars w_1 "power.value") (RunStep.eval_var B w_1 "cap.factorial" ?_) (RunStep.eval_var B w_1 "power.value" (?nAX_g4681_0_0_7)) ?_))))))))) (?nAX_g4681_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4681_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hfactorial hpower
  all_goals simp_all [FieldsAgree,K,a,hc,Nat.mul_assoc]

end Lax109476Proofs.RamCoordinateCap

end

section

namespace Lax109476Proofs.RamCoordinateCapBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerCertificates RationalSizeBounds RamCoordinateCap

theorem magnitude_bound (m n H:ℕ) (hH:1≤ H):
    magnitude m n H≤ m + n + 7 * coordinateCap m n H + 10:=by
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  let F:=K.factorial
  let V:=a ^ K
  let C:=coordinateCap m n H
  have hK:0 < K:=by dsimp [K]; omega
  have ha:1≤ a:=by dsimp [a]; omega
  have hV:0 < V:=pow_pos (by omega:0 < a) K
  have hF:0 < F:=Nat.factorial_pos K
  have hC:C=F * V:=by simp only [C,coordinateCap,K,F,V,a,pow_two,Nat.mul_assoc]
  have hFC:F≤ C:=by rw [hC]; exact Nat.le_mul_of_pos_right _ hV
  have hVC:V≤ C:=by rw [hC]; exact Nat.le_mul_of_pos_left _ hF
  have haV:a≤ V:=le_self_pow ha (by omega:K ≠ 0)
  have haC:=haV.trans hVC
  have hKC:K≤ C:=(Nat.self_le_factorial K).trans hFC
  have hprod:K * H * H≤ C:=(by dsimp [a] at haC; omega)
  have hHC:H≤ C:=(Nat.le_mul_of_pos_left H (Nat.mul_pos hK (by omega))).trans hprod
  change m + n + H + K + K * H * H + a + F + V + C + 10≤ m + n + 7 * C + 10
  omega

theorem magnitude_fits (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    magnitude m n (2 ^ (2 * S)) < 2 ^ w:=by
  let Q:=32 * (S + 1) ^ 2
  have hCsize:(coordinateCap m n (2 ^ (2 * S))).size≤ Q:=
    certificate_cap_size (2 * (m + n) + 2) S (by omega)
  have hC:coordinateCap m n (2 ^ (2 * S)) < 2 ^ Q:=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hCsize)
  have hSQ:S + 10≤ Q:=by dsimp [Q]; nlinarith
  have hS:S + 10 < 2 ^ Q:=(Nat.lt_two_pow_self (n:=S + 10)).trans_le
    (Nat.pow_le_pow_right (by decide) hSQ)
  have hmag:=magnitude_bound m n (2 ^ (2 * S)) (Nat.one_le_pow _ _ (by decide))
  have hlarge:magnitude m n (2 ^ (2 * S)) < 2 ^ (Q + 3):=by
    rw [pow_add]
    norm_num
    omega
  have hQw:Q + 3≤ w:=by dsimp [wordWidth,Q] at hw ⊢; omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) hQw)

theorem prepareCap_bounded_spec (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧
        σ.vars "cap.H"=2 ^ (2 * S)) prepareCap
      (fun _ τ => τ.vars "cap.value"=coordinateCap m n (2 ^ (2 * S))∧
        τ.vars "cap.H"=2 ^ (2 * S)∧ τ.vars "query.m"=m∧ τ.vars "query.n"=n)
      (48 * S + 90):=by
  exact (prepareCap_spec (2 ^ w) m n (2 ^ (2 * S)) (magnitude_fits m n S w hdim hw)).mono (by omega)

end Lax109476Proofs.RamCoordinateCapBounds

end

section

namespace Lax109476Proofs.RamFeasibilityScales

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamFrame RamBitLength IntegerCertificates NormalizedFeasibility EllipsoidSequence

def magnitude (m n H:ℕ):ℕ:=
  let C:=coordinateCap m n H
  let G:=m * C + n * m * H * C
  let D:=precisionDenominator m n H
  let R:=outerScale n C
  let Z:=ballDenominator m n H
  let E:=ballExponent m n H
  m + n + H + C + m * C + n * m + n * m * H + n * m * H * C + G + (G + 1) +
    D + (n + 1) + (C + 1) + 4 * (n + 1) + R + n * H + (n * H + 1) +
    D * (n * H + 1) + Z + E + E * n + (E * n + 1) +
    thresholdSteps n E + (thresholdSteps n E + 1) + 20

def Output (m n H:ℕ) (σ:Env):Prop:=
  σ.vars "cap.D"=precisionDenominator m n H∧
    σ.vars "cap.R"=outerScale n (coordinateCap m n H)∧
    σ.vars "cap.E"=ballExponent m n H∧
    σ.vars "search.budget"=thresholdSteps n (ballExponent m n H) + 1∧
    σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.H"=H

set_option maxHeartbeats 0 in
theorem prepareScales_spec (B m n H:ℕ) (hB:magnitude m n H < B):
    Spec B (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧
        σ.vars "cap.H"=H∧ σ.vars "cap.value"=coordinateCap m n H)
      prepareScales (fun _ τ => Output m n H τ) (12 * (ballExponent m n H) + 62):=by
  let C:=coordinateCap m n H
  let G:=m * C + n * m * H * C
  let D:=precisionDenominator m n H
  let R:=outerScale n C
  let Z:=ballDenominator m n H
  let E:=ballExponent m n H
  have h2:2 < B:=by dsimp [magnitude] at hB; omega
  have hD:D=2 * (G + 1):=rfl
  have hR:R=4 * (n + 1) * (C + 1):=rfl
  have hZ:Z=D * (n * H + 1) * R:=rfl
  have hE:E=Z.size:=rfl
  have hZB:Z < B:=by dsimp [Z,magnitude] at hB ⊢; omega
  have hlength:=spec_with_fields ["cap.D", "cap.R", "cap.value", "cap.H", "query.m", "query.n"]
    (bitLength_spec B Z h2 hZB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rfl)
  rintro σ ⟨hσm,hσn,hσH,hσC⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c1 (Env.vars σ "query.m") (Env.vars σ "cap.value"); let c3:Nat:=c1 (Env.vars σ "query.n") (Env.vars σ "query.m"); let c4:Nat:=c1 c3 (Env.vars σ "cap.H"); let c5:Nat:=c1 c4 (Env.vars σ "cap.value"); let c6:Nat:=c0 c2 c5; let c7:Env:=Env.setVar σ "cap.G" c6; let c8:Nat:=Env.vars c7 "cap.G"; let c9:Nat:=c0 c8 ((1:Nat)); let c10:Nat:=c1 ((2:Nat)) c9; let c11:Env:=Env.setVar c7 "cap.D" c10; let c12:Nat→ Nat:=c1 ((4:Nat)); let c13:String→ Nat:=Env.vars c11; let c14:Nat:=c13 "query.n"; let c15:Nat:=c0 c14 ((1:Nat)); let c16:Nat:=c12 c15; let c17:Nat:=c13 "cap.value"; let c18:Nat:=c0 c17 ((1:Nat)); let c19:Nat:=c1 c16 c18; let c20:Env:=Env.setVar c11 "cap.R" c19; let c21:String→ Nat:=Env.vars c20; let c22:Nat:=c21 "cap.D"; let c23:Nat:=c21 "query.n"; let c24:Nat:=c21 "cap.H"; let c25:Nat:=c1 c23 c24; let c26:Nat:=c0 c25 ((1:Nat)); let c27:Nat:=c1 c22 c26; let c28:Nat:=c21 "cap.R"; let c29:Nat:=c1 c27 c28; let c30:Env:=Env.setVar c20 "cap.ball" c29; let c31:Nat:=Env.vars c30 "cap.ball"; let c32:Env:=Env.setVar c30 "bits.v" c31; let c33:Env→ Nat→ Prop:=Run B bitLength c32; let c34:Nat→ Nat:=c1 ((12:Nat)); let c35:Nat:=c0 (c34 (Nat.size Z)) ((6:Nat)); let c36:Env→ Env→ Prop:=FieldsAgree (@List.cons String "cap.D" (@List.cons String "cap.R" (@List.cons String "cap.value" (@List.cons String "cap.H" (@List.cons String "query.m" (@List.cons String "query.n" (@List.nil String))))))); let c37:Env→ Prop:=c36 c32; let c38:String→ List Nat:=Env.arrs c32; let c39:Env→ Prop:=fun (σ':Env) => And (c33 σ' c35) (And (And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size Z))) (And (c37 σ') (@Eq (String→ List Nat) (Env.arrs σ') c38))); let c40:Nat:=c0 (c34 (ballExponent m n H)) ((62:Nat)); let c41:Env→ Prop:=(fun (x τ:Env) => Output m n H τ) σ; let c42:Env→ Prop:=fun (σ':Env) => And (Run B prepareScales σ σ' c40) (c41 σ'); let c43:Prop:= @Exists Env c42; let c44:Nat→ Nat:=c0 ((1:Nat)); let c45:Expr:=Expr.mul (Expr.mul (Expr.var "query.n") (Expr.var "query.m")) (Expr.var "cap.H"); let c46:Expr:=Expr.mul c45 (Expr.var "cap.value"); let c47:Expr:=Expr.add (Expr.mul (Expr.var "query.m") (Expr.var "cap.value")) c46; let c48:Nat:=c44 (Expr.size c47); let c49:Expr:=Expr.add (Expr.var "cap.G") (Expr.lit ((1:Nat))); let c50:Expr:=Expr.mul (Expr.lit ((2:Nat))) c49; let c51:Nat:=c44 (Expr.size c50); let c52:Expr:=Expr.add (Expr.var "query.n") (Expr.lit ((1:Nat))); let c53:Expr:=Expr.mul (Expr.lit ((4:Nat))) c52; let c54:Expr→ Expr:=Expr.mul c53; let c55:Expr:=Expr.add (Expr.var "cap.value") (Expr.lit ((1:Nat))); let c56:Expr:=c54 c55; let c57:Nat:=c44 (Expr.size c56); let c58:Expr:=Expr.add (Expr.mul (Expr.var "query.n") (Expr.var "cap.H")) (Expr.lit ((1:Nat))); let c59:Expr:=Expr.mul (Expr.var "cap.D") c58; let c60:Expr:=Expr.mul c59 (Expr.var "cap.R"); let c61:Nat:=c44 (Expr.size c60); let c62:Nat:=c44 (Expr.size (Expr.var "cap.ball")); let c63:Nat:=c44 (Expr.size (Expr.var "bits.k")); let c64:Expr:=Expr.add (Expr.mul (Expr.var "cap.E") (Expr.var "query.n")) (Expr.lit ((1:Nat))); let c65:Expr:=c54 c64; let c66:Expr:=Expr.add c65 (Expr.lit ((1:Nat))); let c67:Nat:=c44 (Expr.size c66); let c68:Nat:=c0 c63 c67; let c69:Nat:=c0 c35 c68; let c70:Nat:=c0 c62 c69; let c71:Nat:=c0 c61 c70; let c72:Nat:=c0 c57 c71; let c73:Nat:=c0 c51 c72; let c74:Com:=Com.assign "cap.D" c50; let c75:Com:=Com.assign "cap.R" c56; let c76:Com:=Com.assign "cap.ball" c60; let c77:Com:=Com.assign "search.budget" c66; let c78:Com:=Com.seq (Com.assign "cap.E" (Expr.var "bits.k")) c77; let c79:Com:=Com.seq bitLength c78; let c80:Com:=Com.seq (Com.assign "bits.v" (Expr.var "cap.ball")) c79; let c81:Com:=Com.seq c76 c80; let c82:Com:=Com.seq c75 c81; @Exists.casesOn Env c39 (fun (x:@Exists Env c39) => c43) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "bits.v") Z) bitLength (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "bits.v") ((0:Nat))) (@Eq Nat (Env.vars τ "bits.k") (Nat.size Z))) (And (c36 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c35 hlength c32 ?_) fun (w:Env) (h:And (c33 w c35) (And (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size Z))) (And (c37 w) (@Eq (String→ List Nat) (Env.arrs w) c38)))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size Z))) (And (c37 w) (@Eq (String→ List Nat) (Env.arrs w) c38)); let c1_1:String→ Nat:=Env.vars (Env.setVar w "cap.E" (Env.vars w "bits.k")); let c2_1:Nat:=c1_1 "query.n"; let c3_1:Nat:=c0 c2_1 ((1:Nat)); let c4_1:Nat:=c12 c3_1; let c5_1:Nat:=c1_1 "cap.E"; let c6_1:Nat:=c1 c5_1 c2_1; let c7_1:Nat:=c0 c6_1 ((1:Nat)); let c8_1:Nat:=c1 c4_1 c7_1; let c9_1:Nat:=c0 c8_1 ((1:Nat)); let c10_1:Env:=Env.setVar (Env.setVar w "cap.E" (Env.vars w "bits.k")) "search.budget" c9_1; @And.casesOn (c33 w c35) c0_1 (fun (x:And (c33 w c35) c0_1) => c43) h fun (left:c33 w c35) (right:c0_1) => @Exists.intro Env c42 c10_1 (@And.intro (Run B prepareScales σ c10_1 c40) (c41 c10_1) (RunStep.mono B prepareScales σ c10_1 (c0 c48 c73) c40 (RunStep.seq B (Com.assign "cap.G" c47) (Com.seq c74 c82) σ c7 c10_1 c48 c73 (RunStep.assign B σ "cap.G" c47 c6 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.m") (Expr.var "cap.value")) c46 c2 c5 (RunStep.eval_mul B σ (Expr.var "query.m") (Expr.var "cap.value") (Env.vars σ "query.m") (Env.vars σ "cap.value") (RunStep.eval_var B σ "query.m" ?_) (RunStep.eval_var B σ "cap.value" ?_) ?_) (RunStep.eval_mul B σ c45 (Expr.var "cap.value") c4 (Env.vars σ "cap.value") (RunStep.eval_mul B σ (Expr.mul (Expr.var "query.n") (Expr.var "query.m")) (Expr.var "cap.H") c3 (Env.vars σ "cap.H") (RunStep.eval_mul B σ (Expr.var "query.n") (Expr.var "query.m") (Env.vars σ "query.n") (Env.vars σ "query.m") (RunStep.eval_var B σ "query.n" ?_) (RunStep.eval_var B σ "query.m" ?_) ?_) (RunStep.eval_var B σ "cap.H" ?_) ?_) (RunStep.eval_var B σ "cap.value" ?_) ?_) ?_)) (RunStep.seq B c74 c82 c7 c11 c10_1 c51 c72 (RunStep.assign B c7 "cap.D" c50 c10 (RunStep.eval_mul B c7 (Expr.lit ((2:Nat))) c49 ((2:Nat)) c9 (RunStep.eval_lit B ((2:Nat)) c7 h2) (RunStep.eval_add B c7 (Expr.var "cap.G") (Expr.lit ((1:Nat))) c8 ((1:Nat)) (RunStep.eval_var B c7 "cap.G" ?_) (RunStep.eval_lit B ((1:Nat)) c7 (?nAX_g4689_0_0_0)) ?_) ?_)) (RunStep.seq B c75 c81 c11 c20 c10_1 c57 c71 (RunStep.assign B c11 "cap.R" c56 c19 (RunStep.eval_mul B c11 c53 c55 c16 c18 (RunStep.eval_mul B c11 (Expr.lit ((4:Nat))) c52 ((4:Nat)) c15 (RunStep.eval_lit B ((4:Nat)) c11 ?_) (RunStep.eval_add B c11 (Expr.var "query.n") (Expr.lit ((1:Nat))) c14 ((1:Nat)) (RunStep.eval_var B c11 "query.n" ?_) (RunStep.eval_lit B ((1:Nat)) c11 (?nAX_g4689_0_0_1)) ?_) ?_) (RunStep.eval_add B c11 (Expr.var "cap.value") (Expr.lit ((1:Nat))) c17 ((1:Nat)) (RunStep.eval_var B c11 "cap.value" ?_) (RunStep.eval_lit B ((1:Nat)) c11 (?nAX_g4689_0_0_2)) ?_) ?_)) (RunStep.seq B c76 c80 c20 c30 c10_1 c61 c70 (RunStep.assign B c20 "cap.ball" c60 c29 (RunStep.eval_mul B c20 c59 (Expr.var "cap.R") c27 c28 (RunStep.eval_mul B c20 (Expr.var "cap.D") c58 c22 c26 (RunStep.eval_var B c20 "cap.D" ?_) (RunStep.eval_add B c20 (Expr.mul (Expr.var "query.n") (Expr.var "cap.H")) (Expr.lit ((1:Nat))) c25 ((1:Nat)) (RunStep.eval_mul B c20 (Expr.var "query.n") (Expr.var "cap.H") c23 c24 (RunStep.eval_var B c20 "query.n" ?_) (RunStep.eval_var B c20 "cap.H" ?_) ?_) (RunStep.eval_lit B ((1:Nat)) c20 (?nAX_g4689_0_0_3)) ?_) ?_) (RunStep.eval_var B c20 "cap.R" ?_) ?_)) (RunStep.seq B (Com.assign "bits.v" (Expr.var "cap.ball")) c79 c30 c32 c10_1 c62 c69 (RunStep.assign B c30 "bits.v" (Expr.var "cap.ball") c31 (RunStep.eval_var B c30 "cap.ball" ?_)) (RunStep.seq B bitLength c78 c32 w c10_1 c35 c68 left (RunStep.seq B (Com.assign "cap.E" (Expr.var "bits.k")) c77 w (Env.setVar w "cap.E" (Env.vars w "bits.k")) c10_1 c63 c67 (RunStep.assign B w "cap.E" (Expr.var "bits.k") (Env.vars w "bits.k") (RunStep.eval_var B w "bits.k" ?_)) (RunStep.assign B (Env.setVar w "cap.E" (Env.vars w "bits.k")) "search.budget" c66 c9_1 (RunStep.eval_add B (Env.setVar w "cap.E" (Env.vars w "bits.k")) c65 (Expr.lit ((1:Nat))) c8_1 ((1:Nat)) (RunStep.eval_mul B (Env.setVar w "cap.E" (Env.vars w "bits.k")) c53 c64 c4_1 c7_1 (RunStep.eval_mul B (Env.setVar w "cap.E" (Env.vars w "bits.k")) (Expr.lit ((4:Nat))) c52 ((4:Nat)) c3_1 (RunStep.eval_lit B ((4:Nat)) (Env.setVar w "cap.E" (Env.vars w "bits.k")) ?_) (RunStep.eval_add B (Env.setVar w "cap.E" (Env.vars w "bits.k")) (Expr.var "query.n") (Expr.lit ((1:Nat))) c2_1 ((1:Nat)) (RunStep.eval_var B (Env.setVar w "cap.E" (Env.vars w "bits.k")) "query.n" ?_) (RunStep.eval_lit B ((1:Nat)) (Env.setVar w "cap.E" (Env.vars w "bits.k")) (?nAX_g4689_0_0_4)) ?_) ?_) (RunStep.eval_add B (Env.setVar w "cap.E" (Env.vars w "bits.k")) (Expr.mul (Expr.var "cap.E") (Expr.var "query.n")) (Expr.lit ((1:Nat))) c6_1 ((1:Nat)) (RunStep.eval_mul B (Env.setVar w "cap.E" (Env.vars w "bits.k")) (Expr.var "cap.E") (Expr.var "query.n") c5_1 c2_1 (RunStep.eval_var B (Env.setVar w "cap.E" (Env.vars w "bits.k")) "cap.E" ?_) (RunStep.eval_var B (Env.setVar w "cap.E" (Env.vars w "bits.k")) "query.n" ?_) ?_) (RunStep.eval_lit B ((1:Nat)) (Env.setVar w "cap.E" (Env.vars w "bits.k")) (?nAX_g4689_0_0_5)) ?_) ?_) (RunStep.eval_lit B ((1:Nat)) (Env.setVar w "cap.E" (Env.vars w "bits.k")) (?nAX_g4689_0_0_6)) ?_))))))))) (?nAX_g4689_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4689_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4689_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlength
  all_goals simp_all [Output,FieldsAgree,C,G,D,R,Z,E,hD,hR,hZ,hE,
    ballExponent,ballDenominator,precisionDenominator,Relaxation.relaxationDenominator,
    outerScale,thresholdSteps]
  all_goals dsimp [magnitude,ballExponent,ballDenominator,precisionDenominator,
    Relaxation.relaxationDenominator,outerScale,thresholdSteps] at hB
  all_goals omega

end Lax109476Proofs.RamFeasibilityScales

end

section

namespace Lax109476Proofs.RamFeasibilityScaleBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerCertificates NormalizedFeasibility EllipsoidSequence IterationBudget RamFeasibilityScales

theorem magnitude_bound (m n H:ℕ) (hH:1≤ H):
    magnitude m n H≤ 30 * (ballDenominator m n H + H +
      (thresholdSteps n (ballExponent m n H) + 1) + 1):=by
  let C:=coordinateCap m n H
  let G:=m * C + n * m * H * C
  let D:=precisionDenominator m n H
  let R:=outerScale n C
  let Z:=ballDenominator m n H
  let E:=ballExponent m n H
  let T:=thresholdSteps n E
  have hC:1≤ C:=by
    dsimp [C,coordinateCap]
    exact Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by omega) _)
  have hD:D=2 * (G + 1):=rfl
  have hR:R=4 * (n + 1) * (C + 1):=rfl
  have hZ:Z=D * (n * H + 1) * R:=rfl
  have hDp:0 < D:=precisionDenominator_pos _ _ _
  have hRp:0 < R:=outerScale_pos _ _
  have hnp:0 < n * H + 1:=by omega
  have hDZ:D≤ Z:=by
    rw [hZ]
    exact (Nat.le_mul_of_pos_right _ hnp).trans (Nat.le_mul_of_pos_right _ hRp)
  have hRZ:R≤ Z:=by
    rw [hZ]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hDp hnp)
  have hnHZ:n * H + 1≤ Z:=by
    rw [hZ]
    exact (Nat.le_mul_of_pos_left _ hDp).trans (Nat.le_mul_of_pos_right _ hRp)
  have hDZprod:D * (n * H + 1)≤ Z:=by rw [hZ]; exact Nat.le_mul_of_pos_right _ hRp
  have hGZ:G + 1≤ Z:=(by rw [hD] at hDZ; omega)
  have hnmHC:n * m * H≤ n * m * H * C:=Nat.le_mul_of_pos_right _ (by omega)
  have hnmH:n * m≤ n * m * H:=Nat.le_mul_of_pos_right _ (by omega)
  have hmC:m≤ m * C:=Nat.le_mul_of_pos_right _ (by omega)
  have hEZ:E≤ Z:=RationalSizeBounds.size_le_self Z
  have hET:E * n + 1≤ T:=by
    dsimp [T,thresholdSteps]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hCn:C + 1≤ R:=by rw [hR]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hnC:4 * (n + 1)≤ R:=by rw [hR]; exact Nat.le_mul_of_pos_right _ (by omega)
  change m + n + H + C + m * C + n * m + n * m * H + n * m * H * C + G + (G + 1) +
    D + (n + 1) + (C + 1) + 4 * (n + 1) + R + n * H + (n * H + 1) +
    D * (n * H + 1) + Z + E + E * n + (E * n + 1) + T + (T + 1) + 20≤
      30 * (Z + H + (T + 1) + 1)
  dsimp only [G] at hGZ
  omega

theorem magnitude_fits (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    magnitude m n (2 ^ (2 * S)) < 2 ^ w:=by
  let Q:=1024 * (S + 1) ^ 4 + 128 * (S + 1) ^ 2 + 2 * S + 16
  let Z:=ballDenominator m n (2 ^ (2 * S))
  let T:=thresholdSteps n (ballExponent m n (2 ^ (2 * S)))
  have hZsize:=ballExponent_polynomial m n S hdim
  have hZ:Z < 2 ^ Q:=(Nat.lt_size_self Z).trans_le
    (Nat.pow_le_pow_right (by decide) (by change (ballExponent m n (2 ^ (2 * S)))≤ Q; dsimp [Q]; omega))
  have hTbound:=thresholdSteps_polynomial m n S hdim
  have hTQ:T + 2≤ Q:=by dsimp [Q,T] at *; omega
  have hT:T + 2 < 2 ^ Q:=(Nat.lt_two_pow_self (n:=T + 2)).trans_le
    (Nat.pow_le_pow_right (by decide) hTQ)
  have hH:2 ^ (2 * S) < 2 ^ Q:=Nat.pow_lt_pow_right (by decide) (by dsimp [Q]; omega)
  have hmag:=magnitude_bound m n (2 ^ (2 * S)) (Nat.one_le_pow _ _ (by decide))
  have hlarge:magnitude m n (2 ^ (2 * S)) < 2 ^ (Q + 7):=by
    rw [pow_add]
    norm_num
    change magnitude m n (2 ^ (2 * S))≤ 30 * (Z + 2 ^ (2 * S) + (T + 1) + 1) at hmag
    omega
  have hsq:(S + 1) ^ 2≤ (S + 1) ^ 4:=by
    exact pow_le_pow_right₀ (by omega:1≤ S + 1) (by decide:2≤ 4)
  have hSsq:S≤ (S + 1) ^ 2:=by nlinarith
  have hQw:Q + 7≤ w:=by dsimp [wordWidth,Q] at hw ⊢; nlinarith
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) hQw)

theorem prepareScales_bounded_spec (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧
        σ.vars "cap.H"=2 ^ (2 * S)∧ σ.vars "cap.value"=coordinateCap m n (2 ^ (2 * S)))
      prepareScales (fun _ τ => Output m n (2 ^ (2 * S)) τ)
      (1536 * (S + 1) ^ 2 + 62):=by
  exact (prepareScales_spec (2 ^ w) m n (2 ^ (2 * S)) (magnitude_fits m n S w hdim hw)).mono
    (by have h:=ballExponent_polynomial m n S hdim; omega)

end Lax109476Proofs.RamFeasibilityScaleBounds

end

section

namespace Lax109476Proofs.RamFeasibilityParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCoordinateCap RamFeasibilityScales IntegerCertificates

theorem prepareParameters_spec (m n S w:ℕ) (hdim:m + n≤ S)
    (hw:RamFeasibilityScaleBounds.wordWidth S≤ w):
    Spec (2 ^ w) (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "query.bits"=S)
      prepareParameters
      (fun σ τ => Output m n (2 ^ (2 * S)) τ∧
        τ.vars "cap.value"=coordinateCap m n (2 ^ (2 * S))∧
        τ.vars "query.bits"=S∧ τ.arrs=σ.arrs)
      (instructionBound S):=by
  have hsq:(S + 1) ^ 2≤ (S + 1) ^ 4:=
    pow_le_pow_right₀ (by omega:1≤ S + 1) (by decide:2≤ 4)
  have hSsq:S≤ (S + 1) ^ 2:=by nlinarith
  have hwcap:RamCoordinateCapBounds.wordWidth S≤ w:=by
    dsimp [RamCoordinateCapBounds.wordWidth,RamFeasibilityScaleBounds.wordWidth] at hw ⊢
    nlinarith
  have hmag:=RamFeasibilityScaleBounds.magnitude_fits m n S w hdim hw
  have hH:2 ^ (2 * S) < 2 ^ w:=by dsimp [RamFeasibilityScales.magnitude] at hmag; omega
  have he:2 * S < 2 ^ w:=(Nat.lt_two_pow_self (n:=2 * S)).trans hH
  have h1:1 < 2 ^ w:=by have h:=Nat.one_le_pow (2 * S) 2 (by decide); omega
  have hw2:2≤ w:=by
    have hp:1≤ (S + 1) ^ 4:=Nat.one_le_pow _ _ (by omega)
    dsimp [RamFeasibilityScaleBounds.wordWidth] at hw
    omega
  have h4:4≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) hw2
  have h2:2 < 2 ^ w:=by omega
  have hSB:S < 2 ^ w:=by omega
  intro σ ⟨hσm,hσn,hσbits⟩
  have hr₁:Run (2 ^ w)
      (.assign "cap.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "query.bits")))) σ
      (σ.setVar "cap.H" (2 ^ (2 * S))) 6:=by
    apply Run.assign
    simpa only [hσbits,Bop.apply_mul,Bop.apply_shiftl,one_mul] using
      evalB_bin (evalB_lit h1)
        (evalB_bin (evalB_lit h2) (evalB_var (B:=2 ^ w) (σ:=σ) (x:= "query.bits")
          (hσbits ▸ hSB)) (show Bop.mul.apply 2 (σ.vars "query.bits") < 2 ^ w by simpa [hσbits] using he))
        (show Bop.shiftl.apply 1 (Bop.mul.apply 2 (σ.vars "query.bits")) < 2 ^ w by simpa [hσbits] using hH)
  obtain ⟨τ,hr₂,hτC,hτH,hτm,hτn⟩:=
    RamCoordinateCapBounds.prepareCap_bounded_spec m n S w hdim hwcap (σ.setVar "cap.H" (2 ^ (2 * S)))
      ⟨by simpa using hσm,by simpa using hσn,by simp⟩
  obtain ⟨υ,hr₃,hυ⟩:=RamFeasibilityScaleBounds.prepareScales_bounded_spec m n S w hdim hw
    τ ⟨hτm,hτn,hτH,hτC⟩
  have hr:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨υ,hr.mono ?_,hυ, (hr₃.frame_var "cap.value" (by decide)).trans hτC,
    (hr.frame_var "query.bits" (by decide)).trans hσbits, ?_⟩
  · dsimp [instructionBound]
    omega
  · funext a
    exact hr.frame_arr a (by simp [prepareParameters,Com.warrs,prepareCap,prepareScales,
      RamNaturalPower.factorial,RamNaturalPower.factorialStep,RamNaturalPower.power,
      RamNaturalPower.powerStep,RamBitLength.bitLength,RamBitLength.bitLengthLoop,RamBitLength.bitLengthStep])

end Lax109476Proofs.RamFeasibilityParameters

end

section

namespace Lax109476Proofs.RamNormalizedBounds

open Lax109476.LinearProgram
open IntegerCertificates NormalizedFeasibility RationalArithmeticBounds

theorem factors_le_ball (m n H:ℕ):
    precisionDenominator m n H≤ ballDenominator m n H∧
      outerScale n (coordinateCap m n H)≤ ballDenominator m n H:=by
  have hD:=precisionDenominator_pos m n H
  have hR:=outerScale_pos n (coordinateCap m n H)
  have hN:0 < n * H + 1:=by omega
  unfold ballDenominator
  exact ⟨(Nat.le_mul_of_pos_right _ hN).trans (Nat.le_mul_of_pos_right _ hR),
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hD hN)⟩

end Lax109476Proofs.RamNormalizedBounds

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

namespace Lax109476Proofs.RamFeasibilitySetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding NormalizedFeasibility
open RamNormalizedBounds

theorem setup_spec (m n S w:ℕ) (P:Program ℤ m n) (hdim:m + n≤ S)
    (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S)) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (Input P S) setup
      (fun _ τ => RamSearchBounds.Input
        (normalizedMatrix P (outerScale n (IntegerCertificates.coordinateCap m n (2 ^ (2 * S)))))
        (normalizedBound P (1 / (precisionDenominator m n (2 ^ (2 * S)):ℚ)))
        (EllipsoidSequence.thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) τ)
      (instructionBound S):=by
  let H:=2 ^ (2 * S)
  let M:=2 ^ coefficientBits S
  let D:=precisionDenominator m n H
  let R:=outerScale n (IntegerCertificates.coordinateCap m n H)
  let N:=EllipsoidSequence.thresholdSteps n (ballExponent m n H) + 1
  have hwParams:RamFeasibilityScaleBounds.wordWidth S≤ w:=by unfold wordWidth at hw; omega
  have hwNormal:RamDecoder.wordWidth (coefficientBits S)≤ w:=by unfold wordWidth at hw; omega
  have hM:1≤ M:=Nat.one_le_pow _ _ (by decide)
  have hguard:=RamSolverFrontEnd.clearing_word_guard (coefficientBits S) w hwNormal
  have hHM:H≤ M:=Nat.pow_le_pow_right (by decide) (by unfold coefficientBits; omega)
  have hsize:=IterationBudget.ballExponent_polynomial m n S hdim
  have hball:ballDenominator m n H≤ M:=(Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) (by change ballExponent m n H≤ coefficientBits S; dsimp only [H]; unfold coefficientBits; omega))
  have hfactors:=factors_le_ball m n H
  have hR:R≤ M:=hfactors.2.trans hball
  have hD:0 < D:=precisionDenominator_pos _ _ _
  have hDM:D≤ M:=hfactors.1.trans hball
  have hn:n≤ S:=by omega
  have hprod:(m + n) * n≤ S * S:=Nat.mul_le_mul hdim hn
  have hwD:S * S + S + 1≤ w:=by unfold wordWidth at hw; nlinarith
  have hwidth:=(Nat.lt_two_pow_self (n:=S * S + S + 1)).trans_le
    (Nat.pow_le_pow_right (by decide) hwD)
  have hdims:(m + n) * n + m + n + 1 < 2 ^ w:=by omega
  rintro σ ⟨hσA,hσb,hσrows,hσrhs,hσcenter,hσshape,hσworkspace,hσnormal,hσm,hσn,hσbits⟩
  obtain ⟨τ,hr₁,hparams,hτC,hτbits,harr⟩:=
    RamFeasibilityParameters.prepareParameters_spec m n S w hdim hwParams σ ⟨hσm,hσn,hσbits⟩
  obtain ⟨hτD,hτR,hτE,hτN,hτm,hτn,hτH⟩:=hparams
  have hτinput:RamNormalizeQuery.Input P R D N τ:=by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,hτm,hτn,hτR,hτD,hτN⟩
    · simpa only [Represents,harr] using hσA
    · simpa only [Represents,harr] using hσb
    · simpa only [Extents,harr] using hσrows
    · simpa only [Extents,harr] using hσrhs
    · simpa only [Extents,harr] using hσcenter
    · simpa only [Extents,harr] using hσshape
    · exact RamAdvanceState.workspace_of_run hr₁ n hσworkspace
    · simpa only [Extents,harr] using hσnormal
  obtain ⟨υ,hr₂,hυ⟩:=RamNormalizeQuery.normalizeQuery_spec (2 ^ w) M m n R D N P
    hM hR hD hDM hdims hguard (fun i j => (hA i j).trans hHM) (fun i => (hb i).trans hHM) τ hτinput
  have hmulA:=Nat.mul_le_mul_left (72 * (coefficientBits S + 1) + 181) hprod
  have hmulb:=Nat.mul_le_mul_left (72 * (coefficientBits S + 1) + 189) hdim
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυ⟩
  simp only [instructionBound,M,Nat.size_pow]
  omega

end Lax109476Proofs.RamFeasibilitySetup

end

theorem solution:∀ (m n S w:Nat) (P:Lax109476.LinearProgram.Program Int m n),
  Nat.le (Nat.add m n) S→
    (∀ (i:Fin m) (j:Fin n),
        Nat.le (@Lax109476.LinearProgram.Program.A Int m n P i j).natAbs
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat))
            (Nat.mul ((2:Nat))
              S)))→
      (∀ (i:Fin m),
          Nat.le (@Lax109476.LinearProgram.Program.b Int m n P i).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat))
              (Nat.mul
                ((2:Nat)) S)))→
        Nat.le (Lax109476Proofs.RamFeasibilitySetup.wordWidth S) w→
          Lax808846Proofs.Reasoning.Spec
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            (@Lax109476Proofs.RamFeasibilitySetup.Input m n P S) Lax109476Proofs.RamFeasibilitySetup.setup
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              @Lax109476Proofs.RamSearchBounds.Input (Nat.add m n) n
                (@Lax109476Proofs.NormalizedFeasibility.normalizedMatrix m n P
                  (Lax109476Proofs.NormalizedFeasibility.outerScale n
                    (Lax109476Proofs.IntegerCertificates.coordinateCap m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat))
                        (Nat.mul
                          ((2:Nat)) S)))))
                (@Lax109476Proofs.NormalizedFeasibility.normalizedBound m n P
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                    (@Nat.cast Rat Rat.instNatCast
                      (Lax109476Proofs.NormalizedFeasibility.precisionDenominator m n
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          ((2:Nat))
                          (Nat.mul
                            ((2:Nat)) S))))))
                (Nat.add
                  (Lax109476Proofs.EllipsoidSequence.thresholdSteps n
                    (Lax109476Proofs.NormalizedFeasibility.ballExponent m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat))
                        (Nat.mul
                          ((2:Nat)) S))))
                  ((1:Nat)))
                τ)
            (Lax109476Proofs.RamFeasibilitySetup.instructionBound S):= @Lax109476Proofs.RamFeasibilitySetup.setup_spec
