-- Prove2me | solution 1 for Lax109476Proofs.RamEllipsoidStep.ellipsoidStep_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:57:45.673856+00:00
-- url     : https://prove2.me/submissions/320a5bdd-ec11-4f74-8254-74e108b1ed75

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
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamEllipsoidCoefficients_computeCoefficients_spec
import Theorems.Thm_Lax109476Proofs_RamCenterUpdate_updateCenter_ellipsoid_spec
import Theorems.Thm_Lax109476Proofs_RamShapeUpdate_updateShape_ellipsoid_spec
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamMatrixVector_ellipsoidMulVec_spec_native

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
namespace Lax109476Proofs.RamMatrixVector
end Lax109476Proofs.RamMatrixVector
theorem Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec:∀ (B n H:Nat) (A:Matrix (Fin n) (Fin n) Rat) (c:Fin n→ Rat),
  Nat.le ((1:Nat)) H→
    (∀ (k j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (A k j) H)→
      (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (c j) H)→
        Nat.lt
            (HAdd.hAdd
              (HAdd.hAdd (HAdd.hAdd n n)
                (HMul.hMul n n))
              ((1:Nat)))
            B→
          Nat.lt
              (HAdd.hAdd
                (HMul.hMul
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
              (HAdd.hAdd
                (HMul.hMul
                  (HAdd.hAdd
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HAdd.hAdd
                          ((4:Nat))
                          (HAdd.hAdd
                            (HMul.hMul
                              (HAdd.hAdd
                                (HAdd.hAdd
                                  (HMul.hMul
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
                ((8:Nat))):= @Lax109476Proofs.RamMatrixVector.ellipsoidMulVec_spec_native

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

def _root_.Lax808846Proofs.Imp.Com.NoWrite:Com→ Prop
  | .skip => True
  | .assign _ _ => True
  | .store _ _ _ => True
  | .read _ => True
  | .write _ => False
  | .seq c d => c.NoWrite∧ d.NoWrite
  | .ite _ c d => c.NoWrite∧ d.NoWrite
  | .while _ c => c.NoWrite

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

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_shiftl (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * 2 ^ n < B):
    (Expr.bin .shiftl e f).evalB B σ=some (m * 2 ^ n):=evalB_bin he hf h

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

theorem loadLeft_frame_spec (B:ℕ) (a:String) (qs:List ℚ) (i:ℕ) (hi:i < qs.length)
    (hB:1 < B) (hiB:i < B) (hn:qs[i].num.natAbs < B) (hd:qs[i].den < B):
    Spec B (fun σ => Represents a qs σ∧ σ.vars "vec.i"=i) (loadLeft a)
      (fun σ τ => LeftOutput qs[i] τ∧ τ.vars "vec.i"=i∧ τ.arrs=σ.arrs) 9:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=loadLeft_spec B a qs i hi hB hiB hn hd σ hσ
  refine ⟨τ,hr,hτ, (hr.frame_var "vec.i" (by simp [loadLeft,Com.wvars])).trans hσ.2, ?_⟩
  funext b
  exact hr.frame_arr b (by simp [loadLeft,Com.warrs])

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

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

open Lax808846.Ram

def runOut (w:ℕ):ℕ→ Program→ State→ ℕ→ Option (List ℕ × ℕ)
  | 0,p,s,k => if s.pc < p.length then none else some (s.out,k)
  | fuel + 1,p,s,k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out,k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out,k)

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

theorem Below.length (h:Below a x n F σ):(σ.arrs a).length=n:=by
  obtain ⟨_,hf⟩:=h; exact hf.length

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

def demo (a x m:String):Com:=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

def demoWatched (a x m:String):Com:=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

def layout:Lax808846Proofs.Compile.Layout:= ⟨["i", "m"], ["ar"],2⟩

def prog:Lax808846.Ram.Program:=
  Lax808846Proofs.Compile.compileProgram layout (demoWatched "ar" "i" "m")

def demoRun:Option (List ℕ × ℕ):=runOut 16 1000 prog (Lax808846.Ram.initState []) 0

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

theorem multiplyAt_spec (B M:ℕ) (a b:String) (xs ys:List ℚ) (i:ℕ)
    (hix:i < xs.length) (hiy:i < ys.length) (hiB:i < B)
    (hB:2 * M ^ 2 + 3 < B) (hx:Height xs[i] M) (hy:Height ys[i] M):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧ σ.vars "vec.i"=i)
      (multiplyAt a b) (fun _ τ => FractionOutput (xs[i] * ys[i]) τ)
      (72 * M.size + 82):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσx,hσy,hσi⟩
  obtain ⟨τ,hr₁,hτx,hτi,hτa⟩:=loadLeft_frame_spec B a xs i hix h1 hiB
    (hx.1.trans_lt hM) (hx.2.trans_lt hM) σ ⟨hσx,hσi⟩
  have hτy:Represents b ys τ:=by simpa only [Represents,hτa] using hσy
  obtain ⟨υ,hr₂,hυy,hυi,hυa,hυs,hυn,hυd⟩:=loadRight_frame_spec B b ys i hiy h1 hiB
    (hy.1.trans_lt hM) (hy.2.trans_lt hM) τ ⟨hτy,hτi⟩
  have hυx:LeftOutput xs[i] υ:=by simpa only [LeftOutput,hυs,hυn,hυd] using hτx
  obtain ⟨ρ,hr₃,hρ⟩:=multiplyFraction_uniform_spec B M
    (rationalSign xs[i]) xs[i].num.natAbs xs[i].den
    (rationalSign ys[i]) ys[i].num.natAbs ys[i].den hB
    (rationalSign_le_one _) (rationalSign_le_one _) hx.1 hx.2 hy.1 hy.2 xs[i].den_pos ys[i].den_pos
    υ ⟨hυx.1,hυx.2.1,hυx.2.2,hυy.1,hυy.2.1,hυy.2.2⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_⟩
  simpa only [canonical_fractionValue] using hρ

def loopFields:List String:= ["dot.s", "dot.n", "dot.d", "vec.i", "vec.n"]

theorem multiplyAt_frame_spec (B M:ℕ) (a b:String) (xs ys:List ℚ) (i:ℕ)
    (hix:i < xs.length) (hiy:i < ys.length) (hiB:i < B)
    (hB:2 * M ^ 2 + 3 < B) (hx:Height xs[i] M) (hy:Height ys[i] M):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧ σ.vars "vec.i"=i)
      (multiplyAt a b) (fun σ τ => FractionOutput (xs[i] * ys[i]) τ∧
        FieldsAgree loopFields σ τ∧ τ.arrs=σ.arrs) (72 * M.size + 82):=by
  apply spec_with_fields loopFields (multiplyAt_spec B M a b xs ys i hix hiy hiB hB hx hy)
  · intro x hx
    simp [loopFields] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals simp [multiplyAt,loadLeft,loadRight,multiplyFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars]
  · simp [multiplyAt,loadLeft,loadRight,multiplyFraction,RamArithmetic.normalizeFraction,
      RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs]

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

def LoopInvariant (a b:String) (xs ys:List ℚ) (n:ℕ) (σ:Env):Prop:=
  Represents a xs σ∧ Represents b ys σ∧ σ.vars "vec.i" ≤ n∧
    σ.vars "vec.n"=n∧ DotOutput (prefixValue xs ys (σ.vars "vec.i")) σ

theorem dotStep_spec (B n H:ℕ) (a b:String) (xs ys:List ℚ)
    (hx:xs.length=n) (hy:ys.length=n) (hH:1≤ H)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H)
    (hnB:n < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => LoopInvariant a b xs ys n σ∧ σ.vars "vec.i" < n)
      (dotStep a b)
      (fun σ τ => LoopInvariant a b xs ys n τ∧ τ.vars "vec.i"=σ.vars "vec.i" + 1)
      (144 * (cap n H).size + 210):=by
  rintro σ ⟨⟨hσx,hσy,hσin,hσn,hσq⟩,hσi⟩
  let i:=σ.vars "vec.i"
  have hix:i < xs.length:=by dsimp [i]; omega
  have hiy:i < ys.length:=by dsimp [i]; omega
  have hcap:=cap_ge n H hH
  have hxq:=hxs _ (List.getElem_mem hix)
  have hyq:=hys _ (List.getElem_mem hiy)
  have hprefix:=prefix_height xs ys n H i hH hx hy hσin hxs hys
  have hproduct:=height_mono _ (height_mul _ _ H H hxq hyq) hcap.1
  obtain ⟨τ,hr₁,hτp,hτf,hτa⟩:=multiplyAt_frame_spec B (cap n H) a b xs ys i hix hiy
    (hσi.trans hnB) hB (height_mono _ hxq hcap.2) (height_mono _ hyq hcap.2)
    σ ⟨hσx,hσy,rfl⟩
  have hτi:τ.vars "vec.i"=i:=hτf _ (by simp [loopFields])
  have hτn:τ.vars "vec.n"=σ.vars "vec.n" :=hτf _ (by simp [loopFields])
  have hτq:DotOutput (prefixValue xs ys i) τ:=by
    simpa only [DotOutput,hτf "dot.s" (by simp [loopFields]),
      hτf "dot.n" (by simp [loopFields]),hτf "dot.d" (by simp [loopFields])] using hσq
  obtain ⟨υ,hr₂,hυq,hυi,hυn,hυa⟩:=addToAccumulator_spec B (cap n H) i
    (prefixValue xs ys i) (xs[i] * ys[i]) hB hprefix hproduct
    (lt_of_le_of_lt (by dsimp [i]; omega) hnB) τ ⟨hτq,hτp,hτi⟩
  have hsum:prefixValue xs ys (i + 1)=prefixValue xs ys i + xs[i] * ys[i]:=by
    rw [prefix_succ]
    simp [List.getD_eq_getElem?_getD,hix,hiy]
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega), ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩,hυi⟩
  · simpa only [Represents,hυa,hτa] using hσx
  · simpa only [Represents,hυa,hτa] using hσy
  · rw [hυi]; dsimp [i]; omega
  · rw [hυn,hτn,hσn]
  · rw [hυi,hsum]; exact hυq

theorem dotProduct_spec (B n H:ℕ) (a b:String) (xs ys:List ℚ)
    (hx:xs.length=n) (hy:ys.length=n) (hH:1≤ H)
    (hxs:∀ q∈ xs,Height q H) (hys:∀ q∈ ys,Height q H)
    (hnB:n < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧ σ.vars "vec.n"=n)
      (dotProduct a b)
      (fun _ τ => DotOutput (prefixValue xs ys n) τ∧ Represents a xs τ∧
        Represents b ys τ∧ τ.vars "vec.i"=n∧ τ.vars "vec.n"=n)
      ((144 * (cap n H).size + 210 + 4) * n + 12):=by
  have hlo:=Spec.forRangeZero "vec.i" "vec.n" (LoopInvariant a b xs ys n) n
    (144 * (cap n H).size + 210) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (dotStep_spec B n H a b xs ys hx hy hH hxs hys hnB hB)
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσx,hσy,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "vec.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "vec.i") (Expr.var "vec.n")) (dotStep a b)); let c1:Env:=Env.setVar σ "dot.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "dot.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "dot.d" ((1:Nat)); let c4:Env→ Nat→ Prop:=Run B c0 c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat→ Nat:=c5 (c6 (c5 (c5 (c6 ((144:Nat)) (Nat.size (cap n H))) ((210:Nat))) ((4:Nat))) n); let c8:Nat:=c7 ((6:Nat)); let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' c8) (And (LoopInvariant a b xs ys n σ') (@Eq Nat (Env.vars σ' "vec.i") n)); let c10:Nat:=c7 ((12:Nat)); let c11:Env→ Prop:=(fun (x τ:Env) => And (DotOutput (prefixValue xs ys n) τ) (And (Represents a xs τ) (And (Represents b ys τ) (And (@Eq Nat (Env.vars τ "vec.i") n) (@Eq Nat (Env.vars τ "vec.n") n))))) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B (dotProduct a b) σ σ' c10) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Nat→ Nat:=c5 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat→ Nat:=c5 c15; let c17:Nat:=c14 (Expr.size (Expr.lit ((1:Nat)))); let c18:Nat:=c5 c17 c8; let c19:Nat:=c16 c18; let c20:Com:=Com.assign "dot.n" (Expr.lit ((0:Nat))); let c21:Com:=Com.assign "dot.d" (Expr.lit ((1:Nat))); let c22:Com:=Com.seq c21 c0; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c13) (RunStep.use B (fun (σ_1:Env) => LoopInvariant a b xs ys n (Env.setVar σ_1 "vec.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (LoopInvariant a b xs ys n σ') (@Eq Nat (Env.vars σ' "vec.i") n)) c8 hlo c3 ?_) fun (w:Env) (h:And (c4 w c8) (And (LoopInvariant a b xs ys n w) (@Eq Nat (Env.vars w "vec.i") n))) => let c0_1:Prop:=And (LoopInvariant a b xs ys n w) (@Eq Nat (Env.vars w "vec.i") n); @And.casesOn (c4 w c8) c0_1 (fun (x:And (c4 w c8) c0_1) => c13) h fun (left:c4 w c8) (right:c0_1) => @Exists.intro Env c12 w (@And.intro (Run B (dotProduct a b) σ w c10) (c11 w) (RunStep.mono B (dotProduct a b) σ w (c16 c19) c10 (RunStep.seq B (Com.assign "dot.s" (Expr.lit ((0:Nat)))) (Com.seq c20 c22) σ c1 w c15 c19 (RunStep.assign B σ "dot.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4181_0_0_0))) (RunStep.seq B c20 c22 c1 c2 w c15 c18 (RunStep.assign B c1 "dot.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g4181_0_0_1))) (RunStep.seq B c21 c0 c2 c3 w c17 c8 (RunStep.assign B c2 "dot.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) left))) (?nAX_g4181_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4181_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4181_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4181_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [LoopInvariant,DotOutput,Represents,prefix_zero,fractionValue]
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

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamDotProduct RamMatrixRows RationalArithmeticBounds

theorem ellipsoidMulVecInitialized_spec (B n H:ℕ)
    (A:Matrix (Fin n) (Fin n) ℚ) (c:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (hc:∀ j,Height (c j) H)
    (hdims:n + n + n * n + 1 < B) (hB:2 * (cap n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows "ell.shape" A σ∧ Represents "ell.normal" (List.ofFn c) σ∧
        (σ.arrs "ell.u.s").length=n∧ (σ.arrs "ell.u.n").length=n∧
        (σ.arrs "ell.u.d").length=n∧ σ.vars "vec.n"=n)
      ellipsoidMulVecInitialized
      (fun _ τ => Represents "ell.u" (List.ofFn (A *ᵥ c)) τ∧ MatrixRows "ell.shape" A τ∧
        Represents "ell.normal" (List.ofFn c) τ∧ τ.vars "vec.n"=n)
      (33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8)):=by
  have hnB:n < B:=by omega
  have h1:1 < B:=by nlinarith
  rintro σ ⟨hσA,hσc,hσus,hσun,hσud,hσn⟩
  obtain ⟨τ,hr₁,hτu,hτn,hτa⟩:=RamZeroArray.zeroRationalArray_spec B n "ell.u" hnB h1
    σ ⟨hσus,hσun,hσud,hσn⟩
  have hτA:MatrixRows "ell.shape" A τ:=by
    simpa only [MatrixRows,Slice,hτa ("ell.shape" ++ ".s") (by decide),
      hτa ("ell.shape" ++ ".n") (by decide),hτa ("ell.shape" ++ ".d") (by decide)] using hσA
  have hτc:Represents "ell.normal" (List.ofFn c) τ:=by
    simpa only [Represents,hτa ("ell.normal" ++ ".s") (by decide),
      hτa ("ell.normal" ++ ".n") (by decide),hτa ("ell.normal" ++ ".d") (by decide)] using hσc
  obtain ⟨υ,hr₂,hυ⟩:=ellipsoidMulVec_spec B n H A c hH hA hc hdims hB τ ⟨hτA,hτc,hτu,hτn⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

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

theorem saveForm_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (DotOutput q) saveForm (fun σ τ => FormOutput q τ∧ τ.arrs=σ.arrs) 6:=by
  rintro σ ⟨hσq,hσn,hσd,hσs⟩
  have hsB:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (σ_1 τ:Env) => And (FormOutput q τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1))) σ; let c1:Nat:=Env.vars (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) "dot.n"; let c2:Env:=Env.setVar (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) "ell.form.n" c1; let c3:Nat:=Env.vars c2 "dot.d"; let c4:Env:=Env.setVar c2 "ell.form.d" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "dot.s")); let c8:Nat:=c6 (Expr.size (Expr.var "dot.n")); let c9:Nat:=c6 (Expr.size (Expr.var "dot.d")); let c10:Nat:=c5 c8 c9; @Exists.intro Env (fun (σ':Env) => And (Run B saveForm σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B saveForm σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B saveForm σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "ell.form.s" (Expr.var "dot.s")) (Com.seq (Com.assign "ell.form.n" (Expr.var "dot.n")) (Com.assign "ell.form.d" (Expr.var "dot.d"))) σ (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) c4 c7 c10 (RunStep.assign B σ "ell.form.s" (Expr.var "dot.s") (Env.vars σ "dot.s") (RunStep.eval_var B σ "dot.s" hsB)) (RunStep.seq B (Com.assign "ell.form.n" (Expr.var "dot.n")) (Com.assign "ell.form.d" (Expr.var "dot.d")) (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) "ell.form.n" (Expr.var "dot.n") c1 (RunStep.eval_var B (Env.setVar σ "ell.form.s" (Env.vars σ "dot.s")) "dot.n" (?nAX_g4269_0_0_0))) (RunStep.assign B c2 "ell.form.d" (Expr.var "dot.d") c3 (RunStep.eval_var B c2 "dot.d" (?nAX_g4269_0_0_1))))) (?nAX_g4269_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4269_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4269_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4269_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FormOutput]

theorem formHeight_ge (n H:ℕ) (hH:1≤ H):cap n H≤ formHeight n H:=by
  have hcap:=(cap_ge n H hH).2
  exact (cap_ge n (cap n H) (hH.trans hcap)).2

theorem ellipsoidForm_spec (B n H:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a:Fin n→ ℚ)
    (hH:1≤ H) (hA:∀ k j,Height (A k j) H) (ha:∀ j,Height (a j) H)
    (hdims:n + n + n * n + 1 < B) (hB:2 * (formHeight n H) ^ 2 + 3 < B):
    Spec B (fun σ => MatrixRows "ell.shape" A σ∧ Represents "ell.normal" (List.ofFn a) σ∧
        (σ.arrs "ell.u.s").length=n∧ (σ.arrs "ell.u.n").length=n∧
        (σ.arrs "ell.u.d").length=n∧ σ.vars "vec.n"=n)
      ellipsoidForm
      (fun _ τ => FormOutput (a ⬝ᵥ (A *ᵥ a)) τ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ∧ MatrixRows "ell.shape" A τ∧
        Represents "ell.normal" (List.ofFn a) τ∧ τ.vars "vec.n"=n)
      (33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
        (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)):=by
  have hcap:=(cap_ge n H hH).2
  have hform:=formHeight_ge n H hH
  have hcapB:cap n H < B:=by nlinarith
  have hfB:formHeight n H < B:=by nlinarith
  have hB₁:2 * (cap n H) ^ 2 + 3 < B:=by nlinarith
  have hnB:n < B:=by omega
  have h1:1 < B:=by nlinarith
  rintro σ hσ
  obtain ⟨τ,hr₁,hτu,hτA,hτa,hτn⟩:=ellipsoidMulVecInitialized_spec B n H A a hH hA ha
    hdims hB₁ σ hσ
  have hn:(List.ofFn a).length=n:=by simp
  have hu:(List.ofFn (A *ᵥ a)).length=n:=by simp
  have han:∀ q∈ List.ofFn a,Height q (cap n H):=by
    intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq
    exact height_mono _ (ha j) hcap
  have hun:∀ q∈ List.ofFn (A *ᵥ a),Height q (cap n H):=by
    intro q hq; simp only [List.mem_ofFn] at hq; obtain ⟨j,rfl⟩:=hq
    exact mulVec_height n H A a hH hA ha j
  obtain ⟨υ,hr₂,hυq,_,_,_,_⟩:=dotProduct_spec B n (cap n H) "ell.normal" "ell.u"
    (List.ofFn a) (List.ofFn (A *ᵥ a)) hn hu (hH.trans hcap) han hun hnB hB
    τ ⟨hτa,hτu,hτn⟩
  have hformq:Height (a ⬝ᵥ (A *ᵥ a)) (formHeight n H):=by
    change Height (∑ j,a j * (A *ᵥ a) j) (formHeight n H)
    rw [← prefix_ofFn]
    exact prefix_height _ _ n (cap n H) n (hH.trans hcap) hn hu le_rfl han hun
  have hυform:DotOutput (a ⬝ᵥ (A *ᵥ a)) υ:=by
    simpa only [prefix_ofFn,_root_.dotProduct] using hυq
  obtain ⟨ρ,hr₃,hρ,_⟩:=saveForm_spec B (a ⬝ᵥ (A *ᵥ a)) h1
    (hformq.1.trans_lt hfB) (hformq.2.trans_lt hfB) υ hυform
  have hυarr:υ.arrs=τ.arrs:=by
    funext b
    exact hr₂.frame_arr b (by
      simp [RamDotProduct.dotProduct,dotStep,multiplyAt,loadLeft,loadRight,addToAccumulator,
        multiplyFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])
  have hρarr:ρ.arrs=υ.arrs:=by
    funext b
    exact hr₃.frame_arr b (by simp [saveForm,Com.warrs])
  have hυn:υ.vars "vec.n"=n:=
    (hr₂.frame_var "vec.n" (by
      simp [RamDotProduct.dotProduct,dotStep,multiplyAt,loadLeft,loadRight,addToAccumulator,
        multiplyFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
        RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])).trans hτn
  have hρn:ρ.vars "vec.n"=n:=(hr₃.frame_var "vec.n" (by simp [saveForm,Com.wvars])).trans hυn
  refine ⟨ρ,hr₁.seq (hr₂.seq hr₃),hρ, ?_, ?_, ?_,hρn⟩
  · simpa only [Represents,hρarr,hυarr] using hτu
  · simpa only [MatrixRows,Slice,hρarr,hυarr] using hτA
  · simpa only [Represents,hρarr,hυarr] using hτa

end Lax109476Proofs.RamEllipsoidForm

end

section

namespace Lax109476Proofs.RamEllipsoidScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamEllipsoidForm RationalSizeBounds RationalArithmeticBounds
open RamRounding RamPrimitiveBounds RamFrame

theorem epsilonDenominator_spec (B n:ℕ) (hB:2 ^ (2 * n + 4) < B):
    Spec B (fun σ => σ.vars "vec.n"=n) epsilonDenominator
      (fun _ τ => τ.vars "ell.epsden"=2 ^ (2 * n + 4)) 8:=by
  have hexp:=Nat.lt_two_pow_self (n:=2 * n + 4)
  have hn:n < B:=by omega
  have htwo:2 < B:=by omega
  have hfour:4 < B:=by omega
  have h1:1 < B:=by omega
  intro σ hσ
  (expose_names;
    (refine let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat→ Nat:=c2 ((2:Nat)); let c4:Nat:=c0 (c1 (c3 n) ((4:Nat))); let c5:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "ell.epsden") c4) σ; let c6:Nat:=c3 (Env.vars σ "vec.n"); let c7:Nat:=c1 c6 ((4:Nat)); let c8:Nat:=c2 ((1:Nat)) (c0 c7); let c9:Env:=Env.setVar σ "ell.epsden" c8; let c10:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "vec.n"); let c11:Expr:=Expr.add c10 (Expr.lit ((4:Nat))); let c12:Expr:=Expr.shiftl (Expr.lit ((1:Nat))) c11; @Exists.intro Env (fun (σ':Env) => And (Run B epsilonDenominator σ σ' ((8:Nat))) (c5 σ')) c9 (@And.intro (Run B epsilonDenominator σ c9 ((8:Nat))) (c5 c9) (RunStep.mono B epsilonDenominator σ c9 (c1 ((1:Nat)) (Expr.size c12)) ((8:Nat)) (RunStep.assign B σ "ell.epsden" c12 c8 (RunStep.eval_shiftl B σ (Expr.lit ((1:Nat))) c11 ((1:Nat)) c7 (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_add B σ c10 (Expr.lit ((4:Nat))) c6 ((4:Nat)) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "vec.n") ((2:Nat)) (Env.vars σ "vec.n") (RunStep.eval_lit B ((2:Nat)) σ htwo) (RunStep.eval_var B σ "vec.n" (?nAX_g4280_0_0_0)) (?nAX_g4280_0_0_1)) (RunStep.eval_lit B ((4:Nat)) σ hfour) (?nAX_g4280_0_0_2)) ?_)) (?nAX_g4280_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4280_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4280_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4280_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4280_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem precisionGrid_value (k n:ℕ):
    EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n=2 ^ (2 * k + 3 * n + 9):=by
  unfold EllipsoidPrecision.gridDenominator
  congr 1
  omega

theorem precisionGrid_spec (B k n:ℕ) (hB:2 ^ (2 * k + 3 * n + 9) < B):
    Spec B (fun σ => σ.vars "iter.k"=k∧ σ.vars "vec.n"=n) precisionGrid
      (fun _ τ => τ.vars "grid.D" =
        EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n) 12:=by
  have hexp:=Nat.lt_two_pow_self (n:=2 * k + 3 * n + 9)
  have hn:n < B:=by omega
  have hk:k < B:=by omega
  have htwo:2 < B:=by omega
  have hthree:3 < B:=by omega
  have hnine:9 < B:=by omega
  have h1:1 < B:=by omega
  have hval:=precisionGrid_value k n
  rintro σ ⟨hσk,hσn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((2:Nat)); let c3:Nat:=EllipsoidPrecision.gridDenominator (c0 (c2 k) ((2:Nat))) (c0 (c2 n) ((4:Nat))) n; let c4:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "grid.D") c3) σ; let c5:Nat:=c2 (Env.vars σ "iter.k"); let c6:Nat:=c1 ((3:Nat)) (Env.vars σ "vec.n"); let c7:Nat:=c0 c5 c6; let c8:Nat:=c0 c7 ((9:Nat)); let c9:Nat:=c1 ((1:Nat)) (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)) c8); let c10:Env:=Env.setVar σ "grid.D" c9; let c11:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "iter.k"); let c12:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "vec.n"); let c13:Expr:=Expr.add c11 c12; let c14:Expr:=Expr.add c13 (Expr.lit ((9:Nat))); let c15:Expr:=Expr.shiftl (Expr.lit ((1:Nat))) c14; @Exists.intro Env (fun (σ':Env) => And (Run B precisionGrid σ σ' ((12:Nat))) (c4 σ')) c10 (@And.intro (Run B precisionGrid σ c10 ((12:Nat))) (c4 c10) (RunStep.mono B precisionGrid σ c10 (c0 ((1:Nat)) (Expr.size c15)) ((12:Nat)) (RunStep.assign B σ "grid.D" c15 c9 (RunStep.eval_shiftl B σ (Expr.lit ((1:Nat))) c14 ((1:Nat)) c8 (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_add B σ c13 (Expr.lit ((9:Nat))) c7 ((9:Nat)) (RunStep.eval_add B σ c11 c12 c5 c6 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var "iter.k") ((2:Nat)) (Env.vars σ "iter.k") (RunStep.eval_lit B ((2:Nat)) σ htwo) (RunStep.eval_var B σ "iter.k" (?nAX_g4286_0_0_0)) (?nAX_g4286_0_0_1)) (RunStep.eval_mul B σ (Expr.lit ((3:Nat))) (Expr.var "vec.n") ((3:Nat)) (Env.vars σ "vec.n") (RunStep.eval_lit B ((3:Nat)) σ hthree) (RunStep.eval_var B σ "vec.n" (?nAX_g4286_0_0_2)) (?nAX_g4286_0_0_3)) (?nAX_g4286_0_0_4)) (RunStep.eval_lit B ((9:Nat)) σ hnine) (?nAX_g4286_0_0_5)) ?_)) (?nAX_g4286_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4286_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4286_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

end Lax109476Proofs.RamEllipsoidScalars

end

section

namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds

def scalarFields:List String:=
  ["vec.n", "grid.D", "ell.form.s", "ell.form.n", "ell.form.d", "ell.epsden"]

theorem scalarInput_frame (n:ℕ) (q:ℚ) (D E:ℕ) (σ τ:Env)
    (hσ:ScalarInput n q D E σ) (hf:FieldsAgree scalarFields σ τ):ScalarInput n q D E τ:=by
  simpa only [ScalarInput,FormOutput,hf "vec.n" (by simp [scalarFields]),
    hf "grid.D" (by simp [scalarFields]),hf "ell.epsden" (by simp [scalarFields]),
    hf "ell.form.s" (by simp [scalarFields]),hf "ell.form.n" (by simp [scalarFields]),
    hf "ell.form.d" (by simp [scalarFields])] using hσ

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

theorem computeCoefficients_bounded_spec (B n M D E:ℕ) (q:ℚ) (hn:2≤ n)
    (hqpos:0 < q) (hq:Height q M) (hnM:n≤ M) (hDM:D≤ M) (hEM:E≤ M)
    (hDpos:0 < D) (hEpos:0 < E) (hnnB:n ^ 2 < B) (hInflB:(E + 1) ^ 2 < B)
    (hPrimB:2 * M ^ 2 + 3 < B)
    (hRootB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB:coefficientCap M < B):
    Spec B (fun σ => ScalarInput n q D E σ∧ Represents "ell.coeff" (List.replicate 5 0) σ)
      computeCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ∧ ScalarInput n q D E τ)
      (582 * M.size + 687):=
  computeCoefficients_spec B n M (coefficientCap M) D E q hn hqpos hq hnM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hCB (coefficients_height n M D E q hq hnM hDM hEM hDpos)

theorem initializeCoefficients_spec (B n:ℕ) (hnB:n < B) (h5B:5 < B):
    Spec B (fun σ => (σ.arrs "ell.coeff.s").length=5∧ (σ.arrs "ell.coeff.n").length=5∧
        (σ.arrs "ell.coeff.d").length=5∧ σ.vars "vec.n"=n)
      initializeCoefficients
      (fun σ τ => Represents "ell.coeff" (List.replicate 5 0) τ∧ FieldsAgree scalarFields σ τ∧
        ∀ a∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"],τ.arrs a=σ.arrs a) 189:=by
  have hzero:=spec_with_write_frame ("coeff.savedn" ::scalarFields)
    (RamZeroArray.zeroRationalArray_spec B 5 "ell.coeff" h5B (by omega))
    (by
      intro x hx
      simp [scalarFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])
  rintro σ ⟨hσs,hσnum,hσd,hσn⟩
  (expose_names;
    (refine let c0:Env:=Env.setVar (Env.setVar σ "coeff.savedn" (Env.vars σ "vec.n")) "vec.n" ((5:Nat)); let c1:Env→ Nat→ Prop:=Run B (RamZeroArray.zeroRationalArray "ell.coeff") c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 (Nat.mul ((33:Nat)) ((5:Nat))) ((18:Nat)); let c4:Env→ Prop:=Represents "ell.coeff" (@List.replicate Rat ((5:Nat)) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "ell.coeff"; let c6:String:=c5 ".s"; let c7:String:=c5 ".n"; let c8:String:=c5 ".d"; let c9:String→ List Nat:=Env.arrs c0; let c10:Env→ Prop:=FieldsAgree (@List.cons String "coeff.savedn" scalarFields) c0; let c11:Env→ Prop:=fun (σ':Env) => And (c1 σ' c3) (And (And (c4 σ') (And (@Eq Nat (Env.vars σ' "vec.n") ((5:Nat))) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c9 b)))) (And (c10 σ') (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "ell.coeff"), @Eq (List Nat) (Env.arrs σ' a) (c9 a)))); let c12:Env→ Prop:=(fun (σ_1 τ:Env) => And (c4 τ) (And (FieldsAgree scalarFields σ_1 τ) (∀ a∉ @List.cons String "ell.coeff.s" (@List.cons String "ell.coeff.n" (@List.cons String "ell.coeff.d" (@List.nil String))), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B initializeCoefficients σ σ' ((189:Nat))) (c12 σ'); let c14:Prop:= @Exists Env c13; let c15:Nat→ Nat:=c2 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.var "vec.n")); let c17:Nat:=c15 (Expr.size (Expr.lit ((5:Nat)))); let c18:Nat:=c15 (Expr.size (Expr.var "coeff.savedn")); let c19:Nat:=c2 c3 c18; let c20:Nat:=c2 c17 c19; let c21:Com:=Com.assign "vec.n" (Expr.lit ((5:Nat))); let c22:Com:=Com.seq (RamZeroArray.zeroRationalArray "ell.coeff") (Com.assign "vec.n" (Expr.var "coeff.savedn")); @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => c14) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c6)) ((5:Nat))) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c7)) ((5:Nat))) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c8)) ((5:Nat))) (@Eq Nat (Env.vars σ_1 "vec.n") ((5:Nat)))))) (RamZeroArray.zeroRationalArray "ell.coeff") (fun (σ_1 τ:Env) => And (And (c4 τ) (And (@Eq Nat (Env.vars τ "vec.n") ((5:Nat))) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (FieldsAgree (@List.cons String "coeff.savedn" scalarFields) σ_1 τ) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "ell.coeff"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c3 hzero c0 ?_) fun (w:Env) (h:And (c1 w c3) (And (And (c4 w) (And (@Eq Nat (Env.vars w "vec.n") ((5:Nat))) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c9 b)))) (And (c10 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "ell.coeff"), @Eq (List Nat) (Env.arrs w a) (c9 a))))) => let c0_1:Prop:=And (And (c4 w) (And (@Eq Nat (Env.vars w "vec.n") ((5:Nat))) (∀ b∉ @List.cons String c6 (@List.cons String c7 (@List.cons String c8 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c9 b)))) (And (c10 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "ell.coeff"), @Eq (List Nat) (Env.arrs w a) (c9 a))); @And.casesOn (c1 w c3) c0_1 (fun (x:And (c1 w c3) c0_1) => c14) h fun (left:c1 w c3) (right:c0_1) => @Exists.intro Env c13 (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) (@And.intro (Run B initializeCoefficients σ (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) ((189:Nat))) (c12 (Env.setVar w "vec.n" (Env.vars w "coeff.savedn"))) (RunStep.mono B initializeCoefficients σ (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) (c2 c16 c20) ((189:Nat)) (RunStep.seq B (Com.assign "coeff.savedn" (Expr.var "vec.n")) (Com.seq c21 c22) σ (Env.setVar σ "coeff.savedn" (Env.vars σ "vec.n")) (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) c16 c20 (RunStep.assign B σ "coeff.savedn" (Expr.var "vec.n") (Env.vars σ "vec.n") (RunStep.eval_var B σ "vec.n" (?nAX_g4316_0_0_0))) (RunStep.seq B c21 c22 (Env.setVar σ "coeff.savedn" (Env.vars σ "vec.n")) c0 (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) c17 c19 (RunStep.assign B (Env.setVar σ "coeff.savedn" (Env.vars σ "vec.n")) "vec.n" (Expr.lit ((5:Nat))) ((5:Nat)) (RunStep.eval_lit B ((5:Nat)) (Env.setVar σ "coeff.savedn" (Env.vars σ "vec.n")) h5B)) (RunStep.seq B (RamZeroArray.zeroRationalArray "ell.coeff") (Com.assign "vec.n" (Expr.var "coeff.savedn")) c0 w (Env.setVar w "vec.n" (Env.vars w "coeff.savedn")) c3 c18 left (RunStep.assign B w "vec.n" (Expr.var "coeff.savedn") (Env.vars w "coeff.savedn") (RunStep.eval_var B w "coeff.savedn" ?_))))) (?nAX_g4316_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4316_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4316_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hzero
  all_goals simp_all [Represents,FieldsAgree,scalarFields]

theorem prepareCoefficients_spec (B n M D E:ℕ) (q:ℚ) (hn:2≤ n)
    (hqpos:0 < q) (hq:Height q M) (hnM:n≤ M) (hDM:D≤ M) (hEM:E≤ M)
    (hDpos:0 < D) (hEpos:0 < E) (hnnB:n ^ 2 < B) (hInflB:(E + 1) ^ 2 < B)
    (hPrimB:2 * M ^ 2 + 3 < B)
    (hRootB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB:coefficientCap M < B) (h5B:5 < B):
    Spec B (fun σ => ScalarInput n q D E σ∧ (σ.arrs "ell.coeff.s").length=5∧
        (σ.arrs "ell.coeff.n").length=5∧ (σ.arrs "ell.coeff.d").length=5)
      prepareCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ∧ ScalarInput n q D E τ)
      (582 * M.size + 876):=by
  have hMB:M < B:=by nlinarith only [hPrimB]
  rintro σ ⟨hσinput,hσs,hσnum,hσd⟩
  obtain ⟨τ,hr₁,hτg,hf,_⟩:=initializeCoefficients_spec B n (hnM.trans_lt hMB) h5B
    σ ⟨hσs,hσnum,hσd,hσinput.2.1⟩
  have hτinput:=scalarInput_frame n q D E σ τ hσinput hf
  obtain ⟨υ,hr₂,hυ⟩:=computeCoefficients_bounded_spec B n M D E q hn hqpos hq hnM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hCB τ ⟨hτinput,hτg⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by omega),hυ⟩

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

theorem center_no_other_writes (a:String)
    (ha:a∉ ["ell.nextcenter.s", "ell.nextcenter.n", "ell.nextcenter.d"]):a∉ updateCenter.warrs:=by
  simp at ha
  simp [updateCenter,centerLoop,centerStep,centerCoordinate,RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,loadLeft,loadRight,storeReduced,multiplyFraction,
    RamFractionInterface.subtractFraction,RamFractionInterface.negateRight,
    RamFractionInterface.resultToRight,RamFractionInterface.resultToLeft,
    RamRounding.roundFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs,ha.1,ha.2.1,ha.2.2]

theorem shape_no_other_writes (a:String)
    (ha:a∉ ["ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"]):a∉ updateShape.warrs:=by
  simp at ha
  simp [updateShape,initializeShape,shapeLoop,shapeStep,shapeCoordinate,entryIndex,entryProduct,
    shapeDifference,roundedEntry,inflatedEntry,addDiagonal,RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,loadLeft,loadRight,storeReduced,multiplyFraction,
    RamFractionInterface.subtractFraction,RamFractionInterface.negateRight,
    RamFractionInterface.resultToRight,RamFractionInterface.resultToLeft,
    RamRounding.roundFraction,addFraction,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs,ha.1,ha.2.1,ha.2.2]

theorem roundedUpdate_ellipsoid_spec (B n M D E:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (gs:List ℚ) (hg:4 < gs.length) (hM:1≤ M) (hnM:n * n≤ M)
    (hu:∀ j,Height ((A *ᵥ a) j) M) (hc:∀ j,Height (c j) M) (hA:∀ i j,Height (A i j) M)
    (hα:Height gs[0] M) (hβ:Height gs[1] M) (hγ:Height gs[2] M)
    (hρ:Height gs[3] M) (hδ:Height gs[4] M)
    (hD:D≤ M) (hDpos:0 < D) (hnB:n * n < B) (hnB':n < B)
    (hCenterB:2 * (centerCap M) ^ 2 + 3 < B) (hShapeB:2 * (shapeCap M) ^ 2 + 3 < B)
    (hgs:gs=coefficients n (a ⬝ᵥ (A *ᵥ a)) D E):
    Spec B (fun σ => Represents "ell.u" (List.ofFn (A *ᵥ a)) σ∧ Represents "ell.center" (List.ofFn c) σ∧
        Represents "ell.shape" (flatten A) σ∧ Represents "ell.coeff" gs σ∧
        (σ.arrs "ell.nextcenter.s").length=n∧ (σ.arrs "ell.nextcenter.n").length=n∧
        (σ.arrs "ell.nextcenter.d").length=n∧ (σ.arrs "ell.nextshape.s").length=n * n∧
        (σ.arrs "ell.nextshape.n").length=n * n∧ (σ.arrs "ell.nextshape.d").length=n * n∧
        σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      roundedUpdate
      (fun _ τ => Represents "ell.nextcenter" (List.ofFn (EllipsoidCenter.roundedCenter n A a c D)) τ∧
        Represents "ell.nextshape" (flatten (EllipsoidCenter.roundedStepShape n A a D (1 / (E:ℚ)))) τ∧
        Represents "ell.u" (List.ofFn (A *ᵥ a)) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        Represents "ell.shape" (flatten A) τ∧ Represents "ell.coeff" gs τ∧
        τ.vars "vec.n"=n∧ τ.vars "grid.D"=D)
      ((33 * n + 18 + ((180 * (centerCap M).size + 318 + 4 + 4) * n + 6)) +
        (33 * (n * n) + 26 + ((468 * (shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))):=by
  rintro σ ⟨hσu,hσc,hσA,hσg,hσcs,hσcn,hσcd,hσAs,hσAn,hσAd,hσn,hσD⟩
  obtain ⟨τ,hr₁,hτnextc,hτu,hτc,hτg,hτn,hτD⟩:=
    Lax109476Proofs.RamCenterUpdate.updateCenter_ellipsoid_spec B n M D A a c gs
      (by omega) hM hu hc hγ (by simp [hgs,coefficients]) hD hDpos hnB' hCenterB
      σ ⟨hσu,hσc,hσg,hσcs,hσcn,hσcd,hσn,hσD⟩
  have hτA:Represents "ell.shape" (flatten A) τ:=represents_frame hr₁ "ell.shape" _ hσA
    (center_no_other_writes _ (by simp)) (center_no_other_writes _ (by simp)) (center_no_other_writes _ (by simp))
  have hτAs:(τ.arrs "ell.nextshape.s").length=n * n:=by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAs
  have hτAn:(τ.arrs "ell.nextshape.n").length=n * n:=by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAn
  have hτAd:(τ.arrs "ell.nextshape.d").length=n * n:=by
    rw [hr₁.frame_arr _ (center_no_other_writes _ (by simp))]; exact hσAd
  obtain ⟨υ,hr₂,hυnextA,hυu,hυA,hυg,hυn,hυD⟩:=
    Lax109476Proofs.RamShapeUpdate.updateShape_ellipsoid_spec B n M D A a gs hg (1 / (E:ℚ))
      hM hnM hu hA hα hβ hρ hδ hD hDpos hnB hnB' hShapeB
      (by simp [hgs,coefficients]) (by simp [hgs,coefficients])
      (by simp [hgs,coefficients]) (by simp [hgs,coefficients])
      τ ⟨hτu,hτA,hτg,hτAs,hτAn,hτAd,hτn,hτD⟩
  have hυnextc:=represents_frame hr₂ "ell.nextcenter" _ hτnextc
    (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp))
  have hυc:=represents_frame hr₂ "ell.center" _ hτc
    (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp)) (shape_no_other_writes _ (by simp))
  exact ⟨υ,hr₁.seq hr₂,hυnextc,hυnextA,hυu,hυc,hυA,hυg,hυn,hυD⟩

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

namespace Lax109476Proofs.RamEllipsoidPrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEllipsoidScalars RamFrame

theorem preparePrecision_spec (B k n:ℕ)
    (hE:2 ^ (2 * n + 4) < B) (hD:2 ^ (2 * k + 3 * n + 9) < B):
    Spec B (fun σ => σ.vars "vec.n"=n∧ σ.vars "iter.k"=k) preparePrecision
      (fun σ τ => τ.vars "ell.epsden"=2 ^ (2 * n + 4)∧
        τ.vars "grid.D"=2 ^ (2 * k + 3 * n + 9)∧ τ.vars "vec.n"=n∧
        τ.vars "iter.k"=k∧ τ.arrs=σ.arrs) 20:=by
  have heps:=spec_with_fields ["vec.n", "iter.k"] (epsilonDenominator_spec B n hE)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [epsilonDenominator,Com.wvars])
    (by simp [epsilonDenominator,Com.warrs])
  have hgrid:=spec_with_fields ["vec.n", "iter.k", "ell.epsden"] (precisionGrid_spec B k n hD)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> simp [precisionGrid,Com.wvars])
    (by simp [precisionGrid,Com.warrs])
  rintro σ ⟨hσn,hσk⟩
  (expose_names;
    (refine let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) ((2:Nat)); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat→ Nat:=c2 ((2:Nat)); let c4:Nat:=c1 (c3 n) ((4:Nat)); let c5:Nat:=c0 c4; let c6:Env→ Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.cons String "iter.k" (@List.nil String))); let c7:Env→ Prop:=c6 σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B epsilonDenominator σ σ' ((8:Nat))) (And (@Eq Nat (Env.vars σ' "ell.epsden") c5) (And (c7 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c9:Nat→ Nat:=c1 (c3 k); let c10:Nat:=c0 (c1 (c9 (c2 ((3:Nat)) n)) ((9:Nat))); let c11:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "ell.epsden") c5) (And (@Eq Nat (Env.vars τ "grid.D") c10) (And (@Eq Nat (Env.vars τ "vec.n") n) (And (@Eq Nat (Env.vars τ "iter.k") k) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))))) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B preparePrecision σ σ' ((20:Nat))) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Nat:=EllipsoidPrecision.gridDenominator (c9 ((2:Nat))) c4 n; let c15:Env→ Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.cons String "iter.k" (@List.cons String "ell.epsden" (@List.nil String)))); @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c13) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "vec.n") n) epsilonDenominator (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "ell.epsden") c5) (And (c6 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((8:Nat)) heps σ ?_) fun (w:Env) (h:And (Run B epsilonDenominator σ w ((8:Nat))) (And (@Eq Nat (Env.vars w "ell.epsden") c5) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=Run B epsilonDenominator σ w ((8:Nat)); let c1_1:Prop:=And (@Eq Nat (Env.vars w "ell.epsden") c5) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B precisionGrid w σ' ((12:Nat))) (And (@Eq Nat (Env.vars σ' "grid.D") c14) (And (c15 w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c13) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "iter.k") k) (@Eq Nat (Env.vars σ_1 "vec.n") n)) precisionGrid (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "grid.D") c14) (And (c15 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((12:Nat)) hgrid w ?_) fun (w_1:Env) (h_1:And (Run B precisionGrid w w_1 ((12:Nat))) (And (@Eq Nat (Env.vars w_1 "grid.D") c14) (And (c15 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B precisionGrid w w_1 ((12:Nat)); let c1_2:Prop:=And (@Eq Nat (Env.vars w_1 "grid.D") c14) (And (c15 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c13) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c12 w_1 (@And.intro (Run B preparePrecision σ w_1 ((20:Nat))) (c11 w_1) (RunStep.mono B preparePrecision σ w_1 (c1 ((8:Nat)) ((12:Nat))) ((20:Nat)) (RunStep.seq B epsilonDenominator precisionGrid σ w w_1 ((8:Nat)) ((12:Nat)) left left_1) (?nAX_g4334_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4334_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear heps hgrid
  all_goals simp_all [FieldsAgree,precisionGrid_value]

theorem precision_form_frame {B K:ℕ} {σ τ:Env} (hr:Run B preparePrecision σ τ K)
    (q:ℚ) (hσ:RamEllipsoidForm.FormOutput q σ):RamEllipsoidForm.FormOutput q τ:=by
  have hs:=hr.frame_var "ell.form.s" (by simp [preparePrecision,epsilonDenominator,precisionGrid,Com.wvars])
  have hn:=hr.frame_var "ell.form.n" (by simp [preparePrecision,epsilonDenominator,precisionGrid,Com.wvars])
  have hd:=hr.frame_var "ell.form.d" (by simp [preparePrecision,epsilonDenominator,precisionGrid,Com.wvars])
  simpa only [RamEllipsoidForm.FormOutput,hs,hn,hd] using hσ

end Lax109476Proofs.RamEllipsoidPrecision

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

theorem form_no_other_writes (b:String)
    (hb:b∉ ["ell.u.s", "ell.u.n", "ell.u.d"]):b∉ ellipsoidForm.warrs:=by
  simp at hb
  simp [ellipsoidForm,ellipsoidMulVecInitialized,ellipsoidMulVec,matrixVectorStep,storeDotAtRow,
    RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,saveForm,
    matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,
    RamDotProduct.dotProduct,dotStep,multiplyAt,addToAccumulator,loadLeft,loadRight,
    storeReduced,multiplyFraction,addFraction,RamArithmetic.normalizeFraction,
    RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs,
    hb.1,hb.2.1,hb.2.2]

theorem form_iter_frame {B K:ℕ} {σ τ:Env} (hr:Run B ellipsoidForm σ τ K):
    τ.vars "iter.k"=σ.vars "iter.k" :=by
  apply hr.frame_var
  simp [ellipsoidForm,ellipsoidMulVecInitialized,ellipsoidMulVec,matrixVectorStep,storeDotAtRow,
    RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Lib.Fill.put,saveForm,
    matrixRowDot,rowDotProduct,rowDotStep,multiplyRowAt,loadRowLeft,
    RamDotProduct.dotProduct,dotStep,multiplyAt,addToAccumulator,loadLeft,loadRight,
    storeReduced,multiplyFraction,addFraction,RamArithmetic.normalizeFraction,
    RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars]

theorem coefficients_no_other_writes (b:String)
    (hb:b∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"]):b∉ prepareCoefficients.warrs:=by
  simp at hb
  simp [prepareCoefficients,initializeCoefficients,computeCoefficients,computeAndStore,
    storeCoefficient,storeReduced,RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,
    Lib.Fill.put,alphaFraction,betaFraction,gammaFraction,scaledInverseFraction,inflationFraction,
    diagonalFraction,RamRounding.upperRootFraction,RamSquareRoot.squareRoot,RamSquareRoot.sqrtLoop,
    RamSquareRoot.sqrtStep,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs,hb.1,hb.2.1,hb.2.2]

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

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem ellipsoidStep_spec (B n H M k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j,Height (A i j) H)
    (ha:∀ i,Height (a i) H) (hc:∀ i,Height (c i) H)
    (hqpos:0 < a ⬝ᵥ (A *ᵥ a)) (hnM:n * n≤ M) (hFM:formHeight n H≤ M)
    (hDM:2 ^ (2 * k + 3 * n + 9)≤ M) (hEM:2 ^ (2 * n + 4)≤ M)
    (hB:2 * (RamShapeCoordinate.shapeCap (coefficientCap M)) ^ 2 + 3 < B):
    Spec B (fun σ => Represents "ell.shape" (flatten A) σ∧ Represents "ell.normal" (List.ofFn a) σ∧
        Represents "ell.center" (List.ofFn c) σ∧ Workspace n σ∧
        σ.vars "vec.n"=n∧ σ.vars "iter.k"=k)
      ellipsoidStep
      (fun _ τ => Represents "ell.nextcenter"
          (List.ofFn (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) τ∧
        Represents "ell.nextshape"
          (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
            (EllipsoidIteration.stepAccuracy n))) τ∧
        Represents "ell.shape" (flatten A) τ∧ Represents "ell.center" (List.ofFn c) τ∧
        τ.vars "vec.n"=n∧ τ.vars "grid.D"=2 ^ (2 * k + 3 * n + 9))
      (stepCost n H M):=by
  let D:=2 ^ (2 * k + 3 * n + 9)
  let E:=2 ^ (2 * n + 4)
  let q:=a ⬝ᵥ (A *ᵥ a)
  let N:=coefficientCap M
  let gs:=coefficients n q D E
  have hcapM:cap n H≤ M:=(formHeight_ge n H hH).trans hFM
  have hHM:H≤ M:=(cap_ge n H hH).2.trans hcapM
  have hM:1≤ M:=hH.trans hHM
  have hMN:M≤ N:=(coefficientCap_bounds M).1
  have hN:1≤ N:=hM.trans hMN
  have hbounds:=unified_word_bounds B M n hn hnM hB
  have hNB:N < B:=hbounds.1
  have hMB:M < B:=hbounds.2.1
  have hnnB:n ^ 2 < B:=hbounds.2.2.1
  have hnB:n < B:=hbounds.2.2.2.1
  have h5B:5 < B:=hbounds.2.2.2.2.1
  have hdims:=hbounds.2.2.2.2.2.1
  have hPrimB:=hbounds.2.2.2.2.2.2.1
  have hRootB:=hbounds.2.2.2.2.2.2.2.1
  have hCenterB:=hbounds.2.2.2.2.2.2.2.2
  have hnleM:n≤ M:=by
    have hnp:n≤ n * n:=by
      simpa only [pow_two] using le_self_pow (by omega:1≤ n) (by decide:(2:ℕ) ≠ 0)
    exact hnp.trans hnM
  have hDpos:0 < D:=Nat.pow_pos (by decide)
  have hEpos:0 < E:=Nat.pow_pos (by decide)
  have hDB:D < B:=hDM.trans_lt hMB
  have hEB:E < B:=hEM.trans_lt hMB
  have hInflB:(E + 1) ^ 2 < B:=by
    have hp:=(Nat.pow_le_pow_left (Nat.add_le_add_right hEM 1) 2).trans
      (Nat.pow_le_pow_right (by omega:1≤ M + 1) (by decide:(2:ℕ)≤ 4))
    have htoN:(M + 1) ^ 4≤ N:=by dsimp [N,coefficientCap]; omega
    exact hp.trans htoN |>.trans_lt hNB
  have hFormB:2 * (formHeight n H) ^ 2 + 3 < B:=by
    have hp:=Nat.pow_le_pow_left hFM 2
    exact lt_of_le_of_lt (by omega) hPrimB
  have hq:Height q M:=height_mono _ (form_height n H A a hH hA ha) hFM
  have hu:∀ i,Height ((A *ᵥ a) i) N:=fun i =>
    height_mono _ (mulVec_height n H A a hH hA ha i) (hcapM.trans hMN)
  have hAc:∀ i j,Height (A i j) N:=fun i j => height_mono _ (hA i j) (hHM.trans hMN)
  have hcc:∀ i,Height (c i) N:=fun i => height_mono _ (hc i) (hHM.trans hMN)
  have hgs:∀ v∈ gs,Height v N:=coefficients_height n M D E q hq hnleM hDM hEM hDpos
  have hg:4 < gs.length:=by simp [gs,coefficients]
  have hα:=hgs gs[0] (by simp [gs,coefficients])
  have hβ:=hgs gs[1] (by simp [gs,coefficients])
  have hγ:=hgs gs[2] (by simp [gs,coefficients])
  have hρ:=hgs gs[3] (by simp [gs,coefficients])
  have hδ:=hgs gs[4] (by simp [gs,coefficients])
  rintro σ ⟨hσA,hσa,hσc, ⟨hσuExt,hσgExt,hσcExt,hσAExt⟩,hσn,hσk⟩
  obtain ⟨τ,hr₁,hτq,hτu,_,_,hτn⟩:=ellipsoidForm_spec B n H A a hH hA ha hdims hFormB
    σ ⟨rows_of_represents "ell.shape" A σ hσA,hσa,
      hσuExt ".s" (by simp),hσuExt ".n" (by simp),hσuExt ".d" (by simp),hσn⟩
  have hτA:=represents_frame hr₁ "ell.shape" _ hσA
    (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp))
  have hτc:=represents_frame hr₁ "ell.center" _ hσc
    (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp)) (form_no_other_writes _ (by simp))
  have hτgExt:=extents_frame hr₁ "ell.coeff" 5 hσgExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτcExt:=extents_frame hr₁ "ell.nextcenter" n hσcExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτAExt:=extents_frame hr₁ "ell.nextshape" (n * n) hσAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact form_no_other_writes _ (by simp))
  have hτk:τ.vars "iter.k"=k:=(form_iter_frame hr₁).trans hσk
  obtain ⟨υ,hr₂,hυE,hυD,hυn,_,hυarr⟩:=preparePrecision_spec B k n hEB hDB τ ⟨hτn,hτk⟩
  have hυq:=precision_form_frame hr₂ q hτq
  have hυA:Represents "ell.shape" (flatten A) υ:=by simpa only [Represents,hυarr] using hτA
  have hυc:Represents "ell.center" (List.ofFn c) υ:=by simpa only [Represents,hυarr] using hτc
  have hυu:Represents "ell.u" (List.ofFn (A *ᵥ a)) υ:=by simpa only [Represents,hυarr] using hτu
  have hυgExt:Extents "ell.coeff" 5 υ:=by simpa only [Extents,hυarr] using hτgExt
  have hυcExt:Extents "ell.nextcenter" n υ:=by simpa only [Extents,hυarr] using hτcExt
  have hυAExt:Extents "ell.nextshape" (n * n) υ:=by simpa only [Extents,hυarr] using hτAExt
  obtain ⟨ρ,hr₃,hρg,hρinput⟩:=prepareCoefficients_spec B n M D E q hn hqpos hq hnleM hDM hEM
    hDpos hEpos hnnB hInflB hPrimB hRootB hNB h5B υ
    ⟨⟨hυq,hυn,hυD,hυE⟩,hυgExt ".s" (by simp),hυgExt ".n" (by simp),hυgExt ".d" (by simp)⟩
  have hρA:=represents_frame hr₃ "ell.shape" _ hυA
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρc:=represents_frame hr₃ "ell.center" _ hυc
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρu:=represents_frame hr₃ "ell.u" _ hυu
    (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp)) (coefficients_no_other_writes _ (by simp))
  have hρcExt:=extents_frame hr₃ "ell.nextcenter" n hυcExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact coefficients_no_other_writes _ (by simp))
  have hρAExt:=extents_frame hr₃ "ell.nextshape" (n * n) hυAExt (by
    intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> exact coefficients_no_other_writes _ (by simp))
  obtain ⟨ξ,hr₄,hξc,hξA,_,hξoldc,hξoldA,_,hξn,hξD⟩:=roundedUpdate_ellipsoid_spec B n N D E A a c gs hg
    hN (hnM.trans hMN) hu hcc hAc hα hβ hγ hρ hδ (hDM.trans hMN) hDpos
    (by simpa only [pow_two] using hnnB) hnB hCenterB hB rfl ρ
    ⟨hρu,hρc,hρA,hρg,hρcExt ".s" (by simp),hρcExt ".n" (by simp),hρcExt ".d" (by simp),
      hρAExt ".s" (by simp),hρAExt ".n" (by simp),hρAExt ".d" (by simp),hρinput.2.1,hρinput.2.2.1⟩
  have hη:(1 / (E:ℚ))=EllipsoidIteration.stepAccuracy n:=by
    simp [E,EllipsoidIteration.stepAccuracy]
  refine ⟨ξ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_, ?_, ?_,hξoldA,hξoldc,hξn,hξD⟩
  · change formCost n H + (20 + (582 * M.size + 876 + updateCost n N))≤ stepCost n H M
    simp only [stepCost,N]
    omega
  · exact hξc
  · simpa only [hη] using hξA

end Lax109476Proofs.RamEllipsoidStep

end

theorem solution:∀ (B n H M k:ℕ) (A:Matrix (Fin n) (Fin n) ℚ) (a c:Fin n→ ℚ),
  2≤ n→
    1≤ H→
      (∀ (i j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (A i j) H)→
        (∀ (i:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (a i) H)→
          (∀ (i:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (c i) H)→
            0 < a ⬝ᵥ A.mulVec a→
              n * n≤ M→
                Lax109476Proofs.RamEllipsoidForm.formHeight n H≤ M→
                  2 ^ (2 * k + 3 * n + 9)≤ M→
                    2 ^ (2 * n + 4)≤ M→
                      2 *
                              Lax109476Proofs.RamShapeCoordinate.shapeCap
                                  (Lax109476Proofs.RamEllipsoidCoefficients.coefficientCap M) ^
                                2 +
                            3 <
                          B→
                        Lax808846Proofs.Reasoning.Spec B
                          (fun (σ:Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                (Lax109476Proofs.RamMatrixStorage.flatten A) σ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.normal" (List.ofFn a) σ∧
                                Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) σ∧
                                  Lax109476Proofs.RamEllipsoidStep.Workspace n σ∧
                                    σ.vars "vec.n"=n∧ σ.vars "iter.k"=k)
                          Lax109476Proofs.RamEllipsoidStep.ellipsoidStep
                          (fun (x τ:Lax808846Proofs.Imp.Env) =>
                            Lax109476Proofs.RamRationalArrays.Represents "ell.nextcenter"
                                (List.ofFn
                                  (Lax109476Proofs.EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))))
                                τ∧
                              Lax109476Proofs.RamRationalArrays.Represents "ell.nextshape"
                                  (Lax109476Proofs.RamMatrixStorage.flatten
                                    (Lax109476Proofs.EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
                                      (Lax109476Proofs.EllipsoidIteration.stepAccuracy n)))
                                  τ∧
                                Lax109476Proofs.RamRationalArrays.Represents "ell.shape"
                                    (Lax109476Proofs.RamMatrixStorage.flatten A) τ∧
                                  Lax109476Proofs.RamRationalArrays.Represents "ell.center" (List.ofFn c) τ∧
                                    τ.vars "vec.n"=n∧ τ.vars "grid.D"=2 ^ (2 * k + 3 * n + 9))
                          (Lax109476Proofs.RamEllipsoidStep.stepCost n H M):= @Lax109476Proofs.RamEllipsoidStep.ellipsoidStep_spec
