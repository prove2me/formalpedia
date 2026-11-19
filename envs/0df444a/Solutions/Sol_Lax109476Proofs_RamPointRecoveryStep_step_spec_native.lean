-- Prove2me | solution 1 for Lax109476Proofs.RamPointRecoveryStep.step_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:51.317755+00:00
-- url     : https://prove2.me/submissions/0b270221-5ad5-48c2-b8a7-6bb3d693145b

import Mathlib.Tactic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RationalFeasibilityDecision_feasible_correct_native
import Theorems.Thm_Lax109476Proofs_RamRecoveryMinimum_recoverCoordinate_spec_native

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
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
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

namespace Lax109476Proofs.RationalFeasibilityDecision
end Lax109476Proofs.RationalFeasibilityDecision
theorem Lax109476Proofs.RationalFeasibilityDecision.feasible_correct:∀ {m n:Nat} (P:Lax109476.LinearProgram.Program Rat m n),
  Iff (@Eq Bool (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P) Bool.true)
    (@Lax109476.LinearProgram.IsFeasible m n (@Lax109476.RationalCertificates.toReal m n P)):= @Lax109476Proofs.RationalFeasibilityDecision.feasible_correct_native
namespace Lax109476Proofs.RamRecoveryMinimum
end Lax109476Proofs.RamRecoveryMinimum
theorem Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec:∀ (S N w D M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat)
  (hk:LT.lt k n),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((4:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)→
    LT.lt (Lax109476Proofs.BinaryOptimization.steps D)
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)→
      LE.le
          (HMul.hMul
            (HAdd.hAdd D
              ((1:Nat)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) (Lax109476Proofs.BinaryOptimization.steps D)))
          M→
        LE.le M
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) S)→
          LE.le
              (HAdd.hAdd
                (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                ((1:Nat)))
              N→
            LE.le (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w→
              LT.lt D
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w)→
                LT.lt
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (HMul.hMul
                            (HAdd.hAdd
                              (HAdd.hAdd m
                                (HAdd.hAdd n n))
                              ((1:Nat)))
                            n)
                          m)
                        (HAdd.hAdd n n))
                      ((4:Nat)))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  LE.le
                      (Lax109476Proofs.RamStoredFeasibility.wordWidth
                        (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n
                          (HMul.hMul
                            ((4:Nat))
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                              ((2:Nat))))))
                      w→
                    (∀ (i:Fin m) (j:Fin n),
                        Lax109476Proofs.RationalArithmeticBounds.Height
                          (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
                      (∀ (i:Fin m),
                          Lax109476Proofs.RationalArithmeticBounds.Height
                            (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
                        (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
                          (∀ (j:Fin n),
                              @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                                (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                            Lax808846Proofs.Reasoning.Spec
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                ((2:Nat)) w)
                              (fun (σ:Lax808846Proofs.Imp.Env) =>
                                And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k σ)
                                  (And (@Eq Nat (σ.vars "minimum.bound") D)
                                    (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                              Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate
                              (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                                And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k τ)
                                  (Lax109476Proofs.RamReconstructionRecord.Output
                                    (@Lax109476Proofs.CoordinateOptimization.coordinateMinimum
                                      (HAdd.hAdd m
                                        (HAdd.hAdd n n))
                                      n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) D)
                                    τ))
                              (HAdd.hAdd
                                (HAdd.hAdd
                                  (HAdd.hAdd
                                    (HMul.hMul
                                      (HAdd.hAdd
                                        (HAdd.hAdd
                                          (HMul.hMul
                                            ((144:Nat)) M.size)
                                          ((342:Nat)))
                                        (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n
                                          (HMul.hMul
                                            ((4:Nat))
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              M ((2:Nat))))))
                                      (Lax109476Proofs.BinaryOptimization.steps D))
                                    (HMul.hMul
                                      ((12:Nat)) D.size))
                                  (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                ((48:Nat))):= @Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec_native

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

end

section

namespace Lax109476Proofs.RationalReconstruction

theorem rational_gap (q r:ℚ) (B:ℕ) (hq:q.den≤ B) (hr:r.den≤ B)
    (hne:q ≠ r):(1:ℚ) / (B:ℚ) ^ 2≤ |q - r|:=by
  let a:ℤ:=q.num * r.den - r.num * q.den
  have hD:(0:ℚ) < (q.den:ℚ) * r.den:=by positivity
  have hqd:(q.den:ℚ) ≠ 0:=by positivity
  have hrd:(r.den:ℚ) ≠ 0:=by positivity
  have hid:q - r=(a:ℚ) / ((q.den:ℚ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    simp only [a,Int.cast_sub,Int.cast_mul,Int.cast_natCast]
    field_simp
  have ha:a ≠ 0:=by
    intro h
    rw [h,Int.cast_zero,zero_div] at hid
    exact hne (sub_eq_zero.mp hid)
  have habs:(1:ℚ)≤ |(a:ℚ)|:=by
    have hn:(1:ℕ)≤ a.natAbs:=Int.natAbs_pos.mpr ha
    have h:(1:ℚ)≤ (a.natAbs:ℚ):=by exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have hB:(0:ℚ) < B:=by
    have h:0 < B:=lt_of_lt_of_le q.den_pos hq
    exact_mod_cast h
  have hDb:(q.den:ℚ) * r.den≤ (B:ℚ) ^ 2:=by
    have h₁:(q.den:ℚ)≤ B:=by exact_mod_cast hq
    have h₂:(r.den:ℚ)≤ B:=by exact_mod_cast hr
    simpa only [pow_two] using mul_le_mul h₁ h₂ (by positivity) hB.le
  rw [hid,abs_div,abs_of_pos hD]
  calc
    _≤ 1 / ((q.den:ℚ) * r.den):=one_div_le_one_div_of_le hD hDb
    _≤ _:=(div_le_div_iff_of_pos_right hD).mpr habs

theorem unique_in_interval (l u q r:ℚ) (B:ℕ)
    (hq:q.den≤ B) (hr:r.den≤ B) (hql:l≤ q) (hqu:q≤ u)
    (hrl:l≤ r) (hru:r≤ u) (hwidth:u - l < (1:ℚ) / (B:ℚ) ^ 2):
    q=r:=by
  by_contra hne
  have hgap:=rational_gap q r B hq hr hne
  have hdist:|q - r|≤ u - l:=by apply abs_le.mpr; constructor <;> linarith
  linarith

theorem convergent_eq_real (a:ℚ) (k:ℕ):convergent a k=Real.convergent (a:ℝ) k:=by
  induction k generalizing a with
  | zero => simp [convergent,Real.convergent_zero]
  | succ k ih =>
    simp only [convergent,Real.convergent_succ,Rat.floor_cast]
    rw [ih]
    congr 2
    simp

theorem exists_target_convergent (a q:ℚ)
    (h:|(a:ℝ) - (q:ℝ)| < 1 / (2 * (q.den:ℝ) ^ 2)):
    ∃ k,convergent a k=q:=by
  obtain ⟨k,hk⟩:=Real.exists_rat_eq_convergent h
  exact ⟨k, (convergent_eq_real a k).trans hk.symm⟩

theorem fract_numerator (q:ℚ):(Int.fract q).num=q.num % q.den:=by
  have hd:(q.den:ℚ) ≠ 0:=by positivity
  have hrep:=(Int.fract q).num_div_den
  rw [Rat.den_intFract] at hrep
  have hnum:((Int.fract q).num:ℚ) =
      (q.num:ℚ) - (Int.floor q:ℚ) * q.den:=by
    calc
      _=Int.fract q * q.den:=(div_eq_iff hd).mp hrep
      _=q * q.den - (Int.floor q:ℚ) * q.den:=by rw [Int.fract,sub_mul]
      _=_:=by rw [← Rat.mul_den_eq_num]
  have hnum':(Int.fract q).num=q.num - Int.floor q * q.den:=by exact_mod_cast hnum
  rw [hnum',Rat.floor_def',Int.emod_def]
  ring

def tail (q:ℚ):ℚ:=(Int.fract q)⁻¹

theorem tail_eq_zero_of_den_one (q:ℚ) (hq:q.den=1):tail q=0:=by
  have hfract:Int.fract q=0:=by
    have hn:(Int.fract q).num=0:=by rw [fract_numerator,hq]; simp
    exact Rat.num_eq_zero.mp hn
  simp [tail,hfract]

private theorem remainder_half (d r:ℕ) (hr:0 < r) (hrd:r < d):d % r≤ d / 2:=by
  by_cases h:r≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le,Nat.mod_eq_of_lt (by omega)]
    omega

theorem tail_tail_den_half (q:ℚ) (hq:1 < q.den):(tail (tail q)).den≤ q.den / 2:=by
  have hf:Int.fract q ≠ 0:=by
    intro h
    have hd:=Rat.den_intFract q
    rw [h,Rat.den_zero] at hd
    omega
  have hfp:0 < Int.fract q:=lt_of_le_of_ne (Int.fract_nonneg q) hf.symm
  have hnp:0 < (Int.fract q).num:=Rat.num_pos.mpr hfp
  let r:=(Int.fract q).num.natAbs
  have hr:0 < r:=Int.natAbs_pos.mpr (ne_of_gt hnp)
  have hrint:(r:ℤ)=(Int.fract q).num:=Int.natAbs_of_nonneg hnp.le
  have hnumlt:(Int.fract q).num < (q.den:ℤ):=by
    simpa only [Int.floor_fract,zero_add,one_mul,Rat.den_intFract]
      using Rat.num_lt_succ_floor_mul_den (Int.fract q)
  have hrd:r < q.den:=by rw [← hrint] at hnumlt; exact_mod_cast hnumlt
  have htden:(tail q).den=r:=Rat.den_inv_of_ne_zero hf
  have htnum:(tail q).num=(q.den:ℤ):=by
    simp only [tail,Rat.num_inv, (Int.sign_eq_one_iff_pos).mpr hnp,one_mul,Rat.den_intFract]
  by_cases ht:Int.fract (tail q)=0
  · change ((Int.fract (tail q))⁻¹).den≤ q.den / 2
    rw [ht,inv_zero,Rat.den_zero]
    omega
  · rw [tail,Rat.den_inv_of_ne_zero ht,fract_numerator,htnum,htden]
    have hmod:((q.den:ℤ) % (r:ℤ)).natAbs=q.den % r:=by
      rw [← Int.natCast_emod,Int.natAbs_natCast]
    rw [hmod]
    exact remainder_half q.den r hr hrd

theorem convergent_zero_value (k:ℕ):convergent 0 k=0:=by
  induction k with
  | zero => simp [convergent]
  | succ k ih => simpa [convergent] using ih

theorem convergent_of_den_one (q:ℚ) (hq:q.den=1) (k:ℕ):convergent q k=q:=by
  have hf:Int.fract q=0:=inv_eq_zero.mp (tail_eq_zero_of_den_one q hq)
  have hfloor:(Int.floor q:ℚ)=q:=by
    have h:=Int.floor_add_fract q
    simpa [hf] using h
  cases k with
  | zero => exact hfloor
  | succ k => simp [convergent,hf,convergent_zero_value,hfloor]

theorem iterated_tail_den_one (s:ℕ) (q:ℚ) (hq:q.den≤ 2 ^ s):
    (tail^[2 * s] q).den=1:=by
  induction s generalizing q with
  | zero => simpa using le_antisymm hq q.den_pos
  | succ s ih =>
    have hnext:(tail (tail q)).den≤ 2 ^ s:=by
      by_cases hd:q.den=1
      · rw [tail_eq_zero_of_den_one q hd]
        simp only [tail,Int.fract_zero,inv_zero,Rat.den_zero]
        have hp:0 < 2 ^ s:=by positivity
        omega
      · have hhalf:=tail_tail_den_half q (by have:=q.den_pos; omega)
        have hpow:2 ^ (s + 1)=2 * 2 ^ s:=by rw [pow_succ]; omega
        rw [hpow] at hq
        omega
    have h:=ih (tail (tail q)) hnext
    simpa [Nat.mul_succ,Function.iterate_add_apply,Function.iterate_succ_apply] using h

theorem convergent_stable (j k:ℕ) (q:ℚ) (h:(tail^[j] q).den=1)
    (hjk:j≤ k):convergent q k=q:=by
  induction j generalizing q k with
  | zero => exact convergent_of_den_one q h k
  | succ j ih =>
    cases k with
    | zero => omega
    | succ k =>
      have ht:(tail^[j] (tail q)).den=1:=by
        simpa only [Function.iterate_succ_apply] using h
      have he:=ih k (tail q) ht (by omega)
      change (Int.floor q:ℚ) + (convergent (tail q) k)⁻¹=q
      rw [he,tail,inv_inv]
      exact Int.floor_add_fract q

theorem convergent_stable_size (q:ℚ) (k:ℕ) (hk:2 * q.den.size≤ k):
    convergent q k=q:=by
  apply convergent_stable (2 * q.den.size) k q _ hk
  apply iterated_tail_den_one
  exact (Nat.lt_size_self q.den).le

theorem exists_bounded_target_convergent (a q:ℚ)
    (h:|(a:ℝ) - (q:ℝ)| < 1 / (2 * (q.den:ℝ) ^ 2)):
    ∃ k≤ 2 * a.den.size,convergent a k=q:=by
  obtain ⟨k,hk⟩:=exists_target_convergent a q h
  by_cases hle:k≤ 2 * a.den.size
  · exact ⟨k,hle,hk⟩
  · have ha:a=q:=(convergent_stable_size a k (by omega)).symm.trans hk
    exact ⟨2 * a.den.size,le_rfl, (convergent_stable_size a _ le_rfl).trans ha⟩

theorem reconstruct_spec (l u q:ℚ) (B:ℕ) (h:reconstruct l u B=some q):
    q.den≤ B∧ l≤ q∧ q≤ u:=by
  have hp:decide (q.den≤ B∧ l≤ q∧ q≤ u)=true:=
    List.find?_some (p:=fun (r:ℚ) => decide (r.den≤ B∧ l≤ r∧ r≤ u)) h
  exact of_decide_eq_true hp

theorem reconstruct_exact (l u q:ℚ) (B:ℕ) (hq:q.den≤ B)
    (hql:l≤ q) (hqu:q≤ u) (hwidth:u - l < (1:ℚ) / (2 * (B:ℚ) ^ 2)):
    reconstruct l u B=some q:=by
  have hB:(0:ℚ) < B:=by exact_mod_cast lt_of_lt_of_le q.den_pos hq
  have hqb:(q.den:ℚ)≤ B:=by exact_mod_cast hq
  have hgap:|u - q| < (1:ℚ) / (2 * (q.den:ℚ) ^ 2):=by
    rw [abs_of_nonneg (sub_nonneg.mpr hqu)]
    have hd:2 * (q.den:ℚ) ^ 2≤ 2 * (B:ℚ) ^ 2:=by nlinarith
    have hi:=one_div_le_one_div_of_le (by positivity:(0:ℚ) < 2 * (q.den:ℚ) ^ 2) hd
    linarith
  have hgapR:|(u:ℝ) - (q:ℝ)| < 1 / (2 * (q.den:ℝ) ^ 2):=by
    rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hqu)]
    rw [abs_of_nonneg (sub_nonneg.mpr hqu)] at hgap
    have hc:=(Rat.cast_strictMono (K:=ℝ)) hgap
    simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast] using hc
  obtain ⟨k,hk,he⟩:=exists_bounded_target_convergent u q hgapR
  have hmem:q∈ (List.range (2 * u.den.size + 1)).map (convergent u):=by
    apply List.mem_map.mpr
    exact ⟨k,List.mem_range.mpr (by omega),he⟩
  have hnone:reconstruct l u B ≠ none:=by
    intro h
    have hbad:=List.find?_eq_none.mp h q hmem
    exact hbad (by simpa using And.intro hq (And.intro hql hqu))
  obtain ⟨r,hr⟩:=Option.ne_none_iff_exists'.mp hnone
  have hs:=reconstruct_spec l u r B hr
  have hwide:u - l < (1:ℚ) / (B:ℚ) ^ 2:=by
    have hpos:(0:ℚ) < (B:ℚ) ^ 2:=by positivity
    have hi:(1:ℚ) / (2 * (B:ℚ) ^ 2) < 1 / (B:ℚ) ^ 2:=by
      apply one_div_lt_one_div_of_lt hpos
      nlinarith
    exact hwidth.trans hi
  have heq:=unique_in_interval l u r q B hs.1 hq hs.2.1 hs.2.2 hql hqu hwide
  simpa [heq] using hr

end Lax109476Proofs.RationalReconstruction

end

section

namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

theorem bisect_invariant (query:ℚ→ Bool) (v l u:ℚ)
    (hquery:∀ t,query t=true↔ v≤ t) (hl:l≤ v) (hu:v≤ u) (k:ℕ):
    (bisect query l u k).1≤ v∧ v≤ (bisect query l u k).2∧
      (bisect query l u k).2 - (bisect query l u k).1=(u - l) / (2:ℚ) ^ k:=by
  induction k with
  | zero =>
    simp only [bisect,pow_zero,div_one]
    exact ⟨hl,hu,True.intro⟩
  | succ k ih =>
    let old:=bisect query l u k
    let mid:=(old.1 + old.2) / 2
    change (if query mid then (old.1,mid) else (mid,old.2)).1≤ v∧
      v≤ (if query mid then (old.1,mid) else (mid,old.2)).2∧
      (if query mid then (old.1,mid) else (mid,old.2)).2 -
        (if query mid then (old.1,mid) else (mid,old.2)).1=_
    by_cases hq:query mid=true
    · have hv:=(hquery mid).mp hq
      rw [if_pos hq]
      refine ⟨ih.1,hv, ?_⟩
      change (old.1 + old.2) / 2 - old.1=_
      rw [pow_succ,div_mul_eq_div_div, ← ih.2.2]
      ring
    · have hv:mid≤ v:=(lt_of_not_ge (fun h => hq ((hquery mid).mpr h))).le
      rw [if_neg hq]
      refine ⟨hv,ih.2.1, ?_⟩
      change old.2 - (old.1 + old.2) / 2=_
      rw [pow_succ,div_mul_eq_div_div, ← ih.2.2]
      ring

theorem initial_width_small (B:ℕ) (hB:0 < B):
    (B:ℚ) / (2:ℚ) ^ steps B < 1 / (2 * (B:ℚ) ^ 2):=by
  have hBR:(0:ℚ) < B:=by exact_mod_cast hB
  have hs:(B:ℚ) < (2:ℚ) ^ B.size:=by exact_mod_cast Nat.lt_size_self B
  have hcube:(B:ℚ) ^ 3 < ((2:ℚ) ^ B.size) ^ 3:=
    pow_lt_pow_left₀ hs hBR.le (by decide)
  have he:(2:ℚ) ^ steps B=4 * ((2:ℚ) ^ B.size) ^ 3:=by
    unfold steps
    rw [pow_add,show 3 * B.size=B.size * 3 by omega,pow_mul]
    norm_num
    ring
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  rw [he]
  nlinarith [show (0:ℚ) < ((2:ℚ) ^ B.size) ^ 3 by positivity]

theorem minimum_exact (query:ℚ→ Bool) (v:ℚ) (B:ℕ)
    (hquery:∀ t,query t=true↔ v≤ t) (hvl:0≤ v) (hvu:v≤ B)
    (hden:v.den≤ B):minimum query B=some v:=by
  obtain ⟨hl,hu,hw⟩:=bisect_invariant query v 0 B hquery hvl hvu (steps B)
  apply reconstruct_exact _ _ v B hden hl hu
  rw [hw,sub_zero]
  exact initial_width_small B (lt_of_lt_of_le v.den_pos hden)

end Lax109476Proofs.BinaryOptimization

end

section

open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem coordinateCut_feasible {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (t:ℚ)
    (x:Fin n→ ℝ):
    PrimalFeasible (toReal (coordinateCut P j t)) x↔
      PrimalFeasible (toReal P) x∧ x j≤ (t:ℝ):=by
  have hrow:∀ i:Fin m,rowValue (toReal (coordinateCut P j t)) x
      (Fin.castAdd 1 i)=rowValue (toReal P) x i:=by
    intro i
    simp [rowValue,toReal,coordinateCut]
  have hlast:rowValue (toReal (coordinateCut P j t)) x (Fin.natAdd m 0)=x j:=by
    simp [rowValue,toReal,coordinateCut,apply_ite]
  constructor
  · rintro ⟨hx,hr⟩
    refine ⟨⟨hx,fun i => ?_⟩, ?_⟩
    · have h:=hr (Fin.castAdd 1 i)
      rw [hrow] at h
      simpa [toReal,coordinateCut] using h
    · have h:=hr (Fin.natAdd m 0)
      rw [hlast] at h
      simpa [toReal,coordinateCut] using h
  · rintro ⟨⟨hx,hr⟩,hj⟩
    refine ⟨hx, ?_⟩
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hrow]
      simpa [toReal,coordinateCut] using hr i
    · have hi:i=0:=Subsingleton.elim _ _
      subst i
      rw [hlast]
      simpa [toReal,coordinateCut] using hj

theorem coordinateMinimum_exact {m n:ℕ} (P:Program ℚ m n) (j:Fin n)
    (x:Fin n→ ℚ) (hx:PrimalFeasible (toReal P) (realVector x))
    (hmin:∀ y,PrimalFeasible (toReal P) y→ (x j:ℝ)≤ y j)
    (B:ℕ) (hb:x j≤ B) (hd:(x j).den≤ B):
    coordinateMinimum P j B=some (x j):=by
  apply BinaryOptimization.minimum_exact _ (x j) B _ _ hb hd
  · intro t
    rw [RationalFeasibilityDecision.feasible_correct]
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨hyp,hyt⟩:=(coordinateCut_feasible P j t y).mp hy
      exact (Rat.cast_le (K:=ℝ)).mp ((hmin y hyp).trans hyt)
    · intro ht
      refine ⟨realVector x, (coordinateCut_feasible P j t _).mpr ⟨hx, ?_⟩⟩
      exact (Rat.cast_le (K:=ℝ)).mpr ht
  · exact (Rat.cast_nonneg (K:=ℝ)).mp (hx.1 j)

end Lax109476Proofs.CoordinateOptimization

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates
open RationalMinima

theorem fixedPrefix_feasible {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ)
    (k:ℕ) (y:Fin n→ ℝ):
    PrimalFeasible (toReal (fixedPrefix P x k)) y↔
      PrimalFeasible (toReal P) y∧ ∀ j,j.val < k→ y j=(x j:ℝ):=by
  have hrow:∀ i:Fin m,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.castAdd (n + n) i)=rowValue (toReal P) y i:=by
    intro i
    simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix]
  have hpos:∀ j:Fin n,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.castAdd n j))=if j.val < k then y j else 0:=by
    intro j
    by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix,hj,apply_ite]
  have hneg:∀ j:Fin n,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.natAdd n j))=if j.val < k then -y j else 0:=by
    intro j
    by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix,hj,apply_ite]
  constructor
  · rintro ⟨hy,hr⟩
    refine ⟨⟨hy,fun i => ?_⟩,fun j hj => ?_⟩
    · have h:=hr (Fin.castAdd (n + n) i)
      rw [hrow] at h
      simpa [toReal,fixedPrefix] using h
    · have hp:=hr (Fin.natAdd m (Fin.castAdd n j))
      have hn:=hr (Fin.natAdd m (Fin.natAdd n j))
      rw [hpos] at hp
      rw [hneg] at hn
      simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj] at hp hn
      linarith
  · rintro ⟨⟨hy,hr⟩,hprefix⟩
    refine ⟨hy,fun i => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hrow]
      simpa [toReal,fixedPrefix] using hr i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [hpos]
        by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj,hprefix j]
      · rw [hneg]
        by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj,hprefix j]

end Lax109476Proofs.LexicographicMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization LexicographicBounds

def recoverPrefix {m n:ℕ} (P:Program ℚ m n) (B:ℕ):
    ℕ→ Option (Fin n→ ℚ)
  | 0 => some 0
  | k + 1 =>
    (recoverPrefix P B k).bind (fun old =>
      if h:k < n then
        (coordinateMinimum (fixedPrefix P old k) ⟨k,h⟩ B).map
          (fun v => Function.update old ⟨k,h⟩ v)
      else some old)

theorem recoverPrefix_exact {m n:ℕ} (P:Program ℚ m n) (B:ℕ)
    (x:Fin n→ ℚ) (hx:PrimalFeasible (toReal P) (realVector x))
    (hlex:∀ i, ∀ y,PrimalFeasible (toReal P) y→
      (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i)
    (hb:∀ j,x j≤ B∧ (x j).den≤ B) (k:ℕ) (hk:k≤ n):
    recoverPrefix P B k=some (prefixVector x k):=by
  induction k with
  | zero =>
    simp only [recoverPrefix,Option.some.injEq]
    funext j
    simp [prefixVector]
  | succ k ih =>
    have hkn:k < n:=by omega
    have hprev:=ih (by omega)
    let i:Fin n:= ⟨k,hkn⟩
    have hxf:PrimalFeasible (toReal (fixedPrefix P (prefixVector x k) k)) (realVector x):=by
      apply (fixedPrefix_feasible P _ k _).mpr
      refine ⟨hx,fun j hj => ?_⟩
      simp [prefixVector,hj,realVector]
    have hmin:∀ y,PrimalFeasible (toReal (fixedPrefix P (prefixVector x k) k)) y→
        (x i:ℝ)≤ y i:=by
      intro y hy
      obtain ⟨hyP,hypref⟩:=(fixedPrefix_feasible P _ k y).mp hy
      apply hlex i y hyP
      intro j hj
      have hval:j.val < k:=hj
      simpa [prefixVector,hval] using hypref j hval
    have hcoord:=coordinateMinimum_exact (fixedPrefix P (prefixVector x k) k) i x hxf hmin
      B (hb i).1 (hb i).2
    simp only [recoverPrefix,hprev,Option.bind_some,dif_pos hkn]
    rw [hcoord]
    simp only [Option.map_some,Option.some.injEq]
    funext j
    by_cases hji:j=i
    · subst j
      simp [prefixVector,i,Function.update]
    · have hv:j.val ≠ k:=by intro he; exact hji (Fin.ext he)
      change Function.update (prefixVector x k) i (x i) j=prefixVector x (k + 1) j
      rw [Function.update_of_ne hji]
      simp only [prefixVector]
      have he:(j.val < k + 1)=(j.val < k):=propext (by omega)
      simp only [he]

end Lax109476Proofs.PointRecovery

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

end Lax109476Proofs.RationalArithmeticBounds

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

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

open Lax808846.Ram Lax808846Proofs.Machine

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

namespace Fill

namespace Demo

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

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

namespace Lax109476Proofs.RamScalarFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem value_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (q:ℚ) (h:Value name q σ)
    (hs:name ++ ".s" ∉ c.wvars) (hn:name ++ ".n" ∉ c.wvars)
    (hd:name ++ ".d" ∉ c.wvars):Value name q τ:=by
  simpa only [Value,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

end Lax109476Proofs.RamScalarFrame

end

section

namespace Lax109476Proofs.RamScalarCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem copy_spec (B:ℕ) (a b:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hab:RamCopy.Disjoint a b):
    Spec B (Value a q) (copy a b) (fun _ τ => Value b q τ) 6:=by
  have hsn:a ++ ".n" ≠ b ++ ".s" :=hab ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:a ++ ".d" ≠ b ++ ".s" :=hab ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:a ++ ".d" ≠ b ++ ".n" :=hab ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  have hbSN:b ++ ".s" ≠ b ++ ".n" :=by simp
  have hbSD:b ++ ".s" ≠ b ++ ".d" :=by simp
  have hbND:b ++ ".n" ≠ b ++ ".d" :=by simp
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Value b q τ) σ; let c1:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c2:String→ String:=c1 b; let c3:String:=c2 ".s"; let c4:String→ String:=c1 a; let c5:String:=c4 ".s"; let c6:Nat:=Env.vars σ c5; let c7:Env:=Env.setVar σ c3 c6; let c8:String:=c2 ".n"; let c9:String:=c4 ".n"; let c10:Nat:=Env.vars c7 c9; let c11:Env:=Env.setVar c7 c8 c10; let c12:String:=c2 ".d"; let c13:String:=c4 ".d"; let c14:Nat:=Env.vars c11 c13; let c15:Env:=Env.setVar c11 c12 c14; let c16:Nat→ Nat→ Nat:=Nat.add; let c17:Nat→ Nat:=c16 ((1:Nat)); let c18:Expr:=Expr.var c5; let c19:Nat:=c17 (Expr.size c18); let c20:Expr:=Expr.var c9; let c21:Nat:=c17 (Expr.size c20); let c22:Expr:=Expr.var c13; let c23:Nat:=c17 (Expr.size c22); let c24:Nat:=c16 c21 c23; let c25:Com:=Com.assign c8 c20; let c26:Com:=Com.assign c12 c22; @Exists.intro Env (fun (σ':Env) => And (Run B (copy a b) σ σ' ((6:Nat))) (c0 σ')) c15 (@And.intro (Run B (copy a b) σ c15 ((6:Nat))) (c0 c15) (RunStep.mono B (copy a b) σ c15 (c16 c19 c24) ((6:Nat)) (RunStep.seq B (Com.assign c3 c18) (Com.seq c25 c26) σ c7 c15 c19 c24 (RunStep.assign B σ c3 c18 c6 (RunStep.eval_var B σ c5 hs)) (RunStep.seq B c25 c26 c7 c11 c15 c21 c23 (RunStep.assign B c7 c8 c20 c10 (RunStep.eval_var B c7 c9 ?_)) (RunStep.assign B c11 c12 c22 c14 (RunStep.eval_var B c11 c13 ?_)))) (?nAX_g4103_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4103_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,Ne.symm hbSN,Ne.symm hbSD,Ne.symm hbND]

end Lax109476Proofs.RamScalarCopy

end

section

namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamScalarFrame RamRationalScalars

theorem copyResult_spec (B:ℕ) (a:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (ha:RamCopy.Disjoint a "rat"):
    Spec B (Value a q) (RamScalarCopy.copy a "rat") (fun _ τ => FractionOutput q τ) 6:=by
  refine (RamScalarCopy.copy_spec B a "rat" q h1 hn hd ha).post ?_
  intro σ τ _ hτ
  exact hτ

end Lax109476Proofs.RamArrayResult

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

namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamFrame RamEllipsoidStep RamAdvanceState

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamRecoveryQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamRecoveryData RationalArithmeticBounds RamStoredProgram

theorem extent_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    (m n:ℕ) (hσ:Extent m n σ):Extent m n τ:=
  ⟨RamAdvanceState.extents_of_run hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2⟩

end Lax109476Proofs.RamRecoveryQuery

end

section

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem workspace_of_run {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (m n:ℕ) (h:RamFeasibilityQuery.Workspace m n σ):RamFeasibilityQuery.Workspace m n τ:=by
  rcases h with ⟨hqA,hqb,hpA,hpb,hrows,hrhs,hcenter,hshape,hw,hnormal⟩
  exact ⟨RamAdvanceState.extents_of_run hr _ _ hqA,RamAdvanceState.extents_of_run hr _ _ hqb,
    RamAdvanceState.extents_of_run hr _ _ hpA,RamAdvanceState.extents_of_run hr _ _ hpb,
    RamAdvanceState.extents_of_run hr _ _ hrows,RamAdvanceState.extents_of_run hr _ _ hrhs,
    RamAdvanceState.extents_of_run hr _ _ hcenter,RamAdvanceState.extents_of_run hr _ _ hshape,
    RamAdvanceState.workspace_of_run hr _ hw,RamAdvanceState.extents_of_run hr _ _ hnormal⟩

end Lax109476Proofs.RamStoredFeasibility

end

section

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

theorem workspace_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    (m n:ℕ) (hσ:Workspace m n σ):Workspace m n τ:=
  ⟨RamRecoveryQuery.extent_frame hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2.2.1,
    RamStoredFeasibility.workspace_of_run hr _ _ hσ.2.2.2.2⟩

end Lax109476Proofs.RamRecoveryThreshold

end

section

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization

theorem coordinateMinimum_prefix {m n:ℕ} (P:Program ℚ m n) (D:ℕ)
    (x:Fin n→ ℚ) (hx:PrimalFeasible (toReal P) (realVector x))
    (hlex:∀ i, ∀ y,PrimalFeasible (toReal P) y→
      (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i)
    (hb:∀ j,x j≤ D∧ (x j).den≤ D) (k:ℕ) (hk:k < n):
    coordinateMinimum (fixedPrefix P (prefixVector x k) k) ⟨k,hk⟩ D=some (x ⟨k,hk⟩):=by
  have hprev:=recoverPrefix_exact P D x hx hlex hb k hk.le
  have hnext:=recoverPrefix_exact P D x hx hlex hb (k + 1) hk
  simp only [recoverPrefix,hprev,Option.bind_some,dif_pos hk] at hnext
  obtain ⟨v,hv,he⟩:=Option.map_eq_some_iff.mp hnext
  have hvalue:v=x ⟨k,hk⟩:=by
    have hi:=congrFun he ⟨k,hk⟩
    simpa [prefixVector] using hi
  simpa only [hvalue] using hv

end Lax109476Proofs.PointRecovery

end

section

namespace Lax109476Proofs.RamPointRecoveryStep

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars RamScalarFrame RamRecoveryThreshold
open RationalArithmeticBounds PointRecovery

theorem prefix_height {n:ℕ} (x:Fin n→ ℚ) (k M:ℕ) (hM:1≤ M)
    (hx:∀ j,Height (x j) M):∀ j,Height (prefixVector x k j) M:=by
  intro j
  dsimp only [prefixVector]
  split_ifs
  · exact hx j
  · exact height_mono 0 height_zero (by omega)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem step_spec (S N w D M m n k:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hk:k < n) (hB:4 * M ^ 2 + 3 < 2 ^ w) (hKB:BinaryOptimization.steps D < 2 ^ w)
    (hM:(D + 1) * 2 ^ BinaryOptimization.steps D≤ M) (hMS:M≤ 2 ^ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamRationalReconstruction.wordWidth S≤ w) (hDB:D < 2 ^ w)
    (hsize:((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hwQuery:RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2))≤ w)
    (hA:∀ i j,Height (P.A i j) M) (hb:∀ i,Height (P.b i) M)
    (hxHeight:∀ j,Height (x j) M) (hc:∀ j,P.c j=0)
    (hx:PrimalFeasible (toReal P) (realVector x))
    (hlex:∀ i, ∀ y,PrimalFeasible (toReal P) y→
      (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i)
    (hxBound:∀ j,x j≤ D∧ (x j).den≤ D):
    Spec (2 ^ w) (fun σ => Persistent P (prefixVector x k) k σ∧
      σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N) step
      (fun σ τ => Persistent P (prefixVector x (k + 1)) (k + 1) τ∧
        τ.vars "minimum.bound"=D∧ (τ.arrs "cf.stack").length=N∧
        τ.vars "point.k"=σ.vars "point.k" + 1)
      (coordinateCost S D M m n + 25):=by
  have hM1:1≤ M:=by
    have hp:1≤ 2 ^ BinaryOptimization.steps D:=Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hMB:M < 2 ^ w:=by nlinarith
  have hnB:n < 2 ^ w:=by omega
  have hkB:k < 2 ^ w:=hk.trans hnB
  have h1:1 < 2 ^ w:=by omega
  have hcoord:=coordinateMinimum_prefix P D x hx hlex hxBound k hk
  let i:Fin n:= ⟨k,hk⟩
  rintro σ ⟨hσP,hσD,hσN⟩
  obtain ⟨τ,hr₁,hτP,hτout⟩:=RamRecoveryMinimum.recoverCoordinate_spec S N w D M m n k P (prefixVector x k)
    hk hB hKB hM hMS hN hw hDB hsize hwQuery hA hb (prefix_height x k M hM1 hxHeight) hc σ ⟨hσP,hσD,hσN⟩
  rw [hcoord] at hτout
  change τ.vars "recon.found"=1∧ Value "recon.result" (x i) τ at hτout
  obtain ⟨υ,hr₂,hυrat⟩:=RamArrayResult.copyResult_spec (2 ^ w) "recon.result" (x i) h1
    ((hxHeight i).1.trans_lt hMB) ((hxHeight i).2.trans_lt hMB)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) τ hτout.2
  have hυk:υ.vars "point.k"=k:=(hr₂.frame_var _ (by decide)).trans hτP.1.2.2.2.2.2
  have hr₃:Run (2 ^ w) (.assign "vec.i" (.var "point.k")) υ (υ.setVar "vec.i" k) 2:=
    Run.assign (by simpa only [hυk] using (evalB_var (B:=2 ^ w) (σ:=υ) (x:= "point.k") (hυk ▸ hkB)))
  have hυx:=RamReadBody.represents_frame "point.x" (List.ofFn (prefixVector x k)) hτP.1.2.2.1 hr₂
    (by intro s hs; change "point.x" ++ s∉ ([]:List String); simp)
  obtain ⟨ρ,hr₄,hρx⟩:=storeReduced_spec (2 ^ w) "point.x" (List.ofFn (prefixVector x k)) (x i) k
    (by simpa using hk) h1 hkB ((hxHeight i).1.trans_lt hMB) ((hxHeight i).2.trans_lt hMB)
    (υ.setVar "vec.i" k) ⟨hυx,by simp,value_frame hr₃ "rat" (x i) hυrat (by decide) (by decide) (by decide)⟩
  have hρk:ρ.vars "point.k"=k:=
    (hr₄.frame_var _ (by decide)).trans ((hr₃.frame_var _ (by decide)).trans hυk)
  have hsum:Bop.add.apply (ρ.vars "point.k") 1 < 2 ^ w:=by simpa [hρk] using (show k + 1 < 2 ^ w by omega)
  have hr₅:Run (2 ^ w) (.assign "point.k" (.add (.var "point.k") (.lit 1))) ρ (ρ.setVar "point.k" (k + 1)) 4:=
    Run.assign (by simpa only [hρk,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=2 ^ w) (σ:=ρ) (x:= "point.k") (hρk ▸ hkB)) (evalB_lit h1) hsum))
  let ξ:=ρ.setVar "point.k" (k + 1)
  have hrRest:=hr₂.seq (hr₃.seq (hr₄.seq hr₅))
  have hr:=hr₁.seq hrRest
  have hξA:=RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten P.A) hτP.1.1 hrRest
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hξb:=RamReadBody.represents_frame "point.b" (List.ofFn P.b) hτP.1.2.1 hrRest
    (by intro s hs; simp [RamCopy.suffixes] at hs; rcases hs with rfl | rfl | rfl <;> decide)
  have hξx:Represents "point.x" (List.ofFn (prefixVector x (k + 1))) ξ:=by
    have he:(List.ofFn (prefixVector x k)).set k (x i)=List.ofFn (prefixVector x (k + 1)):=
      RamCenterUpdate.filled_step x i
    rw [he] at hρx
    simpa only [ξ,Represents,arrs_setVar] using hρx
  have hξm:=(hrRest.frame_var "point.m" (by decide)).trans hτP.1.2.2.2.1
  have hξn:=(hrRest.frame_var "point.n" (by decide)).trans hτP.1.2.2.2.2.1
  have hξD:=(hr.frame_var "minimum.bound" (by decide)).trans hσD
  have hξN:(ξ.arrs "cf.stack").length=N:=by
    obtain ⟨_,_,hs⟩:=hr.bigStep
    exact (RamAdvanceState.array_length_of_bigStep hs "cf.stack").trans hσN
  refine ⟨ξ,hr.mono (by dsimp only [coordinateCost]; omega),
    ⟨⟨hξA,hξb,hξx,hξm,hξn,by simp [ξ]⟩,workspace_frame hr _ _ hσP.2⟩,hξD,hξN, ?_⟩
  simp [ξ,hσP.1.2.2.2.2.2]

end Lax109476Proofs.RamPointRecoveryStep

end

theorem solution:∀ (S N w D M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat),
  Nat.lt k n→
    Nat.lt
        (Nat.add
          (Nat.mul ((4:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              ((2:Nat))))
          ((3:Nat)))
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)→
      Nat.lt (Lax109476Proofs.BinaryOptimization.steps D)
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) w)→
        Nat.le
            (Nat.mul
              (Nat.add D
                ((1:Nat)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) (Lax109476Proofs.BinaryOptimization.steps D)))
            M→
          Nat.le M
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) S)→
            Nat.le
                (Nat.add
                  (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                  ((1:Nat)))
                N→
              Nat.le (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w→
                Nat.lt D
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) w)→
                  Nat.lt
                      (Nat.add
                        (Nat.add
                          (Nat.add
                            (Nat.mul
                              (Nat.add
                                (Nat.add m
                                  (Nat.add n n))
                                ((1:Nat)))
                              n)
                            m)
                          (Nat.add n n))
                        ((4:Nat)))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)→
                    Nat.le
                        (Lax109476Proofs.RamStoredFeasibility.wordWidth
                          (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n
                            (Nat.mul
                              ((4:Nat))
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                                ((2:Nat))))))
                        w→
                      (∀ (i:Fin m) (j:Fin n),
                          Lax109476Proofs.RationalArithmeticBounds.Height
                            (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
                        (∀ (i:Fin m),
                            Lax109476Proofs.RationalArithmeticBounds.Height
                              (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
                          (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
                            (∀ (j:Fin n),
                                @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                                  (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                              @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                  (@Lax109476.RationalCertificates.toReal m n P)
                                  (@Lax109476.RationalCertificates.realVector n x)→
                                (∀ (i:Fin n) (y:Fin n→ Real),
                                    @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                        (@Lax109476.RationalCertificates.toReal m n P) y→
                                      (∀ (j:Fin n),
                                          @LT.lt (Fin n) (@instLTFin n) j i→
                                            @Eq Real (y j) (@Rat.cast Real Real.instRatCast (x j)))→
                                        @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (x i)) (y i))→
                                  (∀ (j:Fin n),
                                      And (@LE.le Rat Rat.instLE (x j) (@Nat.cast Rat Rat.instNatCast D))
                                        (Nat.le (x j).den D))→
                                    Lax808846Proofs.Reasoning.Spec
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        ((2:Nat)) w)
                                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x k) k σ)
                                          (And (@Eq Nat (σ.vars "minimum.bound") D)
                                            (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                                      Lax109476Proofs.RamPointRecoveryStep.step
                                      (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x
                                              (Nat.add k
                                                ((1:Nat))))
                                            (Nat.add k
                                              ((1:Nat)))
                                            τ)
                                          (And (@Eq Nat (τ.vars "minimum.bound") D)
                                            (And (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)
                                              (@Eq Nat (τ.vars "point.k")
                                                (Nat.add (σ.vars "point.k")
                                                  ((1:Nat)))))))
                                      (Nat.add
                                        (Lax109476Proofs.RamPointRecoveryStep.coordinateCost S D M m n)
                                        ((25:Nat))):= @Lax109476Proofs.RamPointRecoveryStep.step_spec
