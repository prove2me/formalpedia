-- Prove2me | solution 1 for Lax455465Proofs.RamRoundAndOutput.command_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:39.314018+00:00
-- url     : https://prove2.me/submissions/110133cb-caff-4fcb-b2c0-4ce0957a1d8a

import Mathlib.Tactic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax455465Proofs_RamUniformRounding_command_spec_native
import Theorems.Thm_Lax455465Proofs_RamOutputResources_command_spec_native

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

namespace Lax455465Proofs.RamUniformRounding
end Lax455465Proofs.RamUniformRounding
theorem Lax455465Proofs.RamUniformRounding.command_spec:∀ (P:@Polynomial Nat Nat.instSemiring) {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind)
  (I:Lax455465.RationalEncoding.RationalInstance n) (d:Lax455465Proofs.MetricMatrix.Matrix n),
  (∀ (u v:Fin n),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (@NNRat.cast Rat Rat.instNNRatCast (d u v)))→
    LT.lt ((0:Nat))
        (@Lax455465Proofs.RamRoundingInit.support n (@Lax455465.RationalEncoding.RationalInstance.weight n I))→
      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (@Lax455465Proofs.LargeBallRounding.total n I)→
        (∀ (v:Fin n),
            @Eq NNRat (d v v)
              (@OfNat.ofNat NNRat (nat_lit 0)
                (@Zero.toOfNat0 NNRat
                  (@MulZeroClass.toZero NNRat
                    (@instMulZeroClassOfSemiring NNRat
                      (@DivisionSemiring.toSemiring NNRat
                        (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))→
          (∀ (u v t:Fin n),
              @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u t))
                (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                  (@NNRat.cast Rat Rat.instNNRatCast (d v t))))→
            @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                  (@Lax455465Proofs.MetricMatrix.rational n d))→
              ∀ (W:Nat),
                LE.le
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.wordBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P)))
                    W→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) W)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamMetricRounding.Input n I d σ)
                        (And
                          (Lax455465Proofs.RamRegionInvariant.Room n
                            (@Lax455465Proofs.RamRoundingInit.support n
                              (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                            σ)
                          (Lax455465Proofs.RamRegionCut.Room n σ)))
                    Lax455465Proofs.RamMetricRounding.command
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      @Lax455465Proofs.RamRegionCut.Output n I d
                        (@Lax455465Proofs.RamRoundingInit.support n
                          (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                        τ)
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      (Lax455465Proofs.RamRoundingResources.timeBound
                        (Lax455465Proofs.RamRoundingResources.baseBound P))):= @Lax455465Proofs.RamUniformRounding.command_spec_native
namespace Lax455465Proofs.RamOutputResources
end Lax455465Proofs.RamOutputResources
theorem Lax455465Proofs.RamOutputResources.command_spec:∀ (P:@Polynomial Nat Nat.instSemiring) {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind)
  (I:Lax455465.RationalEncoding.RationalInstance n) (S:Finset (Fin n))
  (z:
    Fin
        (HAdd.hAdd ((1:Nat))
          (HMul.hMul (HMul.hMul n n)
            (HMul.hMul n n)))→
      Rat)
  (hz:
    ∀
      (i:
        Fin
          (HAdd.hAdd ((1:Nat))
            (HMul.hMul (HMul.hMul n n)
              (HMul.hMul n n)))),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (z i)),
  (∀
      (i:
        Fin
          (HAdd.hAdd ((1:Nat))
            (HMul.hMul (HMul.hMul n n)
              (HMul.hMul n n)))),
      Lax455465Proofs.LpInputSize.Height
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I)) P))
        (z i))→
    ∀ (W:Nat),
      LE.le
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.wordBound P))
          W→
        Lax808846Proofs.Reasoning.Spec
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) W)
          (fun (σ:Lax808846Proofs.Imp.Env) =>
            And
              (Lax455465Proofs.RamFlowConvert.Context kind
                (@Lax455465Proofs.RamOptimalDecode.vector
                  (HAdd.hAdd
                    ((1:Nat))
                    (HMul.hMul
                      (HMul.hMul n n)
                      (HMul.hMul n n)))
                  z hz)
                σ)
              (And (@Eq Nat (σ.vars "metric.n") n)
                (And
                  (Lax455465Proofs.RamVirtualState.Prefix
                    (Lax455465Proofs.RamUnsignedBuffer.encode (@Lax455465Proofs.CutScoreData.vertexFlags n S))
                    "cut.flags" σ)
                  (And
                    (LT.lt
                      (HMul.hMul
                        ((2:Nat))
                        (HAdd.hAdd
                          ((1:Nat))
                          (HMul.hMul
                            (HMul.hMul n n)
                            (HMul.hMul n n))))
                      (@List.length Nat (σ.arrs "flow.converted")))
                    (@Eq (List Nat) σ.out (@List.nil Nat))))))
          Lax455465Proofs.RamJointOutput.command
          (fun (x τ:Lax808846Proofs.Imp.Env) =>
            @Eq (List Nat) τ.out
              (@Lax455465.FlowCutCertificate.encodeCertificate n
                (@Lax455465.FlowCutCertificate.Certificate.mk n S
                  (@Lax455465Proofs.CertificatePostprocessing.convertFlow n kind
                    (@Lax455465Proofs.CertificatePostprocessing.primalFlow n z)))))
          (@Polynomial.eval Nat Nat.instSemiring
            (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
            (Lax455465Proofs.RamOutputResources.timeBound P)):= @Lax455465Proofs.RamOutputResources.command_spec_native

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

open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork

abbrev PathFlow (n:ℕ):=List (Fin n)→₀ ℝ≥0

end Lax455465.ConcurrentFlow

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

noncomputable def FlowCertificate.flow {n:ℕ} (certificate:FlowCertificate n):
    PathFlow n:=
  certificate.paths.foldl
    (fun F record => F + Finsupp.single record.1 (record.2:ℝ≥0)) 0

end Lax455465.RationalEncoding

end

section

namespace Lax808846Proofs.Imp

def Com.decNoWrite:(c:Com)→ Decidable c.NoWrite
  | .skip => decidable_of_iff True (by rw [Com.NoWrite])
  | .assign _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .store _ _ _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .seq c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .ite _ c d =>
      have:=c.decNoWrite
      have:=d.decNoWrite
      decidable_of_iff (c.NoWrite∧ d.NoWrite) (by rw [Com.NoWrite])
  | .while _ c =>
      have:=c.decNoWrite
      decidable_of_iff c.NoWrite (by rw [Com.NoWrite])
  | .read _ => decidable_of_iff True (by rw [Com.NoWrite])
  | .write _ => decidable_of_iff False (by rw [Com.NoWrite])

instance:DecidablePred Com.NoWrite:=Com.decNoWrite

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

end Lax455465Proofs.RamFrames

end

section

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowLP

open Lax455465.RationalEncoding Lax109476.LinearProgram

def vector {n:ℕ} (f:ℚ) (x:CommodityArc n→ ℚ):
    Fin (1 + (n * n) * (n * n))→ ℚ:=
  fun j => match (variableIndex n).symm j with
    | .inl _ => f
    | .inr a => x a

def Feasible {n:ℕ} (I:RationalInstance n) (f:ℚ) (x:CommodityArc n→ ℚ):Prop:=
  0≤ f∧ (∀ a,0≤ x a)∧
  (∀ e:Edge n, (∑ st:Edge n,x (st,e))≤ (I.capacity e.1 e.2:ℚ))∧
  ∀ (st:Edge n) (u:Fin n),
    (∑ v,x (st, (u,v))) - (∑ v,x (st, (v,u))) =
      f * divergence I st.1 st.2 u

private theorem sum_variables {n:ℕ} (g:Variable n→ ℚ):
    (∑ j:Fin (1 + (n * n) * (n * n)),g ((variableIndex n).symm j)) =
      g (.inl 0) + ∑ a:CommodityArc n,g (.inr a):=by
  rw [← Equiv.sum_comp (variableIndex n)]
  simp

private theorem capacity_row {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (e:Edge n):
    rowValue (program I) (vector f x) (rowIndex n (.inl e)) =
      ∑ st:Edge n,x (st,e):=by
  simp only [rowValue,program,Equiv.symm_apply_apply,vector]
  change (∑ j, (fun v:Variable n => coefficient I (.inl e) v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j))=_
  rw [sum_variables (n:=n) (fun v => coefficient I (.inl e) v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [coefficient,Fintype.sum_prod_type]

private theorem balance_row {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (b:Balance n):
    (∑ j:Fin (1 + (n * n) * (n * n)),
      balanceCoefficient I b ((variableIndex n).symm j) * vector f x j) =
      -divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v,x (b.1, (b.2,v))) - ∑ v,x (b.1, (v,b.2))):=by
  change (∑ j, (fun v:Variable n => balanceCoefficient I b v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j))=_
  rw [sum_variables (n:=n) (fun v => balanceCoefficient I b v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [balanceCoefficient,Fintype.sum_prod_type,sub_mul,Finset.sum_sub_distrib,
    Finset.sum_ite_irrel]
  rw [Finset.sum_comm]
  simp

private theorem positive_balance_row {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (b:Balance n):
    rowValue (program I) (vector f x) (rowIndex n (.inr (0,b))) =
      -divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v,x (b.1, (b.2,v))) - ∑ v,x (b.1, (v,b.2))):=by
  simp only [rowValue,program,Equiv.symm_apply_apply]
  simpa only [coefficient,ite_true] using balance_row I f x b

private theorem negative_balance_row {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (b:Balance n):
    rowValue (program I) (vector f x) (rowIndex n (.inr (1,b))) =
      -(-divergence I b.1.1 b.1.2 b.2 * f +
        ((∑ v,x (b.1, (b.2,v))) - ∑ v,x (b.1, (v,b.2)))):=by
  simp only [rowValue,program,Equiv.symm_apply_apply,coefficient]
  have h:(1:Fin 2) ≠ 0:=by decide
  simp only [if_neg h,neg_mul,Finset.sum_neg_distrib]
  rw [balance_row]
  ring

theorem feasible_iff {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ):
    PrimalFeasible (program I) (vector f x)↔ Feasible I f x:=by
  constructor
  · rintro ⟨hpos,hrows⟩
    have hf:0≤ f:=by simpa [vector] using hpos (variableIndex n (.inl 0))
    have hx:∀ a,0≤ x a:=by
      intro a; simpa [vector] using hpos (variableIndex n (.inr a))
    refine ⟨hf,hx, ?_, ?_⟩
    · intro e
      have h:=hrows (rowIndex n (.inl e))
      rw [capacity_row] at h
      simpa only [program,Equiv.symm_apply_apply,rowBound] using h
    · intro st u
      have hp:=hrows (rowIndex n (.inr (0, (st,u))))
      have hn:=hrows (rowIndex n (.inr (1, (st,u))))
      rw [positive_balance_row] at hp
      rw [negative_balance_row] at hn
      simp only [program,Equiv.symm_apply_apply,rowBound] at hp hn
      linarith
  · rintro ⟨hf,hx,hcap,hbal⟩
    constructor
    · intro j
      simp only [vector]
      cases (variableIndex n).symm j with
      | inl _ => exact hf
      | inr a => exact hx a
    · intro i
      obtain ⟨r,rfl⟩:=(rowIndex n).surjective i
      cases r with
      | inl e =>
        rw [capacity_row]
        simpa only [program,Equiv.symm_apply_apply,rowBound] using hcap e
      | inr b =>
        rcases b with ⟨sign,st,u⟩
        have hzero:
            -divergence I st.1 st.2 u * f +
              ((∑ v,x (st, (u,v))) - ∑ v,x (st, (v,u)))=0:=by
          rw [hbal]; ring
        have hsign:sign=0∨ sign=1:=by fin_cases sign <;> simp
        rcases hsign with rfl | rfl
        · rw [positive_balance_row,hzero]
          simp [program,rowBound]
        · rw [negative_balance_row,hzero]
          simp [program,rowBound]

theorem objective_value {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ):primalValue (program I) (vector f x)=f:=by
  simp only [primalValue,program,vector]
  change (∑ j, (fun v:Variable n => objective v *
    (match v with | .inl _ => f | .inr a => x a)) ((variableIndex n).symm j))=_
  rw [sum_variables (n:=n) (fun v => objective v *
    (match v with | .inl _ => f | .inr a => x a))]
  simp [objective]

end Lax455465Proofs.DirectedFlowLP

end

section

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.DirectedFlowBounds

open Lax455465.ProductNetwork Lax455465.RationalEncoding
open Lax455465Proofs.DirectedFlowLP Lax109476.LinearProgram
open Lax109476.RationalCertificates Lax109476.FarkasCertificate
open Lax109476.RecessionDirection

theorem vector_representation {n:ℕ}
    (z:Fin (1 + (n * n) * (n * n))→ ℚ):
    vector (z (variableIndex n (.inl 0)))
      (fun a => z (variableIndex n (.inr a)))=z:=by
  funext j
  obtain ⟨v,rfl⟩:=(variableIndex n).surjective j
  cases v with
  | inl i =>
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [vector]
  | inr a => simp [vector]

end Lax455465Proofs.DirectedFlowBounds

end

section

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowDual

open Lax455465.RationalEncoding Lax455465Proofs.DirectedFlowLP Lax109476.LinearProgram

def potential {n:ℕ} (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ)
    (st:Edge n) (u:Fin n):ℚ:=
  y (rowIndex n (.inr (0, (st,u)))) - y (rowIndex n (.inr (1, (st,u))))

theorem objective_eq {n:ℕ} (I:RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ):
    dualValue (program I) y=∑ u, ∑ v, (I.capacity u v:ℚ) * length y u v:=by
  unfold dualValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program,rowBound,length,Fintype.sum_sum_type,Fintype.sum_prod_type]

theorem arc_column {n:ℕ} (I:RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ) (st:Edge n) (u v:Fin n):
    columnValue (program I) y (variableIndex n (.inr (st, (u,v)))) =
      length y u v + potential y st u - potential y st v:=by
  unfold columnValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program,coefficient,balanceCoefficient,potential,length,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,
    sub_mul,Finset.sum_sub_distrib,Finset.sum_ite_irrel]
  ring

theorem value_column {n:ℕ} (I:RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ):
    columnValue (program I) y (variableIndex n (.inl 0)) =
      ∑ st:Edge n, (I.weight st.1:ℚ) * I.weight st.2 *
        (potential y st st.2 - potential y st st.1):=by
  unfold columnValue
  rw [← Equiv.sum_comp (rowIndex n)]
  simp [program,coefficient,balanceCoefficient,divergence,potential,
    Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_two,
    sub_mul,Finset.sum_sub_distrib,Finset.sum_ite_irrel]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  by_cases hst:s=t
  · subst t; simp
  · simp [hst] <;> ring

theorem dual_geometry {n:ℕ} (I:RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ)
    (hy:DualFeasible (program I) y):
    (∀ u v,0≤ length y u v)∧
    (∀ st u v,potential y st v - potential y st u≤ length y u v)∧
    1≤ ∑ st:Edge n, (I.weight st.1:ℚ) * I.weight st.2 *
      (potential y st st.2 - potential y st st.1):=by
  refine ⟨fun u v => hy.1 _, ?_, ?_⟩
  · intro st u v
    have h:=hy.2 (variableIndex n (.inr (st, (u,v))))
    rw [arc_column] at h
    have hc:(program I).c (variableIndex n (.inr (st, (u,v))))=0:=by
      simp [program,objective]
    rw [hc] at h
    linarith
  · have h:=hy.2 (variableIndex n (.inl 0))
    rw [value_column] at h
    simpa only [program,Equiv.symm_apply_apply,objective] using h

end Lax455465Proofs.DirectedFlowDual

end

section

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

def Nonnegative {n:ℕ} (d:Distance n):Prop:= ∀ u v,0≤ d u v

def ClosedAt {n:ℕ} (d:Distance n) (p:Fin n):Prop:=
  ∀ u v,d u v≤ d u p + d p v

theorem step_le {n:ℕ} (d:Distance n) (p u v:Fin n):step d p u v≤ d u v:=
  min_le_left _ _

theorem step_via {n:ℕ} (d:Distance n) (p u v:Fin n):
    step d p u v≤ d u p + d p v:=min_le_right _ _

theorem nonnegative_step {n:ℕ} (d:Distance n) (p:Fin n) (h:Nonnegative d):
    Nonnegative (step d p):=by
  intro u v
  exact le_min (h u v) (add_nonneg (h u p) (h p v))

theorem closed_step {n:ℕ} (d:Distance n) (p q:Fin n)
    (hnonneg:Nonnegative d) (hclosed:ClosedAt d q):ClosedAt (step d p) q:=by
  intro u v
  by_cases hu:d u q≤ d u p + d p q
  · have hlu:step d p u q=d u q:=min_eq_left hu
    rw [hlu]
    by_cases hv:d q v≤ d q p + d p v
    · rw [show step d p q v=d q v from min_eq_left hv]
      exact (step_le d p u v).trans (hclosed u v)
    · rw [show step d p q v=d q p + d p v from min_eq_right (le_of_not_ge hv)]
      have h:=step_via d p u v
      have hq:=hclosed u p
      linarith
  · have hlu:step d p u q=d u p + d p q:=min_eq_right (le_of_not_ge hu)
    rw [hlu]
    by_cases hv:d q v≤ d q p + d p v
    · rw [show step d p q v=d q v from min_eq_left hv]
      have h:=step_via d p u v
      have hq:=hclosed p v
      linarith
    · rw [show step d p q v=d q p + d p v from min_eq_right (le_of_not_ge hv)]
      have h:=step_via d p u v
      have hpq:=hnonneg p q
      have hqp:=hnonneg q p
      linarith

theorem closed_pivot {n:ℕ} (d:Distance n) (p:Fin n) (h:Nonnegative d):
    ClosedAt (step d p) p:=by
  intro u v
  have hu:step d p u p=d u p:=min_eq_left (by linarith [h p p])
  have hv:step d p p v=d p v:=min_eq_left (by linarith [h p p])
  rw [hu,hv]
  exact step_via d p u v

theorem nonnegative_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (h:Nonnegative d):Nonnegative (iterate d pivots):=by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (nonnegative_step d p h)

theorem iterate_le {n:ℕ} (d:Distance n) (pivots:List (Fin n)) (u v:Fin n):
    iterate d pivots u v≤ d u v:=by
  induction pivots generalizing d with
  | nil => exact le_rfl
  | cons p rest ih => exact (ih (step d p)).trans (step_le d p u v)

theorem closed_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n)) (q:Fin n)
    (hnonneg:Nonnegative d) (hclosed:ClosedAt d q):ClosedAt (iterate d pivots) q:=by
  induction pivots generalizing d with
  | nil => exact hclosed
  | cons p rest ih =>
    exact ih (step d p) (nonnegative_step d p hnonneg) (closed_step d p q hnonneg hclosed)

theorem pivots_closed {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (hnonneg:Nonnegative d):∀ q∈ pivots,ClosedAt (iterate d pivots) q:=by
  induction pivots generalizing d with
  | nil => simp
  | cons p rest ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact closed_iterate (step d q) rest q (nonnegative_step d q hnonneg)
        (closed_pivot d q hnonneg)
    · exact ih (step d p) (nonnegative_step d p hnonneg) q hq

theorem triangle {n:ℕ} (d:Distance n) (h:Nonnegative d) (u v w:Fin n):
    solve d u w≤ solve d u v + solve d v w:=
  pivots_closed d (List.finRange n) h v (List.mem_finRange v) u w

theorem potential_step {n:ℕ} (d:Distance n) (p:Fin n) (a:Fin n→ ℚ)
    (h:∀ u v,a v - a u≤ d u v):∀ u v,a v - a u≤ step d p u v:=by
  intro u v
  apply le_min (h u v)
  linarith [h u p,h p v]

theorem potential_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (a:Fin n→ ℚ) (h:∀ u v,a v - a u≤ d u v):
    ∀ u v,a v - a u≤ iterate d pivots u v:=by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (potential_step d p a h)

theorem nonnegative_zeroDiagonal {n:ℕ} (d:Distance n) (h:Nonnegative d):
    Nonnegative (zeroDiagonal d):=by
  intro u v
  unfold zeroDiagonal
  split_ifs; exact le_rfl; exact h u v

theorem potential_zeroDiagonal {n:ℕ} (d:Distance n) (a:Fin n→ ℚ)
    (h:∀ u v,a v - a u≤ d u v):
    ∀ u v,a v - a u≤ zeroDiagonal d u v:=by
  intro u v
  unfold zeroDiagonal
  split_ifs with huv
  · subst v; simp
  · exact h u v

theorem diagonal_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (hnonneg:Nonnegative d) (hdiag:∀ u,d u u=0):
    ∀ u,iterate d pivots u u=0:=by
  induction pivots generalizing d with
  | nil => exact hdiag
  | cons p rest ih =>
    apply ih (step d p) (nonnegative_step d p hnonneg)
    intro u
    simp only [step,hdiag]
    exact min_eq_left (add_nonneg (hnonneg u p) (hnonneg p u))

theorem dualDistance_spec {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ)
    (hy:Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y):
    Nonnegative (dualDistance y)∧
    (∀ u,dualDistance y u u=0)∧
    (∀ u v w,dualDistance y u w≤ dualDistance y u v + dualDistance y v w)∧
    1≤ ∑ st:Lax455465Proofs.DirectedFlowLP.Edge n,
      (I.weight st.1:ℚ) * I.weight st.2 * dualDistance y st.1 st.2:=by
  obtain ⟨hnonneg,hpot,hsep⟩:=Lax455465Proofs.DirectedFlowDual.dual_geometry I y hy
  have hinit:=nonnegative_zeroDiagonal _ hnonneg
  refine ⟨nonnegative_iterate _ _ hinit, ?_,triangle _ hinit,hsep.trans ?_⟩
  · exact diagonal_iterate _ _ hinit (fun u => by simp [zeroDiagonal])
  · apply Finset.sum_le_sum
    intro st _
    exact mul_le_mul_of_nonneg_left
      (potential_iterate _ _ (Lax455465Proofs.DirectedFlowDual.potential y st)
        (potential_zeroDiagonal _ _ (hpot st)) st.1 st.2)
      (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _))

theorem dualDistance_cost {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ)
    (hy:Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y):
    (∑ u, ∑ v, (I.capacity u v:ℚ) * dualDistance y u v)≤
      Lax109476.LinearProgram.dualValue (Lax455465Proofs.DirectedFlowLP.program I) y:=by
  rw [Lax455465Proofs.DirectedFlowDual.objective_eq]
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_left _ (NNRat.coe_nonneg _)
  have h:=iterate_le (zeroDiagonal (Lax455465Proofs.DirectedFlowDual.length y))
    (List.finRange n) u v
  apply h.trans
  unfold zeroDiagonal
  split_ifs
  · exact hy.1 _
  · exact le_rfl

end Lax455465Proofs.RationalDistances

end

section

namespace Lax455465Proofs.RegionBudget

theorem steps_le_log (p:ℕ) (hp:2≤ p):
    (steps p:ℝ)≤ 6 * (Real.log p / Real.log 2):=by
  have hpReal:(2:ℝ)≤ p:=by exact_mod_cast hp
  have htwo:0 < Real.log 2:=Real.log_pos (by norm_num)
  have hpNonzero:p ≠ 0:=by omega
  have hpowerNat:2 ^ Nat.log2 p≤ p:=by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hpNonzero
  have hpower:(2:ℝ) ^ Nat.log2 p≤ p:=by exact_mod_cast hpowerNat
  have hlog:=Real.log_le_log (pow_pos (show (0:ℝ) < 2 by norm_num) _) hpower
  rw [Real.log_pow] at hlog
  have hfloor:(Nat.log2 p:ℝ)≤ Real.log p / Real.log 2:=
    (le_div_iff₀ htwo).mpr hlog
  have hone:1≤ Real.log p / Real.log 2:=by
    apply (le_div_iff₀ htwo).mpr
    simpa only [one_mul] using Real.log_le_log (show (0:ℝ) < 2 by norm_num) hpReal
  unfold steps
  push_cast
  nlinarith

end Lax455465Proofs.RegionBudget

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume

theorem weight_nonnegative {n:ℕ} (capacity length:Matrix n)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    0≤ weight capacity length:=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hc u v) (hl u v)

end Lax455465Proofs.RegionCharging

end

section

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.CutSweeps

open Lax455465.ProductNetwork Lax455465.RationalEncoding

theorem massQ_cast {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    (massQ I S:ℝ)=(mass I.weights S:ℝ):=by
  simp [massQ,mass,RationalInstance.weights]
  rfl

theorem capacityQ_cast {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    (capacityQ I S:ℝ)=(cutCapacity I.network S:ℝ):=by
  simp [capacityQ,cutCapacity,RationalInstance.network]
  rfl

theorem ratioQ_cast {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    (ratioQ I S:ℝ)=(ratioCost I.network I.weights S:ℝ):=by
  simp only [ratioQ,Rat.cast_div,Rat.cast_mul,massQ_cast,capacityQ_cast,
    ratioCost,NNReal.coe_div,NNReal.coe_mul]

theorem admissibleQ_iff {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    admissibleQ I S↔ AdmissibleCut I.weights S:=by
  simp only [admissibleQ,AdmissibleCut, ← NNReal.coe_pos, ← massQ_cast]
  norm_cast

end Lax455465Proofs.CutSweeps

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

theorem weights_le {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (v:Fin n):
    weights I active v≤ (I.weight v:ℚ):=by
  unfold weights
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

end Lax455465Proofs.RegionLoop

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionRounding

open Lax455465.RationalEncoding RegionLoop CutSweeps RationalDistances

def supportSize {n:ℕ} (I:RationalInstance n):ℕ:=(RegionSelection.support (weights I Finset.univ)).card

end Lax455465Proofs.RegionRounding

end

section

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.MetricRounding

open Lax455465.RationalEncoding Lax455465.ProductNetwork CutSweeps RationalDistances RegionRounding

theorem supportSize_eq {n:ℕ} (I:RationalInstance n):supportSize I=supportCount I.weights:=by
  unfold supportSize RegionSelection.support supportCount
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,RegionLoop.weights, ↓reduceIte]
  change (0:ℚ) < (I.weight v:ℚ)↔ (0:ℝ≥0) < (I.weight v:ℝ≥0)
  norm_cast

theorem total_positive {n:ℕ} (I:RationalInstance n) (hp:0 < supportSize I):
    0 < LargeBallRounding.total I:=by
  obtain ⟨v,hv⟩:=Finset.card_pos.mp hp
  have hroot:=(Finset.mem_filter.mp hv).2
  have hpositive:0 < (I.weight v:ℚ):=hroot.trans_le (RegionLoop.weights_le I Finset.univ v)
  exact hpositive.trans_le (Finset.single_le_sum (fun u _ => NNRat.coe_nonneg (I.weight u)) (Finset.mem_univ v))

end Lax455465Proofs.MetricRounding

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.ArcCertificates

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding
open Lax455465Proofs.DirectedFlowLP Lax455465Proofs.DirectedFlowBounds

def certificate {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (_h:Feasible I f x):ArcCertificate n where
  value:=f.toNNRat
  arcs s t u v:=(x ((s,t), (u,v))).toNNRat

private theorem cast_rational (q:ℚ≥0):
    ((q:ℝ≥0):ℝ)=((q:ℚ):ℝ):=by
  change (NNRat.cast q:ℝ)=((q:ℚ):ℝ)
  exact (Rat.cast_nnratCast q).symm

theorem certificate_valid {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (h:Feasible I f x):
    IsArcConcurrentFlow .directed I.network I.weights
      ((certificate I f x h).value:ℝ≥0) (certificate I f x h).flow:=by
  have hvalue:(((certificate I f x h).value:ℝ≥0):ℝ)=(f:ℝ):=by
    rw [cast_rational]
    simp [certificate,Rat.coe_toNNRat f h.1]
  have harcs:∀ s t u v, ((certificate I f x h).flow s t u v:ℝ) =
      (x ((s,t), (u,v)):ℝ):=by
    intro s t u v
    change (((x ((s,t), (u,v))).toNNRat:ℝ≥0):ℝ)=_
    rw [cast_rational,Rat.coe_toNNRat _ (h.2.1 _)]
  constructor
  · intro u v
    apply NNReal.coe_le_coe.mp
    simp only [totalEdgeLoad,totalArcLoad,NNReal.coe_sum,harcs,
      RationalInstance.network,cast_rational]
    have hcap:=h.2.2.1 (u,v)
    have hR:(∑ st:Edge n, (x (st, (u,v)):ℝ))≤
        ((I.capacity u v:ℚ):ℝ):=by exact_mod_cast hcap
    simpa only [Fintype.sum_prod_type] using hR
  · intro s t u
    have hbal:=h.2.2.2 (s,t) u
    have hR:(∑ v, (x ((s,t), (u,v)):ℝ)) -
        (∑ v, (x ((s,t), (v,u)):ℝ)) =
        (f:ℝ) * (divergence I s t u:ℝ):=by exact_mod_cast hbal
    simp only [harcs]
    rw [hR]
    simp only [divergence,requiredSupply,pairDemand]
    split_ifs <;> simp [NNReal.coe_mul,hvalue,RationalInstance.weights,
      cast_rational,Rat.cast_nnratCast] <;> ring

end Lax455465Proofs.ArcCertificates

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators NNReal NNRat

namespace Lax455465Proofs.UndirectedConversion

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

private theorem arc_halved {n:ℕ} (F:ArcCertificate n) (s t u v:Fin n):
    ((halve F).flow s t u v:ℝ)=(F.flow s t u v:ℝ) / 2:=by
  simp [halve,ArcCertificate.flow,NNRat.cast_div]

private theorem load_halved {n:ℕ} (F:ArcCertificate n) (u v:Fin n):
    (totalArcLoad (halve F).flow u v:ℝ)=(totalArcLoad F.flow u v:ℝ) / 2:=by
  simp only [totalArcLoad,NNReal.coe_sum,arc_halved]
  simp only [Finset.sum_div]

private theorem supply_halved {n:ℕ} (π:VertexWeight n) (f:ℝ≥0)
    (s t u:Fin n):
    requiredSupply .undirected π f s t u=requiredSupply .directed π f s t u / 2:=by
  simp only [requiredSupply,pairDemand,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_ofNat]
  split_ifs <;> simp [NNReal.coe_mul,NNReal.coe_div] <;> ring

theorem halve_valid {n:ℕ} (I:RationalInstance n) (F:ArcCertificate n)
    (hsym:I.network.IsUndirected)
    (hF:IsArcConcurrentFlow .directed I.network I.weights (F.value:ℝ≥0) F.flow):
    IsArcConcurrentFlow .undirected I.network I.weights
      ((halve F).value:ℝ≥0) (halve F).flow:=by
  constructor
  · intro u v
    have huv:=hF.1 u v
    have hvu:=hF.1 v u
    simp only [totalEdgeLoad] at huv hvu
    rw [hsym v u] at hvu
    apply NNReal.coe_le_coe.mp
    simp only [totalEdgeLoad,NNReal.coe_add,load_halved]
    have huvR:=NNReal.coe_le_coe.mpr huv
    have hvuR:=NNReal.coe_le_coe.mpr hvu
    linarith
  · intro s t u
    change (∑ v, ((halve F).flow s t u v:ℝ)) -
      (∑ v, ((halve F).flow s t v u:ℝ)) =
      requiredSupply .undirected I.weights (F.value:ℝ≥0) s t u
    simp only [arc_halved]
    rw [← Finset.sum_div, ← Finset.sum_div, ← sub_div,hF.2 s t u,supply_halved]

end Lax455465Proofs.UndirectedConversion

end

section

namespace Lax455465Proofs.RamFlowConvert
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational RamRegionContext
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {kind:EdgeKind} {qs:List ℚ≥0} (h:Context kind qs σ)
    (hx:∀ x∈["flow.kind","lp.columns"],x∉cmd.wvars) (ha:"flow.primal"∉cmd.warrs):Context kind qs τ:=by
  simpa only [Context,Prefix,rr.frame_var "flow.kind" (hx _ (by simp)),
    rr.frame_var "lp.columns" (hx _ (by simp)),rr.frame_arr "flow.primal" ha] using h

end Lax455465Proofs.RamFlowConvert

end

section

open scoped BigOperators NNReal NNRat
namespace Lax455465Proofs.RuntimeCutCertificate
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.FlowCutCertificate Lax109476.LinearProgram RationalDistances CutSweeps

theorem log_bound {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (S:Finset (Fin n))
    (hp:2≤ supportCount I.weights)
    (hbound:ratioQ I S≤ (288/5:ℚ)*(RegionBudget.steps (supportCount I.weights):ℚ)*
      RegionRounding.metricCost I (MetricMatrix.rational d)):
    (ratioQ I S:ℝ)≤ 512*logFactor (supportCount I.weights)*
      (RegionRounding.metricCost I (MetricMatrix.rational d):ℝ):=by
  have hratioR:=Rat.cast_le (K:=ℝ).mpr hbound
  norm_num only [Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] at hratioR
  have hlog:=RegionBudget.steps_le_log (supportCount I.weights) hp
  have hlogpos:0≤ Real.log (supportCount I.weights)/Real.log 2:=by positivity
  have hW:0≤ (RegionRounding.metricCost I (MetricMatrix.rational d):ℝ):=by
    exact_mod_cast RegionCharging.weight_nonnegative (fun u v => (I.capacity u v:ℚ)) (MetricMatrix.rational d)
      (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
  have hbudget:=mul_le_mul_of_nonneg_left hlog (show (0:ℝ)≤ 288/5 by norm_num)
  have hbudgetW:=mul_le_mul_of_nonneg_right hbudget hW
  have hlogW:=mul_nonneg hlogpos hW
  unfold logFactor
  nlinarith

theorem certificate_valid {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (z:Fin (1+(n*n)*(n*n))→ ℚ)
    (y:Fin (n*n+2*((n*n)*n))→ ℚ)
    (hz:PrimalFeasible (DirectedFlowLP.program I) z) (hy:DualFeasible (DirectedFlowLP.program I) y)
    (hmatch:primalValue (DirectedFlowLP.program I) z=dualValue (DirectedFlowLP.program I) y)
    (d:MetricMatrix.Matrix n) (hmetric:MetricMatrix.rational d=dualDistance y)
    (S:Finset (Fin n)) (hadm:admissibleQ I S)
    (hbound:ratioQ I S≤ (288/5:ℚ)*(RegionBudget.steps (supportCount I.weights):ℚ)*
      RegionRounding.metricCost I (MetricMatrix.rational d))
    (hp:2≤ supportCount I.weights) (hsym:kind=.undirected→ I.network.IsUndirected):
    IsValid kind I 512 ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩:=by
  let f:=z (DirectedFlowLP.variableIndex n (.inl 0))
  let x:=fun a => z (DirectedFlowLP.variableIndex n (.inr a))
  have hrepr:DirectedFlowLP.vector f x=z:=DirectedFlowBounds.vector_representation z
  have hfeasible:DirectedFlowLP.Feasible I f x:=by
    rw [←hrepr,DirectedFlowLP.feasible_iff] at hz
    exact hz
  let F:=ArcCertificates.certificate I f x hfeasible
  have hF:=ArcCertificates.certificate_valid I f x hfeasible
  have hprimal:F=CertificatePostprocessing.primalFlow z:=rfl
  have hvalue:(F.value:ℚ)=dualValue (DirectedFlowLP.program I) y:=by
    rw [←hrepr,DirectedFlowLP.objective_value] at hmatch
    simpa only [F,ArcCertificates.certificate,Rat.coe_toNNRat f hfeasible.1] using hmatch
  have hratio:=log_bound I d S hp hbound
  have hcost:(RegionRounding.metricCost I (MetricMatrix.rational d):ℝ)≤ ((F.value:ℚ):ℝ):=by
    rw [hvalue,hmetric]
    exact Rat.cast_le.mpr (dualDistance_cost I y hy)
  have hlog:0≤ logFactor (supportCount I.weights):=by
    unfold logFactor
    positivity
  have hratioF:=hratio.trans (mul_le_mul_of_nonneg_left hcost (mul_nonneg (by norm_num:(0:ℝ)≤ 512) hlog))
  have hdirected:IsValid .directed I 512 ⟨S,F⟩:=by
    refine ⟨(admissibleQ_iff I S).mp hadm,hF,?_⟩
    rw [←ratioQ_cast]
    simpa only [Rat.cast_nnratCast] using hratioF
  rw [←hprimal]
  cases kind with
  | directed => exact hdirected
  | undirected => exact ⟨hdirected.1,UndirectedConversion.halve_valid I F (hsym rfl) hF,hdirected.2.2⟩

end Lax455465Proofs.RuntimeCutCertificate

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRoundAndOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram
open scoped NNRat

theorem support_eq {n:ℕ} (I:RationalInstance n):RamRoundingInit.support I.weight=supportCount I.weights:=by
  have he:RamRoundingInit.support I.weight=RegionRounding.supportSize I:=by
    unfold RamRoundingInit.support RegionRounding.supportSize
    congr 2
    funext v
    simp [RegionLoop.weights]
  exact he.trans (MetricRounding.supportSize_eq I)

set_option maxHeartbeats 0 in

theorem command_spec (metric primal:Polynomial ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (z:Fin (1+(n*n)*(n*n))→ ℚ) (y:Fin (n*n+2*((n*n)*n))→ ℚ)
    (hz:PrimalFeasible (DirectedFlowLP.program I) z) (hy:DualFeasible (DirectedFlowLP.program I) y)
    (hmatch:primalValue (DirectedFlowLP.program I) z=dualValue (DirectedFlowLP.program I) y)
    (d:MetricMatrix.Matrix n) (hmetric:MetricMatrix.rational d=RationalDistances.dualDistance y)
    (hd:∀ u v,LpInputSize.Height (2^(metric.eval (bitSize (encodeInput kind I)))) (d u v:ℚ))
    (hzheight:∀ i,LpInputSize.Height (2^(primal.eval (bitSize (encodeInput kind I)))) (z i))
    (hp:2≤ supportCount I.weights) (hsym:kind=.undirected→ I.network.IsUndirected)
    (W:ℕ) (hW:(wordBound metric primal).eval (bitSize (encodeInput kind I))≤ W):
    Spec (2^W) (fun σ => RamMetricRounding.Input I d σ∧
      RamRegionInvariant.Room n (RamRoundingInit.support I.weight) σ∧ RamRegionCut.Room n σ∧
      RamFlowConvert.Context kind (RamOptimalDecode.vector z hz.1) σ∧
      2*(1+(n*n)*(n*n)) < (σ.arrs "flow.converted").length∧ σ.out=[]) command
      (fun _ τ => ∃ certificate:Lax455465.FlowCutCertificate.Certificate n,
        Lax455465.FlowCutCertificate.IsValid kind I 512 certificate∧
        τ.out=Lax455465.FlowCutCertificate.encodeCertificate certificate)
      ((timeBound metric primal).eval (bitSize (encodeInput kind I))):=by
  let L:=bitSize (encodeInput kind I)
  have hsum:(RamRoundingResources.wordBound (RamRoundingResources.baseBound metric)).eval L+
      (RamOutputResources.wordBound primal).eval L≤ W:=by simpa only [wordBound,Polynomial.eval_add] using hW
  dsimp only [L] at hsum
  have hp':0 < RamRoundingInit.support I.weight:=by rw [support_eq]; omega
  have ht:0 < LargeBallRounding.total I:=MetricRounding.total_positive I (by
    rw [MetricRounding.supportSize_eq]; omega)
  obtain ⟨_,hdiag,htri,hsep⟩:=RationalDistances.dualDistance_spec I y hy
  have hdiag':∀ v,d v v=0:=by
    intro v
    apply NNRat.coe_injective
    change MetricMatrix.rational d v v=0
    rw [hmetric,hdiag]
  have htri':∀ u v t,(d u t:ℚ)≤ (d u v:ℚ)+(d v t:ℚ):=by
    intro u v t
    change MetricMatrix.rational d u t≤ MetricMatrix.rational d u v+MetricMatrix.rational d v t
    rw [hmetric]
    exact htri u v t
  have hsep':1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d):=by
    rw [hmetric]
    simpa only [LargeBallRounding.distanceSeparation,DirectedFlowLP.Edge,Fintype.sum_prod_type] using hsep
  rintro σ ⟨hin,hregion,hcut,hprimal,hroom,hout⟩
  obtain ⟨ν,r1,S,hadm,hbound,hmask⟩:=RamUniformRounding.command_spec metric kind I d hd hp' ht hdiag' htri' hsep'
    W (by omega) σ ⟨hin,hregion,hcut⟩
  obtain ⟨τ,r2,p2⟩:=RamOutputResources.command_spec primal kind I S z hz.1 hzheight W (by omega) ν
    ⟨RamFlowConvert.frame r1 hprimal (by decide) (by decide),
      (r1.frame_var "metric.n" (by decide)).trans hin.nValue,hmask,
      by rw [RamFrames.run_array_length r1]; exact hroom,
      (r1.out_eq (by decide)).trans hout⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [timeBound,Polynomial.eval_add]; rfl),
    ⟨S,CertificatePostprocessing.convertFlow kind (CertificatePostprocessing.primalFlow z)⟩,?_,p2⟩
  exact RuntimeCutCertificate.certificate_valid kind I z y hz hy hmatch d hmetric S hadm
    (by simpa only [support_eq] using hbound) hp hsym

end Lax455465Proofs.RamRoundAndOutput

end

theorem solution:∀ (metric primal:Polynomial ℕ) {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind)
  (I:Lax455465.RationalEncoding.RationalInstance n) (z:Fin (1 + n * n * (n * n))→ ℚ)
  (y:Fin (n * n + 2 * (n * n * n))→ ℚ)
  (hz:Lax109476.LinearProgram.PrimalFeasible (Lax455465Proofs.DirectedFlowLP.program I) z),
  Lax109476.LinearProgram.DualFeasible (Lax455465Proofs.DirectedFlowLP.program I) y→
    Lax109476.LinearProgram.primalValue (Lax455465Proofs.DirectedFlowLP.program I) z =
        Lax109476.LinearProgram.dualValue (Lax455465Proofs.DirectedFlowLP.program I) y→
      ∀ (d:Lax455465Proofs.MetricMatrix.Matrix n),
        Lax455465Proofs.MetricMatrix.rational d=Lax455465Proofs.RationalDistances.dualDistance y→
          (∀ (u v:Fin n),
              Lax455465Proofs.LpInputSize.Height
                (2 ^
                  Polynomial.eval (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                    metric)
                ↑(d u v))→
            (∀ (i:Fin (1 + n * n * (n * n))),
                Lax455465Proofs.LpInputSize.Height
                  (2 ^
                    Polynomial.eval
                      (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I)) primal)
                  (z i))→
              2≤ Lax455465.ProductNetwork.supportCount I.weights→
                (kind=Lax455465.ProductNetwork.EdgeKind.undirected→ I.network.IsUndirected)→
                  ∀ (W:ℕ),
                    Polynomial.eval
                          (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                          (Lax455465Proofs.RamRoundAndOutput.wordBound metric primal)≤
                        W→
                      Lax808846Proofs.Reasoning.Spec (2 ^ W)
                        (fun (σ:Lax808846Proofs.Imp.Env) =>
                          Lax455465Proofs.RamMetricRounding.Input I d σ∧
                            Lax455465Proofs.RamRegionInvariant.Room n (Lax455465Proofs.RamRoundingInit.support I.weight)
                                σ∧
                              Lax455465Proofs.RamRegionCut.Room n σ∧
                                Lax455465Proofs.RamFlowConvert.Context kind
                                    (Lax455465Proofs.RamOptimalDecode.vector z hz.1) σ∧
                                  2 * (1 + n * n * (n * n)) < (σ.arrs "flow.converted").length∧ σ.out=[])
                        Lax455465Proofs.RamRoundAndOutput.command
                        (fun (x τ:Lax808846Proofs.Imp.Env) =>
                          ∃ (certificate:Lax455465.FlowCutCertificate.Certificate n),
                            Lax455465.FlowCutCertificate.IsValid kind I 512 certificate∧
                              τ.out=Lax455465.FlowCutCertificate.encodeCertificate certificate)
                        (Polynomial.eval
                          (Lax759944.BinaryWordEncoding.bitSize (Lax455465.RationalEncoding.encodeInput kind I))
                          (Lax455465Proofs.RamRoundAndOutput.timeBound metric primal)):= @Lax455465Proofs.RamRoundAndOutput.command_spec
