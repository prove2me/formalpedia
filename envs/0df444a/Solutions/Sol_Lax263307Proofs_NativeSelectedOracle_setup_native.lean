-- Prove2me | solution 1 for Lax263307Proofs.NativeSelectedOracle.setup_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:35:13.594579+00:00
-- url     : https://prove2.me/submissions/1b2142e3-7b0a-4fe4-bf8f-395b181e680f

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.Int.NatAbs
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax263307Proofs_NativeSelectedLP_invocation_native
import Theorems.Thm_Lax263307Proofs_NativeSelectedNear_setup_native

set_option maxHeartbeats 0
set_option maxRecDepth 30000

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
namespace Lax109476Proofs.EllipsoidStateSize
end Lax109476Proofs.EllipsoidStateSize
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

namespace Lax263307Proofs.NativeSelectedLP
end Lax263307Proofs.NativeSelectedLP
theorem Lax263307Proofs.NativeSelectedLP.invocation:∀ {f:List Nat→ List Nat} (p:Lax263307Proofs.NativeSelectedLP.Program f) {n:Nat} (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (k r D F R w:Nat)
  (center:Lax263307.MomentLP.Index n r→ Rat),
  LT.lt ((0:Nat)) n→
    LT.lt ((0:Nat)) D→
      LT.lt ((0:Nat)) F→
        LE.le n R→
          LE.le k R→
            LE.le r R→
              LE.le D R→
                LE.le F R→
                  LE.le (Lax263307.MomentLP.dimension n r) R→
                    (∀ (i:Lax263307.MomentLP.Index n r),
                        Lax263307.NativeRoundedStep.height (center i)
                          (HMul.hMul
                            ((80:Nat))
                            (HAdd.hAdd R
                              ((1:Nat)))))→
                      LE.le (@Lax263307Proofs.NativeSelectedLP.wordHeight f p R) w→
                        Lax808846Proofs.Reasoning.Spec
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            ((2:Nat)) w)
                          (@Lax263307Proofs.NativeProjectionTrace.InvocationInput (Lax263307.MomentLP.rowCount n r)
                            (Lax263307.MomentLP.dimension n r) (@Lax263307.MomentLP.program n G inst k r)
                            (@Lax263307.ProjectedOracle.raw (Lax263307.MomentLP.dimension n r) center)
                            (Lax263307Proofs.NativeNodeTolerance.tolerance n D F)
                            (@Lax263307Proofs.NativeSelectedLP.oracleTime f p R))
                          (Lax263307Proofs.NativeProjectionOracle.command
                            (@Lax263307Proofs.NativeSelectedLP.Program.code f p)
                            (@Lax263307Proofs.NativeSelectedLP.Program.coeff f p))
                          (fun (x τ:Lax808846Proofs.Imp.Env) =>
                            And
                              (@Lax263307Proofs.NativeProjectionResult.Output (Lax263307.MomentLP.dimension n r)
                                (@Lax263307Proofs.NativeOracleExecution.projection n r f G inst k D F center) τ)
                              (@Eq Nat (τ.vars "projection.n") (Lax263307.MomentLP.dimension n r)))
                          (@Lax263307Proofs.NativeSelectedLP.callCost f p R):= @Lax263307Proofs.NativeSelectedLP.invocation_native
namespace Lax263307Proofs.NativeSelectedNear
end Lax263307Proofs.NativeSelectedNear
theorem Lax263307Proofs.NativeSelectedNear.setup:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {flow:List Nat→ List Nat} (fp:Lax263307Proofs.NativeSelectedNear.Program flow)
      (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp) cfg.flow→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp) cfg.flowWidth→
          Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
            LT.lt ((0:Nat)) cfg.K→
              LT.lt ((0:Nat)) cfg.b→
                ∀ {n:Nat} (G:SimpleGraph (Fin n))
                  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                  (D k fuel S v H T w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
                  (front:List Nat),
                  Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                      (HAdd.hAdd
                        (HMul.hMul S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                      capacity
                      (HAdd.hAdd fuel
                        ((1:Nat)))
                      n G k (@List.length Nat front)→
                    LT.lt ((1:Nat)) n→
                      LE.le ((4:Nat)) D→
                        LT.lt (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k→
                          ∀
                            (x:
                              Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))→
                                Rat),
                            @Lax263307.LinearRelaxation.IsFeasible n G k
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                (@Lax263307.RationalConditioning.realVector n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                  (@Lax263307.MomentLP.decode Rat n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) x))→
                              (∀
                                  (i:
                                    Fin
                                      (Lax263307.MomentLP.dimension n
                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                  Lax263307Proofs.NativeSignedArithmetic.Bounded
                                    (@HPow.hPow Nat Nat Nat
                                      (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                      ((2:Nat)) H)
                                    (x i))→
                                LE.le
                                    (HAdd.hAdd n
                                      ((1:Nat)))
                                    T→
                                  Lax263307Proofs.NativeNearExecution.Bounds n
                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                      (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        ((2:Nat)) H)
                                      (HMul.hMul
                                        ((2:Nat)) H)
                                      T fuel S w cfg extent front→
                                    LE.le
                                        (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                          (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                            (HMul.hMul
                                              ((2:Nat)) H))
                                          (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.width flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp)
                                          (@Lax263307Proofs.NativeSelectedNear.Program.output flow fp))
                                        w→
                                      (∀ (a:String),
                                          @Membership.mem String (List String) (@List.instMembership String)
                                              Lax263307Proofs.NativeSeparatorContext.workspace a→
                                            LE.le
                                              (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                  (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                  (HMul.hMul
                                                    ((2:Nat)) H))
                                                (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                              (extent a))→
                                        ∀
                                          (child:
                                            (A:Finset (Fin n))→
                                              Nat→ Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                          @Lax263307Proofs.NativeRecursiveSetup.Near n
                                            (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                            (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                            (Lax263307.AlgorithmParameters.load cfg.b n D) fuel S v
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              ((2:Nat)) H)
                                            (HMul.hMul
                                              ((2:Nat)) H)
                                            T w
                                            (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (HMul.hMul
                                                  ((2:Nat)) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                              (Lax263307Proofs.NativeLargeResources.heightExponent cfg.b n
                                                (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                (HMul.hMul
                                                  ((2:Nat)) H))
                                              (@Lax263307Proofs.NativeSelectedNear.Program.code flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow fp)
                                              (@Lax263307Proofs.NativeSelectedNear.Program.time flow fp))
                                            childSteps childTime cfg G inst flow x extent front child
                                            (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                              (HAdd.hAdd
                                                (HMul.hMul S
                                                  (@List.length String
                                                    (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                                (@List.length String
                                                  (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                              capacity):= @Lax263307Proofs.NativeSelectedNear.setup_native

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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem bounded_size (xs:List ℕ) (K:ℕ) (h:∀ x∈ xs,x.size≤ K):
    bitSize xs≤ xs.length * (K + 1):=by
  induction xs with
  | nil => simp [bitSize_nil]
  | cons x xs ih =>
    have hx:=h x List.mem_cons_self
    have ht:=ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    rw [bitSize_cons]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end Lax455465Proofs.WordSize

end

section

open scoped BigOperators

namespace Lax109476.LinearProgram

def IsBoundedAbove {m n:ℕ} (P:Program ℝ m n):Prop:=
  ∃ B:ℝ, ∀ x,PrimalFeasible P x→ primalValue P x≤ B

def IsPrimalOptimal {K:Type} [Ring K] [PartialOrder K] {m n:ℕ}
    (P:Program K m n) (x:Fin n→ K):Prop:=
  PrimalFeasible P x∧ ∀ z,PrimalFeasible P z→ primalValue P z≤ primalValue P x

end Lax109476.LinearProgram

end

section

open scoped BigOperators

namespace Lax109476Proofs.Basic

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem transpose_identity {m n:ℕ} (P:Program ℝ m n)
    (x:Fin n→ ℝ) (y:Fin m→ ℝ):
    (∑ j,columnValue P y j * x j)=∑ i,rowValue P x i * y i:=by
  simp only [columnValue,rowValue,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weak_duality:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x:Fin n→ ℝ) (y:Fin m→ ℝ),
      PrimalFeasible P x→ DualFeasible P y→ primalValue P x≤ dualValue P y:=by
  intro m n P x y hx hy
  calc
    primalValue P x≤ ∑ j,columnValue P y j * x j:=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy.2 j) (hx.1 j)
    _=∑ i,rowValue P x i * y i:=transpose_identity P x y
    _≤ dualValue P y:=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)

theorem farkas_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (y:Fin m→ ℝ),
      IsInfeasibilityCertificate P y→ ¬ IsFeasible P:=by
  intro m n P y hy ⟨x,hx⟩
  have hnonneg:0≤ ∑ j,columnValue P y j * x j:=
    Finset.sum_nonneg fun j _ => mul_nonneg (hy.2.1 j) (hx.1 j)
  have hle:(∑ j,columnValue P y j * x j)≤ dualValue P y:=by
    rw [transpose_identity]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)
  exact (not_lt_of_ge (hnonneg.trans hle)) hy.2.2

end Lax109476Proofs.Basic

end

section

open scoped BigOperators

namespace Lax109476Proofs.Duality

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem row_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ) (i:Fin m):rowValue P (fun j => t * d j) i=t * rowValue P d i:=by
  simp only [rowValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem objective_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ):primalValue P (fun j => t * d j)=t * primalValue P d:=by
  simp only [primalValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem row_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ)
    (i:Fin m):rowValue P (fun j => x j + d j) i=rowValue P x i + rowValue P d i:=by
  simp [rowValue,mul_add,Finset.sum_add_distrib]

theorem objective_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ):
    primalValue P (fun j => x j + d j)=primalValue P x + primalValue P d:=by
  simp [primalValue,mul_add,Finset.sum_add_distrib]

end Lax109476Proofs.Duality

end

section

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def IsCorrectOutcome {m n:ℕ} (P:Program ℚ m n):Certificate m n→ Prop
  | .optimal x _ => IsPrimalOptimal (toReal P) (realVector x)
  | .infeasible _ => ¬ IsFeasible (toReal P)
  | .unbounded _ _ => IsFeasible (toReal P)∧ ¬ IsBoundedAbove (toReal P)

end Lax109476.RationalCertificates

end

section

open scoped BigOperators

namespace Lax109476Proofs.Certificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RecessionDirection Lax109476.RationalCertificates
open Lax109476Proofs.Duality

theorem recession_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x d:Fin n→ ℝ),
      PrimalFeasible P x→ IsImprovingDirection P d→ ¬ IsBoundedAbove P:=by
  intro m n P x d hx hd ⟨B,hB⟩
  have hbase:=hB x hx
  have hpos:0 < primalValue P d:=hd.2.2
  let t:=(B - primalValue P x) / primalValue P d + 1
  have ht:0≤ t:=by
    dsimp [t]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hbase) (le_of_lt hpos)) (by norm_num)
  let z:Fin n→ ℝ:=fun j => x j + t * d j
  have hz:PrimalFeasible P z:=by
    refine ⟨fun j => add_nonneg (hx.1 j) (mul_nonneg ht (hd.1 j)), ?_⟩
    intro i
    change rowValue P (fun j => x j + t * d j) i≤ P.b i
    rw [row_add,row_scale]
    have hdir:t * rowValue P d i≤ 0:=
      mul_nonpos_of_nonneg_of_nonpos ht (hd.2.1 i)
    linarith [hx.2 i]
  have hval:primalValue P z=B + primalValue P d:=by
    change primalValue P (fun j => x j + t * d j)=_
    rw [objective_add,objective_scale]
    dsimp [t]
    field_simp [ne_of_gt hpos]
    ring
  have hbound:=hB z hz
  rw [hval] at hbound
  linarith [hd.2.2]

private theorem cast_row {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (i:Fin m):
    rowValue (toReal P) (realVector x) i=(rowValue P x i:ℚ):=by
  simp [rowValue,toReal,realVector]

private theorem cast_column {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (j:Fin n):
    columnValue (toReal P) (realVector y) j=(columnValue P y j:ℚ):=by
  simp [columnValue,toReal,realVector]

private theorem cast_primal {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ):
    primalValue (toReal P) (realVector x)=(primalValue P x:ℚ):=by
  simp [primalValue,toReal,realVector]

private theorem cast_dual {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ):
    dualValue (toReal P) (realVector y)=(dualValue P y:ℚ):=by
  simp [dualValue,toReal,realVector]

private theorem cast_feasible {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (hx:PrimalFeasible P x):
    PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℚ)
    exact_mod_cast hx.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i:ℚ):ℝ)≤ (P.b i:ℚ)
    exact_mod_cast hx.2 i

private theorem cast_dual_feasible {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:DualFeasible P y):
    DualFeasible (toReal P) (realVector y):=by
  constructor
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    change ((P.c j:ℚ):ℝ)≤ (columnValue P y j:ℚ)
    exact_mod_cast hy.2 j

private theorem cast_farkas {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:IsInfeasibilityCertificate P y):
    IsInfeasibilityCertificate (toReal P) (realVector y):=by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    exact_mod_cast hy.2.1 j
  · rw [cast_dual]
    exact_mod_cast hy.2.2

private theorem cast_direction {m n:ℕ} (P:Program ℚ m n)
    (d:Fin n→ ℚ) (hd:IsImprovingDirection P d):
    IsImprovingDirection (toReal P) (realVector d):=by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (0:ℝ)≤ (d j:ℚ)
    exact_mod_cast hd.1 j
  · intro i
    rw [cast_row]
    exact_mod_cast hd.2.1 i
  · rw [cast_primal]
    exact_mod_cast hd.2.2

theorem certificate_soundness:
    ∀ (m n:ℕ) (P:Program ℚ m n) (certificate:Certificate m n),
      IsValidCertificate P certificate→ IsCorrectOutcome P certificate:=by
  intro m n P certificate h
  cases certificate with
  | optimal x y =>
      rcases h with ⟨hx,hy,heq⟩
      have hxR:=cast_feasible P x hx
      have hyR:=cast_dual_feasible P y hy
      have heqR:primalValue (toReal P) (realVector x) =
          dualValue (toReal P) (realVector y):=by
        rw [cast_primal,cast_dual,heq]
      refine ⟨hxR, ?_⟩
      intro z hz
      rw [heqR]
      exact Lax109476Proofs.Basic.weak_duality m n (toReal P)
        z (realVector y) hz hyR
  | infeasible y =>
      exact Lax109476Proofs.Basic.farkas_soundness m n
        (toReal P) (realVector y) (cast_farkas P y h)
  | unbounded x d =>
      have hxR:=cast_feasible P x h.1
      exact ⟨⟨realVector x,hxR⟩,
        Lax109476Proofs.Certificates.recession_soundness m n (toReal P)
          (realVector x) (realVector d) hxR (cast_direction P d h.2)⟩

end Lax109476Proofs.Certificates

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

@[simp] theorem Com.wvars_skip:Com.skip.wvars=[]:=by simp [Com.wvars]

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

theorem use (B:ℕ) (P:Env→ Prop) (c:Com) (Q:Env→ Env→ Prop) (K:ℕ)
    (h:Spec B P c Q K) (σ:Env) (hσ:P σ):∃ σ',Run B c σ σ' K∧ Q σ σ':=h σ hσ

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

end Lax455465Proofs.RamRational

end

section

namespace Lax263307Proofs.NativeEncodedLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.RegisteredLP

theorem coordinate_bounds (M n:ℕ) (x:Fin n→ ℚ)
    (hx:∀ v∈encodeVector x,v≤ M) (i:Fin n):NativeSignedArithmetic.Bounded M (x i):=by
  have hmem (v:ℕ) (hv:v∈encodeRational (x i)):v∈encodeVector x:=by
    apply List.mem_flatMap.mpr
    exact ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
  exact ⟨hx _ (hmem _ (by simp [encodeRational])),hx _ (hmem _ (by simp [encodeRational]))⟩

end Lax263307Proofs.NativeEncodedLP

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation ConditioningDistribution Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

def Correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ):
    Outcome n→ Prop
  | .near y => PrimalFeasible (toReal P) (realVector y)∧
      ∀ j, |(y j:ℝ) - (center j:ℝ)|≤ (ρ:ℝ)
  | .far a α => (∑ j, |(a j:ℝ)|)≤ 1∧
      (∀ y,PrimalFeasible (toReal P) y→ (∑ j, (a j:ℝ) * y j)≤ (α:ℝ))∧
      (ρ:ℝ) < (∑ j, (a j:ℝ) * (center j:ℝ)) - (α:ℝ)
  | .reject => ¬ IsFeasible (toReal P)

end Lax263307.RationalProjection

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

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem value_mono (coefficients:List ℕ) {x y:ℕ} (h:x≤ y):
    value coefficients x≤ value coefficients y:=by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem exists_coefficients (p:Polynomial ℕ):∃ coefficients:List ℕ,
    ∀ x:ℕ,value coefficients x=p.eval x:=by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[],fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a)::rest, ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    refine ⟨0::coefficients, ?_⟩
    intro x
    simp only [value,Nat.zero_add,hcoeff,Polynomial.eval_mul,Polynomial.eval_X,Nat.mul_comm]

end Lax455465Proofs.RamPolynomial

end

section

namespace Lax455465Proofs.RamInputCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def Invariant (xs:List ℕ) (σ:Env):Prop:=
  σ.vars "input.length"=xs.length∧ σ.vars "input.i" ≤ xs.length∧
  σ.inp=xs.drop (σ.vars "input.i")∧ xs.length≤ (σ.arrs "input.data").length∧
  ∀ j,j < σ.vars "input.i" → (σ.arrs "input.data")[j]?=xs[j]?

theorem drop_head (xs:List ℕ) (i:ℕ) (hi:i < xs.length):
    xs.drop i=xs[i]::xs.drop (i + 1):=by
  exact List.cons_getElem_drop_succ.symm

private theorem prefix_advance (xs buffer:List ℕ) (i:ℕ) (hi:i < xs.length)
    (hbuffer:xs.length≤ buffer.length) (h:∀ j,j < i→ buffer[j]?=xs[j]?):
    ∀ j,j < i + 1→ (buffer.set i xs[i])[j]?=xs[j]?:=by
  intro j hj
  by_cases he:i=j
  · subst j
    rw [List.getElem?_set_self (by omega),List.getElem?_eq_getElem hi]
  · rw [List.getElem?_set_ne he]
    exact h j (by omega)

theorem copyStep_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Invariant xs σ∧ σ.vars "input.i" < xs.length) copyStep
      (fun σ τ => Invariant xs τ∧ τ.vars "input.i"=σ.vars "input.i" + 1) 8:=by
  rintro σ ⟨⟨hcount,hindex,hinp,hlength,harrays⟩,hi⟩
  have hhead:=drop_head xs (σ.vars "input.i") hi
  have hv:=hwords xs[σ.vars "input.i"] (List.getElem_mem hi)
  rw [hhead] at hinp
  have hnext:=prefix_advance xs (σ.arrs "input.data") (σ.vars "input.i") hi hlength harrays
  clear hhead harrays
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (Invariant xs τ) (@Eq Nat (Env.vars τ "input.i") (c0 (Env.vars σ_1 "input.i") ((1:Nat))))) σ; let c2:String→ Nat:=Env.vars (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)); let c3:Nat:=c2 "input.i"; let c4:Nat:=c2 "input.word"; let c5:Env:=Env.setArr (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.data" c3 c4; let c6:Nat:=Env.vars c5 "input.i"; let c7:Nat:=c0 c6 ((1:Nat)); let c8:Env:=Env.setVar c5 "input.i" c7; let c9:Nat→ Nat:=c0 ((1:Nat)); let c10:Nat:=c0 (c9 (Expr.size (Expr.var "input.i"))) (Expr.size (Expr.var "input.word")); let c11:Expr:=Expr.add (Expr.var "input.i") (Expr.lit ((1:Nat))); let c12:Nat:=c9 (Expr.size c11); let c13:Nat:=c0 c10 c12; let c14:Com:=Com.assign "input.i" c11; let c15:Prop:= @Ne (List Nat) (Env.inp σ) (@List.nil Nat); let c16:List Nat→ Prop:= @Ne (List Nat) (@List.drop Nat (Env.vars σ "input.i") xs); let c17:Prop:= @Eq (List Nat) (Env.inp σ) (@List.drop Nat (Env.vars σ "input.i") xs); let c18:Nat:=c0 (Env.vars σ "input.i") ((1:Nat)); let c19:List Nat:= @List.cons Nat (@getElem (List Nat) Nat Nat (fun (as:List Nat) (i:Nat) => Nat.lt i (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) xs (Env.vars σ "input.i") hi) (@List.drop Nat c18 xs); let c20:Prop:= @Eq (List Nat) (@List.drop Nat (Env.vars σ "input.i") xs) (@List.nil Nat); let c21:Prop:= @LT.lt Nat (@Preorder.toLT Nat (@PartialOrder.toPreorder Nat (@LinearOrder.toPartialOrder Nat Nat.instLinearOrder))) (Env.vars σ "input.i") (@List.length Nat xs); let c22:Prop:=Nat.le (@List.length Nat xs) (Env.vars σ "input.i"); @Exists.intro Env (fun (σ':Env) => And (Run B copyStep σ σ' ((8:Nat))) (c1 σ')) c8 (@And.intro (Run B copyStep σ c8 ((8:Nat))) (c1 c8) (RunStep.mono B copyStep σ c8 (c9 c13) ((8:Nat)) (RunStep.seq B (Com.read "input.word") (Com.seq (Com.store "input.data" (Expr.var "input.i") (Expr.var "input.word")) c14) σ (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) c8 ((1:Nat)) c13 (RunStep.read B σ "input.word" (@of_eq_true c15 (@Eq.trans Prop c15 (c16 (@List.nil Nat)) True (@congrFun' (List Nat) Prop (@Ne (List Nat) (Env.inp σ)) c16 (@congrArg (List Nat) (List Nat→ Prop) (Env.inp σ) (@List.drop Nat (Env.vars σ "input.i") xs) (@Ne (List Nat)) (@id c17 (@Eq.mp (@Eq (List Nat) (Env.inp σ) c19) c17 (@congrArg (List Nat) Prop c19 (@List.drop Nat (Env.vars σ "input.i") xs) (@Eq (List Nat) (Env.inp σ)) (@List.getElem_cons_drop Nat xs (Env.vars σ "input.i") hi)) hinp))) (@List.nil Nat)) (@Eq.trans Prop (Not c20) c21 True (@Eq.trans Prop (Not c20) (Not c22) c21 (@congrArg Prop Prop c20 c22 Not (@List.drop_eq_nil_iff._simp_1 Nat xs (Env.vars σ "input.i"))) (@not_le._simp_1 Nat Nat.instLinearOrder (@List.length Nat xs) (Env.vars σ "input.i"))) (@eq_true (Nat.lt (Env.vars σ "input.i") (@List.length Nat xs)) hi))))) (RunStep.seq B (Com.store "input.data" (Expr.var "input.i") (Expr.var "input.word")) c14 (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) c5 c8 c10 c12 (RunStep.store B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.data" (Expr.var "input.i") (Expr.var "input.word") c3 c4 (RunStep.eval_var B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.i" (?nAX_g6127_0_0_0)) (RunStep.eval_var B (let __src:Env:=Env.setVar σ "input.word" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) "input.word" ?_) (?nAX_g6127_0_0_1)) (RunStep.assign B c5 "input.i" c11 c7 (RunStep.eval_add B c5 (Expr.var "input.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "input.i" (?nAX_g6127_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c5 h1) (?nAX_g6127_0_0_3))))) (?nAX_g6127_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6127_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6127_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Invariant]

def copy:Com:=.seq (.read "input.length")
  (.seq (.assign "input.i" (.lit 0))
    (.while (.lt (.var "input.i") (.var "input.length")) copyStep))

theorem copy_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => σ.inp=xs.length::xs∧ xs.length≤ (σ.arrs "input.data").length) copy
      (fun _ τ => τ.vars "input.length"=xs.length∧ τ.inp=[]∧
        ∀ j (hj:j < xs.length), (τ.arrs "input.data")[j]?=some xs[j])
      (12 * xs.length + 7):=by
  have hlo:=Spec.forRangeZero "input.i" "input.length" (Invariant xs) xs.length 8 hlen
    (fun _ h => h.2.1) (fun _ h => h.1) (copyStep_spec B xs h1 hlen hwords)
  have hfinish:=hlo.post (fun _ τ _ h =>
    (show τ.vars "input.length"=xs.length∧ τ.inp=[]∧
      ∀ j (hj:j < xs.length), (τ.arrs "input.data")[j]?=some xs[j] from
      ⟨h.1.1,by simpa only [h.2,List.drop_length] using h.1.2.2.1,
        by
          intro j hj
          have he:=h.1.2.2.2.2 j (by simpa only [h.2] using hj)
          simpa only [List.getElem?_eq_getElem hj] using he⟩))
  rintro σ ⟨hinp,hlength⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "input.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "input.i") (Expr.var "input.length")) copyStep); let c1:Env→ Nat→ Prop:=Run B c0 (let __src:Env:=Env.setVar σ "input.length" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat:=c2 (c3 (c2 ((8:Nat)) ((4:Nat))) (@List.length Nat xs)) ((6:Nat)); let c5:List Nat→ Nat→ Prop:=fun (as:List Nat) (i:Nat) => Nat.lt i (@List.length Nat as); let c6:List Nat→ Nat→ Option Nat:= @getElem? (List Nat) Nat Nat c5 (@List.instGetElem?NatLtLength Nat); let c7:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "input.length") (@List.length Nat xs)) (And (@Eq (List Nat) (Env.inp σ') (@List.nil Nat)) (∀ (j:Nat) (hj:Nat.lt j (@List.length Nat xs)), @Eq (Option Nat) (c6 (Env.arrs σ' "input.data") j) (@some Nat (@getElem (List Nat) Nat Nat c5 (@List.instGetElemNatLtLength Nat) xs j hj))))); let c8:Nat:=c2 (c3 ((12:Nat)) (@List.length Nat xs)) ((7:Nat)); let c9:Env→ Env→ Prop:=fun (x τ:Env) => And (@Eq Nat (Env.vars τ "input.length") (@List.length Nat xs)) (And (@Eq (List Nat) (Env.inp τ) (@List.nil Nat)) (∀ (j:Nat) (hj:Nat.lt j (@List.length Nat xs)), @Eq (Option Nat) (c6 (Env.arrs τ "input.data") j) (@some Nat (@getElem (List Nat) Nat Nat c5 (@List.instGetElemNatLtLength Nat) xs j hj)))); let c10:Env→ Prop:=c9 σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B copy σ σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Prop:= @Ne (List Nat) (Env.inp σ) (@List.nil Nat); let c14:List Nat→ Prop:= @Ne (List Nat) (@List.cons Nat (@List.length Nat xs) xs); let c15:Prop:= @Eq (List Nat) (@List.cons Nat (@List.length Nat xs) xs) (@List.nil Nat); @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => c12) (RunStep.use B (fun (σ_1:Env) => Invariant xs (Env.setVar σ_1 "input.i" ((0:Nat)))) c0 c9 c4 hfinish (let __src:Env:=Env.setVar σ "input.length" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "input.length") (@List.length Nat xs)) (And (@Eq (List Nat) (Env.inp w) (@List.nil Nat)) (∀ (j:Nat) (hj:Nat.lt j (@List.length Nat xs)), @Eq (Option Nat) (c6 (Env.arrs w "input.data") j) (@some Nat (@getElem (List Nat) Nat Nat c5 (@List.instGetElemNatLtLength Nat) xs j hj)))))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "input.length") (@List.length Nat xs)) (And (@Eq (List Nat) (Env.inp w) (@List.nil Nat)) (∀ (j:Nat) (hj:Nat.lt j (@List.length Nat xs)), @Eq (Option Nat) (c6 (Env.arrs w "input.data") j) (@some Nat (@getElem (List Nat) Nat Nat c5 (@List.instGetElemNatLtLength Nat) xs j hj)))); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c12) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c11 w (@And.intro (Run B copy σ w c8) (c10 w) (RunStep.mono B copy σ w (c2 ((1:Nat)) c4) c8 (RunStep.seq B (Com.read "input.length") c0 σ (let __src:Env:=Env.setVar σ "input.length" (@List.headD Nat (Env.inp σ) ((0:Nat))); Env.mk (Env.vars __src) (Env.arrs __src) (@List.tail Nat (Env.inp σ)) (Env.out __src)) w ((1:Nat)) c4 (RunStep.read B σ "input.length" (@of_eq_true c13 (@Eq.trans Prop c13 (c14 (@List.nil Nat)) True (@congrFun' (List Nat) Prop (@Ne (List Nat) (Env.inp σ)) c14 (@congrArg (List Nat) (List Nat→ Prop) (Env.inp σ) (@List.cons Nat (@List.length Nat xs) xs) (@Ne (List Nat)) hinp) (@List.nil Nat)) (@Eq.trans Prop (Not c15) (Not False) True (@congrArg Prop Prop c15 False Not (@eq_false' c15 fun (h_1:c15) => @False.elim False (@noConfusion_of_Nat (List Nat) (@List.ctorIdx Nat) (@List.cons Nat (@List.length Nat xs) xs) (@List.nil Nat) h_1))) not_false_eq_true)))) left) (?nAX_g6129_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6129_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [Invariant]

end Lax455465Proofs.RamInputCopy

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

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax455465Proofs.RamArrayCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Invariant (xs:List ℕ) (source target count:String) (σ:Env):Prop:=
  Prefix xs source σ∧ σ.vars count=xs.length∧ σ.vars "copy.i" ≤ xs.length∧
    xs.length≤ (σ.arrs target).length∧ Prefix (xs.take (σ.vars "copy.i")) target σ

theorem step_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Invariant xs source target count σ∧ σ.vars "copy.i" < xs.length)
      (step source target) (fun σ τ => Invariant xs source target count τ∧
        τ.vars "copy.i"=σ.vars "copy.i"+1) 8:=by
  rintro σ ⟨⟨hp,hc,hi,hroom,ht⟩,hlt⟩
  let i:=σ.vars "copy.i"
  have hi':i < xs.length:=hlt
  have hget:(σ.arrs source)[i]?=some xs[i]:=hp i hi'
  have hiB:i < B:=hi'.trans hlen
  have hvB:xs[i] < B:=hwords _ (List.getElem_mem hi')
  have rstore:Run B (.store target (.var "copy.i") (.get source (.var "copy.i"))) σ
      (σ.setArr target i xs[i]) 4:=Run.store (evalB_var hiB)
        (evalB_get (evalB_var hiB) hget hvB) (by omega)
  let ν:=σ.setArr target i xs[i]
  have rinc:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) ν
      (ν.setVar "copy.i" (i+1)) 4:=Run.assign
    (evalB_bin (op:=.add) (evalB_var (by simpa [ν] using hiB)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  have hprefix:Prefix (xs.take (i+1)) target ν:=by
    intro j hj
    have hj':j < i+1:=by simp only [List.length_take] at hj; omega
    have hxj:j < xs.length:=by omega
    have htake:(xs.take (i+1))[j]=xs[j]:=List.getElem_take
    simp only [ν,arrs_setArr,if_true]
    by_cases he:i=j
    · subst j
      rw [List.getElem?_set_self (by omega)]
      exact congrArg some htake.symm
    · rw [List.getElem?_set_ne he]
      have hji:j < i:=by omega
      have hjtake:j < (xs.take i).length:=by simp only [List.length_take]; omega
      exact (ht j hjtake).trans (congrArg some (by simp only [List.getElem_take,htake]))
  refine ⟨ν.setVar "copy.i" (i+1),rstore.seq rinc,?_,?_⟩
  · refine ⟨?_,?_,by simp; omega,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_neg harray] using hp
    · simpa only [ν,vars_setVar,vars_setArr,if_neg hcount] using hc
    · simpa only [ν,length_arrs_setArr,arrs_setVar] using hroom
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hprefix
  · simp [i]

theorem command_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars count=xs.length∧
      xs.length≤ (σ.arrs target).length) (command source target count)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (12*xs.length+6):=by
  have hloop:=Spec.forRangeZero "copy.i" count (Invariant xs source target count) xs.length 8 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B xs source target count h1 hlen hwords harray hcount)
  rintro σ ⟨hp,hc,hroom⟩
  have hinit:Invariant xs source target count (σ.setVar "copy.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hp
    · simpa only [vars_setVar,if_neg hcount] using hc
    · simpa only [arrs_setVar] using hroom
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,List.length_nil] at hi
      omega
  obtain ⟨τ,hr,hpost⟩:=hloop σ hinit
  exact ⟨τ,by simpa only [command] using hr,hpost.1.1,
    by simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2⟩

end Lax455465Proofs.RamArrayCopy

end

section

namespace Lax455465Proofs.RamEmitWords
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Data (array:String) (stride:ℕ) (xs:List ℕ) (σ:Env):Prop:=
  ∀ i,∀ hi:i < xs.length,(σ.arrs array)[stride*i]?=some xs[i]

def Invariant (array:String) (stride:ℕ) (xs front:List ℕ) (σ:Env):Prop:=
  Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.vars "emit.i"≤ xs.length∧
    σ.out=front++xs.take (σ.vars "emit.i")

theorem command_spec (B:ℕ) (array:String) (stride:ℕ) (xs front:List ℕ)
    (h1:1 < B) (hstride:stride < B) (hoffset:stride*xs.length < B) (hlen:xs.length < B) (hwords:∀ x∈xs,x < B):
    Spec B (fun σ => Data array stride xs σ∧ σ.vars "emit.count"=xs.length∧ σ.out=front)
      (command array stride) (fun _ τ => τ.out=front++xs) (13*xs.length+6):=by
  have hstep:Spec B (fun σ => Invariant array stride xs front σ∧ σ.vars "emit.i" < xs.length)
      (step array stride) (fun σ τ => Invariant array stride xs front τ∧ τ.vars "emit.i"=σ.vars "emit.i"+1) 9:=by
    rintro σ ⟨⟨hp,hcount,hle,hout⟩,hlt⟩
    let i:=σ.vars "emit.i"
    have hi:i < xs.length:=hlt
    have hval:xs[i] < B:=hwords _ (List.getElem_mem hi)
    have he:(Expr.get array (.mul (.lit stride) (.var "emit.i"))).evalB B σ=some xs[i]:=
      evalB_get (evalB_bin (op:=.mul) (evalB_lit hstride) (evalB_var (hi.trans hlen))
        ((Nat.mul_le_mul_left stride hi.le).trans_lt hoffset)) (hp i hi) hval
    let ν:Env:= {σ with out:=σ.out++[xs[i]]}
    have r1:Run B (.write (.get array (.mul (.lit stride) (.var "emit.i")))) σ ν 5:=Run.write he
    have r2:Run B (.assign "emit.i" (.add (.var "emit.i") (.lit 1))) ν (ν.setVar "emit.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (evalB_var (hi.trans hlen)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨_,r1.seq r2,⟨hp,by simpa [ν] using hcount,by simp; omega,?_⟩,by simp [i,ν]⟩
    change σ.out++[xs[i]]=front++xs.take (i+1)
    rw [List.take_succ_eq_append_getElem hi,←List.append_assoc]
    exact congrArg (fun a => a++[xs[i]]) hout
  have hloop:=Spec.forRangeZero "emit.i" "emit.count" (Invariant array stride xs front) xs.length 9 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) hstep
  rintro σ ⟨hp,hcount,hout⟩
  obtain ⟨τ,rr,pr⟩:=hloop σ ⟨hp,by simpa using hcount,by simp,by simpa using hout⟩
  exact ⟨τ,by simpa [command] using rr,by simpa only [pr.2,List.take_length] using pr.1.2.2.2⟩

end Lax455465Proofs.RamEmitWords

end

section

namespace Lax263307Proofs.MomentLP

open Lax263307.LinearRelaxation Lax263307.CoordinateCatalog Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem single_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)):
    (∑ j, (singleRow A j:ℝ) * x j)=value (decode x) A:=by
  by_cases hA:A.card≤ r + 2
  · let B:Coordinate n r:= ⟨A,hA⟩
    let i:Index n r:=(indexing n r).symm B
    have heq (j:Index n r):A=(indexing n r j).val↔ i=j:=by
      constructor
      · intro h
        apply (indexing n r).injective
        change indexing n r ((indexing n r).symm B)=indexing n r j
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext h
      · intro h
        rw [← h]
        simp [i,B]
    simp only [singleRow,apply_ite,Rat.cast_one,Rat.cast_zero,ite_mul,one_mul,zero_mul]
    simp_rw [heq]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    simp [value,decode,hA,i,B]
  · have hne (j:Index n r):A ≠ (indexing n r j).val:=by
      intro h
      exact hA (h ▸ (indexing n r j).property)
    simp [singleRow,hne,value,hA]

theorem monotone_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)) (v:Fin n):
    (∑ j, (monotoneRow A v j:ℝ) * x j)=value (decode x) (insert v A) - value (decode x) A:=by
  simp only [monotoneRow,Rat.cast_sub,sub_mul,Finset.sum_sub_distrib]
  rw [Lax263307Proofs.MomentLP.single_row_value,Lax263307Proofs.MomentLP.single_row_value]

theorem mass_row_value {n r:ℕ} (x:Index n r→ ℝ) (A:Finset (Fin n)) (k:ℕ):
    (∑ j, (massRow A k j:ℝ) * x j) =
      (∑ v,value (decode x) (insert v A)) - (k:ℝ) * value (decode x) A:=by
  simp only [massRow,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast,
    sub_mul,Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Lax263307Proofs.MomentLP.single_row_value]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,Lax263307Proofs.MomentLP.single_row_value]

abbrev Rows (n r:ℕ):=Fin (2 + (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))))

def normalPort {n r:ℕ} (i:Fin 2):Rows n r:=
  Fin.castAdd (dimension n r + (dimension n r + (dimension n r * n + (dimension n r + dimension n r)))) i

def upperPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.castAdd (dimension n r + (dimension n r * n + (dimension n r + dimension n r))) i)

def vanishPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.castAdd (dimension n r * n + (dimension n r + dimension n r)) i))

def monotonePort {n r:ℕ} (i:Index n r) (v:Fin n):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.castAdd (dimension n r + dimension n r) (finProdFinEquiv (i,v)))))

def massPlusPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.castAdd (dimension n r) i))))

def massMinusPort {n r:ℕ} (i:Index n r):Rows n r:=
  Fin.natAdd 2 (Fin.natAdd (dimension n r) (Fin.natAdd (dimension n r)
    (Fin.natAdd (dimension n r * n) (Fin.natAdd (dimension n r) i))))

theorem indexed_value {n r:ℕ} (x:Index n r→ ℝ) (i:Index n r):
    value (decode x) (indexing n r i).val=x i:=by
  rw [value,dif_pos (indexing n r i).property]
  change x ((indexing n r).symm (indexing n r i))=x i
  rw [Equiv.symm_apply_apply]

theorem normal_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Fin 2):
    rowValue (toReal (program G k r)) x (normalPort i) =
      if i=0 then value (decode x) ∅ else -value (decode x) ∅:=by
  unfold rowValue toReal program normalPort
  simp only [Fin.addCases_left]
  by_cases hi:i=0
  · simp only [if_pos hi]
    exact Lax263307Proofs.MomentLP.single_row_value x ∅
  · simp only [if_neg hi,Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
    rw [Lax263307Proofs.MomentLP.single_row_value]

theorem upper_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (upperPort i)=x i:=by
  unfold rowValue toReal program upperPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  rw [Lax263307Proofs.MomentLP.single_row_value,indexed_value]

theorem vanish_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (vanishPort i) =
      if G.IsIndepSet ((indexing n r i).val:Set (Fin n)) then 0 else x i:=by
  unfold rowValue toReal program vanishPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  split_ifs
  · simp
  · rw [Lax263307Proofs.MomentLP.single_row_value,indexed_value]

theorem monotone_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r) (v:Fin n):
    rowValue (toReal (program G k r)) x (monotonePort i v) =
      if (indexing n r i).val.card≤ r + 1 then
        value (decode x) (insert v (indexing n r i).val) - value (decode x) (indexing n r i).val else 0:=by
  unfold rowValue toReal program monotonePort
  simp only [Fin.addCases_left,Fin.addCases_right,Equiv.symm_apply_apply]
  split_ifs
  · exact monotone_row_value x _ v
  · simp

theorem mass_plus_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (massPlusPort i) =
      if (indexing n r i).val.card≤ r + 1 then
        (∑ v,value (decode x) (insert v (indexing n r i).val)) - (k:ℝ) * value (decode x) (indexing n r i).val else 0:=by
  unfold rowValue toReal program massPlusPort
  simp only [Fin.addCases_left,Fin.addCases_right]
  split_ifs
  · exact mass_row_value x _ k
  · simp

theorem mass_minus_row {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ) (i:Index n r):
    rowValue (toReal (program G k r)) x (massMinusPort i) =
      if (indexing n r i).val.card≤ r + 1 then
        -((∑ v,value (decode x) (insert v (indexing n r i).val)) - (k:ℝ) * value (decode x) (indexing n r i).val) else 0:=by
  unfold rowValue toReal program massMinusPort
  simp only [Fin.addCases_right]
  split_ifs
  · simp only [Rat.cast_neg,neg_mul,Finset.sum_neg_distrib]
    rw [mass_row_value]
  · simp

theorem normal_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Fin 2):
    (toReal (program G k r)).b (normalPort i)=if i=0 then 1 else -1:=by
  by_cases hi:i=0 <;> simp [toReal,program,normalPort,hi]

theorem upper_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (upperPort i)=1:=by
  simp only [toReal,program,upperPort,Fin.addCases_left,Fin.addCases_right,Rat.cast_one]

theorem vanish_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (vanishPort i)=0:=by
  simp only [toReal,program,vanishPort,Fin.addCases_right,Rat.cast_zero]

theorem monotone_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r) (v:Fin n):
    (toReal (program G k r)).b (monotonePort i v)=0:=by
  simp only [toReal,program,monotonePort,Fin.addCases_right,Rat.cast_zero]

theorem mass_plus_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (massPlusPort i)=0:=by
  simp only [toReal,program,massPlusPort,Fin.addCases_right,Rat.cast_zero]

theorem mass_minus_rhs {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (i:Index n r):
    (toReal (program G k r)).b (massMinusPort i)=0:=by
  simp only [toReal,program,massMinusPort,Fin.addCases_right,Rat.cast_zero]

theorem primal_characterization {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (x:Index n r→ ℝ):
    PrimalFeasible (toReal (program G k r)) x↔ Lax263307.LinearRelaxation.IsFeasible G k r (decode x):=by
  constructor
  · rintro ⟨hnonnegative,hrows⟩
    have hupper (i:Index n r):x i≤ 1:=by
      have h:=hrows (upperPort i)
      rwa [upper_row,upper_rhs] at h
    exact {
      normalized:=by
        have h0:=hrows (normalPort (0:Fin 2))
        have h1:=hrows (normalPort (1:Fin 2))
        rw [normal_row,normal_rhs] at h0 h1
        norm_num at h0 h1
        linarith
      bounds:=fun A => ⟨hnonnegative ((indexing n r).symm A),hupper ((indexing n r).symm A)⟩
      monotone:=by
        intro A hA v
        let B:Coordinate n r:= ⟨A,by omega⟩
        let i:Index n r:=(indexing n r).symm B
        have hi:(indexing n r i).val=A:=by simp [i,B]
        have h:=hrows (monotonePort i v)
        rw [monotone_row,monotone_rhs,hi,if_pos hA] at h
        exact sub_nonpos.mp h
      vanishes:=by
        intro A hA
        let i:Index n r:=(indexing n r).symm A
        have hi:indexing n r i=A:=Equiv.apply_symm_apply _ _
        have h:=hrows (vanishPort i)
        rw [vanish_row,vanish_rhs,hi,if_neg hA] at h
        exact le_antisymm h (hnonnegative i)
      mass:=by
        intro A hA
        let B:Coordinate n r:= ⟨A,by omega⟩
        let i:Index n r:=(indexing n r).symm B
        have hi:(indexing n r i).val=A:=by simp [i,B]
        have hp:=hrows (massPlusPort i)
        have hm:=hrows (massMinusPort i)
        rw [mass_plus_row,mass_plus_rhs,hi,if_pos hA] at hp
        rw [mass_minus_row,mass_minus_rhs,hi,if_pos hA] at hm
        linarith }
  · intro feasible
    refine ⟨?_, ?_⟩
    · intro i
      simpa [decode] using (feasible.bounds (indexing n r i)).1
    · intro row
      refine Fin.addCases (fun i:Fin 2 => ?_) (fun row => ?_) row
      · change rowValue (toReal (program G k r)) x (normalPort i)≤ (toReal (program G k r)).b (normalPort i)
        rw [normal_row,normal_rhs,feasible.normalized]
      · refine Fin.addCases (fun i:Index n r => ?_) (fun row => ?_) row
        · change rowValue (toReal (program G k r)) x (upperPort i)≤ (toReal (program G k r)).b (upperPort i)
          rw [upper_row,upper_rhs]
          simpa [decode] using (feasible.bounds (indexing n r i)).2
        · refine Fin.addCases (fun i:Index n r => ?_) (fun row => ?_) row
          · change rowValue (toReal (program G k r)) x (vanishPort i)≤ (toReal (program G k r)).b (vanishPort i)
            rw [vanish_row,vanish_rhs]
            by_cases hI:G.IsIndepSet ((indexing n r i).val:Set (Fin n))
            · simp [hI]
            · have hzero:x i=0:=by simpa [decode] using feasible.vanishes (indexing n r i) hI
              simp [hI,hzero]
          · refine Fin.addCases (fun j:Fin (dimension n r * n) => ?_) (fun row => ?_) row
            · obtain ⟨⟨i,v⟩,rfl⟩:=(finProdFinEquiv:Index n r × Fin n ≃ Fin (dimension n r * n)).surjective j
              change rowValue (toReal (program G k r)) x (monotonePort i v)≤ (toReal (program G k r)).b (monotonePort i v)
              rw [monotone_row,monotone_rhs]
              by_cases hi:(indexing n r i).val.card≤ r + 1
              · rw [if_pos hi]
                exact sub_nonpos.mpr (feasible.monotone _ hi v)
              · simp [hi]
            · refine Fin.addCases (fun i:Index n r => ?_) (fun i:Index n r => ?_) row
              · change rowValue (toReal (program G k r)) x (massPlusPort i)≤ (toReal (program G k r)).b (massPlusPort i)
                rw [mass_plus_row,mass_plus_rhs]
                by_cases hi:(indexing n r i).val.card≤ r + 1
                · rw [if_pos hi,feasible.mass _ hi]
                  simp
                · simp [hi]
              · change rowValue (toReal (program G k r)) x (massMinusPort i)≤ (toReal (program G k r)).b (massMinusPort i)
                rw [mass_minus_row,mass_minus_rhs]
                by_cases hi:(indexing n r i).val.card≤ r + 1
                · rw [if_pos hi,feasible.mass _ hi]
                  simp
                · simp [hi]

end Lax263307Proofs.MomentLP

end

section

namespace Lax263307Proofs.DistanceProjection

open Lax109476.LinearProgram Lax263307.DistanceProjection

theorem old_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin m):
    rowValue (distanceProgram P center) z (Fin.castAdd (n + n) i)=rowValue P (point z) i:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left]
  rw [Fin.sum_univ_add]
  simp [point]

theorem plus_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin n):
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.castAdd n i))=point z i - distance z:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_left,Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point,distance,sub_eq_add_neg]

theorem minus_row {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (i:Fin n):
    rowValue (distanceProgram P center) z (Fin.natAdd m (Fin.natAdd n i))=-point z i - distance z:=by
  unfold rowValue distanceProgram
  simp only [Fin.addCases_right]
  rw [Fin.sum_univ_add]
  simp [point,distance,sub_eq_add_neg]

theorem primal_characterization {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ):
    PrimalFeasible (distanceProgram P center) z↔
      PrimalFeasible P (point z)∧ 0≤ distance z∧
        ∀ j, |point z j - center j|≤ distance z:=by
  constructor
  · rintro ⟨hnonneg,hrows⟩
    refine ⟨⟨fun j => hnonneg (Fin.castAdd 1 j),fun i => ?_⟩,
      hnonneg (Fin.natAdd n (0:Fin 1)),fun j => ?_⟩
    · have h:=hrows (Fin.castAdd (n + n) i)
      rw [old_row] at h
      simpa only [distanceProgram,Fin.addCases_left] using h
    · have hplus:=hrows (Fin.natAdd m (Fin.castAdd n j))
      have hminus:=hrows (Fin.natAdd m (Fin.natAdd n j))
      rw [plus_row] at hplus
      rw [minus_row] at hminus
      simp only [distanceProgram,Fin.addCases_left,Fin.addCases_right] at hplus hminus
      exact abs_le.mpr ⟨by linarith,by linarith⟩
  · rintro ⟨⟨hnonneg,hrows⟩,ht,hnear⟩
    constructor
    · intro j
      refine Fin.addCases (fun j => hnonneg j) (fun j => ?_) j
      have hj:j=0:=Fin.eq_zero j
      subst j
      exact ht
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [old_row]
        simpa only [distanceProgram,Fin.addCases_left] using hrows i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · rw [plus_row]
          simp only [distanceProgram,Fin.addCases_left,Fin.addCases_right]
          have h:=(abs_le.mp (hnear j)).2
          linarith
        · rw [minus_row]
          simp only [distanceProgram,Fin.addCases_right]
          have h:=(abs_le.mp (hnear j)).1
          linarith

theorem objective_value {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ):
    primalValue (distanceProgram P center) z=-distance z:=by
  unfold primalValue distanceProgram
  rw [Fin.sum_univ_add]
  simp [distance]

theorem objective_bounded {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ):
    IsBoundedAbove (distanceProgram P center):=by
  refine ⟨0,fun z hz => ?_⟩
  rw [objective_value]
  exact neg_nonpos.mpr ((primal_characterization P center z).mp hz).2.1

theorem projection_feasible_iff {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ):
    IsFeasible (distanceProgram P center)↔ IsFeasible P:=by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨point z, ((primal_characterization P center z).mp hz).1⟩
  · rintro ⟨y,hy⟩
    let t:= ∑ j, |y j - center j|
    let z:Fin (n + 1)→ ℝ:=Fin.addCases y (fun _:Fin 1 => t)
    refine ⟨z, (primal_characterization P center z).mpr ?_⟩
    have hpoint:point z=y:=by funext j; simp [point,z]
    have hdist:distance z=t:=by simp [distance,z]
    rw [hpoint,hdist]
    refine ⟨hy,Finset.sum_nonneg (fun j _ => abs_nonneg _), ?_⟩
    intro j
    exact Finset.single_le_sum (fun j _ => abs_nonneg (y j - center j)) (Finset.mem_univ j)

theorem point_column {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ) (j:Fin n):
    columnValue (distanceProgram P center) dual (Fin.castAdd 1 j) =
      columnValue P (oldMultipliers dual) j - normal dual j:=by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  simp [oldMultipliers,plusMultipliers,minusMultipliers,normal]
  ring

theorem distance_column {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ):
    columnValue (distanceProgram P center) dual (Fin.natAdd n (0:Fin 1)) =
      -(∑ j,plusMultipliers dual j) - ∑ j,minusMultipliers dual j:=by
  unfold columnValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  simp [plusMultipliers,minusMultipliers,Finset.sum_neg_distrib]
  ring

theorem dual_objective {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ):
    dualValue (distanceProgram P center) dual=dualValue P (oldMultipliers dual) - ∑ j,normal dual j * center j:=by
  unfold dualValue distanceProgram
  rw [Fin.sum_univ_add,Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,neg_mul,Finset.sum_neg_distrib]
  simp only [oldMultipliers,normal,minusMultipliers,plusMultipliers,sub_mul,Finset.sum_sub_distrib]
  have hcomm:(∑ j,center j * dual (Fin.natAdd m (Fin.castAdd n j))) =
      ∑ j,dual (Fin.natAdd m (Fin.castAdd n j)) * center j:=by apply Finset.sum_congr rfl; intro j _; ring
  have hcomm':(∑ j,center j * dual (Fin.natAdd m (Fin.natAdd n j))) =
      ∑ j,dual (Fin.natAdd m (Fin.natAdd n j)) * center j:=by apply Finset.sum_congr rfl; intro j _; ring
  rw [hcomm,hcomm']
  ring

theorem dual_normal {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (dual:Fin (m + (n + n))→ ℝ) (feasible:DualFeasible (distanceProgram P center) dual):
    (∑ j, |normal dual j|)≤ 1∧
      ∀ z,PrimalFeasible P z→ (∑ j,normal dual j * z j)≤ dualValue P (oldMultipliers dual):=by
  have hplus (j:Fin n):0≤ plusMultipliers dual j:=feasible.1 _
  have hminus (j:Fin n):0≤ minusMultipliers dual j:=feasible.1 _
  have hmass:(∑ j,plusMultipliers dual j) + (∑ j,minusMultipliers dual j)≤ 1:=by
    have h:=feasible.2 (Fin.natAdd n (0:Fin 1))
    rw [distance_column] at h
    simp only [distanceProgram,Fin.addCases_right] at h
    linarith
  constructor
  · have h:=Finset.sum_le_sum (fun j (_:j∈ (Finset.univ:Finset (Fin n))) =>
      show |normal dual j|≤ plusMultipliers dual j + minusMultipliers dual j from by
        unfold normal
        exact abs_le.mpr ⟨by linarith [hplus j,hminus j],by linarith [hplus j,hminus j]⟩)
    rw [Finset.sum_add_distrib] at h
    exact h.trans hmass
  · intro z hz
    have hcol (j:Fin n):normal dual j≤ columnValue P (oldMultipliers dual) j:=by
      have h:=feasible.2 (Fin.castAdd 1 j)
      rw [point_column] at h
      simp only [distanceProgram,Fin.addCases_left] at h
      linarith
    calc
      _≤ ∑ j,columnValue P (oldMultipliers dual) j * z j:=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hz.1 j))
      _=∑ i,oldMultipliers dual i * rowValue P z i:=by
        unfold columnValue rowValue
        simp_rw [Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _≤ dualValue P (oldMultipliers dual):=
        Finset.sum_le_sum (fun i _ => by
          have hnonnegative:0≤ oldMultipliers dual i:=feasible.1 _
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz.2 i) hnonnegative)

theorem optimal_gap {m n:ℕ} (P:Program ℝ m n) (center:Fin n→ ℝ)
    (z:Fin (n + 1)→ ℝ) (dual:Fin (m + (n + n))→ ℝ)
    (primal:PrimalFeasible (distanceProgram P center) z)
    (dual_feasible:DualFeasible (distanceProgram P center) dual)
    (matching:primalValue (distanceProgram P center) z=dualValue (distanceProgram P center) dual):
    PrimalFeasible P (point z)∧ 0≤ distance z∧
      (∀ j, |point z j - center j|≤ distance z)∧
      (∑ j, |normal dual j|)≤ 1∧
      (∀ y,PrimalFeasible P y→ (∑ j,normal dual j * y j)≤ dualValue P (oldMultipliers dual))∧
      (∑ j,normal dual j * center j) - dualValue P (oldMultipliers dual)=distance z:=by
  obtain ⟨hpoint,hdist,hnear⟩:=(primal_characterization P center z).mp primal
  obtain ⟨hl1,hvalid⟩:=Lax263307Proofs.DistanceProjection.dual_normal P center dual dual_feasible
  refine ⟨hpoint,hdist,hnear,hl1,hvalid, ?_⟩
  rw [objective_value,dual_objective] at matching
  linarith

end Lax263307Proofs.DistanceProjection

end

section

namespace Lax263307Proofs.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax263307.DistanceProjection

theorem cast_row {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (i:Fin m):
    rowValue (toReal P) (realVector x) i=((rowValue P x i:ℚ):ℝ):=by
  unfold rowValue toReal realVector
  push_cast
  rfl

theorem cast_column {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ) (j:Fin n):
    columnValue (toReal P) (realVector x) j=((columnValue P x j:ℚ):ℝ):=by
  unfold columnValue toReal realVector
  push_cast
  rfl

theorem cast_primal_value {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ):
    primalValue (toReal P) (realVector x)=((primalValue P x:ℚ):ℝ):=by
  unfold primalValue toReal realVector
  push_cast
  rfl

theorem cast_dual_value {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ):
    dualValue (toReal P) (realVector x)=((dualValue P x:ℚ):ℝ):=by
  unfold dualValue toReal realVector
  push_cast
  rfl

theorem primal_transfer {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (feasible:PrimalFeasible P x):
    PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℝ)
    exact_mod_cast feasible.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i:ℚ):ℝ)≤ (P.b i:ℝ)
    exact_mod_cast feasible.2 i

theorem dual_transfer {m n:ℕ} (P:Program ℚ m n) (x:Fin m→ ℚ) (feasible:DualFeasible P x):
    DualFeasible (toReal P) (realVector x):=by
  constructor
  · intro i
    change (0:ℝ)≤ (x i:ℝ)
    exact_mod_cast feasible.1 i
  · intro j
    rw [cast_column]
    change (P.c j:ℝ)≤ ((columnValue P x j:ℚ):ℝ)
    exact_mod_cast feasible.2 j

theorem distance_cast {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ):
    toReal (distanceProgram P center)=distanceProgram (toReal P) (realVector center):=by
  unfold toReal distanceProgram
  congr 1
  · funext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
      · simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> first | rfl | simp [apply_ite]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> first | rfl | simp [apply_ite]
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> (simp only [Fin.addCases_left,Fin.addCases_right]; simp [realVector])
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> norm_num

theorem normal_cast {m n:ℕ} (dual:Fin (m + (n + n))→ ℚ):
    normal (realVector dual)=fun j => ((normal dual j:ℚ):ℝ):=by
  funext j
  simp [normal,plusMultipliers,minusMultipliers,realVector]

theorem classify_correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ)
    (certificate:Certificate (m + (n + n)) (n + 1))
    (valid:IsValidCertificate (distanceProgram P center) certificate):
    Lax263307.RationalProjection.Correct P center ρ
      (Lax263307.RationalProjection.classify P ρ certificate):=by
  cases certificate with
  | optimal z dual =>
    obtain ⟨primal,dual_feasible,matching⟩:=valid
    have hp:=primal_transfer (distanceProgram P center) z primal
    have hd:=dual_transfer (distanceProgram P center) dual dual_feasible
    rw [distance_cast] at hp hd
    have hm:primalValue (distanceProgram (toReal P) (realVector center)) (realVector z) =
        dualValue (distanceProgram (toReal P) (realVector center)) (realVector dual):=by
      rw [← distance_cast,cast_primal_value,cast_dual_value,matching]
    have hg:=Lax263307Proofs.DistanceProjection.optimal_gap
      (toReal P) (realVector center) (realVector z) (realVector dual) hp hd hm
    have hdistance:distance (realVector z)=((distance z:ℚ):ℝ):=rfl
    have hpoint:point (realVector z)=realVector (point z):=rfl
    have hold:oldMultipliers (realVector dual)=realVector (oldMultipliers dual):=rfl
    simp only [Lax263307.RationalProjection.classify]
    split_ifs with hnear
    · change PrimalFeasible (toReal P) (realVector (point z))∧ _
      refine ⟨by simpa only [hpoint] using hg.1, ?_⟩
      intro j
      have hdist:((distance z:ℚ):ℝ)≤ (ρ:ℝ):=by exact_mod_cast hnear
      exact (hg.2.2.1 j).trans hdist
    · change (∑ j, |((normal dual j:ℚ):ℝ)|)≤ 1∧ _
      have hfar:(ρ:ℝ) < ((distance z:ℚ):ℝ):=by
        exact_mod_cast (lt_of_not_ge hnear)
      have hgap:=hg.2.2.2.2.2
      rw [normal_cast,hold,cast_dual_value,hdistance] at hgap
      refine ⟨?_, ?_, ?_⟩
      · simpa only [normal_cast] using hg.2.2.2.1
      · simpa only [normal_cast,hold,cast_dual_value] using hg.2.2.2.2.1
      · simpa only [← hgap,realVector] using hfar
  | infeasible dual =>
    have hbad:=Lax109476Proofs.Certificates.certificate_soundness _ _
      (distanceProgram P center) (.infeasible dual) valid
    change ¬ IsFeasible (toReal (distanceProgram P center)) at hbad
    rw [distance_cast,Lax263307Proofs.DistanceProjection.projection_feasible_iff] at hbad
    exact hbad
  | unbounded z direction =>
    have hbad:=Lax109476Proofs.Certificates.certificate_soundness _ _
      (distanceProgram P center) (.unbounded z direction) valid
    change IsFeasible (toReal (distanceProgram P center))∧
      ¬ IsBoundedAbove (toReal (distanceProgram P center)) at hbad
    rw [distance_cast] at hbad
    exact False.elim (hbad.2 (Lax263307Proofs.DistanceProjection.objective_bounded
      (toReal P) (realVector center)))

end Lax263307Proofs.RationalProjection

end

section

namespace Lax263307Proofs.NativeRationalBounds

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem negate (M:ℕ) (q:ℚ) (hq:Bounded M q):Bounded M (-q):=by
  simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq

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

theorem subtract (M:ℕ) (a b:ℚ) (ha:Bounded M a) (hb:Bounded M b):
    Bounded (2*M^2) (a-b):=by
  simpa only [sub_eq_add_neg] using add M a (-b) ha (negate M b hb)

end Lax263307Proofs.NativeRationalBounds

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem adjacency_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:
    (adjacency G).length=n*n:=by
  simp [adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const]

open Lax109476Proofs

end Lax263307Proofs.NativeWeightReduction

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

theorem flattened_coordinate {α:Type*} (xs:List (List α)) (i:ℕ) (hi:i< xs.length)
    (j:ℕ) (hj:j< xs[i].length):
    xs.flatten[((xs.take i).map List.length).sum+j]?=some xs[i][j]:=by
  have he:xs=xs.take i++xs[i]::xs.drop (i+1):=by
    rw [← List.drop_eq_getElem_cons hi,List.take_append_drop]
  have hf:xs.flatten=(xs.take i).flatten++xs[i]++(xs.drop (i+1)).flatten:=by
    conv_lhs => rw [he]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
  rw [hf,List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_flatten]; omega)]
  rw [List.length_flatten]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

theorem matrix_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (i j:Fin n):
    (matrix f)[i.val*n+j.val]?=some (f i j):=by
  let xs:=List.ofFn fun i => List.ofFn (f i)
  have hi:i.val< xs.length:=by simpa only [xs,List.length_ofFn] using i.isLt
  have hj:j.val< xs[i.val].length:=by simpa only [xs,List.getElem_ofFn,List.length_ofFn] using j.isLt
  have hx:=flattened_coordinate xs i.val hi j.val hj
  have hp:((xs.take i.val).map List.length).sum=i.val*n:=by
    rw [List.map_take]
    have hm:xs.map List.length=List.replicate n n:=by
      dsimp only [xs]
      rw [List.map_ofFn,←List.ofFn_const]
      congr 1
      funext v
      exact List.length_ofFn
    rw [hm]
    simp [List.take_replicate,List.sum_replicate]
  simpa only [hp,matrix,xs,List.getElem_ofFn] using hx

def row {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val/n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact (Nat.div_lt_iff_lt_mul hn).mpr q.isLt⟩

def col {n:ℕ} (q:Fin (n*n)):Fin n:= ⟨q.val%n,by
  have hn:0< n:=by nlinarith only [q.isLt]
  exact Nat.mod_lt _ hn⟩

theorem matrix_flat_coordinate {n:ℕ} (f:Fin n→ Fin n→ ℕ) (q:Fin (n*n)):
    (matrix f)[q.val]?=some (f (row q) (col q)):=by
  have hx:=matrix_coordinate f (row q) (col q)
  have he:(row q).val*n+(col q).val=q.val:=by
    simpa only [row,col,Nat.mul_comm] using Nat.div_add_mod q.val n
  rwa [he] at hx

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

open Lax109476Proofs

end Lax263307Proofs.NativeBlowUp

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def select {α:Type*}:ℕ→ List α→ ℕ→ List α
  | 0,_,_ => []
  | _+1, [],_ => []
  | k+1,a::xs,q =>
      if q< xs.length.choose (k+1) then select (k+1) xs q
      else a::select k xs (q-xs.length.choose (k+1))

theorem select_correct {α:Type*} (xs:List α) (k q:ℕ)
    (hq:q< xs.length.choose k):(xs.sublistsLen k)[q]?=some (select k xs q):=by
  induction xs generalizing k q with
  | nil =>
    cases k with
    | zero =>
      have:q=0:=by simpa using hq
      subst q
      simp [select]
    | succ k => simp at hq
  | cons a xs ih =>
    cases k with
    | zero =>
      have:q=0:=by simpa using hq
      subst q
      simp [select]
    | succ k =>
      rw [List.sublistsLen_succ_cons]
      by_cases hh:q< xs.length.choose (k+1)
      · rw [List.getElem?_append_left (by rwa [List.length_sublistsLen])]
        simpa only [select,if_pos hh] using ih (k+1) q hh
      · rw [List.getElem?_append_right (by rw [List.length_sublistsLen]; omega)]
        rw [List.length_sublistsLen,List.getElem?_map]
        have hrem:q-xs.length.choose (k+1)< xs.length.choose k:=by
          simp only [List.length_cons,Nat.choose_succ_succ,Nat.succ_eq_add_one] at hq
          omega
        rw [ih k _ hrem]
        simp only [Option.map_some,select,if_neg hh]

def table (n k:ℕ):List ℕ:=
  (List.ofFn fun i:Fin (n+1) => List.ofFn fun j:Fin (k+1) => i.val.choose j.val).flatten

theorem table_length (n k:ℕ):(table n k).length=(n+1)*(k+1):=by
  simp [table,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]
  ring

theorem table_coordinate (n k i j:ℕ) (hi:i≤ n) (hj:j≤ k):
    (table n k)[i*(k+1)+j]?=some (i.choose j):=by
  let xs:=List.ofFn fun i:Fin (n+1) => List.ofFn fun j:Fin (k+1) => i.val.choose j.val
  have hi':i< xs.length:=by simp only [xs,List.length_ofFn]; omega
  have hj':j< xs[i].length:=by simp only [xs,List.getElem_ofFn,List.length_ofFn]; omega
  have hh:=NativeBlowUp.flattened_coordinate xs i hi' j hj'
  have hm:xs.map List.length=List.replicate (n+1) (k+1):=by
    dsimp only [xs]
    rw [List.map_ofFn,←List.ofFn_const]
    congr 1
    funext i
    exact List.length_ofFn
  have hp:((xs.take i).map List.length).sum=i*(k+1):=by
    rw [List.map_take,hm]
    simp [List.take_replicate,List.sum_replicate,Nat.min_eq_left (by omega:i≤ n+1)]
  simpa only [table,xs,hp,List.getElem_ofFn] using hh

theorem coordinates_spec (B q d:ℕ) (_hd:0< d) (hq:q< B) (hdB:d< B):
    Spec B (fun σ => σ.vars "choose.i"=q∧ σ.vars "choose.cols"=d) coordinates
      (fun _ τ => τ.vars "choose.row"=q/d∧ τ.vars "choose.col"=q%d) 10:=by
  have hquot:q/d< B:=(Nat.div_le_self _ _).trans_lt hq
  have hmul:q/d*d< B:=(Nat.div_mul_le_self _ _).trans_lt hq
  have hrem:q-q/d*d< B:=(Nat.sub_le _ _).trans_lt hq
  rintro σ ⟨hσq,hσd⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 q d; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) q d; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.row") c1) (@Eq Nat (Env.vars τ "choose.col") c2)) σ; let c4:Nat:=c0 (Env.vars σ "choose.i") (Env.vars σ "choose.cols"); let c5:Env:=Env.setVar σ "choose.row" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "choose.i"; let c8:Nat:=c6 "choose.row"; let c9:Nat:=c6 "choose.cols"; let c10:Nat:=Nat.mul c8 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10; let c12:Env:=Env.setVar c5 "choose.col" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols"))); let c16:Expr:=Expr.sub (Expr.var "choose.i") (Expr.mul (Expr.var "choose.row") (Expr.var "choose.cols")); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B coordinates σ σ' ((10:Nat))) (c3 σ')) c12 (@And.intro (Run B coordinates σ c12 ((10:Nat))) (c3 c12) (RunStep.mono B coordinates σ c12 (c13 c15 c17) ((10:Nat)) (RunStep.seq B (Com.assign "choose.row" (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols"))) (Com.assign "choose.col" c16) σ c5 c12 c15 c17 (RunStep.assign B σ "choose.row" (Expr.div (Expr.var "choose.i") (Expr.var "choose.cols")) c4 (RunStep.eval_div B σ (Expr.var "choose.i") (Expr.var "choose.cols") (Env.vars σ "choose.i") (Env.vars σ "choose.cols") (RunStep.eval_var B σ "choose.i" (?nAX_g7913_0_0_0)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7913_0_0_1)) ?_)) (RunStep.assign B c5 "choose.col" c16 c11 (RunStep.eval_sub B c5 (Expr.var "choose.i") (Expr.mul (Expr.var "choose.row") (Expr.var "choose.cols")) c7 c10 (RunStep.eval_var B c5 "choose.i" (?nAX_g7913_0_0_2)) (RunStep.eval_mul B c5 (Expr.var "choose.row") (Expr.var "choose.cols") c8 c9 (RunStep.eval_var B c5 "choose.row" ?_) (RunStep.eval_var B c5 "choose.cols" (?nAX_g7913_0_0_3)) ?_) (?nAX_g7913_0_0_4)))) (?nAX_g7913_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7913_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7913_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]

theorem entry_spec (B n k i j:ℕ) (hi:i≤ n) (hj:j≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.row"=i∧ σ.vars "choose.col"=j∧ σ.vars "choose.cols"=k+1∧
      Prefix ((table n k).take (i*(k+1)+j)) "choose.table" σ) entry
      (fun _ τ => τ.vars "choose.value"=i.choose j) 30:=by
  rintro σ ⟨hrow,hcol,hcols,hprefix⟩
  have hzero:0< B:=by omega
  have hone:1< B:=by omega
  have hiB:i< B:=by omega
  have hjB:j< B:=by omega
  have hkB:k+1< B:=by omega
  by_cases hj0:j=0
  · subst j
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i (Env.vars σ "choose.col"))) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_0_0_0)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_1)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_0_0_2)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" hjB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_0_0_4)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_0_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_0_0_6)) (?nAX_g7914_0_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_0_0_10)) (?nAX_g7914_0_0_11)) (?nAX_g7914_0_0_12) (?nAX_g7914_0_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_0_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_0_0_15)) (?nAX_g7914_0_0_16)) (?nAX_g7914_0_0_17) (?nAX_g7914_0_0_18)) (?nAX_g7914_0_0_19)))))) (?nAX_g7914_0_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · by_cases hi0:i=0
    · subst i
      have hchoose:Nat.choose 0 j=0:=Nat.choose_eq_zero_of_lt (by omega)
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose (Env.vars σ "choose.row") j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:Nat→ Nat→ Nat:= @List.getD Nat (Env.arrs c33 "choose.table"); let c35:String→ Nat:=Env.vars c33; let c36:Nat:=c35 "choose.prev"; let c37:Nat→ Nat:=c5 c36; let c38:Nat:=c35 "choose.col"; let c39:Nat:=c30 c38 ((1:Nat)); let c40:Nat:=c37 c39; let c41:Nat:=c34 c40 ((0:Nat)); let c42:Nat:=c37 c38; let c43:Nat:=c34 c42 ((0:Nat)); let c44:Nat:=c5 c41 c43; let c45:Env:=Env.setVar c33 "choose.value" c44; let c46:Nat:=c6 (Expr.size c14); let c47:Nat:=c6 (Expr.size c20); let c48:Nat:=c5 c46 c47; let c49:Nat:=c27 c48; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_1_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_1_0_3)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c45 (@And.intro (Run B entry σ c45 ((30:Nat))) (c2 c45) (RunStep.mono B entry σ c45 (c8 c49) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c45 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c45 c48 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c45 c46 c47 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" hiB) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_1_0_5)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_1_0_6)) (?nAX_g7914_1_0_7))) (RunStep.assign B c33 "choose.value" c20 c44 (RunStep.eval_add B c33 c18 c19 c41 c43 (RunStep.eval_get B c33 "choose.table" c17 c40 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c36 c39 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_8)) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c38 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_9)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_1_0_10)) (?nAX_g7914_1_0_11)) (?nAX_g7914_1_0_12) (?nAX_g7914_1_0_13)) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c42 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c36 c38 (RunStep.eval_var B c33 "choose.prev" (?nAX_g7914_1_0_14)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_1_0_15)) (?nAX_g7914_1_0_16)) (?nAX_g7914_1_0_17) (?nAX_g7914_1_0_18)) (?nAX_g7914_1_0_19)))))) (?nAX_g7914_1_0_20)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]
    · have hjp:0< j:=by omega
      have hip:0 < i:=by omega
      have hrec:i.choose j=(i-1).choose (j-1)+(i-1).choose j:=by
        obtain ⟨i',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hi0
        obtain ⟨j',rfl⟩:=Nat.exists_eq_succ_of_ne_zero hj0
        simp [Nat.choose_succ_succ]
      have hlast:i*(k+1)+j<(table n k).length:=by rw [table_length]; nlinarith only [hi,hj]
      have hidx0:(i-1)*(k+1)+(j-1)< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        have hsubj:j-1+1=j:=by omega
        nlinarith only [hsubi,hsubj]
      have hidx1:(i-1)*(k+1)+j< i*(k+1)+j:=by
        have hsubi:i-1+1=i:=by omega
        nlinarith only [hsubi]
      have get (a b:ℕ) (ha:a≤ n) (hb:b≤ k) (hlt:a*(k+1)+b< i*(k+1)+j):
          (σ.arrs "choose.table")[a*(k+1)+b]?=some (a.choose b):=by
        have hp:=hprefix (a*(k+1)+b) (by rw [List.length_take]; omega)
        rw [List.getElem_take] at hp
        have hc:=table_coordinate n k a b ha hb
        rw [List.getElem?_eq_getElem (hlt.trans hlast)] at hc
        exact hp.trans hc
      have hget0:=get (i-1) (j-1) (by omega) (by omega) hidx0
      have hget1:=get (i-1) j (by omega) hj hidx1
      have hroom0:(i-1)*(k+1)+(j-1)<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget0
        contradiction
      have hroom1:(i-1)*(k+1)+j<(σ.arrs "choose.table").length:=by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget1
        contradiction
      have hc0:=hcoeff (i-1) (by omega) (j-1) (by omega)
      have hc1:=hcoeff (i-1) (by omega) j hj
      have hsum:(i-1).choose (j-1)+(i-1).choose j< B:=hrec ▸ hcoeff i hi j hj
      have hdim:(table n k).length< B:=by rw [table_length]; omega
      have hprev:(i-1)*(k+1)< B:=by omega
      have hb0:(i-1)*(k+1)+(j-1)< B:=(hidx0.trans hlast).trans hdim
      have hb1:(i-1)*(k+1)+j< B:=(hidx1.trans hlast).trans hdim
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "choose.col") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "choose.value") (Nat.choose i j)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B entry σ σ' ((30:Nat))) (c2 σ'); let c4:Env:=Env.setVar σ "choose.value" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "choose.col") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Com:=Com.assign "choose.value" (Expr.lit ((1:Nat))); let c11:Cond:=Cond.eq (Expr.var "choose.row") (Expr.lit ((0:Nat))); let c12:Com:=Com.assign "choose.value" (Expr.lit ((0:Nat))); let c13:Expr:=Expr.sub (Expr.var "choose.row") (Expr.lit ((1:Nat))); let c14:Expr:=Expr.mul c13 (Expr.var "choose.cols"); let c15:Com:=Com.assign "choose.prev" c14; let c16:Expr:=Expr.sub (Expr.var "choose.col") (Expr.lit ((1:Nat))); let c17:Expr:=Expr.add (Expr.var "choose.prev") c16; let c18:Expr:=Expr.get "choose.table" c17; let c19:Expr:=Expr.get "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")); let c20:Expr:=Expr.add c18 c19; let c21:Com:=Com.assign "choose.value" c20; let c22:Com:=Com.seq c15 c21; let c23:Com:=Com.ite c11 c12 c22; let c24:Prop:= @Eq Nat (Env.vars σ "choose.row") ((0:Nat)); let c25:Prop:=Not c24; let c26:Env:=Env.setVar σ "choose.value" ((0:Nat)); let c27:Nat→ Nat:=c5 (c6 (Cond.size c11)); let c28:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c27 c28; let c30:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c31:Nat:=c30 (Env.vars σ "choose.row") ((1:Nat)); let c32:Nat:=Nat.mul c31 (Env.vars σ "choose.cols"); let c33:Env:=Env.setVar σ "choose.prev" c32; let c34:List Nat:=Env.arrs c33 "choose.table"; let c35:Nat→ Nat→ Nat:= @List.getD Nat c34; let c36:String→ Nat:=Env.vars c33; let c37:Nat:=c36 "choose.prev"; let c38:Nat→ Nat:=c5 c37; let c39:Nat:=c36 "choose.col"; let c40:Nat:=c30 c39 ((1:Nat)); let c41:Nat:=c38 c40; let c42:Nat:=c35 c41 ((0:Nat)); let c43:Nat:=c38 c39; let c44:Nat:=c35 c43 ((0:Nat)); let c45:Nat:=c5 c42 c44; let c46:Env:=Env.setVar c33 "choose.value" c45; let c47:Nat:=c6 (Expr.size c14); let c48:Nat:=c6 (Expr.size c20); let c49:Nat:=c5 c47 c48; let c50:Nat:=c27 c49; let c51:Nat→ Prop:=Nat.lt c41; let c52:Nat:= @List.length Nat c34; let c53:Nat→ Prop:=Nat.lt c43; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c4 (@And.intro (Run B entry σ c4 ((30:Nat))) (c2 c4) (RunStep.mono B entry σ c4 (c8 c9) ((30:Nat)) (RunStep.ite_true B c7 c10 c23 σ c4 c9 (RunStep.cond_eq_true B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.assign B σ "choose.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ hone))) (?nAX_g7914_2_0_1)) ?_)) fun (hcase:c1) => @Or.casesOn c24 c25 (fun (x:Or c24 c25) => @Exists Env c3) (Classical.em c24) (fun (hcase_1:c24) => @Exists.intro Env c3 c26 (@And.intro (Run B entry σ c26 ((30:Nat))) (c2 c26) (RunStep.mono B entry σ c26 (c8 c29) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c26 c29 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_2)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_true B c11 c12 c22 σ c26 c28 (RunStep.cond_eq_true B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_3)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.assign B σ "choose.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hzero)))) (?nAX_g7914_2_0_4)) ?_)) fun (hcase_1:c25) => @Exists.intro Env c3 c46 (@And.intro (Run B entry σ c46 ((30:Nat))) (c2 c46) (RunStep.mono B entry σ c46 (c8 c50) ((30:Nat)) (RunStep.ite_false B c7 c10 c23 σ c46 c50 (RunStep.cond_eq_false B σ (Expr.var "choose.col") (Expr.lit ((0:Nat))) (Env.vars σ "choose.col") ((0:Nat)) (RunStep.eval_var B σ "choose.col" (?nAX_g7914_2_0_5)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase) (RunStep.ite_false B c11 c12 c22 σ c46 c49 (RunStep.cond_eq_false B σ (Expr.var "choose.row") (Expr.lit ((0:Nat))) (Env.vars σ "choose.row") ((0:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_6)) (RunStep.eval_lit B ((0:Nat)) σ hzero) hcase_1) (RunStep.seq B c15 c21 σ c33 c46 c47 c48 (RunStep.assign B σ "choose.prev" c14 c32 (RunStep.eval_mul B σ c13 (Expr.var "choose.cols") c31 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.var "choose.row") (Expr.lit ((1:Nat))) (Env.vars σ "choose.row") ((1:Nat)) (RunStep.eval_var B σ "choose.row" (?nAX_g7914_2_0_7)) (RunStep.eval_lit B ((1:Nat)) σ hone) (?nAX_g7914_2_0_8)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7914_2_0_9)) ?_)) (RunStep.assign B c33 "choose.value" c20 c45 (RunStep.eval_add B c33 c18 c19 c42 c44 (RunStep.eval_get B c33 "choose.table" c17 c41 (RunStep.eval_add B c33 (Expr.var "choose.prev") c16 c37 c40 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_sub B c33 (Expr.var "choose.col") (Expr.lit ((1:Nat))) c39 ((1:Nat)) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_10)) (RunStep.eval_lit B ((1:Nat)) c33 hone) (?nAX_g7914_2_0_11)) ?_) ?_ ?_) (RunStep.eval_get B c33 "choose.table" (Expr.add (Expr.var "choose.prev") (Expr.var "choose.col")) c43 (RunStep.eval_add B c33 (Expr.var "choose.prev") (Expr.var "choose.col") c37 c39 (RunStep.eval_var B c33 "choose.prev" ?_) (RunStep.eval_var B c33 "choose.col" (?nAX_g7914_2_0_12)) ?_) ?_ ?_) ?_))))) (?nAX_g7914_2_0_13)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7914_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7914_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar]

def Invariant (n k:ℕ) (σ:Env):Prop:=
  σ.vars "choose.cols"=k+1∧ σ.vars "choose.length"=(table n k).length∧
  σ.vars "choose.i"≤(table n k).length∧ (table n k).length≤(σ.arrs "choose.table").length∧
  Prefix ((table n k).take (σ.vars "choose.i")) "choose.table" σ

theorem step_spec (B n k:ℕ) (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => Invariant n k σ∧ σ.vars "choose.i"<(table n k).length) step
      (fun σ τ => Invariant n k τ∧ τ.vars "choose.i"=σ.vars "choose.i"+1) 50:=by
  rintro σ ⟨⟨hcols,hlen,hle,hroom,hprefix⟩,hlt⟩
  let q:=σ.vars "choose.i"
  let i:=q/(k+1)
  let j:=q%(k+1)
  have hlen':=table_length n k
  have hq:q<(n+1)*(k+1):=by rwa [←hlen']
  have hi:i≤ n:=by
    have:q/(k+1)< n+1:=(Nat.div_lt_iff_lt_mul (by omega)).mpr hq
    omega
  have hj:j≤ k:=by have hh:=Nat.mod_lt q (by omega:0< k+1); omega
  have hqB:q< B:=by omega
  have heq:i*(k+1)+j=q:=by
    dsimp [i,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod q (k+1)
  obtain ⟨ν,r1,p1⟩:=coordinates_spec B q (k+1) (by omega) hqB (by omega) σ ⟨rfl,hcols⟩
  obtain ⟨μ,r2,p2⟩:=entry_spec B n k i j hi hj hB hcoeff ν
    ⟨p1.1,p1.2,(r1.frame_var "choose.cols" (by decide)).trans hcols,
      by rw [heq]; simpa only [Prefix,r1.frame_arr "choose.table" (by decide)] using hprefix⟩
  have r12:=r1.seq r2
  have hqμ:μ.vars "choose.i"=q:=r12.frame_var "choose.i" (by decide)
  have htlen:((table n k).take q).length=q:=by rw [List.length_take]; omega
  have hvalue:(table n k)[q]=i.choose j:=by
    have hc:=table_coordinate n k i j hi hj
    rw [heq,List.getElem?_eq_getElem hlt] at hc
    exact Option.some.inj hc
  obtain ⟨τ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "choose.table" "choose.i"
    ((table n k).take q) (i.choose j) (.var "choose.value") (by omega) (by rw [htlen]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "choose.table" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨p2.symm,p2 ▸ hcoeff i hi j hj⟩⟩
  have ht:τ.vars "choose.i"=q+1:=by simpa only [htlen] using p3.2
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.cols" (by decide)).trans hcols,
    (rr.frame_var "choose.length" (by decide)).trans hlen,by rw [ht]; omega,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hlt,hvalue]
    exact p3.1

theorem command_spec (B n k:ℕ) (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.k"=k∧
      (n+1)*(k+1)≤(σ.arrs "choose.table").length) command
      (fun _ τ => Prefix (table n k) "choose.table" τ∧ τ.vars "choose.cols"=k+1)
      (54*(n+1)*(k+1)+16):=by
  have hl:=table_length n k
  have hloop:=Spec.forRangeZero "choose.i" "choose.length" (Invariant n k)
    (table n k).length 50 (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (step_spec B n k hB hcoeff)
  have hmeta:Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.k"=k) metadata
      (fun _ τ => τ.vars "choose.cols"=k+1∧ τ.vars "choose.length"=(n+1)*(k+1)) 10:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 k ((1:Nat)); let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=c2 (c0 n ((1:Nat))) c1; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.cols") c1) (@Eq Nat (Env.vars τ "choose.length") c3)) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B metadata σ σ' ((10:Nat))) (c4 σ'); let c6:Nat:=c0 (Env.vars σ "choose.k") ((1:Nat)); let c7:Env:=Env.setVar σ "choose.cols" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "choose.n"; let c10:Nat:=c0 c9 ((1:Nat)); let c11:Nat:=c8 "choose.cols"; let c12:Nat:=c2 c10 c11; let c13:Env:=Env.setVar c7 "choose.length" c12; let c14:Nat→ Nat:=c0 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "choose.k") (Expr.lit ((1:Nat))); let c16:Nat:=c14 (Expr.size c15); let c17:Expr:=Expr.add (Expr.var "choose.n") (Expr.lit ((1:Nat))); let c18:Expr:=Expr.mul c17 (Expr.var "choose.cols"); let c19:Nat:=c14 (Expr.size c18); let c20:String→ Nat:=Env.vars c13; @And.casesOn (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k) (fun (x:And (@Eq Nat (Env.vars σ "choose.n") n) (@Eq Nat (Env.vars σ "choose.k") k)) => @Exists Env c5) a fun (left:@Eq Nat (Env.vars σ "choose.n") n) (right:@Eq Nat (Env.vars σ "choose.k") k) => @Exists.intro Env c5 c13 (@And.intro (Run B metadata σ c13 ((10:Nat))) (c4 c13) (RunStep.mono B metadata σ c13 (c0 c16 c19) ((10:Nat)) (RunStep.seq B (Com.assign "choose.cols" c15) (Com.assign "choose.length" c18) σ c7 c13 c16 c19 (RunStep.assign B σ "choose.cols" c15 c6 (RunStep.eval_add B σ (Expr.var "choose.k") (Expr.lit ((1:Nat))) (Env.vars σ "choose.k") ((1:Nat)) (RunStep.eval_var B σ "choose.k" (?nAX_g7919_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7919_0_0_1)) (?nAX_g7919_0_0_2))) (RunStep.assign B c7 "choose.length" c18 c12 (RunStep.eval_mul B c7 c17 (Expr.var "choose.cols") c10 c11 (RunStep.eval_add B c7 (Expr.var "choose.n") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "choose.n" (?nAX_g7919_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c7 (?nAX_g7919_0_0_4)) (?nAX_g7919_0_0_5)) (RunStep.eval_var B c7 "choose.cols" (?nAX_g7919_0_0_6)) ?_))) (?nAX_g7919_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7919_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7919_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
    all_goals omega
  rintro σ ⟨hn,hk,hroom⟩
  obtain ⟨ν,r1,p1⟩:=hmeta σ ⟨hn,hk⟩
  have hi:Invariant n k (ν.setVar "choose.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using p1.1
    · simpa only [vars_setVar,String.reduceEq,if_false,hl] using p1.2
    · rw [arrs_setVar,Lax455465Proofs.RamFrames.run_array_length r1,hl]
      exact hroom
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by rw [hl]; nlinarith),?_,p2.1.1⟩
  simpa only [p2.2,List.take_length] using p2.1.2.2.2.2

def bits:ℕ→ ℕ→ ℕ→ List ℕ
  | 0,_,_ => []
  | n+1,0,q => 0::bits n 0 q
  | n+1,k+1,q => if q< n.choose (k+1) then 0::bits n (k+1) q
      else 1::bits n k (q-n.choose (k+1))

theorem bits_length (n k q:ℕ):(bits n k q).length=n:=by
  induction n generalizing k q with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => simp [bits,ih]
    | succ k => simp only [bits]; split_ifs <;> simp [ih]

def decode {α:Type*} (xs:List α) (bs:List ℕ):List α:=
  (xs.zip bs).filterMap fun p => if p.2=1 then some p.1 else none

theorem decode_bits {α:Type*} (xs:List α) (k q:ℕ):
    decode xs (bits xs.length k q)=select k xs q:=by
  induction xs generalizing k q with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => simpa [decode,bits,select] using ih 0 q
    | succ k =>
      by_cases hq:q< xs.length.choose (k+1)
      · simpa [decode,bits,select,hq] using ih (k+1) q
      · simpa [decode,bits,select,hq] using congrArg (List.cons a) (ih k (q-xs.length.choose (k+1)))

def advance (remaining need rank:ℕ):ℕ × ℕ × ℕ:=
  if need=0 then (0,need,rank)
  else if rank<(remaining-1).choose need then (0,need,rank)
  else (1,need-1,rank-(remaining-1).choose need)

theorem bits_step (remaining need rank:ℕ) (h:0< remaining):
    bits remaining need rank=(advance remaining need rank).1::
      bits (remaining-1) (advance remaining need rank).2.1 (advance remaining need rank).2.2:=by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  cases need <;> simp [bits,advance]
  split_ifs <;> rfl

theorem advance_bounds (remaining need rank:ℕ):
    (advance remaining need rank).1≤1∧ (advance remaining need rank).2.1≤ need∧
      (advance remaining need rank).2.2≤ rank:=by
  unfold advance
  split_ifs <;> simp

theorem subset_entry_spec (B n k i need rank:ℕ) (hi:i< n) (hneed:need≤ k)
    (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
      σ.vars "subset.i"=i∧ σ.vars "subset.need"=need∧ σ.vars "subset.rank"=rank∧
      Prefix (table n k) "choose.table" σ) subsetEntry
      (fun _ τ => τ.vars "subset.bit"=(advance (n-i) need rank).1∧
        τ.vars "subset.need"=(advance (n-i) need rank).2.1∧
        τ.vars "subset.rank"=(advance (n-i) need rank).2.2) 40:=by
  rintro σ ⟨hn,hcols,hiσ,hneedσ,hrankσ,hprefix⟩
  have hrow:n-i-1≤ n:=by omega
  have hidx:(n-i-1)*(k+1)+need<(table n k).length:=by
    rw [table_length]
    nlinarith only [hrow,hneed]
  have hc:=table_coordinate n k (n-i-1) need hrow hneed
  have hp:=hprefix ((n-i-1)*(k+1)+need) hidx
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget:=hp.trans hc
  have hroom:(n-i-1)*(k+1)+need<(σ.arrs "choose.table").length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    contradiction
  have htableB:(table n k).length< B:=by rw [table_length]; omega
  have hidxB:=hidx.trans htableB
  have hmul:(n-i-1)*(k+1)< B:=by omega
  have hcB:=hcoeff (n-i-1) hrow need hneed
  by_cases hneed0:need=0
  · subst need
    (expose_names;
      (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Prod Nat (Prod Nat Nat):=advance (c2 n i) (Env.vars σ "subset.need") rank; let c4:Nat:= @Prod.fst Nat (Prod Nat Nat) c3; let c5:Prod Nat Nat:= @Prod.snd Nat (Prod Nat Nat) c3; let c6:Nat:= @Prod.fst Nat Nat c5; let c7:Nat:= @Prod.snd Nat Nat c5; let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "subset.bit") c4) (And (@Eq Nat (Env.vars τ "subset.need") c6) (@Eq Nat (Env.vars τ "subset.rank") c7))) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (c8 σ'); let c10:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c17:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c18:Expr:=Expr.mul c17 (Expr.var "choose.cols"); let c19:Expr:=Expr.add c18 (Expr.var "subset.need"); let c20:Expr:=Expr.get "choose.table" c19; let c21:Com:=Com.assign "subset.count" c20; let c22:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c24:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c25:Com:=Com.assign "subset.need" c24; let c26:Com:=Com.seq c23 c25; let c27:Com:=Com.seq c22 c26; let c28:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27; let c29:Com:=Com.seq c21 c28; let c30:String→ Nat:=Env.vars c10; let c31:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c32:Nat:=c2 c31 ((1:Nat)); let c33:Nat:=Nat.mul c32 (Env.vars σ "choose.cols"); let c34:Nat:=c11 c33 (Env.vars σ "subset.need"); let c35:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c34 ((0:Nat)); let c36:Env:=Env.setVar σ "subset.count" c35; let c37:String→ Nat:=Env.vars c36; let c38:Nat:=c37 "subset.rank"; let c39:Nat:=c37 "subset.count"; let c40:Prop:=Nat.lt c38 c39; let c41:Prop:=Not c40; let c42:Nat→ Env:=Env.setVar c36 "subset.bit"; let c43:Env:=c42 ((0:Nat)); let c44:Nat:=c12 (Expr.size c20); let c45:Nat→ Nat:=c11 c44; let c46:Nat→ Nat:=c11 (c12 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c47:Nat:=c46 c15; let c48:Nat:=c45 c47; let c49:String→ Nat:=Env.vars c43; let c50:Env:=c42 ((1:Nat)); let c51:String→ Nat:=Env.vars c50; let c52:Nat:=c51 "subset.rank"; let c53:Nat:=c51 "subset.count"; let c54:Nat:=c2 c52 c53; let c55:Env:=Env.setVar c50 "subset.rank" c54; let c56:Nat:=Env.vars c55 "subset.need"; let c57:Nat:=c2 c56 ((1:Nat)); let c58:Env:=Env.setVar c55 "subset.need" c57; let c59:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c60:Nat:=c12 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c61:Nat:=c12 (Expr.size c24); let c62:Nat:=c11 c60 c61; let c63:Nat:=c11 c59 c62; let c64:Nat:=c46 c63; let c65:Nat:=c45 c64; let c66:String→ Nat:=Env.vars c58; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c9) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c9 c10 (@And.intro (Run B subsetEntry σ c10 ((40:Nat))) (c8 c10) (RunStep.mono B subsetEntry σ c10 (c14 c15) ((40:Nat)) (RunStep.ite_true B c13 c16 c29 σ c10 c15 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_2)))) (?nAX_g7928_0_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c40 c41 (fun (x:Or c40 c41) => @Exists Env c9) (Classical.em c40) (fun (hcase_1:c40) => @Exists.intro Env c9 c43 (@And.intro (Run B subsetEntry σ c43 ((40:Nat))) (c8 c43) (RunStep.mono B subsetEntry σ c43 (c14 c48) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c43 c48 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_5)) hcase) (RunStep.seq B c21 c28 σ c36 c43 c44 c47 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_7)) (?nAX_g7928_0_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_9)) (?nAX_g7928_0_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_11)) (?nAX_g7928_0_0_12)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_13)) (?nAX_g7928_0_0_14)) (?nAX_g7928_0_0_15) (?nAX_g7928_0_0_16))) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c43 c15 (RunStep.cond_lt_true B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_17)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_18)) hcase_1) (RunStep.assign B c36 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c36 (?nAX_g7928_0_0_19)))))) (?nAX_g7928_0_0_20)) ?_)) fun (hcase_1:c41) => @Exists.intro Env c9 c58 (@And.intro (Run B subsetEntry σ c58 ((40:Nat))) (c8 c58) (RunStep.mono B subsetEntry σ c58 (c14 c65) ((40:Nat)) (RunStep.ite_false B c13 c16 c29 σ c58 c65 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_21)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_0_0_22)) hcase) (RunStep.seq B c21 c28 σ c36 c58 c44 c64 (RunStep.assign B σ "subset.count" c20 c35 (RunStep.eval_get B σ "choose.table" c19 c34 (RunStep.eval_add B σ c18 (Expr.var "subset.need") c33 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c17 (Expr.var "choose.cols") c32 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c31 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_0_0_23)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_0_0_24)) (?nAX_g7928_0_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_0_0_26)) (?nAX_g7928_0_0_27)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_0_0_28)) (?nAX_g7928_0_0_29)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_0_0_30)) (?nAX_g7928_0_0_31)) (?nAX_g7928_0_0_32) (?nAX_g7928_0_0_33))) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c16 c27 c36 c58 c63 (RunStep.cond_lt_false B c36 (Expr.var "subset.rank") (Expr.var "subset.count") c38 c39 (RunStep.eval_var B c36 "subset.rank" (?nAX_g7928_0_0_34)) (RunStep.eval_var B c36 "subset.count" (?nAX_g7928_0_0_35)) hcase_1) (RunStep.seq B c22 c26 c36 c50 c58 c59 c62 (RunStep.assign B c36 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c36 (?nAX_g7928_0_0_36))) (RunStep.seq B c23 c25 c50 c55 c58 c60 c61 (RunStep.assign B c50 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c54 (RunStep.eval_sub B c50 (Expr.var "subset.rank") (Expr.var "subset.count") c52 c53 (RunStep.eval_var B c50 "subset.rank" (?nAX_g7928_0_0_37)) (RunStep.eval_var B c50 "subset.count" (?nAX_g7928_0_0_38)) (?nAX_g7928_0_0_39))) (RunStep.assign B c55 "subset.need" c24 c57 (RunStep.eval_sub B c55 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c56 ((1:Nat)) (RunStep.eval_var B c55 "subset.need" (?nAX_g7928_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c55 (?nAX_g7928_0_0_41)) (?nAX_g7928_0_0_42)))))))) (?nAX_g7928_0_0_43)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,advance]
  · by_cases hsmall:rank<(n-i-1).choose need
    · have ha:advance (n-i) need rank=(0,need,rank):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((0:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") need) (@Eq Nat (Env.vars σ' "subset.rank") rank))); let c3:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c4:String→ Nat:=Env.vars c3; let c5:Prop:=And (@Eq Nat (c4 "subset.bit") ((0:Nat))) (And (@Eq Nat (c4 "subset.need") need) (@Eq Nat (c4 "subset.rank") rank)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c12:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c13:Expr:=Expr.mul c12 (Expr.var "choose.cols"); let c14:Expr:=Expr.add c13 (Expr.var "subset.need"); let c15:Expr:=Expr.get "choose.table" c14; let c16:Com:=Com.assign "subset.count" c15; let c17:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c18:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c19:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c20:Com:=Com.assign "subset.need" c19; let c21:Com:=Com.seq c18 c20; let c22:Com:=Com.seq c17 c21; let c23:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22; let c24:Com:=Com.seq c16 c23; let c25:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c26:Nat:=c25 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c27:Nat:=c25 c26 ((1:Nat)); let c28:Nat:=Nat.mul c27 (Env.vars σ "choose.cols"); let c29:Nat:=c6 c28 (Env.vars σ "subset.need"); let c30:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c29 ((0:Nat)); let c31:Env:=Env.setVar σ "subset.count" c30; let c32:String→ Nat:=Env.vars c31; let c33:Nat:=c32 "subset.rank"; let c34:Nat:=c32 "subset.count"; let c35:Prop:=Nat.lt c33 c34; let c36:Prop:=Not c35; let c37:Nat→ Env:=Env.setVar c31 "subset.bit"; let c38:Env:=c37 ((0:Nat)); let c39:String→ Nat:=Env.vars c38; let c40:Prop:=And (@Eq Nat (c39 "subset.bit") ((0:Nat))) (And (@Eq Nat (c39 "subset.need") need) (@Eq Nat (c39 "subset.rank") rank)); let c41:Nat:=c7 (Expr.size c15); let c42:Nat→ Nat:=c6 c41; let c43:Nat→ Nat:=c6 (c7 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c44:Nat:=c43 c10; let c45:Nat:=c42 c44; let c46:Nat→ Prop:=Nat.lt c29; let c47:Env:=c37 ((1:Nat)); let c48:String→ Nat:=Env.vars c47; let c49:Nat:=c48 "subset.rank"; let c50:Nat:=c48 "subset.count"; let c51:Nat:=c25 c49 c50; let c52:Env:=Env.setVar c47 "subset.rank" c51; let c53:Nat:=Env.vars c52 "subset.need"; let c54:Nat:=c25 c53 ((1:Nat)); let c55:Env:=Env.setVar c52 "subset.need" c54; let c56:String→ Nat:=Env.vars c55; let c57:Prop:=And (@Eq Nat (c56 "subset.bit") ((0:Nat))) (And (@Eq Nat (c56 "subset.need") need) (@Eq Nat (c56 "subset.rank") rank)); let c58:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c59:Nat:=c7 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c60:Nat:=c7 (Expr.size c19); let c61:Nat:=c6 c59 c60; let c62:Nat:=c6 c58 c61; let c63:Nat:=c43 c62; let c64:Nat:=c42 c63; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c2) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c2 c3 (@And.intro (Run B subsetEntry σ c3 ((40:Nat))) c5 (RunStep.mono B subsetEntry σ c3 (c9 c10) ((40:Nat)) (RunStep.ite_true B c8 c11 c24 σ c3 c10 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_2)))) (?nAX_g7928_1_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c35 c36 (fun (x:Or c35 c36) => @Exists Env c2) (Classical.em c35) (fun (hcase_1:c35) => @Exists.intro Env c2 c38 (@And.intro (Run B subsetEntry σ c38 ((40:Nat))) c40 (RunStep.mono B subsetEntry σ c38 (c9 c45) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c38 c45 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_5)) hcase) (RunStep.seq B c16 c23 σ c31 c38 c41 c44 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_7)) (?nAX_g7928_1_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_9)) (?nAX_g7928_1_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c38 c10 (RunStep.cond_lt_true B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_13)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.assign B c31 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c31 (?nAX_g7928_1_0_14)))))) (?nAX_g7928_1_0_15)) ?_)) fun (hcase_1:c36) => @Exists.intro Env c2 c55 (@And.intro (Run B subsetEntry σ c55 ((40:Nat))) c57 (RunStep.mono B subsetEntry σ c55 (c9 c64) ((40:Nat)) (RunStep.ite_false B c8 c11 c24 σ c55 c64 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_1_0_17)) hcase) (RunStep.seq B c16 c23 σ c31 c55 c41 c63 (RunStep.assign B σ "subset.count" c15 c30 (RunStep.eval_get B σ "choose.table" c14 c29 (RunStep.eval_add B σ c13 (Expr.var "subset.need") c28 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c12 (Expr.var "choose.cols") c27 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c26 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_1_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_1_0_19)) (?nAX_g7928_1_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_1_0_21)) (?nAX_g7928_1_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_1_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_1_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c11 c22 c31 c55 c62 (RunStep.cond_lt_false B c31 (Expr.var "subset.rank") (Expr.var "subset.count") c33 c34 (RunStep.eval_var B c31 "subset.rank" (?nAX_g7928_1_0_25)) (RunStep.eval_var B c31 "subset.count" ?_) hcase_1) (RunStep.seq B c17 c21 c31 c47 c55 c58 c61 (RunStep.assign B c31 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c31 (?nAX_g7928_1_0_26))) (RunStep.seq B c18 c20 c47 c52 c55 c59 c60 (RunStep.assign B c47 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c51 (RunStep.eval_sub B c47 (Expr.var "subset.rank") (Expr.var "subset.count") c49 c50 (RunStep.eval_var B c47 "subset.rank" (?nAX_g7928_1_0_27)) (RunStep.eval_var B c47 "subset.count" ?_) (?nAX_g7928_1_0_28))) (RunStep.assign B c52 "subset.need" c19 c54 (RunStep.eval_sub B c52 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c53 ((1:Nat)) (RunStep.eval_var B c52 "subset.need" (?nAX_g7928_1_0_29)) (RunStep.eval_lit B ((1:Nat)) c52 (?nAX_g7928_1_0_30)) (?nAX_g7928_1_0_31)))))))) (?nAX_g7928_1_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
    · have ha:advance (n-i) need rank=(1,need-1,rank-(n-i-1).choose need):=by simp [advance,hneed0,hsmall]
      simp only [ha]
      (expose_names;
        (refine let c0:Prop:= @Eq Nat (Env.vars σ "subset.need") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c3:Nat:=c2 need ((1:Nat)); let c4:Nat:=c2 rank (Nat.choose (c2 (c2 n i) ((1:Nat))) need); let c5:Env→ Prop:=fun (σ':Env) => And (Run B subsetEntry σ σ' ((40:Nat))) (And (@Eq Nat (Env.vars σ' "subset.bit") ((1:Nat))) (And (@Eq Nat (Env.vars σ' "subset.need") c3) (@Eq Nat (Env.vars σ' "subset.rank") c4))); let c6:Env:=Env.setVar σ "subset.bit" ((0:Nat)); let c7:String→ Nat:=Env.vars c6; let c8:Prop:=And (@Eq Nat (c7 "subset.bit") ((1:Nat))) (And (@Eq Nat (c7 "subset.need") c3) (@Eq Nat (c7 "subset.rank") c4)); let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Cond:=Cond.eq (Expr.var "subset.need") (Expr.lit ((0:Nat))); let c12:Nat→ Nat:=c9 (c10 (Cond.size c11)); let c13:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c14:Com:=Com.assign "subset.bit" (Expr.lit ((0:Nat))); let c15:Expr:=Expr.sub (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))); let c16:Expr:=Expr.mul c15 (Expr.var "choose.cols"); let c17:Expr:=Expr.add c16 (Expr.var "subset.need"); let c18:Expr:=Expr.get "choose.table" c17; let c19:Com:=Com.assign "subset.count" c18; let c20:Com:=Com.assign "subset.bit" (Expr.lit ((1:Nat))); let c21:Com:=Com.assign "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")); let c22:Expr:=Expr.sub (Expr.var "subset.need") (Expr.lit ((1:Nat))); let c23:Com:=Com.assign "subset.need" c22; let c24:Com:=Com.seq c21 c23; let c25:Com:=Com.seq c20 c24; let c26:Com:=Com.ite (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25; let c27:Com:=Com.seq c19 c26; let c28:Nat:=c2 (Env.vars σ "choose.n") (Env.vars σ "subset.i"); let c29:Nat:=c2 c28 ((1:Nat)); let c30:Nat:=Nat.mul c29 (Env.vars σ "choose.cols"); let c31:Nat:=c9 c30 (Env.vars σ "subset.need"); let c32:Nat:= @List.getD Nat (Env.arrs σ "choose.table") c31 ((0:Nat)); let c33:Env:=Env.setVar σ "subset.count" c32; let c34:String→ Nat:=Env.vars c33; let c35:Nat:=c34 "subset.rank"; let c36:Nat:=c34 "subset.count"; let c37:Prop:=Nat.lt c35 c36; let c38:Prop:=Not c37; let c39:Nat→ Env:=Env.setVar c33 "subset.bit"; let c40:Env:=c39 ((0:Nat)); let c41:String→ Nat:=Env.vars c40; let c42:Prop:=And (@Eq Nat (c41 "subset.bit") ((1:Nat))) (And (@Eq Nat (c41 "subset.need") c3) (@Eq Nat (c41 "subset.rank") c4)); let c43:Nat:=c10 (Expr.size c18); let c44:Nat→ Nat:=c9 c43; let c45:Nat→ Nat:=c9 (c10 (Cond.size (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")))); let c46:Nat:=c45 c13; let c47:Nat:=c44 c46; let c48:Nat→ Prop:=Nat.lt c31; let c49:Env:=c39 ((1:Nat)); let c50:String→ Nat:=Env.vars c49; let c51:Nat:=c50 "subset.rank"; let c52:Nat:=c50 "subset.count"; let c53:Nat:=c2 c51 c52; let c54:Env:=Env.setVar c49 "subset.rank" c53; let c55:Nat:=Env.vars c54 "subset.need"; let c56:Nat:=c2 c55 ((1:Nat)); let c57:Env:=Env.setVar c54 "subset.need" c56; let c58:String→ Nat:=Env.vars c57; let c59:Prop:=And (@Eq Nat (c58 "subset.bit") ((1:Nat))) (And (@Eq Nat (c58 "subset.need") c3) (@Eq Nat (c58 "subset.rank") c4)); let c60:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c61:Nat:=c10 (Expr.size (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count"))); let c62:Nat:=c10 (Expr.size c22); let c63:Nat:=c9 c61 c62; let c64:Nat:=c9 c60 c63; let c65:Nat:=c45 c64; let c66:Nat:=c44 c65; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c5 c6 (@And.intro (Run B subsetEntry σ c6 ((40:Nat))) c8 (RunStep.mono B subsetEntry σ c6 (c12 c13) ((40:Nat)) (RunStep.ite_true B c11 c14 c27 σ c6 c13 (RunStep.cond_eq_true B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_1)) hcase) (RunStep.assign B σ "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_2)))) (?nAX_g7928_2_0_3)) ?_)) fun (hcase:c1) => @Or.casesOn c37 c38 (fun (x:Or c37 c38) => @Exists Env c5) (Classical.em c37) (fun (hcase_1:c37) => @Exists.intro Env c5 c40 (@And.intro (Run B subsetEntry σ c40 ((40:Nat))) c42 (RunStep.mono B subsetEntry σ c40 (c12 c47) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c40 c47 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_5)) hcase) (RunStep.seq B c19 c26 σ c33 c40 c43 c46 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_6)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_7)) (?nAX_g7928_2_0_8)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_9)) (?nAX_g7928_2_0_10)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_11)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_12)) ?_) ?_ ?_)) (RunStep.ite_true B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c40 c13 (RunStep.cond_lt_true B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_13)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.assign B c33 "subset.bit" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c33 (?nAX_g7928_2_0_14)))))) (?nAX_g7928_2_0_15)) ?_)) fun (hcase_1:c38) => @Exists.intro Env c5 c57 (@And.intro (Run B subsetEntry σ c57 ((40:Nat))) c59 (RunStep.mono B subsetEntry σ c57 (c12 c66) ((40:Nat)) (RunStep.ite_false B c11 c14 c27 σ c57 c66 (RunStep.cond_eq_false B σ (Expr.var "subset.need") (Expr.lit ((0:Nat))) (Env.vars σ "subset.need") ((0:Nat)) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_16)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7928_2_0_17)) hcase) (RunStep.seq B c19 c26 σ c33 c57 c43 c65 (RunStep.assign B σ "subset.count" c18 c32 (RunStep.eval_get B σ "choose.table" c17 c31 (RunStep.eval_add B σ c16 (Expr.var "subset.need") c30 (Env.vars σ "subset.need") (RunStep.eval_mul B σ c15 (Expr.var "choose.cols") c29 (Env.vars σ "choose.cols") (RunStep.eval_sub B σ (Expr.sub (Expr.var "choose.n") (Expr.var "subset.i")) (Expr.lit ((1:Nat))) c28 ((1:Nat)) (RunStep.eval_sub B σ (Expr.var "choose.n") (Expr.var "subset.i") (Env.vars σ "choose.n") (Env.vars σ "subset.i") (RunStep.eval_var B σ "choose.n" (?nAX_g7928_2_0_18)) (RunStep.eval_var B σ "subset.i" (?nAX_g7928_2_0_19)) (?nAX_g7928_2_0_20)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g7928_2_0_21)) (?nAX_g7928_2_0_22)) (RunStep.eval_var B σ "choose.cols" (?nAX_g7928_2_0_23)) ?_) (RunStep.eval_var B σ "subset.need" (?nAX_g7928_2_0_24)) ?_) ?_ ?_)) (RunStep.ite_false B (Cond.lt (Expr.var "subset.rank") (Expr.var "subset.count")) c14 c25 c33 c57 c64 (RunStep.cond_lt_false B c33 (Expr.var "subset.rank") (Expr.var "subset.count") c35 c36 (RunStep.eval_var B c33 "subset.rank" (?nAX_g7928_2_0_25)) (RunStep.eval_var B c33 "subset.count" ?_) hcase_1) (RunStep.seq B c20 c24 c33 c49 c57 c60 c63 (RunStep.assign B c33 "subset.bit" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g7928_2_0_26))) (RunStep.seq B c21 c23 c49 c54 c57 c61 c62 (RunStep.assign B c49 "subset.rank" (Expr.sub (Expr.var "subset.rank") (Expr.var "subset.count")) c53 (RunStep.eval_sub B c49 (Expr.var "subset.rank") (Expr.var "subset.count") c51 c52 (RunStep.eval_var B c49 "subset.rank" (?nAX_g7928_2_0_27)) (RunStep.eval_var B c49 "subset.count" ?_) (?nAX_g7928_2_0_28))) (RunStep.assign B c54 "subset.need" c22 c56 (RunStep.eval_sub B c54 (Expr.var "subset.need") (Expr.lit ((1:Nat))) c55 ((1:Nat)) (RunStep.eval_var B c54 "subset.need" (?nAX_g7928_2_0_29)) (RunStep.eval_lit B ((1:Nat)) c54 (?nAX_g7928_2_0_30)) (?nAX_g7928_2_0_31)))))))) (?nAX_g7928_2_0_32)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7928_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7928_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Env.setVar,advance]
      all_goals omega

def SubsetInvariant (n k rank:ℕ) (σ:Env):Prop:=
  σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
  Prefix (table n k) "choose.table" σ∧ n≤(σ.arrs "subset.bits").length∧
  σ.vars "subset.i"≤ n∧ σ.vars "subset.need"≤ k∧ σ.vars "subset.rank"≤ rank∧
  Prefix ((bits n k rank).take (σ.vars "subset.i")) "subset.bits" σ∧
  (bits n k rank).drop (σ.vars "subset.i")=
    bits (n-σ.vars "subset.i") (σ.vars "subset.need") (σ.vars "subset.rank")

theorem subset_step_spec (B n k rank:ℕ) (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => SubsetInvariant n k rank σ∧ σ.vars "subset.i"< n) subsetStep
      (fun σ τ => SubsetInvariant n k rank τ∧ τ.vars "subset.i"=σ.vars "subset.i"+1) 50:=by
  rintro σ ⟨⟨hn,hcols,htable,hroom,hle,hneed,hq,hprefix,htail⟩,hlt⟩
  let i:=σ.vars "subset.i"
  let need:=σ.vars "subset.need"
  let q:=σ.vars "subset.rank"
  let a:=advance (n-i) need q
  let xs:=bits n k rank
  have hlen:xs.length=n:=bits_length _ _ _
  have hab:=advance_bounds (n-i) need q
  have htail':xs.drop i=a.1::bits (n-i-1) a.2.1 a.2.2:=by
    rw [htail,bits_step (n-i) need q (by omega)]
  have hval:xs[i]=a.1:=by
    have he:=congrArg (fun ys:List ℕ => ys[0]?) htail'
    simp only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] at he
    rw [List.getElem?_eq_getElem (by omega)] at he
    exact Option.some.inj he
  have hnext:xs.drop (i+1)=bits (n-(i+1)) a.2.1 a.2.2:=by
    rw [←List.drop_drop,htail']
    simp only [List.drop_succ_cons,List.drop_zero,Nat.sub_sub]
  obtain ⟨ν,r1,p1⟩:=subset_entry_spec B n k i need q hlt hneed hB (hq.trans_lt hrank) hcoeff σ
    ⟨hn,hcols,rfl,rfl,rfl,htable⟩
  have hiν:ν.vars "subset.i"=i:=r1.frame_var "subset.i" (by decide)
  have htlen:(xs.take i).length=i:=by rw [List.length_take,hlen]; omega
  have hbit:a.1< B:=hab.1.trans_lt (by omega)
  obtain ⟨τ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "subset.i"
    (xs.take i) a.1 (.var "subset.bit") (by omega) (by rw [htlen]; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hbit⟩⟩
  have ht:τ.vars "subset.i"=i+1:=by simpa only [htlen] using p2.2
  have htn:τ.vars "subset.need"=a.2.1:=(r2.frame_var "subset.need" (by decide)).trans p1.2.1
  have htq:τ.vars "subset.rank"=a.2.2:=(r2.frame_var "subset.rank" (by decide)).trans p1.2.2
  have rr:=r1.seq r2
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.n" (by decide)).trans hn,
    (rr.frame_var "choose.cols" (by decide)).trans hcols,?_,?_,by rw [ht]; omega,
    by rw [htn]; exact hab.2.1.trans hneed,by rw [htq]; exact hab.2.2.trans hq,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "choose.table" (by decide)] using htable
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem (by rw [bits_length]; exact hlt),hval]
    exact p2.1
  · rw [ht,htn,htq]
    exact hnext

theorem subset_command_spec (B n k rank:ℕ) (hB:(n+1)*(k+1)+n+k+3< B) (hrank:rank< B)
    (hcoeff:∀ i≤ n,∀ j≤ k,i.choose j< B):
    Spec B (fun σ => σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
      σ.vars "subset.need"=k∧ σ.vars "subset.rank"=rank∧
      Prefix (table n k) "choose.table" σ∧ n≤(σ.arrs "subset.bits").length) subsetCommand
      (fun _ τ => Prefix (bits n k rank) "subset.bits" τ) (54*n+6):=by
  have hloop:=Spec.forRangeZero "subset.i" "choose.n" (SubsetInvariant n k rank) n 50
    (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.1) (subset_step_spec B n k rank hB hrank hcoeff)
  rintro σ ⟨hn,hcols,hneed,hq,htable,hroom⟩
  have hi:SubsetInvariant n k rank (σ.setVar "subset.i" 0):=by
    refine ⟨?_,?_,htable,hroom,by simp,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcols
    · simp only [vars_setVar,String.reduceEq,if_false,hneed,le_refl]
    · simp only [vars_setVar,String.reduceEq,if_false,hq,le_refl]
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp only [vars_setVar,String.reduceEq,if_true,if_false,List.drop_zero,Nat.sub_zero,hneed,hq]
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr,?_⟩
  have ht:(bits n k rank).take n=bits n k rank:=List.take_of_length_le (by rw [bits_length])
  simpa only [p.2,ht] using p.1.2.2.2.2.2.2.2.1

theorem bits_binary (n k rank:ℕ):∀ b∈bits n k rank,b=0∨ b=1:=by
  induction n generalizing k rank with
  | zero => simp [bits]
  | succ n ih =>
    intro b hb
    cases k with
    | zero =>
      simp only [bits,List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact ih _ _ b hb
    | succ k =>
      by_cases h:rank< n.choose (k+1)
      · simp only [bits,if_pos h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inl rfl
        · exact ih _ _ b hb
      · simp only [bits,if_neg h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact ih _ _ b hb

theorem decode_get {α:Type*} (xs:List α) (bs:List ℕ) (hnd:xs.Nodup)
    (hlen:bs.length=xs.length) (i:ℕ) (hi:i< xs.length):
    xs[i]∈decode xs bs↔ bs[i]=1:=by
  constructor
  · intro h
    obtain ⟨p,hp,hval⟩:=List.mem_filterMap.mp h
    obtain ⟨j,hj,hpj⟩:=List.mem_iff_getElem.mp hp
    have hjx:j< xs.length:=by simpa only [List.length_zip,hlen,Nat.min_self] using hj
    have hjb:j< bs.length:=by omega
    rw [List.getElem_zip] at hpj
    subst p
    dsimp only at hval
    split_ifs at hval with hb
    · have hx:xs[j]=xs[i]:=Option.some.inj hval
      have he:j=i:=(List.Nodup.getElem_inj_iff hnd).mp hx
      subst j
      exact hb
  · intro hb
    apply List.mem_filterMap.mpr
    refine ⟨(xs[i],bs[i]),?_,?_⟩
    · have hz:i<(xs.zip bs).length:=by simp only [List.length_zip,hlen,Nat.min_self]; exact hi
      have hh:=List.getElem_mem hz
      simpa only [List.getElem_zip] using hh
    · simp [hb]

theorem bits_encoding (n k rank:ℕ):
    bits n k rank=Lax263307.IndependentSetEncoding.encodeOutput
      (decode (List.finRange n) (bits n k rank)).toFinset:=by
  let bs:=bits n k rank
  let I:=(decode (List.finRange n) bs).toFinset
  have hlen:bs.length=n:=bits_length _ _ _
  apply List.ext_getElem
  · simpa [Lax263307.IndependentSetEncoding.encodeOutput] using hlen
  · intro i hi hi'
    have hin:i< n:=by simpa only [bits_length] using hi
    have hxs:i<(List.finRange n).length:=by simpa using hin
    have hd:=decode_get (List.finRange n) bs (List.nodup_finRange n) (by simpa using hlen) i hxs
    simp only [List.getElem_finRange] at hd
    have hget:(Lax263307.IndependentSetEncoding.encodeOutput I)[i]=
        if (⟨i,hin⟩:Fin n)∈I then 1 else 0:=List.getElem_ofFn hi'
    change bs[i]=(Lax263307.IndependentSetEncoding.encodeOutput I)[i]
    rw [hget]
    by_cases hb:bs[i]=1
    · have hm:(⟨i,hin⟩:Fin n)∈I:=List.mem_toFinset.mpr (hd.mpr hb)
      rw [if_pos hm]
      exact hb
    · have hz:bs[i]=0:=(bits_binary n k rank _ (List.getElem_mem hi)).resolve_right hb
      have hm:(⟨i,hin⟩:Fin n)∉I:=fun h => hb (hd.mp (List.mem_toFinset.mp h))
      rw [if_neg hm]
      exact hz

theorem candidate_coordinate (n k rank:ℕ) (hrank:rank< n.choose k):
    (Lax263307.ExhaustiveTargets.candidates n k)[rank]?=
      some (decode (List.finRange n) (bits n k rank)).toFinset:=by
  have hs:=select_correct (List.finRange n) k rank (by simpa using hrank)
  rw [Lax263307.ExhaustiveTargets.candidates,List.getElem?_map,hs]
  simp only [Option.map_some]
  congr 2
  have hd:=decode_bits (List.finRange n) k rank
  simpa only [List.length_finRange] using hd.symm

end Lax263307Proofs.NativeCombinations

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

theorem mask_injective (n:ℕ):Function.Injective (mask (n:=n)):=by
  intro I J h
  ext v
  have hh:=congrArg (fun m:ℕ => m.testBit v.val) h
  simpa only [mask_member,decide_eq_decide] using hh

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

namespace Lax263307Proofs.NativeZeroScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def prefixOK (xs:List ℕ) (i:ℕ):ℕ:=
  if (xs.take i).all (fun x => x==0) then 1 else 0

theorem prefix_ok_zero (xs:List ℕ):prefixOK xs 0=1:=by simp [prefixOK]

theorem prefix_ok_le (xs:List ℕ) (i:ℕ):prefixOK xs i≤1:=by
  unfold prefixOK
  split_ifs <;> omega

theorem prefix_ok_succ (xs:List ℕ) (i:ℕ) (hi:i< xs.length):
    prefixOK xs (i+1)=if xs[i]=0 then prefixOK xs i else 0:=by
  unfold prefixOK
  rw [List.take_succ_eq_append_getElem hi,List.all_append]
  cases h:(xs.take i).all (fun x => x==0) <;> by_cases hx:xs[i]=0 <;> simp [hx]

theorem prefix_ok_full (xs:List ℕ):prefixOK xs xs.length=1↔ ∀ x∈xs,x=0:=by
  simp [prefixOK,List.all_eq_true]

theorem update_spec (B i bit ok:ℕ) (hi:i+1< B) (hbit:bit< B) (_hok:ok≤1) (h1:1< B):
    Spec B (fun σ => σ.vars "test.i"=i∧ σ.vars "test.bit"=bit∧ σ.vars "test.ok"=ok)
      update (fun _ τ => τ.vars "test.i"=i+1∧ τ.vars "test.ok"=if bit=0 then ok else 0) 10:=by
  by_cases hbit0:bit=0
  · subst bit
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") ((0:Nat))) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c1:Prop:=And c0 (@Eq Nat (Env.vars σ "test.ok") ok); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 i ((1:Nat)); let c4:Nat:= @ite Nat (@Eq Nat ((0:Nat)) ((0:Nat))) (instDecidableEqNat ((0:Nat)) ((0:Nat))) ok ((0:Nat)); let c5:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c3) (@Eq Nat (Env.vars τ "test.ok") c4)) σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:=Not c0; let c9:Nat:=c2 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c2 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c2 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c2 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c1 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c1) => c7) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c1) => @And.casesOn c0 (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c1) => c7) right fun (left_1:c0) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c0 c8 (fun (x:Or c0 c8) => c7) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c6 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c5 c10) (RunStep.mono B update σ c10 (c2 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_0_0_1)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_0_0_2)))) (?nAX_g7963_0_0_3)) ?_)) fun (hcase:c8) => @Exists.intro Env c6 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c5 c22) (RunStep.mono B update σ c22 (c2 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ hbit) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hbit))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_0_0_6)))) (?nAX_g7963_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "test.i") i) (And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 i ((1:Nat)); let c3:Nat:= @ite Nat (@Eq Nat bit ((0:Nat))) (instDecidableEqNat bit ((0:Nat))) ok ((0:Nat)); let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "test.i") c2) (@Eq Nat (Env.vars τ "test.ok") c3)) σ; let c5:Env→ Prop:=fun (σ':Env) => And (Run B update σ σ' ((10:Nat))) (c4 σ'); let c6:Prop:= @Exists Env c5; let c7:Prop:= @Eq Nat (Env.vars σ "test.bit") ((0:Nat)); let c8:Prop:=Not c7; let c9:Nat:=c1 (Env.vars σ "test.i") ((1:Nat)); let c10:Env:=Env.setVar σ "test.i" c9; let c11:Nat→ Nat:=c1 ((1:Nat)); let c12:Cond:=Cond.eq (Expr.var "test.bit") (Expr.lit ((0:Nat))); let c13:Nat→ Nat:=c1 (c11 (Cond.size c12)); let c14:Nat:=c13 ((1:Nat)); let c15:Expr:=Expr.add (Expr.var "test.i") (Expr.lit ((1:Nat))); let c16:Nat:=c11 (Expr.size c15); let c17:Com:=Com.assign "test.ok" (Expr.lit ((0:Nat))); let c18:String→ Nat:=Env.vars c10; let c19:Env:=Env.setVar σ "test.ok" ((0:Nat)); let c20:Nat:=Env.vars c19 "test.i"; let c21:Nat:=c1 c20 ((1:Nat)); let c22:Env:=Env.setVar c19 "test.i" c21; let c23:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c13 c23; let c25:String→ Nat:=Env.vars c22; @And.casesOn (@Eq Nat (Env.vars σ "test.i") i) c0 (fun (x:And (@Eq Nat (Env.vars σ "test.i") i) c0) => c6) a fun (left:@Eq Nat (Env.vars σ "test.i") i) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "test.bit") bit) (@Eq Nat (Env.vars σ "test.ok") ok) (fun (x:c0) => c6) right fun (left_1:@Eq Nat (Env.vars σ "test.bit") bit) (right_1:@Eq Nat (Env.vars σ "test.ok") ok) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c6) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c5 c10 (@And.intro (Run B update σ c10 ((10:Nat))) (c4 c10) (RunStep.mono B update σ c10 (c1 c14 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ σ c10 c14 c16 (RunStep.ite_true B c12 Com.skip c17 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_1)) hcase) (RunStep.skip B σ)) (RunStep.assign B σ "test.i" c15 c9 (RunStep.eval_add B σ (Expr.var "test.i") (Expr.lit ((1:Nat))) (Env.vars σ "test.i") ((1:Nat)) (RunStep.eval_var B σ "test.i" (?nAX_g7963_1_0_2)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g7963_1_0_3)))) (?nAX_g7963_1_0_4)) ?_)) fun (hcase:c8) => @Exists.intro Env c5 c22 (@And.intro (Run B update σ c22 ((10:Nat))) (c4 c22) (RunStep.mono B update σ c22 (c1 c24 c16) ((10:Nat)) (RunStep.seq B (Com.ite c12 Com.skip c17) (Com.assign "test.i" c15) σ c19 c22 c24 c16 (RunStep.ite_false B c12 Com.skip c17 σ c19 c23 (RunStep.cond_eq_false B σ (Expr.var "test.bit") (Expr.lit ((0:Nat))) (Env.vars σ "test.bit") ((0:Nat)) (RunStep.eval_var B σ "test.bit" (?nAX_g7963_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_6)) hcase) (RunStep.assign B σ "test.ok" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g7963_1_0_7)))) (RunStep.assign B c19 "test.i" c15 c21 (RunStep.eval_add B c19 (Expr.var "test.i") (Expr.lit ((1:Nat))) c20 ((1:Nat)) (RunStep.eval_var B c19 "test.i" (?nAX_g7963_1_0_8)) (RunStep.eval_lit B ((1:Nat)) c19 h1) (?nAX_g7963_1_0_9)))) (?nAX_g7963_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7963_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7963_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]

def Invariant (P:Env→ Prop) (xs:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "test.limit"=xs.length∧ σ.vars "test.i"≤ xs.length∧
  σ.vars "test.ok"=prefixOK xs (σ.vars "test.i")

theorem command_spec (B:ℕ) (xs:List ℕ) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:xs.length+2< B) (hwords:∀ x∈xs,x< B)
    (hri:"test.i"∉read.wvars) (hrl:"test.limit"∉read.wvars) (hro:"test.ok"∉read.wvars)
    (hinit:∀ σ,P σ→ P ((σ.setVar "test.ok" 1).setVar "test.i" 0))
    (hupdate:∀ σ τ,Run B update σ τ 10→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "test.i"=i) read
      (fun _ τ => P τ∧ τ.vars "test.bit"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "test.limit"=xs.length) (command read)
      (fun _ τ => P τ∧ τ.vars "test.ok"=prefixOK xs xs.length)
      ((K+14)*xs.length+8):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant P xs σ∧ σ.vars "test.i"< xs.length) (body read)
      (fun σ τ => Invariant P xs τ∧ τ.vars "test.i"=σ.vars "test.i"+1) (K+10):=by
    rintro σ ⟨⟨hPσ,hlen,hle,hok⟩,hlt⟩
    let i:=σ.vars "test.i"
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hPσ,rfl⟩
    have hiν:ν.vars "test.i"=i:=r1.frame_var "test.i" hri
    have hokν:ν.vars "test.ok"=prefixOK xs i:=(r1.frame_var "test.ok" hro).trans hok
    obtain ⟨τ,r2,p2⟩:=update_spec B i xs[i] (prefixOK xs i) (by dsimp [i]; omega)
      (hwords _ (List.getElem_mem hlt)) (prefix_ok_le xs i) h1 ν ⟨hiν,p1.2,hokν⟩
    have hPτ:P τ:=hupdate ν τ r2 p1.1
    refine ⟨τ,r1.seq r2,⟨hPτ,?_,by rw [p2.1]; omega,?_⟩,p2.1⟩
    · exact (r2.frame_var "test.limit" (by decide)).trans ((r1.frame_var "test.limit" hrl).trans hlen)
    · rw [p2.1,prefix_ok_succ xs i hlt]
      exact p2.2
  have hloop:=Spec.forRangeZero "test.i" "test.limit" (Invariant P xs) xs.length (K+10)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hPσ,hlen⟩
  let ν:=σ.setVar "test.ok" 1
  have r1:Run B (.assign "test.ok" (.lit 1)) σ ν 2:=Run.assign (evalB_lit h1)
  have hi:Invariant P xs (ν.setVar "test.i" 0):=by
    refine ⟨?_,?_,by simp,?_⟩
    · exact hinit σ hPσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hlen
    · simp [ν,prefix_ok_zero]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  simpa only [p2.2] using p2.1.2.2.2

end Lax263307Proofs.NativeZeroScan

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeIndependentTest

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

def pairValue {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):ℕ:=
  (if u∈I then 1 else 0)*(if v∈I then 1 else 0)*(if G.Adj u v then 1 else 0)

theorem pair_value_le {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v≤1:=by
  unfold pairValue
  split_ifs <;> norm_num

theorem pair_value_zero {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (u v:Fin n):pairValue G I u v=0↔ (u∈I→ v∈I→ ¬G.Adj u v):=by
  unfold pairValue
  split_ifs <;> simp_all

def values {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):List ℕ:=
  List.ofFn fun q:Fin (n*n) => pairValue G I (NativeBlowUp.row q) (NativeBlowUp.col q)

theorem values_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):(values G I).length=n*n:=List.length_ofFn

theorem values_correct {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)):
    NativeZeroScan.prefixOK (values G I) (n*n)=1↔ G.IsIndepSet (I:Set (Fin n)):=by
  rw [←values_length G I,NativeZeroScan.prefix_ok_full]
  constructor
  · intro h u hu v hv huv
    let q:Fin (n*n):= ⟨u.val*n+v.val,by nlinarith only [u.isLt,v.isLt]⟩
    have hn:0< n:=by omega
    have hrow:NativeBlowUp.row q=u:=by
      apply Fin.ext
      dsimp [NativeBlowUp.row,q]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt]
      omega
    have hcol:NativeBlowUp.col q=v:=by
      apply Fin.ext
      simp [NativeBlowUp.col,q,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
    have hh:=h _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
    rw [hrow,hcol,pair_value_zero] at hh
    exact hh hu hv
  · intro h z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    rw [pair_value_zero]
    intro hu hv hadj
    exact h hu hv hadj.ne hadj

theorem read_spec (B n q a b e:ℕ) (graphArray membershipArray:String)
    (hB:n*n+n+3< B) (hq:q< n*n) (ha:a≤1) (hb:b≤1) (he:e≤1):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "test.i"=q∧
      (σ.arrs membershipArray)[q/n]?=some a∧ (σ.arrs membershipArray)[q%n]?=some b∧
      (σ.arrs graphArray)[q]?=some e) (read graphArray membershipArray)
      (fun _ τ => τ.vars "test.bit"=a*b*e) 24:=by
  have hn:0< n:=by nlinarith only [hq]
  have hqn:q/n< n:=(Nat.div_lt_iff_lt_mul hn).mpr hq
  have hmod:q%n< n:=Nat.mod_lt _ hn
  have hqB:q< B:=by omega
  have hdivmul:q/n*n≤ q:=Nat.div_mul_le_self _ _
  have hab:a*b≤1:=by nlinarith only [Nat.mul_le_mul ha hb]
  have habe:a*b*e≤1:=by nlinarith only [Nat.mul_le_mul hab he]
  rintro σ ⟨hnσ,hqσ,haσ,hbσ,heσ⟩
  have hrooma:q/n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at haσ
    contradiction
  have hroomb:q%n<(σ.arrs membershipArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hbσ
    contradiction
  have hroome:q<(σ.arrs graphArray).length:=by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (c0 a b) e; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "test.bit") c1) σ; let c3:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "test.i") (Env.vars σ "graph.n"); let c4:Env:=Env.setVar σ "test.row" c3; let c5:String→ Nat:=Env.vars c4; let c6:Nat:=c5 "test.i"; let c7:Nat:=c5 "test.row"; let c8:Nat:=c5 "graph.n"; let c9:Nat:=c0 c7 c8; let c10:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c6 c9; let c11:Env:=Env.setVar c4 "test.col" c10; let c12:String→ List Nat:=Env.arrs c11; let c13:List Nat:=c12 membershipArray; let c14:Nat→ Nat→ Nat:= @List.getD Nat c13; let c15:String→ Nat:=Env.vars c11; let c16:Nat:=c15 "test.row"; let c17:Nat:=c14 c16 ((0:Nat)); let c18:Nat:=c15 "test.col"; let c19:Nat:=c14 c18 ((0:Nat)); let c20:Nat:=c0 c17 c19; let c21:Nat:=c15 "test.i"; let c22:Nat:= @List.getD Nat (c12 graphArray) c21 ((0:Nat)); let c23:Nat:=c0 c20 c22; let c24:Env:=Env.setVar c11 "test.bit" c23; let c25:Nat→ Nat→ Nat:=Nat.add; let c26:Nat→ Nat:=c25 ((1:Nat)); let c27:Nat:=c26 (Expr.size (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))); let c28:Expr:=Expr.sub (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")); let c29:Nat:=c26 (Expr.size c28); let c30:Expr:=Expr.mul (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")); let c31:Expr:=Expr.mul c30 (Expr.get graphArray (Expr.var "test.i")); let c32:Nat:=c26 (Expr.size c31); let c33:Nat:=c25 c29 c32; let c34:Com:=Com.assign "test.col" c28; let c35:Com:=Com.assign "test.bit" c31; let c36:Nat→ Prop:=Nat.lt c16; let c37:Nat:= @List.length Nat c13; @Exists.intro Env (fun (σ':Env) => And (Run B (read graphArray membershipArray) σ σ' ((24:Nat))) (c2 σ')) c24 (@And.intro (Run B (read graphArray membershipArray) σ c24 ((24:Nat))) (c2 c24) (RunStep.mono B (read graphArray membershipArray) σ c24 (c25 c27 c33) ((24:Nat)) (RunStep.seq B (Com.assign "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n"))) (Com.seq c34 c35) σ c4 c24 c27 c33 (RunStep.assign B σ "test.row" (Expr.div (Expr.var "test.i") (Expr.var "graph.n")) c3 (RunStep.eval_div B σ (Expr.var "test.i") (Expr.var "graph.n") (Env.vars σ "test.i") (Env.vars σ "graph.n") (RunStep.eval_var B σ "test.i" (?nAX_g7975_0_0_0)) (RunStep.eval_var B σ "graph.n" (?nAX_g7975_0_0_1)) ?_)) (RunStep.seq B c34 c35 c4 c11 c24 c29 c32 (RunStep.assign B c4 "test.col" c28 c10 (RunStep.eval_sub B c4 (Expr.var "test.i") (Expr.mul (Expr.var "test.row") (Expr.var "graph.n")) c6 c9 (RunStep.eval_var B c4 "test.i" (?nAX_g7975_0_0_2)) (RunStep.eval_mul B c4 (Expr.var "test.row") (Expr.var "graph.n") c7 c8 (RunStep.eval_var B c4 "test.row" ?_) (RunStep.eval_var B c4 "graph.n" (?nAX_g7975_0_0_3)) ?_) (?nAX_g7975_0_0_4))) (RunStep.assign B c11 "test.bit" c31 c23 (RunStep.eval_mul B c11 c30 (Expr.get graphArray (Expr.var "test.i")) c20 c22 (RunStep.eval_mul B c11 (Expr.get membershipArray (Expr.var "test.row")) (Expr.get membershipArray (Expr.var "test.col")) c17 c19 (RunStep.eval_get B c11 membershipArray (Expr.var "test.row") c16 (RunStep.eval_var B c11 "test.row" ?_) ?_ ?_) (RunStep.eval_get B c11 membershipArray (Expr.var "test.col") c18 (RunStep.eval_var B c11 "test.col" (?nAX_g7975_0_0_5)) ?_ ?_) ?_) (RunStep.eval_get B c11 graphArray (Expr.var "test.i") c21 (RunStep.eval_var B c11 "test.i" (?nAX_g7975_0_0_6)) (?nAX_g7975_0_0_7) ?_) ?_)))) (?nAX_g7975_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7975_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7975_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def Representation {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ Prefix (NativeWeightReduction.adjacency G) graphArray σ∧
    Prefix (encodeOutput I) membershipArray σ

theorem read_graph_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B)
    (q:ℕ) (hq:q<(values G I).length):
    Spec B (fun σ => Representation G I graphArray membershipArray σ∧ σ.vars "test.i"=q)
      (read graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧ τ.vars "test.bit"=(values G I)[q]) 24:=by
  have hq':q< n*n:=by rwa [values_length] at hq
  let u:=NativeBlowUp.row (⟨q,hq'⟩:Fin (n*n))
  let v:=NativeBlowUp.col (⟨q,hq'⟩:Fin (n*n))
  let a:=if u∈I then 1 else 0
  let b:=if v∈I then 1 else 0
  let e:=if G.Adj u v then 1 else 0
  have ha:a≤1:=by dsimp [a]; split_ifs <;> omega
  have hb:b≤1:=by dsimp [b]; split_ifs <;> omega
  have he:e≤1:=by dsimp [e]; split_ifs <;> omega
  rintro σ ⟨⟨hn,hgraph,hmem⟩,hqi⟩
  have hua:(σ.arrs membershipArray)[q/n]?=some a:=by
    have hh:=hmem u.val (by simp [encodeOutput])
    simpa [encodeOutput,a,u,NativeBlowUp.row] using hh
  have hvb:(σ.arrs membershipArray)[q%n]?=some b:=by
    have hh:=hmem v.val (by simp [encodeOutput])
    simpa [encodeOutput,b,v,NativeBlowUp.col] using hh
  have hge:(σ.arrs graphArray)[q]?=some e:=by
    have hh:=hgraph q (by rwa [NativeWeightReduction.adjacency_length])
    have hc:=NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) (⟨q,hq'⟩:Fin (n*n))
    change (NativeWeightReduction.adjacency G)[q]?=some e at hc
    rw [List.getElem?_eq_getElem (by rwa [NativeWeightReduction.adjacency_length])] at hc
    exact hh.trans hc
  obtain ⟨τ,rr,p⟩:=read_spec B n q a b e graphArray membershipArray hB hq' ha hb he σ
    ⟨hn,hqi,hua,hvb,hge⟩
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by simp [read,Com.wvars])).trans hn,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr graphArray (by simp [read,Com.warrs])] using hgraph
  · simpa only [Prefix,rr.frame_arr membershipArray (by simp [read,Com.warrs])] using hmem
  · simpa [values,pairValue,a,b,e,u,v] using p

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I:Finset (Fin n)) (graphArray membershipArray:String) (hB:n*n+n+3< B):
    Spec B (Representation G I graphArray membershipArray) (command graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ∧
        τ.vars "test.ok"≤1∧ (τ.vars "test.ok"=1↔ G.IsIndepSet (I:Set (Fin n))))
      (38*n*n+12):=by
  have hwords:∀ z∈values G I,z< B:=by
    intro z hz
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hz
    exact (pair_value_le G I _ _).trans_lt (by omega)
  have hs:=NativeZeroScan.command_spec B (values G I) (Representation G I graphArray membershipArray)
    (read graphArray membershipArray) 24 (by rw [values_length]; omega) hwords
    (by simp [read,Com.wvars]) (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by
      rintro σ ⟨hn,hg,hm⟩
      exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hn,hg,hm⟩)
    (by
      rintro σ τ rr ⟨hn,hg,hm⟩
      refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩
      · simpa only [Prefix,rr.frame_arr graphArray (by simp [NativeZeroScan.update,Com.warrs])] using hg
      · simpa only [Prefix,rr.frame_arr membershipArray (by simp [NativeZeroScan.update,Com.warrs])] using hm)
    (read_graph_spec B G I graphArray membershipArray hB)
  intro σ hσ
  let ν:=σ.setVar "test.limit" (n*n)
  have hnB:n< B:=by omega
  have hnnB:n*n< B:=by omega
  have r1:Run B (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩) hnnB)
  have hν:Representation G I graphArray membershipArray ν:=
    ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hσ.1,hσ.2⟩
  obtain ⟨τ,r2,p2⟩:=hs ν ⟨hν,by simp [ν,values_length]⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [values_length]; nlinarith),p2.1,?_,?_⟩
  · rw [p2.2]
    exact NativeZeroScan.prefix_ok_le _ _
  · rw [p2.2,values_length,values_correct]

end Lax263307Proofs.NativeIndependentTest

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeExhaustive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307.ExhaustiveTargets

def candidate (n k rank:ℕ):Finset (Fin n):=
  (NativeCombinations.decode (List.finRange n) (NativeCombinations.bits n k rank)).toFinset

theorem candidate_get (n k rank:ℕ) (hrank:rank< n.choose k):
    (candidates n k)[rank]?=some (candidate n k rank):=
  NativeCombinations.candidate_coordinate n k rank hrank

theorem candidates_length (n k:ℕ):(candidates n k).length=n.choose k:=by
  simp [candidates,List.length_sublistsLen]

theorem adjacency_words {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:
    ∀ z∈NativeWeightReduction.adjacency G,z≤1:=by
  intro z hz
  obtain ⟨r,hr,hz⟩:=List.mem_flatten.mp hz
  obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hr
  obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hz
  split_ifs <;> omega

open Lax109476Proofs

end Lax263307Proofs.NativeExhaustive

end

section

namespace Lax263307Proofs.NativeCatalogOrder

open Lax263307

theorem sublist_toFinset_injective (n:ℕ) (xs ys:List (Fin n))
    (hx:xs.Sublist (List.finRange n)) (hy:ys.Sublist (List.finRange n))
    (he:xs.toFinset=ys.toFinset):xs=ys:=by
  have hs:(List.finRange n).Pairwise (fun u v:Fin n => u< v):=by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simpa only [List.getElem_finRange,Fin.lt_def,Fin.val_cast] using hij
  apply (hs.sublist hx).eq_of_mem_iff (hs.sublist hy)
  intro v
  have hh:=congrArg (fun I:Finset (Fin n) => v∈I) he
  simpa only [List.mem_toFinset] using Iff.of_eq hh

theorem candidates_nodup (n k:ℕ):(ExhaustiveTargets.candidates n k).Nodup:=by
  exact List.Nodup.map_on (by
    intro xs hx ys hy he
    exact sublist_toFinset_injective n xs ys (List.mem_sublistsLen.mp hx).1
      (List.mem_sublistsLen.mp hy).1 he)
    (List.nodup_sublistsLen k (List.nodup_finRange n))

theorem candidate_card (n k:ℕ) (I:Finset (Fin n)) (hI:I∈ExhaustiveTargets.candidates n k):
    I.card=k:=by
  obtain ⟨xs,hxs,rfl⟩:=List.mem_map.mp hI
  obtain ⟨hsub,hlen⟩:=List.mem_sublistsLen.mp hxs
  rw [List.toFinset_card_of_nodup (hsub.nodup (List.nodup_finRange n)),hlen]

theorem all_candidates_nodup (n R:ℕ):(RationalConditioning.candidates n R).Nodup:=by
  change ((List.range (R+1)).flatMap (fun k => ExhaustiveTargets.candidates n k)).Nodup
  rw [List.nodup_flatMap]
  refine ⟨fun k _ => candidates_nodup n k,?_⟩
  apply List.nodup_range.imp
  intro k l hne I hI hJ
  exact hne ((candidate_card n k I hI).symm.trans (candidate_card n l I hJ))

theorem sets_eq (n r:ℕ):CoordinateCatalog.sets n r=RationalConditioning.candidates n (r+2):=by
  exact List.dedup_eq_self.mpr (all_candidates_nodup n (r+2))

theorem catalog_values (n r:ℕ):
    (CoordinateCatalog.catalog n r).map Subtype.val=RationalConditioning.candidates n (r+2):=by
  rw [CoordinateCatalog.catalog,List.map_map]
  simpa only [Function.comp_def,List.attach_map_subtype_val] using sets_eq n r

theorem catalog_index (n r:ℕ) (j:Fin (CoordinateCatalog.catalog n r).length):
    (RationalConditioning.candidates n (r+2))[j.val]?=some (CoordinateCatalog.indexing n r j).val:=by
  rw [←catalog_values,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

theorem all_candidates_succ (n R:ℕ):
    RationalConditioning.candidates n (R+1)=
      RationalConditioning.candidates n R++ExhaustiveTargets.candidates n (R+1):=by
  unfold RationalConditioning.candidates ExhaustiveTargets.candidates
  rw [List.range_succ,List.flatMap_append]
  simp

end Lax263307Proofs.NativeCatalogOrder

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCatalog

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

def block (n k:ℕ):List ℕ:=
  (ExhaustiveTargets.candidates n k).map NativeMasks.mask

theorem block_length (n k:ℕ):(block n k).length=n.choose k:=by
  simp only [block,List.length_map,NativeExhaustive.candidates_length]

theorem block_entry (n k i:ℕ) (hi:i< n.choose k):
    (block n k)[i]?=some (NativeMasks.mask (NativeExhaustive.candidate n k i)):=by
  rw [block,List.getElem?_map,NativeExhaustive.candidate_get n k i hi]
  rfl

def Data (n k:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "choose.n"=n∧ σ.vars "choose.cols"=k+1∧
  σ.vars "catalog.k"=k∧ Prefix (NativeCombinations.table n k) "choose.table" σ∧
  n≤(σ.arrs "subset.bits").length

theorem data_frame {B n k K:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"choose.n"∉c.wvars) (h2:"choose.cols"∉c.wvars)
    (h3:"catalog.k"∉c.wvars) (h4:"choose.table"∉c.warrs)
    (hσ:Data n k σ):Data n k τ:=by
  rcases hσ with ⟨hn,hcn,hcols,hk,ht,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "choose.n" h1).trans hcn,
    (rr.frame_var "choose.cols" h2).trans hcols,(rr.frame_var "catalog.k" h3).trans hk,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "choose.table" h4] using ht
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

theorem candidate_spec (B n k i:ℕ) (hB:(n+1)*(k+1)+n+k+3< B) (hi:i< B)
    (hm:2^n< B) (hcoeff:∀ a≤ n,∀ b≤ k,a.choose b< B):
    Spec B (fun σ => Data n k σ∧ σ.vars "catalog.i"=i) candidateCommand
      (fun _ τ => Data n k τ∧ τ.vars "mask.value"=NativeMasks.mask (NativeExhaustive.candidate n k i))
      (69*n+18):=by
  have hsetup:Spec B (fun σ => σ.vars "catalog.k"=k∧ σ.vars "catalog.i"=i) prepareCandidate
      (fun _ τ => τ.vars "subset.need"=k∧ τ.vars "subset.rank"=i) 4:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "catalog.k") k) (@Eq Nat (Env.vars σ "catalog.i") i)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "subset.need") k) (@Eq Nat (Env.vars τ "subset.rank") i)) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B prepareCandidate σ σ' ((4:Nat))) (c0 σ'); let c2:Nat:=Env.vars (Env.setVar σ "subset.need" (Env.vars σ "catalog.k")) "catalog.i"; let c3:Env:=Env.setVar (Env.setVar σ "subset.need" (Env.vars σ "catalog.k")) "subset.rank" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "catalog.k")); let c7:Nat:=c5 (Expr.size (Expr.var "catalog.i")); let c8:String→ Nat:=Env.vars c3; @And.casesOn (@Eq Nat (Env.vars σ "catalog.k") k) (@Eq Nat (Env.vars σ "catalog.i") i) (fun (x:And (@Eq Nat (Env.vars σ "catalog.k") k) (@Eq Nat (Env.vars σ "catalog.i") i)) => @Exists Env c1) a fun (left:@Eq Nat (Env.vars σ "catalog.k") k) (right:@Eq Nat (Env.vars σ "catalog.i") i) => @Exists.intro Env c1 c3 (@And.intro (Run B prepareCandidate σ c3 ((4:Nat))) (c0 c3) (RunStep.mono B prepareCandidate σ c3 (c4 c6 c7) ((4:Nat)) (RunStep.seq B (Com.assign "subset.need" (Expr.var "catalog.k")) (Com.assign "subset.rank" (Expr.var "catalog.i")) σ (Env.setVar σ "subset.need" (Env.vars σ "catalog.k")) c3 c6 c7 (RunStep.assign B σ "subset.need" (Expr.var "catalog.k") (Env.vars σ "catalog.k") (RunStep.eval_var B σ "catalog.k" (?nAX_g8030_0_0_0))) (RunStep.assign B (Env.setVar σ "subset.need" (Env.vars σ "catalog.k")) "subset.rank" (Expr.var "catalog.i") c2 (RunStep.eval_var B (Env.setVar σ "subset.need" (Env.vars σ "catalog.k")) "catalog.i" (?nAX_g8030_0_0_1)))) (?nAX_g8030_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8030_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8030_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8030_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hd,hiσ⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ ⟨hd.2.2.2.1,hiσ⟩
  have d1:=data_frame r1 (by decide) (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩:=NativeCombinations.subset_command_spec B n k i hB hi hcoeff ν
    ⟨d1.2.1,d1.2.2.1,p1.1,p1.2,d1.2.2.2.2.1,d1.2.2.2.2.2⟩
  have d2:=data_frame r2 (by decide) (by decide) (by decide) (by decide) (by decide) d1
  have hb:Prefix (encodeOutput (NativeExhaustive.candidate n k i)) "subset.bits" μ:=by
    rw [NativeCombinations.bits_encoding] at p2
    exact p2
  obtain ⟨τ,r3,p3⟩:=NativeMasks.command_spec B (NativeExhaustive.candidate n k i) (by omega) hm μ ⟨d2.1,hb⟩
  have d3:=data_frame r3 (by decide) (by decide) (by decide) (by decide) (by decide) d2
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),d3,p3⟩

def BlockInvariant (n k:ℕ) (before:List ℕ) (σ:Env):Prop:=
  Data n k σ∧ σ.vars "catalog.blockLength"=n.choose k∧ σ.vars "catalog.i"≤ n.choose k∧
  σ.vars "catalog.count"=before.length+σ.vars "catalog.i" ∧
  before.length+n.choose k≤(σ.arrs "catalog.mask").length∧
  Prefix (before++(block n k).take (σ.vars "catalog.i")) "catalog.mask" σ

theorem block_step_spec (B n k:ℕ) (before:List ℕ)
    (hB:(n+1)*(k+1)+n+k+3< B) (hm:2^n< B)
    (hsize:before.length+n.choose k+1< B) (hcoeff:∀ a≤ n,∀ b≤ k,a.choose b< B):
    Spec B (fun σ => BlockInvariant n k before σ∧ σ.vars "catalog.i"< n.choose k) blockStep
      (fun σ τ => BlockInvariant n k before τ∧ τ.vars "catalog.i"=σ.vars "catalog.i"+1)
      (69*n+29):=by
  rintro σ ⟨⟨hd,hlimit,hle,hcount,hroom,hprefix⟩,hlt⟩
  let i:=σ.vars "catalog.i"
  have hiB:i< B:=hlt.trans (hcoeff n le_rfl k le_rfl)
  have hlen:(before++(block n k).take i).length=before.length+i:=by
    rw [List.length_append,List.length_take,block_length,Nat.min_eq_left (by omega)]
  have hval:=block_entry n k i hlt
  have hib:i<(block n k).length:=by rwa [block_length]
  rw [List.getElem?_eq_getElem hib] at hval
  have hv:=Option.some.inj hval
  obtain ⟨ν,r1,p1⟩:=candidate_spec B n k i hB hiB hm hcoeff σ ⟨hd,rfl⟩
  have hiν:ν.vars "catalog.i"=i:=r1.frame_var "catalog.i" (by decide)
  have hcν:ν.vars "catalog.count"=before.length+i:=
    (r1.frame_var "catalog.count" (by decide)).trans hcount
  obtain ⟨μ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "catalog.mask" "catalog.count"
    (before++(block n k).take i) (NativeMasks.mask (NativeExhaustive.candidate n k i))
    (.var "mask.value") (by omega) (by rw [hlen]; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "catalog.mask" (by decide)] using hprefix,
      by rwa [hlen],by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ (NativeMasks.mask_bound _).trans hm⟩⟩
  have hiμ:μ.vars "catalog.i"=i:=(r2.frame_var "catalog.i" (by decide)).trans hiν
  let τ:=μ.setVar "catalog.i" (i+1)
  have r3:Run B (.assign "catalog.i" (.add (.var "catalog.i") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  have ht:τ.vars "catalog.i"=i+1:=by simp [τ]
  refine ⟨τ,rr.mono (by simp only [Expr.size]; omega),?_,ht⟩
  refine ⟨data_frame rr (by decide) (by decide) (by decide) (by decide) (by decide) hd,
    (rr.frame_var "catalog.blockLength" (by decide)).trans hlimit,by rw [ht]; omega,?_,?_,?_⟩
  · rw [ht]
    have hc:=(r3.frame_var "catalog.count" (by decide)).trans p2.2
    rw [hlen] at hc
    exact hc
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hib,hv,←List.append_assoc]
    simpa only [Prefix,r3.frame_arr "catalog.mask" (by decide)] using p2.1

theorem block_command_spec (B n k:ℕ) (before:List ℕ)
    (hB:(n+1)*(k+1)+n+k+3< B) (hm:2^n< B)
    (hsize:before.length+n.choose k+1< B) (hcoeff:∀ a≤ n,∀ b≤ k,a.choose b< B):
    Spec B (fun σ => Data n k σ∧ σ.vars "catalog.blockLength"=n.choose k∧
      σ.vars "catalog.count"=before.length∧ before.length+n.choose k≤(σ.arrs "catalog.mask").length∧
      Prefix before "catalog.mask" σ) blockCommand
      (fun _ τ => Data n k τ∧ τ.vars "catalog.count"=before.length+n.choose k∧ Prefix (before++block n k) "catalog.mask" τ)
      ((69*n+33)*(n.choose k)+6):=by
  have hloop:=Spec.forRangeZero "catalog.i" "catalog.blockLength" (BlockInvariant n k before)
    (n.choose k) (69*n+29) (hcoeff n le_rfl k le_rfl)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (block_step_spec B n k before hB hm hsize hcoeff)
  rintro σ ⟨hd,hlimit,hcount,hroom,hprefix⟩
  have hi:BlockInvariant n k before (σ.setVar "catalog.i" 0):=by
    refine ⟨?_,?_,by simp,?_,hroom,?_⟩
    · simpa [Data,Prefix] using hd
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlimit
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.add_zero] using hcount
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using hprefix
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr,p.1.1,?_,?_⟩
  · simpa only [p.2] using p.1.2.2.2.1
  · have htake:(block n k).take (n.choose k)=block n k:=
      List.take_of_length_le (by rw [block_length])
    simpa only [p.2,htake] using p.1.2.2.2.2.2

theorem prepare_spec (B n k:ℕ) (hB:(n+1)*(k+1)+n+k+3< B)
    (hcoeff:∀ a≤ n,∀ b≤ k,a.choose b< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "catalog.k"=k∧
      (n+1)*(k+1)≤(σ.arrs "choose.table").length∧ n≤(σ.arrs "subset.bits").length) prepare
      (fun _ τ => Data n k τ∧ τ.vars "catalog.blockLength"=n.choose k)
      (54*(n+1)*(k+1)+27):=by
  have hsetup:Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "catalog.k"=k)
      (.seq (.assign "choose.n" (.var "graph.n")) (.assign "choose.k" (.var "catalog.k")))
      (fun _ τ => τ.vars "choose.n"=n∧ τ.vars "choose.k"=k) 4:=by
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.k") k)) => let c0:Com:=Com.seq (Com.assign "choose.n" (Expr.var "graph.n")) (Com.assign "choose.k" (Expr.var "catalog.k")); let c1:Env→ Nat→ Prop:=Run B c0 σ; let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "choose.n") n) (@Eq Nat (Env.vars τ "choose.k") k)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (c1 σ' ((4:Nat))) (c2 σ'); let c4:Nat:=Env.vars (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "catalog.k"; let c5:Env:=Env.setVar (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "choose.k" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.var "graph.n")); let c9:Nat:=c7 (Expr.size (Expr.var "catalog.k")); let c10:String→ Nat:=Env.vars c5; @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.k") k) (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.k") k)) => @Exists Env c3) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "catalog.k") k) => @Exists.intro Env c3 c5 (@And.intro (c1 c5 ((4:Nat))) (c2 c5) (RunStep.mono B c0 σ c5 (c6 c8 c9) ((4:Nat)) (RunStep.seq B (Com.assign "choose.n" (Expr.var "graph.n")) (Com.assign "choose.k" (Expr.var "catalog.k")) σ (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) c5 c8 c9 (RunStep.assign B σ "choose.n" (Expr.var "graph.n") (Env.vars σ "graph.n") (RunStep.eval_var B σ "graph.n" (?nAX_g8037_0_0_0))) (RunStep.assign B (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "choose.k" (Expr.var "catalog.k") c4 (RunStep.eval_var B (Env.setVar σ "choose.n" (Env.vars σ "graph.n")) "catalog.k" (?nAX_g8037_0_0_1)))) (?nAX_g8037_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8037_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8037_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8037_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hn,hk,hroom,hbits⟩
  obtain ⟨ν,r1,p1⟩:=hsetup σ ⟨hn,hk⟩
  obtain ⟨μ,r2,p2⟩:=NativeCombinations.command_spec B n k hB hcoeff ν
    ⟨p1.1,p1.2,by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  have r12:=r1.seq r2
  have hcn:μ.vars "choose.n"=n:=(r2.frame_var "choose.n" (by decide)).trans p1.1
  have hkμ:μ.vars "catalog.k"=k:=(r12.frame_var "catalog.k" (by decide)).trans hk
  have hindex:n*(k+1)+k<(NativeCombinations.table n k).length:=by
    rw [NativeCombinations.table_length]
    nlinarith
  have hget:=p2.1 (n*(k+1)+k) hindex
  have he:=NativeCombinations.table_coordinate n k n k le_rfl le_rfl
  rw [List.getElem?_eq_getElem hindex] at he
  rw [Option.some.inj he] at hget
  have hval:(Expr.get "choose.table"
      (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k"))).evalB B μ=some (n.choose k):=by
    apply evalB_get _ hget (hcoeff n le_rfl k le_rfl)
    apply evalB_bin (op:=.add) _ _ (by change n*(k+1)+k< B; nlinarith)
    · apply evalB_bin (op:=.mul) _ _ (by change n*(k+1)< B; nlinarith)
      · rw [evalB_var_iff]; exact ⟨hcn.symm,hcn ▸ (by omega)⟩
      · rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (by omega)⟩
    · rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ (by omega)⟩
  let τ:=μ.setVar "catalog.blockLength" (n.choose k)
  have r3:Run B (.assign "catalog.blockLength" (.get "choose.table"
      (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k")))) μ τ 7:=Run.assign hval
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by omega),?_,by simp [τ]⟩
  refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (r3.frame_var "choose.n" (by decide)).trans hcn,
    (r3.frame_var "choose.cols" (by decide)).trans p2.2,
    (rr.frame_var "catalog.k" (by decide)).trans hk,?_,?_⟩
  · simpa only [Prefix,r3.frame_arr "choose.table" (by decide)] using p2.1
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def rows (n q:ℕ):List ℕ:=(List.range q).flatMap (block n)

theorem rows_zero (n:ℕ):rows n 0=[]:=rfl

theorem rows_succ (n q:ℕ):rows n (q+1)=rows n q++block n q:=by
  simp only [rows,List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem rows_length_mono (n:ℕ):Monotone (fun q => (rows n q).length):=by
  apply monotone_nat_of_le_succ
  intro q
  rw [rows_succ,List.length_append]
  omega

theorem rows_length_step (n q:ℕ):(rows n (q+1)).length=(rows n q).length+n.choose q:=by
  rw [rows_succ,List.length_append,block_length]

theorem rows_exact (n r:ℕ):rows n (r+3)=
    (CoordinateCatalog.catalog n r).map (fun A => NativeMasks.mask A.val):=by
  change rows n (r+3)=(CoordinateCatalog.catalog n r).map (NativeMasks.mask ∘ Subtype.val)
  rw [←List.map_map,NativeCatalogOrder.catalog_values]
  simp only [rows,RationalConditioning.candidates,List.map_flatMap]
  rfl

def OuterData (n R:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "catalog.limit"=R+1∧
  (n+1)*(R+1)≤(σ.arrs "choose.table").length∧ n≤(σ.arrs "subset.bits").length∧
  (rows n (R+1)).length≤(σ.arrs "catalog.mask").length

theorem outer_data_frame {B n R K:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"catalog.limit"∉c.wvars)
    (hσ:OuterData n R σ):OuterData n R τ:=by
  rcases hσ with ⟨hn,hl,ht,hb,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.limit" h1).trans hl,?_,?_,?_⟩
  all_goals rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def OuterInvariant (n R:ℕ) (σ:Env):Prop:=
  OuterData n R σ∧ σ.vars "catalog.k"≤ R+1∧
  σ.vars "catalog.count"=(rows n (σ.vars "catalog.k")).length∧
  Prefix (rows n (σ.vars "catalog.k")) "catalog.mask" σ

theorem outer_step_spec (B n R:ℕ) (hB:(n+1)*(R+1)+n+R+3< B) (hm:2^n< B)
    (hsize:(rows n (R+1)).length+1< B) (hcoeff:∀ a≤ n,∀ b≤ R,a.choose b< B):
    Spec B (fun σ => OuterInvariant n R σ∧ σ.vars "catalog.k"< R+1) outerStep
      (fun σ τ => OuterInvariant n R τ∧ τ.vars "catalog.k"=σ.vars "catalog.k"+1)
      (54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+37):=by
  rintro σ ⟨⟨hd,hle,hcount,hprefix⟩,hlt⟩
  let k:=σ.vars "catalog.k"
  have hk:k≤ R:=by omega
  have htable:(n+1)*(k+1)≤(n+1)*(R+1):=Nat.mul_le_mul_left _ (by omega)
  have hb:(n+1)*(k+1)+n+k+3< B:=by omega
  have hc:∀ a≤ n,∀ b≤ k,a.choose b< B:=fun a ha b hbk => hcoeff a ha b (hbk.trans hk)
  have hrows:=rows_length_mono n (show k+1≤ R+1 by omega)
  have hroom:(rows n k).length+n.choose k≤(rows n (R+1)).length:=by
    simpa only [rows_length_step] using hrows
  obtain ⟨ν,r1,p1⟩:=prepare_spec B n k hb hc σ ⟨hd.1,rfl,htable.trans hd.2.2.1,hd.2.2.2.1⟩
  have d1:=outer_data_frame r1 (by decide) (by decide) hd
  have hkν:ν.vars "catalog.k"=k:=r1.frame_var "catalog.k" (by decide)
  obtain ⟨μ,r2,p2⟩:=block_command_spec B n k (rows n k) hb hm (by omega) hc ν
    ⟨p1.1,p1.2,(r1.frame_var "catalog.count" (by decide)).trans hcount,
      hroom.trans d1.2.2.2.2,
      by simpa only [Prefix,r1.frame_arr "catalog.mask" (by decide)] using hprefix⟩
  have hkμ:μ.vars "catalog.k"=k:=(r2.frame_var "catalog.k" (by decide)).trans hkν
  let τ:=μ.setVar "catalog.k" (k+1)
  have r3:Run B (.assign "catalog.k" (.add (.var "catalog.k") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ (by omega)⟩) (evalB_lit (by omega))
      (by change k+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  have ht:τ.vars "catalog.k"=k+1:=by simp [τ]
  refine ⟨τ,rr.mono ?_,?_,ht⟩
  · have h1:=Nat.mul_le_mul_left 54 htable
    have h2:=Nat.mul_le_mul_left (69*n+33) (show n.choose k≤(rows n (R+1)).length by omega)
    nlinarith
  · refine ⟨outer_data_frame rr (by decide) (by decide) hd,by rw [ht]; omega,?_,?_⟩
    · rw [ht,rows_length_step]
      exact (r3.frame_var "catalog.count" (by decide)).trans p2.2.1
    · rw [ht,rows_succ]
      simpa only [Prefix,r3.frame_arr "catalog.mask" (by decide)] using p2.2.2

theorem command_spec (B n R:ℕ) (hB:(n+1)*(R+1)+n+R+3< B) (hm:2^n< B)
    (hsize:(rows n (R+1)).length+1< B) (hcoeff:∀ a≤ n,∀ b≤ R,a.choose b< B):
    Spec B (OuterData n R) command
      (fun _ τ => OuterData n R τ∧ τ.vars "catalog.count"=(rows n (R+1)).length∧
        Prefix (rows n (R+1)) "catalog.mask" τ)
      ((54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+41)*(R+1)+8):=by
  have hloop:=Spec.forRangeZero "catalog.k" "catalog.limit" (OuterInvariant n R)
    (R+1) (54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+37) (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (outer_step_spec B n R hB hm hsize hcoeff)
  rintro σ hd
  let ν:=σ.setVar "catalog.count" 0
  have r1:Run B (.assign "catalog.count" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:OuterInvariant n R (ν.setVar "catalog.k" 0):=by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa [ν,OuterData] using hd
    · simp [ν,rows_zero]
    · simp only [vars_setVar,if_true,rows_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_,?_⟩
  · simpa only [p2.2] using p2.1.2.2.1
  · simpa only [p2.2] using p2.1.2.2.2

theorem rows_words (n r:ℕ):rows n (r+3)=Lax263307.NativeCatalog.words n r:=rows_exact n r

theorem rows_positive (n R:ℕ):1≤(rows n (R+1)).length:=by
  have h:=rows_length_mono n (show 1≤ R+1 by omega)
  have h1:(rows n 1).length=1:=by
    rw [show 1=0+1 from rfl,rows_length_step,rows_zero]
    simp
  simpa only [h1] using h

theorem coefficient_bound (n R a b:ℕ) (ha:a≤ n) (hb:b≤ R):
    a.choose b≤(rows n (R+1)).length:=by
  have h:=rows_length_mono n (Nat.add_le_add_right hb 1)
  have hh:(rows n b).length+n.choose b≤(rows n (R+1)).length:=by
    simpa only [rows_length_step] using h
  exact (Nat.choose_le_choose b ha).trans (by omega)

open Lax109476Proofs

end Lax263307Proofs.NativeCatalog

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

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (h0:"graph.n"∉c.wvars) (h1:"catalog.count"∉c.wvars)
    (h2:"catalog.mask"∉c.warrs) (h3:"search.graph"∉c.warrs) (hσ:Data G r σ):Data G r τ:=by
  rcases hσ with ⟨hn,hc,hm,hg,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.count" h1).trans hc,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "catalog.mask" h2] using hm
  · simpa only [Prefix,rr.frame_arr "search.graph" h3] using hg
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

theorem read_mask_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readMask
      (fun _ τ => Data G r τ∧ τ.vars "unpack.mask"=NativeMasks.mask (atIndex n r i)) 3:=by
  rintro σ ⟨hd,hi⟩
  have hlen:(Lax263307.NativeCatalog.words n r).length=N n r:=by simp [Lax263307.NativeCatalog.words]
  have hget:=hd.2.2.1 i.val (by rw [hlen]; exact i.isLt)
  have hw:(Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i):=by
    simp only [Lax263307.NativeCatalog.words,List.getElem_map]
    rfl
  rw [hw] at hget
  let τ:=σ.setVar "unpack.mask" (NativeMasks.mask (atIndex n r i))
  have rr:Run B readMask σ τ 3:=Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hget ((NativeMasks.mask_bound _).trans hm))
  exact ⟨τ,rr,data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,by simp [τ]⟩

theorem prepare_set_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) prepareSet
      (fun _ τ => Data G r τ∧ Prefix (encodeOutput (atIndex n r i)) "subset.bits" τ∧
        τ.vars "unpack.card"=(atIndex n r i).card) (21*n+11):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=read_mask_spec B G r i hN hm σ ⟨hd,hi⟩
  obtain ⟨τ,r2,p2⟩:=NativeMaskUnpack.command_spec B (atIndex n r i) hB hm ν
    ⟨p1.1.1,p1.2,p1.1.2.2.2.2⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,p2⟩

theorem read_card_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n+2< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readCard
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=(atIndex n r i).card) (21*n+13):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i hB hN hm σ ⟨hd,hi⟩
  let τ:=ν.setVar "fill.value" (atIndex n r i).card
  have r2:Run B (.assign "fill.value" (.var "unpack.card")) ν τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p1.2.2.symm,p1.2.2 ▸ (NativeMaskUnpack.card_bound _).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq r2).mono (by omega),
    data_frame G r r2 (by decide) (by decide) (by decide) (by decide) p1.1,by simp [τ]⟩

theorem read_independent_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i:Fin (N n r)) (hB:n*n+n+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "fill.i"=i.val) readIndependent
      (fun _ τ => Data G r τ∧ τ.vars "fill.value"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)
      (38*n*n+21*n+25):=by
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩:=prepare_set_spec B G r i (by omega) hN hm σ ⟨hd,hi⟩
  obtain ⟨μ,r2,p2⟩:=NativeIndependentTest.command_spec B G (atIndex n r i) "search.graph" "subset.bits" hB ν
    ⟨p1.1.1,p1.1.2.2.2.1,p1.2.1⟩
  have hok:μ.vars "test.ok"=if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0:=by
    split_ifs with h
    · exact p2.2.2.mpr h
    · have hh:μ.vars "test.ok"≠1:=fun h1 => h (p2.2.2.mp h1)
      omega
  let τ:=μ.setVar "fill.value" (μ.vars "test.ok")
  have r3:Run B (.assign "fill.value" (.var "test.ok")) μ τ 2:=Run.assign (evalB_var (p2.2.1.trans_lt (by omega)))
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),data_frame G r rr (by decide) (by decide) (by decide) (by decide) hd,
    by simpa only [τ,vars_setVar,if_true] using hok⟩

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (hB:n*n+n+3< B) (hN:N n r+1< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ N n r≤(σ.arrs "catalog.card").length∧ N n r≤(σ.arrs "catalog.independent").length)
      command (fun _ τ => Data G r τ∧ Prefix (cards n r) "catalog.card" τ∧ Prefix (independent G r) "catalog.independent" τ)
      ((38*n*n+42*n+60)*(N n r)+14):=by
  have hc:(cards n r).length=N n r:=List.length_ofFn
  have hi:(independent G r).length=N n r:=List.length_ofFn
  have hcards:=NativeTabulate.command_spec B (cards n r) "catalog.card" (Data G r) readCard (21*n+13)
    (by rwa [hc]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega))
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i hi; simpa only [cards,List.getElem_ofFn] using read_card_spec B G r ⟨i,by rwa [hc] at hi⟩ (by omega) (by omega) hm)
  have hind:=NativeTabulate.command_spec B (independent G r) "catalog.independent" (Data G r) readIndependent (38*n*n+21*n+25)
    (by rwa [hi]) (by intro z hz; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz; split_ifs <;> omega)
    (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,Prefix] using h)
    (by intro σ τ rr h; exact data_frame G r rr (by decide) (by decide) (by decide) (by decide) h)
    (by intro i h; simpa only [independent,List.getElem_ofFn] using read_independent_spec B G r ⟨i,by rwa [hi] at h⟩ hB (by omega) hm)
  rintro σ ⟨hd,hcr,hir⟩
  let ν:=σ.setVar "fill.length" (N n r)
  have r1:Run B (.assign "fill.length" (.var "catalog.count")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (by omega)⟩)
  have d1:=data_frame G r r1 (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩:=hcards ν ⟨d1,by simp [ν,hc],by simpa only [ν,arrs_setVar,hc] using hcr⟩
  have hlength:μ.vars "fill.length"=(independent G r).length:=by
    rw [r2.frame_var "fill.length" (by decide)]
    simp [ν,hi]
  obtain ⟨τ,r3,p3⟩:=hind μ ⟨p2.1,hlength,by rw [hi,Lax455465Proofs.RamFrames.run_array_length r2]; exact hir⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hc,hi]; nlinarith),p3.1,?_,p3.2⟩
  simpa only [Prefix,r3.frame_arr "catalog.card" (by decide)] using p2.2

end Lax263307Proofs.NativeCatalogMetadata

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks
open Lax263307

def same {n:ℕ} (A J:Finset (Fin n)):ℕ:=if A=J then 1 else 0

theorem same_le {n:ℕ} (A J:Finset (Fin n)):same A J≤1:=by unfold same; split_ifs <;> omega

theorem same_masks {n:ℕ} (A J:Finset (Fin n)):
    (if mask A=mask J then 1 else 0)=same A J:=by simp only [(mask_injective n).eq_iff,same]

theorem same_single_row {n r:ℕ} (A:Finset (Fin n)) (j:MomentLP.Index n r):
    (same A (CoordinateCatalog.indexing n r j).val:ℚ)=MomentLP.singleRow A j:=by
  simp only [same,MomentLP.singleRow,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem compare_spec (B a b:ℕ) (dst left right:String) (ha:a< B) (hb:b< B) (h1:1< B):
    Spec B (fun σ => σ.vars left=a∧ σ.vars right=b) (compare dst left right)
      (fun _ τ => τ.vars dst=if a=b then 1 else 0) 6:=by
  rintro σ ⟨hleft,hright⟩
  have hcond:=evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ ha⟩)
    (by rw [evalB_var_iff]; exact ⟨hright.symm,hright ▸ hb⟩)
  by_cases h:a=b
  · have hc:(Cond.eq (.var left) (.var right)).evalB B σ=some true:=by simpa only [h,beq_self_eq_true] using hcond
    have hr:=Run.ite_true (d:=.assign dst (.lit 0)) hc (Run.assign (x:=dst) (evalB_lit h1))
    exact ⟨_,hr,by simp [h]⟩
  · have hc:(Cond.eq (.var left) (.var right)).evalB B σ=some false:=by simpa only [beq_eq_false_iff_ne.mpr h] using hcond
    have hr:=Run.ite_false (c:=.assign dst (.lit 1)) hc (Run.assign (x:=dst) (evalB_lit (by omega:0< B)))
    exact ⟨_,hr,by simp [h]⟩

theorem insert_spec {n:ℕ} (B:ℕ) (A:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "row.v"=v.val) insertCommand
      (fun _ τ => τ.vars "row.insert"=mask (insert v A)) 6:=by
  rintro σ ⟨hA,hv⟩
  have hAv:mask A< B:=(mask_bound _).trans hm
  have hvB:v.val< B:=v.isLt.trans (by omega)
  have hpow:2^v.val< B:=(Nat.pow_lt_pow_right (by omega) v.isLt).trans hm
  have hins:mask (insert v A)< B:=(mask_bound _).trans hm
  have hval:(Expr.or (.var "row.mask") (.shiftl (.lit 1) (.var "row.v"))).evalB B σ=some (mask (insert v A)):=by
    have hh:=evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hA.symm,hA ▸ hAv⟩)
      (evalB_bin (op:=.shiftl) (evalB_lit (show 1< B by omega))
        (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ hvB⟩) (by simpa only [Bop.apply_shiftl,one_mul] using hpow))
      (by change Nat.lor (mask A) (1*2^v.val)< B; simpa only [one_mul,←mask_insert] using hins)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←mask_insert] using hh
  exact ⟨_,Run.assign hval,by simp⟩

theorem monotone_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => τ.vars "coefficient.positive"=same (insert v A) J∧ τ.vars "coefficient.negative"=same A J) 18:=by
  rintro σ ⟨hA,hJ,hv⟩
  obtain ⟨ν,r1,p1⟩:=insert_spec B A v hB hm σ ⟨hA,hv⟩
  obtain ⟨μ,r2,p2⟩:=compare_spec B (mask (insert v A)) (mask J) "coefficient.positive" "row.insert" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨p1,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have r12:=r1.seq r2
  obtain ⟨τ,r3,p3⟩:=compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) μ
    ⟨(r12.frame_var "row.mask" (by decide)).trans hA,(r12.frame_var "column.mask" (by decide)).trans hJ⟩
  refine ⟨τ,r1.seq (r2.seq r3),?_,?_⟩
  · rw [r3.frame_var "coefficient.positive" (by decide),p2,same_masks]
  · simpa only [same_masks] using p3

theorem monotone_value {n r:ℕ} (A:Finset (Fin n)) (v:Fin n) (j:MomentLP.Index n r):
    (same (insert v A) (CoordinateCatalog.indexing n r j).val:ℚ)-same A (CoordinateCatalog.indexing n r j).val=
      MomentLP.monotoneRow A v j:=by rw [same_single_row,same_single_row]; rfl

def matchCount {n:ℕ} (A J:Finset (Fin n)) (i:ℕ):ℕ:=
  ((List.finRange n).take i).countP fun v => decide (insert v A=J)

theorem matches_zero {n:ℕ} (A J:Finset (Fin n)):matchCount A J 0=0:=by simp [matchCount]

theorem matches_bound {n:ℕ} (A J:Finset (Fin n)) (i:ℕ):matchCount A J i≤ n:=by
  have h:matchCount A J i≤((List.finRange n).take i).length:=List.countP_le_length
  simp only [List.length_take,List.length_finRange] at h
  omega

theorem matches_succ {n:ℕ} (A J:Finset (Fin n)) (i:ℕ) (hi:i< n):
    matchCount A J (i+1)=matchCount A J i+same (insert ⟨i,hi⟩ A) J:=by
  have hilen:i<(List.finRange n).length:=by simpa using hi
  simp only [matchCount,List.take_succ_eq_append_getElem hilen,List.countP_append,List.countP_singleton,
    List.getElem_finRange,same,decide_eq_true_eq]
  rfl

theorem countP_as_sum {α:Type*} (xs:List α) (f:α→ Bool):
    xs.countP f=(xs.map fun x => if f x then 1 else 0).sum:=by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h:f a <;> simp [h,ih,Nat.add_comm]

theorem matches_value {n r:ℕ} (A:Finset (Fin n)) (j:MomentLP.Index n r):
    (matchCount A (CoordinateCatalog.indexing n r j).val n:ℚ)=∑ v,MomentLP.singleRow (insert v A) j:=by
  rw [matchCount,List.take_of_length_le (by simp),countP_as_sum,←List.ofFn_eq_map,List.sum_ofFn]
  simp [MomentLP.singleRow]

theorem mass_value {n r:ℕ} (A:Finset (Fin n)) (k:ℕ) (j:MomentLP.Index n r):
    (matchCount A (CoordinateCatalog.indexing n r j).val n:ℚ)-(k*same A (CoordinateCatalog.indexing n r j).val:ℕ)=
      MomentLP.massRow A k j:=by
  rw [matches_value,Nat.cast_mul,same_single_row]
  rfl

def CountInvariant {n:ℕ} (A J:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧
  σ.vars "row.v"≤ n∧ σ.vars "coefficient.positive"=matchCount A J (σ.vars "row.v")

theorem count_step_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => CountInvariant A J σ∧ σ.vars "row.v"< n) countStep
      (fun σ τ => CountInvariant A J τ∧ τ.vars "row.v"=σ.vars "row.v"+1) 18:=by
  rintro σ ⟨⟨hn,hA,hJ,hle,hcount⟩,hlt⟩
  let i:=σ.vars "row.v"
  let v:Fin n:= ⟨i,hlt⟩
  have hiB:i< B:=by omega
  obtain ⟨ν,r1,p1⟩:=insert_spec B A v hB hm σ ⟨hA,rfl⟩
  have hcolν:ν.vars "column.mask"=mask J:=(r1.frame_var "column.mask" (by decide)).trans hJ
  have hcountν:ν.vars "coefficient.positive"=matchCount A J i:=
    (r1.frame_var "coefficient.positive" (by decide)).trans hcount
  have hcB:matchCount A J i< B:=(matches_bound A J i).trans_lt (by omega)
  have hc1B:matchCount A J i+1< B:=by have h:=matches_bound A J i; omega
  have heval:=evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (mask_bound _).trans hm⟩)
    (by rw [evalB_var_iff]; exact ⟨hcolν.symm,hcolν ▸ (mask_bound _).trans hm⟩)
  obtain ⟨μ,r2,p2⟩:∃ μ,Run B countBranch ν μ 8∧ μ.vars "coefficient.positive"=matchCount A J (i+1):=by
    by_cases h:insert v A=J
    · have he:mask (insert v A)=mask J:=congrArg mask h
      have hb:(Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some true:=by
        simpa only [he,beq_self_eq_true] using heval
      have hv:(Expr.add (.var "coefficient.positive") (.lit 1)).evalB B ν=some (matchCount A J i+1):=
        evalB_bin (op:=.add)
          (by rw [evalB_var_iff]; exact ⟨hcountν.symm,hcountν ▸ hcB⟩) (evalB_lit (by omega)) hc1B
      refine ⟨_,Run.ite_true (d:=.skip) hb (Run.assign hv),?_⟩
      simp only [vars_setVar,if_true,matches_succ A J i hlt,same,show insert ⟨i,hlt⟩ A=J from h,if_true]
    · have he:mask (insert v A)≠mask J:=fun he => h ((mask_injective n) he)
      have hb:(Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some false:=by
        simpa only [beq_eq_false_iff_ne.mpr he] using heval
      refine ⟨ν,(Run.ite_false (c:=.assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))) hb Run.skip).mono (by decide),?_⟩
      simpa only [matches_succ A J i hlt,same,show ¬insert ⟨i,hlt⟩ A=J from h,if_false,Nat.add_zero] using hcountν
  have r12:=r1.seq r2
  have hiμ:μ.vars "row.v"=i:=r12.frame_var "row.v" (by decide)
  let τ:=μ.setVar "row.v" (i+1)
  have r3:Run B (.assign "row.v" (.add (.var "row.v") (.lit 1))) μ τ 4:=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) (evalB_lit (by omega)) (by change i+1< B; omega))
  have rr:=r1.seq (r2.seq r3)
  have ht:τ.vars "row.v"=i+1:=by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "row.mask" (by decide)).trans hA,(rr.frame_var "column.mask" (by decide)).trans hJ,
    by rw [ht]; omega,?_⟩,ht⟩
  rw [ht,r3.frame_var "coefficient.positive" (by decide)]
  exact p2

theorem count_command_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J)
      countCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n) (22*n+8):=by
  have hloop:=Spec.forRangeZero "row.v" "graph.n" (CountInvariant A J) n 18 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1) (count_step_spec B A J hB hm)
  rintro σ ⟨hn,hA,hJ⟩
  let ν:=σ.setVar "coefficient.positive" 0
  have r1:Run B (.assign "coefficient.positive" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have r0:Run B (.assign "row.v" (.lit 0)) ν (ν.setVar "row.v" 0) 2:=Run.assign (evalB_lit (by omega))
  have hi:CountInvariant A J (ν.setVar "row.v" 0):=by
    refine ⟨?_,?_,?_,by simp,?_⟩
    · exact ((r1.seq r0).frame_var "graph.n" (by decide)).trans hn
    · exact ((r1.seq r0).frame_var "row.mask" (by decide)).trans hA
    · exact ((r1.seq r0).frame_var "column.mask" (by decide)).trans hJ
    · change 0=matchCount A J 0
      exact (matches_zero A J).symm
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [p2.2] using p2.1.2.2.2.2⟩

theorem mass_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (k:ℕ) (hB:n+2< B) (hk:k< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n∧ τ.vars "coefficient.negative"=k*same A J)
      (22*n+18):=by
  rintro σ ⟨hn,hA,hJ,hkσ⟩
  obtain ⟨ν,r1,p1⟩:=count_command_spec B A J hB hm σ ⟨hn,hA,hJ⟩
  obtain ⟨μ,r2,p2⟩:=compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨(r1.frame_var "row.mask" (by decide)).trans hA,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have hb:μ.vars "coefficient.negative"=same A J:=by simpa only [same_masks] using p2
  have r12:=r1.seq r2
  have hkμ:μ.vars "row.k"=k:=(r12.frame_var "row.k" (by decide)).trans hkσ
  have hprod:k*same A J< B:=(by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J):k*same A J≤ k).trans_lt hk
  let τ:=μ.setVar "coefficient.negative" (k*same A J)
  have r3:Run B (.assign "coefficient.negative" (.mul (.var "row.k") (.var "coefficient.negative"))) μ τ 4:=Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ hk⟩)
      (by rw [evalB_var_iff]; exact ⟨hb.symm,hb ▸ (same_le A J).trans_lt (by omega)⟩) hprod)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,by simp [τ]⟩
  exact ((r2.seq r3).frame_var "coefficient.positive" (by decide)).trans p1

end Lax263307Proofs.NativeMomentRows

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata

theorem activate_spec (B c r:ℕ) (hB:c+r+3< B):
    Spec B (fun σ => σ.vars "row.card"=c∧ σ.vars "moment.r"=r) activate
      (fun _ τ => τ.vars "row.active"=if c≤ r+1 then 1 else 0) 8:=by
  by_cases h:c< r+2
  · have h':c≤ r+1:=by omega
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 r ((1:Nat)); let c2:Nat:= @ite Nat (Nat.le c c1) (Nat.decLe c c1) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "row.active") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B activate σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat:=c0 (Env.vars σ "moment.r") ((2:Nat)); let c7:Prop:=Nat.lt (Env.vars σ "row.card") c6; let c8:Prop:=Not c7; let c9:Env:=Env.setVar σ "row.active" ((1:Nat)); let c10:Nat→ Nat:=c0 ((1:Nat)); let c11:Expr:=Expr.add (Expr.var "moment.r") (Expr.lit ((2:Nat))); let c12:Cond:=Cond.lt (Expr.var "row.card") c11; let c13:Nat→ Nat:=c0 (c10 (Cond.size c12)); let c14:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c15:Com:=Com.assign "row.active" (Expr.lit ((1:Nat))); let c16:Com:=Com.assign "row.active" (Expr.lit ((0:Nat))); let c17:Env:=Env.setVar σ "row.active" ((0:Nat)); let c18:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); @And.casesOn (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r) (fun (x:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => c5) a fun (left:@Eq Nat (Env.vars σ "row.card") c) (right:@Eq Nat (Env.vars σ "moment.r") r) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c5) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c4 c9 (@And.intro (Run B activate σ c9 ((8:Nat))) (c3 c9) (RunStep.mono B activate σ c9 (c13 c14) ((8:Nat)) (RunStep.ite_true B c12 c15 c16 σ c9 c14 (RunStep.cond_lt_true B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_0_0_0)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_0_0_1)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_0_0_2)) (?nAX_g8118_0_0_3)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8118_0_0_4)))) (?nAX_g8118_0_0_5)) ?_)) fun (hcase:c8) => @Exists.intro Env c4 c17 (@And.intro (Run B activate σ c17 ((8:Nat))) (c3 c17) (RunStep.mono B activate σ c17 (c13 c18) ((8:Nat)) (RunStep.ite_false B c12 c15 c16 σ c17 c18 (RunStep.cond_lt_false B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_0_0_6)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_0_0_7)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_0_0_8)) (?nAX_g8118_0_0_9)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8118_0_0_10)))) (?nAX_g8118_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8118_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
  · have h':¬c≤ r+1:=by omega
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 r ((1:Nat)); let c2:Nat:= @ite Nat (Nat.le c c1) (Nat.decLe c c1) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "row.active") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B activate σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat:=c0 (Env.vars σ "moment.r") ((2:Nat)); let c7:Prop:=Nat.lt (Env.vars σ "row.card") c6; let c8:Prop:=Not c7; let c9:Env:=Env.setVar σ "row.active" ((1:Nat)); let c10:Nat→ Nat:=c0 ((1:Nat)); let c11:Expr:=Expr.add (Expr.var "moment.r") (Expr.lit ((2:Nat))); let c12:Cond:=Cond.lt (Expr.var "row.card") c11; let c13:Nat→ Nat:=c0 (c10 (Cond.size c12)); let c14:Nat:=c10 (Expr.size (Expr.lit ((1:Nat)))); let c15:Com:=Com.assign "row.active" (Expr.lit ((1:Nat))); let c16:Com:=Com.assign "row.active" (Expr.lit ((0:Nat))); let c17:Env:=Env.setVar σ "row.active" ((0:Nat)); let c18:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); @And.casesOn (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r) (fun (x:And (@Eq Nat (Env.vars σ "row.card") c) (@Eq Nat (Env.vars σ "moment.r") r)) => c5) a fun (left:@Eq Nat (Env.vars σ "row.card") c) (right:@Eq Nat (Env.vars σ "moment.r") r) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c5) (Classical.em c7) (fun (hcase:c7) => @Exists.intro Env c4 c9 (@And.intro (Run B activate σ c9 ((8:Nat))) (c3 c9) (RunStep.mono B activate σ c9 (c13 c14) ((8:Nat)) (RunStep.ite_true B c12 c15 c16 σ c9 c14 (RunStep.cond_lt_true B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_1_0_0)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_1_0_1)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_1_0_2)) (?nAX_g8118_1_0_3)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8118_1_0_4)))) (?nAX_g8118_1_0_5)) ?_)) fun (hcase:c8) => @Exists.intro Env c4 c17 (@And.intro (Run B activate σ c17 ((8:Nat))) (c3 c17) (RunStep.mono B activate σ c17 (c13 c18) ((8:Nat)) (RunStep.ite_false B c12 c15 c16 σ c17 c18 (RunStep.cond_lt_false B σ (Expr.var "row.card") c11 (Env.vars σ "row.card") c6 (RunStep.eval_var B σ "row.card" (?nAX_g8118_1_0_6)) (RunStep.eval_add B σ (Expr.var "moment.r") (Expr.lit ((2:Nat))) (Env.vars σ "moment.r") ((2:Nat)) (RunStep.eval_var B σ "moment.r" (?nAX_g8118_1_0_7)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8118_1_0_8)) (?nAX_g8118_1_0_9)) hcase) (RunStep.assign B σ "row.active" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8118_1_0_10)))) (?nAX_g8118_1_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8118_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8118_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar]
    all_goals omega

def Loaded {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (σ:Env):Prop:=
  σ.vars "row.mask"=NativeMasks.mask (atIndex n r i)∧
  σ.vars "column.mask"=NativeMasks.mask (atIndex n r j)∧
  σ.vars "row.card"=(atIndex n r i).card∧
  σ.vars "row.independent"=(if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)

theorem mask_word (n r:ℕ) (i:Fin (N n r)):
    (Lax263307.NativeCatalog.words n r)[i.val]?=some (NativeMasks.mask (atIndex n r i)):=by
  rw [Lax263307.NativeCatalog.words,List.getElem?_map,List.getElem?_eq_getElem i.isLt]
  rfl

theorem load_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (hB:n+r+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "row.index"=i.val∧ σ.vars "column.index"=j.val)
      load (fun _ τ => Loaded G r i j τ) 12:=by
  rintro σ ⟨hd,hi,hj⟩
  have hlen:(Lax263307.NativeCatalog.words n r).length=N n r:=by simp [Lax263307.NativeCatalog.words]
  have hmask:∀ l:Fin (N n r),(σ.arrs "catalog.mask")[l.val]?=some (NativeMasks.mask (atIndex n r l)):=by
    intro l
    have hli:l.val<(Lax263307.NativeCatalog.words n r).length:=by rw [hlen]; exact l.isLt
    have hh:=hd.1.2.2.1 l.val hli
    have he:=mask_word n r l
    rw [List.getElem?_eq_getElem hli] at he
    exact hh.trans he
  have hcard:(σ.arrs "catalog.card")[i.val]?=some (atIndex n r i).card:=by
    have hh:=hd.2.1 i.val (by simp [cards])
    simpa only [cards,List.getElem_ofFn] using hh
  have hind:(σ.arrs "catalog.independent")[i.val]?=
      some (if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0):=by
    have hh:=hd.2.2.1 i.val (by simp [independent])
    simpa only [independent,List.getElem_ofFn] using hh
  have hcardB:(atIndex n r i).card< B:=(NativeMaskUnpack.card_bound _).trans_lt (by omega)
  have hindB:(if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)< B:=by split_ifs <;> omega
  have hiB:=i.isLt.trans hN
  have hjB:=j.isLt.trans hN
  have hrowB:=(NativeMasks.mask_bound (atIndex n r i)).trans hm
  have hcolB:=(NativeMasks.mask_bound (atIndex n r j)).trans hm
  let ν:=σ.setVar "row.mask" (NativeMasks.mask (atIndex n r i))
  have r1:Run B (.assign "row.mask" (.get "catalog.mask" (.var "row.index"))) σ ν 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (hmask i) hrowB)
  have hiν:ν.vars "row.index"=i.val:=(r1.frame_var "row.index" (by decide)).trans hi
  let μ:=ν.setVar "row.card" (atIndex n r i).card
  have r2:Run B (.assign "row.card" (.get "catalog.card" (.var "row.index"))) ν μ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) hcard hcardB)
  have hiμ:μ.vars "row.index"=i.val:=(r2.frame_var "row.index" (by decide)).trans hiν
  let ξ:=μ.setVar "row.independent" (if G.IsIndepSet (atIndex n r i:Set (Fin n)) then 1 else 0)
  have r3:Run B (.assign "row.independent" (.get "catalog.independent" (.var "row.index"))) μ ξ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) hind hindB)
  have hjξ:ξ.vars "column.index"=j.val:=((r1.seq (r2.seq r3)).frame_var "column.index" (by decide)).trans hj
  let τ:=ξ.setVar "column.mask" (NativeMasks.mask (atIndex n r j))
  have r4:Run B (.assign "column.mask" (.get "catalog.mask" (.var "column.index"))) ξ τ 3:=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hjξ.symm,hjξ ▸ hjB⟩) (hmask j) hcolB)
  have rr:=r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr,?_,?_,?_,?_⟩
  · rw [(r2.seq (r3.seq r4)).frame_var "row.mask" (by decide)]
    exact (vars_setVar σ "row.mask" (NativeMasks.mask (atIndex n r i)) "row.mask").trans (if_pos rfl)
  · exact (vars_setVar ξ "column.mask" (NativeMasks.mask (atIndex n r j)) "column.mask").trans (if_pos rfl)
  · rw [(r3.seq r4).frame_var "row.card" (by decide)]
    exact (vars_setVar ν "row.card" (atIndex n r i).card "row.card").trans (if_pos rfl)
  · rw [r4.frame_var "row.independent" (by decide)]
    exact (vars_setVar μ "row.independent" _ "row.independent").trans (if_pos rfl)

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ)
    (i j:Fin (N n r)) (hB:n+r+3< B) (hN:N n r< B) (hm:2^n< B):
    Spec B (fun σ => Data G r σ∧ σ.vars "row.index"=i.val∧ σ.vars "column.index"=j.val)
      command (fun _ τ => Loaded G r i j τ∧ τ.vars "row.active"=if (atIndex n r i).card≤ r+1 then 1 else 0) 20:=by
  rintro σ ⟨hd,hi,hj⟩
  obtain ⟨ν,r1,p1⟩:=load_spec B G r i j hB hN hm σ ⟨hd,hi,hj⟩
  obtain ⟨τ,r2,p2⟩:=activate_spec B (atIndex n r i).card r
    (by have h:=NativeMaskUnpack.card_bound (atIndex n r i); omega) ν
    ⟨p1.2.2.1,(r1.frame_var "moment.r" (by decide)).trans hd.2.2.2⟩
  refine ⟨τ,r1.seq r2,?_,p2⟩
  simpa only [Loaded,r2.frame_var "row.mask" (by decide),r2.frame_var "column.mask" (by decide),
    r2.frame_var "row.card" (by decide),r2.frame_var "row.independent" (by decide)] using p1

end Lax263307Proofs.NativeMomentAccess

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentProduce

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks NativeMomentRows

def Value (B:ℕ) (q:ℚ) (σ:Env):Prop:=
  σ.vars "coefficient.positive"< B∧ σ.vars "coefficient.negative"< B∧
  ((σ.vars "coefficient.positive" :ℕ):ℚ)-σ.vars "coefficient.negative"=q

theorem zero_spec (B:ℕ) (hB:0< B):Spec B (fun _ => True) zeroCommand (fun _ τ => Value B 0 τ) 4:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=Value B (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c3:Env:=Env.setVar c2 "coefficient.negative" ((0:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat:=c4 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B zeroCommand σ σ' ((4:Nat))) (c1 σ')) c3 (@And.intro (Run B zeroCommand σ c3 ((4:Nat))) (c1 c3) (RunStep.mono B zeroCommand σ c3 (c4 c5 c5) ((4:Nat)) (RunStep.seq B (Com.assign "coefficient.positive" (Expr.lit ((0:Nat)))) (Com.assign "coefficient.negative" (Expr.lit ((0:Nat)))) σ c2 c3 c5 c5 (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hB)) (RunStep.assign B c2 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 hB))) (?nAX_g8126_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8126_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,Env.setVar]

theorem single_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (h1:1< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J)
      singleCommand (fun _ τ => Value B (same A J) τ) 8:=by
  rintro σ ⟨hA,hJ⟩
  obtain ⟨ν,r1,p1⟩:=compare_spec B (mask A) (mask J) "coefficient.positive" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) h1 σ ⟨hA,hJ⟩
  have hp:ν.vars "coefficient.positive"=same A J:=by simpa only [same_masks] using p1
  let τ:=ν.setVar "coefficient.negative" 0
  have r2:Run B (.assign "coefficient.negative" (.lit 0)) ν τ 2:=Run.assign (evalB_lit (by omega))
  refine ⟨τ,r1.seq r2,?_,by simp [τ]; omega,?_⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,hp] using (same_le A J).trans_lt h1
  · simp only [τ,vars_setVar,String.reduceEq,if_false,if_true,hp,Nat.cast_zero,sub_zero]

theorem monotone_value_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (v:Fin n) (hB:n+2< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => Value B ((same (insert v A) J:ℚ)-same A J) τ) 18:=by
  intro σ hσ
  obtain ⟨τ,rr,p⟩:=monotone_spec B A J v hB hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.2]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.1,p.2]

theorem mass_value_spec {n:ℕ} (B:ℕ) (A J:Finset (Fin n)) (k:ℕ) (hB:n+2< B) (hk:k< B) (hm:2^n< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "row.mask"=mask A∧ σ.vars "column.mask"=mask J∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => Value B ((matchCount A J n:ℚ)-(k*same A J:ℕ)) τ) (22*n+18):=by
  intro σ hσ
  obtain ⟨τ,rr,p⟩:=mass_spec B A J k hB hk hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (matches_bound A J n).trans_lt (by omega)
  · rw [p.2]
    exact (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J):k*same A J≤ k).trans_lt hk
  · rw [p.1,p.2]

theorem swap_spec (B:ℕ) (q:ℚ):Spec B (Value B q) swap (fun _ τ => Value B (-q) τ) 6:=by
  rintro σ ⟨hp,hn,hq⟩
  let ν:=σ.setVar "coefficient.temp" (σ.vars "coefficient.positive")
  have r1:Run B (.assign "coefficient.temp" (.var "coefficient.positive")) σ ν 2:=Run.assign (evalB_var hp)
  let μ:=ν.setVar "coefficient.positive" (σ.vars "coefficient.negative")
  have r2:Run B (.assign "coefficient.positive" (.var "coefficient.negative")) ν μ 2:=Run.assign (evalB_var hn)
  let τ:=μ.setVar "coefficient.negative" (σ.vars "coefficient.positive")
  have r3:Run B (.assign "coefficient.negative" (.var "coefficient.temp")) μ τ 2:=Run.assign (evalB_var hp)
  refine ⟨τ,r1.seq (r2.seq r3),hn,hp,?_⟩
  change (σ.vars "coefficient.negative" :ℚ)-σ.vars "coefficient.positive"=-q
  rw [←hq]
  ring

theorem guard_spec (B expected K:ℕ) (flag:String) (P:Env→ Prop) (test:Prop) [Decidable test]
    (q:ℚ) (c:Com) (hB:1< B) (hex:expected≤1)
    (hc:Spec B P c (fun _ τ => Value B q τ) K):
    Spec B (fun σ => P σ∧ σ.vars flag=if test then expected else 1-expected)
      (guard flag expected c) (fun _ τ => Value B (if test then q else 0) τ) (K+8):=by
  rintro σ ⟨hP,hflag⟩
  have heB:expected< B:=hex.trans_lt hB
  have hnB:1-expected< B:=by omega
  by_cases h:test
  · have hf:σ.vars flag=expected:=by simpa only [if_pos h] using hflag
    obtain ⟨τ,rr,p⟩:=hc σ hP
    have hb:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some true:=by
      have hh:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some (expected==expected):=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ heB⟩) (evalB_lit heB)
      simpa using hh
    exact ⟨τ,(Run.ite_true (d:=zeroCommand) hb rr).mono (by simp [Cond.size,Expr.size]; omega),by simpa only [if_pos h] using p⟩
  · have hf:σ.vars flag=1-expected:=by simpa only [if_neg h] using hflag
    obtain ⟨τ,rr,p⟩:=zero_spec B (by omega) σ trivial
    have hne:1-expected≠expected:=by omega
    have hb:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some false:=by
      have hh:(Cond.eq (.var flag) (.lit expected)).evalB B σ=some (1-expected==expected):=evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hnB⟩) (evalB_lit heB)
      simpa only [beq_eq_false_iff_ne.mpr hne] using hh
    exact ⟨τ,(Run.ite_false (c:=c) hb rr).mono (by simp [Cond.size,Expr.size]),by simpa only [if_neg h] using p⟩

end Lax263307Proofs.NativeMomentProduce

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeIntegerEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def sign (p q:ℕ):ℕ:=if p< q then 1 else 0

def magnitude (p q:ℕ):ℕ:=if p< q then q-p else p-q

theorem sign_le (p q:ℕ):sign p q≤1:=by unfold sign; split_ifs <;> omega

theorem magnitude_bound (p q:ℕ):magnitude p q≤ max p q:=by unfold magnitude; split_ifs <;> omega

theorem encoding (p q:ℕ):encodeRational ((p:ℚ)-q)=[sign p q,magnitude p q,1]:=by
  have he:(p:ℚ)-q=(((p:ℤ)-(q:ℤ):ℤ):ℚ):=by simp
  rw [he,encodeRational]
  simp only [Rat.num_intCast,Rat.den_intCast]
  have hsg:((p:ℤ)-(q:ℤ)<0)↔ p< q:=by omega
  simp only [hsg,sign,magnitude]
  by_cases h:p< q
  · simp only [if_pos h,Int.natAbs_natCast_sub_natCast_of_le h.le]
  · simp only [if_neg h,Int.natAbs_natCast_sub_natCast_of_ge (by omega:q≤ p)]

theorem normalize_spec (B p q:ℕ) (h1:1< B) (hp:p< B) (hq:q< B):
    Spec B (fun σ => σ.vars "coefficient.positive"=p∧ σ.vars "coefficient.negative"=q) normalize
      (fun _ τ => τ.vars "coefficient.sign"=sign p q∧ τ.vars "coefficient.magnitude"=magnitude p q) 10:=by
  by_cases h:p< q
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "coefficient.sign") (sign p q)) (@Eq Nat (Env.vars τ "coefficient.magnitude") (magnitude p q))) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B normalize σ σ' ((10:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:=Nat.lt (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative"); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.sign" ((1:Nat)); let c6:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c7:String→ Nat:=Env.vars c5; let c8:Nat:=c7 "coefficient.negative"; let c9:Nat:=c7 "coefficient.positive"; let c10:Nat:=c6 c8 c9; let c11:Env:=Env.setVar c5 "coefficient.magnitude" c10; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat→ Nat:=c12 (c13 (Cond.size (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")))); let c15:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive"))); let c17:Nat:=c12 c15 c16; let c18:Com:=Com.assign "coefficient.sign" (Expr.lit ((1:Nat))); let c19:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")); let c20:Com:=Com.seq c18 c19; let c21:Com:=Com.assign "coefficient.sign" (Expr.lit ((0:Nat))); let c22:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")); let c23:Com:=Com.seq c21 c22; let c24:String→ Nat:=Env.vars c11; let c25:Env:=Env.setVar σ "coefficient.sign" ((0:Nat)); let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "coefficient.positive"; let c28:Nat:=c26 "coefficient.negative"; let c29:Nat:=c6 c27 c28; let c30:Env:=Env.setVar c25 "coefficient.magnitude" c29; let c31:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c32:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative"))); let c33:Nat:=c12 c31 c32; let c34:String→ Nat:=Env.vars c30; @And.casesOn (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q) (fun (x:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => c2) a fun (left:@Eq Nat (Env.vars σ "coefficient.positive") p) (right:@Eq Nat (Env.vars σ "coefficient.negative") q) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Exists.intro Env c1 c11 (@And.intro (Run B normalize σ c11 ((10:Nat))) (c0 c11) (RunStep.mono B normalize σ c11 (c14 c17) ((10:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c11 c17 (RunStep.cond_lt_true B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_0_0_0)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_0_0_1)) hcase) (RunStep.seq B c18 c19 σ c5 c11 c15 c16 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.assign B c5 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")) c10 (RunStep.eval_sub B c5 (Expr.var "coefficient.negative") (Expr.var "coefficient.positive") c8 c9 (RunStep.eval_var B c5 "coefficient.negative" (?nAX_g8141_0_0_2)) (RunStep.eval_var B c5 "coefficient.positive" (?nAX_g8141_0_0_3)) (?nAX_g8141_0_0_4))))) (?nAX_g8141_0_0_5)) ?_)) fun (hcase:c4) => @Exists.intro Env c1 c30 (@And.intro (Run B normalize σ c30 ((10:Nat))) (c0 c30) (RunStep.mono B normalize σ c30 (c14 c33) ((10:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c30 c33 (RunStep.cond_lt_false B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_0_0_6)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_0_0_7)) hcase) (RunStep.seq B c21 c22 σ c25 c30 c31 c32 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8141_0_0_8))) (RunStep.assign B c25 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c29 (RunStep.eval_sub B c25 (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") c27 c28 (RunStep.eval_var B c25 "coefficient.positive" (?nAX_g8141_0_0_9)) (RunStep.eval_var B c25 "coefficient.negative" (?nAX_g8141_0_0_10)) (?nAX_g8141_0_0_11))))) (?nAX_g8141_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8141_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,sign,magnitude]
  · (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "coefficient.sign") (sign p q)) (@Eq Nat (Env.vars τ "coefficient.magnitude") (magnitude p q))) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B normalize σ σ' ((10:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:=Nat.lt (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative"); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.sign" ((1:Nat)); let c6:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c7:String→ Nat:=Env.vars c5; let c8:Nat:=c7 "coefficient.negative"; let c9:Nat:=c7 "coefficient.positive"; let c10:Nat:=c6 c8 c9; let c11:Env:=Env.setVar c5 "coefficient.magnitude" c10; let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Nat→ Nat:=c12 (c13 (Cond.size (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")))); let c15:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive"))); let c17:Nat:=c12 c15 c16; let c18:Com:=Com.assign "coefficient.sign" (Expr.lit ((1:Nat))); let c19:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")); let c20:Com:=Com.seq c18 c19; let c21:Com:=Com.assign "coefficient.sign" (Expr.lit ((0:Nat))); let c22:Com:=Com.assign "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")); let c23:Com:=Com.seq c21 c22; let c24:String→ Nat:=Env.vars c11; let c25:Env:=Env.setVar σ "coefficient.sign" ((0:Nat)); let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "coefficient.positive"; let c28:Nat:=c26 "coefficient.negative"; let c29:Nat:=c6 c27 c28; let c30:Env:=Env.setVar c25 "coefficient.magnitude" c29; let c31:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c32:Nat:=c13 (Expr.size (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative"))); let c33:Nat:=c12 c31 c32; let c34:String→ Nat:=Env.vars c30; @And.casesOn (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q) (fun (x:And (@Eq Nat (Env.vars σ "coefficient.positive") p) (@Eq Nat (Env.vars σ "coefficient.negative") q)) => c2) a fun (left:@Eq Nat (Env.vars σ "coefficient.positive") p) (right:@Eq Nat (Env.vars σ "coefficient.negative") q) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Exists.intro Env c1 c11 (@And.intro (Run B normalize σ c11 ((10:Nat))) (c0 c11) (RunStep.mono B normalize σ c11 (c14 c17) ((10:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c11 c17 (RunStep.cond_lt_true B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_1_0_0)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_1_0_1)) hcase) (RunStep.seq B c18 c19 σ c5 c11 c15 c16 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.assign B c5 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.negative") (Expr.var "coefficient.positive")) c10 (RunStep.eval_sub B c5 (Expr.var "coefficient.negative") (Expr.var "coefficient.positive") c8 c9 (RunStep.eval_var B c5 "coefficient.negative" (?nAX_g8141_1_0_2)) (RunStep.eval_var B c5 "coefficient.positive" (?nAX_g8141_1_0_3)) (?nAX_g8141_1_0_4))))) (?nAX_g8141_1_0_5)) ?_)) fun (hcase:c4) => @Exists.intro Env c1 c30 (@And.intro (Run B normalize σ c30 ((10:Nat))) (c0 c30) (RunStep.mono B normalize σ c30 (c14 c33) ((10:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c20 c23 σ c30 c33 (RunStep.cond_lt_false B σ (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") (Env.vars σ "coefficient.positive") (Env.vars σ "coefficient.negative") (RunStep.eval_var B σ "coefficient.positive" (?nAX_g8141_1_0_6)) (RunStep.eval_var B σ "coefficient.negative" (?nAX_g8141_1_0_7)) hcase) (RunStep.seq B c21 c22 σ c25 c30 c31 c32 (RunStep.assign B σ "coefficient.sign" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8141_1_0_8))) (RunStep.assign B c25 "coefficient.magnitude" (Expr.sub (Expr.var "coefficient.positive") (Expr.var "coefficient.negative")) c29 (RunStep.eval_sub B c25 (Expr.var "coefficient.positive") (Expr.var "coefficient.negative") c27 c28 (RunStep.eval_var B c25 "coefficient.positive" (?nAX_g8141_1_0_9)) (RunStep.eval_var B c25 "coefficient.negative" (?nAX_g8141_1_0_10)) (?nAX_g8141_1_0_11))))) (?nAX_g8141_1_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8141_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8141_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Env.setVar,sign,magnitude]

theorem append_spec (B p q:ℕ) (front:List ℕ) (h1:1< B) (hp:p< B) (hq:q< B) (hlen:front.length+3< B):
    Spec B (fun σ => σ.vars "coefficient.positive"=p∧ σ.vars "coefficient.negative"=q∧
      Prefix front "lp.input" σ∧ σ.vars "lp.length"=front.length∧ front.length+3≤(σ.arrs "lp.input").length)
      append (fun _ τ => Prefix (front++encodeRational ((p:ℚ)-q)) "lp.input" τ∧ τ.vars "lp.length"=front.length+3) 31:=by
  rintro σ ⟨hpos,hneg,hprefix,hcount,hroom⟩
  obtain ⟨ν,r1,p1⟩:=normalize_spec B p q h1 hp hq σ ⟨hpos,hneg⟩
  have hs:sign p q< B:=(sign_le p q).trans_lt h1
  have hm:magnitude p q< B:=(magnitude_bound p q).trans_lt (max_lt hp hq)
  obtain ⟨μ,r2,p2⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" front (sign p q)
    (.var "coefficient.sign") h1 (by omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hprefix,
      (r1.frame_var "lp.length" (by decide)).trans hcount,
      by rw [Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hs⟩⟩
  have hlen1:(front++[sign p q]).length=front.length+1:=by simp
  have hmag:μ.vars "coefficient.magnitude"=magnitude p q:=(r2.frame_var "coefficient.magnitude" (by decide)).trans p1.2
  obtain ⟨ξ,r3,p3⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" (front++[sign p q]) (magnitude p q)
    (.var "coefficient.magnitude") h1 (by rw [hlen1]; omega) μ
    ⟨p2.1,by rw [hlen1]; exact p2.2,by rw [hlen1,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨hmag.symm,hmag ▸ hm⟩⟩
  have hlen2:((front++[sign p q])++[magnitude p q]).length=front.length+2:=by simp
  obtain ⟨τ,r4,p4⟩:=Lax455465Proofs.RamWordBuffer.append_spec B "lp.input" "lp.length" ((front++[sign p q])++[magnitude p q]) 1
    (.lit 1) h1 (by rw [hlen2]; omega) ξ
    ⟨p3.1,by simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using p3.2,
      by rw [hlen2,Lax455465Proofs.RamFrames.run_array_length r3,Lax455465Proofs.RamFrames.run_array_length r2,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      evalB_lit h1⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp [Expr.size]),?_,?_⟩
  · simpa only [encoding,List.append_assoc,List.cons_append,List.nil_append] using p4.1
  · simpa only [hlen2,Nat.add_assoc] using p4.2

end Lax263307Proofs.NativeIntegerEncoding

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

theorem words_append (xs ys:List ℚ):words (xs++ys)=words xs++words ys:=List.flatMap_append

theorem words_take_succ (xs:List ℚ) (i:ℕ) (hi:i< xs.length):
    words (xs.take (i+1))=words (xs.take i)++encodeRational xs[i]:=by
  rw [List.take_succ_eq_append_getElem hi,words_append]
  simp [words]

def Invariant (P:Env→ Prop) (xs:List ℚ) (front:List ℕ) (σ:Env):Prop:=
  P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "fill.i"≤ xs.length∧
  σ.vars "lp.length"=front.length+3*σ.vars "fill.i" ∧
  front.length+3*xs.length≤(σ.arrs "lp.input").length∧
  Prefix (front++words (xs.take (σ.vars "fill.i"))) "lp.input" σ

theorem command_spec (B:ℕ) (xs:List ℚ) (front:List ℕ) (P:Env→ Prop) (read:Com) (K:ℕ)
    (hB:front.length+3*xs.length+2< B)
    (hri:"fill.i"∉read.wvars) (hrl:"fill.length"∉read.wvars)
    (hrlen:"lp.length"∉read.wvars) (hra:"lp.input"∉read.warrs)
    (hinit:∀ σ,P σ→ P (σ.setVar "fill.i" 0))
    (hwrite:∀ σ τ,Run B NativeIntegerEncoding.append σ τ 31→ P σ→ P τ)
    (hadvance:∀ σ τ,Run B advance σ τ 4→ P σ→ P τ)
    (hread:∀ i (hi:i< xs.length),Spec B (fun σ => P σ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ∧ τ.vars "coefficient.positive"< B∧ τ.vars "coefficient.negative"< B∧
        ((τ.vars "coefficient.positive" :ℕ):ℚ)-τ.vars "coefficient.negative"=xs[i]) K):
    Spec B (fun σ => P σ∧ σ.vars "fill.length"=xs.length∧ σ.vars "lp.length"=front.length∧
      front.length+3*xs.length≤(σ.arrs "lp.input").length∧ Prefix front "lp.input" σ)
      (command read) (fun _ τ => P τ∧ τ.vars "lp.length"=front.length+3*xs.length∧ Prefix (front++words xs) "lp.input" τ)
      ((K+39)*xs.length+6):=by
  have h1:1< B:=by omega
  have hbody:Spec B (fun σ => Invariant P xs front σ∧ σ.vars "fill.i"< xs.length)
      (body read) (fun σ τ => Invariant P xs front τ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+35):=by
    rintro σ ⟨⟨hP,hlen,hle,hcount,hroom,hprefix⟩,hlt⟩
    let i:=σ.vars "fill.i"
    have htake:(xs.take i).length=i:=by rw [List.length_take,Nat.min_eq_left hle]
    have hfront:(front++words (xs.take i)).length=front.length+3*i:=by rw [List.length_append,words_length,htake]
    obtain ⟨ν,r1,p1⟩:=hread i hlt σ ⟨hP,rfl⟩
    obtain ⟨μ,r2,p2⟩:=NativeIntegerEncoding.append_spec B (ν.vars "coefficient.positive") (ν.vars "coefficient.negative")
      (front++words (xs.take i)) h1 p1.2.1 p1.2.2.1 (by rw [hfront]; omega) ν
      ⟨rfl,rfl,by simpa only [Prefix,r1.frame_arr "lp.input" hra] using hprefix,
        by rw [hfront]; exact (r1.frame_var "lp.length" hrlen).trans hcount,
        by rw [hfront,Lax455465Proofs.RamFrames.run_array_length r1]; omega⟩
    have hPμ:=hwrite ν μ r2 p1.1
    have hiμ:μ.vars "fill.i"=i:=
      (r2.frame_var "fill.i" (by decide)).trans (r1.frame_var "fill.i" hri)
    let τ:=μ.setVar "fill.i" (i+1)
    have r3:Run B advance μ τ 4:=Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega)⟩) (evalB_lit h1) (by change i+1< B; omega))
    have rr:=r1.seq (r2.seq r3)
    have ht:τ.vars "fill.i"=i+1:=by simp [τ]
    refine ⟨τ,rr.mono (by omega),⟨hadvance μ τ r3 hPμ,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
    · exact ((r2.seq r3).frame_var "fill.length" (by decide)).trans ((r1.frame_var "fill.length" hrl).trans hlen)
    · rw [ht]
      have hc:=(r3.frame_var "lp.length" (by decide)).trans p2.2
      rw [hfront] at hc
      omega
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,words_take_succ xs i hlt,←List.append_assoc,←p1.2.2.2]
      simpa only [Prefix,r3.frame_arr "lp.input" (by decide)] using p2.1
  have hloop:=Spec.forRangeZero "fill.i" "fill.length" (Invariant P xs front) xs.length (K+35)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hcount,hroom,hprefix⟩
  have hi:Invariant P xs front (σ.setVar "fill.i" 0):=by
    refine ⟨hinit σ hP,?_,by simp,?_,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.mul_zero,Nat.add_zero] using hcount
    · simpa only [vars_setVar,if_true,List.take_zero,words,List.flatMap_nil,List.append_nil,Prefix,arrs_setVar] using hprefix
  obtain ⟨τ,rr,p⟩:=hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_,?_⟩
  · simpa only [p.2] using p.1.2.2.2.1
  · simpa only [p.2,List.take_length] using p.1.2.2.2.2.2

end Lax263307Proofs.NativeRationalTabulate

end

section

namespace Lax263307Proofs.NativeMomentAssembly

open Lax263307 Lax109476.RationalEncoding
open MomentLP CoordinateCatalog

def matrixWords {m n:ℕ} (A:Fin m→ Fin n→ ℚ):List ℕ:=
  (List.ofFn fun i => List.ofFn (A i)).flatten.flatMap encodeRational

theorem ofFn_addCases {α:Type*} {m n:ℕ} (f:Fin m→ α) (g:Fin n→ α):
    List.ofFn (Fin.addCases f g)=List.ofFn f++List.ofFn g:=by
  simpa only [Fin.append] using List.ofFn_fin_append f g

theorem matrix_addCases {a b n:ℕ} (f:Fin a→ Fin n→ ℚ) (g:Fin b→ Fin n→ ℚ):
    matrixWords (Fin.addCases f g)=matrixWords f++matrixWords g:=by
  have he:(fun i => List.ofFn (Fin.addCases f g i))=
      Fin.addCases (fun i => List.ofFn (f i)) (fun i => List.ofFn (g i)):=by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  simp only [matrixWords,he,ofFn_addCases,List.flatten_append,List.flatMap_append]

def normalization (n r:ℕ):Fin 2→ Index n r→ ℚ:=
  fun i j => if i=0 then singleRow ∅ j else -singleRow ∅ j

def upper (n r:ℕ):Index n r→ Index n r→ ℚ:=fun i => singleRow (indexing n r i).val

def nonindependent {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if G.IsIndepSet ((indexing n r i).val:Set (Fin n)) then 0 else singleRow (indexing n r i).val j

def monotone (n r:ℕ):Fin (dimension n r*n)→ Index n r→ ℚ:=
  fun i => let uv:=finProdFinEquiv.symm i
    if (indexing n r uv.1).val.card≤ r+1 then monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0

def massPositive (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i => if (indexing n r i).val.card≤ r+1 then massRow (indexing n r i).val k else fun _ => 0

def massNegative (n k r:ℕ):Index n r→ Index n r→ ℚ:=
  fun i j => if (indexing n r i).val.card≤ r+1 then -massRow (indexing n r i).val k j else 0

theorem matrix_words_exact {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    matrixWords (MomentLP.program G k r).A=
      matrixWords (normalization n r)++(matrixWords (upper n r)++
        (matrixWords (nonindependent G r)++(matrixWords (monotone n r)++
          (matrixWords (massPositive n k r)++matrixWords (massNegative n k r))))):=by
  change matrixWords (Fin.addCases (normalization n r) (Fin.addCases (upper n r)
    (Fin.addCases (nonindependent G r) (Fin.addCases (monotone n r)
      (Fin.addCases (massPositive n k r) (massNegative n k r))))))=_
  simp only [matrix_addCases]

theorem matrix_length {m n:ℕ} (A:Fin m→ Fin n→ ℚ):(matrixWords A).length=3*m*n:=by
  change (NativeRationalTabulate.words ((List.ofFn fun i => List.ofFn (A i)).flatten)).length=3*m*n
  rw [NativeRationalTabulate.words_length]
  simp [List.length_flatten,List.map_ofFn,List.sum_ofFn,Nat.mul_assoc]

end Lax263307Proofs.NativeMomentAssembly

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP

def rowCount (kind:Kind) (n r:ℕ):ℕ:=match kind with
  | .normalization => 2
  | .monotone => dimension n r*n
  | _ => dimension n r

def matrix (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    Fin (rowCount kind n r)→ Index n r→ ℚ:=match kind with
  | .normalization => NativeMomentAssembly.normalization n r
  | .upper => NativeMomentAssembly.upper n r
  | .nonindependent => NativeMomentAssembly.nonindependent G r
  | .monotone => NativeMomentAssembly.monotone n r
  | .massPositive => NativeMomentAssembly.massPositive n k r
  | .massNegative => NativeMomentAssembly.massNegative n k r

def entries (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):List ℚ:=
  (List.ofFn fun i => List.ofFn (matrix kind G k r i)).flatten

theorem entries_words (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    NativeRationalTabulate.words (entries kind G k r)=NativeMomentAssembly.matrixWords (matrix kind G k r):=rfl

theorem entries_length (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    (entries kind G k r).length=rowCount kind n r*dimension n r:=by
  simp [entries,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem coordinates_spec (B q columns:ℕ) (hB:q+columns+3< B):
    Spec B (fun σ => σ.vars "fill.i"=q∧ σ.vars "catalog.count"=columns) coordinates
      (fun _ τ => τ.vars "family.row"=q/columns∧ τ.vars "column.index"=q%columns) 10:=by
  have hdiv:q/columns≤ q:=Nat.div_le_self _ _
  have hmul:q/columns*columns≤ q:=Nat.div_mul_le_self _ _
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns)) => let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 q columns; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) q columns; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "family.row") c1) (@Eq Nat (Env.vars τ "column.index") c2)) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B coordinates σ σ' ((10:Nat))) (c3 σ'); let c5:Nat:=c0 (Env.vars σ "fill.i") (Env.vars σ "catalog.count"); let c6:Env:=Env.setVar σ "family.row" c5; let c7:String→ Nat:=Env.vars c6; let c8:Nat:=c7 "fill.i"; let c9:Nat:=c7 "family.row"; let c10:Nat:=c7 "catalog.count"; let c11:Nat:=Nat.mul c9 c10; let c12:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c8 c11; let c13:Env:=Env.setVar c6 "column.index" c12; let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count"))); let c17:Expr:=Expr.sub (Expr.var "fill.i") (Expr.mul (Expr.var "family.row") (Expr.var "catalog.count")); let c18:Nat:=c15 (Expr.size c17); let c19:String→ Nat:=Env.vars c13; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") columns)) => @Exists Env c4) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") columns) => @Exists.intro Env c4 c13 (@And.intro (Run B coordinates σ c13 ((10:Nat))) (c3 c13) (RunStep.mono B coordinates σ c13 (c14 c16 c18) ((10:Nat)) (RunStep.seq B (Com.assign "family.row" (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count"))) (Com.assign "column.index" c17) σ c6 c13 c16 c18 (RunStep.assign B σ "family.row" (Expr.div (Expr.var "fill.i") (Expr.var "catalog.count")) c5 (RunStep.eval_div B σ (Expr.var "fill.i") (Expr.var "catalog.count") (Env.vars σ "fill.i") (Env.vars σ "catalog.count") (RunStep.eval_var B σ "fill.i" (?nAX_g8178_0_0_0)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8178_0_0_1)) ?_)) (RunStep.assign B c6 "column.index" c17 c12 (RunStep.eval_sub B c6 (Expr.var "fill.i") (Expr.mul (Expr.var "family.row") (Expr.var "catalog.count")) c8 c11 (RunStep.eval_var B c6 "fill.i" (?nAX_g8178_0_0_2)) (RunStep.eval_mul B c6 (Expr.var "family.row") (Expr.var "catalog.count") c9 c10 (RunStep.eval_var B c6 "family.row" ?_) (RunStep.eval_var B c6 "catalog.count" (?nAX_g8178_0_0_3)) ?_) (?nAX_g8178_0_0_4)))) (?nAX_g8178_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8178_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8178_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar,Nat.mod_eq_sub_div_mul]
  all_goals omega

theorem candidates_first (n R:ℕ):(RationalConditioning.candidates n R)[0]?=some (∅:Finset (Fin n)):=by
  induction R with
  | zero => simp [RationalConditioning.candidates]
  | succ R ih =>
    rw [NativeCatalogOrder.all_candidates_succ]
    have hp:0<(RationalConditioning.candidates n R).length:=by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at ih
      contradiction
    rw [List.getElem?_append_left hp]
    exact ih

theorem dimension_positive (n r:ℕ):0< dimension n r:=by
  have h:=NativeCatalog.rows_positive n (r+2)
  change 1≤(NativeCatalog.rows n (r+3)).length at h
  rw [NativeCatalog.rows_words] at h
  simpa only [Lax263307.NativeCatalog.words,List.length_map,Nat.succ_le_iff] using h

theorem first_coordinate (n r:ℕ):
    (CoordinateCatalog.indexing n r ⟨0,dimension_positive n r⟩).val=∅:=by
  have hi:=NativeCatalogOrder.catalog_index n r ⟨0,dimension_positive n r⟩
  have he:=candidates_first n (r+2)
  exact Option.some.inj (hi.symm.trans he)

def rowSlot (kind:Kind) (n r:ℕ) (i:Fin (rowCount kind n r)):Index n r:=match kind with
  | .normalization => ⟨0,dimension_positive n r⟩
  | .monotone => (finProdFinEquiv.symm i).1
  | .upper => i
  | .nonindependent => i
  | .massPositive => i
  | .massNegative => i

def Vertex (kind:Kind) (n r:ℕ) (i:Fin (rowCount kind n r)) (σ:Env):Prop:=match kind with
  | .monotone => σ.vars "row.v"=(finProdFinEquiv.symm i).2.val
  | _ => True

theorem select_row_spec (kind:Kind) (n r B:ℕ) (i:Fin (rowCount kind n r))
    (hB:i.val+n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "family.row"=i.val) (selectRow kind)
      (fun _ τ => τ.vars "row.index"=(rowSlot kind n r i).val∧ Vertex kind n r i τ) 10:=by
  have hdiv:i.val/n≤ i.val:=Nat.div_le_self _ _
  have hmul:i.val/n*n≤ i.val:=Nat.div_mul_le_self _ _
  cases kind <;> (first
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.normalization n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.normalization n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.normalization n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.normalization n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.normalization) σ σ' ((10:Nat)))
                              (c2 σ');
                          let c4:Env:=Env.setVar σ "row.index" ((0:Nat));
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 c4
                              (@And.intro
                                (Run B (selectRow Kind.normalization) σ c4 ((10:Nat)))
                                (c2 c4)
                                (RunStep.mono B (selectRow Kind.normalization) σ c4
                                  (Nat.add
                                    ((1:Nat))
                                    (Expr.size (Expr.lit ((0:Nat)))))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.lit ((0:Nat)))
                                    ((0:Nat))
                                    (RunStep.eval_lit B ((0:Nat)) σ
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.upper n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.upper n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.upper n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.upper n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.upper) σ σ' ((10:Nat))) (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.upper) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.upper) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.nonindependent n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.nonindependent n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.nonindependent n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.nonindependent n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.nonindependent) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.nonindependent) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.nonindependent) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.monotone n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.monotone n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.monotone n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.monotone n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.monotone) σ σ' ((10:Nat))) (c2 σ');
                          let c4:Nat:=
                            @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "family.row") (Env.vars σ "graph.n");
                          let c5:Env:=Env.setVar σ "row.index" c4;
                          let c6:String→ Nat:=Env.vars c5;
                          let c7:Nat:=c6 "family.row";
                          let c8:Nat:=c6 "row.index";
                          let c9:Nat:=c6 "graph.n";
                          let c10:Nat:=Nat.mul c8 c9;
                          let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10;
                          let c12:Env:=Env.setVar c5 "row.v" c11;
                          let c13:Nat→ Nat→ Nat:=Nat.add;
                          let c14:Nat→ Nat:=c13 ((1:Nat));
                          let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "family.row") (Expr.var "graph.n")));
                          let c16:Expr:=Expr.sub (Expr.var "family.row") (Expr.mul (Expr.var "row.index") (Expr.var "graph.n"));
                          let c17:Nat:=c14 (Expr.size c16);
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 c12
                              (@And.intro
                                (Run B (selectRow Kind.monotone) σ c12 ((10:Nat))) (c2 c12)
                                (RunStep.mono B (selectRow Kind.monotone) σ c12 (c13 c15 c17)
                                  ((10:Nat))
                                  (RunStep.seq B (Com.assign "row.index" (Expr.div (Expr.var "family.row") (Expr.var "graph.n")))
                                    (Com.assign "row.v" c16) σ c5 c12 c15 c17
                                    (RunStep.assign B σ "row.index" (Expr.div (Expr.var "family.row") (Expr.var "graph.n")) c4
                                      (RunStep.eval_div B σ (Expr.var "family.row") (Expr.var "graph.n") (Env.vars σ "family.row")
                                        (Env.vars σ "graph.n")
                                        (RunStep.eval_var B σ "family.row"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        (RunStep.eval_var B σ "graph.n"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        ?_))
                                    (RunStep.assign B c5 "row.v" c16 c11
                                      (RunStep.eval_sub B c5 (Expr.var "family.row") (Expr.mul (Expr.var "row.index") (Expr.var "graph.n"))
                                        c7 c10
                                        (RunStep.eval_var B c5 "family.row"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        (RunStep.eval_mul B c5 (Expr.var "row.index") (Expr.var "graph.n") c8 c9
                                          (RunStep.eval_var B c5 "row.index" ?_)
                                          (RunStep.eval_var B c5 "graph.n"
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_)
                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massPositive n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massPositive n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.massPositive n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.massPositive n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.massPositive) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.massPositive) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.massPositive) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                  | (expose_names;
                      (refine
                          fun (σ:Env)
                            (a:
                              And (@Eq Nat (Env.vars σ "graph.n") n)
                                (@Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massNegative n r) i))) =>
                          let c0:Prop:= @Eq Nat (Env.vars σ "family.row") (@Fin.val (rowCount Kind.massNegative n r) i);
                          let c1:Nat:= @Fin.val (dimension n r) (rowSlot Kind.massNegative n r i);
                          let c2:Env→ Prop:=
                            (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "row.index") c1) (Vertex Kind.massNegative n r i τ)) σ;
                          let c3:Env→ Prop:=fun (σ':Env) =>
                            And (Run B (selectRow Kind.massNegative) σ σ' ((10:Nat)))
                              (c2 σ');
                          @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                            (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c3) a
                            fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                            @Exists.intro Env c3 (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                              (@And.intro
                                (Run B (selectRow Kind.massNegative) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  ((10:Nat)))
                                (c2 (Env.setVar σ "row.index" (Env.vars σ "family.row")))
                                (RunStep.mono B (selectRow Kind.massNegative) σ (Env.setVar σ "row.index" (Env.vars σ "family.row"))
                                  (Nat.add
                                    ((1:Nat)) (Expr.size (Expr.var "family.row")))
                                  ((10:Nat))
                                  (RunStep.assign B σ "row.index" (Expr.var "family.row") (Env.vars σ "family.row")
                                    (RunStep.eval_var B σ "family.row"
                                      ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                 )
  all_goals simp_all [rowSlot,Vertex,Env.setVar,finProdFinEquiv,Fin.divNat,Fin.modNat,Nat.mod_eq_sub_div_mul]
  all_goals omega

def fixedVars:List String:= ["graph.n","catalog.count","moment.r","row.k"]
def fixedArrays:List String:= ["catalog.mask","search.graph","catalog.card","catalog.independent"]

theorem data_frame {n B K:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hv:∀ x∈ fixedVars,x∉c.wvars) (ha:∀ x∈ fixedArrays,x∉c.warrs)
    (hσ:Data G k r σ):Data G k r τ:=by
  refine ⟨⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by decide)) (hv _ (by decide))
    (ha _ (by decide)) (ha _ (by decide)) hσ.1.1,?_,?_,?_⟩,?_⟩
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.card" (ha _ (by decide))] using hσ.1.2.1
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.independent" (ha _ (by decide))] using hσ.1.2.2.1
  · exact (rr.frame_var "moment.r" (hv _ (by decide))).trans hσ.1.2.2.2
  · exact (rr.frame_var "row.k" (hv _ (by decide))).trans hσ.2

open NativeCatalogMetadata NativeMomentProduce

def Ready (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (i:Fin (rowCount kind n r)) (j:Index n r) (σ:Env):Prop:=
  NativeMomentAccess.Loaded G r (rowSlot kind n r i) j σ∧ σ.vars "graph.n"=n∧
  σ.vars "row.k"=k∧ σ.vars "row.active"=(if (atIndex n r (rowSlot kind n r i)).card≤ r+1 then 1 else 0)∧
  σ.vars "family.row"=i.val∧ Vertex kind n r i σ

theorem produce_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (i:Fin (rowCount kind n r)) (j:Index n r) (hB:n+k+3 < B) (hm:2^n < B):
    Spec B (Ready kind G k r i j) (produce kind)
      (fun _ τ => Value B (matrix kind G k r i j) τ) (22*n+50):=by
  rintro σ ⟨hl,hn,hk,ha,hi,hv⟩
  have h1:1 < B:=by omega
  cases kind with
  | normalization =>
    change Fin 2 at i
    have hz:atIndex n r (rowSlot .normalization n r i)=∅:=first_coordinate n r
    obtain ⟨ν,r1,p1⟩:=single_spec B (atIndex n r (rowSlot .normalization n r i)) (atIndex n r j)
      h1 hm σ ⟨hl.1,hl.2.1⟩
    have pv:Value B (MomentLP.singleRow ∅ j) ν:=by
      rw [hz] at p1
      simpa only [atIndex,NativeMomentRows.same_single_row] using p1
    have hiB:i.val < B:=i.isLt.trans (by change 2 < B; omega)
    have hc:(Cond.eq (.var "family.row") (.lit 0)).evalB B σ=some (i.val==0):=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (evalB_lit (show 0 < B by omega))
    by_cases he:i=0
    · have hei:i.val=0:=congrArg Fin.val he
      have rr:=Run.ite_true (d:=.seq singleCommand swap) (by simpa only [hei,beq_self_eq_true] using hc) r1
      exact ⟨ν,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_pos he] using pv⟩
    · have hei:i.val≠0:=fun hh => he (Fin.ext hh)
      obtain ⟨τ,r2,p2⟩:=swap_spec B (MomentLP.singleRow ∅ j) ν pv
      have rr:=Run.ite_false (c:=singleCommand) (by simpa only [beq_eq_false_iff_ne.mpr hei] using hc) (r1.seq r2)
      exact ⟨τ,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_neg he] using p2⟩
  | upper =>
    obtain ⟨τ,rr,p⟩:=single_spec B (atIndex n r i) (atIndex n r j) h1 hm σ ⟨hl.1,hl.2.1⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,matrix,NativeMomentAssembly.upper] using p
  | nonindependent =>
    have hf:σ.vars "row.independent"=(if ¬G.IsIndepSet (atIndex n r i:Set (Fin n)) then 0 else 1-0):=by
      by_cases h:G.IsIndepSet (atIndex n r i:Set (Fin n))
      · simpa [rowSlot,h] using hl.2.2.2
      · simpa [rowSlot,h] using hl.2.2.2
    obtain ⟨τ,rr,p⟩:=guard_spec B 0 8 "row.independent" _ (¬G.IsIndepSet (atIndex n r i:Set (Fin n)))
      (NativeMomentRows.same (atIndex n r i) (atIndex n r j)) singleCommand h1 (by omega)
      (single_spec B (atIndex n r i) (atIndex n r j) h1 hm) σ ⟨⟨hl.1,hl.2.1⟩,hf⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,ite_not,matrix,NativeMomentAssembly.nonindependent] using p
  | monotone =>
    let v:Fin n:=(finProdFinEquiv.symm i).2
    let A:=atIndex n r (finProdFinEquiv.symm i).1
    obtain ⟨τ,rr,p⟩:=guard_spec B 1 18 "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.same (insert v A) (atIndex n r j):ℚ)-NativeMomentRows.same A (atIndex n r j))
      NativeMomentRows.monotoneCommand h1 (by omega)
      (monotone_value_spec B A (atIndex n r j) v (by omega) hm) σ ⟨⟨hl.1,hl.2.1,hv⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,v,atIndex,NativeMomentRows.monotone_value,matrix,NativeMomentAssembly.monotone,ite_apply] using p
  | massPositive =>
    let A:=atIndex n r i
    obtain ⟨τ,rr,p⟩:=guard_spec B 1 (22*n+18) "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n:ℚ)-(k*NativeMomentRows.same A (atIndex n r j):ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,matrix,NativeMomentAssembly.massPositive,ite_apply] using p
  | massNegative =>
    let A:=atIndex n r i
    obtain ⟨ν,r1,p1⟩:=guard_spec B 1 (22*n+18) "row.active" _ (A.card≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n:ℚ)-(k*NativeMomentRows.same A (atIndex n r j):ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    obtain ⟨τ,r2,p2⟩:=swap_spec B _ ν p1
    refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,apply_ite,neg_zero,matrix,NativeMomentAssembly.massNegative] using p2

theorem entries_ofFn (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    entries kind G k r=List.ofFn (fun z:Fin (rowCount kind n r*dimension n r) =>
      matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2):=by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hh:(⟨i.val*dimension n r+j.val,by have h:=j.isLt; have hi:=i.isLt; nlinarith⟩:Fin (rowCount kind n r*dimension n r))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [hh,Equiv.symm_apply_apply]

theorem entries_get (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (z:Fin (rowCount kind n r*dimension n r)):
    (entries kind G k r)[z.val]?=some (matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2):=by
  rw [entries_ofFn,List.getElem?_ofFn,dif_pos z.isLt]

theorem read_fixed_vars (kind:Kind):∀ x∈ fixedVars,x∉(read kind).wvars:=by
  cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_fixed_arrays (kind:Kind):∀ x∈ fixedArrays,x∉(read kind).warrs:=by
  cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (z:Fin (rowCount kind n r*dimension n r))
    (hB:rowCount kind n r*dimension n r+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "fill.i"=z.val) (read kind)
      (fun _ τ => Data G k r τ∧ Value B
        (matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) τ) (22*n+90):=by
  rintro σ ⟨hd,hz⟩
  let i:=(finProdFinEquiv.symm z).1
  let j:=(finProdFinEquiv.symm z).2
  have hiq:i.val=z.val/dimension n r:=rfl
  have hjq:j.val=z.val%dimension n r:=rfl
  have hiq':i.val≤ z.val:=by rw [hiq]; exact Nat.div_le_self _ _
  obtain ⟨ν,r1,p1⟩:=coordinates_spec B z.val (dimension n r) (by have h:=z.isLt; omega) σ ⟨hz,hd.1.1.2.1⟩
  have d1:Data G k r ν:=data_frame G k r r1
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd
  obtain ⟨μ,r2,p2⟩:=select_row_spec kind n r B i (by have h:=z.isLt; omega) ν ⟨d1.1.1.1,p1.1⟩
  have d2:Data G k r μ:=data_frame G k r r2
    (by cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide)
    (by cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide) d1
  obtain ⟨ξ,r3,p3⟩:=NativeMomentAccess.command_spec B G r (rowSlot kind n r i) j (by omega) (by change dimension n r < B; omega) hm μ
    ⟨d2.1,p2.1,(r2.frame_var "column.index" (by cases kind <;> decide)).trans p1.2⟩
  have hn:ξ.vars "graph.n"=n:=(r3.frame_var "graph.n" (by decide)).trans d2.1.1.1
  have hk:ξ.vars "row.k"=k:=(r3.frame_var "row.k" (by decide)).trans d2.2
  have hir:ξ.vars "family.row"=i.val:=((r2.seq r3).frame_var "family.row" (by cases kind <;> decide)).trans p1.1
  have hv:Vertex kind n r i ξ:=by
    cases kind <;> simp only [Vertex] at p2 ⊢
    all_goals first | trivial | exact (r3.frame_var "row.v" (by decide)).trans p2.2
  obtain ⟨τ,r4,p4⟩:=produce_spec kind B G k r i j (by omega) hm ξ ⟨p3.1,hn,hk,p3.2,hir,hv⟩
  have rr:Run B (read kind) σ τ (10+(10+(20+(22*n+50)))):=r1.seq (r2.seq (r3.seq r4))
  exact ⟨τ,rr.mono (by omega),data_frame G k r rr (read_fixed_vars kind) (read_fixed_arrays kind) hd,p4⟩

theorem append_matrix_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (front:List ℕ)
    (hB:front.length+3*(rowCount kind n r*dimension n r)+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "fill.length"=rowCount kind n r*dimension n r∧
      σ.vars "lp.length"=front.length∧ front.length+3*(rowCount kind n r*dimension n r)≤ (σ.arrs "lp.input").length∧
      Lax455465Proofs.RamVirtualState.Prefix front "lp.input" σ)
      (appendMatrix kind) (fun _ τ => Data G k r τ∧
        τ.vars "lp.length"=front.length+3*(rowCount kind n r*dimension n r)∧
        Lax455465Proofs.RamVirtualState.Prefix (front++NativeMomentAssembly.matrixWords (matrix kind G k r)) "lp.input" τ)
      ((22*n+129)*(rowCount kind n r*dimension n r)+6):=by
  have hh:=NativeRationalTabulate.command_spec B (entries kind G k r) front (Data G k r) (read kind) (22*n+90)
    (by rw [entries_length]; omega)
    (by cases kind <;> decide) (by cases kind <;> decide) (by cases kind <;> decide) (by cases kind <;> decide)
    (by intro σ h; simpa [Data,NativeMomentAccess.Data,NativeCatalogMetadata.Data,Lax455465Proofs.RamVirtualState.Prefix] using h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro q hq σ hσ
      let z:Fin (rowCount kind n r*dimension n r):= ⟨q,by rwa [entries_length] at hq⟩
      obtain ⟨τ,rr,p⟩:=read_spec kind B G k r z (by omega) hm σ hσ
      have he:=entries_get kind G k r z
      rw [List.getElem?_eq_getElem hq] at he
      exact ⟨τ,rr,p.1,by simpa only [Value,Option.some.inj he] using p.2⟩)
  simpa only [appendMatrix,entries_length,entries_words,show 22*n+90+39=22*n+129 by omega] using hh

theorem count_spec (kind:Kind) (n r B:ℕ)
    (hB:rowCount kind n r*dimension n r+n+dimension n r+3 < B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "catalog.count"=dimension n r)
      (.assign "fill.length" (countExpr kind))
      (fun _ τ => τ.vars "fill.length"=rowCount kind n r*dimension n r) 6:=by
  have hp:=dimension_positive n r
  have hb:dimension n r*n≤ dimension n r*n*dimension n r:=Nat.le_mul_of_pos_right _ hp
  cases kind <;> simp only [rowCount,countExpr] at hB ⊢ <;> (first
                                                             | (expose_names;
                                                                 (refine
                                                                     fun (σ:Env)
                                                                       (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") (dimension n r))) =>
                                                                     let c0:Prop:= @Eq Nat (Env.vars σ "catalog.count") (dimension n r);
                                                                     let c1:Expr:=
                                                                       Expr.mul (Expr.lit ((2:Nat))) (Expr.var "catalog.count");
                                                                     let c2:Com:=Com.assign "fill.length" c1;
                                                                     let c3:Env→ Nat→ Prop:=Run B c2 σ;
                                                                     let c4:Nat→ Nat:=
                                                                       Nat.mul ((2:Nat));
                                                                     let c5:Nat:=c4 (dimension n r);
                                                                     let c6:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "fill.length") c5) σ;
                                                                     let c7:Env→ Prop:=fun (σ':Env) =>
                                                                       And (c3 σ' ((6:Nat))) (c6 σ');
                                                                     let c8:Nat:=c4 (Env.vars σ "catalog.count");
                                                                     let c9:Env:=Env.setVar σ "fill.length" c8;
                                                                     @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                                                                       (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c7) a
                                                                       fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                                                                       @Exists.intro Env c7 c9
                                                                         (@And.intro (c3 c9 ((6:Nat))) (c6 c9)
                                                                           (RunStep.mono B c2 σ c9
                                                                             (Nat.add
                                                                               ((1:Nat)) (Expr.size c1))
                                                                             ((6:Nat))
                                                                             (RunStep.assign B σ "fill.length" c1 c8
                                                                               (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                                                                 (Expr.var "catalog.count") ((2:Nat))
                                                                                 (Env.vars σ "catalog.count")
                                                                                 (RunStep.eval_lit B ((2:Nat)) σ
                                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                 (RunStep.eval_var B σ "catalog.count"
                                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                           ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                             | (expose_names;
                                                                 (refine
                                                                     fun (σ:Env)
                                                                       (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") (dimension n r))) =>
                                                                     let c0:Prop:= @Eq Nat (Env.vars σ "catalog.count") (dimension n r);
                                                                     let c1:Com:=Com.assign "fill.length" (Expr.mul (Expr.var "catalog.count") (Expr.var "catalog.count"));
                                                                     let c2:Env→ Nat→ Prop:=Run B c1 σ;
                                                                     let c3:Nat→ Nat→ Nat:=Nat.mul;
                                                                     let c4:Nat:=c3 (dimension n r) (dimension n r);
                                                                     let c5:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "fill.length") c4) σ;
                                                                     let c6:Env→ Prop:=fun (σ':Env) =>
                                                                       And (c2 σ' ((6:Nat))) (c5 σ');
                                                                     let c7:Nat:=c3 (Env.vars σ "catalog.count") (Env.vars σ "catalog.count");
                                                                     let c8:Env:=Env.setVar σ "fill.length" c7;
                                                                     @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                                                                       (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c6) a
                                                                       fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                                                                       @Exists.intro Env c6 c8
                                                                         (@And.intro (c2 c8 ((6:Nat))) (c5 c8)
                                                                           (RunStep.mono B c1 σ c8
                                                                             (Nat.add
                                                                               ((1:Nat))
                                                                               (Expr.size (Expr.mul (Expr.var "catalog.count") (Expr.var "catalog.count"))))
                                                                             ((6:Nat))
                                                                             (RunStep.assign B σ "fill.length" (Expr.mul (Expr.var "catalog.count") (Expr.var "catalog.count")) c7
                                                                               (RunStep.eval_mul B σ (Expr.var "catalog.count") (Expr.var "catalog.count") (Env.vars σ "catalog.count")
                                                                                 (Env.vars σ "catalog.count")
                                                                                 (RunStep.eval_var B σ "catalog.count"
                                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                 (RunStep.eval_var B σ "catalog.count"
                                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                 ?_))
                                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                           ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                             | (expose_names;
                                                                 (refine
                                                                     fun (σ:Env)
                                                                       (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") (dimension n r))) =>
                                                                     let c0:Prop:= @Eq Nat (Env.vars σ "catalog.count") (dimension n r);
                                                                     let c1:Expr:=Expr.mul (Expr.mul (Expr.var "catalog.count") (Expr.var "graph.n")) (Expr.var "catalog.count");
                                                                     let c2:Com:=Com.assign "fill.length" c1;
                                                                     let c3:Env→ Nat→ Prop:=Run B c2 σ;
                                                                     let c4:Nat→ Nat→ Nat:=Nat.mul;
                                                                     let c5:Nat:=c4 (c4 (dimension n r) n) (dimension n r);
                                                                     let c6:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "fill.length") c5) σ;
                                                                     let c7:Env→ Prop:=fun (σ':Env) =>
                                                                       And (c3 σ' ((6:Nat))) (c6 σ');
                                                                     let c8:Nat:=c4 (Env.vars σ "catalog.count") (Env.vars σ "graph.n");
                                                                     let c9:Nat:=c4 c8 (Env.vars σ "catalog.count");
                                                                     let c10:Env:=Env.setVar σ "fill.length" c9;
                                                                     @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) c0
                                                                       (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) c0) => @Exists Env c7) a
                                                                       fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:c0) =>
                                                                       @Exists.intro Env c7 c10
                                                                         (@And.intro (c3 c10 ((6:Nat))) (c6 c10)
                                                                           (RunStep.mono B c2 σ c10
                                                                             (Nat.add
                                                                               ((1:Nat)) (Expr.size c1))
                                                                             ((6:Nat))
                                                                             (RunStep.assign B σ "fill.length" c1 c9
                                                                               (RunStep.eval_mul B σ (Expr.mul (Expr.var "catalog.count") (Expr.var "graph.n"))
                                                                                 (Expr.var "catalog.count") c8 (Env.vars σ "catalog.count")
                                                                                 (RunStep.eval_mul B σ (Expr.var "catalog.count") (Expr.var "graph.n") (Env.vars σ "catalog.count")
                                                                                   (Env.vars σ "graph.n")
                                                                                   (RunStep.eval_var B σ "catalog.count"
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                   (RunStep.eval_var B σ "graph.n"
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                   ?_)
                                                                                 (RunStep.eval_var B σ "catalog.count"
                                                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                 ?_))
                                                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                           ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                            )
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem command_spec (kind:Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (front:List ℕ)
    (hB:front.length+3*(rowCount kind n r*dimension n r)+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "lp.length"=front.length∧
      front.length+3*(rowCount kind n r*dimension n r)≤ (σ.arrs "lp.input").length∧
      Lax455465Proofs.RamVirtualState.Prefix front "lp.input" σ)
      (command kind) (fun _ τ => Data G k r τ∧
        τ.vars "lp.length"=front.length+3*(rowCount kind n r*dimension n r)∧
        Lax455465Proofs.RamVirtualState.Prefix (front++NativeMomentAssembly.matrixWords (matrix kind G k r)) "lp.input" τ)
      ((22*n+129)*(rowCount kind n r*dimension n r)+12):=by
  rintro σ ⟨hd,hl,hr,hp⟩
  obtain ⟨ν,r1,p1⟩:=count_spec kind n r B (by omega) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have d1:=data_frame G k r r1
    (by simp [fixedVars,Com.wvars])
    (by simp [fixedArrays,Com.warrs]) hd
  obtain ⟨τ,r2,p2⟩:=append_matrix_spec kind B G k r front hB hm ν
    ⟨d1,p1,(r1.frame_var "lp.length" (by simp [Com.wvars])).trans hl,
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by simpa only [Lax455465Proofs.RamVirtualState.Prefix,r1.frame_arr "lp.input" (by simp [Com.warrs])] using hp⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

end Lax263307Proofs.NativeMomentFamily

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily

def entryCount (ks:List Kind) (n r:ℕ):ℕ:=
  (ks.map fun kind => NativeMomentFamily.rowCount kind n r*dimension n r).sum

def words (ks:List Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):List ℕ:=
  ks.flatMap fun kind => NativeMomentAssembly.matrixWords (matrix kind G k r)

theorem command_spec (ks:List Kind) {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (front:List ℕ)
    (hB:front.length+3*entryCount ks n r+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "lp.length"=front.length∧
      front.length+3*entryCount ks n r≤ (σ.arrs "lp.input").length∧ Prefix front "lp.input" σ)
      (command ks) (fun _ τ => Data G k r τ∧ τ.vars "lp.length"=front.length+3*entryCount ks n r∧
        Prefix (front++words ks G k r) "lp.input" τ)
      ((22*n+129)*entryCount ks n r+12*ks.length+1):=by
  induction ks generalizing front with
  | nil =>
    intro σ hσ
    exact ⟨σ,Run.skip.mono (by simp [entryCount]),hσ.1,by simpa [entryCount] using hσ.2.1,by simpa [words] using hσ.2.2.2⟩
  | cons kind ks ih =>
    have he:entryCount (kind::ks) n r=NativeMomentFamily.rowCount kind n r*dimension n r+entryCount ks n r:=rfl
    rintro σ ⟨hd,hl,hr,hp⟩
    obtain ⟨ν,r1,p1⟩:=NativeMomentFamily.command_spec kind B G k r front (by rw [he] at hB; omega) hm σ
      ⟨hd,hl,by rw [he] at hr; omega,hp⟩
    let next:=front++NativeMomentAssembly.matrixWords (matrix kind G k r)
    have hlen:next.length=front.length+3*(NativeMomentFamily.rowCount kind n r*dimension n r):=by
      simp only [next,List.length_append,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
    obtain ⟨τ,r2,p2⟩:=ih next (by rw [hlen]; rw [he] at hB; omega) ν
      ⟨p1.1,by rw [hlen]; exact p1.2.1,by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; rw [he] at hr; omega,p1.2.2⟩
    refine ⟨τ,(r1.seq r2).mono (by rw [he,List.length_cons]; nlinarith),p2.1,?_,?_⟩
    · rw [he,hlen] at *
      omega
    · simpa only [next,words,List.flatMap_cons,List.append_assoc] using p2.2.2

theorem all_count (n r:ℕ):entryCount allKinds n r=NativeMomentAssembly.rowCount n r*dimension n r:=by
  simp only [entryCount,allKinds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NativeMomentFamily.rowCount,NativeMomentAssembly.rowCount]
  ring

theorem all_words {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    words allKinds G k r=NativeMomentAssembly.matrixWords (MomentLP.program G k r).A:=by
  rw [NativeMomentAssembly.matrix_words_exact]
  simp only [words,allKinds,matrix,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

end Lax263307Proofs.NativeMomentMatrix

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce

def entries (N zeros:ℕ):List ℚ:= [1,-1]++List.replicate N 1++List.replicate zeros 0

def value (N q:ℕ):ℚ:=if q=1 then -1 else if q < N+2 then 1 else 0

theorem entries_length (N zeros:ℕ):(entries N zeros).length=2+N+zeros:=by simp [entries]; omega

theorem entries_get (N zeros q:ℕ) (hq:q < 2+N+zeros):
    (entries N zeros)[q]?=some (value N q):=by
  cases q with
  | zero => simp [entries,value]
  | succ q =>
    cases q with
    | zero => simp [entries,value]
    | succ q =>
      have he:(entries N zeros)[q+2]?=(List.replicate N (1:ℚ)++List.replicate zeros 0)[q]?:=by simp [entries]
      rw [he]
      by_cases h:q < N
      · rw [List.getElem?_append_left (by simpa using h)]
        simp [h,value,show q+2 < N+2 by omega]
      · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
        have htail:q-N < zeros:=by omega
        simp [htail,value,show ¬q+2 < N+2 by omega]

theorem read_spec (B N q:ℕ) (hB:q+N+4 < B):
    Spec B (fun σ => σ.vars "fill.i"=q∧ σ.vars "catalog.count"=N) read
      (fun _ τ => Value B (value N q) τ) 18:=by
  by_cases hq:q=1
  · subst q
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") ((1:Nat))) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c1:Env→ Prop:=Value B (value N ((1:Nat))); let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Prop:=Not c0; let c6:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c7:Nat:=Env.vars c6 "fill.i"; let c8:Prop:= @Eq Nat c7 ((1:Nat)); let c9:Prop:=Not c8; let c10:Nat→ Env:=Env.setVar c6 "coefficient.negative"; let c11:Env:=c10 ((1:Nat)); let c12:Nat→ Nat→ Nat:=Nat.add; let c13:Nat→ Nat:=c12 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c15:Nat→ Nat:=c12 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat:=c15 c16; let c18:Nat→ Nat:=c12 c17; let c19:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c20:Nat:=c15 c19; let c21:Com→ Com→ Com:=Com.ite c14; let c22:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c23:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c24:Cond:=Cond.lt (Expr.var "fill.i") c23; let c25:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c26:Com:=Com.ite c24 c25 c22; let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c28:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c29:Env:=c10 ((0:Nat)); let c30:Nat:=c12 (Env.vars σ "catalog.count") ((2:Nat)); let c31:Prop:=Nat.lt (Env.vars σ "fill.i") c30; let c32:Prop:=Not c31; let c33:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c34:Nat:=Env.vars c33 "fill.i"; let c35:Prop:= @Eq Nat c34 ((1:Nat)); let c36:Prop:=Not c35; let c37:Nat→ Env:=Env.setVar c33 "coefficient.negative"; let c38:Env:=c37 ((1:Nat)); let c39:Nat→ Nat:=c12 (c13 (Cond.size c24)); let c40:Nat:=c39 c19; let c41:Nat:=c15 c40; let c42:Nat→ Nat:=c12 c41; let c43:Env:=c37 ((0:Nat)); let c44:Nat:=c39 c16; let c45:Nat:=c15 c44; let c46:Nat→ Nat:=c12 c45; @And.casesOn c0 (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And c0 (@Eq Nat (Env.vars σ "catalog.count") N)) => c4) a fun (left:c0) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c0 c5 (fun (x:Or c0 c5) => c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c4) (Classical.em c8) (fun (hcase_1:c8) => @Exists.intro Env c3 c11 (@And.intro (Run B read σ c11 ((18:Nat))) (c2 c11) (RunStep.mono B read σ c11 (c18 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c11 c17 c20 (RunStep.ite_true B c14 c22 c26 σ c6 c16 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_2)))) (RunStep.ite_true B c14 c27 c28 c6 c11 c19 (RunStep.cond_eq_true B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_4)) hcase_1) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_5))))) (?nAX_g8213_0_0_6)) ?_)) fun (hcase_1:c9) => @Exists.intro Env c3 c29 (@And.intro (Run B read σ c29 ((18:Nat))) (c2 c29) (RunStep.mono B read σ c29 (c18 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c29 c17 c17 (RunStep.ite_true B c14 c22 c26 σ c6 c16 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_9)))) (RunStep.ite_false B c14 c27 c28 c6 c29 c16 (RunStep.cond_eq_false B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_10)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_11)) hcase_1) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c6 (?nAX_g8213_0_0_12))))) (?nAX_g8213_0_0_13)) ?_)) fun (hcase:c5) => @Or.casesOn c31 c32 (fun (x:Or c31 c32) => c4) (Classical.em c31) (fun (hcase_1:c31) => @Or.casesOn c35 c36 (fun (x:Or c35 c36) => c4) (Classical.em c35) (fun (hcase_2:c35) => @Exists.intro Env c3 c38 (@And.intro (Run B read σ c38 ((18:Nat))) (c2 c38) (RunStep.mono B read σ c38 (c42 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c33 c38 c41 c20 (RunStep.ite_false B c14 c22 c26 σ c33 c40 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_15)) hcase) (RunStep.ite_true B c24 c25 c22 σ c33 c19 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_18)) (?nAX_g8213_0_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_20))))) (RunStep.ite_true B c14 c27 c28 c33 c38 c19 (RunStep.cond_eq_true B c33 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c34 ((1:Nat)) (RunStep.eval_var B c33 "fill.i" (?nAX_g8213_0_0_21)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_22)) hcase_2) (RunStep.assign B c33 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_23))))) (?nAX_g8213_0_0_24)) ?_)) fun (hcase_2:c36) => @Exists.intro Env c3 c43 (@And.intro (Run B read σ c43 ((18:Nat))) (c2 c43) (RunStep.mono B read σ c43 (c42 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c33 c43 c41 c17 (RunStep.ite_false B c14 c22 c26 σ c33 c40 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_26)) hcase) (RunStep.ite_true B c24 c25 c22 σ c33 c19 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_29)) (?nAX_g8213_0_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_31))))) (RunStep.ite_false B c14 c27 c28 c33 c43 c16 (RunStep.cond_eq_false B c33 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c34 ((1:Nat)) (RunStep.eval_var B c33 "fill.i" (?nAX_g8213_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c33 (?nAX_g8213_0_0_33)) hcase_2) (RunStep.assign B c33 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c33 (?nAX_g8213_0_0_34))))) (?nAX_g8213_0_0_35)) ?_)) fun (hcase_1:c32) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c4) (Classical.em c8) (fun (hcase_2:c8) => @Exists.intro Env c3 c11 (@And.intro (Run B read σ c11 ((18:Nat))) (c2 c11) (RunStep.mono B read σ c11 (c46 c20) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c11 c45 c20 (RunStep.ite_false B c14 c22 c26 σ c6 c44 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_37)) hcase) (RunStep.ite_false B c24 c25 c22 σ c6 c16 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_40)) (?nAX_g8213_0_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_42))))) (RunStep.ite_true B c14 c27 c28 c6 c11 c19 (RunStep.cond_eq_true B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_43)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_44)) hcase_2) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_45))))) (?nAX_g8213_0_0_46)) ?_)) fun (hcase_2:c9) => @Exists.intro Env c3 c29 (@And.intro (Run B read σ c29 ((18:Nat))) (c2 c29) (RunStep.mono B read σ c29 (c46 c17) ((18:Nat)) (RunStep.seq B (c21 c22 c26) (c21 c27 c28) σ c6 c29 c45 c17 (RunStep.ite_false B c14 c22 c26 σ c6 c44 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_0_0_48)) hcase) (RunStep.ite_false B c24 c25 c22 σ c6 c16 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c23 (Env.vars σ "fill.i") c30 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_0_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_0_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_0_0_51)) (?nAX_g8213_0_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_0_0_53))))) (RunStep.ite_false B c14 c27 c28 c6 c29 c16 (RunStep.cond_eq_false B c6 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "fill.i" (?nAX_g8213_0_0_54)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g8213_0_0_55)) hcase_2) (RunStep.assign B c6 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c6 (?nAX_g8213_0_0_56))))) (?nAX_g8213_0_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Value,value,Env.setVar]
    all_goals omega
  · by_cases ht:q < N+2
    · (expose_names;
        (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Env→ Prop:=(fun (x τ:Env) => Value B (value N q) τ) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c6:Nat:=Env.vars c5 "fill.i"; let c7:Prop:= @Eq Nat c6 ((1:Nat)); let c8:Prop:=Not c7; let c9:Nat→ Env:=Env.setVar c5 "coefficient.negative"; let c10:Env:=c9 ((1:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat:=c14 c15; let c17:Nat→ Nat:=c11 c16; let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c19:Nat:=c14 c18; let c20:Com→ Com→ Com:=Com.ite c13; let c21:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c22:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c23:Cond:=Cond.lt (Expr.var "fill.i") c22; let c24:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c25:Com:=Com.ite c23 c24 c21; let c26:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c28:Env:=c9 ((0:Nat)); let c29:Nat:=c11 (Env.vars σ "catalog.count") ((2:Nat)); let c30:Prop:=Nat.lt (Env.vars σ "fill.i") c29; let c31:Prop:=Not c30; let c32:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c33:Nat:=Env.vars c32 "fill.i"; let c34:Prop:= @Eq Nat c33 ((1:Nat)); let c35:Prop:=Not c34; let c36:Nat→ Env:=Env.setVar c32 "coefficient.negative"; let c37:Env:=c36 ((1:Nat)); let c38:Nat→ Nat:=c11 (c12 (Cond.size c23)); let c39:Nat:=c38 c18; let c40:Nat:=c14 c39; let c41:Nat→ Nat:=c11 c40; let c42:Env:=c36 ((0:Nat)); let c43:Nat:=c38 c15; let c44:Nat:=c14 c43; let c45:Nat→ Nat:=c11 c44; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => c2) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_1:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c17 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c16 c19 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_2)))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_3)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_4)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_5))))) (?nAX_g8213_1_0_6)) ?_)) fun (hcase_1:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c17 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c16 c16 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_9)))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_10)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_11)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_1_0_12))))) (?nAX_g8213_1_0_13)) ?_)) fun (hcase:c4) => @Or.casesOn c30 c31 (fun (x:Or c30 c31) => c2) (Classical.em c30) (fun (hcase_1:c30) => @Or.casesOn c34 c35 (fun (x:Or c34 c35) => c2) (Classical.em c34) (fun (hcase_2:c34) => @Exists.intro Env c1 c37 (@And.intro (Run B read σ c37 ((18:Nat))) (c0 c37) (RunStep.mono B read σ c37 (c41 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c37 c40 c19 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_15)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_18)) (?nAX_g8213_1_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_20))))) (RunStep.ite_true B c13 c26 c27 c32 c37 c18 (RunStep.cond_eq_true B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_1_0_21)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_22)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_23))))) (?nAX_g8213_1_0_24)) ?_)) fun (hcase_2:c35) => @Exists.intro Env c1 c42 (@And.intro (Run B read σ c42 ((18:Nat))) (c0 c42) (RunStep.mono B read σ c42 (c41 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c42 c40 c16 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_26)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_29)) (?nAX_g8213_1_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_31))))) (RunStep.ite_false B c13 c26 c27 c32 c42 c15 (RunStep.cond_eq_false B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_1_0_32)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_1_0_33)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c32 (?nAX_g8213_1_0_34))))) (?nAX_g8213_1_0_35)) ?_)) fun (hcase_1:c31) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_2:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c45 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c44 c19 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_37)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_40)) (?nAX_g8213_1_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_42))))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_43)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_44)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_45))))) (?nAX_g8213_1_0_46)) ?_)) fun (hcase_2:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c45 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c44 c16 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_1_0_48)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_1_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_1_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_1_0_51)) (?nAX_g8213_1_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_1_0_53))))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_1_0_54)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_1_0_55)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_1_0_56))))) (?nAX_g8213_1_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_1_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega
    · (expose_names;
        (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Env→ Prop:=(fun (x τ:Env) => Value B (value N q) τ) σ; let c1:Env→ Prop:=fun (σ':Env) => And (Run B read σ σ' ((18:Nat))) (c0 σ'); let c2:Prop:= @Exists Env c1; let c3:Prop:= @Eq Nat (Env.vars σ "fill.i") ((1:Nat)); let c4:Prop:=Not c3; let c5:Env:=Env.setVar σ "coefficient.positive" ((0:Nat)); let c6:Nat:=Env.vars c5 "fill.i"; let c7:Prop:= @Eq Nat c6 ((1:Nat)); let c8:Prop:=Not c7; let c9:Nat→ Env:=Env.setVar c5 "coefficient.negative"; let c10:Env:=c9 ((1:Nat)); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Cond:=Cond.eq (Expr.var "fill.i") (Expr.lit ((1:Nat))); let c14:Nat→ Nat:=c11 (c12 (Cond.size c13)); let c15:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c16:Nat:=c14 c15; let c17:Nat→ Nat:=c11 c16; let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c19:Nat:=c14 c18; let c20:Com→ Com→ Com:=Com.ite c13; let c21:Com:=Com.assign "coefficient.positive" (Expr.lit ((0:Nat))); let c22:Expr:=Expr.add (Expr.var "catalog.count") (Expr.lit ((2:Nat))); let c23:Cond:=Cond.lt (Expr.var "fill.i") c22; let c24:Com:=Com.assign "coefficient.positive" (Expr.lit ((1:Nat))); let c25:Com:=Com.ite c23 c24 c21; let c26:Com:=Com.assign "coefficient.negative" (Expr.lit ((1:Nat))); let c27:Com:=Com.assign "coefficient.negative" (Expr.lit ((0:Nat))); let c28:Env:=c9 ((0:Nat)); let c29:Nat:=c11 (Env.vars σ "catalog.count") ((2:Nat)); let c30:Prop:=Nat.lt (Env.vars σ "fill.i") c29; let c31:Prop:=Not c30; let c32:Env:=Env.setVar σ "coefficient.positive" ((1:Nat)); let c33:Nat:=Env.vars c32 "fill.i"; let c34:Prop:= @Eq Nat c33 ((1:Nat)); let c35:Prop:=Not c34; let c36:Nat→ Env:=Env.setVar c32 "coefficient.negative"; let c37:Env:=c36 ((1:Nat)); let c38:Nat→ Nat:=c11 (c12 (Cond.size c23)); let c39:Nat:=c38 c18; let c40:Nat:=c14 c39; let c41:Nat→ Nat:=c11 c40; let c42:Env:=c36 ((0:Nat)); let c43:Nat:=c38 c15; let c44:Nat:=c14 c43; let c45:Nat→ Nat:=c11 c44; @And.casesOn (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "fill.i") q) (@Eq Nat (Env.vars σ "catalog.count") N)) => c2) a fun (left:@Eq Nat (Env.vars σ "fill.i") q) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Or.casesOn c3 c4 (fun (x:Or c3 c4) => c2) (Classical.em c3) (fun (hcase:c3) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_1:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c17 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c16 c19 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_0)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_1)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_2)))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_3)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_4)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_5))))) (?nAX_g8213_2_0_6)) ?_)) fun (hcase_1:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c17 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c16 c16 (RunStep.ite_true B c13 c21 c25 σ c5 c15 (RunStep.cond_eq_true B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_7)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_8)) hcase) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_9)))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_10)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_11)) hcase_1) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_2_0_12))))) (?nAX_g8213_2_0_13)) ?_)) fun (hcase:c4) => @Or.casesOn c30 c31 (fun (x:Or c30 c31) => c2) (Classical.em c30) (fun (hcase_1:c30) => @Or.casesOn c34 c35 (fun (x:Or c34 c35) => c2) (Classical.em c34) (fun (hcase_2:c34) => @Exists.intro Env c1 c37 (@And.intro (Run B read σ c37 ((18:Nat))) (c0 c37) (RunStep.mono B read σ c37 (c41 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c37 c40 c19 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_14)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_15)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_16)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_17)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_18)) (?nAX_g8213_2_0_19)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_20))))) (RunStep.ite_true B c13 c26 c27 c32 c37 c18 (RunStep.cond_eq_true B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_2_0_21)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_22)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_23))))) (?nAX_g8213_2_0_24)) ?_)) fun (hcase_2:c35) => @Exists.intro Env c1 c42 (@And.intro (Run B read σ c42 ((18:Nat))) (c0 c42) (RunStep.mono B read σ c42 (c41 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c32 c42 c40 c16 (RunStep.ite_false B c13 c21 c25 σ c32 c39 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_25)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_26)) hcase) (RunStep.ite_true B c23 c24 c21 σ c32 c18 (RunStep.cond_lt_true B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_27)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_28)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_29)) (?nAX_g8213_2_0_30)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_31))))) (RunStep.ite_false B c13 c26 c27 c32 c42 c15 (RunStep.cond_eq_false B c32 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c33 ((1:Nat)) (RunStep.eval_var B c32 "fill.i" (?nAX_g8213_2_0_32)) (RunStep.eval_lit B ((1:Nat)) c32 (?nAX_g8213_2_0_33)) hcase_2) (RunStep.assign B c32 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c32 (?nAX_g8213_2_0_34))))) (?nAX_g8213_2_0_35)) ?_)) fun (hcase_1:c31) => @Or.casesOn c7 c8 (fun (x:Or c7 c8) => c2) (Classical.em c7) (fun (hcase_2:c7) => @Exists.intro Env c1 c10 (@And.intro (Run B read σ c10 ((18:Nat))) (c0 c10) (RunStep.mono B read σ c10 (c45 c19) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c10 c44 c19 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_36)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_37)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_38)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_39)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_40)) (?nAX_g8213_2_0_41)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_42))))) (RunStep.ite_true B c13 c26 c27 c5 c10 c18 (RunStep.cond_eq_true B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_43)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_44)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_45))))) (?nAX_g8213_2_0_46)) ?_)) fun (hcase_2:c8) => @Exists.intro Env c1 c28 (@And.intro (Run B read σ c28 ((18:Nat))) (c0 c28) (RunStep.mono B read σ c28 (c45 c16) ((18:Nat)) (RunStep.seq B (c20 c21 c25) (c20 c26 c27) σ c5 c28 c44 c16 (RunStep.ite_false B c13 c21 c25 σ c5 c43 (RunStep.cond_eq_false B σ (Expr.var "fill.i") (Expr.lit ((1:Nat))) (Env.vars σ "fill.i") ((1:Nat)) (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_47)) (RunStep.eval_lit B ((1:Nat)) σ (?nAX_g8213_2_0_48)) hcase) (RunStep.ite_false B c23 c24 c21 σ c5 c15 (RunStep.cond_lt_false B σ (Expr.var "fill.i") c22 (Env.vars σ "fill.i") c29 (RunStep.eval_var B σ "fill.i" (?nAX_g8213_2_0_49)) (RunStep.eval_add B σ (Expr.var "catalog.count") (Expr.lit ((2:Nat))) (Env.vars σ "catalog.count") ((2:Nat)) (RunStep.eval_var B σ "catalog.count" (?nAX_g8213_2_0_50)) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8213_2_0_51)) (?nAX_g8213_2_0_52)) hcase_1) (RunStep.assign B σ "coefficient.positive" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8213_2_0_53))))) (RunStep.ite_false B c13 c26 c27 c5 c28 c15 (RunStep.cond_eq_false B c5 (Expr.var "fill.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "fill.i" (?nAX_g8213_2_0_54)) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g8213_2_0_55)) hcase_2) (RunStep.assign B c5 "coefficient.negative" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c5 (?nAX_g8213_2_0_56))))) (?nAX_g8213_2_0_57)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8213_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8213_2_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega

def size (n r:ℕ):ℕ:=2+dimension n r+dimension n r*(n+4)

theorem count_spec (B n N:ℕ) (hB:2+N+N*(n+4)+n+10 < B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "catalog.count"=N)
      (.assign "fill.length" countExpr) (fun _ τ => τ.vars "fill.length"=2+N+N*(n+4)) 8:=by
  have hm:N*(n+5)=N+N*(n+4):=by ring
  simp only [countExpr]
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Expr:=Expr.add (Expr.var "graph.n") (Expr.lit ((5:Nat))); let c1:Expr:=Expr.mul (Expr.var "catalog.count") c0; let c2:Expr:=Expr.add (Expr.lit ((2:Nat))) c1; let c3:Com:=Com.assign "fill.length" c2; let c4:Env→ Nat→ Prop:=Run B c3 σ; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((2:Nat)); let c7:Nat→ Nat→ Nat:=Nat.mul; let c8:Nat:=c5 (c6 N) (c7 N (c5 n ((4:Nat)))); let c9:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "fill.length") c8) σ; let c10:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((8:Nat))) (c9 σ'); let c11:Nat:=c5 (Env.vars σ "graph.n") ((5:Nat)); let c12:Nat:=c7 (Env.vars σ "catalog.count") c11; let c13:Nat:=c6 c12; let c14:Env:=Env.setVar σ "fill.length" c13; @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N)) => @Exists Env c10) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Exists.intro Env c10 c14 (@And.intro (c4 c14 ((8:Nat))) (c9 c14) (RunStep.mono B c3 σ c14 (c5 ((1:Nat)) (Expr.size c2)) ((8:Nat)) (RunStep.assign B σ "fill.length" c2 c13 (RunStep.eval_add B σ (Expr.lit ((2:Nat))) c1 ((2:Nat)) c12 (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8217_0_0_0)) (RunStep.eval_mul B σ (Expr.var "catalog.count") c0 (Env.vars σ "catalog.count") c11 (RunStep.eval_var B σ "catalog.count" (?nAX_g8217_0_0_1)) (RunStep.eval_add B σ (Expr.var "graph.n") (Expr.lit ((5:Nat))) (Env.vars σ "graph.n") ((5:Nat)) (RunStep.eval_var B σ "graph.n" (?nAX_g8217_0_0_2)) (RunStep.eval_lit B ((5:Nat)) σ (?nAX_g8217_0_0_3)) (?nAX_g8217_0_0_4)) ?_) ?_)) (?nAX_g8217_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8217_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8217_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8217_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8217_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8217_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8217_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem vector_entries {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    List.ofFn (MomentLP.program G k r).b++List.ofFn (MomentLP.program G k r).c=
      entries (dimension n r) (dimension n r*(n+4)):=by
  simp only [MomentLP.program,NativeMomentAssembly.ofFn_addCases,List.ofFn_const]
  norm_num only [List.ofFn_succ,List.ofFn_zero,Fin.isValue,Fin.succ_ne_zero,if_true,if_false]
  simp only [entries,List.append_assoc]
  have hz:dimension n r+(dimension n r*n+(dimension n r+dimension n r))+dimension n r=dimension n r*(n+4):=by ring
  rw [←List.replicate_add,hz]

theorem words_exact {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    NativeRationalTabulate.words (entries (dimension n r) (dimension n r*(n+4)))=
      Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).b++Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).c:=by
  rw [←vector_entries G k r,NativeRationalTabulate.words_append]
  rfl

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (front:List ℕ)
    (hB:front.length+3*size n r+n+k+r+dimension n r+10 < B):
    Spec B (fun σ => Data G k r σ∧ σ.vars "lp.length"=front.length∧
      front.length+3*size n r≤ (σ.arrs "lp.input").length∧ Prefix front "lp.input" σ)
      command (fun _ τ => Data G k r τ∧ τ.vars "lp.length"=front.length+3*size n r∧
        Prefix (front++(Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).b++
          Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).c)) "lp.input" τ)
      (57*size n r+14):=by
  have hlen:(entries (dimension n r) (dimension n r*(n+4))).length=size n r:=entries_length _ _
  have ht:=NativeRationalTabulate.command_spec B (entries (dimension n r) (dimension n r*(n+4))) front (Data G k r) read 18
    (by rw [hlen]; omega) (by decide) (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,NativeMomentAccess.Data,NativeCatalogMetadata.Data,Prefix] using h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro q hq σ hσ
      have hq':q < size n r:=by rwa [hlen] at hq
      obtain ⟨τ,rr,p⟩:=read_spec B (dimension n r) q (by omega) σ ⟨hσ.2,hσ.1.1.1.2.1⟩
      have he:=entries_get (dimension n r) (dimension n r*(n+4)) q hq'
      rw [List.getElem?_eq_getElem hq] at he
      refine ⟨τ,rr,data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hσ.1,?_⟩
      simpa only [Value,Option.some.inj he] using p)
  rintro σ ⟨hd,hl,hr,hp⟩
  obtain ⟨ν,r1,p1⟩:=count_spec B n (dimension n r) (by dsimp [size] at hB; omega) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have d1:=data_frame G k r r1
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd
  obtain ⟨τ,r2,p2⟩:=ht ν ⟨d1,by rw [hlen]; exact p1,
    (r1.frame_var "lp.length" (by decide)).trans hl,
    by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; exact hr,
    by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hp⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2.1,by simpa only [hlen] using p2.2.1,?_⟩
  simpa only [words_exact G k r] using p2.2.2

end Lax263307Proofs.NativeMomentVectors

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP NativeMomentFamily
open Lax109476.RationalEncoding

theorem row_count_eq (n r:ℕ):M n r=2+dimension n r*(n+4):=by
  unfold M NativeMomentAssembly.rowCount
  ring

theorem vector_size (n r:ℕ):NativeMomentVectors.size n r=M n r+dimension n r:=by
  rw [row_count_eq]
  unfold NativeMomentVectors.size
  omega

theorem row_count_spec (B n N:ℕ) (hB:2+N*(n+4)+n+N+10 < B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "catalog.count"=N)
      (.assign "moment.rows" rowCountExpr) (fun _ τ => τ.vars "moment.rows"=2+N*(n+4)) 8:=by
  simp only [rowCountExpr]
  (expose_names;
    (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N)) => let c0:Expr:=Expr.add (Expr.var "graph.n") (Expr.lit ((4:Nat))); let c1:Expr:=Expr.mul (Expr.var "catalog.count") c0; let c2:Expr:=Expr.add (Expr.lit ((2:Nat))) c1; let c3:Com:=Com.assign "moment.rows" c2; let c4:Env→ Nat→ Prop:=Run B c3 σ; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((2:Nat)); let c7:Nat→ Nat→ Nat:=Nat.mul; let c8:Nat:=c6 (c7 N (c5 n ((4:Nat)))); let c9:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "moment.rows") c8) σ; let c10:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((8:Nat))) (c9 σ'); let c11:Nat:=c5 (Env.vars σ "graph.n") ((4:Nat)); let c12:Nat:=c7 (Env.vars σ "catalog.count") c11; let c13:Nat:=c6 c12; let c14:Env:=Env.setVar σ "moment.rows" c13; @And.casesOn (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N) (fun (x:And (@Eq Nat (Env.vars σ "graph.n") n) (@Eq Nat (Env.vars σ "catalog.count") N)) => @Exists Env c10) a fun (left:@Eq Nat (Env.vars σ "graph.n") n) (right:@Eq Nat (Env.vars σ "catalog.count") N) => @Exists.intro Env c10 c14 (@And.intro (c4 c14 ((8:Nat))) (c9 c14) (RunStep.mono B c3 σ c14 (c5 ((1:Nat)) (Expr.size c2)) ((8:Nat)) (RunStep.assign B σ "moment.rows" c2 c13 (RunStep.eval_add B σ (Expr.lit ((2:Nat))) c1 ((2:Nat)) c12 (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g8226_0_0_0)) (RunStep.eval_mul B σ (Expr.var "catalog.count") c0 (Env.vars σ "catalog.count") c11 (RunStep.eval_var B σ "catalog.count" (?nAX_g8226_0_0_1)) (RunStep.eval_add B σ (Expr.var "graph.n") (Expr.lit ((4:Nat))) (Env.vars σ "graph.n") ((4:Nat)) (RunStep.eval_var B σ "graph.n" (?nAX_g8226_0_0_2)) (RunStep.eval_lit B ((4:Nat)) σ (?nAX_g8226_0_0_3)) (?nAX_g8226_0_0_4)) ?_) ?_)) (?nAX_g8226_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8226_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8226_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8226_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8226_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8226_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8226_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem header_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (hB:M n r+n+dimension n r+10 < B):
    Spec B (fun σ => Data G k r σ∧ 2≤ (σ.arrs "lp.input").length) header
      (fun _ τ => Data G k r τ∧ τ.vars "lp.length"=2∧ Prefix [M n r,dimension n r] "lp.input" τ) 24:=by
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩:=row_count_spec B n (dimension n r) (by rwa [row_count_eq] at hB) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have hrows:ν.vars "moment.rows"=M n r:=by rwa [row_count_eq]
  let μ:=ν.setVar "lp.length" 0
  have r2:Run B (.assign "lp.length" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (by omega))
  have hm:μ.vars "moment.rows"=M n r:=(r2.frame_var "moment.rows" (by decide)).trans hrows
  have hc:μ.vars "catalog.count"=dimension n r:=((r1.seq r2).frame_var "catalog.count" (by decide)).trans hd.1.1.2.1
  obtain ⟨ξ,r3,p3⟩:=RamWordBuffer.append_spec B "lp.input" "lp.length" [] (M n r) (.var "moment.rows")
    (by omega) (by simp; omega) μ
    ⟨by simp [Prefix],by simp [μ],by rw [RamFrames.run_array_length (r1.seq r2)]; simp only [List.length_nil]; omega,
      by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ (by omega)⟩⟩
  have hcξ:ξ.vars "catalog.count"=dimension n r:=(r3.frame_var "catalog.count" (by decide)).trans hc
  obtain ⟨τ,r4,p4⟩:=RamWordBuffer.append_spec B "lp.input" "lp.length" [M n r] (dimension n r) (.var "catalog.count")
    (by omega) (by simp; omega) ξ
    ⟨by simpa using p3.1,by simpa using p3.2,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; simp only [List.length_singleton]; omega,
      by rw [evalB_var_iff]; exact ⟨hcξ.symm,hcξ ▸ (by omega)⟩⟩
  have rr:Run B header σ τ 24:=r1.seq (r2.seq (r3.seq r4))
  exact ⟨τ,rr,data_frame G k r rr
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd,
    by simpa using p4.2,by simpa using p4.1⟩

theorem input_length {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    (encodeProgram (MomentLP.program G k r)).length=length n r:=by
  have hv:(encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=3*(M n r+dimension n r):=by
    rw [←NativeMomentVectors.words_exact G k r,NativeRationalTabulate.words_length,NativeMomentVectors.entries_length]
    change 3*NativeMomentVectors.size n r=_
    rw [vector_size]
  change ([M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A++
    encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=_
  rw [List.append_assoc ( [M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A)]
  rw [List.length_append,hv,List.length_append,NativeMomentAssembly.matrix_length]
  simp only [List.length_cons,List.length_nil,length]
  simp only [M,NativeMomentAssembly.rowCount]
  ring

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (hB:length n r+n+k+r+dimension n r+10 < B) (hm:2^n < B):
    Spec B (fun σ => Data G k r σ∧ length n r≤ (σ.arrs "lp.input").length) command
      (fun _ τ => Data G k r τ∧ τ.vars "lp.length"=length n r∧ Prefix (encodeProgram (MomentLP.program G k r)) "lp.input" τ)
      (cost n r):=by
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩:=header_spec B G k r (by dsimp only [length,M] at hB ⊢; omega) σ ⟨hd,by dsimp only [length,M] at hr; omega⟩
  obtain ⟨μ,r2,p2⟩:=NativeMomentMatrix.command_spec NativeMomentMatrix.allKinds B G k r [M n r,dimension n r]
    (by rw [NativeMomentMatrix.all_count]; simp only [List.length_cons,List.length_nil]; dsimp only [length,M] at hB; omega) hm ν
    ⟨p1.1,p1.2.1,by rw [NativeMomentMatrix.all_count,RamFrames.run_array_length r1]; simp only [List.length_cons,List.length_nil]; dsimp only [length,M] at hr; omega,p1.2.2⟩
  let front:= [M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A
  have hfront:front.length=2+3*(M n r*dimension n r):=by
    simp only [front,List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
    rfl
  have hp:Prefix front "lp.input" μ:=by simpa only [NativeMomentMatrix.all_words] using p2.2.2
  have hl:μ.vars "lp.length"=front.length:=by
    simpa only [hfront,NativeMomentMatrix.all_count,List.length_cons,List.length_nil] using p2.2.1
  obtain ⟨τ,r3,p3⟩:=NativeMomentVectors.command_spec B G k r front
    (by rw [hfront,vector_size]; exact hB) μ
    ⟨p2.1,hl,by rw [hfront,vector_size,RamFrames.run_array_length (r1.seq r2)]; exact hr,hp⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [NativeMomentMatrix.all_count,vector_size]; simp only [NativeMomentMatrix.allKinds,List.length_cons,List.length_nil,cost,M]; omega),p3.1,?_,?_⟩
  · simpa only [hfront,vector_size,length] using p3.2.1
  · change Prefix ([M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A++
      encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c) "lp.input" τ
    simpa only [front,List.append_assoc] using p3.2.2

end Lax263307Proofs.NativeMomentInput

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP

def Input {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "row.k"=k∧ σ.vars "moment.r"=r∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ∧
  (n+1)*(r+3)≤ (σ.arrs "choose.table").length∧ n≤ (σ.arrs "subset.bits").length∧
  N n r≤ (σ.arrs "catalog.mask").length∧ N n r≤ (σ.arrs "catalog.card").length∧
  N n r≤ (σ.arrs "catalog.independent").length

theorem catalog_length (n r:ℕ):(NativeCatalog.rows n (r+3)).length=N n r:=by
  rw [NativeCatalog.rows_words]
  simp only [Lax263307.NativeCatalog.words,List.length_map]

theorem command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (hB:guardBound n k r < B) (hm:2^n < B):
    Spec B (Input G k r) command (fun _ τ => NativeMomentFamily.Data G k r τ) (cost n r):=by
  have hb:n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N n r+20 < B:=hB
  rintro σ ⟨hn,hk,hr,hg,htable,hbits,hmask,hcard,hind⟩
  let ν:=σ.setVar "catalog.limit" (r+3)
  have r1:Run B (.assign "catalog.limit" (.add (.var "moment.r") (.lit 3))) σ ν 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hr.symm,hr ▸ (by omega)⟩)
      (evalB_lit (show 3 < B by omega)) (by change r+3 < B; omega))
  have hcoeff:∀ a≤ n,∀ b≤ r+2,a.choose b < B:=by
    intro a ha b hb'
    have hh:=NativeCatalog.coefficient_bound n (r+2) a b ha hb'
    rw [show r+2+1=r+3 from rfl,catalog_length] at hh
    omega
  obtain ⟨μ,r2,p2⟩:=NativeCatalog.command_spec B n (r+2) (by change (n+1)*(r+3)+n+(r+2)+3 < B; omega) hm
    (by rw [show r+2+1=r+3 from rfl,catalog_length]; omega) hcoeff ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,by simp [ν],htable,hbits,by rwa [catalog_length]⟩
  have hd:NativeCatalogMetadata.Data G r μ:=by
    refine ⟨p2.1.1,?_,?_,?_,?_⟩
    · simpa only [show r+2+1=r+3 from rfl,catalog_length] using p2.2.1
    · simpa only [show r+2+1=r+3 from rfl,NativeCatalog.rows_words] using p2.2.2
    · simpa only [Prefix,(r1.seq r2).frame_arr "search.graph" (by decide)] using hg
    · rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)]
  obtain ⟨τ,r3,p3⟩:=NativeCatalogMetadata.command_spec B G r (by omega)
    (by change N n r+1 < B; omega) hm μ
    ⟨hd,by rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)],
      by rwa [Lax455465Proofs.RamFrames.run_array_length (r1.seq r2)]⟩
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono ?_,⟨p3.1,p3.2.1,p3.2.2,?_⟩,?_⟩
  · simp only [show r+2+1=r+3 from rfl,catalog_length,cost,catalogCost,NativeCatalogMetadata.N,N,MomentLP.dimension]
    omega
  · exact (rr.frame_var "moment.r" (by decide)).trans hr
  · exact (rr.frame_var "row.k" (by decide)).trans hk

end Lax263307Proofs.NativeMomentSetup

end

section

namespace Lax263307Proofs.NativeArrayBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

theorem big_step {B K:ℕ} {c:Com} {σ τ:Env} (rr:BigStepB B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  induction rr with
  | skip => exact hb
  | assign _ => exact hb
  | store hi he hj =>
    intro a z hz
    simp only [arrs_setArr] at hz
    split_ifs at hz with h
    · obtain hz|rfl:=List.mem_or_eq_of_mem_set hz
      · exact hb _ _ hz
      · exact Expr.lt_of_evalB he
    · exact hb _ _ hz
  | seq _ _ ih ih' => exact ih' (ih hb)
  | ite_true _ _ ih => exact ih hb
  | ite_false _ _ ih => exact ih hb
  | while_true _ _ _ ih ih' => exact ih' (ih hb)
  | while_false _ => exact hb
  | read _ => exact hb
  | write _ => exact hb

theorem run {B K:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ K)
    (hb:Bounded B σ):Bounded B τ:=by
  obtain ⟨_,_,h⟩:=rr
  exact big_step h hb

theorem prefix_words {B:ℕ} {σ:Env} {xs:List ℕ} {a:String} (hb:Bounded B σ)
    (hp:Prefix xs a σ):∀ z∈ xs,z < B:=by
  intro z hz
  obtain ⟨i,hi,hz⟩:=List.getElem_of_mem hz
  have he:=hp i hi
  rw [hz] at he
  exact hb a z (List.mem_of_getElem? he)

end Lax263307Proofs.NativeArrayBounds

end

section

namespace Lax263307Proofs.NativeScaleFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamArithmetic
open NativeSignedArithmetic

theorem value (sign n d s:ℕ):fractionValue sign (n*s) d=fractionValue sign n d*(s:ℚ):=by
  unfold fractionValue
  split_ifs <;> push_cast <;> ring

theorem bounds (M s:ℕ) (q:ℚ) (hs:s≤ M) (hq:Bounded M q):
    Bounded (M^2) (q*(s:ℚ)):=by
  have hM:1≤ M:=q.den_pos.trans_le hq.2
  let sign:=RamLpRationalRead.sign q
  have hv:fractionValue sign q.num.natAbs q.den=q:=RamLpRationalRead.value_eq q
  have he:fractionValue sign (q.num.natAbs*s) q.den=q*(s:ℚ):=by rw [value,hv]
  obtain ⟨hn,hd⟩:=fractionValue_num_den sign (q.num.natAbs*s) q.den q.den_pos
  rw [he] at hn hd
  constructor
  · rw [hn]
    exact (Nat.div_le_self _ _).trans (by simpa only [pow_two] using Nat.mul_le_mul hq.1 hs)
  · rw [hd]
    exact (Nat.div_le_self _ _).trans (hq.2.trans (by nlinarith only [hM]))

end Lax263307Proofs.NativeScaleFraction

end

section

namespace Lax263307Proofs.NativeDistanceEntries

open Lax263307.DistanceProjection Lax109476.LinearProgram Lax109476.RationalEncoding

def matrixEntry {m n:ℕ} (P:Program ℚ m n) (i j:ℕ):ℚ:=
  if hi:i < m then
    if hj:j < n then P.A ⟨i,hi⟩ ⟨j,hj⟩ else 0
  else if i < m+n then
    if j < n then if i-m=j then 1 else 0 else -1
  else if j < n then if i-(m+n)=j then -1 else 0 else -1

def boundEntry {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (i:ℕ) (hi:i < m+(n+n)):ℚ:=
  if h:i < m then P.b ⟨i,h⟩
  else if h':i < m+n then center ⟨i-m,by omega⟩
  else -center ⟨i-(m+n),by omega⟩

def objectiveEntry (n j:ℕ):ℚ:=if j < n then 0 else -1

theorem matrix_entry {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ)
    (i:Fin (m+(n+n))) (j:Fin (n+1)):
    (distanceProgram P center).A i j=matrixEntry P i.val j.val:=by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) i
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,u.isLt,v.isLt]
    · intro v
      have hv:v.val=0:=by have hh:=v.isLt; omega
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,u.isLt]
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      have hui:=u.isLt
      have hvi:=v.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+u.val < m by omega,
        show m+u.val < m+n by omega,hvi,Fin.ext_iff]
    · intro v
      have hv:v.val=0:=by have hh:=v.isLt; omega
      have hui:=u.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+u.val < m by omega,
        show m+u.val < m+n by omega]
  · intro u
    refine Fin.addCases ?_ ?_ j
    · intro v
      have hui:=u.isLt
      have hvi:=v.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+n+u.val < m by omega,
        show ¬m+n+u.val < m+n by omega,hvi,Fin.ext_iff,←Nat.add_assoc]
    · intro v
      have hv:v.val=0:=by have hh:=v.isLt; omega
      have hui:=u.isLt
      simp [-Fin.natAdd_eq_addNat,distanceProgram,matrixEntry,show ¬m+n+u.val < m by omega,
        show ¬m+n+u.val < m+n by omega,←Nat.add_assoc]

theorem bound_entry {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ)
    (i:Fin (m+(n+n))):(distanceProgram P center).b i=boundEntry P center i.val i.isLt:=by
  refine Fin.addCases ?_ (Fin.addCases ?_ ?_) i
  · intro u
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,u.isLt]
  · intro u
    have hui:=u.isLt
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,show ¬m+u.val < m by omega,show m+u.val < m+n by omega]
  · intro u
    have hui:=u.isLt
    simp [-Fin.natAdd_eq_addNat,distanceProgram,boundEntry,show ¬m+n+u.val < m by omega,
      show ¬m+n+u.val < m+n by omega,←Nat.add_assoc]

theorem objective_entry {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ)
    (j:Fin (n+1)):(distanceProgram P center).c j=objectiveEntry n j.val:=by
  refine Fin.addCases ?_ ?_ j
  · intro u
    simp [-Fin.natAdd_eq_addNat,distanceProgram,objectiveEntry,u.isLt]
  · intro u
    have hu:u.val=0:=by have hh:=u.isLt; omega
    simp [-Fin.natAdd_eq_addNat,distanceProgram,objectiveEntry]

end Lax263307Proofs.NativeDistanceEntries

end

section

namespace Lax263307Proofs.NativeDistanceData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeDistanceEntries

theorem matrix_height {m n:ℕ} (B:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ) (hb:Bounded B P x)
    (i:Fin (rows m n)) (j:Fin (columns n)):Height B ((distanceProgram P x).A i j):=by
  rw [matrix_entry]
  unfold matrixEntry
  split_ifs
  all_goals first | exact hb.matrix _ _ | simpa [Height] using hb.one | simp only [Height,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]; exact ⟨by have hh:=hb.one; omega,hb.one⟩

theorem bound_height {m n:ℕ} (B:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ) (hb:Bounded B P x)
    (i:Fin (rows m n)):Height B ((distanceProgram P x).b i):=by
  rw [bound_entry]
  unfold boundEntry
  split_ifs
  · exact hb.bound _
  · exact hb.center _
  · simpa only [Height,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hb.center _

theorem objective_height {m n:ℕ} (B:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ) (hb:Bounded B P x)
    (j:Fin (columns n)):Height B ((distanceProgram P x).c j):=by
  rw [objective_entry]
  unfold objectiveEntry
  split_ifs
  · simp only [Height,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    exact ⟨by have hh:=hb.one; omega,hb.one⟩
  · simpa [Height] using hb.one

end Lax263307Proofs.NativeDistanceData

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeDistanceInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

theorem input_length {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ):
    (encodeProgram (distanceProgram P x)).length=wordLength m n:=by
  change ([rows m n,columns n]++NativeMomentAssembly.matrixWords (distanceProgram P x).A++
    RamVectorEncoding.encode (List.ofFn (distanceProgram P x).b)++
    RamVectorEncoding.encode (List.ofFn (distanceProgram P x).c)).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,
    RamVectorEncoding.length_encode,List.length_ofFn,wordLength,rows,columns]
  ring

end Lax263307Proofs.NativeDistanceInput

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeDistanceData

theorem certificate_bound (M m n:ℕ) (c:Certificate (m+(n+n)) (n+1))
    (hc:∀ v∈encodeCertificate c,v≤ M):NativeProjectionResult.CertificateBounded M c:=by
  cases c with
  | optimal z y =>
    constructor
    · intro i
      apply NativeEncodedLP.coordinate_bounds M (n+1) z _ i
      intro v hv
      exact hc v (List.mem_append_left _ (List.mem_append_right _ hv))
    · intro i
      apply NativeEncodedLP.coordinate_bounds M (m+(n+n)) y _ i
      intro v hv
      exact hc v (List.mem_append_right _ hv)
  | infeasible _ => trivial
  | unbounded _ _ => trivial

end Lax263307Proofs.NativeProjectionOracle

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

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem eval_mono (P:Polynomial ℕ) {x y:ℕ} (h:x≤ y):P.eval x≤ P.eval y:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources

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

namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem words_length (names:List String) (S:ℕ) (σ:Env)
    (hS:∀ a∈names,(σ.arrs a).length=S):(words names σ).length=S*names.length:=by
  induction names with
  | nil => simp [words]
  | cons a as ih =>
    have hi:=ih (fun b hb => hS b (List.mem_cons_of_mem a hb))
    change (List.flatMap σ.arrs as).length=S*as.length at hi
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons]
    rw [hS a (by simp),hi]
    nlinarith only []

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (names:List String) (s:String) (hs:s≠"stack.words"):s∉(save names).wvars:=by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

end Lax263307Proofs.NativeFrameScalars

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem buffers_variable (names:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):s∉(NativeFrameBuffers.save names).wvars:=by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

end Lax263307Proofs.NativeRecursionFrame

end

section

namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (arrays scalars:List String) (s:String)
    (hs:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉(NativeRecursionFrame.save arrays scalars).wvars:=by
  have hw:s≠"stack.words" :=fun h => hs (by simp [h])
  simpa only [NativeRecursionFrame.save,Com.wvars,List.mem_append,not_or] using
    And.intro (NativeRecursionFrame.buffers_variable arrays s hs) (NativeFrameScalars.save_variable scalars s hw)

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

theorem phase {B K:ℕ} {cases:List Com} {σ τ:Env}
    (running:σ.vars "machine.running"=1) (j:Fin cases.length)
    (phase:σ.vars "machine.phase"=j.val) (rr:Run B cases[j.val] σ τ K):
    Segment B cases 1 K σ τ:=by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

end Lax263307Proofs.NativeMachineSegment

end

section

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

theorem array_length {B steps total:ℕ} {cases:List Com} {σ τ:Env}
    (trace:Segment B cases steps total σ τ) (a:String):(τ.arrs a).length=(σ.arrs a).length:=by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (Lax455465Proofs.RamFrames.run_array_length rr a)

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

namespace Lax263307Proofs.NativeMachineBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning NativeMachineSegment

theorem state {B steps total:ℕ} {phases:List Com} {σ τ:Env}
    (trace:Segment B phases steps total σ τ) (hσ:NativeStateBounds.Bounded B σ):
    NativeStateBounds.Bounded B τ:=by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeStateBounds.run rr hσ)

end Lax263307Proofs.NativeMachineBounds

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

theorem collection {n B D k r p b load F fuel S v limit steps total:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {base τ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front base)
    (trace:Segment B (phases cfg) steps total base τ)
    (anchor:NativeCollectionAnchor.Anchor base τ)
    (order:τ.vars "graph.n"=n)
    (stack:Prefix front "recursion.frames" τ) (cursor:τ.vars "stack.words"=front.length):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∉NativeCollectionAnchor.workScalars):=anchor.1 s hs
  have a (s:String) (hs:s∉NativeCollectionAnchor.workArrays):=anchor.2 s hs
  refine ⟨?_,(v _ (by decide)).trans hc.target,(v _ (by decide)).trans hc.sparsity,
    (v _ (by decide)).trans hc.denominator,(v _ (by decide)).trans hc.classB,
    (v _ (by decide)).trans hc.loadValue,(v _ (by decide)).trans hc.nodeD,
    (v _ (by decide)).trans hc.floorPower,?_,(v _ (by decide)).trans hc.programLength,
    (v _ (by decide)).trans hc.roundLimit,(v _ (by decide)).trans hc.roundWidth,NativeMachineBounds.state trace hc.bounded,
    ?_,stack,cursor,(v _ (by decide)).trans hc.stride,(v _ (by decide)).trans hc.depth,
    (v _ (by decide)).trans hc.frameLength⟩
  · rcases hc.moments with ⟨⟨hn,hN,hm,hg,hbits⟩,hcard,hind,hr⟩
    refine ⟨⟨order,(v _ (by decide)).trans hN,?_,?_,?_⟩,
      ?_,?_,(v _ (by decide)).trans hr⟩
    · simpa only [Prefix,a "catalog.mask" (by decide)] using hm
    · simpa only [Prefix,a "search.graph" (by decide)] using hg
    · rw [NativeMachineFrame.array_length trace]; exact hbits
    · simpa only [Prefix,a "catalog.card" (by decide)] using hcard
    · simpa only [Prefix,a "catalog.independent" (by decide)] using hind
  · simpa only [Prefix,a "moment.program" (by decide)] using hc.program
  · intro s; rw [NativeMachineFrame.array_length trace]; exact hc.lengths s

end Lax263307Proofs.NativeOracleContext

end

section

namespace Lax263307Proofs.NativeDistanceQueryResources

open Lax455465Proofs Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

private theorem rational_words (M:ℕ) (q:ℚ) (hM:1≤ M)
    (hq:NativeSignedArithmetic.Bounded M q):∀ z∈encodeRational q,z≤ M:=by
  intro z hz
  simp only [encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl
  · split_ifs <;> omega
  · exact hq.1
  · exact hq.2

private theorem vector_words {n:ℕ} (M:ℕ) (x:Fin n→ ℚ) (hM:1≤ M)
    (hx:∀ i,NativeSignedArithmetic.Bounded M (x i)):∀ z∈encodeVector x,z≤ M:=by
  intro z hz
  simp only [encodeVector,List.mem_flatMap,List.mem_ofFn] at hz
  obtain ⟨q,⟨i,rfl⟩,hz⟩:=hz
  exact rational_words M (x i) hM (hx i) z hz

theorem program_words {m n:ℕ} (M:ℕ) (P:Program ℚ m n) (hM:1≤ M)
    (hm:m≤ M) (hn:n≤ M)
    (hA:∀ i j,NativeSignedArithmetic.Bounded M (P.A i j))
    (hb:∀ i,NativeSignedArithmetic.Bounded M (P.b i))
    (hc:∀ i,NativeSignedArithmetic.Bounded M (P.c i)):
    ∀ z∈encodeProgram P,z≤ M:=by
  intro z hz
  simp only [encodeProgram,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with ((hdim|hz)|hz)|hz
  · rcases hdim with rfl|rfl
    · exact hm
    · exact hn
  · obtain ⟨q,hq,hz⟩:=List.mem_flatMap.mp hz
    obtain ⟨row,hrow,hq⟩:=List.mem_flatten.mp hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hrow
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq
    exact rational_words M _ hM (hA i j) z hz
  · exact vector_words M _ hM hb z hz
  · exact vector_words M _ hM hc z hz

theorem source_fields {m n:ℕ} (B:ℕ) (P:Program ℚ m n)
    (hw:∀ z∈encodeProgram P,z< B):
    (∀ i j,Height B (P.A i j))∧ (∀ i,Height B (P.b i))∧ (∀ j,Height B (P.c j)):=by
  have rational (q:ℚ) (hq:∀ z∈encodeRational q,z< B):Height B q:=
    ⟨hq _ (by simp [encodeRational]),hq _ (by simp [encodeRational])⟩
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    refine Or.inl (Or.inl (Or.inr ?_))
    apply List.mem_flatMap.mpr
    refine ⟨P.A i j,?_,hz⟩
    apply List.mem_flatten.mpr
    exact ⟨List.ofFn (P.A i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩
  · intro i
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨P.b i,List.mem_ofFn.mpr ⟨i,rfl⟩,hz⟩))
  · intro j
    apply rational
    intro z hz
    apply hw z
    simp only [encodeProgram,List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨P.c j,List.mem_ofFn.mpr ⟨j,rfl⟩,hz⟩)

theorem query_size {m n:ℕ} (h:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hb:NativeDistanceData.Bounded (2^h) P x):
    bitSize (encodeProgram (distanceProgram P x))≤ sizeBound m n h:=by
  let E:=h+m+2*n+2
  have hp:2^h≤2^E:=Nat.pow_le_pow_right (by decide) (by dsimp [E]; omega)
  have hrows:rows m n≤2^E:=by
    exact (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (by dsimp [E,rows]; omega))
  have hcols:columns n≤2^E:=by
    exact (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_right (by decide) (by dsimp [E,columns]; omega))
  have hwords:=program_words (2^E) (distanceProgram P x) Nat.one_le_two_pow hrows hcols
    (fun i j => ⟨(matrix_height _ P x hb i j).1.le.trans hp,(matrix_height _ P x hb i j).2.le.trans hp⟩)
    (fun i => ⟨(bound_height _ P x hb i).1.le.trans hp,(bound_height _ P x hb i).2.le.trans hp⟩)
    (fun j => ⟨(objective_height _ P x hb j).1.le.trans hp,(objective_height _ P x hb j).2.le.trans hp⟩)
  have hs:=WordSize.bounded_size (encodeProgram (distanceProgram P x)) (E+1) (by
    intro z hz
    apply Nat.size_le.mpr
    have hh:=hwords z hz
    rw [pow_succ]
    have ht:=Nat.two_pow_pos E
    omega)
  simpa only [NativeDistanceInput.input_length,E,sizeBound,Nat.add_assoc] using hs

end Lax263307Proofs.NativeDistanceQueryResources

end

section

namespace Lax263307.NativeMomentLP

def encodeInput {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):List ℕ:=
  n::k::r::(n*n)::(List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

end Lax263307.NativeMomentLP

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP
open Lax109476.RationalEncoding

abbrev N (n r:ℕ):=dimension n r
abbrev L (n r:ℕ):=NativeMomentInput.length n r

abbrev encodeInput:= @Lax263307.NativeMomentLP.encodeInput

def readInput:Com:=.seq (.read "graph.n") (.seq (.read "row.k") (.seq (.read "moment.r")
  (.seq RamInputCopy.copy (RamArrayCopy.command "input.data" "search.graph" "input.length"))))

theorem read_input_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (hB:n*n+n+k+r+3 < B):
    Spec B (fun σ => σ.inp=encodeInput G k r∧ n*n≤ (σ.arrs "input.data").length∧ n*n≤ (σ.arrs "search.graph").length)
      readInput (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "row.k"=k∧ τ.vars "moment.r"=r∧
        Prefix (NativeWeightReduction.adjacency G) "search.graph" τ) (24*n*n+16):=by
  let xs:=NativeWeightReduction.adjacency G
  have hl:xs.length=n*n:=NativeWeightReduction.adjacency_length G
  have hw:∀ z∈ xs,z < B:=fun z hz => (NativeExhaustive.adjacency_words G z hz).trans_lt (by omega)
  rintro σ ⟨hinp,hroom,hgraph⟩
  let ν:= {σ.setVar "graph.n" n with inp:=k::r::(n*n)::xs}
  have r1:Run B (.read "graph.n") σ ν 1:=Run.read hinp
  let μ:= {ν.setVar "row.k" k with inp:=r::(n*n)::xs}
  have r2:Run B (.read "row.k") ν μ 1:=Run.read rfl
  let ξ:= {μ.setVar "moment.r" r with inp:=(n*n)::xs}
  have r3:Run B (.read "moment.r") μ ξ 1:=Run.read rfl
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨ρ,r4,p4⟩:=RamInputCopy.copy_spec B xs (by omega) (by omega) hw ξ
    ⟨by simp [ξ,hl],by rw [RamFrames.run_array_length r123,hl]; exact hroom⟩
  obtain ⟨τ,r5,p5⟩:=RamArrayCopy.command_spec B xs "input.data" "search.graph" "input.length"
    (by omega) (by omega) hw (by decide) (by decide) ρ
    ⟨p4.2.2,p4.1,by rw [RamFrames.run_array_length (r123.seq r4),hl]; exact hgraph⟩
  have rr:=r4.seq r5
  refine ⟨τ,(r1.seq (r2.seq (r3.seq rr))).mono (by rw [hl]; nlinarith),?_,?_,?_,p5.2⟩
  · rw [rr.frame_var "graph.n" (by decide)]; simp [ξ,μ,ν]
  · rw [rr.frame_var "row.k" (by decide)]; simp [ξ,μ]
  · rw [rr.frame_var "moment.r" (by decide)]; simp [ξ]

def emit:Com:=.seq (.assign "emit.count" (.var "lp.length")) (RamEmitWords.command "lp.input" 1)

theorem emit_spec (B:ℕ) (xs:List ℕ) (hB:xs.length+2 < B) (hw:∀ z∈ xs,z < B):
    Spec B (fun σ => σ.vars "lp.length"=xs.length∧ Prefix xs "lp.input" σ) emit
      (fun σ τ => τ.out=σ.out++xs) (13*xs.length+8):=by
  rintro σ ⟨hl,hp⟩
  let ν:=σ.setVar "emit.count" xs.length
  have r1:Run B (.assign "emit.count" (.var "lp.length")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hl.symm,hl ▸ (by omega)⟩)
  obtain ⟨τ,r2,p2⟩:=RamEmitWords.command_spec B "lp.input" 1 xs σ.out (by omega) (by omega)
    (by simpa only [one_mul] using (show xs.length < B by omega)) (by omega) hw ν
    ⟨by simpa only [RamEmitWords.Data,Prefix,one_mul,ν,arrs_setVar] using hp,by simp [ν],rfl⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

def fullCommand:Com:=.seq readInput (.seq NativeMomentSetup.command (.seq NativeMomentInput.command emit))

def totalCost (n r:ℕ):ℕ:=24*n*n+16+NativeMomentSetup.cost n r+NativeMomentInput.cost n r+13*L n r+8

theorem full_command_spec {n:ℕ} (B:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ)
    (hB:NativeMomentSetup.guardBound n k r < B) (hm:2^n < B):
    Spec B (fun σ => σ.inp=encodeInput G k r∧ NativeArrayBounds.Bounded B σ∧
      ∀ a,NativeMomentSetup.guardBound n k r≤ (σ.arrs a).length)
      fullCommand (fun σ τ => τ.out=σ.out++encodeProgram (MomentLP.program G k r)) (totalCost n r):=by
  rintro σ ⟨hinp,hbounded,hroom⟩
  have hg:n*n+(n+1)*(r+3)+L n r+n+k+r+N n r+20 < B:=hB
  obtain ⟨ν,r1,p1⟩:=read_input_spec B G k r (by omega) σ
    ⟨hinp,by have hh:=hroom "input.data"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh:=hroom "search.graph"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  have hrν:∀ a,NativeMomentSetup.guardBound n k r≤ (ν.arrs a).length:=fun a => by rw [RamFrames.run_array_length r1]; exact hroom a
  obtain ⟨μ,r2,p2⟩:=NativeMomentSetup.command_spec B G k r hB hm ν
    ⟨p1.1,p1.2.1,p1.2.2.1,p1.2.2.2,
      by have hh:=hrν "choose.table"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh:=hrν "subset.bits"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh:=hrν "catalog.mask"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh:=hrν "catalog.card"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh:=hrν "catalog.independent"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  obtain ⟨ξ,r3,p3⟩:=NativeMomentInput.command_spec B G k r (by change L n r+n+k+r+N n r+10 < B; omega) hm μ
    ⟨p2,by rw [RamFrames.run_array_length (r1.seq r2)]; have hh:=hroom "lp.input"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  have rr:=r1.seq (r2.seq r3)
  have hw:=NativeArrayBounds.prefix_words (NativeArrayBounds.run rr hbounded) p3.2.2
  obtain ⟨τ,r4,p4⟩:=emit_spec B (encodeProgram (MomentLP.program G k r))
    (by rw [NativeMomentInput.input_length]; change L n r+2 < B; omega) hw ξ
    ⟨by rw [NativeMomentInput.input_length]; exact p3.2.1,p3.2.2⟩
  have hout:ξ.out=σ.out:=rr.out_eq (by decide)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [NativeMomentInput.input_length]; dsimp only [totalCost,L]; omega),by rwa [hout] at p4⟩

open Lax109476Proofs

def size (n k r:ℕ):ℕ:=n+k+r+N n r+2

theorem polynomial_bounds (n k r:ℕ):
    NativeMomentSetup.guardBound n k r≤ 73*(size n k r)^3∧ totalCost n r≤ 2646*(size n k r)^4:=by
  let X:=size n k r
  have hN:1≤ N n r:=NativeMomentFamily.dimension_positive n r
  have hX:1≤ X:=by dsimp [X,size]; omega
  have hn:n≤ X:=by dsimp [X,size]; omega
  have hk:k≤ X:=by dsimp [X,size]; omega
  have hr:r≤ X:=by dsimp [X,size]; omega
  have hNc:N n r≤ X:=by dsimp [X,size]; omega
  have hn1:n+1≤ X:=by dsimp [X,size]; omega
  have hr3:r+3≤ X:=by dsimp [X,size]; omega
  have h12:X≤ X^2:=le_self_pow hX (by omega)
  have h23:X^2≤ X^3:=Nat.pow_le_pow_right hX (by omega)
  have h34:X^3≤ X^4:=Nat.pow_le_pow_right hX (by omega)
  have h02:1≤ X^2:=Nat.one_le_pow _ _ (by omega)
  have h03:1≤ X^3:=Nat.one_le_pow _ _ (by omega)
  have h04:1≤ X^4:=Nat.one_le_pow _ _ (by omega)
  have hn2:n*n≤ X^2:=by simpa only [pow_two] using Nat.mul_le_mul hn hn
  have hdim:(n+1)*(r+3)≤ X^2:=by simpa only [pow_two] using Nat.mul_le_mul hn1 hr3
  have hM:NativeMomentInput.M n r≤ 7*X^2:=by
    rw [NativeMomentInput.row_count_eq]
    have hh:=Nat.mul_le_mul hNc (show n+4≤ 5*X by omega)
    nlinarith only [hh,h02]
  have hMN:NativeMomentInput.M n r*N n r≤ 7*X^3:=by
    have hh:=Nat.mul_le_mul hM hNc
    nlinarith only [hh]
  have hL:L n r≤ 47*X^3:=by
    change 2+3*(NativeMomentInput.M n r*N n r)+3*(NativeMomentInput.M n r+N n r)≤ _
    nlinarith only [hMN,hM,hNc,h12,h23,h03]
  have hguard:NativeMomentSetup.guardBound n k r≤ 73*X^3:=by
    change n*n+(n+1)*(r+3)+L n r+n+k+r+N n r+20≤ _
    nlinarith only [hn2,hdim,hL,hn,hk,hr,hNc,h12,h23,h03]
  have hcat:NativeMomentSetup.catalogCost n r≤ 205*X^3:=by
    have hh:=Nat.mul_le_mul (show 69*n+33≤ 102*X by omega) hNc
    have ht:54*(n+1)*(r+3)+(69*n+33)*N n r+41≤ 197*X^2:=by
      nlinarith only [hh,hdim,h02]
    have hp:=Nat.mul_le_mul ht hr3
    change (54*(n+1)*(r+3)+(69*n+33)*N n r+41)*(r+3)+8≤ _
    nlinarith only [hp,h03]
  have hsetup:NativeMomentSetup.cost n r≤ 363*X^3:=by
    have hc:38*n*n+42*n+60≤ 140*X^2:=by nlinarith only [hn2,hn,h12,h02]
    have hh:=Nat.mul_le_mul hc hNc
    change NativeMomentSetup.catalogCost n r+(38*n*n+42*n+60)*N n r+18≤ _
    nlinarith only [hh,hcat,h03]
  have hinput:NativeMomentInput.cost n r≤ 1624*X^4:=by
    have hc:22*n+129≤ 151*X:=by omega
    have hh:=Nat.mul_le_mul hc hMN
    change (22*n+129)*(NativeMomentInput.M n r*N n r)+57*(NativeMomentInput.M n r+N n r)+111≤ _
    nlinarith only [hh,hM,hNc,h12,h23,h34,h04]
  refine ⟨hguard,?_⟩
  change 24*n*n+16+NativeMomentSetup.cost n r+NativeMomentInput.cost n r+13*L n r+8≤ _
  nlinarith only [hn2,hsetup,hinput,hL,h23,h34,h04]

end Lax263307Proofs.NativeMomentProgram

end

section

namespace Lax263307Proofs.NativeOutputBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem big_step {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:BigStepB B c σ τ K)
    (hd:∀ v∈σ.out,v< B):∀ v∈τ.out,v< B:=by
  induction rr with
  | skip => exact hd
  | assign he => exact hd
  | store hi he hk => exact hd
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh => exact hd
  | write he =>
    intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hd v hv
    · exact Expr.lt_of_evalB he

theorem run {B:ℕ} {c:Com} {σ τ:Env} {K:ℕ} (rr:Run B c σ τ K)
    (hd:∀ v∈σ.out,v< B):∀ v∈τ.out,v< B:=by
  obtain ⟨_,_,rr⟩:=rr
  exact big_step rr hd

end Lax263307Proofs.NativeOutputBounds

end

section

namespace Lax263307Proofs.NativeMomentEncodingHeight

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP NativeCatalogMetadata
open Lax109476.RationalEncoding
open Lax455465Proofs

def height (n k r:ℕ):ℕ:=100*(NativeMomentProgram.size n k r)^3+10

theorem program_words {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    ∀ z∈encodeProgram (program G k r),z<2^height n k r:=by
  let X:=NativeMomentProgram.size n k r
  let v:=height n k r
  let B:=2^v
  let ext:=fun (_:String) => NativeMomentSetup.guardBound n k r
  let input:=NativeMomentProgram.encodeInput G k r
  let σ:=initEnv ext input
  have hX:1≤ X:=by dsimp [X,NativeMomentProgram.size]; omega
  have h13:X≤ X^3:=le_self_pow hX (by omega)
  have hnX:n≤ X:=by dsimp [X,NativeMomentProgram.size]; omega
  have hguard:NativeMomentSetup.guardBound n k r< v:=by
    have hg:=(NativeMomentProgram.polynomial_bounds n k r).1
    change _≤73*X^3 at hg
    change NativeMomentSetup.guardBound n k r<100*X^3+10
    omega
  have hB:NativeMomentSetup.guardBound n k r< B:=hguard.trans Nat.lt_two_pow_self
  have hm:2^n< B:=Nat.pow_lt_pow_right (by decide) (by dsimp [v,height]; nlinarith only [h13,hnX])
  have hσ:NativeArrayBounds.Bounded B σ:=by
    intro a z hz
    have he:z=0:=List.eq_of_mem_replicate hz
    subst z
    exact Nat.two_pow_pos v
  obtain ⟨τ,rr,ho⟩:=NativeMomentProgram.full_command_spec B G k r hB hm σ
    ⟨rfl,hσ,by intro a; simp [σ,initEnv,ext]⟩
  have hb:=NativeOutputBounds.run rr (by simp [σ,initEnv])
  simpa only [ho,σ,initEnv,List.nil_append] using hb

end Lax263307Proofs.NativeMomentEncodingHeight

end

section

namespace Lax263307Proofs.NativeProjectionQueryBounds

open Lax263307 MomentLP
open NativeSignedArithmetic Lax109476.RationalEncoding

abbrev rows (n r:ℕ):ℕ:=2+(dimension n r+(dimension n r+(dimension n r*n+(dimension n r+dimension n r))))

def height (n k r R:ℕ):ℕ:=NativeMomentEncodingHeight.height n k r+2*scaleHeight (dimension n r) R+1

theorem bounded {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r R:ℕ)
    (center:Index n r→ ℚ) (hc:∀ i,NativeRoundedStep.height (center i) (80*(R+1))):
    NativeDistanceData.Bounded (2^height n k r R) (program G k r) (ProjectedOracle.raw center):=by
  let N:=dimension n r
  let s:=scaleHeight N R
  let H:=height n k r R
  have hH:0< H:=by dsimp [H,height]; omega
  have hsrc:2^NativeMomentEncodingHeight.height n k r≤2^H:=
    Nat.pow_le_pow_right (by decide) (by dsimp [H,height]; omega)
  have hf:=NativeDistanceQueryResources.source_fields _ (program G k r)
    (NativeMomentEncodingHeight.program_words G k r)
  have hpow:2^(s*2)<2^H:=Nat.pow_lt_pow_right (by decide) (by dsimp [H,height,s,N]; omega)
  refine ⟨Nat.one_lt_pow (by omega) (by decide),?_,?_,?_⟩
  · intro i j
    exact ⟨(hf.1 i j).1.trans_le hsrc,(hf.1 i j).2.trans_le hsrc⟩
  · intro i
    exact ⟨(hf.2.1 i).1.trans_le hsrc,(hf.2.1 i).2.trans_le hsrc⟩
  · intro i
    have hscale:4*N≤2^s:=(show 4*N≤ s by dsimp [s,scaleHeight]; omega).trans Nat.lt_two_pow_self.le
    have hs:2^(80*(R+1))≤2^s:=Nat.pow_le_pow_right (by decide) (by dsimp [s,scaleHeight]; omega)
    have hi:Bounded (2^s) (center i):= ⟨(hc i).1.trans hs,(hc i).2.trans hs⟩
    have hr:Bounded ((2^s)^2) (ProjectedOracle.raw center i):=by
      have hh:=NativeScaleFraction.bounds (2^s) (4*N) (center i) hscale hi
      simpa only [ProjectedOracle.raw,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using hh
    have hpow':(2^s)^2<2^H:=by simpa only [pow_mul] using hpow
    exact ⟨hr.1.trans_lt hpow',hr.2.trans_lt hpow'⟩

theorem uniform_query_size {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r R:ℕ)
    (hn:n≤ R) (hk:k≤ R) (hr:r≤ R) (hN:dimension n r≤ R)
    (center:Index n r→ ℚ) (hc:∀ i,NativeRoundedStep.height (center i) (80*(R+1))):
    Lax759944.BinaryWordEncoding.bitSize
      (encodeProgram (DistanceProjection.distanceProgram (program G k r) (ProjectedOracle.raw center)))≤ queryBound R:=by
  have hsize:=NativeDistanceQueryResources.query_size (height n k r R) (program G k r)
    (ProjectedOracle.raw center) (bounded G k r R center hc)
  have hm:rows n r≤ rootRows R:=by
    have hprod:=Nat.mul_le_mul hN hn
    dsimp [rows,rootRows]
    nlinarith only [hprod,hN]
  have hsrc:NativeMomentEncodingHeight.height n k r≤100*(4*R+2)^3+10:=by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    change n+k+r+dimension n r+2≤4*R+2
    omega
  have hH:height n k r R≤ rootHeight R:=by
    dsimp [height,rootHeight,scaleHeight]
    omega
  apply hsize.trans
  dsimp [queryBound,NativeDistanceQueryResources.sizeBound]
  apply Nat.mul_le_mul
  · dsimp [NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns]
    gcongr
  · change height n k r R+rows n r+2*dimension n r+4≤ rootHeight R+rootRows R+2*R+4
    omega

end Lax263307Proofs.NativeProjectionQueryBounds

end

section

namespace Lax263307Proofs.NativeCutResources

open Lax263307.RationalCutBuffer NativeSignedArithmetic

theorem product_bound (n h:ℕ) (a:Fin n→ ℚ) (ha:∀ i,Bounded (2^h) (a i)):
    denominator a≤2^(n*h):=by
  have hh (s:Finset (Fin n)):(∏ i∈s,(a i).den)≤2^(s.card*h):=by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,pow_add]
      simpa only [Nat.one_mul,Nat.mul_one,Nat.mul_comm] using Nat.mul_le_mul (ha i).2 ih
  simpa only [Finset.card_univ,Fintype.card_fin,denominator] using hh Finset.univ

theorem guard_bound (n h:ℕ) (a:Fin n→ ℚ) (ha:∀ i,Bounded (2^h) (a i)):
    2^h*denominator a+2^h+denominator a+3*n+10<2^(wordExponent n h):=by
  let E:=(n+1)*(h+1)
  have hD:=product_bound n h a ha
  have hE:n*h≤ E:=by dsimp [E]; nlinarith
  have hH:h≤ E:=by dsimp [E]; nlinarith
  have hboth:h+n*h≤ E:=by dsimp [E]; nlinarith
  have hnE:n≤ E:=by dsimp [E]; nlinarith
  have hpD:denominator a≤2^E:=hD.trans (Nat.pow_le_pow_right (by decide) hE)
  have hpH:2^h≤2^E:=Nat.pow_le_pow_right (by decide) hH
  have hpM:2^h*denominator a≤2^E:=by
    calc
      _≤ 2^h*2^(n*h):=Nat.mul_le_mul_left _ hD
      _=2^(h+n*h):=(pow_add _ _ _).symm
      _≤ 2^E:=Nat.pow_le_pow_right (by decide) hboth
  have hnU:n<2^E:=hnE.trans_lt Nat.lt_two_pow_self
  have hU:=Nat.two_pow_pos E
  change _<2^(E+10)
  rw [pow_add]
  norm_num
  omega

end Lax263307Proofs.NativeCutResources

end

section

namespace Lax263307Proofs.NativeNormalHeight

open Lax263307 RoundedOracleSearch RationalProjection DistanceProjection
open Lax109476.LinearProgram Lax109476.RationalCertificates
open NativeSignedArithmetic

theorem far_height {m n:ℕ} (M:ℕ) (P:Program ℚ m n) (ρ:ℚ)
    (c:Certificate (m+(n+n)) (n+1)) (hc:NativeProjectionResult.CertificateBounded M c)
    (a:Fin n→ ℚ) (β:ℚ) (he:classify P ρ c=.far a β):
    ∀ i,Bounded (2*M^2) (a i):=by
  cases c with
  | infeasible y => simp [classify] at he
  | unbounded z y => simp [classify] at he
  | optimal z y =>
    dsimp only [classify] at he
    split at he
    · contradiction
    · cases he
      intro i
      exact NativeRationalBounds.subtract M _ _ (hc.2 _) (hc.2 _)

end Lax263307Proofs.NativeNormalHeight

end

section

namespace Lax263307Proofs.NativeOraclePrecision

open Lax263307 Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime

theorem height_mono (q:ℚ) (h H:ℕ) (hq:NativeRoundedStep.height q h) (hh:h≤ H):
    NativeRoundedStep.height q H:=by
  have hp:2^h≤2^H:=Nat.pow_le_pow_right (by decide) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩

end Lax263307Proofs.NativeOraclePrecision

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedLP

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 DistanceProjection NativeDistanceData

theorem certificate_bound {f:List ℕ→ List ℕ} (p:Program f) (he:NativeEncodedLP.Encoded f)
    {m n:ℕ} (P:Lax109476.LinearProgram.Program ℚ m n) (x:Fin n→ ℚ) (R:ℕ)
    (hq:bitSize (encodeProgram (distanceProgram P x))≤ queryBound R):
    NativeProjectionResult.CertificateBounded (2^certificateHeight p R)
      (RegisteredLP.certificate f (distanceProgram P x)):=by
  apply NativeProjectionOracle.certificate_bound
  intro z hz
  have hz':z∈f (encodeProgram (distanceProgram P x)):=by rwa [(he _ _ _).1]
  exact (p.fits _ _ P x z hz').le.trans
    (Nat.pow_le_pow_right (by decide) (NativeFlowQueryResources.eval_mono p.width hq))

end Lax263307Proofs.NativeSelectedLP

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem child_variable (cfg:Config) (s:String)
    (hg:s∉NativeChildGraph.command.wvars) (hc:s∉NativeChildActivate.command.wvars)
    (he:s∉(NativeChildCall.enter 1).wvars) (hphase:s≠"machine.phase")
    (hstack:s∉["stack.i","stack.copy.length","stack.words"]):
    s∉((phases cfg)[11]'(by change 11<16; decide)).wvars:=by
  have hsave:=NativeChildCall.save_variable (frameArrays cfg) (frameScalars cfg) s hstack
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeChildCall.command,go,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem pushed_length {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {σ saved:Env} {c:Com} (rr:Run B c σ saved t)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S):
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved).length=
      front.length+S*(frameArrays cfg).length+(frameScalars cfg).length:=by
  have h:(NativeFrameBuffers.words (frameArrays cfg) saved).length=S*(frameArrays cfg).length:=
    NativeFrameBuffers.words_length _ S saved (fun a ha => by rw [RamFrames.run_array_length rr,hc.lengths]; exact hext a ha)
  simp only [List.length_append,NativeRecursionFrame.words,NativeFrameScalars.words,List.length_map,h,Nat.add_assoc]

theorem child_entry {B D S v t cost:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ saved entry:Env} {c:Com} (snapshot:Run B c σ saved t)
    (call:Segment B (phases cfg) 1 cost σ entry)
    (hc:Protocol B D S v cfg extent front σ) (hext:∀ a∈frameArrays cfg,extent a=S)
    (hp:σ.vars "machine.phase"=11)
    (hfront:Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry)
    (hwords:entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length):
    Protocol B D S v cfg extent
      (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry:=by
  have rr:=NativeMachineFrame.single_run call ⟨11,by change 11<16; decide⟩ hp
  refine ⟨NativeMachineBounds.state call hc.bounded,?_,hfront,?_,?_,?_,?_,?_⟩
  · intro a; rw [NativeMachineFrame.array_length call]; exact hc.lengths a
  · rw [pushed_length snapshot hc hext]; exact hwords
  all_goals apply (rr.frame_var _ (child_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide))).trans
  all_goals first | exact hc.stride | exact hc.frameLength | exact hc.roundWidth | exact hc.accuracy

theorem children {n:ℕ} (B D fuel S v childSteps childTime:ℕ) (cfg:Config)
    (lp flow:List ℕ→ List ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent:String→ ℕ) (front:List ℕ) (eligible:Eligible)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (ih:Executes B D fuel S v childSteps childTime cfg lp flow extent eligible):
    Children B D fuel S v childSteps childTime cfg G extent front eligible
      (fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (ComputedSeparators.restriction G C) t):=by
  intro C target σ hel hp phase saved entry snapshot call hfront hwords hgraph horder hk hf hr he
  have protocolEntry:=child_entry cfg snapshot call hp hext phase hfront hwords
  have hlength:=pushed_length snapshot hp hext
  obtain ⟨τ,s,t,trace,hs,ht,answer,protocolDone,rootDone,graphDone⟩:=ih C.card (ComputedSeparators.restriction G C) target
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry
    (by simpa only [hlength] using hel) ⟨protocolEntry,horder,hgraph,hk,hf⟩ hr he
  exact ⟨τ,s,t,trace,hs,ht,answer,protocolDone.stack,
    by simpa only [hlength] using protocolDone.cursor,protocolDone.frameLength,protocolDone.stride⟩

end Lax263307Proofs.NativeNodeProtocol

end

section

namespace Lax263307Proofs.NativeSelectedParts

open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators LinearRelaxation

theorem near_bound {m N:ℕ} (M:ℕ) (P:Lax109476.LinearProgram.Program ℚ m N) (ρ:ℚ)
    (certificate:Lax109476.RationalCertificates.Certificate (m+(N+N)) (N+1))
    (hc:NativeProjectionResult.CertificateBounded M certificate) (x:Fin N→ ℚ)
    (hnear:RationalProjection.classify P ρ certificate=.near x):
    ∀ i,NativeSignedArithmetic.Bounded M (x i):=by
  cases certificate with
  | infeasible y => simp [RationalProjection.classify] at hnear
  | unbounded z y => simp [RationalProjection.classify] at hnear
  | optimal z y =>
    dsimp only [RationalProjection.classify] at hnear
    split at hnear
    · cases hnear
      intro i
      exact hc.1 _
    · contradiction

theorem near_feasible {n r:ℕ} (lp:List ℕ→ List ℕ) (hlp:NativeEncodedLP.Encoded lp)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k:ℕ) (center:MomentLP.Index n r→ ℚ) (ρ:ℚ)
    (x:MomentLP.Index n r→ ℚ)
    (hnear:RationalProjection.classify (MomentLP.program G k r) ρ
      (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) center))=.near x):
    LinearRelaxation.IsFeasible G k r (realVector (MomentLP.decode x)):=by
  have correct:=Lax263307Proofs.RationalProjection.classify_correct (MomentLP.program G k r) center ρ
    (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) center))
    (hlp _ _ _).2
  rw [hnear] at correct
  have feasible:=(Lax263307Proofs.MomentLP.primal_characterization G k r
    (fun i => (x i:ℝ))).mp correct.1
  exact feasible

end Lax263307Proofs.NativeSelectedParts

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedOracle

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch
open NativeCoreMachine

theorem far_guard {N:ℕ} (H w:ℕ) (a:Fin N→ ℚ)
    (ha:∀ i,NativeSignedArithmetic.Bounded (2^H) (a i))
    (hw:NativeCutResources.wordExponent N H+4≤ w):
    2^H*RationalCutBuffer.denominator a+2^H+RationalCutBuffer.denominator a+3*N+23<2^w:=by
  have h:=NativeCutResources.guard_bound N H a ha
  have hp:=Nat.pow_le_pow_right (by decide:1≤2) hw
  rw [pow_add] at hp
  norm_num at hp
  have hpos:=Nat.two_pow_pos (NativeCutResources.wordExponent N H)
  omega

theorem setup {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} (lpProgram:NativeSelectedLP.Program lp)
    (flowProgram:NativeSelectedNear.Program flow) (cfg:Config)
    (hlpCode:lpProgram.code=cfg.lp) (hlpCoeff:lpProgram.coeff=cfg.lpWidth)
    (hflowCode:flowProgram.code=cfg.flow) (hflowCoeff:flowProgram.coeff=cfg.flowWidth)
    (encoded:NativeEncodedLP.Encoded lp)
    (hsep:NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b) (hK:0< cfg.K) (hb:0< cfg.b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v R F w rootN capacity childSteps childTime:ℕ)
    (extent:String→ ℕ) (front:List ℕ)
    (hi:NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn:1< n) (hD:4≤ D) (hF:0< F) (hlarge:cutoff cfg.a cfg.K cfg.b n D< k)
    (hnR:n≤ R) (hkR:k≤ R) (hrR:level cfg.a cfg.K cfg.b n D≤ R)
    (hDR:D≤ R) (hFR:F≤ R) (hNR:MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)≤ R)
    (state:State (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)))
    (hcenter:∀ i,NativeRoundedStep.height (state.2 i) (80*(R+1)))
    (projectionBounds:NativeOracleExecution.ProjectionBounds D k (level cfg.a cfg.K cfg.b n D) F
      (2^(100*(R+1))) w (NativeSelectedLP.oracleTime lpProgram R) G extent)
    (nearBounds:NativeNearExecution.Bounds n (level cfg.a cfg.K cfg.b n D) D k
      (sparsity cfg.a cfg.K cfg.b n D) (2^NativeSelectedLP.certificateHeight lpProgram R)
      (2*NativeSelectedLP.certificateHeight lpProgram R) (R+1) fuel S w cfg extent front)
    (hlpWidth:NativeSelectedLP.wordHeight lpProgram R≤ w)
    (hfarWidth:NativeCutResources.wordExponent (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D))
      (2*NativeSelectedLP.certificateHeight lpProgram R+1)+4≤ w)
    (hqueryRoom:NativeSelectedLP.queryBound R< extent "vm.input")
    (hflowWidth:NativeUniformFlow.wordHeight n
      (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
      flowProgram.code flowProgram.width flowProgram.time flowProgram.output≤ w)
    (hspace:∀ a∈NativeSeparatorContext.workspace,
      NativeUniformFlow.spaceBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
        flowProgram.time≤ extent a)
    (child:(A:Finset (Fin n))→ ℕ→ Option (Finset (Fin A.card))):
    NativeRecursiveSetup.Oracle D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D) F fuel S v w
      (2^(100*(R+1))) (2^(2*NativeSelectedLP.certificateHeight lpProgram R+1))
      (2^NativeSelectedLP.certificateHeight lpProgram R) (2*NativeSelectedLP.certificateHeight lpProgram R)
      (R+1)
      (NativeUniformFlow.spaceBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R)) flowProgram.time)
      (NativeSelectedLP.oracleTime lpProgram R) (NativeSelectedLP.callCost lpProgram R)
      (NativeSeparatorOutput.timeBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
        flowProgram.code flowProgram.coeff flowProgram.time)
      childSteps childTime cfg G lp flow extent front child state
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity):=by
  have query:=NativeProjectionQueryBounds.uniform_query_size G k _ R hnR hkR hrR hNR state.2 hcenter
  have certificate:=NativeSelectedLP.certificate_bound lpProgram encoded (MomentLP.program G k _)
    (ProjectedOracle.raw state.2) R query
  refine ⟨projectionBounds,?_,?_,?_,?_,?_⟩
  · intro i
    exact NativeOraclePrecision.height_mono _ _ _ (hcenter i) (by omega)
  · exact (Lax455465Proofs.WordSize.length_le _).trans_lt (query.trans_lt hqueryRoom)
  · simpa only [hlpCode,hlpCoeff] using NativeSelectedLP.invocation lpProgram G k _ D F R w state.2
      (by omega) (by omega) hF hnR hkR hrR hDR hFR hNR hcenter hlpWidth
  · intro a β hfar
    have ha:=NativeNormalHeight.far_height _ (MomentLP.program G k _)
      (NativeNodeTolerance.tolerance n D F) _ certificate a β hfar
    have he:2*(2^NativeSelectedLP.certificateHeight lpProgram R)^2=
        2^(2*NativeSelectedLP.certificateHeight lpProgram R+1):=by
      rw [pow_add,Nat.mul_comm 2 (NativeSelectedLP.certificateHeight lpProgram R),pow_mul]; norm_num; ring
    rw [he] at ha
    exact ⟨ha,far_guard _ w a ha hfarWidth⟩
  · intro x hx
    have feasible:=NativeSelectedParts.near_feasible lp encoded G k (ProjectedOracle.raw state.2)
      (NativeNodeTolerance.tolerance n D F) x hx
    have bounded:=NativeSelectedParts.near_bound _ (MomentLP.program G k _)
      (NativeNodeTolerance.tolerance n D F) _ certificate x hx
    exact NativeSelectedNear.setup hereditary flowProgram cfg hflowCode hflowCoeff hsep hK hb G
      D k fuel S v (NativeSelectedLP.certificateHeight lpProgram R) (R+1) w rootN capacity childSteps childTime
      extent front hi hn hD hlarge x feasible bounded (by omega) nearBounds hflowWidth hspace child

end Lax263307Proofs.NativeSelectedOracle

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} (lpProgram:Lax263307Proofs.NativeSelectedLP.Program lp)
      (flowProgram:Lax263307Proofs.NativeSelectedNear.Program flow) (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp lpProgram) cfg.lp→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp lpProgram) cfg.lpWidth→
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow flowProgram) cfg.flow→
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow flowProgram) cfg.flowWidth→
              Lax263307Proofs.NativeEncodedLP.Encoded lp→
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
                  Nat.lt ((0:Nat)) cfg.K→
                    Nat.lt ((0:Nat)) cfg.b→
                      ∀ {n:Nat} (G:SimpleGraph (Fin n))
                        [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                        (D k fuel S v R F w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
                        (front:List Nat),
                        Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                            (Nat.add
                              (Nat.mul S
                                (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                            capacity
                            (Nat.add fuel
                              ((1:Nat)))
                            n G k (@List.length Nat front)→
                          Nat.lt ((1:Nat)) n→
                            Nat.le ((4:Nat)) D→
                              Nat.lt ((0:Nat)) F→
                                Nat.lt (Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D) k→
                                  Nat.le n R→
                                    Nat.le k R→
                                      Nat.le (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                                          R→
                                        Nat.le D R→
                                          Nat.le F R→
                                            Nat.le
                                                (Lax263307.MomentLP.dimension n
                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                                                R→
                                              ∀
                                                (state:
                                                  Lax263307.RoundedOracleSearch.State
                                                    (Lax263307.MomentLP.dimension n
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                (∀
                                                    (i:
                                                      Fin
                                                        (Lax263307.MomentLP.dimension n
                                                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))),
                                                    Lax263307.NativeRoundedStep.height
                                                      (@Prod.snd
                                                        (Matrix
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D)))
                                                          Rat)
                                                        (Fin
                                                            (Lax263307.MomentLP.dimension n
                                                              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n
                                                                D))→
                                                          Rat)
                                                        state i)
                                                      (Nat.mul
                                                        ((80:Nat))
                                                        (Nat.add R
                                                          ((1:Nat)))))→
                                                  @Lax263307Proofs.NativeOracleExecution.ProjectionBounds n D k
                                                      (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) F
                                                      (@HPow.hPow Nat Nat Nat
                                                        (@instHPow Nat Nat
                                                          (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                        ((2:Nat))
                                                        (Nat.mul
                                                          ((100:Nat))
                                                          (Nat.add R
                                                            ((1:Nat)))))
                                                      w (@Lax263307Proofs.NativeSelectedLP.oracleTime lp lpProgram R) G
                                                      inst extent→
                                                    Lax263307Proofs.NativeNearExecution.Bounds n
                                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D) D k
                                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D)
                                                        (@HPow.hPow Nat Nat Nat
                                                          (@instHPow Nat Nat
                                                            (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                          ((2:Nat))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (Nat.mul
                                                          ((2:Nat))
                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight lp
                                                            lpProgram R))
                                                        (Nat.add R
                                                          ((1:Nat)))
                                                        fuel S w cfg extent front→
                                                      Nat.le
                                                          (@Lax263307Proofs.NativeSelectedLP.wordHeight lp lpProgram R)
                                                          w→
                                                        Nat.le
                                                            (Nat.add
                                                              (Lax263307Proofs.NativeCutResources.wordExponent
                                                                (Lax263307.MomentLP.dimension n
                                                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b
                                                                    n D))
                                                                (Nat.add
                                                                  (Nat.mul
                                                                    ((2:Nat))
                                                                    (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                      lp lpProgram R))
                                                                  ((1:Nat))))
                                                              ((4:Nat)))
                                                            w→
                                                          Nat.lt
                                                              (Lax263307Proofs.NativeSelectedLP.queryBound R)
                                                              (extent "vm.input")→
                                                            Nat.le
                                                                (Lax263307Proofs.NativeUniformFlow.wordHeight n
                                                                  (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                    cfg.b n
                                                                    (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                    (Nat.mul
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R)))
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.code flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.width
                                                                    flow flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.time flow
                                                                    flowProgram)
                                                                  (@Lax263307Proofs.NativeSelectedNear.Program.output
                                                                    flow flowProgram))
                                                                w→
                                                              (∀ (a:String),
                                                                  @Membership.mem String (List String)
                                                                      (@List.instMembership String)
                                                                      Lax263307Proofs.NativeSeparatorContext.workspace
                                                                      a→
                                                                    Nat.le
                                                                      (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                        (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                          cfg.b n
                                                                          (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                          k
                                                                          (@HMul.hMul Nat Nat Nat
                                                                            (@instHMul Nat instMulNat)
                                                                            ((2:Nat))
                                                                            (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                              lp lpProgram R)))
                                                                        (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                          flow flowProgram))
                                                                      (extent a))→
                                                                ∀
                                                                  (child:
                                                                    (A:Finset (Fin n))→
                                                                      Nat→
                                                                        Option (Finset (Fin (@Finset.card (Fin n) A)))),
                                                                  @Lax263307Proofs.NativeRecursiveSetup.Oracle n
                                                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    D k
                                                                    (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K
                                                                      cfg.b n D)
                                                                    cfg.b (Lax263307.AlgorithmParameters.load cfg.b n D)
                                                                    F fuel S v w
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (Nat.mul
                                                                        ((100:Nat))
                                                                        (@HAdd.hAdd Nat Nat Nat
                                                                          (@instHAdd Nat instAddNat) R
                                                                          ((1:Nat)))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (Nat.add
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R))
                                                                        ((1:Nat))))
                                                                    (@HPow.hPow Nat Nat Nat
                                                                      (@instHPow Nat Nat
                                                                        (@NPow.toPow Nat
                                                                          (@Monoid.toNPow Nat Nat.instMonoid)))
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (Nat.mul
                                                                      ((2:Nat))
                                                                      (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                        lp lpProgram R))
                                                                    (Nat.add R
                                                                      ((1:Nat)))
                                                                    (Lax263307Proofs.NativeUniformFlow.spaceBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    (@Lax263307Proofs.NativeSelectedLP.oracleTime lp
                                                                      lpProgram R)
                                                                    (@Lax263307Proofs.NativeSelectedLP.callCost lp
                                                                      lpProgram R)
                                                                    (Lax263307Proofs.NativeSeparatorOutput.timeBound n
                                                                      (Lax263307Proofs.NativeLargeResources.heightExponent
                                                                        cfg.b n
                                                                        (Lax263307.AlgorithmParameters.load cfg.b n D) k
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat)
                                                                          ((2:Nat))
                                                                          (@Lax263307Proofs.NativeSelectedLP.certificateHeight
                                                                            lp lpProgram R)))
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.code
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.coeff
                                                                        flow flowProgram)
                                                                      (@Lax263307Proofs.NativeSelectedNear.Program.time
                                                                        flow flowProgram))
                                                                    childSteps childTime cfg G inst lp flow extent front
                                                                    child state
                                                                    (Lax263307Proofs.NativeRecursiveDomain.eligible C
                                                                      rootN
                                                                      (Nat.add
                                                                        (@HMul.hMul Nat Nat Nat
                                                                          (@instHMul Nat instMulNat) S
                                                                          (@List.length String
                                                                            (Lax263307Proofs.NativeCoreMachine.frameArrays
                                                                              cfg)))
                                                                        (@List.length String
                                                                          (Lax263307Proofs.NativeCoreMachine.frameScalars
                                                                            cfg)))
                                                                      capacity):= @Lax263307Proofs.NativeSelectedOracle.setup
