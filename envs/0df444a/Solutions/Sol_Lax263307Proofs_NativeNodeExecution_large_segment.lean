-- Prove2me | solution 1 for Lax263307Proofs.NativeNodeExecution.large_segment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:49.683013+00:00
-- url     : https://prove2.me/submissions/4d4043e7-102a-4b7a-aeae-b1bd4a90f7a3

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax263307Proofs_NativeOracleRounds_search_segment
import Theorems.Thm_Lax263307Proofs_NativeNodeTrace_large_segment_native
import Theorems.Thm_Lax263307Proofs_NativeOracleContext_of_large_native

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

namespace Lax263307Proofs.NativeNodeTrace
end Lax263307Proofs.NativeNodeTrace
theorem Lax263307Proofs.NativeNodeTrace.large_segment:∀ {n:Nat} (B:Nat) (cfg:Lax263307Proofs.NativeCoreMachine.Config) (D k fuel:Nat) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
  LT.lt ((0:Nat)) n→
    LT.lt ((0:Nat)) cfg.K→
      LT.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd
                (Lax263307Proofs.NativeNodeParameters.guard cfg.a cfg.K cfg.b n D) k)
              cfg.b)
            ((5:Nat)))
          B→
        LT.lt
            (Lax263307Proofs.NativeMomentSetup.guardBound n k
              (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
            B→
          LT.lt
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) n)
              B→
            LT.lt
                (Lax263307Proofs.NativeNodePrecision.guard n D
                  (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                  (Lax263307.AlgorithmParameters.floorDenominator cfg.a cfg.K cfg.b n D)
                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                B→
              LT.lt
                  (HAdd.hAdd
                    (HAdd.hAdd
                      (HMul.hMul
                        ((3:Nat))
                        (HMul.hMul
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                          (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))))
                      (HMul.hMul
                        ((3:Nat))
                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))))
                    ((20:Nat)))
                  B→
                ∀ (σ:Lax808846Proofs.Imp.Env),
                  @Lax263307Proofs.NativeLargeNode.Input n B cfg.a cfg.K cfg.b D k G inst σ→
                    @Eq Nat (σ.vars "recursion.fuel") fuel→
                      @Eq Nat (σ.vars "machine.running") ((1:Nat))→
                        @Eq Nat (σ.vars "machine.phase") ((3:Nat))→
                          ∃ (τ:Lax808846Proofs.Imp.Env),
                            And
                              (Lax263307Proofs.NativeMachineSegment.Segment B
                                (Lax263307Proofs.NativeCoreMachine.phases cfg)
                                ((1:Nat))
                                (HAdd.hAdd
                                  (Lax263307Proofs.NativeLargeNode.cost cfg.a n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                                  ((2:Nat)))
                                σ τ)
                              (And (@Lax263307Proofs.NativeLargeNode.Output n cfg.a cfg.K cfg.b D k G inst τ)
                                (And (@Eq Nat (τ.vars "recursion.fuel") fuel)
                                  (And
                                    (@Eq Nat (τ.vars "machine.running")
                                      ((1:Nat)))
                                    (@Eq Nat (τ.vars "machine.phase")
                                      ((4:Nat)))))):= @Lax263307Proofs.NativeNodeTrace.large_segment_native
namespace Lax263307Proofs.NativeOracleContext
end Lax263307Proofs.NativeOracleContext
theorem Lax263307Proofs.NativeOracleContext.of_large:∀ {n:Nat} (B D k fuel S v:Nat) (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n))
  [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)] (extent:String→ Nat) (front:List Nat)
  (σ:Lax808846Proofs.Imp.Env),
  @Lax263307Proofs.NativeLargeNode.Output n cfg.a cfg.K cfg.b D k G inst σ→
    Lax263307Proofs.NativeStateBounds.Bounded B σ→
      (∀ (a:String), @Eq Nat (@List.length Nat (σ.arrs a)) (extent a))→
        Lax455465Proofs.RamVirtualState.Prefix front "recursion.frames" σ→
          @Eq Nat (σ.vars "stack.words") (@List.length Nat front)→
            @Eq Nat (σ.vars "recursion.stride") S→
              @Eq Nat (σ.vars "recursion.fuel")
                  (HAdd.hAdd fuel
                    ((1:Nat)))→
                @Eq Nat (σ.vars "algorithm.roundWidth") v→
                  @Eq Nat (σ.vars "frame.length")
                      (HAdd.hAdd
                        (HMul.hMul S
                          (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                        (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))→
                    And
                      (@Lax263307Proofs.NativeOracleContext.Context n B D k
                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                        (Lax263307.AlgorithmParameters.load cfg.b n D)
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (Lax263307.AlgorithmParameters.floorDenominator cfg.a cfg.K cfg.b n D)
                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                        fuel S v (Lax263307.AlgorithmParameters.iterations cfg.a cfg.K cfg.b n D) cfg G inst extent
                        front σ)
                      (@Lax263307Proofs.NativeRoundedTrace.StoredState
                        (Lax263307.MomentLP.dimension n (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))
                        ((0:Nat))
                        (@Prod.mk
                          (Matrix
                            (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                            (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                            Rat)
                          (Fin
                              (Lax263307.MomentLP.dimension n
                                (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))→
                            Rat)
                          (@OfNat.ofNat
                            (Matrix
                              (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                              (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                              Rat)
                            (nat_lit 1)
                            (@One.toOfNat1
                              (Matrix
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                Rat)
                              (@Matrix.one
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                Rat
                                (instDecidableEqFin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring))
                                (@AddMonoidWithOne.toOne Rat
                                  (@AddGroupWithOne.toAddMonoidWithOne Rat
                                    (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))))))
                          (@OfNat.ofNat
                            (Fin
                                (Lax263307.MomentLP.dimension n
                                  (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))→
                              Rat)
                            (nat_lit 0)
                            (@Zero.toOfNat0
                              (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))→
                                Rat)
                              (@Pi.instZero
                                (Fin
                                  (Lax263307.MomentLP.dimension n
                                    (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D)))
                                (fun
                                    (a:
                                      Fin
                                        (Lax263307.MomentLP.dimension n
                                          (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))) =>
                                  Rat)
                                fun
                                  (i:
                                    Fin
                                      (Lax263307.MomentLP.dimension n
                                        (Lax263307.AlgorithmParameters.level cfg.a cfg.K cfg.b n D))) =>
                                @MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
                        σ):= @Lax263307Proofs.NativeOracleContext.of_large_native

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

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

end

section

namespace Lax808846Proofs.Imp

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

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

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

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

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

namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem word_spec (B v:ℕ) (h2:2 < B) (hv:v < B):
    Spec B (fun σ => σ.vars "size.value"=v) word
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 6):=by
  let I:=fun σ:Env => σ.vars "size.value" ≤ v∧
    σ.vars "size.count" + (σ.vars "size.value").size=v.size
  have hs:v.size≤ v:=Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hlo:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => I τ∧ (Cond.lt (.lit 0) (.var "size.value")).evalB B τ=some false)
      (12 * v.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "size.value").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))⟩
    · rintro σ ⟨hI,hcond⟩
      have hval:=hI.1.trans_lt hv
      have hp:0 < σ.vars "size.value" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var hval)] at hcond
        simpa using hcond
      have hhalf:=WordSize.size_half (σ.vars "size.value") hp
      have hcounter:σ.vars "size.count" + 1 < B:=by
        have hsz:=Nat.size_pos.mpr hp
        have heq:=hI.2
        omega
      have hdiv:=(Nat.div_le_self (σ.vars "size.value") 2).trans_lt hval
      have hle:=(Nat.div_le_self (σ.vars "size.value") 2).trans hI.1
      (expose_names;
        (refine let c0:Env→ Prop:=(fun (σ_1 σ':Env) => And (I σ') (Nat.lt (Nat.size (Env.vars σ' "size.value")) (Nat.size (Env.vars σ_1 "size.value")))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "size.value") ((2:Nat)); let c2:Env:=Env.setVar σ "size.value" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=Env.vars c2 "size.count"; let c5:Nat:=c3 c4 ((1:Nat)); let c6:Env:=Env.setVar c2 "size.count" c5; let c7:Nat→ Nat:=c3 ((1:Nat)); let c8:Expr:=Expr.div (Expr.var "size.value") (Expr.lit ((2:Nat))); let c9:Nat:=c7 (Expr.size c8); let c10:Expr:=Expr.add (Expr.var "size.count") (Expr.lit ((1:Nat))); let c11:Nat:=c7 (Expr.size c10); @Exists.intro Env (fun (σ':Env) => And (Run B wordStep σ σ' ((8:Nat))) (c0 σ')) c6 (@And.intro (Run B wordStep σ c6 ((8:Nat))) (c0 c6) (RunStep.mono B wordStep σ c6 (c3 c9 c11) ((8:Nat)) (RunStep.seq B (Com.assign "size.value" c8) (Com.assign "size.count" c10) σ c2 c6 c9 c11 (RunStep.assign B σ "size.value" c8 c1 (RunStep.eval_div B σ (Expr.var "size.value") (Expr.lit ((2:Nat))) (Env.vars σ "size.value") ((2:Nat)) (RunStep.eval_var B σ "size.value" hval) (RunStep.eval_lit B ((2:Nat)) σ h2) hdiv)) (RunStep.assign B c2 "size.count" c10 c5 (RunStep.eval_add B c2 (Expr.var "size.count") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c2 "size.count" (?nAX_g6023_0_0_0)) (RunStep.eval_lit B ((1:Nat)) c2 (?nAX_g6023_0_0_1)) (?nAX_g6023_0_0_2)))) (?nAX_g6023_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp_all [I]
      all_goals omega
    · rintro σ ⟨hvalue,hcount⟩
      simp [I,hvalue,hcount]
    · rintro σ ⟨hvalue,hcount⟩
      simp [hvalue]
  have hfinish:Spec B (fun σ => σ.vars "size.value"=v∧ σ.vars "size.count"=0) wordLoop
      (fun _ τ => τ.vars "size.value"=0∧ τ.vars "size.count"=v.size) (12 * v.size + 4):=hlo.post (by
    rintro σ τ _ ⟨hI,hcond⟩
    have hzero:τ.vars "size.value"=0:=by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hv))] at hcond
      simpa using hcond
    exact ⟨hzero,by simpa only [hzero,Nat.size_zero,Nat.add_zero] using hI.2⟩)
  rintro σ hvalue
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "size.count" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B wordLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size v)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "size.value") ((0:Nat))) (@Eq Nat (Env.vars σ' "size.count") (Nat.size v))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x τ:Env) => And (@Eq Nat (Env.vars τ "size.value") ((0:Nat))) (@Eq Nat (Env.vars τ "size.count") (Nat.size v)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B word σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "size.value") v) (@Eq Nat (Env.vars σ_1 "size.count") ((0:Nat)))) wordLoop c7 c4 hfinish c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "size.value") ((0:Nat))) (@Eq Nat (Env.vars w "size.count") (Nat.size v)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B word σ w c6) (c8 w) (RunStep.mono B word σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "size.count" (Expr.lit ((0:Nat)))) wordLoop σ c0 w c12 c4 (RunStep.assign B σ "size.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6023_1_0_0))) left) (?nAX_g6023_1_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6023_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6023_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

open RamVirtualState Lax759944.BinaryWordEncoding

end Lax455465Proofs.RamBitSize

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.NativeLogarithms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open Lax455465Proofs

theorem size_eq (n:ℕ) (hn:0< n):n.size=Nat.log2 n+1:=by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  · have hp:2^Nat.log2 n≤ n:=by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hs:=Nat.lt_size.mpr hp
    omega

theorem small_spec (B n:ℕ) (hn:0< n) (hB:n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) small
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1) (12*n.size+10):=by
  intro σ hs
  let ν:=σ.setVar "size.value" n
  have r1:Run B (.assign "size.value" (.var "graph.n")) σ ν 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩)
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B n (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.log" n.size
  have hsize:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.log" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change n.size=Nat.log2 n+1; exact size_eq n hn⟩

theorem large_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) large
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.logarithm"=logarithm n) (12*(2*n).size+12):=by
  intro σ hs
  let ν:=σ.setVar "size.value" (2*n)
  have r1:Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩) (by change 2*n< B; omega))
  obtain ⟨μ,r2,p2⟩:=RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by rfl)
  let τ:=μ.setVar "node.logarithm" (2*n).size
  have hsize:(2*n).size≤2*n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have r3:Run B (.assign "node.logarithm" (.var "size.count")) μ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change (2*n).size=Nat.log2 (2*n)+1; exact size_eq (2*n) (by omega)⟩

theorem command_spec (B n:ℕ) (hn:0< n) (hB:2*n+3< B):
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n∧ τ.vars "node.log"=Nat.log2 n+1∧
        τ.vars "node.logarithm"=logarithm n) (12*n.size+12*(2*n).size+22):=by
  intro σ hs
  obtain ⟨ν,r1,p1⟩:=small_spec B n hn (by omega) σ hs
  obtain ⟨τ,r2,p2⟩:=large_spec B n hn hB ν p1.1
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1,
    (r2.frame_var "node.log" (by decide)).trans p1.2,p2.2⟩

end Lax263307Proofs.NativeLogarithms

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

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

def Invariant {n:ℕ} (I:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "mask.i"≤ n∧
  Prefix (encodeOutput I) "subset.bits" σ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

end Lax263307Proofs.NativeMasks

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

end Lax263307Proofs.NativeCatalogMetadata

end

section

namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Context (b e:ℕ) (σ:Env):Prop:=σ.vars "power.base"=b∧ σ.vars "power.exponent"=e

def Invariant (b e:ℕ) (σ:Env):Prop:=
  Context b e σ∧ σ.vars "power.i"≤ e∧ σ.vars "power.value"=b^(σ.vars "power.i")

theorem step_spec (B b e i:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B) (hi:i< e):
    Spec B (fun σ => Context b e σ∧ σ.vars "power.i"=i∧ σ.vars "power.value"=b^i) step
      (fun _ τ => Context b e τ∧ τ.vars "power.i"=i+1∧ τ.vars "power.value"=b^(i+1)) 8:=by
  have hp:b^i< B:=(Nat.pow_le_pow_right hb hi.le).trans_lt (by omega)
  have hnext:b^i*b< B:=by
    rw [←pow_succ]
    exact (Nat.pow_le_pow_right hb hi).trans_lt (by omega)
  (expose_names;
    (refine fun (σ:Env) (a:And (Context b e σ) (And (@Eq Nat (Env.vars σ "power.i") i) (@Eq Nat (Env.vars σ "power.value") (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b i)))) => let c0:Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) b; let c1:Prop:= @Eq Nat (Env.vars σ "power.value") (c0 i); let c2:Prop:=And (@Eq Nat (Env.vars σ "power.i") i) c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:=c3 i ((1:Nat)); let c5:Nat:=c0 c4; let c6:Env→ Prop:=(fun (x τ:Env) => And (Context b e τ) (And (@Eq Nat (Env.vars τ "power.i") c4) (@Eq Nat (Env.vars τ "power.value") c5))) σ; let c7:Env→ Prop:=fun (σ':Env) => And (Run B step σ σ' ((8:Nat))) (c6 σ'); let c8:Prop:= @Exists Env c7; let c9:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c10:Env:=Env.setVar σ "power.value" c9; let c11:Nat:=Env.vars c10 "power.i"; let c12:Nat:=c3 c11 ((1:Nat)); let c13:Env:=Env.setVar c10 "power.i" c12; let c14:Nat→ Nat:=c3 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c16:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c13; @And.casesOn (Context b e σ) c2 (fun (x:And (Context b e σ) c2) => c8) a fun (left:Context b e σ) (right:c2) => @And.casesOn (@Eq Nat (Env.vars σ "power.i") i) c1 (fun (x:c2) => c8) right fun (left_1:@Eq Nat (Env.vars σ "power.i") i) (right_1:c1) => @Exists.intro Env c7 c13 (@And.intro (Run B step σ c13 ((8:Nat))) (c6 c13) (RunStep.mono B step σ c13 (c3 c15 c17) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c16) σ c10 c13 c15 c17 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c9 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g8253_0_0_0)) (RunStep.eval_var B σ "power.base" ?_) ?_)) (RunStep.assign B c10 "power.i" c16 c12 (RunStep.eval_add B c10 (Expr.var "power.i") (Expr.lit ((1:Nat))) c11 ((1:Nat)) (RunStep.eval_var B c10 "power.i" (?nAX_g8253_0_0_1)) (RunStep.eval_lit B ((1:Nat)) c10 (?nAX_g8253_0_0_2)) (?nAX_g8253_0_0_3)))) (?nAX_g8253_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8253_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8253_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,pow_succ]
  all_goals omega

theorem command_spec (B b e:ℕ) (hb:1≤ b) (hB:b+e+b^e+3< B):
    Spec B (Context b e) command
      (fun _ τ => Context b e τ∧ τ.vars "power.value"=b^e) (12*e+8):=by
  have hbody:Spec B (fun σ => Invariant b e σ∧ σ.vars "power.i"< e) step
      (fun σ τ => Invariant b e τ∧ τ.vars "power.i"=σ.vars "power.i"+1) 8:=by
    rintro σ ⟨⟨hc,hle,hv⟩,hlt⟩
    obtain ⟨τ,rr,ht⟩:=step_spec B b e (σ.vars "power.i") hb hB hlt σ ⟨hc,rfl,hv⟩
    exact ⟨τ,rr,⟨ht.1,by rw [ht.2.1]; omega,by simpa only [ht.2.1] using ht.2.2⟩,ht.2.1⟩
  have hloop:=Spec.forRangeZero "power.i" "power.exponent" (Invariant b e) e 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν:=σ.setVar "power.value" 1
  have r1:Run B (.assign "power.value" (.lit 1)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hi:Invariant b e (ν.setVar "power.i" 0):=by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,ν,vars_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩:=hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,by simpa only [p2.2] using p2.1.2.2⟩

end Lax263307Proofs.NativeNaturalPower

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.ParameterResources

open Lax263307.AlgorithmParameters Lax263307.ParameterResources

theorem cutoff_eq_level (a K B n D:ℕ):cutoff a K B n D=level a K B n D:=by
  have h:targetThreshold a K B n D≤ level a K B n D:=by
    unfold level sparsity
    have hfactor:1≤ Nat.log2 n + 1:=by omega
    nlinarith
  exact max_eq_right h

end Lax263307Proofs.ParameterResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.AlgorithmParameters

def Context (n D:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.D"=D∧ σ.vars "node.log"=Nat.log2 n+1∧
    σ.vars "node.logarithm"=logarithm n

def Data (a K b n D:ℕ) (σ:Env):Prop:=Context n D σ∧
  σ.vars "node.load"=load b n D∧ σ.vars "node.threshold"=targetThreshold a K b n D∧
  σ.vars "node.sparsity"=sparsity a K b n D∧ σ.vars "moment.r"=level a K b n D∧
  σ.vars "node.cutoff"=cutoff a K b n D∧ σ.vars "node.floorDen"=floorDenominator a K b n D

theorem context_frame {B n D t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hs:Context n D σ) (hn:"graph.n"∉c.wvars) (hD:"node.D"∉c.wvars)
    (hl:"node.log"∉c.wvars) (hL:"node.logarithm"∉c.wvars):Context n D τ:=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,
    (rr.frame_var _ hl).trans hs.2.2.1,(rr.frame_var _ hL).trans hs.2.2.2⟩

theorem floor_eq (a K b n D:ℕ):floorDenominator a K b n D=2*n*level a K b n D:=by
  unfold floorDenominator level
  ring

theorem setup_spec (B a K b n D:ℕ) (hB:guard a K b n D< B):
    Spec B (Context n D) (setup a b)
      (fun _ τ => Context n D τ∧ τ.vars "node.load"=load b n D∧
        NativeNaturalPower.Context (load b n D+1) (4*a+2) τ) 12:=by
  intro σ hs
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c0 (c1 ((4:Nat)) a) ((2:Nat)); let c3:Env→ Prop:=NativeNaturalPower.Context (c0 (load b n D) ((1:Nat))) c2; let c4:Env→ Prop:=(fun (x τ:Env) => And (Context n D τ) (And (@Eq Nat (Env.vars τ "node.load") (load b n D)) (c3 τ))) σ; let c5:Nat:=c1 ((12:Nat)) b; let c6:Nat:=c1 c5 (Env.vars σ "node.D"); let c7:Nat:=c1 c6 (Env.vars σ "node.logarithm"); let c8:Env:=Env.setVar σ "node.load" c7; let c9:Nat:=Env.vars c8 "node.load"; let c10:Nat:=c0 c9 ((1:Nat)); let c11:Env:=Env.setVar c8 "power.base" c10; let c12:Env:=Env.setVar c11 "power.exponent" c2; let c13:Nat→ Nat:=c0 ((1:Nat)); let c14:Expr:=Expr.lit c5; let c15:Expr:=Expr.mul c14 (Expr.var "node.D"); let c16:Expr:=Expr.mul c15 (Expr.var "node.logarithm"); let c17:Nat:=c13 (Expr.size c16); let c18:Expr:=Expr.add (Expr.var "node.load") (Expr.lit ((1:Nat))); let c19:Nat:=c13 (Expr.size c18); let c20:Expr:=Expr.lit c2; let c21:Nat:=c13 (Expr.size c20); let c22:Nat:=c0 c19 c21; let c23:Com:=Com.assign "power.base" c18; let c24:Com:=Com.assign "power.exponent" c20; @Exists.intro Env (fun (σ':Env) => And (Run B (setup a b) σ σ' ((12:Nat))) (c4 σ')) c12 (@And.intro (Run B (setup a b) σ c12 ((12:Nat))) (c4 c12) (RunStep.mono B (setup a b) σ c12 (c0 c17 c22) ((12:Nat)) (RunStep.seq B (Com.assign "node.load" c16) (Com.seq c23 c24) σ c8 c12 c17 c22 (RunStep.assign B σ "node.load" c16 c7 (RunStep.eval_mul B σ c15 (Expr.var "node.logarithm") c6 (Env.vars σ "node.logarithm") (RunStep.eval_mul B σ c14 (Expr.var "node.D") c5 (Env.vars σ "node.D") (RunStep.eval_lit B c5 σ ?_) (RunStep.eval_var B σ "node.D" ?_) ?_) (RunStep.eval_var B σ "node.logarithm" ?_) ?_)) (RunStep.seq B c23 c24 c8 c11 c12 c19 c21 (RunStep.assign B c8 "power.base" c18 c10 (RunStep.eval_add B c8 (Expr.var "node.load") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c8 "node.load" ?_) (RunStep.eval_lit B ((1:Nat)) c8 ?_) ?_)) (RunStep.assign B c11 "power.exponent" c20 c2 (RunStep.eval_lit B c2 c11 ?_)))) (?nAX_g8271_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8271_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Context,NativeNaturalPower.Context,Env.setVar,guard,load]
  all_goals omega

theorem finish_spec (B a K b n D:ℕ) (hB:guard a K b n D< B):
    Spec B (fun σ => Context n D σ∧ σ.vars "node.load"=load b n D∧
      σ.vars "power.value"=(load b n D+1)^(4*a+2)) (finish K)
      (fun _ τ => Data a K b n D τ) 22:=by
  have hg:=hB
  dsimp only [guard] at hg
  have hth:K*(load b n D+1)^(4*a+2)=targetThreshold a K b n D:=rfl
  have hsp:2*targetThreshold a K b n D=sparsity a K b n D:=rfl
  have hl:sparsity a K b n D*(Nat.log2 n+1)=level a K b n D:=rfl
  have hf:=floor_eq a K b n D
  rintro σ ⟨hc,hload,hpower⟩
  let ν:=σ.setVar "node.threshold" (targetThreshold a K b n D)
  have r1:Run B (.assign "node.threshold" (.mul (.lit K) (.var "power.value"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show K< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hpower.symm,hpower ▸ (by omega)⟩)
      (by change K*(load b n D+1)^(4*a+2)< B; rw [hth]; omega))
  have hν:ν.vars "node.threshold"=targetThreshold a K b n D:=by rfl
  let μ:=ν.setVar "node.sparsity" (sparsity a K b n D)
  have r2:Run B (.assign "node.sparsity" (.mul (.lit 2) (.var "node.threshold"))) ν μ 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
      (by rw [evalB_var_iff]; exact ⟨hν.symm,hν ▸ (by omega)⟩)
      (by change 2*targetThreshold a K b n D< B; rw [hsp]; omega))
  have hμ:μ.vars "node.sparsity"=sparsity a K b n D:=by rfl
  have hlog:=((r1.seq r2).frame_var "node.log" (by simp [Com.wvars])).trans hc.2.2.1
  let ρ:=μ.setVar "node.level" (level a K b n D)
  have r3:Run B (.assign "node.level" (.mul (.var "node.sparsity") (.var "node.log"))) μ ρ 4:=Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlog.symm,hlog ▸ (by omega)⟩)
      (by change sparsity a K b n D*(Nat.log2 n+1)< B; rw [hl]; omega))
  have hρ:ρ.vars "node.level"=level a K b n D:=by rfl
  let υ:=ρ.setVar "node.cutoff" (level a K b n D)
  have r4:Run B (.assign "node.cutoff" (.var "node.level")) ρ υ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hρ.symm,hρ ▸ (by omega)⟩)
  have hυ:=(r4.frame_var "node.level" (by simp [Com.wvars])).trans hρ
  let τ:=υ.setVar "moment.r" (level a K b n D)
  have r5:Run B (.assign "moment.r" (.var "node.level")) υ τ 2:=Run.assign
    (by rw [evalB_var_iff]; exact ⟨hυ.symm,hυ ▸ (by omega)⟩)
  have hτ:=(r5.frame_var "node.level" (by simp [Com.wvars])).trans hυ
  have horder:=((r1.seq (r2.seq (r3.seq (r4.seq r5)))).frame_var "graph.n" (by simp [Com.wvars])).trans hc.1
  let κ:=τ.setVar "node.floorDen" (floorDenominator a K b n D)
  have r6:Run B (.assign "node.floorDen" (.mul (.mul (.lit 2) (.var "graph.n")) (.var "node.level"))) τ κ 6:=by
    apply Run.assign
    rw [hf]
    apply evalB_bin (op:=.mul)
    · exact evalB_bin (op:=.mul) (evalB_lit (show 2< B by omega))
        (by rw [evalB_var_iff]; exact ⟨horder.symm,horder ▸ (by omega)⟩) (by change 2*n< B; omega)
    · rw [evalB_var_iff]; exact ⟨hτ.symm,hτ ▸ (by omega)⟩
    · change 2*n*level a K b n D< B
      rw [←hf]
      omega
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  refine ⟨κ,rr,⟨context_frame rr hc (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]),
    (rr.frame_var "node.load" (by simp [Com.wvars])).trans hload,
    ((r2.seq (r3.seq (r4.seq (r5.seq r6)))).frame_var "node.threshold" (by simp [Com.wvars])).trans hν,
    ((r3.seq (r4.seq (r5.seq r6))).frame_var "node.sparsity" (by simp [Com.wvars])).trans hμ,
    (r6.frame_var "moment.r" (by simp [Com.wvars])).trans (by rfl),?_,by rfl⟩⟩
  rw [Lax263307Proofs.ParameterResources.cutoff_eq_level]
  exact ((r5.seq r6).frame_var "node.cutoff" (by simp [Com.wvars])).trans (by rfl)

theorem command_spec (B a K b n D:ℕ) (hn:0< n) (hB:guard a K b n D< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "node.D"=D) (command a K b)
      (fun _ τ => Data a K b n D τ) (12*n.size+12*(2*n).size+12*(4*a+2)+64):=by
  rintro σ ⟨hnσ,hDσ⟩
  obtain ⟨ν,r1,p1⟩:=NativeLogarithms.command_spec B n hn (by dsimp [guard] at hB; omega) σ hnσ
  have hd1:Context n D ν:= ⟨p1.1,(r1.frame_var "node.D" (by decide)).trans hDσ,p1.2⟩
  obtain ⟨μ,r2,p2⟩:=setup_spec B a K b n D hB ν hd1
  obtain ⟨ρ,r3,p3⟩:=NativeNaturalPower.command_spec B (load b n D+1) (4*a+2) (by omega)
    (by dsimp [guard] at hB; omega) μ p2.2.2
  have hd3:=context_frame r3 p2.1 (by decide) (by decide) (by decide) (by decide)
  have hl3:=(r3.frame_var "node.load" (by decide)).trans p2.2.1
  obtain ⟨τ,r4,p4⟩:=finish_spec B a K b n D hB ρ ⟨hd3,hl3,p3.2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),p4⟩

end Lax263307Proofs.NativeNodeParameters

end

section

namespace Lax263307Proofs.NativeAttemptReply

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

theorem none_spec (B n ret:ℕ) (hB:n+ret+5< B):
    Spec B (fun σ => σ.vars "graph.n"=n) (noneCommand ret)
      (fun _ τ => τ.vars "graph.n"=n∧ NativeTargetDriver.Reply (none:Option (Finset (Fin n))) τ∧
        τ.vars "machine.phase"=ret) 6:=by
  intro σ hs
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "graph.n") n) (And (@NativeTargetDriver.Reply n (@none (Finset (Fin n))) τ) (@Eq Nat (Env.vars τ "machine.phase") ret))) σ; let c1:Env:=Env.setVar σ "recursion.return.tag" ((0:Nat)); let c2:Env:=Env.setVar c1 "recursion.return.mask" ((0:Nat)); let c3:Env:=Env.setVar c2 "machine.phase" ret; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ret)); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "recursion.return.mask" (Expr.lit ((0:Nat))); let c11:String→ Nat:=Env.vars c3; @Exists.intro Env (fun (σ':Env) => And (Run B (noneCommand ret) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (noneCommand ret) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (noneCommand ret) σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "recursion.return.tag" (Expr.lit ((0:Nat)))) (Com.seq c10 (Com.assign "machine.phase" (Expr.lit ret))) σ c1 c3 c6 c9 (RunStep.assign B σ "recursion.return.tag" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g8286_0_0_0))) (RunStep.seq B c10 (Com.assign "machine.phase" (Expr.lit ret)) c1 c2 c3 c6 c8 (RunStep.assign B c1 "recursion.return.mask" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g8286_0_0_1))) (RunStep.assign B c2 "machine.phase" (Expr.lit ret) ret (RunStep.eval_lit B ret c2 (?nAX_g8286_0_0_2))))) (?nAX_g8286_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g8286_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g8286_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeAttemptReply

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 AlgorithmParameters

inductive Route | exhaustive | reject | search
  deriving DecidableEq

def route (n k threshold fuel:ℕ):Route:=
  if k≤ threshold∨ n≤1 then .exhaustive else if n< k∨ fuel=0 then .reject else .search

def Output (small large ret:ℕ):Route→ Env→ Prop
  | .exhaustive,σ => σ.vars "machine.phase"=small
  | .reject,σ => σ.vars "machine.phase"=ret∧ σ.vars "recursion.return.tag"=0
  | .search,σ => σ.vars "machine.phase"=large

private theorem value {B x:ℕ} {s:String} {σ:Env} (h:σ.vars s=x) (hx:x< B):
    (Expr.var s).evalB B σ=some x:=by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem select_spec (B n k threshold fuel small large ret:ℕ) (hn:1< n)
    (hB:n+k+threshold+fuel+small+large+ret+10< B):
    Spec B (fun σ => σ.vars "graph.n"=n∧ σ.vars "node.k"=k∧ σ.vars "node.cutoff"=threshold∧
      σ.vars "recursion.fuel"=fuel) (select small large ret)
      (fun _ τ => Output small large ret (route n k threshold fuel) τ) 20:=by
  rintro σ ⟨hnσ,hk,ht,hf⟩
  have hsmall:(Cond.lt (.var "node.k") (.add (.var "node.cutoff") (.lit 1))).evalB B σ=
      some (decide (k≤ threshold)):=by
    have hh:=evalB_condLt (value hk (by omega))
      (evalB_bin (op:=.add) (value ht (by omega)) (evalB_lit (show 1< B by omega))
        (by change threshold+1< B; omega))
    simpa only [Bop.apply_add,Nat.lt_succ_iff] using hh
  have hlarge:(Cond.lt (.var "graph.n") (.var "node.k")).evalB B σ=some (decide (n< k)):=
    evalB_condLt (value hnσ (by omega)) (value hk (by omega))
  have hzero:(Cond.eq (.var "recursion.fuel") (.lit 0)).evalB B σ=some (decide (fuel=0)):=by
    simpa only [Bool.beq_eq_decide_eq] using evalB_condEq (value hf (by omega)) (evalB_lit (show 0< B by omega))
  by_cases hs:k≤ threshold
  · let τ:=σ.setVar "machine.phase" small
    have rr:Run B (.assign "machine.phase" (.lit small)) σ τ 2:=Run.assign (evalB_lit (show small< B by omega))
    refine ⟨τ,(Run.ite_true (d:=.ite (.lt (.var "graph.n") (.var "node.k")) (NativeAttemptReply.noneCommand ret)
      (.ite (.eq (.var "recursion.fuel") (.lit 0)) (NativeAttemptReply.noneCommand ret)
        (.assign "machine.phase" (.lit large)))) (by simpa only [hs,decide_true] using hsmall) rr).mono
      (by simp [Cond.size,Expr.size]),?_⟩
    simp [Output,route,hs,τ]
  · have hnot:¬(k≤ threshold∨ n≤1):=by omega
    by_cases hk':n< k
    · obtain ⟨τ,rr,p⟩:=NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
      have r2:=Run.ite_true (d:=.ite (.eq (.var "recursion.fuel") (.lit 0))
        (NativeAttemptReply.noneCommand ret) (.assign "machine.phase" (.lit large)))
        (by simpa only [hk',decide_true] using hlarge) rr
      refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
        (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
      simpa only [route,if_neg hnot,hk',true_or,if_true,Output] using (show τ.vars "machine.phase"=ret∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
    · by_cases hz:fuel=0
      · obtain ⟨τ,rr,p⟩:=NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
        have r3:=Run.ite_true (d:=.assign "machine.phase" (.lit large))
          (by simpa only [hz,decide_true] using hzero) rr
        have r2:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret)
          (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simpa only [route,if_neg hnot,hz,or_true,if_true,Output] using (show τ.vars "machine.phase"=ret∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
      · let τ:=σ.setVar "machine.phase" large
        have rr:Run B (.assign "machine.phase" (.lit large)) σ τ 2:=Run.assign (evalB_lit (show large< B by omega))
        have r3:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hz,decide_false] using hzero) rr
        have r2:=Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simp [route,hnot,hk',hz,Output,τ]

def Input (n D k fuel:ℕ) (σ:Env):Prop:=
  σ.vars "graph.n"=n∧ σ.vars "node.D"=D∧ σ.vars "node.k"=k∧ σ.vars "recursion.fuel"=fuel

theorem command_spec (B a K b n D k fuel small large ret:ℕ)
    (hB:NativeNodeParameters.guard a K b n D+n+k+cutoff a K b n D+fuel+small+large+ret+10< B):
    Spec B (Input n D k fuel) (command a K b small large ret)
      (fun _ τ => Input n D k fuel τ∧ Output small large ret (route n k (cutoff a K b n D) fuel) τ∧
        (route n k (cutoff a K b n D) fuel=.search→ NativeNodeParameters.Data a K b n D τ))
      (12*n.size+12*(2*n).size+12*(4*a+2)+88):=by
  rintro σ ⟨hn,hD,hk,hf⟩
  have htest:=evalB_condLt (value hn (show n< B by omega)) (evalB_lit (show 2< B by omega))
  by_cases hs:n<2
  · let τ:=σ.setVar "machine.phase" small
    have rr:Run B (.assign "machine.phase" (.lit small)) σ τ 2:=Run.assign (evalB_lit (show small< B by omega))
    refine ⟨τ,(Run.ite_true (d:=.seq (NativeNodeParameters.command a K b) (select small large ret))
      (by simpa only [hs,decide_true] using htest) rr).mono (by simp [Cond.size,Expr.size] <;> omega),?_,?_,?_⟩
    · simpa [Input,τ] using (show Input n D k fuel σ from ⟨hn,hD,hk,hf⟩)
    · have hsmall:n≤1:=by omega
      simp [route,hsmall,Output,τ]
    · have hsmall:n≤1:=by omega
      simp [route,hsmall]
  · obtain ⟨ν,r1,p1⟩:=NativeNodeParameters.command_spec B a K b n D (by omega) (by omega) σ ⟨hn,hD⟩
    have hk1:ν.vars "node.k"=k:=(r1.frame_var _ (by
      change "node.k"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hk
    have hf1:ν.vars "recursion.fuel"=fuel:=(r1.frame_var _ (by
      change "recursion.fuel"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hf
    obtain ⟨τ,r2,p2⟩:=select_spec B n k (cutoff a K b n D) fuel small large ret (by omega) (by omega) ν
      ⟨p1.1.1,hk1,p1.2.2.2.2.2.1,hf1⟩
    have hn2:=(r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.1
    have hD2:=(r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.2.1
    have hk2:=(r2.frame_var "node.k" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hk1
    have hf2:=(r2.frame_var "recursion.fuel" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hf1
    refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
      (by simpa only [hs,decide_false] using htest) (r1.seq r2)).mono (by simp [Cond.size,Expr.size] <;> omega),
      ⟨hn2,hD2,hk2,hf2⟩,p2,?_⟩
    intro _
    simpa only [NativeNodeParameters.Data,NativeNodeParameters.Context,
      r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.log" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.logarithm" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.load" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.threshold" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.sparsity" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "moment.r" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.cutoff" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.floorDen" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])] using p1

end Lax263307Proofs.NativeNodeDispatch

end

section

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target index cursor count:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars count=xs.length
  counter:σ.vars index≤ xs.length
  position:σ.vars cursor=front.length+σ.vars index
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars index)) target σ

end Lax263307Proofs.NativeAppendBuffer

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

end Lax263307Proofs.NativeArrayBounds

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding
open Lax263307

theorem actual_tolerance (a K b n D:ℕ):
    tolerance n D ((AlgorithmParameters.floorDenominator a K b n D)^(AlgorithmParameters.level a K b n D))=
      Lax263307.ProjectedOracle.tolerance a K b n D:=by
  unfold tolerance denominator Lax263307.ProjectedOracle.tolerance AlgorithmParameters.momentFloor
  rw [div_div]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  congr 1
  ring

end Lax263307Proofs.NativeNodeTolerance

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

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command:Com:=.ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))

end Lax263307Proofs.NativeChildReturn

end

section

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars "stack.copy.length"=xs.length
  index:σ.vars "stack.i"≤ xs.length
  position:σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars "stack.i")) target σ

end Lax263307Proofs.NativeBlockAppend

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

theorem append {B s t s' t':ℕ} {cases:List Com} {σ μ τ:Env}
    (a:Segment B cases s t σ μ) (b:Segment B cases s' t' μ τ):
    Segment B cases (s+s') (t+t') σ τ:=by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Segment.step h j hj rr (ih b)

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

theorem RootData.trans {σ ν τ:Env} (h1:RootData σ ν) (h2:RootData ν τ):RootData σ τ:=
  ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem root_frame {B t:ℕ} {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (ht:"root.target"∉c.wvars) (hf:"root.fuel"∉c.wvars):RootData σ τ:=
  ⟨rr.frame_var _ ht,rr.frame_var _ hf⟩

theorem protocol {n B D k r p b load F fuel S v limit:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {σ:Env} (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ):
    Protocol B D S v cfg extent front σ:=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

def arrays:List String:= ["catalog.mask","search.graph","catalog.card",
  "catalog.independent","moment.program","recursion.frames"]

theorem frame {n B D k r p b load F fuel S v limit t:ℕ} {cfg:Config}
    {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent:String→ ℕ} {front:List ℕ}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t)
    (hc:Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:∀ a∈arrays,a∉c.warrs):
    Context B D k r p b load F fuel S v limit cfg G extent front τ:=by
  have v (s:String) (hs:s∈scalars):=rr.frame_var s (hv s hs)
  have a (s:String) (hs:s∈arrays):=rr.frame_arr s (ha s hs)
  refine ⟨?_,(v _ (by simp [scalars])).trans hc.target,
    (v _ (by simp [scalars])).trans hc.sparsity,
    (v _ (by simp [scalars])).trans hc.denominator,
    (v _ (by simp [scalars])).trans hc.classB,
    (v _ (by simp [scalars])).trans hc.loadValue,
    (v _ (by simp [scalars])).trans hc.nodeD,
    (v _ (by simp [scalars])).trans hc.floorPower,?_,
    (v _ (by simp [scalars])).trans hc.programLength,
    (v _ (by simp [scalars])).trans hc.roundLimit,
    (v _ (by simp [scalars])).trans hc.roundWidth,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (v _ (by simp [scalars])).trans hc.cursor,
    (v _ (by simp [scalars])).trans hc.stride,
    (v _ (by simp [scalars])).trans hc.depth,
    (v _ (by simp [scalars])).trans hc.frameLength⟩
  · refine ⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by simp [scalars]))
      (hv _ (by simp [scalars])) (ha _ (by simp [arrays])) (ha _ (by simp [arrays])) hc.moments.1,
      ?_,?_,(v _ (by simp [scalars])).trans hc.moments.2.2.2⟩
    · simpa only [Prefix,a "catalog.card" (by simp [arrays])] using hc.moments.2.1
    · simpa only [Prefix,a "catalog.independent" (by simp [arrays])] using hc.moments.2.2.1
  · simpa only [Prefix,a "moment.program" (by simp [arrays])] using hc.program
  · intro s; rw [RamFrames.run_array_length rr]; exact hc.lengths s
  · simpa only [Prefix,a "recursion.frames" (by simp [arrays])] using hc.stack

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem actual_reply {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D k fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (center:MomentLP.Index n (AlgorithmParameters.level a K b n D)→ ℚ):
    let r:=AlgorithmParameters.level a K b n D
    let child:=fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t
    reply flow G D k (AlgorithmParameters.sparsity a K b n D) b (AlgorithmParameters.load b n D) child
      (projection lp G k D ((AlgorithmParameters.floorDenominator a K b n D)^r) center) =
      ProjectedOracle.run lp flow a K b D G k
        (fun C t => (child C t).map (fun I => I.image (label C))) center:=by
  dsimp only
  unfold projection
  rw [NativeNodeTolerance.actual_tolerance]
  have near_eq (x:MomentLP.Index n (AlgorithmParameters.level a K b n D)→ ℚ):
      NativeNearExecution.run flow G D k (AlgorithmParameters.sparsity a K b n D) b
        (AlgorithmParameters.load b n D) (MomentLP.decode x)
        (fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t) =
      NearOracle.run flow a K b D G k (MomentLP.decode x)
        (fun C t => (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t).map
          (fun I => I.image (label C))):=by rfl
  cases he:RationalProjection.classify (MomentLP.program G k (AlgorithmParameters.level a K b n D))
      (ProjectedOracle.tolerance a K b n D)
      (RegisteredLP.certificate lp (DistanceProjection.distanceProgram
        (MomentLP.program G k (AlgorithmParameters.level a K b n D)) (ProjectedOracle.raw center))) <;>
    simp only [reply,ProjectedOracle.run,he,near_eq,NativeComponentNormal.normal] <;> rfl

end Lax263307Proofs.NativeOracleExecution

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters NativeCoreMachine NativeMachineSegment

theorem large_input_frame {n B a K b D k t:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t) (hi:NativeLargeNode.Input B a K b D k G σ)
    (hn:τ.vars "graph.n"=n) (hD:τ.vars "node.D"=D) (hk:τ.vars "node.k"=k)
    (hg:τ.arrs "search.graph"=σ.arrs "search.graph"):NativeLargeNode.Input B a K b D k G τ:=by
  dsimp only [NativeLargeNode.Input] at hi ⊢
  rcases hi with ⟨_,_,_,graph,hb,ht,hbits,hm,hc,hi,hinput,hcache,hri,hs,hcenter⟩
  refine ⟨hn,hD,hk,?_,NativeArrayBounds.run rr hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Prefix,hg] using graph
  · simpa only [RamFrames.run_array_length rr] using ht
  · simpa only [RamFrames.run_array_length rr] using hbits
  · simpa only [RamFrames.run_array_length rr] using hm
  · simpa only [RamFrames.run_array_length rr] using hc
  · simpa only [RamFrames.run_array_length rr] using hi
  · simpa only [RamFrames.run_array_length rr] using hinput
  · simpa only [RamFrames.run_array_length rr] using hcache
  · simpa only [RamFrames.run_array_length rr] using hri
  · simpa only [RamFrames.run_array_length rr] using hs
  · simpa only [RamFrames.run_array_length rr] using hcenter

theorem search_entry_segment {n:ℕ} (B:ℕ) (cfg:Config)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel:ℕ)
    (hsmall:¬(k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1)) (hk:k≤ n) (hf:0< fuel)
    (hdispatch:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29< B)
    (σ:Env) (hi:NativeLargeNode.Input B cfg.a cfg.K cfg.b D k G σ)
    (hfu:σ.vars "recursion.fuel"=fuel) (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=1):
    ∃ τ,Segment B (phases cfg) 1 (entryCost cfg.a n) σ τ∧
      NativeLargeNode.Input B cfg.a cfg.K cfg.b D k G τ∧
      τ.vars "recursion.fuel"=fuel∧ τ.vars "machine.running"=1∧ τ.vars "machine.phase"=3:=by
  obtain ⟨τ,rr,po⟩:=NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ ⟨hi.1,hi.2.1,hi.2.2.1,hfu⟩
  refine ⟨τ,NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp rr,
    large_input_frame rr hi po.1.1 po.1.2.1 po.1.2.2.1 (rr.frame_arr _ (by
      change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
      decide)),po.1.2.2.2,?_,?_⟩
  · exact (rr.frame_var _ (by
      change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
      decide)).trans hr
  · have hrej:¬(n< k∨ fuel=0):=by omega
    simpa only [NativeNodeDispatch.route,hsmall,if_false,hrej,NativeNodeDispatch.Output] using po.2.1

end Lax263307Proofs.NativeNodeTrace

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

def scalars:List String:= ["stack.words","recursion.stride","frame.length","algorithm.roundWidth","node.D"]

theorem frame {B D S v t:ℕ} {cfg:Config} {extent:String→ ℕ} {front:List ℕ}
    {c:Com} {σ τ:Env} (rr:Run B c σ τ t) (hc:Protocol B D S v cfg extent front σ)
    (hv:∀ s∈scalars,s∉c.wvars) (ha:"recursion.frames"∉c.warrs):
    Protocol B D S v cfg extent front τ:=by
  refine ⟨NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.stride,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.frameLength,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.roundWidth,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.accuracy⟩
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" ha] using hc.stack

theorem dispatch_frame {B D S v t:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t)
    (hc:Protocol B D S v cfg extent front σ):Protocol B D S v cfg extent front τ:=by
  apply frame rr hc
  · change ∀ s∈scalars,s∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide
  · change "recursion.frames"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
    decide

theorem large_frame {B D S v t:ℕ} (cfg:Config) {extent:String→ ℕ} {front:List ℕ}
    {σ τ:Env} (rr:Run B (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) σ τ t)
    (hc:Protocol B D S v cfg extent front σ):Protocol B D S v cfg extent front τ:=by
  apply frame rr hc
  · change ∀ s∈scalars,s∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars
    decide
  · change "recursion.frames"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).warrs
    decide

theorem dispatch_root {B t:ℕ} (cfg:Config) {σ τ:Env}
    (rr:Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t):RootData σ τ:=by
  apply root_frame rr
  all_goals first
    | change "root.target"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
    | change "root.fuel"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide

theorem large_root {B t:ℕ} (cfg:Config) {σ τ:Env}
    (rr:Run B (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) σ τ t):RootData σ τ:=by
  apply root_frame rr
  all_goals first
    | change "root.target"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars; decide
    | change "root.fuel"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars; decide

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeRecursiveSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators RoundedOracleSearch
open NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

theorem Near.to_setup {n r D k p b load fuel S v M h T w space flowTime childSteps childTime:ℕ}
    {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {flow:List ℕ→ List ℕ} {x:Fin (NativeCatalogMetadata.N n r)→ ℚ}
    {extent:String→ ℕ} {front:List ℕ} {eligible:Eligible}
    {child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card))}
    (data:Near D k p b load fuel S v M h T w space flowTime childSteps childTime cfg G flow x extent front child eligible)
    (ih:Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child):
    NativeNearExecution.Setup D k p b load fuel S v M h T w space flowTime childSteps childTime
      cfg G flow x extent front child:=by
  refine ⟨data.bounds,data.hx,data.hselected,data.htarget,data.hspace,data.flowCall,?_⟩
  intro A choice
  dsimp only
  intro i hi heavy base σ hp hσ hd hm ht hr phase
  exact ih _ _ σ (data.children A choice i hi heavy) hp phase

theorem Oracle.to_setup {n r D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime:ℕ}
    {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lp flow:List ℕ→ List ℕ} {extent:String→ ℕ} {front:List ℕ} {eligible:Eligible}
    {child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card))}
    {state:State (MomentLP.dimension n r)}
    (data:Oracle D k p b load F fuel S v w M farM nearM h T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child state eligible)
    (ih:Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child):
    NativeOracleExecution.Setup D k p b load F fuel S v w M farM nearM h T space oracleTime callCost flowTime
      childSteps childTime cfg G lp flow extent front child state:=
  ⟨data.bounds,data.hcenter,data.hquery,data.call,data.farBounds,fun x hx => (data.nearSetup x hx).to_setup ih⟩

theorem Rounds.to_setup {n r D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost:ℕ}
    {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lp flow:List ℕ→ List ℕ} {extent:String→ ℕ} {front:List ℕ} {eligible:Eligible}
    {child:(C:Finset (Fin n))→ ℕ→ Option (Finset (Fin C.card))}
    (data:Rounds (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child eligible)
    (ih:Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child):
    NativeOracleRounds.Setup (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child:=
  ⟨data.program,fun j hj => (data.setup j hj).to_setup ih,data.rounded,data.hcost,data.hround⟩

end Lax263307Proofs.NativeRecursiveSetup

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeNodeExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

theorem large_input {n w D k fuel S v:ℕ} {cfg:Config} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent:String→ ℕ} {front:List ℕ} {σ:Env}
    (bounds:Bounds w D k fuel n cfg extent) (hi:Input (2^w) D fuel S v cfg G k extent front σ):
    NativeLargeNode.Input (2^w) cfg.a cfg.K cfg.b D k G σ:=by
  refine ⟨hi.order,hi.protocol.accuracy,hi.target,hi.graph,hi.protocol.bounded.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hi.protocol.lengths]; exact bounds.largeTable
  · rw [hi.protocol.lengths]; exact bounds.bits
  · rw [hi.protocol.lengths]; exact bounds.catalog
  · rw [hi.protocol.lengths]; exact bounds.cards
  · rw [hi.protocol.lengths]; exact bounds.independent
  · rw [hi.protocol.lengths]; exact bounds.input
  · rw [hi.protocol.lengths]; exact bounds.cache
  · rw [hi.protocol.lengths]; exact bounds.roundInput
  · rw [hi.protocol.lengths]; exact bounds.shape
  · rw [hi.protocol.lengths]; exact bounds.center

theorem large_segment {n:ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches:ℕ)
    (cfg:Config) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ) (eligible:Eligible)
    (bounds:Bounds w D k (fuel+1) n cfg extent)
    (data:Search D k fuel S v w childSteps childTime localSteps localTime branches cfg G lp flow extent front eligible)
    (children:Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible (child cfg lp flow D fuel G))
    (hsmall:¬(k≤ cutoff cfg.a cfg.K cfg.b n D∨ n≤1)) (hk:k≤ n)
    (σ:Env) (hi:Input (2^w) D (fuel+1) S v cfg G k extent front σ)
    (hr:σ.vars "machine.running"=1) (hp:σ.vars "machine.phase"=1):
    ∃ τ s t,Segment (2^w) (phases cfg) s t σ τ∧ s≤ localSteps+branches*childSteps∧
      t≤ localTime+branches*childTime∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel+1) G k) τ∧
      Protocol (2^w) D S v cfg extent front τ∧ RootData σ τ∧ GraphData G τ:=by
  obtain ⟨ν,first,largeν,fuelν,hrν,hpν⟩:=NativeNodeTrace.search_entry_segment (2^w) cfg G D k (fuel+1)
    hsmall hk (by omega) bounds.dispatch σ (large_input bounds hi) hi.depth hr hp
  have r1:=NativeMachineFrame.single_run first ⟨1,by change 1<16; decide⟩ hp
  change Run (2^w) (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ ν _ at r1
  have protocolν:=dispatch_frame cfg r1 hi.protocol
  obtain ⟨μ,second,largeμ,fuelμ,hrμ,hpμ⟩:=NativeNodeTrace.large_segment (2^w) cfg D k (fuel+1) G
    (by omega) bounds.classK bounds.parameters bounds.moment bounds.masks bounds.precision bounds.round
    ν largeν fuelν hrν hpν
  have r2:=NativeMachineFrame.single_run second ⟨3,by change 3<16; decide⟩ hpν
  change Run (2^w) (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) ν μ _ at r2
  have protocolμ:=large_frame cfg r2 protocolν
  obtain ⟨contextμ,storedμ⟩:=NativeOracleContext.of_large (2^w) D k fuel S v cfg G extent front μ largeμ
    protocolμ.bounded protocolμ.lengths protocolμ.stack protocolμ.cursor protocolμ.stride fuelμ protocolμ.roundWidth protocolμ.frameLength
  obtain ⟨τ,s,t,third,hs,ht,contextτ,answerτ,rootτ⟩:=NativeOracleRounds.search_segment
    D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
    ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)) fuel S v (limit cfg n D) w
    data.M data.farM data.nearM data.costH data.T data.space data.oracleTime data.callCost data.flowTime childSteps childTime
    data.c data.roundH (data.oracleLocal+(n+1)*childTime) data.roundCost (precision cfg.a cfg.K cfg.b n D)
    cfg G lp flow extent front (child cfg lp flow D fuel G) (data.data.to_setup children) rfl μ contextμ storedμ hrμ hpμ
  have heq:NativeOracleRounds.oracle (r:=level cfg n D) lp flow G D k (sparsity cfg.a cfg.K cfg.b n D)
      cfg.b (load cfg.b n D) ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)) (child cfg lp flow D fuel G) =
      fun (_:ℕ) center => ProjectedOracle.run lp flow cfg.a cfg.K cfg.b D G k
        (fun C t => (child cfg lp flow D fuel G C t).map (fun I => I.image (label C))) center:=by
    funext j center
    exact NativeOracleExecution.actual_reply lp flow cfg.a cfg.K cfg.b D k fuel G center
  have attemptEq:RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel+1) G k =
      ProjectedOracle.search lp flow cfg.a cfg.K cfg.b D G k
        (fun C t => (child cfg lp flow D fuel G C t).map (fun I => I.image (label C))):=by
    rw [RecursiveAlgorithm.attempt,if_neg hsmall,if_neg (Nat.not_lt.mpr hk)]
  refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second third),?_,?_,?_,
    NativeOracleContext.protocol contextτ,(dispatch_root cfg r1).trans ((large_root cfg r2).trans rootτ),
    contextτ.moments.1.1,contextτ.moments.1.2.2.2.1⟩
  · calc
      1+(1+s)≤2+((childSteps+5)*(n+1)+7)*limit cfg n D:=by omega
      _=(2+(5*(n+1)+7)*limit cfg n D)+((n+1)*limit cfg n D)*childSteps:=by ring
      _≤ localSteps+branches*childSteps:=Nat.add_le_add data.steps (Nat.mul_le_mul_right _ data.branching)
  · calc
      NativeNodeTrace.entryCost cfg.a n+(NativeLargeNode.cost cfg.a n (level cfg n D)+2+t)≤
          NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
            ((data.oracleLocal+(n+1)*childTime)+data.roundCost)*limit cfg n D:=by omega
      _=(NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
          (data.oracleLocal+data.roundCost)*limit cfg n D)+((n+1)*limit cfg n D)*childTime:=by ring
      _≤ localTime+branches*childTime:=Nat.add_le_add data.time (Nat.mul_le_mul_right _ data.branching)
  · rw [attemptEq]
    simpa only [heq,ProjectedOracle.search] using answerτ

end Lax263307Proofs.NativeNodeExecution

end

theorem solution:∀ {n:ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches:ℕ)
  (cfg:Lax263307Proofs.NativeCoreMachine.Config) (G:SimpleGraph (Fin n)) [inst:DecidableRel G.Adj]
  (lp flow:List ℕ→ List ℕ) (extent:String→ ℕ) (front:List ℕ)
  (eligible:Lax263307Proofs.NativeNodeProtocol.Eligible),
  Lax263307Proofs.NativeNodeExecution.Bounds w D k (fuel + 1) n cfg extent→
    ∀
      (data:
        Lax263307Proofs.NativeNodeExecution.Search D k fuel S v w childSteps childTime localSteps localTime branches cfg
          G lp flow extent front eligible),
      Lax263307Proofs.NativeNodeProtocol.Children (2 ^ w) D fuel S v childSteps childTime cfg G extent front eligible
          (Lax263307Proofs.NativeNodeExecution.child cfg lp flow D fuel G)→
        ¬(k≤ Lax263307.AlgorithmParameters.cutoff cfg.a cfg.K cfg.b n D∨ n≤ 1)→
          k≤ n→
            ∀ (σ:Lax808846Proofs.Imp.Env),
              Lax263307Proofs.NativeNodeProtocol.Input (2 ^ w) D (fuel + 1) S v cfg G k extent front σ→
                σ.vars "machine.running"=1→
                  σ.vars "machine.phase"=1→
                    ∃ (τ:Lax808846Proofs.Imp.Env) (s:ℕ) (t:ℕ),
                      Lax263307Proofs.NativeMachineSegment.Segment (2 ^ w)
                          (Lax263307Proofs.NativeCoreMachine.phases cfg) s t σ τ∧
                        s≤ localSteps + branches * childSteps∧
                          t≤ localTime + branches * childTime∧
                            Lax263307Proofs.NativeRoundTrace.Stopped
                                (Lax263307.RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel + 1) G k) τ∧
                              Lax263307Proofs.NativeOracleContext.Protocol (2 ^ w) D S v cfg extent front τ∧
                                Lax263307Proofs.NativeOracleContext.RootData σ τ∧
                                  Lax263307Proofs.NativeNodeProtocol.GraphData G τ:= @Lax263307Proofs.NativeNodeExecution.large_segment
