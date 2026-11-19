-- Prove2me | solution 1 for Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:34:27.805643+00:00
-- url     : https://prove2.me/submissions/67793a0a-8f5e-4b99-8a32-e79e4e0ecd59

import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamBinaryMinimum_minimum_spec_native
import Theorems.Thm_Lax109476Proofs_RamRecoveryThreshold_decideThreshold_spec_native

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

namespace Lax109476Proofs.RamBinaryMinimum
end Lax109476Proofs.RamBinaryMinimum
theorem Lax109476Proofs.RamBinaryMinimum.minimum_spec:∀ (S N w D M queryCost:Nat) (query:Rat→ Bool) (queryCom:Lax808846Proofs.Imp.Com)
  (Q:Lax808846Proofs.Imp.Env→ Prop),
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
                (∀ (t:Rat),
                    Lax109476Proofs.RationalArithmeticBounds.Height t
                        (HMul.hMul
                          ((4:Nat))
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                            ((2:Nat))))→
                      Lax808846Proofs.Reasoning.Spec
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          ((2:Nat)) w)
                        (fun (σ:Lax808846Proofs.Imp.Env) =>
                          And (Q σ) (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ))
                        queryCom
                        (fun (x τ:Lax808846Proofs.Imp.Env) =>
                          And (Q τ)
                            (@Eq (Option Bool)
                              (Lax808846Proofs.Imp.Cond.evalB
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  ((2:Nat)) w)
                                Lax109476Proofs.RamBisectionCommit.condition τ)
                              (@Option.some Bool (query t))))
                        queryCost)→
                  (∀ (x:String),
                      @Membership.mem String (List String) (@List.instMembership String)
                          Lax109476Proofs.RamBisectionLoop.fields x→
                        x∉ queryCom.wvars)→
                    "minimum.bound" ∉ queryCom.wvars→
                      Lax109476Proofs.RamBisectionLoop.preserves
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            ((2:Nat)) w)
                          Q Lax109476Proofs.RamRationalMidpoint.midpoint→
                        Lax109476Proofs.RamBisectionLoop.preserves
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              ((2:Nat)) w)
                            Q
                            (Lax109476Proofs.RamBisectionCommit.commit.seq Lax109476Proofs.RamBisectionLoop.increment)→
                          (∀ (σ:Lax808846Proofs.Imp.Env),
                              Q σ→ Q (σ.setVar "bisect.i" ((0:Nat))))→
                            Lax109476Proofs.RamBisectionLoop.preserves
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  ((2:Nat)) w)
                                Q Lax109476Proofs.RamBinaryMinimum.prepare→
                              Lax109476Proofs.RamBisectionLoop.preserves
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    ((2:Nat)) w)
                                  Q Lax109476Proofs.RamBinaryMinimum.finish→
                                Lax808846Proofs.Reasoning.Spec
                                  (@HPow.hPow Nat Nat Nat
                                    (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                    ((2:Nat)) w)
                                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                                    And (Q σ)
                                      (And (@Eq Nat (σ.vars "minimum.bound") D)
                                        (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                                  (Lax109476Proofs.RamBinaryMinimum.minimum queryCom)
                                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                    And (Q τ)
                                      (Lax109476Proofs.RamReconstructionRecord.Output
                                        (Lax109476Proofs.BinaryOptimization.minimum query D) τ))
                                  (HAdd.hAdd
                                    (HAdd.hAdd
                                      (HAdd.hAdd
                                        (HMul.hMul
                                          (HAdd.hAdd
                                            (HAdd.hAdd
                                              (HMul.hMul
                                                ((144:Nat)) M.size)
                                              ((342:Nat)))
                                            queryCost)
                                          (Lax109476Proofs.BinaryOptimization.steps D))
                                        (HMul.hMul
                                          ((12:Nat)) D.size))
                                      (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                    ((48:Nat))):= @Lax109476Proofs.RamBinaryMinimum.minimum_spec_native
namespace Lax109476Proofs.RamRecoveryThreshold
end Lax109476Proofs.RamRecoveryThreshold
theorem Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec:∀ (m n k M w:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat) (t:Rat)
  (hk:LT.lt k n),
  LE.le ((1:Nat)) M→
    LT.lt M
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
            (Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n M)) w→
          (∀ (i:Fin m) (j:Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M)→
            (∀ (i:Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M)→
              (∀ (j:Fin n),Lax109476Proofs.RationalArithmeticBounds.Height (x j) M)→
                Lax109476Proofs.RationalArithmeticBounds.Height t M→
                  (∀ (j:Fin n),
                      @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k σ)
                          (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ))
                      Lax109476Proofs.RamRecoveryThreshold.decideThreshold
                      (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k τ)
                          (@Eq (Option Bool)
                            (Lax808846Proofs.Imp.Cond.evalB
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                ((2:Nat)) w)
                              Lax109476Proofs.RamBisectionCommit.condition τ)
                            (@Option.some Bool
                              (@Lax109476Proofs.RationalFeasibilityDecision.feasible
                                (HAdd.hAdd
                                  (HAdd.hAdd m
                                    (HAdd.hAdd n n))
                                  ((1:Nat)))
                                n
                                (@Lax109476Proofs.CoordinateOptimization.coordinateCut
                                  (HAdd.hAdd m
                                    (HAdd.hAdd n n))
                                  n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) t)))))
                      (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n M):= @Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec_native

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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

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

theorem Run.bigStep {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K):
    ∃ k≤ K,BigStep c σ σ' k:=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk,hbs.bigStep⟩

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

end Lax109476Proofs.RationalArithmeticBounds

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

namespace Lax109476Proofs.RamRecoveryData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamScalarFrame

def arrays:List String:= ["point.A", "point.b", "point.x"]

end Lax109476Proofs.RamRecoveryData

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

namespace Lax109476Proofs.RamRecoveryMinimum

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalScalars RamRationalArrays RamRecoveryThreshold RationalArithmeticBounds

def pointFields:List String:= ["point.m", "point.n", "point.k"]

theorem state_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (hσ:State P x k σ)
    (hf:∀ a∈ pointFields,a∉ c.wvars)
    (ha:∀ a∈ RamRecoveryData.arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):
    State P x k τ:=by
  rcases hσ with ⟨hA,hb,hx,hm,hn,hk⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [RamRecoveryData.arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [RamRecoveryData.arrays])),
    RamReadBody.represents_frame _ _ hx hr (ha _ (by simp [RamRecoveryData.arrays])),
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hn,
    (hr.frame_var _ (hf _ (by simp [pointFields]))).trans hk⟩

theorem persistent_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ) (hσ:Persistent P x k σ)
    (hf:∀ a∈ pointFields,a∉ c.wvars)
    (ha:∀ a∈ RamRecoveryData.arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):
    Persistent P x k τ:= ⟨state_frame hr P x k hσ.1 hf ha,workspace_frame hr _ _ hσ.2⟩

theorem persistent_setVar {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ)
    (σ:Env) (v:String) (z:ℕ) (hv:v∉ pointFields) (hσ:Persistent P x k σ):
    Persistent P x k (σ.setVar v z):=by
  have hm:v ≠ "point.m" :=by intro h; subst v; simp [pointFields] at hv
  have hn:v ≠ "point.n" :=by intro h; subst v; simp [pointFields] at hv
  have hk:v ≠ "point.k" :=by intro h; subst v; simp [pointFields] at hv
  constructor
  · simpa [State,Represents,arrs_setVar,vars_setVar,Ne.symm hm,Ne.symm hn,Ne.symm hk] using hσ.1
  · exact hσ.2

theorem preserves_persistent (B:ℕ) {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ)
    (c:Com) (hf:∀ a∈ pointFields,a∉ c.wvars)
    (ha:∀ a∈ RamRecoveryData.arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):
    RamBisectionLoop.preserves B (Persistent P x k) c:=fun hr hσ => persistent_frame hr P x k hσ hf ha

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recoverCoordinate_spec (S N w D M m n k:ℕ) (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hk:k < n) (hB:4 * M ^ 2 + 3 < 2 ^ w) (hKB:BinaryOptimization.steps D < 2 ^ w)
    (hM:(D + 1) * 2 ^ BinaryOptimization.steps D≤ M) (hMS:M≤ 2 ^ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamRationalReconstruction.wordWidth S≤ w) (hDB:D < 2 ^ w)
    (hsize:((m + (n + n)) + 1) * n + m + (n + n) + 4 < 2 ^ w)
    (hwQuery:RamStoredFeasibility.wordWidth (sizeBound m n (4 * M ^ 2))≤ w)
    (hA:∀ i j,Height (P.A i j) M) (hb:∀ i,Height (P.b i) M)
    (hx:∀ j,Height (x j) M) (hc:∀ j,P.c j=0):
    Spec (2 ^ w) (fun σ => Persistent P x k σ∧ σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N)
      recoverCoordinate (fun _ τ => Persistent P x k τ∧ RamReconstructionRecord.Output
        (CoordinateOptimization.coordinateMinimum (LexicographicMinima.fixedPrefix P x k) ⟨k,hk⟩ D) τ)
      ((144 * M.size + 342 + instructionBound m n (4 * M ^ 2)) * BinaryOptimization.steps D +
        12 * D.size + RamRationalReconstruction.instructionBound S + 48):=by
  have hM1:1≤ M:=by
    have hp:1≤ 2 ^ BinaryOptimization.steps D:=Nat.one_le_pow _ _ (by decide)
    nlinarith
  have hMQ:M≤ 4 * M ^ 2:=by nlinarith
  have hquery:=fun t ht => decideThreshold_spec m n k (4 * M ^ 2) w P x t hk
    (by nlinarith) (by omega) hsize hwQuery
    (fun i j => height_mono _ (hA i j) hMQ) (fun i => height_mono _ (hb i) hMQ)
    (fun j => height_mono _ (hx j) hMQ) ht hc
  apply RamBinaryMinimum.minimum_spec S N w D M (instructionBound m n (4 * M ^ 2))
    (fun t => RationalFeasibilityDecision.feasible
      (CoordinateOptimization.coordinateCut (LexicographicMinima.fixedPrefix P x k) ⟨k,hk⟩ t))
    decideThreshold (Persistent P x k) hB hKB hM hMS hN hw hDB hquery
  · intro a ha
    simp [RamBisectionLoop.fields] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s∉ ([]:List String); simp
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s∉ ([]:List String); simp
  · intro σ hσ; exact persistent_setVar P x k σ "bisect.i" 0 (by decide) hσ
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; change a ++ s∉ ([]:List String); simp
  · apply preserves_persistent
    · intro a ha; simp [pointFields] at ha; rcases ha with rfl | rfl | rfl <;> decide
    · intro a ha s hs; simp [RamRecoveryData.arrays] at ha; simp [RamCopy.suffixes] at hs;
      rcases ha with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide

end Lax109476Proofs.RamRecoveryMinimum

end

theorem solution:∀ (S N w D M m n k:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat)
  (hk:Nat.lt k n),
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
                                      (Nat.add m
                                        (Nat.add n n))
                                      n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) D)
                                    τ))
                              (Nat.add
                                (Nat.add
                                  (Nat.add
                                    (Nat.mul
                                      (Nat.add
                                        (Nat.add
                                          (Nat.mul
                                            ((144:Nat)) M.size)
                                          ((342:Nat)))
                                        (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n
                                          (Nat.mul
                                            ((4:Nat))
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              M ((2:Nat))))))
                                      (Lax109476Proofs.BinaryOptimization.steps D))
                                    (Nat.mul
                                      ((12:Nat)) D.size))
                                  (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                ((48:Nat))):= @Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec
