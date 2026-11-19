-- Prove2me | solution 1 for Lax455465Proofs.RamRegionBoundedLoop.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:59:40.394577+00:00
-- url     : https://prove2.me/submissions/381ac56c-e66d-4f8c-b884-74cc482e6032

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Logic.Function.Iterate
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax455465Proofs_RamRegionCore_iteration_spec_native

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

namespace Lax455465Proofs.RamRegionCore
end Lax455465Proofs.RamRegionCore
theorem Lax455465Proofs.RamRegionCore.iteration_spec:∀ (B M H:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n)
  (length:Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold:NNRat) (p:Nat)
  (active:Finset (Fin n)) (history:List (Lax455465Proofs.RamRegionRecord.Entry n)),
  Nat.le ((1:Nat)) M→
    Nat.le (Lax455465Proofs.RegionBudget.steps p) M→
      Nat.lt
          (HAdd.hAdd
            (HMul.hMul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        Nat.lt
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) H)
                  ((2:Nat))))
              ((3:Nat)))
            B→
          Nat.lt
              (HAdd.hAdd
                (HMul.hMul
                  ((2:Nat))
                  (HMul.hMul n n))
                ((2:Nat)))
              B→
            Nat.lt
                (HAdd.hAdd
                  (HMul.hMul
                    ((2:Nat)) n)
                  ((2:Nat)))
                B→
              Nat.lt
                  (HAdd.hAdd
                    (HMul.hMul
                      ((2:Nat))
                      (HAdd.hAdd
                        (HAdd.hAdd (Lax455465Proofs.RegionBudget.steps p)
                          ((1:Nat)))
                        (HMul.hMul
                          ((2:Nat)) n)))
                    ((2:Nat)))
                  B→
                Nat.lt
                    (HAdd.hAdd
                      (HMul.hMul
                        ((4:Nat))
                        (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history))
                      ((4:Nat)))
                    B→
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold)→
                    (∀ (v:Fin n),
                        Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M)→
                      (∀ (v:Fin n),
                          Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M)→
                        (∀ (u v:Fin n),
                            Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M)→
                          (∀ (u v:Fin n),
                              Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M)→
                            (∀ (u v:Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v)))→
                              Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                Lax455465Proofs.LpInputSize.Height M
                                    (@NNRat.cast Rat Rat.instNNRatCast
                                      (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                                        (@Nat.cast NNRat
                                          (@AddMonoidWithOne.toNatCast NNRat
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                              (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                                (@Semiring.toNonAssocSemiring NNRat
                                                  (@DivisionSemiring.toSemiring NNRat
                                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                                          (Lax455465Proofs.RegionBudget.steps p))))→
                                  (∀ (root:Fin n) (i:Nat)
                                      (hi:
                                        Nat.lt i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as:List NNRat) (i:Nat) =>
                                              Nat.lt i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H)→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta))→
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed)→
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                          Nat.lt ((0:Nat))
                                              p→
                                            (∀ (u v w:Fin n),
                                                @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                  (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length v w))))→
                                              @LE.le Rat Rat.instLE
                                                  (@Lax455465Proofs.RegionRounding.metricCost n I
                                                    (@Lax455465Proofs.MetricMatrix.rational n length))
                                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                    (@Nat.cast Rat Rat.instNatCast p)
                                                    (@NNRat.cast Rat Rat.instNNRatCast seed))→
                                                Nat.le
                                                    (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history) p→
                                                  Lax808846Proofs.Reasoning.Spec B
                                                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p σ)
                                                        (And
                                                          (@Lax455465Proofs.RamRegionInvariant.Dynamic n active history
                                                            σ)
                                                          (Lax455465Proofs.RamRegionInvariant.Room n p σ)))
                                                    Lax455465Proofs.RamRegionLoop.iteration
                                                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p τ)
                                                        (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                          (@Lax455465Proofs.RamRegionCore.Output n I length seed beta
                                                            delta threshold p active history τ)))
                                                    (Lax455465Proofs.RamRegionCore.cost n p M H):= @Lax455465Proofs.RamRegionCore.iteration_spec_native

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

namespace Lax455465Proofs.RegionBudget

theorem steps_pos (p:ℕ):0 < steps p:=by unfold steps; omega

end Lax455465Proofs.RegionBudget

end

section

namespace Lax455465Proofs.RegionSearch

open RegionVolume

private theorem grid_last (k:ℕ) (delta:ℚ) (hk:0 < k):grid k delta k=delta:=by
  have hkq:(k:ℚ) ≠ 0:=by exact_mod_cast (Nat.ne_of_gt hk)
  simp [grid,hkq]

private theorem grid_nonneg (k:ℕ) (delta:ℚ) (j:ℕ) (hd:0≤ delta):
    0≤ grid k delta j:=by unfold grid; positivity

private theorem grid_le (k:ℕ) (delta:ℚ) (j:ℕ)
    (hk:0 < k) (hd:0≤ delta) (hj:j≤ k):grid k delta j≤ delta:=by
  calc
    grid k delta j≤ grid k delta k:=by
      unfold grid
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hd
    _=delta:=grid_last k delta hk

theorem candidates_bound {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (k:ℕ) (delta r:ℚ) (hk:0 < k) (hd:0≤ delta)
    (hr:r∈ candidates outDistance inDistance k delta):0≤ r∧ r≤ delta:=by
  simp only [candidates,List.mem_append,List.mem_map,List.mem_ofFn] at hr
  rcases hr with (⟨j,hj,rfl⟩ | ⟨v,rfl⟩) | ⟨v,rfl⟩
  · exact ⟨grid_nonneg k delta j hd,grid_le k delta j hk hd (by have hh:=List.mem_range.mp hj; omega)⟩
  · exact ⟨le_min hd (le_max_right _ _),min_le_left _ _⟩
  · exact ⟨le_min hd (le_max_right _ _),min_le_left _ _⟩

theorem search_radius {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool) (r:ℚ) (hd:0≤ delta)
    (hs:search capacity length outDistance inDistance seed delta p direction=some r):
    0 < r∧ r≤ delta:=by
  have hfound:0 < r∧ Good capacity length outDistance inDistance seed
      (slope (RegionBudget.steps p) delta) direction r:=by
    simpa only [decide_eq_true_eq] using List.find?_some hs
  exact ⟨hfound.1, (candidates_bound outDistance inDistance (RegionBudget.steps p) delta r
    (RegionBudget.steps_pos p) hd (List.mem_of_find?_eq_some hs)).2⟩

end Lax455465Proofs.RegionSearch

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume

def chosenBall {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (direction:ℚ→ Bool) (r:ℚ):Finset (Fin n):=
  if direction r then ball outDistance r else ball inDistance r

end Lax455465Proofs.RegionCharging

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionSelection

open RegionCharging

def eraseWeights {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n)):Fin n→ ℚ:=
  fun v => if v∈ S then 0 else weights v

theorem support_erase {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n)):
    support (eraseWeights weights S)=support weights \ S:=by
  ext v
  simp only [support,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,eraseWeights]
  split_ifs <;> simp_all

theorem support_decreases {n:ℕ} (weights:Fin n→ ℚ) (S:Finset (Fin n))
    (root:Fin n) (hroot:0 < weights root) (hmem:root∈ S):
    (support (eraseWeights weights S)).card < (support weights).card:=by
  rw [support_erase]
  apply Finset.card_lt_card
  have hsub:support weights \ S ⊆ support weights:=Finset.sdiff_subset
  exact (Finset.ssubset_iff_of_subset hsub).mpr
    ⟨root,by simp [support,hroot],by simp [hmem]⟩

theorem root_mem_chosen {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (chooseDirection:ℚ→ Bool) (r:ℚ) (root:Fin n)
    (hout:outDistance root=0) (hin:inDistance root=0) (hr:0 < r):
    root∈ chosenBall outDistance inDistance chooseDirection r:=by
  unfold chosenBall
  split_ifs <;> simp [ball,hout,hin,hr]

theorem search_progress {n:ℕ} (capacity length:RegionVolume.Matrix n)
    (weights outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (root:Fin n) (r:ℚ)
    (hroot:0 < weights root) (hout:outDistance root=0) (hin:inDistance root=0)
    (hd:0≤ delta)
    (hs:RegionSearch.search capacity length outDistance inDistance seed delta p
      (direction weights outDistance inDistance)=some r):
    (support (eraseWeights weights
      (chosenBall outDistance inDistance (direction weights outDistance inDistance) r))).card <
      (support weights).card:=by
  exact support_decreases weights _ root hroot
    (root_mem_chosen outDistance inDistance _ r root hout hin
      (RegionSearch.search_radius capacity length outDistance inDistance seed delta p _ r hd hs).1)

end Lax455465Proofs.RegionSelection

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

theorem weights_remove {n:ℕ} (I:RationalInstance n) (active S:Finset (Fin n)):
    weights I (active \ S)=eraseWeights (weights I active) S:=by
  funext v
  simp only [weights,eraseWeights,Finset.mem_sdiff]
  split_ifs <;> (try simp_all)

end Lax455465Proofs.RegionLoop

end

section

namespace Lax455465Proofs.RamRegionContext

open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def sourceVariables:List String:= ["metric.n","metric.n2","region.radius.n","region.radius.d",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d"]
def arrays:List String:= ["region.weights","region.capacities","metric.old","region.out","region.in"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {q:Query n} (h:Input q σ)
    (hx:∀ x∈ sourceVariables,x∉ cmd.wvars) (ha:∀ a∈ arrays,a∉ cmd.warrs):Input q τ:=by
  refine ⟨(hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.nValue,
    (hr.frame_var _ (hx _ (by simp [sourceVariables]))).trans h.n2Value,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "region.radius.n" (hx _ (by simp [sourceVariables])),hr.frame_var "region.radius.d" (hx _ (by simp [sourceVariables]))] using h.radiusData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.seed.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.seed.d" (hx _ (by simp [sourceVariables]))] using h.seedData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.slope.n" (hx _ (by simp [sourceVariables])),hr.frame_var "round.slope.d" (hx _ (by simp [sourceVariables]))] using h.betaData
  · simpa only [Prefix,hr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,hr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,hr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.inData

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem storedFrame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {name:String} {q:ℚ≥0} (h:Stored name q σ)
    (hn:name++".n"∉cmd.wvars) (hd:name++".d"∉cmd.wvars):Stored name q τ:=by
  simpa only [Stored,rr.frame_var (name++".n") hn,rr.frame_var (name++".d") hd] using h

end Lax455465Proofs.RamRoundingConstants

end

section

namespace Lax455465Proofs.RadiusData

open LpInputSize
open scoped NNRat

theorem coe_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0):
    (candidates outDistance inDistance k delta).map (fun q:ℚ≥0 => (q:ℚ)) =
      RegionSearch.candidates (fun v => (outDistance v:ℚ)) (fun v => (inDistance v:ℚ)) k delta:=by
  simp only [candidates,List.map_append,List.map_map,List.map_ofFn,RegionSearch.candidates,Function.comp_apply,NNRat.coe_min]
  congr 2
  · apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply,NNRat.coe_mul,NNRat.coe_div,NNRat.coe_natCast,RegionSearch.grid]
    ring
  · congr 1
    funext v
    simp [max_eq_left (outDistance v).coe_nonneg]
  · funext v
    simp [max_eq_left (inDistance v).coe_nonneg]

end Lax455465Proofs.RadiusData

end

section

namespace Lax455465Proofs.RadiusSearchData
open RegionQueryData
open scoped NNRat

theorem search_value {n:ℕ} (q:Query n) (delta:ℚ≥0) (p:ℕ)
    (hb:(q.beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta):
    ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).find?
      (fun r => accepted (atRadius q r))).map (fun r:ℚ≥0 => (r:ℚ)) =
      RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
        (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) q.seed delta p (direction q):=by
  unfold RegionSearch.search
  rw [← RadiusData.coe_candidates,List.find?_map]
  congr 2
  funext r
  simp only [Function.comp_def,accepted,atRadius,hb]
  rfl

end Lax455465Proofs.RadiusSearchData

end

section

namespace Lax455465Proofs.ResidualData

open Lax455465.RationalEncoding MetricMatrix LpInputSize
open scoped NNRat

theorem rational_weights {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    (fun v => (weights I active v:ℚ))=RegionLoop.weights I active:=by
  funext v
  unfold weights RegionLoop.weights
  split_ifs <;> rfl

theorem rational_capacity {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    rational (capacity I active)=RegionLoop.capacity I active:=by
  funext u v
  dsimp only [capacity,rational,RegionLoop.capacity]
  split_ifs <;> rfl

end Lax455465Proofs.ResidualData

end

section

namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

structure Input {n:ℕ} (history:List (Entry n)) (e:Entry n) (σ:Env):Prop where
  data:Prefix (words history) "region.history" σ
  position:σ.vars "history.pos"=(words history).length
  root:σ.vars "region.root"=e.root.val
  radius:Stored "region.radius" e.radius σ
  outward:σ.vars "region.outward"=(if e.outward then 1 else 0)

end Lax455465Proofs.RamRegionRecord

end

section

namespace Lax455465Proofs.RamRegionBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RegionQueryData RamRegionRecord
open scoped NNRat

structure Input {n:ℕ} (q:Query n) (threshold:ℚ≥0) (active:Finset (Fin n))
    (history:List (Entry n)) (root:Fin n) (σ:Env):Prop where
  smallInput:RamSmallRegion.Input q active history root σ
  phase:σ.vars "region.phase"=0
  thresholdData:Stored "round.largeThreshold" threshold σ
  outMass:Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) σ
  inMass:Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) σ

end Lax455465Proofs.RamRegionBranch

end

section

namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

def names:List String:= ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d",
  "round.largeThreshold.n","round.largeThreshold.d"]
def arrays:List String:= ["flow.weights","flow.capacities","metric.old"]

theorem Fixed.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {length:MetricMatrix.Matrix n} {seed beta delta threshold:ℚ≥0} {p:ℕ}
    (h:Fixed I length seed beta delta threshold p σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈arrays,a∉cmd.warrs):
    Fixed I length seed beta delta threshold p τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.thresholdData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData⟩

def dynamicNames:List String:= ["region.phase","history.pos"]
def dynamicArrays:List String:= ["region.active","region.history"]

theorem Dynamic.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {active:Finset (Fin n)} {history:List (Entry n)} (h:Dynamic active history σ)
    (hx:∀ x∈dynamicNames,x∉cmd.wvars) (ha:∀ a∈dynamicArrays,a∉cmd.warrs):Dynamic active history τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.phase,
    by simpa only [Prefix,rr.frame_arr "region.active" (ha _ (by simp [dynamicArrays]))] using h.activeData,
    by simpa only [Prefix,rr.frame_arr "region.history" (ha _ (by simp [dynamicArrays]))] using h.historyData,
    (rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.historyPosition⟩

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n p:ℕ} (h:Room n p σ):Room n p τ:=by
  intro a count hm
  rw [RamFrames.run_array_length rr a]
  exact h a count hm

end Lax455465Proofs.RamRegionInvariant

end

section

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeState
open Lax455465.RationalEncoding RegionQueryData RamRegionRecord
open scoped NNRat

theorem radius_coe {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ) (active:Finset (Fin n)) (root:Fin n)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta):
    (radius I length seed beta delta p active root).map (fun r:ℚ≥0 => (r:ℚ))=
      RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
        (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
        (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root):=by
  have h:=RadiusSearchData.search_value (RegionExecutionData.query I length active root seed beta) delta p hbeta
  dsimp only [RegionExecutionData.query,RamRegionSetup.query,RegionQueryData.direction] at h
  unfold RegionQueryData.direction at h
  simp only [ResidualData.rational_capacity,ResidualData.rational_weights] at h
  dsimp only [radius,RegionExecutionData.query,RamRegionSetup.query,RegionLoop.chooseDirection,MetricMatrix.rational] at h ⊢
  unfold MetricMatrix.rational
  exact h

theorem radius_of_search {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta:ℚ≥0) (p:ℕ) (active:Finset (Fin n)) (root:Fin n) (r:ℚ≥0)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hs:RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some (r:ℚ)):
    radius I length seed beta delta p active root=some r:=by
  have h:=radius_coe I length seed beta delta p active root hbeta
  rw [hs] at h
  cases hh:radius I length seed beta delta p active root with
  | none => simp only [hh,Option.map_none] at h; cases h
  | some r' =>
    have he:r'=r:=NNRat.coe_injective (by simpa only [hh,Option.map_some,Option.some.injEq] using h)
    simpa only [he] using hh

end Lax455465Proofs.RegionRuntimeState

end

section

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RamRegionState
open Lax808846Proofs.Imp RamVirtualState RamRegionInvariant RamRegionRecord RegionRuntimeState
open Lax455465.RationalEncoding
open scoped NNRat

theorem output_advance {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (s:State n) (σ:Env)
    (hrunning:s.status=.running) (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (houtput:RamRegionCore.Output I length seed beta delta threshold p s.active s.history σ):
    View I length seed beta (advance I length seed beta delta threshold p s) σ:=by
  cases hroot:RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
  | none =>
    simpa only [advance,hrunning,hroot,View,RamRegionCore.Output] using houtput
  | some root =>
    obtain ⟨r,hs,hb⟩:∃ r:ℚ≥0,
        RegionSearch.search (RegionLoop.capacity I s.active) (MetricMatrix.rational length)
          (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
          (RegionLoop.chooseDirection I (MetricMatrix.rational length) s.active root)=some (r:ℚ)∧
        RamRegionBranch.Output (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r)
          threshold s.active s.history root σ:=by
      simpa only [RamRegionCore.Output,hroot] using houtput
    have hr:=radius_of_search I length seed beta delta p s.active root r hbeta hs
    let q:=RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
    change RamRegionBranch.Output q threshold s.active s.history root σ at hb
    by_cases hl:RamRegionBranch.large q threshold
    · have ha:advance I length seed beta delta threshold p s=
          {s with status:=.large (RamSmallRegion.selected q root)}:=by
        simp only [advance,hrunning,hroot,hr]
        change (if RamRegionBranch.large q threshold then _ else _)=_
        rw [if_pos hl]
      rw [ha]
      change σ.vars "region.phase"=1∧ RamSmallRegion.Input q s.active s.history root σ
      simpa only [RamRegionBranch.Output,hl,if_true] using hb
    · have ha:advance I length seed beta delta threshold p s=
          {active:=s.active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational length),
            history:=s.history++[RamSmallRegion.selected q root],status:=.running}:=by
        simp only [advance,hrunning,hroot,hr]
        change (if RamRegionBranch.large q threshold then _ else _)=_
        rw [if_neg hl]
      rw [ha]
      simp only [RamRegionBranch.Output,hl,if_false] at hb
      change Dynamic (s.active \ (RamSmallRegion.selected q root).region.ball (MetricMatrix.rational length))
        (s.history++[RamSmallRegion.selected q root]) σ
      refine ⟨hb.1,?_,hb.2.2.1,by simpa using hb.2.2.2.1⟩
      simpa only [q,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query] using hb.2.2.2.2

end Lax455465Proofs.RamRegionState

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionGuard
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant
open RegionRuntimeState RamRegionState Lax455465.RationalEncoding
open scoped NNRat

def command:Com:=.ite (.eq (.var "region.phase") (.lit 0)) RamRegionLoop.iteration .skip

theorem guard_spec (B K:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (s:State n) (h2:2< B)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hbody:s.status=.running→
      Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Dynamic s.active s.history σ∧ Room n p σ)
        RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
          RamRegionCore.Output I length seed beta delta threshold p s.active s.history τ) K):
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Room n p σ∧ View I length seed beta s σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
        View I length seed beta (advance I length seed beta delta threshold p s) τ) (K+5):=by
  rintro σ ⟨hf,hr,hv⟩
  cases hs:s.status with
  | running =>
    have hd:Dynamic s.active s.history σ:=by simpa only [View,hs] using hv
    have hc:(Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hd.phase ▸ (by omega:0< B))) (evalB_lit (by omega)),hd.phase]
      rfl
    obtain ⟨τ,rr,pr⟩:=hbody hs σ ⟨hf,hd,hr⟩
    exact ⟨τ,(Run.ite_true (d:=.skip) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),pr.1,pr.2.1,
      output_advance I length seed beta delta threshold p s τ hs hbeta pr.2.2⟩
  | large e =>
    have hp:σ.vars "region.phase"=1:=(show σ.vars "region.phase"=1∧ _ from by simpa only [View,hs] using hv).1
    have hc:(Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hp ▸ (by omega:1< B))) (evalB_lit (by omega)),hp]
      rfl
    exact ⟨σ,(Run.ite_false (c:=RamRegionLoop.iteration) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hf,hr,
      by simpa only [advance,hs] using hv⟩
  | exhausted =>
    have hp:σ.vars "region.phase"=2:=(show σ.vars "region.phase"=2∧ _ from by simpa only [View,hs] using hv).1
    have hc:(Cond.eq (.var "region.phase") (.lit 0)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hp ▸ h2)) (evalB_lit (by omega)),hp]
      rfl
    exact ⟨σ,(Run.ite_false (c:=RamRegionLoop.iteration) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hf,hr,
      by simpa only [advance,hs] using hv⟩
  | failed =>
    have:False:=by simpa only [View,hs] using hv
    exact this.elim

theorem View.frameCounter {B K:ℕ} {e:Expr} {σ τ:Env}
    (rr:Run B (.assign "loop.i" e) σ τ K)
    {n:ℕ} {I:RationalInstance n} {length:MetricMatrix.Matrix n} {seed beta:ℚ≥0} {s:State n}
    (h:View I length seed beta s σ):View I length seed beta s τ:=by
  cases hs:s.status with
  | running =>
    have hd:Dynamic s.active s.history σ:=by simpa only [View,hs] using h
    simpa only [View,hs] using Dynamic.frame rr hd (by dsimp [dynamicNames,Com.wvars,Com.warrs]; decide) (by dsimp [dynamicArrays,Com.wvars,Com.warrs]; decide)
  | large entry =>
    obtain ⟨hp,hi⟩:=(show σ.vars "region.phase"=1∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I length s.active entry.root seed beta) entry.radius)
        s.active s.history entry.root σ from by simpa only [View,hs] using h)
    simp only [View,hs]
    refine ⟨(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hp,?_,?_,?_,?_,?_⟩
    · refine ⟨RamRegionContext.Input.frame rr hi.masks.input (by dsimp [RamRegionContext.sourceVariables,Com.wvars,Com.warrs]; decide)
        (by dsimp [RamRegionContext.arrays,Com.wvars,Com.warrs]; decide),?_,?_,(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.masks.directionValue⟩
      · simpa only [Prefix,rr.frame_arr "region.outMask" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.masks.outMask
      · simpa only [Prefix,rr.frame_arr "region.inMask" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.masks.inMask
    · exact (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.rootValue
    · simpa only [Prefix,rr.frame_arr "region.active" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.activeData
    · simpa only [Prefix,rr.frame_arr "region.history" (by dsimp [Com.wvars,Com.warrs]; decide)] using hi.historyData
    · exact (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hi.historyPosition
  | exhausted =>
    have hh:σ.vars "region.phase"=2∧ Prefix (RamRegionRecord.words s.history) "region.history" σ∧
        σ.vars "history.pos"=4*s.history.length∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ:=by
      simpa only [View,hs] using h
    simp only [View,hs]
    exact ⟨(rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hh.1,
      by simpa only [Prefix,rr.frame_arr "region.history" (by dsimp [Com.wvars,Com.warrs]; decide)] using hh.2.1,
      (rr.frame_var _ (by dsimp [Com.wvars,Com.warrs]; decide)).trans hh.2.2.1,
      by simpa only [Prefix,rr.frame_arr "region.active" (by dsimp [Com.wvars,Com.warrs]; decide)] using hh.2.2.2⟩
  | failed =>
    have:False:=by simpa only [View,hs] using h
    exact this.elim

end Lax455465Proofs.RamRegionGuard

end

section

set_option backward.isDefEq.respectTransparency false
namespace Lax455465Proofs.RegionRuntimeProgress
open Lax455465.RationalEncoding RegionRuntimeState
open scoped NNRat

def SupportBound {n:ℕ} (I:RationalInstance n) (p:ℕ) (s:State n):Prop:=
  s.history.length+(RegionSelection.support (RegionLoop.weights I s.active)).card≤ p

theorem advance_bound {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (s:State n)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hdiag:∀ v,length v v=0) (hbound:SupportBound I p s):
    SupportBound I p (advance I length seed beta delta threshold p s):=by
  cases hstatus:s.status with
  | large e => simpa only [advance,hstatus] using hbound
  | exhausted => simpa only [advance,hstatus] using hbound
  | failed => simpa only [advance,hstatus] using hbound
  | running =>
    cases hroot:RegionSelection.chooseRoot (RegionLoop.weights I s.active) with
    | none => simpa only [advance,hstatus,hroot,SupportBound] using hbound
    | some root =>
      cases hr:radius I length seed beta delta p s.active root with
      | none => simpa only [advance,hstatus,hroot,hr,SupportBound] using hbound
      | some r =>
        let q:=RadiusSearchData.atRadius (RegionExecutionData.query I length s.active root seed beta) r
        let e:=RamSmallRegion.selected q root
        by_cases hl:RamRegionBranch.large q threshold
        · have ha:advance I length seed beta delta threshold p s={s with status:=.large e}:=by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_pos hl]
          simpa only [ha,SupportBound] using hbound
        · have ha:advance I length seed beta delta threshold p s=
              {active:=s.active \ e.region.ball (MetricMatrix.rational length),history:=s.history++[e],status:=.running}:=by
            simp only [advance,hstatus,hroot,hr]
            change (if RamRegionBranch.large q threshold then _ else _)=_
            rw [if_neg hl]
          have hc:=radius_coe I length seed beta delta p s.active root hbeta
          rw [hr,Option.map_some] at hc
          have hrootPos:0< RegionLoop.weights I s.active root:=by
            simpa only [decide_eq_true_eq] using List.find?_some hroot
          have hball:e.region.ball (MetricMatrix.rational length)=RegionCharging.chosenBall
              (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ))
              (RegionLoop.chooseDirection I (MetricMatrix.rational length) s.active root) r:=by
            unfold e RamSmallRegion.selected RamRegionRecord.Entry.region RegionLoop.Region.ball RegionCharging.chosenBall
            simp only [q,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,
              RegionQueryData.direction,ResidualData.rational_weights,RegionLoop.chooseDirection]
            rfl
          have hprogress:(RegionSelection.support (RegionLoop.weights I (s.active \ e.region.ball (MetricMatrix.rational length)))).card<
              (RegionSelection.support (RegionLoop.weights I s.active)).card:=by
            rw [RegionLoop.weights_remove,hball]
            exact RegionSelection.search_progress (RegionLoop.capacity I s.active) (MetricMatrix.rational length)
              (RegionLoop.weights I s.active) (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ))
              seed delta p root r hrootPos
              (by rw [hdiag root]; rfl) (by rw [hdiag root]; rfl) delta.coe_nonneg hc.symm
          simp only [ha,SupportBound,List.length_append,List.length_singleton]
          unfold SupportBound at hbound
          omega

end Lax455465Proofs.RegionRuntimeProgress

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionScan
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant
open RegionRuntimeState RamRegionState RegionRuntimeProgress Lax455465.RationalEncoding
open scoped NNRat

def Invariant {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (start:State n) (σ:Env):Prop:=
  Fixed I length seed beta delta threshold p σ∧ Room n p σ∧ σ.vars "loop.i"≤ p+1∧
    σ.vars "loop.limit"=p+1∧
    View I length seed beta ((advance I length seed beta delta threshold p)^[σ.vars "loop.i"] start) σ

set_option maxHeartbeats 0 in

theorem command_spec (B K:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (start:State n) (h2:2< B) (hcount:p+1< B)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta) (hdiag:∀ v,length v v=0)
    (hbound:SupportBound I p start)
    (hbody:∀ s:State n,SupportBound I p s→ s.status=.running→
      Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Dynamic s.active s.history σ∧ Room n p σ)
        RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
          RamRegionCore.Output I length seed beta delta threshold p s.active s.history τ) K):
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Room n p σ∧
      σ.vars "loop.limit"=p+1∧ View I length seed beta start σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
        View I length seed beta ((advance I length seed beta delta threshold p)^[p+1] start) τ)
      ((K+13)*(p+1)+6):=by
  let f:=advance I length seed beta delta threshold p
  have hb:∀ i:ℕ,SupportBound I p (f^[i] start):=by
    intro i
    induction i with
    | zero => simpa using hbound
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact advance_bound I length seed beta delta threshold p _ hbeta hdiag ih
  have hstep:Spec B (fun σ => Invariant I length seed beta delta threshold p start σ∧ σ.vars "loop.i"< p+1)
      RamRegionLoop.step (fun σ τ => Invariant I length seed beta delta threshold p start τ∧
        τ.vars "loop.i"=σ.vars "loop.i"+1) (K+9):=by
    rintro σ ⟨⟨hf,hr,hi,hlim,hview⟩,hlt⟩
    let i:=σ.vars "loop.i"
    let s:=f^[i] start
    obtain ⟨ν,rg,pg⟩:=RamRegionGuard.guard_spec B K I length seed beta delta threshold p s h2 hbeta
      (hbody s (hb i)) σ ⟨hf,hr,hview⟩
    have hiν:ν.vars "loop.i"=i:=(rg.frame_var _ (by decide)).trans rfl
    have hnext:i+1< B:=by dsimp [i]; omega
    let τ:=ν.setVar "loop.i" (i+1)
    have ri:Run B (.assign "loop.i" (.add (.var "loop.i") (.lit 1))) ν τ 4:=
      Run.assign (evalB_bin (op:=.add)
        (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i< B)⟩) (evalB_lit (by omega)) hnext)
    have rr:=rg.seq ri
    refine ⟨τ,by simpa only [RamRegionLoop.step,RamRegionGuard.command] using rr,?_,by simp [τ,i]⟩
    refine ⟨Fixed.frame ri pg.1 (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame ri pg.2.1,
      by simp [τ]; dsimp [i]; omega,
      ((rg.seq ri).frame_var _ (by decide)).trans hlim,?_⟩
    have hv:=RamRegionGuard.View.frameCounter ri pg.2.2
    simpa only [τ,vars_setVar,if_true,Function.iterate_succ_apply',f,s] using hv
  have hs:=Spec.forRangeZero "loop.i" "loop.limit" (Invariant I length seed beta delta threshold p start)
    (p+1) (K+9) hcount (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) hstep
  rintro σ ⟨hf,hr,hlimit,hv⟩
  have rz:Run B (.assign "loop.i" (.lit 0)) σ (σ.setVar "loop.i" 0) 2:=Run.assign (evalB_lit (by omega))
  have hinit:Invariant I length seed beta delta threshold p start (σ.setVar "loop.i" 0):=
    ⟨Fixed.frame rz hf (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame rz hr,
      by simp,(rz.frame_var _ (by decide)).trans hlimit,
      by simpa only [vars_setVar,if_true,Function.iterate_zero,Function.id_def] using RamRegionGuard.View.frameCounter rz hv⟩
  obtain ⟨τ,rr,pr⟩:=hs σ hinit
  exact ⟨τ,by simpa only [command] using rr,pr.1.1,pr.1.2.1,
    by simpa only [pr.2] using pr.1.2.2.2.2⟩

end Lax455465Proofs.RamRegionScan

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionBoundedLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionInvariant RegionRuntimeState RamRegionState
open Lax455465.RationalEncoding
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M H:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ)
    (hM:1≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*p+4< B) (ht:LpInputSize.Height (2^H) (threshold:ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ active:Finset (Fin n), ∀ root:Fin n, ∀ i,
      ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (hdiag:∀ v,length v v=0)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hsupport:(RegionSelection.support (RegionLoop.weights I Finset.univ)).card≤ p):
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Room n p σ∧
      σ.vars "loop.limit"=p+1∧ View I length seed beta (initial n) σ)
      RamRegionScan.command (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
        View I length seed beta ((advance I length seed beta delta threshold p)^[p+1] (initial n)) τ)
      (cost n p M H):=by
  apply RamRegionScan.command_spec B (RamRegionCore.cost n p M H) I length seed beta delta threshold p (initial n)
    (by nlinarith) (by omega) hbeta hdiag
  · simpa only [RegionRuntimeProgress.SupportBound,initial,List.length_nil,Nat.zero_add] using hsupport
  · intro s hbound _
    have hhist:s.history.length≤ p:=by unfold RegionRuntimeProgress.SupportBound at hbound; omega
    exact RamRegionCore.iteration_spec B M H I length seed beta delta threshold p s.active s.history hM hk hB hquery
      hindex hvertex hradius (by change 4 * s.history.length + 4 < B; omega) ht hwn hwd hcn hcd hl hd hu (hb s.active) hbeta hseed hdelta hp htri hcost hhist

end Lax455465Proofs.RamRegionBoundedLoop

end

theorem solution:∀ (B M H:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n)
  (length:Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold:NNRat) (p:Nat),
  Nat.le ((1:Nat)) M→
    Nat.le (Lax455465Proofs.RegionBudget.steps p) M→
      Nat.lt
          (Nat.add
            (Nat.mul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        Nat.lt
            (Nat.add
              (Nat.mul
                ((2:Nat))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) H)
                  ((2:Nat))))
              ((3:Nat)))
            B→
          Nat.lt
              (Nat.add
                (Nat.mul
                  ((2:Nat))
                  (Nat.mul n n))
                ((2:Nat)))
              B→
            Nat.lt
                (Nat.add
                  (Nat.mul
                    ((2:Nat)) n)
                  ((2:Nat)))
                B→
              Nat.lt
                  (Nat.add
                    (Nat.mul
                      ((2:Nat))
                      (Nat.add
                        (Nat.add (Lax455465Proofs.RegionBudget.steps p)
                          ((1:Nat)))
                        (Nat.mul
                          ((2:Nat)) n)))
                    ((2:Nat)))
                  B→
                Nat.lt
                    (Nat.add
                      (Nat.mul
                        ((4:Nat)) p)
                      ((4:Nat)))
                    B→
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold)→
                    (∀ (v:Fin n),
                        Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M)→
                      (∀ (v:Fin n),
                          Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M)→
                        (∀ (u v:Fin n),
                            Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M)→
                          (∀ (u v:Fin n),
                              Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M)→
                            (∀ (u v:Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v)))→
                              Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                Lax455465Proofs.LpInputSize.Height M
                                    (@NNRat.cast Rat Rat.instNNRatCast
                                      (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                                        (@Nat.cast NNRat
                                          (@AddMonoidWithOne.toNatCast NNRat
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                              (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                                (@Semiring.toNonAssocSemiring NNRat
                                                  (@DivisionSemiring.toSemiring NNRat
                                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                                          (Lax455465Proofs.RegionBudget.steps p))))→
                                  (∀ (active:Finset (Fin n)) (root:Fin n) (i:Nat)
                                      (hi:
                                        Nat.lt i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as:List NNRat) (i:Nat) =>
                                              Nat.lt i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H)→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta))→
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed)→
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                          Nat.lt ((0:Nat))
                                              p→
                                            (∀ (v:Fin n),
                                                @Eq NNRat (length v v)
                                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                                    (@Zero.toOfNat0 NNRat
                                                      (@MulZeroClass.toZero NNRat
                                                        (@instMulZeroClassOfSemiring NNRat
                                                          (@DivisionSemiring.toSemiring NNRat
                                                            (@Semifield.toDivisionSemiring NNRat
                                                              NNRat.instSemifield)))))))→
                                              (∀ (u v w:Fin n),
                                                  @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                    (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length v w))))→
                                                @LE.le Rat Rat.instLE
                                                    (@Lax455465Proofs.RegionRounding.metricCost n I
                                                      (@Lax455465Proofs.MetricMatrix.rational n length))
                                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                      (@Nat.cast Rat Rat.instNatCast p)
                                                      (@NNRat.cast Rat Rat.instNNRatCast seed))→
                                                  Nat.le
                                                      (@Finset.card (Fin n)
                                                        (@Lax455465Proofs.RegionSelection.support n
                                                          (@Lax455465Proofs.RegionLoop.weights n I
                                                            (@Finset.univ (Fin n) (Fin.fintype n)))))
                                                      p→
                                                    Lax808846Proofs.Reasoning.Spec B
                                                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p σ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p σ)
                                                            (And
                                                              (@Eq Nat (σ.vars "loop.limit")
                                                                (Nat.add p
                                                                  ((1:Nat))))
                                                              (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n) σ))))
                                                      Lax455465Proofs.RamRegionScan.command
                                                      (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p τ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                            (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                              (@Nat.iterate (Lax455465Proofs.RegionRuntimeState.State n)
                                                                (@Lax455465Proofs.RegionRuntimeState.advance n I length
                                                                  seed beta delta threshold p)
                                                                (Nat.add p
                                                                  ((1:Nat)))
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n))
                                                              τ)))
                                                      (Lax455465Proofs.RamRegionBoundedLoop.cost n p M H):= @Lax455465Proofs.RamRegionBoundedLoop.command_spec
