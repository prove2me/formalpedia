-- Prove2me | solution 1 for Lax263307Proofs.NativeUnweightedExecution.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:51.832712+00:00
-- url     : https://prove2.me/submissions/b4c4ce9b-12c1-4340-b8ab-7b3535cbaaa1

import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax263307Proofs_NativeCoreExecution_command_spec
import Theorems.Thm_Lax263307Proofs_NativeSelectedRounds_rounds_native

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

namespace Lax263307Proofs.NativeSelectedRounds
end Lax263307Proofs.NativeSelectedRounds
theorem Lax263307Proofs.NativeSelectedRounds.rounds:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} (p:Lax263307Proofs.NativeSelectedLP.Program lp)
      (q:Lax263307Proofs.NativeSelectedNear.Program flow) (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp p) cfg.lp→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp p) cfg.lpWidth→
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow q) cfg.flow→
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow q) cfg.flowWidth→
              Lax263307Proofs.NativeEncodedLP.Encoded lp→
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
                  Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b→
                    LT.lt ((0:Nat)) cfg.K→
                      LT.lt ((0:Nat)) cfg.b→
                        ∀ {n:Nat} (G:SimpleGraph (Fin n))
                          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
                          (D k fuel S v c R w rootN capacity childSteps childTime:Nat) (extent:String→ Nat)
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
                                  Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c→
                                    @Lax263307Proofs.NativeSelectedRounds.Bounds lp flow cfg p q n G inst D k fuel S v c
                                        R w extent front→
                                      @Lax263307Proofs.NativeRecursiveSetup.Rounds n
                                        (Lax263307Proofs.NativeSelectedRounds.level cfg n D) D k
                                        (Lax263307.AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b
                                        (Lax263307.AlgorithmParameters.load cfg.b n D)
                                        (Lax263307Proofs.NativeSelectedRounds.F cfg n D) fuel S v
                                        (Lax263307Proofs.NativeSelectedRounds.limit cfg n D) w
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (HMul.hMul
                                            ((100:Nat))
                                            (HAdd.hAdd R
                                              ((1:Nat)))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (HAdd.hAdd
                                            (HMul.hMul
                                              ((2:Nat))
                                              (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                            ((1:Nat))))
                                        (@HPow.hPow Nat Nat Nat
                                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                          ((2:Nat))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (HMul.hMul
                                          ((2:Nat))
                                          (@Lax263307Proofs.NativeSelectedRounds.H lp p R))
                                        (HAdd.hAdd R
                                          ((1:Nat)))
                                        (@Lax263307Proofs.NativeSelectedRounds.space lp flow cfg p q n D k R)
                                        (@Lax263307Proofs.NativeSelectedLP.oracleTime lp p R)
                                        (@Lax263307Proofs.NativeSelectedLP.callCost lp p R)
                                        (@Lax263307Proofs.NativeSelectedRounds.flowTime lp flow cfg p q n D k R)
                                        childSteps childTime c
                                        (Lax263307Proofs.NativeOraclePrecision.roundedHeight
                                          (@Lax263307Proofs.NativeSelectedLP.Program.width lp p) R)
                                        (HAdd.hAdd
                                          (@Lax263307Proofs.NativeSelectedRounds.oracleLocal lp flow cfg p q n D k R S)
                                          (HMul.hMul
                                            (HAdd.hAdd n
                                              ((1:Nat)))
                                            childTime))
                                        (@Lax263307Proofs.NativeSelectedRounds.roundCost lp cfg p c R) cfg G inst lp
                                        flow extent front
                                        (@Lax263307Proofs.NativeNodeExecution.child n cfg lp flow D fuel G inst)
                                        (Lax263307Proofs.NativeRecursiveDomain.eligible C rootN
                                          (HAdd.hAdd
                                            (HMul.hMul S
                                              (@List.length String (Lax263307Proofs.NativeCoreMachine.frameArrays cfg)))
                                            (@List.length String (Lax263307Proofs.NativeCoreMachine.frameScalars cfg)))
                                          capacity):= @Lax263307Proofs.NativeSelectedRounds.rounds_native

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

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_le_twice_exponent (L n:ℕ) (hn:n≤ 2 ^ L):depth n≤ 2 * L:=by
  induction L generalizing n with
  | zero =>
    have:n≤ 1:=by simpa using hn
    simp [depth,this]
  | succ L ih =>
    by_cases hn₁:n≤ 1
    · simp [depth,hn₁]
    · rw [depth.eq_def n,if_neg hn₁]
      by_cases ha:2 * n / 3≤ 1
      · rw [depth.eq_def (2 * n / 3),if_pos ha]
        omega
      · rw [depth.eq_def (2 * n / 3),if_neg ha]
        have hb:2 * (2 * n / 3) / 3≤ 2 ^ L:=by
          rw [pow_succ] at hn
          omega
        have:=ih _ hb
        omega

theorem logarithmic_bound (n:ℕ):depth n≤ 2 * (Nat.log2 n + 1):=by
  apply depth_le_twice_exponent
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

end Lax263307Proofs.RecursionDepth

end

section

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

theorem candidate_complete (n r:ℕ) (A:Finset (Fin n)):
    A∈ candidates n r↔ A.card≤ r:=by
  constructor
  · intro h
    obtain ⟨j,hj,hm⟩:=List.mem_flatMap.mp h
    obtain ⟨l,hl,rfl⟩:=List.mem_map.mp hm
    have hsub:=(List.mem_sublistsLen.mp hl).1
    have hlen:=(List.mem_sublistsLen.mp hl).2
    have hnd:=hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd,hlen]
    have:=List.mem_range.mp hj
    omega
  · intro hA
    let l:=(List.finRange n).filter fun v => decide (v∈ A)
    have hsub:List.Sublist l (List.finRange n):=List.filter_sublist
    have hnd:l.Nodup:=hsub.nodup (List.nodup_finRange n)
    have heq:l.toFinset=A:=by ext v; simp [l]
    have hlen:l.length=A.card:=by rw [← List.toFinset_card_of_nodup hnd,heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card,List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l,List.mem_sublistsLen.mpr ⟨hsub,hlen⟩,heq⟩

end Lax263307Proofs.RationalConditioning

end

section

namespace Lax263307Proofs.CoordinateCatalog

open Lax263307.LinearRelaxation Lax263307.RationalConditioning Lax263307.CoordinateCatalog

theorem catalog_complete (n r:ℕ) (A:Coordinate n r):A∈ catalog n r:=by
  have hmem:A.val∈ sets n r:=
    List.mem_dedup.mpr ((Lax263307Proofs.RationalConditioning.candidate_complete n (r + 2) A.val).mpr A.property)
  apply List.mem_map.mpr
  exact ⟨⟨A.val,hmem⟩,List.mem_attach _ _,Subtype.ext rfl⟩

theorem catalog_two (n r:ℕ) (positive:0 < n):2≤ (catalog n r).length:=by
  let v:Fin n:= ⟨0,positive⟩
  let A:Coordinate n r:= ⟨∅,by simp⟩
  let B:Coordinate n r:= ⟨{v},by simp⟩
  have hne:A ≠ B:=by
    intro h
    have heq:(∅:Finset (Fin n))={v}:=congrArg Subtype.val h
    have hv:v∈ (∅:Finset (Fin n)):=heq.symm ▸ Finset.mem_singleton_self v
    exact Finset.notMem_empty v hv
  have hsub:({A,B}:Finset (Coordinate n r)) ⊆ (catalog n r).toFinset:=by
    intro C hC
    simp only [Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r A)
    · exact List.mem_toFinset.mpr (Lax263307Proofs.CoordinateCatalog.catalog_complete n r B)
  have hcard:=Finset.card_le_card hsub
  have hpair:({A,B}:Finset (Coordinate n r)).card=2:=by simp [hne]
  rw [hpair] at hcard
  exact hcard.trans (List.toFinset_card_le _)

end Lax263307Proofs.CoordinateCatalog

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

@[simp] theorem Com.warrs_skip:Com.skip.warrs=[]:=by simp [Com.warrs]

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

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem variable_frame (coefficients:List ℕ) (x:String) (hx:x ≠ "poly.value"):
    x∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars,hx]
  | cons a rest ih => simp [command,Com.wvars,ih,hx]

theorem arrays_frame (coefficients:List ℕ):(command coefficients).warrs=[]:=by
  induction coefficients with
  | nil => simp [command,Com.warrs]
  | cons a rest ih => simp [command,Com.warrs,ih]

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

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeExhaustive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307.ExhaustiveTargets

theorem candidates_length (n k:ℕ):(candidates n k).length=n.choose k:=by
  simp [candidates,List.length_sublistsLen]

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

theorem rows_words (n r:ℕ):rows n (r+3)=Lax263307.NativeCatalog.words n r:=rows_exact n r

theorem rows_positive (n R:ℕ):1≤(rows n (R+1)).length:=by
  have h:=rows_length_mono n (show 1≤ R+1 by omega)
  have h1:(rows n 1).length=1:=by
    rw [show 1=0+1 from rfl,rows_length_step,rows_zero]
    simp
  simpa only [h1] using h

open Lax109476Proofs

end Lax263307Proofs.NativeCatalog

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

theorem entries_length (kind:Kind) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r:ℕ):
    (entries kind G k r).length=rowCount kind n r*dimension n r:=by
  simp [entries,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem dimension_positive (n r:ℕ):0< dimension n r:=by
  have h:=NativeCatalog.rows_positive n (r+2)
  change 1≤(NativeCatalog.rows n (r+3)).length at h
  rw [NativeCatalog.rows_words] at h
  simpa only [Lax263307.NativeCatalog.words,List.length_map,Nat.succ_le_iff] using h

open NativeCatalogMetadata NativeMomentProduce

end Lax263307Proofs.NativeMomentFamily

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce

def entries (N zeros:ℕ):List ℚ:= [1,-1]++List.replicate N 1++List.replicate zeros 0

theorem entries_length (N zeros:ℕ):(entries N zeros).length=2+N+zeros:=by simp [entries]; omega

def size (n r:ℕ):ℕ:=2+dimension n r+dimension n r*(n+4)

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

end Lax263307Proofs.NativeMomentInput

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodeParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.AlgorithmParameters

theorem floor_eq (a K b n D:ℕ):floorDenominator a K b n D=2*n*level a K b n D:=by
  unfold floorDenominator level
  ring

end Lax263307Proofs.NativeNodeParameters

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNodePrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters

theorem actual_radius (a K b n D:ℕ):
    radius n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=radiusDenominator a K b n D:=by
  unfold radius radiusDenominator
  ring

theorem actual_precision (a K b n D:ℕ):
    prec n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=precision a K b n D:=by
  rw [prec,actual_radius]
  rfl

theorem actual_iterations (a K b n D:ℕ):
    count n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=iterations a K b n D:=by
  rw [count,actual_precision]
  rfl

end Lax263307Proofs.NativeNodePrecision

end

section

namespace Lax263307Proofs.NativeOracleFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs

theorem instruction_array (i:Lax808846.Ram.Instr) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.instruction i).warrs:=by
  cases i <;> simp_all [RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.warrs]

theorem dispatch_array (p:Lax808846.Ram.Program) (offset:ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output"]):
    a∉ (RamVirtualProgram.dispatch p offset).warrs:=by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or] using
      And.intro (instruction_array i a ha) (ih (offset+1))

theorem command_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (a:String)
    (ha:a∉ ["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉ (NativeOracleCalls.command p coeff).warrs:=by
  have hm:a∉ ["vm.addresses","vm.values","vm.output"]:=by simp_all
  have hd:=dispatch_array p 0 a hm
  simp_all [NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamPolynomial.arrays_frame,RamLpInputFrame.command,RamLpInputFrame.step,
    RamWordBuffer.append,RamVirtualProgram.execute,RamWordOps.modulus,
    RamVirtualProgram.initCommand,Com.warrs]

end Lax263307Proofs.NativeOracleFrame

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeConditioningResources

open Lax263307 RationalConditioning NativeSignedArithmetic

theorem test_polynomial (k p D M H R:ℕ) (hk:k≤ R) (hp:p≤ R) (hD:D≤ R)
    (hM:M≤ R) (hH:H≤ R) (hR:1≤ R):testBound k p D M H≤32*R^5:=by
  have hmono:testBound k p D M H≤ NativeConditioningTest.resource R R R R R R R:=by
    dsimp [testBound,NativeConditioningTest.resource]
    gcongr
  have h0:1≤ R^5:=one_le_pow₀ hR
  have h1:R≤ R^5:=by simpa using (pow_le_pow_right₀ hR (by omega:1≤5))
  have h2:R^2≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have h3:R^3≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have h4:R^4≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have he:NativeConditioningTest.resource R R R R R R R=3+9*R+4*R^2+3*R^3+3*R^4+2*R^5:=by
    dsimp [NativeConditioningTest.resource]
    ring
  rw [he] at hmono
  nlinarith

end Lax263307Proofs.NativeConditioningResources

end

section

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeOracleScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax455465Proofs

def reserved:List String:= ["frame.i","lookup.address","lookup.i","lookup.result","lp.position","lp.word","poly.argument","poly.value","put.address","put.value","size.count","size.i","size.total","size.value","vm.addresses","vm.count","vm.cursor","vm.input","vm.inputLength","vm.left","vm.modulus","vm.output","vm.outputLength","vm.pc","vm.result","vm.right","vm.running","vm.target","vm.values","vm.width"]

theorem instruction_variable (i:Lax808846.Ram.Instr) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.instruction i).wvars:=by
  cases i <;> simp_all [reserved,RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars]

theorem dispatch_variable (p:Lax808846.Ram.Program) (offset:ℕ) (x:String) (hx:x∉reserved):
    x∉(RamVirtualProgram.dispatch p offset).wvars:=by
  induction p generalizing offset with
  | nil => simp_all [reserved,RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or] using
      And.intro (instruction_variable i x hx) (ih (offset+1))

theorem command_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (x:String) (hx:x∉reserved):
    x∉(NativeOracleCalls.command p coeff).wvars:=by
  have hd:=dispatch_variable p 0 x hx
  have hp:=RamPolynomial.variable_frame coeff x (by simp_all [reserved])
  simp_all [reserved,NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,
    RamVirtualProgram.execute,RamWordOps.modulus,RamVirtualProgram.initCommand,Com.wvars]

end Lax263307Proofs.NativeOracleScalars

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

namespace Lax263307Proofs.NativeSeparatorContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding
open scoped NNRat

theorem callback_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hp:s∉NativeFlowPrepare.command.wvars) (hi:s∉NativeSplitInput.command.wvars)
    (ho:s∉NativeOracleScalars.reserved) (hd:s∉NativeFlowCut.decodeCommand.wvars):
    s∉(callback p coeff).wvars:=by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.wvars,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleScalars.command_variable p coeff s ho)) hd)

theorem callback_array (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hp:s∉NativeFlowPrepare.command.warrs) (hi:s∉NativeSplitInput.command.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"]) (hd:s∉NativeFlowCut.decodeCommand.warrs):
    s∉(callback p coeff).warrs:=by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.warrs,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleFrame.command_array p coeff s ho)) hd)

end Lax263307Proofs.NativeSeparatorContext

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

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeUniformFlow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeFlowQueryResources NativeUniformWordGuards
open scoped NNRat

theorem cost_mono (r n s S t T:ℕ) (p:Lax808846.Ram.Program) (coeff:List ℕ)
    (hr:r≤ n) (hs:s≤ S) (ht:t≤ T):NativeSplitOracle.cost r p coeff t s≤ NativeSplitOracle.cost n p coeff T S:=by
  have hlen:NativeSplitInput.wordLength r≤ NativeSplitInput.wordLength n:=by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hr,Nat.mul_le_mul hr hr]
  dsimp only [NativeSplitOracle.cost]
  gcongr

end Lax263307Proofs.NativeUniformFlow

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

theorem array_frame (names:List String) (a:String) (ha:a≠"recursion.frames"):a∉(save names).warrs:=by
  induction names with
  | nil => simp [save,Com.warrs]
  | cons b bs ih => simp [save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.warrs,ha,ih]

end Lax263307Proofs.NativeFrameBuffers

end

section

namespace Lax263307Proofs.NativeFrameBufferRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem array_frame (names:List String) (a:String) (ha:a∉names):a∉(command names).warrs:=by
  induction names with
  | nil => simp [command,Com.warrs]
  | cons b bs ih =>
    simp only [List.mem_cons,not_or] at ha
    simp [command,NativeBlockRestore.command,NativeBlockRestore.setup,NativeSlice.command,
      NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.warrs,ha.1,ih ha.2]

end Lax263307Proofs.NativeFrameBufferRestore

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

namespace Lax263307Proofs.NativeFrameRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem variable_frame (names:List String) (s:String) (hs:s∉names) (hr:s≠"stack.read.i"):
    s∉(command names).wvars:=by
  induction names with
  | nil => simp [command,Com.wvars]
  | cons t ts ih => simp only [List.mem_cons,not_or] at hs; simp [command,step,Com.wvars,hs.1,hr,ih hs.2]

end Lax263307Proofs.NativeFrameRestore

end

section

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem scalars_array (names:List String) (a:String):a∉(NativeFrameRestore.command names).warrs:=by
  induction names with
  | nil => simp [NativeFrameRestore.command,Com.warrs]
  | cons s ss ih => simp [NativeFrameRestore.command,NativeFrameRestore.step,Com.warrs,ih]

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

theorem save_array (arrays scalars:List String) (a:String) (ha:a≠"recursion.frames"):
    a∉(NativeRecursionFrame.save arrays scalars).warrs:=by
  have hs:a∉(NativeFrameScalars.save scalars).warrs:=by
    induction scalars with
    | nil => simp [NativeFrameScalars.save,Com.warrs]
    | cons s ss ih => simp [NativeFrameScalars.save,RamWordBuffer.append,Com.warrs,ha,ih]
  simpa only [NativeRecursionFrame.save,Com.warrs,List.mem_append,not_or] using
    And.intro (NativeFrameBuffers.array_frame arrays a ha) hs

end Lax263307Proofs.NativeChildCall

end

section

namespace Lax263307Proofs.NativeStackReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def bufferScratch:List String:=
  ["stack.copy.length","fill.length","slice.start","fill.value","fill.i","stack.read.i"]

theorem buffers_variable (arrays:List String) (s:String) (hs:s∉bufferScratch):
    s∉(NativeFrameBufferRestore.command arrays).wvars:=by
  simp only [bufferScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
  induction arrays with
  | nil => simp [NativeFrameBufferRestore.command,Com.wvars]
  | cons a as ih =>
    simp [NativeFrameBufferRestore.command,NativeBlockRestore.command,NativeBlockRestore.setup,
      NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,
      RamWordBuffer.append,Com.wvars,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2,ih]

theorem restore_variable (arrays scalars:List String) (s:String)
    (hs:s∉bufferScratch) (hn:s∉scalars):s∉(NativeRecursionFrame.restore arrays scalars).wvars:=by
  have hr:s≠"stack.read.i" :=fun h => hs (by simp [bufferScratch,h])
  simpa only [NativeRecursionFrame.restore,Com.wvars,List.mem_append,not_or] using
    And.intro (buffers_variable arrays s hs) (NativeFrameRestore.variable_frame scalars s hn hr)

end Lax263307Proofs.NativeStackReturn

end

section

namespace Lax263307Proofs.NativeRawFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem command_variable (p:Lax808846.Ram.Program) (s:String)
    (hpre:s∉NativeRawOracle.prepare.wvars) (hvm:s∉NativeOracleScalars.reserved):
    s∉(NativeRawOracle.command p).wvars:=by
  have hv:=NativeOracleScalars.command_variable p [] s hvm
  simp only [NativeOracleCalls.command,Com.wvars,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.wvars,List.mem_append,not_or] using And.intro hpre hv.2

theorem array (p:Lax808846.Ram.Program) (a:String)
    (hpre:a∉NativeRawOracle.prepare.warrs)
    (hvm:a∉["vm.addresses","vm.values","vm.output","vm.input"]):
    a∉(NativeRawOracle.command p).warrs:=by
  have hv:=NativeOracleFrame.command_array p [] a hvm
  simp only [NativeOracleCalls.command,Com.warrs,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.warrs,List.mem_append,not_or] using And.intro hpre hv.2

end Lax263307Proofs.NativeRawFrame

end

section

namespace Lax263307Proofs.NativeRoundedControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch Matrix

theorem update_variable (p:Lax808846.Ram.Program) (s:String)
    (hq:s∉NativeRoundedQuery.command.wvars) (hpre:s∉NativeRawOracle.prepare.wvars)
    (hvm:s∉NativeOracleScalars.reserved) (hs:s∉NativeRoundedState.command.wvars):
    s∉(NativeRoundedUpdate.command p).wvars:=by
  simpa only [NativeRoundedUpdate.command,Com.wvars,List.mem_append,not_or] using
    And.intro hq (And.intro (NativeRawFrame.command_variable p s hpre hvm) hs)

end Lax263307Proofs.NativeRoundedControl

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

namespace Lax263307Proofs.NativeCoreMachine

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem scalar_saved (cfg:Config) (s:String) (c:Com)
    (hc:c∈cases cfg [] []) (hs:s∈c.wvars) (he:s∉excludedScalars):s∈frameScalars cfg:=by
  simp only [frameScalars,List.mem_filter,List.mem_dedup,decide_eq_true_eq]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,hs⟩,he⟩

theorem phase_saved (cfg:Config):"machine.phase"∈frameScalars cfg:=by
  exact scalar_saved cfg _ rootTarget (by simp [cases])
    (by simp [rootTarget,emptyRoot,go,Com.wvars]) (by decide)

end Lax263307Proofs.NativeCoreMachine

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCoreFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine NativeMachineSegment

theorem array_saved (cfg:Config) (a:String) (c:Com)
    (hc:c∈cases cfg [] []) (ha:a∈c.warrs) (he:a≠"recursion.frames"):a∈frameArrays cfg:=by
  simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,ha⟩,he⟩

theorem scratch_covered (cfg:Config) (s:String) (hs:s∈NativeStackReturn.bufferScratch):
    s∈frameScalars cfg∨ s∈excludedScalars:=by
  have hprep:∀ s∈["fill.length","slice.start","fill.value","fill.i"],
      s∈NativeProjectionPrepare.command.wvars:=by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> decide
  have hsave (s:String) (hs:s∈["fill.length","slice.start","fill.value","fill.i"])
      (he:s∉excludedScalars):s∈frameScalars cfg:=by
    apply scalar_saved cfg s
      (.seq NativeProjectionPrepare.command (.seq (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (go 5)))
    · simp [cases]
    · exact List.mem_append_left _ (hprep s hs)
    · exact he
  simp only [NativeStackReturn.bufferScratch,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr (by decide)
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inr (by decide)

theorem scalar_unwritten (cfg:Config) (s:String) (hs:s∉frameScalars cfg)
    (he:s∉excludedScalars):∀ c∈phases cfg,s∉c.wvars:=by
  have hb (c:Com) (hc:c∈cases cfg [] []):s∉c.wvars:=
    fun hw => hs (scalar_saved cfg s c hc hw he)
  have hsave:s∉(NativeRecursionFrame.save (frameArrays cfg) (frameScalars cfg)).wvars:=by
    apply NativeChildCall.save_variable
    intro h
    apply he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> decide
  have hrestore:s∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).wvars:=
    NativeStackReturn.restore_variable _ _ s
      (fun h => (scratch_covered cfg s h).elim hs he) hs
  have hc:=hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht:=hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.wvars,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.wvars,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.wvars,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

theorem array_unwritten (cfg:Config) (a:String) (ha:a∉frameArrays cfg)
    (he:a≠"recursion.frames"):∀ c∈phases cfg,a∉c.warrs:=by
  have hb (c:Com) (hc:c∈cases cfg [] []):a∉c.warrs:=
    fun hw => ha (array_saved cfg a c hc hw he)
  have hsave:=NativeChildCall.save_array (frameArrays cfg) (frameScalars cfg) a he
  have hrestore:a∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).warrs:=by
    simpa only [NativeRecursionFrame.restore,Com.warrs,List.mem_append,not_or] using
      And.intro (NativeFrameBufferRestore.array_frame _ a ha) (NativeRecursionFrame.scalars_array _ a)
  have hc:=hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht:=hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.warrs,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.warrs,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.warrs,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

end Lax263307Proofs.NativeCoreFrame

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

namespace Lax263307Proofs.NativeProjectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic

theorem oracle_variable (p:Lax808846.Ram.Program) (coeff:List ℕ) (s:String)
    (hd:s∉NativeDistanceInput.command.wvars) (ho:s∉NativeOracleScalars.reserved)
    (ht:s∉NativeProjectionTolerance.command.wvars) (hr:s∉NativeProjectionResult.command.wvars):
    s∉(NativeProjectionOracle.command p coeff).wvars:=by
  simpa only [NativeProjectionOracle.command,NativeDistanceOracle.command,Com.wvars,List.mem_append,not_or]
    using And.intro (And.intro hd (NativeOracleScalars.command_variable p coeff s ho)) (And.intro ht hr)

end Lax263307Proofs.NativeProjectionTrace

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

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

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

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem separator_variable (cfg:Config) (s:String)
    (hf:s∉NativeFullSetMask.command.wvars)
    (ht:s∉NativeCutTest.command.wvars) (hr:s∉NativeCutRecords.command.wvars)
    (hi:s∉["separator.i","separator.count","separator.position","separator.value"])
    (hc:s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).wvars)
    (hp:s∉NativeCutPieces.command.wvars) (he:s∉(NativeComponentControl.start 9).wvars):
    s∉((phases cfg)[8]'(by change 8<16; decide)).wvars:=by
  simpa only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or] using
    (show s∉(Com.seq (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
      (NativeComponentControl.start 9)).wvars from by
        simp only [NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
          NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or]
        simp_all)

theorem separator_array (cfg:Config) (s:String)
    (hf:s∉NativeFullSetMask.command.warrs)
    (ht:s∉NativeCutTest.command.warrs) (hr:s∉NativeCutRecords.command.warrs)
    (hc:s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).warrs)
    (hp:s∉NativeCutPieces.command.warrs):
    s∉((phases cfg)[8]'(by change 8<16; decide)).warrs:=by
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,NativeComponentControl.start,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

end Lax263307Proofs.NativeNearExecution

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem projection_variable (cfg:Config) (s:String)
    (hp:s∉NativeProjectionPrepare.command.wvars)
    (hd:s∉NativeDistanceInput.command.wvars) (ho:s∉NativeOracleScalars.reserved)
    (ht:s∉NativeProjectionTolerance.command.wvars) (hr:s∉NativeProjectionResult.command.wvars)
    (hs:s≠"machine.phase"):
    s∉((phases cfg)[4]'(by change 4<16; decide)).wvars:=by
  have hcall:=NativeProjectionTrace.oracle_variable cfg.lp cfg.lpWidth s hd ho ht hr
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    Com.wvars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem projection_array (cfg:Config) (s:String)
    (hp:s∉NativeProjectionPrepare.command.warrs)
    (hd:s∉NativeDistanceInput.command.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (ht:s∉NativeProjectionTolerance.command.warrs) (hr:s∉NativeProjectionResult.command.warrs):
    s∉((phases cfg)[4]'(by change 4<16; decide)).warrs:=by
  have hcall:=NativeOracleFrame.command_array cfg.lp cfg.lpWidth s ho
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    NativeProjectionOracle.command,NativeDistanceOracle.command,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true]

end Lax263307Proofs.NativeOracleExecution

end

section

namespace Lax263307Proofs.NativeProjectionQueryBounds

open Lax263307 MomentLP
open NativeSignedArithmetic Lax109476.RationalEncoding

theorem polynomial_bound (R:ℕ):queryBound R≤1000000*(R+1)^6:=by
  let S:=R+1
  have hS:1≤ S:=by dsimp [S]; omega
  have hR:R≤ S:=by dsimp [S]; omega
  have h12:S≤ S^2:=le_self_pow hS (by omega)
  have h13:S≤ S^3:=le_self_pow hS (by omega)
  have h23:S^2≤ S^3:=Nat.pow_le_pow_right hS (by omega)
  have h03:1≤ S^3:=Nat.one_le_pow _ _ hS
  have hc:100*(4*R+2)^3≤6400*S^3:=by
    calc
      _≤100*(4*S)^3:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S]; omega) _)
      _=_:=by ring
  have hheight:rootHeight R≤7000*S^3:=by
    dsimp [rootHeight,scaleHeight]
    change 100*(4*R+2)^3+10+2*(80*S+4*R+1)+1≤7000*S^3
    nlinarith only [hc,hR,h13,h03]
  have hrows:rootRows R+2*R≤8*S^2:=by
    change 6*S^2+2*R≤8*S^2
    nlinarith only [hR,h12]
  have hprod:(rootRows R+2*R)*S≤8*S^3:=by
    simpa only [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_right S hrows
  have hwords:NativeDistanceData.wordLength (rootRows R) R≤60*S^3:=by
    have hexpr:2+3*((rootRows R+2*R)*S+(rootRows R+2*R)+S)≤60*S^3:=by
      nlinarith only [hprod,hrows,h23,h13,h03]
    simpa only [NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns,S,Nat.two_mul] using hexpr
  have hfactor:rootHeight R+rootRows R+2*R+4≤8000*S^3:=by
    nlinarith only [hheight,hrows,h23,h03]
  calc
    queryBound R≤(60*S^3)*(8000*S^3):=Nat.mul_le_mul hwords hfactor
    _=480000*S^6:=by ring
    _≤1000000*S^6:=Nat.mul_le_mul_right _ (by decide)

end Lax263307Proofs.NativeProjectionQueryBounds

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeProjectionResources

open Lax263307 Lax109476.RationalEncoding

def buffers:List String:= ["lp.input","lp.word","projection.center","projection.tolerance",
  "vm.addresses","vm.values","vm.output","cut.source","round.normal"]

theorem tolerance_guard (n D F R:ℕ) (hn:n≤ R) (hD:D≤ R) (hF:F≤ R):
    NativeNodeTolerance.guard n D F≤1000*(R+1)^5:=by
  have hs:NativeNodeTolerance.guard n D F≤ NativeNodeTolerance.guard R R R:=by
    dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
    gcongr
  apply hs.trans
  dsimp only [NativeNodeTolerance.guard,NativeNodeTolerance.denominator]
  nlinarith only [Nat.zero_le (R^5),Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]

theorem bounds {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k r F R w T:ℕ) (extent:String→ ℕ)
    (hn:0< n) (hD:0< D) (hF:0< F) (hnR:n≤ R) (hDR:D≤ R) (hFR:F≤ R)
    (hN:MomentLP.dimension n r≤ R) (hw:wordHeight R≤ w)
    (room:∀ s∈buffers,space R T≤ extent s):
    NativeOracleExecution.ProjectionBounds D k r F (2^(100*(R+1))) w T G extent:=by
  let N:=MomentLP.dimension n r
  let m:=NativeMomentAssembly.rowCount n r
  have hm:m≤ NativeProjectionQueryBounds.rootRows R:=by
    have hprod:=Nat.mul_le_mul hN hnR
    dsimp only [m,NativeMomentAssembly.rowCount,NativeProjectionQueryBounds.rootRows]
    change 2+(N+(N+(N*n+(N+N))))≤6*(R+1)^2
    change N*n≤ R*R at hprod
    nlinarith only [hprod,hN]
  have hshape:NativeDistanceData.shapeSize m N≤
      NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R:=by
    dsimp only [NativeDistanceData.shapeSize,NativeDistanceData.wordLength,
      NativeDistanceData.rows,NativeDistanceData.columns]
    gcongr
  have hlen:(encodeProgram (MomentLP.program G k r)).length=
      2+3*(m*N)+3*(m+N):=NativeMomentInput.input_length G k r
  have hmain:(encodeProgram (MomentLP.program G k r)).length+
      NativeDistanceData.wordLength m N+4*N+10≤ shape R:=by
    have hpow:R+1≤(R+1)^5:=le_self_pow (by omega) (by decide)
    have hpad:2*N≤1000*(R+1)^5:=by change MomentLP.dimension n r≤ R at hN; omega
    calc
      _≤ NativeDistanceData.shapeSize m N+2*N:=by
        rw [hlen]; dsimp only [NativeDistanceData.shapeSize]; omega
      _≤ NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R+1000*(R+1)^5:=
        Nat.add_le_add hshape hpad
      _≤ shape R:=by dsimp only [shape]; omega
  have ht:=tolerance_guard n D F R hnR hDR hFR
  have hbase:200*(R+1)+shape R≤ w:=hw
  have hword:w<2^w:=Nat.lt_two_pow_self
  have hsmall:4*R+20≤ w:=by
    have hshape0:=Nat.zero_le (shape R)
    omega
  have hrat:2*(2^(100*(R+1)))^2+3<2^w:=by
    have hexp:2*(100*(R+1))+4≤ w:=by
      have hh:4≤ shape R:=by dsimp only [shape]; omega
      omega
    have hp:=Nat.pow_le_pow_right (by decide:1≤2) hexp
    have he:2^(2*(100*(R+1))+4)=16*(2^(100*(R+1)))^2:=by
      rw [pow_add,Nat.mul_comm 2 (100*(R+1)),pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos:=Nat.one_le_pow (100*(R+1)) 2 (by decide)
    nlinarith only [hp,hpos]
  have scale:4*N≤2^(100*(R+1)):=
    (show 4*N≤100*(R+1) by omega).trans Nat.lt_two_pow_self.le
  have inroom (s:String) (hs:s∈buffers):shape R+T+10≤ extent s:=room s hs
  refine ⟨hn,hD,hF,?_,hrat,?_,scale,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (by omega:(encodeProgram (MomentLP.program G k r)).length+2≤ w).trans_lt hword
  · exact (by omega:4*MomentLP.dimension n r+5≤ w).trans_lt hword
  · have hs:1000*(R+1)^5≤ shape R:=by dsimp only [shape]; omega
    exact (ht.trans (by omega)).trans_lt hword
  · exact (by omega:n+19≤ w).trans_lt hword
  · have h:=inroom "lp.input" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); omega
  · have h:=inroom "projection.center" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); omega
  · have h:=inroom "projection.tolerance" (by simp [buffers]); omega
  · have h:=inroom "lp.word" (by simp [buffers]); change NativeDistanceData.wordLength m N< extent "lp.word"; omega
  · have h:=inroom "vm.addresses" (by simp [buffers]); omega
  · have h:=inroom "vm.values" (by simp [buffers]); omega
  · have h:=inroom "vm.output" (by simp [buffers]); omega
  · have h:=inroom "cut.source" (by simp [buffers]); omega
  · have h:=inroom "round.normal" (by simp [buffers]); omega

end Lax263307Proofs.NativeProjectionResources

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

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment NativeOracleContext

theorem update_variable (cfg:Config) (s:String)
    (hv:s≠"vm.width") (hq:s∉NativeRoundedQuery.command.wvars)
    (hp:s∉NativeRawOracle.prepare.wvars) (ho:s∉NativeOracleScalars.reserved)
    (hs:s∉NativeRoundedState.command.wvars) (hf:s∉(NativeRoundedControl.finish 4 14).wvars):
    s∉(NativeRoundedControl.command cfg.rounded 4 14).wvars:=by
  have hu:=NativeRoundedControl.update_variable cfg.rounded s hq hp ho hs
  simp_all only [NativeRoundedControl.command,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem update_array (cfg:Config) (s:String)
    (hq:s∉NativeRoundedQuery.command.warrs) (hp:s∉NativeRawOracle.prepare.warrs)
    (ho:s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (hs:s∉NativeRoundedState.command.warrs):
    s∉(NativeRoundedControl.command cfg.rounded 4 14).warrs:=by
  have hu:=NativeRawFrame.array cfg.rounded s hp ho
  simp_all only [NativeRoundedControl.command,NativeRoundedUpdate.command,
    NativeRoundedControl.finish,NativeAttemptReply.noneCommand,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

end Lax263307Proofs.NativeOracleRounds

end

section

namespace Lax263307Proofs.NativeRecursiveDomain

open Lax263307 GraphClasses ComputedSeparators NativeNodeProtocol

theorem root {C:GraphClass} {N frameSize capacity:ℕ} (G:SimpleGraph (Fin N))
    (hG:G∈C N) (hN:0< N) (hstack:RecursionDepth.depth N*frameSize≤ capacity)
    (k:ℕ) (hk:0< k) (hkN:k≤ N):
    eligible C N frameSize capacity (RecursionDepth.depth N) N G k 0:=
  ⟨hG,hN,Nat.le_refl _,hk,hkN,Nat.le_refl _,by simpa using hstack⟩

end Lax263307Proofs.NativeRecursiveDomain

end

section

namespace Lax263307Proofs.NativeQuadraticResources

open NativeQuadraticSum

theorem square_power (h:ℕ):(2^h)^2=2^(2*h):=by
  rw [←pow_mul,Nat.mul_comm h 2]

theorem height_bits (n h:ℕ):height (2^h) n=2^((2*h+1)*(n*n+1)):=by
  rw [height,square_power]
  have he:2*2^(2*h)=2^(2*h+1):=by rw [pow_add,pow_one]; exact Nat.mul_comm _ _
  rw [he,←pow_mul]

theorem cost_bound (n h:ℕ):cost (2^h) n≤1000*(h+1)*(n+1)^4:=by
  simp only [cost,height_bits,square_power,Nat.size_pow]
  nlinarith only [Nat.zero_le (h*n),Nat.zero_le (h*n^2),Nat.zero_le (h*n^3),
    Nat.zero_le (h*n^4),Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

end Lax263307Proofs.NativeQuadraticResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeHeavyResources

open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def span (n r k p h:ℕ):ℕ:=n+r+k+p+N n r+h+20

def wordExponent (n r k p h:ℕ):ℕ:=36*(span n r k p h)^4+10

theorem guards (n r k p h w:ℕ) (hw:wordExponent n r k p h≤ w):
    3*N n r+10<2^w∧ 3*(n*n)+3*n+r+10<2^w∧ 2^n<2^w∧
    2*(2^h)^2+3<2^w∧ 2*(NativeQuadraticSum.height (2^h) n)^2+3<2^w∧
    NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n)<2^w∧
    NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<2^w:=by
  let S:=span n r k p h
  let E:=6*S^4
  let R:=2^E
  have hS:20≤ S:=by dsimp [S,span]; omega
  have hn:n+1≤ S:=by dsimp [S,span]; omega
  have hk:k≤ S:=by dsimp [S,span]; omega
  have hp:p≤ S:=by dsimp [S,span]; omega
  have hr:r≤ S:=by dsimp [S,span]; omega
  have hN:N n r≤ S:=by dsimp [S,span]; omega
  have hh:h≤ S:=by dsimp [S,span]; omega
  have hS2:S≤ S^2:=by nlinarith only [hS]
  have hS3:S^2≤ S^3:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  have hS4:S^3≤ S^4:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  have hSE:S≤ E:=by dsimp [E]; omega
  have hER:E≤ R:=(Nat.lt_two_pow_self).le
  have hSR:S≤ R:=hSE.trans hER
  have hR:1≤ R:=one_le_pow₀ (by decide:1≤(2:ℕ))
  have hR2:R≤ R^2:=by nlinarith only [hR]
  have hR5:R^2≤ R^5:=pow_le_pow_right₀ hR (by omega)
  have hMR:2^h≤ R:=Nat.pow_le_pow_right (by decide) (hh.trans hSE)
  have hheight:(2*h+1)*(n*n+1)≤ E:=by
    have ht:(2*h+1)*(n*n+1)≤(2*S+1)*(S*S+1):=by gcongr <;> omega
    dsimp [E]
    nlinarith only [ht,hS,hS4,Nat.zero_le (S^2)]
  have hHR:NativeQuadraticSum.height (2^h) n≤ R:=by
    rw [NativeQuadraticResources.height_bits]
    exact Nat.pow_le_pow_right (by decide) hheight
  have hbase:NativeConditioningFloor.base n p≤2*S^3:=by
    have hlog:Nat.log2 n+1≤ S:=(Nat.add_le_add_right (Nat.log2_le_self n) 1).trans hn
    dsimp [NativeConditioningFloor.base]
    calc
      2*n*p*(Nat.log2 n+1)≤2*S*S*S:=by gcongr <;> omega
      _=2*S^3:=by ring
  have hbaseE:NativeConditioningFloor.base n p≤ E:=by dsimp [E]; omega
  have hDR:NativeConditioningFloor.base n p^r≤ R:=by
    calc
      NativeConditioningFloor.base n p^r≤(2^(2*S^3))^r:=
        Nat.pow_le_pow_left (hbase.trans (Nat.lt_two_pow_self).le) r
      _=2^((2*S^3)*r):=(pow_mul _ _ _).symm
      _≤ 2^E:=Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith only [Nat.mul_le_mul_left (2*S^3) hr,Nat.zero_le (S^4)])
  have hcommon:128*R^5<2^w:=by
    have heq:128*R^5=2^(5*E+7):=by
      dsimp [R]
      rw [←pow_mul,pow_add]
      norm_num
      rw [Nat.mul_comm E 5,Nat.mul_comm]
    rw [heq]
    apply Nat.pow_lt_pow_right (by decide)
    change 36*S^4+10≤ w at hw
    dsimp [E]
    omega
  have hkR:=hk.trans hSR
  have hpR:=hp.trans hSR
  have hnR:n≤ R:=(by omega:n≤ S).trans hSR
  have hrR:=hr.trans hSR
  have hNR:=hN.trans hSR
  have hbaseR:=hbaseE.trans hER
  have hM2:(2^h)^2≤ R^2:=Nat.pow_le_pow_left hMR 2
  have hH2:(NativeQuadraticSum.height (2^h) n)^2≤ R^2:=Nat.pow_le_pow_left hHR 2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by nlinarith only [Nat.mul_le_mul hnR hnR,hnR,hrR,hR,hR2,hR5]) hcommon
  · exact (Nat.pow_le_pow_right (by decide) ((by omega:n≤ S).trans hSE)).trans_lt
      (lt_of_le_of_lt (by omega:R≤128*R^5) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact (NativeConditioningResources.test_polynomial k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n) R hkR hpR hDR hMR hHR hR).trans_lt
      (lt_of_le_of_lt (by omega) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon

theorem cost_bound (n r h:ℕ):NativeHeavySearch.cost (2^h) n r≤
    2000*(n+r+N n r+h+20)^6:=by
  let S:=n+r+N n r+h+20
  have hS:20≤ S:=by dsimp [S]; omega
  have hn:n+1≤ S:=by dsimp [S]; omega
  have hN:N n r≤ S:=by dsimp [S]; omega
  have hr:r≤ S:=by dsimp [S]; omega
  have hh:h+1≤ S:=by dsimp [S]; omega
  have hs:n.size≤ S:=(Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega:n≤ S)
  have hq:NativeQuadraticSum.cost (2^h) n≤1000*S^5:=by
    apply (NativeQuadraticResources.cost_bound n h).trans
    calc
      1000*(h+1)*(n+1)^4≤1000*S*S^4:=by gcongr
      _=1000*S^5:=by ring
  have hsize:((2^h)^2).size≤2*S+1:=by
    rw [NativeQuadraticResources.square_power,Nat.size_pow]
    omega
  have hS2:S≤ S^2:=by nlinarith only [hS]
  have hS25:S^2≤ S^5:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  have hc:NativeConditioningEntry.cost (2^h) n r+18≤1500*S^5:=by
    dsimp [NativeConditioningEntry.cost,NativeHeavyCandidate.cost,NativeConditioningNumerator.cost]
    have hx:(17*N n r+120)*n≤(17*S+120)*S:=by gcongr <;> omega
    nlinarith only [hx,hN,hq,hS2,hS25,hS]
  have hx:(NativeConditioningEntry.cost (2^h) n r+18)*N n r≤1500*S^6:=by
    calc
      _≤ (1500*S^5)*S:=Nat.mul_le_mul hc hN
      _=1500*S^6:=by ring
  have hS56:S^5≤ S^6:=pow_le_pow_right₀ (by omega:1≤ S) (by omega)
  change NativeHeavySearch.cost (2^h) n r≤2000*S^6
  dsimp [NativeHeavySearch.cost]
  omega

end Lax263307Proofs.NativeHeavyResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeNearResources

open Lax263307 NativeCoreMachine

def buffers:List String:= ["child.graph","search.graph","subset.bits","restrict.vertices","lp.word",
  "cut.source","sum.input","near.moments","near.costs","lp.input","round.normal","separator.pieces"]

theorem bounds (cfg:Config) (n r D k p fuel S H R w:ℕ) (extent:String→ ℕ) (front:List ℕ)
    (hn:0< n) (hD:0< D) (hp:0< p) (hnR:n≤ R) (hrR:r≤ R) (hDR:D≤ R)
    (hkR:k≤ R) (hpR:p≤ R) (hNR:NativeCatalogMetadata.N n r≤ R) (hf:fuel≤2*R+2)
    (hw:wordHeight cfg R H S front.length≤ w)
    (hext:∀ a∈frameArrays cfg,extent a=S)
    (hstack:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤ extent "recursion.frames")
    (hroom:∀ a∈buffers,space R≤ extent a):
    NativeNearExecution.Bounds n r D k p (2^H) (2*H) (R+1) fuel S w cfg extent front:=by
  have hspan:NativeHeavyResources.span n r k p H≤5*R+H+20:=by
    dsimp only [NativeHeavyResources.span]; omega
  have hheavy:NativeHeavyResources.wordExponent n r k p H≤36*(5*R+H+20)^4+10:=by
    dsimp only [NativeHeavyResources.wordExponent]
    gcongr
  have hwHeavy:NativeHeavyResources.wordExponent n r k p H≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have guards:=NativeHeavyResources.guards n r k p H w hwHeavy
  have hcomponent:NativeComponentDecision.wordHeight n D k (2*H)≤
      2*((2*H+1)*(R+1))+4*(3*R+20)+20:=by
    dsimp only [NativeComponentDecision.wordHeight,NativeComponentResources.span]
    gcongr <;> omega
  have hwComponent:NativeComponentDecision.wordHeight n D k (2*H)≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have hnn:n*n≤ R*R:=Nat.mul_self_le_mul_self hnR
  have hcollection:front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*(n+1)+(R+1)+fuel+3*NativeCatalogMetadata.N n r+80≤ w:=by
    dsimp only [wordHeight] at hw
    omega
  have hreply:n+19<2^w:=by
    have h:n+19≤ w:=by omega
    exact h.trans_lt Nat.lt_two_pow_self
  have hspace:n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1< space R:=by
    dsimp only [space]
    nlinarith only [hnn,hnR,hNR,Nat.zero_le (R^2)]
  have room (a:String) (ha:a∈buffers):
      n*n+3*n+3*(n*n)+3*NativeCatalogMetadata.N n r+n+1< extent a:=hspace.trans_le (hroom a ha)
  refine ⟨hn,hD,hp,Nat.one_le_pow _ _ (by decide),hreply,guards.1,guards.2.1,guards.2.2.1,
    guards.2.2.2.1,guards.2.2.2.2.1,guards.2.2.2.2.2.1,guards.2.2.2.2.2.2,?_,hwComponent,
    hcollection.trans_lt Nat.lt_two_pow_self,hext,hstack,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←pow_mul,Nat.mul_comm H 2]
  · have h:=room "child.graph" (by simp [buffers]); omega
  · have h:=room "search.graph" (by simp [buffers]); omega
  · have h:=room "subset.bits" (by simp [buffers]); omega
  · have h:=room "restrict.vertices" (by simp [buffers]); omega
  · have h:=room "lp.word" (by simp [buffers]); omega
  · have h:=room "cut.source" (by simp [buffers]); omega
  · have h:=room "sum.input" (by simp [buffers]); omega
  · have h:=room "near.moments" (by simp [buffers]); omega
  · have h:=room "near.costs" (by simp [buffers]); omega
  · have h:=room "lp.input" (by simp [buffers]); omega
  · have h:=room "round.normal" (by simp [buffers]); omega
  · have h:=room "separator.pieces" (by simp [buffers]); omega

end Lax263307Proofs.NativeNearResources

end

section

namespace Lax263307Proofs.NativeNodeResource

open Lax263307 AlgorithmParameters ParameterResources

theorem guard_bound (a K b n D:ℕ) (hK:0< K) (hn:0< n):
    NativeNodeParameters.guard a K b n D≤
      (a+K+24*b+(4*a+2)+50)*(resource a K b n D+1)^2:=by
  let R:=resource a K b n D
  have hnR:n≤ R:=by dsimp [R,resource]; omega
  have hDR:D≤ R:=by dsimp [R,resource]; omega
  have hload:load b n D≤ R:=by dsimp [R,resource]; omega
  have hsp:sparsity a K b n D≤ R:=by dsimp [R,resource]; omega
  have hl:level a K b n D≤ R:=by dsimp [R,resource]; omega
  have hth:targetThreshold a K b n D≤ R:=by
    have ht:targetThreshold a K b n D≤ sparsity a K b n D:=by unfold sparsity; omega
    exact ht.trans hsp
  have hp:(load b n D+1)^(4*a+2)≤ R:=by
    have hh:(load b n D+1)^(4*a+2)≤ targetThreshold a K b n D:=
      Nat.le_mul_of_pos_left _ hK
    exact hh.trans hth
  have hlog:Nat.log2 n+1≤ n:=by
    rw [←NativeLogarithms.size_eq n hn]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hL:logarithm n≤2*n:=by
    change Nat.log2 (2*n)+1≤2*n
    rw [←NativeLogarithms.size_eq (2*n) (by omega)]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hf:floorDenominator a K b n D≤2*R^2:=by
    rw [NativeNodeParameters.floor_eq]
    have hm:=Nat.mul_le_mul hnR hl
    nlinarith only [hm]
  have hmul:12*b*D≤12*b*R:=Nat.mul_le_mul_left _ hDR
  have hR:1≤ R+1:=by omega
  have hRs:R≤(R+1)^2:=by nlinarith only [hR]
  dsimp only [NativeNodeParameters.guard]
  change _≤(a+K+24*b+(4*a+2)+50)*(R+1)^2
  nlinarith only [hnR,hDR,hload,hsp,hl,hth,hp,hlog,hL,hf,hmul,hRs]

end Lax263307Proofs.NativeNodeResource

end

section

namespace Lax263307Proofs.NativePrecisionResources

open Lax263307 AlgorithmParameters ParameterResources
open NativeNodePrecision

theorem guard_bound (n D N b r S:ℕ) (hn:0< n) (hD:0< D) (hN:0< N) (hb:0< b)
    (hnS:n≤ S) (hDS:D≤ S) (hNS:N≤ S) (hrS:r≤ S) (hbS:b≤2*S^2)
    (hR:radius n D N b r≤ S) (hP:prec n D N b r≤ S) (hI:count n D N b r≤ S):
    NativeNodePrecision.guard n D N b r≤400*(S+1)^2:=by
  have hpow:0< b^r:=pow_pos hb _
  have hF:0<256*N*n*n*D*D:=by positivity
  have hp:b^r≤ S:=(Nat.le_mul_of_pos_left _ hF).trans hR
  have h5:256*N*n*n*D*D≤ S:=(Nat.le_mul_of_pos_right _ hpow).trans hR
  have h4:256*N*n*n*D≤ S:=(Nat.le_mul_of_pos_right _ hD).trans h5
  have h3:256*N*n*n≤ S:=(Nat.le_mul_of_pos_right _ hD).trans h4
  have h2:256*N*n≤ S:=(Nat.le_mul_of_pos_right _ hn).trans h3
  have h1:256*N≤ S:=(Nat.le_mul_of_pos_right _ hn).trans h2
  have hprod:prec n D N b r*N≤ S^2:=by simpa only [pow_two] using Nat.mul_le_mul hP hNS
  dsimp only [NativeNodePrecision.guard]
  nlinarith only [hnS,hDS,hNS,hrS,hbS,hR,hP,hI,hp,h5,h4,h3,h2,h1,hprod]

theorem actual_guard (a K b n D:ℕ) (hK:0< K) (hn:0< n) (hD:0< D):
    NativeNodePrecision.guard n D (MomentLP.dimension n (level a K b n D)) (floorDenominator a K b n D)
      (level a K b n D)≤400*(resource a K b n D+1)^2:=by
  let S:=resource a K b n D
  have hnS:n≤ S:=by dsimp [S,resource]; omega
  have hDS:D≤ S:=by dsimp [S,resource]; omega
  have hNS:MomentLP.dimension n (level a K b n D)≤ S:=by dsimp [S,resource]; omega
  have hrS:level a K b n D≤ S:=by dsimp [S,resource]; omega
  have hR:radiusDenominator a K b n D≤ S:=by dsimp [S,resource]; omega
  have hP:precision a K b n D≤ S:=by dsimp [S,resource]; omega
  have hI:iterations a K b n D≤ S:=by dsimp [S,resource]; omega
  have hf:0< floorDenominator a K b n D:=by
    unfold floorDenominator sparsity targetThreshold
    positivity
  have hbS:floorDenominator a K b n D≤2*S^2:=by
    rw [NativeNodeParameters.floor_eq]
    have hm:=Nat.mul_le_mul hnS hrS
    nlinarith only [hm]
  exact guard_bound n D _ _ _ S hn hD (NativeMomentFamily.dimension_positive _ _) hf
    hnS hDS hNS hrS hbS
    (by simpa only [actual_radius] using hR)
    (by simpa only [actual_precision] using hP)
    (by simpa only [actual_iterations] using hI)

end Lax263307Proofs.NativePrecisionResources

end

section

namespace Lax263307Proofs.NativeExhaustiveResources

open Lax263307 AlgorithmParameters ParameterResources

theorem table_words (B n k:ℕ) (hm:2^n< B):∀ i≤ n,∀ j≤ k,i.choose j< B:=by
  intro i hi j hj
  exact (Nat.choose_le_two_pow i j).trans_lt ((Nat.pow_le_pow_right (by decide) hi).trans_lt hm)

theorem choices_bound (n k threshold R:ℕ) (hn:n≤ R)
    (hsmall:k≤ threshold∨ n≤1) (hpower:(n+1)^threshold≤ R):n.choose k≤ R+2:=by
  rcases hsmall with hk | hn1
  · have hbase:n^k≤ (n+1)^k:=Nat.pow_le_pow_left (by omega) k
    have hexp:(n+1)^k≤ (n+1)^threshold:=Nat.pow_le_pow_right (by omega) hk
    exact (Nat.choose_le_pow n k).trans (hbase.trans (hexp.trans (by omega)))
  · exact (Nat.choose_le_two_pow n k).trans
      ((Nat.pow_le_pow_right (by decide) hn1).trans (by norm_num))

theorem time_bound (n k threshold R:ℕ) (hn:n≤ R) (hk:k≤ n)
    (hsmall:k≤ threshold∨ n≤1) (hpower:(n+1)^threshold≤ R):
    NativeExhaustive.cost n k+15*n+20≤300*(R+2)^3:=by
  let S:=R+2
  have hS:1≤ S:=by dsimp [S]; omega
  have hnS:n≤ S:=by dsimp [S]; omega
  have hnp:n+1≤ S:=by dsimp [S]; omega
  have hkp:k+1≤ S:=by omega
  have hchoices:n.choose k≤ S:=choices_bound n k threshold R hn hsmall hpower
  have h12:S≤ S^2:=le_self_pow hS (by omega)
  have h23:S^2≤ S^3:=Nat.pow_le_pow_right hS (by omega)
  have h03:1≤ S^3:=Nat.one_le_pow _ _ hS
  calc
    NativeExhaustive.cost n k+15*n+20≤ 54*S^2+(38*S^2+54*S+44)*S+35+15*S+20:=by
      dsimp only [NativeExhaustive.cost]
      have hsq:n*n≤ S^2:=by simpa only [pow_two] using Nat.mul_self_le_mul_self hnS
      have htable:(n+1)*(k+1)≤ S^2:=by simpa only [pow_two] using Nat.mul_le_mul hnp hkp
      have hb:38*n*n+54*n+44≤38*S^2+54*S+44:=by nlinarith only [hsq,hnS]
      have hc:=Nat.mul_le_mul hb hchoices
      nlinarith only [htable,hc,hnS]
    _≤ 300*S^3:=by nlinarith only [h12,h23,h03]
    _=_:=rfl

theorem node_time (a K b n D k R:ℕ) (hR:resource a K b n D≤ R) (hk:k≤ n)
    (hsmall:k≤ cutoff a K b n D∨ n≤1):
    NativeExhaustive.cost n k+15*n+20≤300*(R+2)^3:=by
  apply time_bound n k (cutoff a K b n D) R _ hk hsmall
  · dsimp only [resource] at hR; omega
  · dsimp only [resource] at hR; omega

end Lax263307Proofs.NativeExhaustiveResources

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeEntryResources

open Lax263307 AlgorithmParameters NativeCoreMachine

def buffers:List String:= ["choose.table","subset.bits","catalog.mask","catalog.card","catalog.independent",
  "lp.input","moment.program","round.shape","round.center"]

def shape (n k r N:ℕ):ℕ:=n*n+(n+1)*(k+1)+(n+1)*(r+3)+
  (2+3*((2+N*(n+4))*N)+3*((2+N*(n+4))+N))+3*(N*N)+3*N+n+k+r+N+100

theorem shape_bound (n k r N R:ℕ) (hn:n≤ R) (hk:k≤ R) (hr:r≤ R) (hN:N≤ R):
    shape n k r N≤1000*(R+1)^4:=by
  have hs:shape n k r N≤ shape R R R R:=by unfold shape; gcongr
  apply hs.trans
  dsimp only [shape]
  nlinarith only [Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]

theorem bounds (cfg:Config) (n D k fuel R w:ℕ) (extent:String→ ℕ)
    (hK:0< cfg.K) (hn:0< n) (hD:0< D) (hk:k≤ n) (hf:fuel≤2*R+2)
    (hR:ParameterResources.resource cfg.a cfg.K cfg.b n D≤ R)
    (hw:amount cfg R≤ w) (hroom:∀ a∈buffers,amount cfg R≤ extent a):
    NativeNodeExecution.Bounds w D k fuel n cfg extent:=by
  let r:=level cfg.a cfg.K cfg.b n D
  let N:=MomentLP.dimension n r
  let U:=R+1
  have hnR:n≤ R:=by dsimp only [ParameterResources.resource] at hR; omega
  have hkR:k≤ R:=hk.trans hnR
  have hrR:r≤ R:=by dsimp only [r,ParameterResources.resource] at hR ⊢; omega
  have hNR:N≤ R:=by dsimp only [N,r,ParameterResources.resource] at hR ⊢; omega
  have hcR:cutoff cfg.a cfg.K cfg.b n D≤ R:=by
    have hp:(n+1)^cutoff cfg.a cfg.K cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at hR; omega
    exact Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_left (by omega:2≤ n+1) _).trans hp)
  have hU:1≤ U:=by dsimp [U]; omega
  have h24:U^2≤ U^4:=Nat.pow_le_pow_right hU (by decide)
  have hU4:U≤ U^4:=le_self_pow hU (by decide)
  have hc:2000≤ coefficient cfg:=by dsimp only [coefficient]; omega
  have hshape:=(shape_bound n k r N R hnR hkR hrR hNR).trans
    (Nat.mul_le_mul_right ((R+1)^4) (show 1000≤ coefficient cfg by omega))
  have hshapeWord:shape n k r N<2^w:=hshape.trans_lt (hw.trans_lt Nat.lt_two_pow_self)
  have hnw:n< w:=by
    have ha:R+1≤ amount cfg R:=hU4.trans (Nat.le_mul_of_pos_left _ (by omega:0< coefficient cfg))
    have ha':=ha.trans hw
    omega
  have hm:2^n<2^w:=Nat.pow_lt_pow_right (by decide) hnw
  have hg:=NativeNodeResource.guard_bound cfg.a cfg.K cfg.b n D hK hn
  have hg4:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D≤
      (cfg.a+cfg.K+24*cfg.b+(4*cfg.a+2)+50)*U^4:=
    hg.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 2).trans h24))
  have hp:=NativePrecisionResources.actual_guard cfg.a cfg.K cfg.b n D hK hn hD
  have hp4:NativeNodePrecision.guard n D N (floorDenominator cfg.a cfg.K cfg.b n D) r≤400*U^4:=
    hp.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 2).trans h24))
  have hguard:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29≤ amount cfg R:=by
    dsimp only [amount,coefficient,U] at *
    nlinarith only [hg4,hnR,hkR,hcR,hf,hU4,Nat.one_le_pow 4 (R+1) (by omega)]
  have hparams:NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+k+cfg.b+5≤ amount cfg R:=by
    have hbR:cfg.b≤ R:=by
      have hload:load cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at hR; omega
      dsimp only [load] at hload
      have hlog:1≤ logarithm n:=by dsimp only [logarithm]; omega
      nlinarith only [hload,Nat.mul_le_mul hD hlog]
    dsimp only [amount,coefficient,U] at *
    nlinarith only [hg4,hkR,hbR,hU4,Nat.one_le_pow 4 (R+1) (by omega)]
  have hprec:NativeNodePrecision.guard n D N (floorDenominator cfg.a cfg.K cfg.b n D) r≤ amount cfg R:=
    hp4.trans (Nat.mul_le_mul_right _ (show 400≤ coefficient cfg by omega))
  have hlen:NativeMomentInput.length n r=2+3*((2+N*(n+4))*N)+3*((2+N*(n+4))+N):=by
    rw [NativeMomentInput.length,NativeMomentInput.row_count_eq]
  have room (a:String) (ha:a∈buffers):shape n k r N≤ extent a:=hshape.trans (hroom a ha)
  dsimp only [shape] at hshapeWord room
  refine ⟨hguard.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,hm,
    NativeExhaustiveResources.table_words _ n k hm,hK,hparams.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,
    hprec.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · change n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N+20<2^w
    rw [hlen]; omega
  · change 3*(N*N)+3*N+20<2^w; omega
  · have h:=room "choose.table" (by simp [buffers]); omega
  · have h:=room "choose.table" (by simp [buffers]); change (n+1)*(r+3)≤ extent "choose.table"; omega
  · have h:=room "subset.bits" (by simp [buffers]); omega
  · have h:=room "catalog.mask" (by simp [buffers]); change N≤ extent "catalog.mask"; omega
  · have h:=room "catalog.card" (by simp [buffers]); change N≤ extent "catalog.card"; omega
  · have h:=room "catalog.independent" (by simp [buffers]); change N≤ extent "catalog.independent"; omega
  · have h:=room "lp.input" (by simp [buffers]); change NativeMomentInput.length n r≤ extent "lp.input"; rw [hlen]; omega
  · have h:=room "moment.program" (by simp [buffers]); change NativeMomentInput.length n r≤ extent "moment.program"; rw [hlen]; omega
  · have h:=room "lp.input" (by simp [buffers]); change 3*(N*N)+3*N≤ extent "lp.input"; omega
  · have h:=room "round.shape" (by simp [buffers]); change 3*(N*N)≤ extent "round.shape"; omega
  · have h:=room "round.center" (by simp [buffers]); change 3*N≤ extent "round.center"; omega

end Lax263307Proofs.NativeEntryResources

end

section

namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 0

theorem height_bound (wp:Polynomial ℕ) (R:ℕ):
    NativeOraclePrecision.roundedHeight wp R≤(heightPolynomial wp).eval R:=by
  have hq:=Lax263307Proofs.NativeProjectionQueryBounds.polynomial_bound R
  have hp:=Lax263307Proofs.NativeFlowQueryResources.eval_mono wp hq
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp [NativeOraclePrecision.roundedHeight,NativeOraclePrecision.certificateHeight]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1)) _) _) _

end Lax263307Proofs.NativePolynomialBudget

end

section

namespace Lax263307Proofs.NativePolynomialEnvelope

def Bounded (f:ℕ→ ℕ):Prop:= ∃ P:Polynomial ℕ,∀ R,f R≤ P.eval R

theorem eval (P:Polynomial ℕ) {f:ℕ→ ℕ} (hf:Bounded f):Bounded (fun R => P.eval (f R)):=by
  obtain ⟨Q,hQ⟩:=hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

end Lax263307Proofs.NativePolynomialEnvelope
end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeFlowBudget

open Lax455465Proofs NativeLargeCapacity NativeLargeResources NativeUniformFlow

private theorem logarithm_bound (n R:ℕ) (hn:n≤ R):Nat.log2 (2*n)+1≤2*R+1:=by
  have h:Nat.log2 (2*n)≤2*n:=by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 (2*n)
  omega

theorem height_bound (b n load k h R:ℕ) (hp:Polynomial ℕ)
    (hn:n≤ R) (hl:load≤ R) (hk:k≤ R) (hh:h≤ hp.eval R):
    heightExponent b n load k h≤(heightPolynomial b hp).eval R:=by
  have hlog:=logarithm_bound n R hn
  have hnum:numerator b n n k≤(numeratorPolynomial b).eval R:=by
    simp only [numeratorPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [numerator]
    gcongr
  have hres:resource b n n load k≤(resourcePolynomial b).eval R:=by
    simp only [resourcePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [resource,denominator]
    gcongr
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [heightExponent]
  omega

theorem query_bound (b n H R:ℕ) (hp:Polynomial ℕ)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    NativeFlowQueryResources.sizeBound n H≤(queryPolynomial b hp).eval R:=by
  simp only [queryPolynomial,lengthPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [NativeFlowQueryResources.sizeBound,NativeSplitInput.wordLength]
  gcongr

theorem width_bound (b n H R:ℕ) (hp wp tp op:Polynomial ℕ) (p:Lax808846.Ram.Program)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    wordHeight n H p wp tp op≤(widthPolynomial b hp wp tp op p).eval R:=by
  have hS:=query_bound b n H R hp hn hH
  have hw:=NativeFlowQueryResources.eval_mono wp (Nat.add_le_add_right hS 1)
  have ht:=NativeFlowQueryResources.eval_mono tp hS
  have ho:=NativeFlowQueryResources.eval_mono op hS
  simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only [wordHeight,shape]
  gcongr

theorem space_bound (b n H R:ℕ) (hp tp:Polynomial ℕ)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    spaceBound n H tp≤(spacePolynomial b hp tp).eval R:=by
  have hS:=query_bound b n H R hp hn hH
  have ht:=NativeFlowQueryResources.eval_mono tp hS
  simp only [spacePolynomial,lengthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_ofNat]
  dsimp only [spaceBound,NativeSplitInput.wordLength]
  gcongr

theorem time_bound (b n H R:ℕ) (hp tp:Polynomial ℕ)
    (p:Lax808846.Ram.Program) (coeff:List ℕ)
    (hn:n≤ R) (hH:H≤(heightPolynomial b hp).eval R):
    NativeSeparatorOutput.timeBound n H p coeff tp≤(timePolynomial b hp tp p coeff).eval R:=by
  have hS:=query_bound b n H R hp hn hH
  have ht:=NativeFlowQueryResources.eval_mono tp hS
  have hs:(2*n).size≤2*n+1:=Nat.size_le.mpr (by
    have hh:2*n<2^(2*n):=Nat.lt_two_pow_self
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsplit:=NativeUniformFlow.cost_mono n R _ _ _ _ p coeff hn hS ht
  have he:NativeSplitOracle.cost R p coeff (tp.eval ((queryPolynomial b hp).eval R))
      ((queryPolynomial b hp).eval R)=(splitPolynomial b hp tp p coeff).eval R:=by
    simp only [splitPolynomial,lengthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_comp,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [NativeSplitOracle.cost,NativeSplitInput.wordLength]
    ring
  rw [he] at hsplit
  have hc:callbackTime n H p coeff tp≤168*R+132+(splitPolynomial b hp tp p coeff).eval R:=by
    dsimp only [callbackTime]
    omega
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only [NativeSeparatorOutput.timeBound,NativeSeparatorProgram.timeBound]
  gcongr

end Lax263307Proofs.NativeFlowBudget

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedBudget

open Lax263307 NativeCoreMachine NativePolynomialEnvelope

theorem cost_height {lp:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (R:ℕ):
    2*NativeSelectedLP.certificateHeight p R≤ (NativePolynomialBudget.heightPolynomial p.width).eval R:=by
  have h:=NativePolynomialBudget.height_bound p.width R
  have hm:2*NativeSelectedLP.certificateHeight p R+1≤
      (R+1)*(2*NativeSelectedLP.certificateHeight p R+1):=Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [NativeOraclePrecision.roundedHeight] at h
  change 80*(R+1)+(R+1)*(2*NativeSelectedLP.certificateHeight p R+1)+2*R+1≤ _ at h
  omega

theorem flow_time {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (c R W n D k:ℕ)
    (hn:n≤ R) (hl:AlgorithmParameters.load cfg.b n D≤ R) (hk:k≤ R)
    (hw:demand cfg p q c R≤ W):NativeSelectedRounds.flowTime cfg p q n D k R≤ W:=by
  have h:=NativeFlowBudget.time_bound cfg.b n (NativeSelectedRounds.flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.time q.code q.coeff hn
    (NativeFlowBudget.height_bound cfg.b n (AlgorithmParameters.load cfg.b n D) k
      (2*NativeSelectedLP.certificateHeight p R) R (NativePolynomialBudget.heightPolynomial p.width)
      hn hl hk (cost_height p R))
  dsimp only [demand] at hw
  exact h.trans (by omega)

end Lax263307Proofs.NativeSelectedBudget

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSourceFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine

theorem base_input_n (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "input.n"∉c.wvars:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "input.n"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
  · decide
  · change "input.n"∉((NativeLargeNode.command 0 0 0).seq (go 4)).wvars; decide
  · exact NativeOracleExecution.projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_blowup_length (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "blowup.length"∉c.wvars:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "blowup.length"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
  · decide
  · change "blowup.length"∉((NativeLargeNode.command 0 0 0).seq (go 4)).wvars; decide
  · exact NativeOracleExecution.projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_blowup_owner (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "blowup.owner"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "blowup.owner"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "blowup.owner"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_image_output (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "image.output"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "image.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "image.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_weighted_output (cfg:Config) (c:Com) (hc:c∈cases cfg [] []):
    "weighted.output"∉c.warrs:=by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "weighted.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "weighted.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem scalar_unsaved (cfg:Config) (s:String) (hs:s∈["input.n","blowup.length"]):
    s∉frameScalars cfg:=by
  intro h
  simp only [frameScalars,List.mem_filter,List.mem_dedup] at h
  obtain ⟨c,hc,hw⟩:=List.mem_flatMap.mp h.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl
  · exact base_input_n cfg c hc hw
  · exact base_blowup_length cfg c hc hw

theorem array_unsaved (cfg:Config) (a:String)
    (ha:a∈["blowup.owner","image.output","weighted.output"]):a∉frameArrays cfg:=by
  intro h
  simp only [frameArrays,List.mem_filter,List.mem_dedup] at h
  obtain ⟨c,hc,hw⟩:=List.mem_flatMap.mp h.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  · exact base_blowup_owner cfg c hc hw
  · exact base_image_output cfg c hc hw
  · exact base_weighted_output cfg c hc hw

theorem dispatch_variable (cs:List Com) (s:String) (hs:s≠"machine.running")
    (h:∀ c∈cs,s∉c.wvars) (i:ℕ):s∉(NativeMachineTrace.dispatch cs i).wvars:=by
  induction cs generalizing i with
  | nil => simpa [NativeMachineTrace.dispatch,Com.wvars] using hs
  | cons c cs ih =>
    simp only [NativeMachineTrace.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem dispatch_array (cs:List Com) (a:String) (h:∀ c∈cs,a∉c.warrs) (i:ℕ):
    a∉(NativeMachineTrace.dispatch cs i).warrs:=by
  induction cs generalizing i with
  | nil => simp [NativeMachineTrace.dispatch,Com.warrs]
  | cons c cs ih =>
    simp only [NativeMachineTrace.dispatch,Com.warrs,List.mem_append,not_or]
    exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem command_variable (cfg:Config) (s:String) (hs:s∈["input.n","blowup.length"]):
    s∉(command cfg).wvars:=by
  have he:s∉excludedScalars:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> decide
  have hphases:=NativeCoreFrame.scalar_unwritten cfg s (scalar_unsaved cfg s hs) he
  have hr:s≠"machine.running" :=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> decide
  have hdriver:=dispatch_variable (phases cfg) s hr hphases 0
  simp only [command,NativeMachineTrace.driver,Com.wvars,List.mem_append,not_or]
  refine ⟨?_,?_,hdriver⟩
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> simp [frameSize,initializeRoot,go,Com.wvars]

theorem command_array (cfg:Config) (a:String)
    (ha:a∈["blowup.owner","image.output","weighted.output"]):a∉(command cfg).warrs:=by
  have he:a≠"recursion.frames" :=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> decide
  have hphases:=NativeCoreFrame.array_unwritten cfg a (array_unsaved cfg a ha) he
  have hdriver:=dispatch_array (phases cfg) a hphases 0
  simpa only [command,frameSize,initializeRoot,go,NativeMachineTrace.driver,Com.warrs,
    List.nil_append,List.not_mem_nil,not_false_eq_true,not_or] using hdriver

end Lax263307Proofs.NativeSourceFrame

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeRootWorkspace

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds

theorem ordinary (cfg:Config) (rootN W originalN:ℕ) (a:String)
    (ha:a∉["recursion.frames","image.output","weighted.output"]):
    extent cfg rootN W originalN a=stride W:=by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ha
  simp only [extent,if_neg ha.1,if_neg ha.2.1,if_neg ha.2.2]

theorem buffer_room (cfg:Config) (rootN W originalN amount:ℕ) (buffers:List String)
    (clean:List.Disjoint buffers ["recursion.frames","image.output","weighted.output"])
    (hamount:amount≤ W):∀ a∈buffers,amount≤ extent cfg rootN W originalN a:=by
  intro a ha
  rw [ordinary cfg rootN W originalN a (List.disjoint_left.mp clean ha)]
  dsimp only [stride]
  omega

theorem frame_extents (cfg:Config) (rootN W originalN:ℕ):
    ∀ a∈frameArrays cfg,extent cfg rootN W originalN a=stride W:=by
  intro a ha
  apply ordinary
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rintro (rfl|rfl|rfl)
  · have h:=ha
    simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne] at h
    exact h.2 rfl
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha

theorem frame_positive (cfg:Config) (W:ℕ):0< frameLength cfg W:=by
  have h:0<(frameScalars cfg).length:=List.length_pos_of_mem (phase_saved cfg)
  dsimp only [frameLength]
  omega

theorem bounds {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (c rootN originalN R W w:ℕ)
    (hK:0< cfg.K) (hb:0< cfg.b) (hroot:rootN≤ R)
    (budget:NativeSelectedBudget.demand cfg p q c R≤ W) (host:hostHeight cfg W≤ w)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel:ℕ) (front:List ℕ)
    (hn:0< n) (hD:0< D) (hk:k≤ n) (hf:fuel≤ 2*R+2)
    (resource:ParameterResources.resource cfg.a cfg.K cfg.b n D≤ R)
    (stack:front.length+frameLength cfg W≤ capacity cfg rootN W):
    NativeSelectedRounds.Bounds cfg p q G D k fuel (stride W) W c R w (extent cfg rootN W originalN) front:=by
  have hdem:=budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hR:R≤ W:=by omega
  have hcert:H p R≤ W:=by change NativeSelectedLP.certificateHeight p R≤ W; omega
  have hroundH:NativeOraclePrecision.roundedHeight p.width R≤ W:=by omega
  have hhost:W≤ w:=by dsimp only [hostHeight] at host; omega
  have hnR:n≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hkR:k≤ R:=hk.trans hnR
  have hrR:level cfg n D≤ R:=by dsimp only [ParameterResources.resource,NativeSelectedRounds.level] at resource ⊢; omega
  have hDR:D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hpR:sparsity cfg.a cfg.K cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hNR:N cfg n D≤ R:=by dsimp only [ParameterResources.resource,N,NativeSelectedRounds.level] at resource ⊢; omega
  have hlR:load cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
  have hiR:limit cfg n D≤ R:=by dsimp only [ParameterResources.resource,limit] at resource ⊢; omega
  have hp:0< sparsity cfg.a cfg.K cfg.b n D:=by
    unfold sparsity targetThreshold
    exact Nat.mul_pos (by decide) (Nat.mul_pos hK (Nat.pow_pos (by omega)))
  have hfloor:0< F cfg n D:=by
    apply Nat.pow_pos
    unfold floorDenominator
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hn) hp) (by omega)
  have hdim:2≤ N cfg n D:=Lax263307Proofs.CoordinateCatalog.catalog_two n (level cfg n D) hn
  have hNpos:0< N cfg n D:=lt_of_lt_of_le (by decide) hdim
  have hFR:F cfg n D≤ R:=by
    have hrad:radiusDenominator cfg.a cfg.K cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at resource; omega
    have hfactor:0<256*N cfg n D*n^2*D^2:=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hNpos) (Nat.pow_pos hn)) (Nat.pow_pos hD)
    have h:=Nat.le_mul_of_pos_left (F cfg n D) hfactor
    apply h.trans
    exact hrad
  have hdepth:RecursionDepth.depth rootN≤ 2*W+2:=by
    have h:=Lax263307Proofs.RecursionDepth.logarithmic_bound rootN
    have hl:Nat.log2 rootN≤ rootN:=Nat.log2_le_self rootN
    omega
  have hcursor:front.length≤ (2*W+2)*frameLength cfg W:=by
    have hcap:=Nat.mul_le_mul_right (frameLength cfg W) hdepth
    dsimp only [capacity] at stack
    omega
  have hnearWord:NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length≤ w:=by
    have hm:NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length≤
        NativeNearResources.wordHeight cfg W W (stride W) ((2*W+2)*frameLength cfg W):=by
      have hbase:5*R+H p R+20≤ 5*W+W+20:=by omega
      have hp:=Nat.mul_le_mul_left 36 (Nat.pow_le_pow_left hbase 4)
      have hprod:=Nat.mul_le_mul (show 2*H p R+1≤ 2*W+1 by omega) (show R+1≤ W+1 by omega)
      have hsquare:=Nat.mul_self_le_mul_self hR
      dsimp only [NativeNearResources.wordHeight]
      omega
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  have hnear:=NativeNearResources.bounds cfg n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    fuel (stride W) (H p R) R w (extent cfg rootN W originalN) front hn hD hp hnR hrR hDR hkR hpR hNR hf
    hnearWord (frame_extents cfg rootN W originalN) (by simpa [extent,frameLength,Nat.add_assoc] using stack)
    (buffer_room cfg rootN W originalN (NativeNearResources.space R) NativeNearResources.buffers (by simp [List.disjoint_left,NativeNearResources.buffers]) (by omega))
  have hproj:=NativeProjectionResources.bounds G D k (level cfg n D) (F cfg n D) R w (NativeSelectedLP.oracleTime p R)
    (extent cfg rootN W originalN) hn hD hfloor hnR hDR hFR hNR
    ((by omega:NativeProjectionResources.wordHeight R≤ W).trans hhost)
    (buffer_room cfg rootN W originalN (NativeProjectionResources.space R (NativeSelectedLP.oracleTime p R)) NativeProjectionResources.buffers (by simp [List.disjoint_left,NativeProjectionResources.buffers]) (by omega))
  have hheight:=NativeSelectedBudget.cost_height p R
  have flowHeight:=NativeFlowBudget.height_bound cfg.b n (load cfg.b n D) k (2*H p R) R
    (NativePolynomialBudget.heightPolynomial p.width) hnR hlR hkR hheight
  have flowWidth:=NativeFlowBudget.width_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.width q.time q.output q.code hnR flowHeight
  have flowSpace:=NativeFlowBudget.space_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.time hnR flowHeight
  have roundedHost:NativeRoundedResources.wordHeight cfg.rounded W R
      (NativeOraclePrecision.roundedHeight p.width R)≤ w:=by
    have hm:NativeRoundedResources.wordHeight cfg.rounded W R
        (NativeOraclePrecision.roundedHeight p.width R)≤ NativeRoundedResources.wordHeight cfg.rounded W W W:=by
      dsimp only [NativeRoundedResources.wordHeight]; gcongr
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  refine ⟨hnR,hkR,hrR,hDR,hFR,hNR,hiR,hproj,hnear,(by omega),?_,?_,?_,?_,?_,roundedHost,?_⟩
  · have hm:NativeCutResources.wordExponent (N cfg n D) (2*H p R+1)≤ NativeCutResources.wordExponent R (2*H p R+1):=by
      dsimp only [NativeCutResources.wordExponent]; gcongr
    have hfar:NativeCutResources.wordExponent R (2*H p R+1)+4≤ W:=by
      change NativeCutResources.wordExponent R (2*NativeSelectedLP.certificateHeight p R+1)+4≤ W
      omega
    exact (Nat.add_le_add_right hm 4).trans (hfar.trans hhost)
  · rw [ordinary cfg rootN W originalN "vm.input" (by decide)]
    dsimp only [stride]
    omega
  · exact flowWidth.trans (by omega)
  · apply buffer_room cfg rootN W originalN _ NativeSeparatorContext.workspace (by simp [List.disjoint_left,NativeSeparatorContext.workspace])
    exact flowSpace.trans (by omega)
  · have hspace:NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)≤ W:=by omega
    dsimp only [NativeRoundedResources.space] at hspace
    omega
  · exact buffer_room cfg rootN W originalN _ NativeRoundedResources.buffers (by simp [List.disjoint_left,NativeRoundedResources.buffers]) (by omega)

end Lax263307Proofs.NativeRootWorkspace

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeLocalTime

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds NativePolynomialEnvelope

theorem row_bound (n r W:ℕ) (hn:n≤ W) (hN:MomentLP.dimension n r≤ W):
    NativeMomentAssembly.rowCount n r≤ rows W:=by
  rw [show NativeMomentAssembly.rowCount n r=2+MomentLP.dimension n r*(n+4) by
    simpa only [NativeMomentInput.M] using NativeMomentInput.row_count_eq n r]
  exact Nat.add_le_add_left (Nat.mul_le_mul hN (Nat.add_le_add_right hn 4)) 2

theorem input_length (n r W:ℕ) (hn:n≤ W) (hN:MomentLP.dimension n r≤ W):
    NativeMomentInput.length n r≤ inputLength W:=by
  have hm:=row_bound n r W hn hN
  dsimp only [NativeMomentInput.length,NativeMomentInput.M,inputLength]
  gcongr

theorem entry_bound (cfg:Config) (n W:ℕ) (hn:n≤ W):NativeNodeTrace.entryCost cfg.a n≤ entry cfg W:=by
  have hs:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have ht:(2*n).size≤ 2*n:=Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [NativeNodeTrace.entryCost,entry]
  omega

theorem large_bound (cfg:Config) (n r W:ℕ) (hn:n≤ W) (hr:r≤ W) (hN:MomentLP.dimension n r≤ W):
    NativeLargeNode.cost cfg.a n r≤ large cfg W:=by
  have hs:n.size≤ n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have ht:(2*n).size≤ 2*n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hm:=row_bound n r W hn hN
  have hi:=input_length n r W hn hN
  have hmoment:NativeMomentSetup.cost n r≤ moment W:=by
    dsimp only [NativeMomentSetup.cost,NativeMomentSetup.catalogCost,NativeMomentSetup.N,moment,catalog]
    gcongr
  have hinput:NativeMomentInput.cost n r≤ inputCost W:=by
    dsimp only [NativeMomentInput.cost,NativeMomentInput.M,inputCost]
    gcongr
  dsimp only [NativeLargeNode.cost,NativeLargeSetup.timeBound,large]
  have hNN:=Nat.mul_self_le_mul_self hN
  nlinarith only [hs,ht,hn,hr,hN,hmoment,hinput,hi,hNN]

theorem component_bound (n H W:ℕ) (hn:n≤ W) (hH:H≤ W):
    NativeComponentDecision.timeBound n (2*H)≤ component W:=by
  simp only [NativeComponentDecision.timeBound,NativeComponentDecision.height,
    NativeQuadraticResources.square_power,Nat.size_pow,component]
  gcongr

theorem part_bound (cfg:Config) (n r H W S:ℕ) (hn:n≤ W) (hN:MomentLP.dimension n r≤ W) (hH:H≤ W):
    NativeCollectionExecution.partCost cfg n r S (2*H) 0≤ part cfg W S:=by
  have hc:=component_bound n H W hn hH
  dsimp only [NativeCollectionExecution.partCost,part]
  simp only [Nat.add_zero]
  gcongr

theorem near_bound (cfg:Config) (n r H W S T:ℕ)
    (hn:n≤ W) (hr:r≤ W) (hN:MomentLP.dimension n r≤ W) (hH:H≤ W) (hT:T≤ W):
    NativeNearExecution.timeBound cfg n r (2^H) S (2*H) 0 T≤ near cfg W S:=by
  have hh:=NativeHeavyResources.cost_bound n r H
  have hbase:n+r+NativeCatalogMetadata.N n r+H+20≤ 4*W+20:=by
    change n+r+MomentLP.dimension n r+H+20≤ 4*W+20
    omega
  have hheavy:NativeHeavySearch.cost (2^H) n r≤ 2000*(4*W+20)^6:=
    hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 6))
  have hp:=part_bound cfg n r H W S hn hN hH
  simp only [NativeNearExecution.timeBound,NativeQuadraticResources.square_power,Nat.size_pow,near]
  gcongr

theorem oracle_bound {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (n D k R W S:ℕ)
    (hR:R≤ W) (hn:n≤ W) (hr:level cfg n D≤ W) (hN:N cfg n D≤ W) (hH:H p R≤ W)
    (hcall:NativeSelectedLP.callCost p R≤ W) (hflow:flowTime cfg p q n D k R≤ W):
    oracleLocal cfg p q n D k R S≤ oracle cfg W S:=by
  have hi:=input_length n (level cfg n D) W hn hN
  have hnear:=near_bound cfg n (level cfg n D) (H p R) W S (flowTime cfg p q n D k R) hn hr hN hH hflow
  simp only [oracleLocal,Nat.size_pow,oracle]
  gcongr

end Lax263307Proofs.NativeLocalTime

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedExecution

open Lax263307 GraphClasses AlgorithmParameters
open NativeCoreMachine NativeRootWorkspace NativeSelectedRounds

abbrev domain (C:GraphClass) (cfg:Config) (rootN W:ℕ):=
  NativeRecursiveDomain.eligible C rootN (frameLength cfg W) (capacity cfg rootN W)

theorem fuel_bound {C:GraphClass} {cfg:Config} {rootN W fuel n k cursor:ℕ} {G:SimpleGraph (Fin n)}
    (hi:domain C cfg rootN W fuel n G k cursor):fuel≤ RecursionDepth.depth rootN:=by
  have h:=hi.2.2.2.2.2.2
  dsimp only [capacity] at h
  exact Nat.le_of_mul_le_mul_right (by omega:fuel*frameLength cfg W≤ RecursionDepth.depth rootN*frameLength cfg W)
    (frame_positive cfg W)

noncomputable def resources {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (q:NativeSelectedNear.Program flow)
    (cfg:Config) (hpc:p.code=cfg.lp) (hpcoeff:p.coeff=cfg.lpWidth)
    (hqc:q.code=cfg.flow) (hqcoeff:q.coeff=cfg.flowWidth)
    (encoded:NativeEncodedLP.Encoded lp) (hsep:NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct:NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK:0< cfg.K) (hb:0< cfg.b)
    (D c rootN originalN R W w:ℕ) (hD:4≤ D) (hroot:rootN≤ R)
    (program:NativeOracleRounds.Program cfg.rounded c)
    (uniform:∀ n,0< n→ n≤ rootN→ ParameterResources.resource cfg.a cfg.K cfg.b n D≤ R)
    (budget:NativeSelectedBudget.demand cfg p q c R≤ W) (host:hostHeight cfg W≤ w):
    NativeNodeExecution.Resources D (stride W) W w (NativeLocalTime.steps W)
      (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) cfg lp flow
      (extent cfg rootN W originalN) (domain C cfg rootN W):=by
  have hdem:=budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hR:R≤ W:=by omega
  have hhost:W≤ w:=by dsimp only [hostHeight] at host; omega
  have rootDepth:RecursionDepth.depth rootN≤ 2*R+2:=by
    have h:=Lax263307Proofs.RecursionDepth.logarithmic_bound rootN
    have hl:=Nat.log2_le_self rootN
    omega
  refine ⟨frame_extents cfg rootN W originalN,?_,?_,?_,?_⟩
  · intro fuel n G _ k cursor hi
    have hres:=uniform n hi.2.1 hi.2.2.1
    exact NativeEntryResources.bounds cfg n D k fuel R w (extent cfg rootN W originalN) hK hi.2.1 (by omega)
      hi.2.2.2.2.1 ((fuel_bound hi).trans rootDepth) hres
      ((by omega:NativeEntryResources.amount cfg R≤ W).trans hhost)
      (buffer_room cfg rootN W originalN _ NativeEntryResources.buffers (by simp [List.disjoint_left,NativeEntryResources.buffers]) (by omega))
  · intro fuel n G _ k cursor hi
    have hnW:n≤ W:=hi.2.2.1.trans (hroot.trans hR)
    refine ⟨by dsimp only [NativeLocalTime.steps]; omega,?_⟩
    exact (NativeLocalTime.entry_bound cfg n W hnW).trans (by dsimp only [NativeLocalTime.time]; omega)
  · intro fuel n G _ k cursor hi small
    have hres:=uniform n hi.2.1 hi.2.2.1
    have hnW:n≤ W:=hi.2.2.1.trans (hroot.trans hR)
    have hentry:=NativeLocalTime.entry_bound cfg n W hnW
    have hsmall:=NativeExhaustiveResources.node_time cfg.a cfg.K cfg.b n D k R hres hi.2.2.2.2.1 small
    have hpow:=Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left (Nat.add_le_add_right hR 2) 3)
    refine ⟨by dsimp only [NativeLocalTime.steps]; omega,?_⟩
    dsimp only [NativeLocalTime.time]
    omega
  · intro fuel n G _ k front hi small hk
    have hres:=uniform n hi.2.1 hi.2.2.1
    have hnR:n≤ R:=hi.2.2.1.trans hroot
    have hnW:n≤ W:=hnR.trans hR
    have hrR:NativeSelectedRounds.level cfg n D≤ R:=by
      dsimp only [ParameterResources.resource,NativeSelectedRounds.level] at hres ⊢; omega
    have hNR:N cfg n D≤ R:=by
      dsimp only [ParameterResources.resource,N,NativeSelectedRounds.level] at hres ⊢; omega
    have hlR:load cfg.b n D≤ R:=by dsimp only [ParameterResources.resource] at hres; omega
    have hiR:limit cfg n D≤ R:=by dsimp only [ParameterResources.resource,limit] at hres ⊢; omega
    have hstack:front.length+frameLength cfg W≤ capacity cfg rootN W:=by
      have h:=hi.2.2.2.2.2.2
      have hm:frameLength cfg W≤ (fuel+1)*frameLength cfg W:=Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hbounds:=NativeRootWorkspace.bounds cfg p q c rootN originalN R W w hK hb hroot budget host G
      D k fuel front hi.2.1 (by omega) hk (by have hf:=(fuel_bound hi).trans rootDepth; omega) hres hstack
    let childSteps:=NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) fuel
    let childTime:=NativeRecursionBudget.work (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) fuel
    have rounds:=NativeSelectedRounds.rounds hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep correct hK hb G
      D k fuel (stride W) W c R w rootN (capacity cfg rootN W) childSteps childTime
      (extent cfg rootN W originalN) front hi (by omega) hD (by omega) program hbounds
    refine
      { M:=2^(100*(R+1))
        farM:=2^(2*H p R+1)
        nearM:=2^H p R
        costH:=2*H p R
        T:=R+1
        space:=space cfg p q n D k R
        oracleTime:=NativeSelectedLP.oracleTime p R
        callCost:=NativeSelectedLP.callCost p R
        flowTime:=flowTime cfg p q n D k R
        c:=c
        roundH:=NativeOraclePrecision.roundedHeight p.width R
        oracleLocal:=oracleLocal cfg p q n D k R (stride W)
        roundCost:=roundCost cfg p c R
        data:=rounds
        steps:= ?_
        time:= ?_
        branching:= ?_ }
    · have hmul:=Nat.mul_le_mul (show 5*(n+1)+7≤ 5*(W+1)+7 by omega) (hiR.trans hR)
      exact Nat.add_le_add_left hmul 2
    · have horacle:=NativeLocalTime.oracle_bound cfg p q n D k R W (stride W) hR hnW (hrR.trans hR) (hNR.trans hR)
        (by change NativeSelectedLP.certificateHeight p R≤ W; omega) (by omega)
        (NativeSelectedBudget.flow_time cfg p q c R W n D k hnR hlR (hk.trans hnR) budget)
      have hround:roundCost cfg p c R≤ W:=by omega
      have hmul:=Nat.mul_le_mul (Nat.add_le_add horacle hround) (hiR.trans hR)
      have hentry:=NativeLocalTime.entry_bound cfg n W hnW
      have hlarge:=NativeLocalTime.large_bound cfg n (NativeSelectedRounds.level cfg n D) W hnW (hrR.trans hR) (hNR.trans hR)
      change NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (NativeSelectedRounds.level cfg n D)+2+
        (oracleLocal cfg p q n D k R (stride W)+roundCost cfg p c R)*limit cfg n D≤ NativeLocalTime.time cfg W (stride W)
      dsimp only [NativeLocalTime.time]
      omega
    · exact Nat.mul_le_mul (Nat.add_le_add_right hnW 1) (hiR.trans hR)

end Lax263307Proofs.NativeSelectedExecution

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeCoreOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs NativeCoreMachine

theorem instruction (i:Lax808846.Ram.Instr):(RamVirtualProgram.instruction i).NoWrite:=by
  cases i with
  | set x0 x1 => change (RamVirtualProgram.instruction (.set 0 0)).NoWrite; decide
  | load x0 x1 => change (RamVirtualProgram.instruction (.load 0 0)).NoWrite; decide
  | store x0 x1 => change (RamVirtualProgram.instruction (.store 0 0)).NoWrite; decide
  | add x0 x1 x2 => change (RamVirtualProgram.instruction (.add 0 0 0)).NoWrite; decide
  | sub x0 x1 x2 => change (RamVirtualProgram.instruction (.sub 0 0 0)).NoWrite; decide
  | mul x0 x1 x2 => change (RamVirtualProgram.instruction (.mul 0 0 0)).NoWrite; decide
  | div x0 x1 x2 => change (RamVirtualProgram.instruction (.div 0 0 0)).NoWrite; decide
  | and x0 x1 x2 => change (RamVirtualProgram.instruction (.and 0 0 0)).NoWrite; decide
  | shiftl x0 x1 x2 => change (RamVirtualProgram.instruction (.shiftl 0 0 0)).NoWrite; decide
  | not x0 x1 => change (RamVirtualProgram.instruction (.not 0 0)).NoWrite; decide
  | jump x0 => change (RamVirtualProgram.instruction (.jump 0)).NoWrite; decide
  | jzero x0 x1 => change (RamVirtualProgram.instruction (.jzero 0 0)).NoWrite; decide
  | jeof x0 => change (RamVirtualProgram.instruction (.jeof 0)).NoWrite; decide
  | inputLength x0 => change (RamVirtualProgram.instruction (.inputLength 0)).NoWrite; decide
  | inputLoad x0 x1 => change (RamVirtualProgram.instruction (.inputLoad 0 0)).NoWrite; decide
  | halt  => change (RamVirtualProgram.instruction (.halt )).NoWrite; decide
  | read x0 => change (RamVirtualProgram.instruction (.read 0)).NoWrite; decide
  | write x0 => change (RamVirtualProgram.instruction (.write 0)).NoWrite; decide

theorem virtual_dispatch (p:Lax808846.Ram.Program) (i:ℕ):(RamVirtualProgram.dispatch p i).NoWrite:=by
  induction p generalizing i with
  | nil => change RamVirtualProgram.stop.NoWrite; decide
  | cons x xs ih => exact ⟨instruction x,ih (i+1)⟩

theorem virtual (p:Lax808846.Ram.Program):(RamVirtualProgram.execute p).NoWrite:=by
  exact ⟨by decide,by decide,virtual_dispatch p 0⟩

theorem polynomial (cs:List ℕ):(RamPolynomial.command cs).NoWrite:=by
  induction cs with
  | nil => decide
  | cons c cs ih => exact ⟨ih,trivial⟩

theorem call (p:Lax808846.Ram.Program) (cs:List ℕ):(NativeOracleCalls.command p cs).NoWrite:=by
  exact ⟨⟨by decide,trivial,polynomial cs,trivial,by decide⟩,virtual p⟩

theorem projection (p:Lax808846.Ram.Program) (cs:List ℕ):
    (NativeProjectionOracle.command p cs).NoWrite:=by
  exact ⟨⟨by decide,call p cs⟩,by decide,by decide⟩

theorem cut_callback (p:Lax808846.Ram.Program) (cs:List ℕ):
    (NativeSeparatorContext.callback p cs).NoWrite:=by
  exact ⟨by decide,⟨by decide,call p cs⟩,by decide⟩

theorem cut_loop (c:Com) (h:c.NoWrite):(NativeCutLoop.command c).NoWrite:=by
  simp only [NativeCutLoop.command,NativeCutLoop.step,NativeCutLoop.branch,Com.NoWrite,h,true_and,and_true]
  decide

theorem separator (p:Lax808846.Ram.Program) (cs:List ℕ):
    (NativeSeparatorOutput.command p cs).NoWrite:=by
  exact ⟨by decide,cut_loop _ (cut_callback p cs),by decide⟩

theorem rounded (p:Lax808846.Ram.Program):(NativeRoundedControl.command p 4 14).NoWrite:=by
  exact ⟨trivial,⟨by decide,⟨by decide,virtual p⟩,by decide⟩,by decide⟩

theorem save_arrays (as:List String):(NativeFrameBuffers.save as).NoWrite:=by
  induction as with
  | nil => decide
  | cons a as ih =>
    refine ⟨⟨trivial,?_⟩,ih⟩
    change (NativeBlockAppend.command "" "recursion.frames").NoWrite
    decide

theorem save_scalars (ss:List String):(NativeFrameScalars.save ss).NoWrite:=by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    change (RamWordBuffer.append "recursion.frames" "stack.words" (.lit 0)).NoWrite∧ (NativeFrameScalars.save ss).NoWrite
    exact ⟨by decide,ih⟩

theorem restore_arrays (as:List String):(NativeFrameBufferRestore.command as).NoWrite:=by
  induction as with
  | nil => decide
  | cons a as ih =>
    refine ⟨⟨trivial,?_⟩,ih⟩
    change (NativeBlockRestore.command "").NoWrite
    decide

theorem restore_scalars (ss:List String):(NativeFrameRestore.command ss).NoWrite:=by
  induction ss with
  | nil => decide
  | cons s ss ih => exact ⟨⟨trivial,trivial⟩,ih⟩

theorem child_call (arrays scalars:List String):(NativeChildCall.command arrays scalars 1 12).NoWrite:=by
  exact ⟨trivial,⟨save_arrays arrays,save_scalars scalars⟩,by decide,by decide⟩

theorem stack_return (arrays scalars:List String):(NativeStackReturn.command arrays scalars 15).NoWrite:=by
  exact ⟨trivial,⟨trivial,trivial⟩,restore_arrays arrays,restore_scalars scalars⟩

theorem phase (cfg:Config) (c:Com) (hc:c∈phases cfg):c.NoWrite:=by
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change (NativeNodeDispatch.command 0 0 0 2 3 14).NoWrite; decide
  · decide
  · change ((NativeLargeNode.command 0 0 0).seq (go 4)).NoWrite; decide
  · exact ⟨by decide,projection cfg.lp cfg.lpWidth,trivial⟩
  · decide
  · decide
  · decide
  · exact ⟨separator cfg.flow cfg.flowWidth,by decide⟩
  · decide
  · decide
  · exact ⟨by decide,child_call (frameArrays cfg) (frameScalars cfg)⟩
  · decide
  · exact rounded cfg.rounded
  · exact stack_return (frameArrays cfg) (frameScalars cfg)
  · decide

theorem dispatch (cs:List Com) (h:∀ c∈cs,c.NoWrite) (i:ℕ):
    (NativeMachineTrace.dispatch cs i).NoWrite:=by
  induction cs generalizing i with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem command (cfg:Config):(NativeCoreMachine.command cfg).NoWrite:=by
  exact ⟨trivial,by decide,dispatch (phases cfg) (phase cfg) 0⟩

end Lax263307Proofs.NativeCoreOutput

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeUnweightedExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 GraphClasses
open NativeCoreMachine NativeRootWorkspace

theorem guards (cfg:Config) (n R W w:ℕ) (hn:n≤ R) (hR:R≤ W) (hw:hostHeight cfg W≤ w):
    stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10<2^w∧
    n+RecursionDepth.depth n+20<2^w∧ 2^n<2^w:=by
  have hA:(frameArrays cfg).length≤ stride W*(frameArrays cfg).length:=Nat.le_mul_of_pos_left _ (by dsimp only [stride]; omega)
  have hframe:frameLength cfg W≤ (2*W+2)*frameLength cfg W:=Nat.le_mul_of_pos_left _ (by omega)
  have hdep:=Lax263307Proofs.RecursionDepth.logarithmic_bound n
  have hlog:=Nat.log2_le_self n
  have hhost:=hw
  dsimp only [hostHeight,NativeNearResources.wordHeight,frameLength,stride] at hhost hA hframe
  have hwidth:n< w:=by omega
  refine ⟨?_,?_,Nat.pow_lt_pow_right (by decide) hwidth⟩
  · exact (by dsimp only [stride]; omega:
      stride W*(frameArrays cfg).length+(frameScalars cfg).length+stride W+(frameArrays cfg).length+10≤ w).trans_lt Nat.lt_two_pow_self
  · exact (by omega:n+RecursionDepth.depth n+20≤ w).trans_lt Nat.lt_two_pow_self

theorem command_spec {C:GraphClass} (hereditary:IsHereditary C)
    {lp flow:List ℕ→ List ℕ} (p:NativeSelectedLP.Program lp) (q:NativeSelectedNear.Program flow)
    (cfg:Config) (hpc:p.code=cfg.lp) (hpcoeff:p.coeff=cfg.lpWidth)
    (hqc:q.code=cfg.flow) (hqcoeff:q.coeff=cfg.flowWidth)
    (encoded:NativeEncodedLP.Encoded lp) (hsep:NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct:NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK:0< cfg.K) (hb:0< cfg.b)
    {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG:G∈C n) (hn:0< n)
    (D c originalN R W w:ℕ) (hD:4≤ D) (hnR:n≤ R)
    (program:NativeOracleRounds.Program cfg.rounded c)
    (uniform:∀ m,0< m→ m≤ n→ ParameterResources.resource cfg.a cfg.K cfg.b m D≤ R)
    (budget:NativeSelectedBudget.demand cfg p q c R≤ W) (host:hostHeight cfg W≤ w):
    Spec (2^w) (NativeCoreExecution.Input (2^w) D (RecursionDepth.depth n) (stride W) W G (extent cfg n W originalN))
      (NativeCoreMachine.command cfg)
      (fun σ τ => NativeCoreExecution.Root (2^w) D (stride W) W cfg G (extent cfg n W originalN) τ∧
        NativeRootTrace.Answer (RecursiveAlgorithm.solve lp flow cfg.a cfg.K cfg.b D G) τ∧
        τ.vars "input.n"=σ.vars "input.n" ∧ τ.vars "blowup.length"=σ.vars "blowup.length" ∧
        τ.arrs "blowup.owner"=σ.arrs "blowup.owner" ∧ τ.out=σ.out) (cost cfg n W):=by
  have resources:=NativeSelectedExecution.resources hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep correct hK hb
    D c n originalN R W w hD hnR program uniform budget host
  have hdem:=budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hguards:=guards cfg n R W w hnR (by omega) host
  have core:=NativeCoreExecution.command_spec D (RecursionDepth.depth n) (stride W) W w
    (NativeLocalTime.steps W) (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W)
    cfg G lp flow (extent cfg n W originalN) (NativeSelectedExecution.domain C cfg n W) resources
    (fun k hk hkn => NativeRecursiveDomain.root G hG hn (by rfl) k hk hkn)
    hguards.1 hguards.2.1 hguards.2.2
  intro σ hi
  obtain ⟨τ,rr,post⟩:=core σ hi
  exact ⟨τ,rr,post.1,post.2,
    rr.frame_var _ (NativeSourceFrame.command_variable cfg _ (by simp)),
    rr.frame_var _ (NativeSourceFrame.command_variable cfg _ (by simp)),
    rr.frame_arr _ (NativeSourceFrame.command_array cfg _ (by simp)),rr.out_eq (NativeCoreOutput.command cfg)⟩

end Lax263307Proofs.NativeUnweightedExecution

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass},
  Lax263307.GraphClasses.IsHereditary C→
    ∀ {lp flow:List Nat→ List Nat} (p:Lax263307Proofs.NativeSelectedLP.Program lp)
      (q:Lax263307Proofs.NativeSelectedNear.Program flow) (cfg:Lax263307Proofs.NativeCoreMachine.Config),
      @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedLP.Program.code lp p) cfg.lp→
        @Eq (List Nat) (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp p) cfg.lpWidth→
          @Eq Lax808846.Ram.Program (@Lax263307Proofs.NativeSelectedNear.Program.code flow q) cfg.flow→
            @Eq (List Nat) (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow q) cfg.flowWidth→
              Lax263307Proofs.NativeEncodedLP.Encoded lp→
                Lax263307Proofs.NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b→
                  Lax263307Proofs.NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b→
                    Nat.lt ((0:Nat)) cfg.K→
                      Nat.lt ((0:Nat)) cfg.b→
                        ∀ {n:Nat} (G:SimpleGraph (Fin n))
                          [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
                          @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n)))
                              (@Set.instMembership (SimpleGraph (Fin n))) (C n) G→
                            Nat.lt ((0:Nat)) n→
                              ∀ (D c originalN R W w:Nat),
                                Nat.le ((4:Nat)) D→
                                  Nat.le n R→
                                    Lax263307Proofs.NativeOracleRounds.Program cfg.rounded c→
                                      (∀ (m:Nat),
                                          Nat.lt ((0:Nat))
                                              m→
                                            Nat.le m n→
                                              Nat.le
                                                (Lax263307.ParameterResources.resource cfg.a cfg.K cfg.b m D) R)→
                                        Nat.le
                                            (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R) W→
                                          Nat.le (Lax263307Proofs.NativeRootWorkspace.hostHeight cfg W)
                                              w→
                                            Lax808846Proofs.Reasoning.Spec
                                              (@HPow.hPow Nat Nat Nat
                                                (@instHPow Nat Nat
                                                  (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                ((2:Nat)) w)
                                              (@Lax263307Proofs.NativeCoreExecution.Input n
                                                (@HPow.hPow Nat Nat Nat
                                                  (@instHPow Nat Nat
                                                    (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                  ((2:Nat)) w)
                                                D (Lax263307.RecursionDepth.depth n)
                                                (Lax263307Proofs.NativeRootWorkspace.stride W) W G inst
                                                (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN))
                                              (Lax263307Proofs.NativeCoreMachine.command cfg)
                                              (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                                                And
                                                  (@Lax263307Proofs.NativeCoreExecution.Root n
                                                    (@HPow.hPow Nat Nat Nat
                                                      (@instHPow Nat Nat
                                                        (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                                      ((2:Nat)) w)
                                                    D (Lax263307Proofs.NativeRootWorkspace.stride W) W cfg G inst
                                                    (Lax263307Proofs.NativeRootWorkspace.extent cfg n W originalN) τ)
                                                  (And
                                                    (@Lax263307Proofs.NativeRootTrace.Answer n
                                                      (@Lax263307.RecursiveAlgorithm.solve n lp flow cfg.a cfg.K cfg.b D
                                                        G inst)
                                                      τ)
                                                    (And (@Eq Nat (τ.vars "input.n") (σ.vars "input.n"))
                                                      (And (@Eq Nat (τ.vars "blowup.length") (σ.vars "blowup.length"))
                                                        (And
                                                          (@Eq (List Nat) (τ.arrs "blowup.owner")
                                                            (σ.arrs "blowup.owner"))
                                                          (@Eq (List Nat) τ.out σ.out))))))
                                              (Lax263307Proofs.NativeUnweightedExecution.cost cfg n W):= @Lax263307Proofs.NativeUnweightedExecution.command_spec
