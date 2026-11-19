-- Prove2me | solution 1 for Lax109476Proofs.RamUniformSolver.exists_exact_polynomial_time_solver
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:37.956238+00:00
-- url     : https://prove2.me/submissions/0199de47-a789-4fa9-b5b0-a9418394a377

import Mathlib.Tactic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax808846Proofs_Simulation_compileProgram_runsTo
import Theorems.Thm_Lax109476Proofs_RamUniformSolverBounds_width_polynomial
import Theorems.Thm_Lax109476Proofs_RamUniformSolverBounds_cost_polynomial
import Theorems.Thm_Lax109476Proofs_RamSolverTotalExecution_solve_spec_native
import Theorems.Thm_Lax109476Proofs_RamSolverCanonicalExecution_solve_spec_native

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

namespace Lax109476Proofs.RamSolverTotalExecution
end Lax109476Proofs.RamSolverTotalExecution
theorem Lax109476Proofs.RamSolverTotalExecution.solve_spec:∀ (xs:List Nat) (w:Nat),
  LE.le (Lax109476Proofs.RamUniformSolverBounds.wordWidth (Lax759944.BinaryWordEncoding.bitSize xs)) w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (Lax109476Proofs.RamSolverTotalExecution.Input
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)
        xs)
      Lax109476Proofs.RamExactSolverProgram.solve (Lax109476Proofs.RamSolverTotalExecution.Result xs)
      (Lax109476Proofs.RamUniformSolverBounds.instructionBound (Lax759944.BinaryWordEncoding.bitSize xs)):= @Lax109476Proofs.RamSolverTotalExecution.solve_spec_native
namespace Lax109476Proofs.RamSolverCanonicalExecution
end Lax109476Proofs.RamSolverCanonicalExecution
theorem Lax109476Proofs.RamSolverCanonicalExecution.solve_spec:∀ (m n w:Nat) (P:Lax109476.LinearProgram.Program Rat m n),
  LE.le
      (Lax109476Proofs.RamUniformSolverBounds.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (@Lax109476Proofs.RamSolverCanonicalExecution.Input m n
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)
        P)
      Lax109476Proofs.RamExactSolverProgram.solve (@Lax109476Proofs.RamSolverFinish.Result m n P)
      (Lax109476Proofs.RamUniformSolverBounds.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))):= @Lax109476Proofs.RamSolverCanonicalExecution.solve_spec_native

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

theorem BigStep.unique {c:Com} {σ σ₁ σ₂:Env} {k₁ k₂:ℕ}
    (h₁:BigStep c σ σ₁ k₁) (h₂:BigStep c σ σ₂ k₂):σ₁=σ₂∧ k₁=k₂:=by
  induction h₁ generalizing σ₂ k₂ with
  | skip => cases h₂; exact ⟨rfl,rfl⟩
  | assign h => cases h₂ with
    | assign h' => rw [h] at h'; cases h'; exact ⟨rfl,rfl⟩
  | store hi he _ => cases h₂ with
    | store hi' he' _ =>
      rw [hi] at hi'; rw [he] at he'; cases hi'; cases he'; exact ⟨rfl,rfl⟩
  | seq _ _ ih ih' => cases h₂ with
    | seq h h' =>
      obtain ⟨rfl,rfl⟩:=ih h
      obtain ⟨rfl,rfl⟩:=ih' h'
      exact ⟨rfl,rfl⟩
  | ite_true hb _ ih => cases h₂ with
    | ite_true hb' h => obtain ⟨rfl,rfl⟩:=ih h; exact ⟨rfl,rfl⟩
    | ite_false hb' _ => rw [hb] at hb'; exact absurd hb' (by simp)
  | ite_false hb _ ih => cases h₂ with
    | ite_true hb' _ => rw [hb] at hb'; exact absurd hb' (by simp)
    | ite_false hb' h => obtain ⟨rfl,rfl⟩:=ih h; exact ⟨rfl,rfl⟩
  | while_true hb _ _ ih ih' => cases h₂ with
    | while_true hb' h h' =>
      obtain ⟨rfl,rfl⟩:=ih h
      obtain ⟨rfl,rfl⟩:=ih' h'
      exact ⟨rfl,rfl⟩
    | while_false hb' => rw [hb] at hb'; exact absurd hb' (by simp)
  | while_false hb => cases h₂ with
    | while_true hb' _ _ => rw [hb] at hb'; exact absurd hb' (by simp)
    | while_false hb' => exact ⟨rfl,rfl⟩
  | read h => cases h₂ with
    | read h' => rw [h] at h'; cases h'; exact ⟨rfl,rfl⟩
  | write h => cases h₂ with
    | write h' => rw [h] at h'; cases h'; exact ⟨rfl,rfl⟩

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

namespace Lax808846Proofs.Transfer

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning

structure Solves (L:Layout) (c:Com) (D:Set (List ℕ)) (f:List ℕ→ List ℕ)
    (B K:List ℕ→ ℕ):Prop where

  ok:Com.Ok L c

  inp:∀ x∈ D, ∀ v∈ x,v < B x

  run:∀ x∈ D, ∃ (ext:String→ ℕ) (σ':Env),
    Run (B x) c (initEnv ext x) σ' (K x)∧ σ'.out=f x

theorem fitsWords_of_max_le {L:Layout} {B w:ℕ} (h1:1 < B)
    (h:max B (L.span B)≤ 2 ^ w):L.FitsWords B w:=
  ⟨h1,le_trans (le_max_left _ _) h,le_trans (le_max_right _ _) h⟩

end Lax808846Proofs.Transfer

end

section

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence

def trajectory {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ):
    ℕ→ Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)
  | 0 => (1,0)
  | k + 1 => nextState A b k (trajectory A b k)

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

end

section

namespace Lax109476Proofs.RationalReconstruction

def convergent:ℚ→ ℕ→ ℚ
  | a,0 => Int.floor a
  | a,k + 1 => Int.floor a + (convergent (Int.fract a)⁻¹ k)⁻¹

def reconstruct (l u:ℚ) (B:ℕ):Option ℚ:=
  ((List.range (2 * u.den.size + 1)).map (convergent u)).find?
    (fun q => decide (q.den≤ B∧ l≤ q∧ q≤ u))

end Lax109476Proofs.RationalReconstruction

end

section

namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

def bisect (query:ℚ→ Bool):ℚ→ ℚ→ ℕ→ ℚ × ℚ
  | l,u,0 => (l,u)
  | l,u,k + 1 =>
    let old:=bisect query l u k
    let mid:=(old.1 + old.2) / 2
    if query mid then (old.1,mid) else (mid,old.2)

def steps (B:ℕ):ℕ:=3 * B.size + 2

def minimum (query:ℚ→ Bool) (B:ℕ):Option ℚ:=
  let interval:=bisect query 0 B (steps B)
  reconstruct interval.1 interval.2 B

end Lax109476Proofs.BinaryOptimization

end

section

open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

def coordinateCut {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (t:ℚ):
    Program ℚ (m + 1) n where
  A:=Fin.addCases P.A (fun _ k => if k=j then 1 else 0)
  b:=Fin.addCases P.b (fun _ => t)
  c:=P.c

def coordinateMinimum {m n:ℕ} (P:Program ℚ m n) (j:Fin n) (B:ℕ):Option ℚ:=
  BinaryOptimization.minimum (fun t => RationalFeasibilityDecision.feasible (coordinateCut P j t)) B

end Lax109476Proofs.CoordinateOptimization

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates

def fixedPrefix {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ):
    Program ℚ (m + (n + n)) n where
  A:=Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j=i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j=i then -1 else 0 else 0))
  b:=Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c:=P.c

end Lax109476Proofs.LexicographicMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.PointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open LexicographicMinima CoordinateOptimization

def recoverPrefix {m n:ℕ} (P:Program ℚ m n) (B:ℕ):
    ℕ→ Option (Fin n→ ℚ)
  | 0 => some 0
  | k + 1 =>
    (recoverPrefix P B k).bind (fun old =>
      if h:k < n then
        (coordinateMinimum (fixedPrefix P old k) ⟨k,h⟩ B).map
          (fun v => Function.update old ⟨k,h⟩ v)
      else some old)

def recover {m n:ℕ} (P:Program ℚ m n) (B:ℕ):Option (Fin n→ ℚ):=
  recoverPrefix P B n

end Lax109476Proofs.PointRecovery

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateSystems

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates

def farkasMatrix {m n:ℕ} (P:Program ℤ m n):(Fin n ⊕ Unit)→ Fin m→ ℤ:=
  Sum.elim (fun j i => -P.A i j) (fun _ => P.b)

def farkasBound {n:ℕ}:(Fin n ⊕ Unit)→ ℤ:=
  Sum.elim (fun _ => 0) (fun _ => -1)

end Lax109476Proofs.CertificateSystems

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateSearch

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates CertificateSystems

def farkasRows (n:ℕ):(Fin n ⊕ Unit) ≃ Fin (n + 1):=
  (Equiv.sumCongr (Equiv.refl _) unitFin).trans finSumFinEquiv

end Lax109476Proofs.CertificateSearch

end

section

namespace Lax109476Proofs.CertificateFamilyPrograms

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates CertificateSystems IndexedPointRecovery CertificateSearch

def infeasible {m n:ℕ} (P:Program ℤ m n):Program ℤ (n + 1) m:=
  reindexProgram (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _)

end Lax109476Proofs.CertificateFamilyPrograms

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

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

namespace Fill

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

namespace Lax109476Proofs.WordDecoding

open Lax109476.LinearProgram Lax109476.RationalEncoding

theorem encodeVector_cons (n:ℕ) (q:ℚ) (x:Fin n→ ℚ):
    encodeVector (Fin.cons q x)=encodeRational q ++ encodeVector x:=by
  simp [encodeVector,List.ofFn_succ]

def encodeRows {m n:ℕ} (A:Fin m→ Fin n→ ℚ):List ℕ:=
  (List.ofFn fun i => encodeVector (A i)).flatten

theorem encodeRows_cons {m n:ℕ} (row:Fin n→ ℚ) (rows:Fin m→ Fin n→ ℚ):
    encodeRows (Fin.cons row rows)=encodeVector row ++ encodeRows rows:=by
  simp [encodeRows,List.ofFn_succ]

theorem encodeVector_length (n:ℕ) (x:Fin n→ ℚ):(encodeVector x).length=3 * n:=by
  induction n with
  | zero => simp [encodeVector]
  | succ n ih =>
    rw [← Fin.cons_self_tail x,encodeVector_cons,List.length_append]
    simp only [encodeRational,List.length_cons,List.length_nil]
    rw [ih]
    omega

theorem encodeRows_length (m n:ℕ) (A:Fin m→ Fin n→ ℚ):
    (encodeRows A).length=3 * m * n:=by
  induction m with
  | zero => simp [encodeRows]
  | succ m ih =>
    rw [← Fin.cons_self_tail A,encodeRows_cons,List.length_append,encodeVector_length,ih]
    ring

theorem encodeProgram_rows {m n:ℕ} (P:Program ℚ m n):
    encodeProgram P=m::n::(encodeRows P.A ++ encodeVector P.b ++ encodeVector P.c):=by
  have hrows:(List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational =
      encodeRows P.A:=by
    unfold encodeRows encodeVector
    rw [List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_def,List.map_ofFn]
    rfl
  simp only [encodeProgram,hrows]
  rfl

structure PackedProgram where
  m:ℕ
  n:ℕ
  program:Program ℚ m n

end Lax109476Proofs.WordDecoding

end

section

namespace Lax109476Proofs.WordSolverSize

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax109476.RationalEncoding EncodingSize

theorem length_le_bitSize (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.length_cons,bitSize_cons]; omega

theorem member_size_le {xs:List ℕ} {a:ℕ} (ha:a∈ xs):
    a.size≤ bitSize xs:=by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h:=ih ha; omega

end Lax109476Proofs.WordSolverSize

end

section

namespace Lax109476Proofs.RamDecoder

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamReadHeader RamReadBody RamRationalArrays RamEllipsoidStep RamAdvanceState

def AcceptedHeader (xs:List ℕ):Prop:=2≤ xs.length∧ ValidDimensions xs

theorem encodedHeader_accepted (m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n):
    AcceptedHeader (Lax109476.RationalEncoding.encodeProgram P):=by
  rw [WordDecoding.encodeProgram_rows]
  have hlen:(WordDecoding.encodeRows P.A ++ Lax109476.RationalEncoding.encodeVector P.b ++
      Lax109476.RationalEncoding.encodeVector P.c).length=3 * m * n + 3 * m + 3 * n:=by
    rw [List.length_append,List.length_append,WordDecoding.encodeRows_length,
      WordDecoding.encodeVector_length,WordDecoding.encodeVector_length]
  simp only [AcceptedHeader,ValidDimensions,List.length_cons,List.headD_cons,
    List.tail_cons,List.drop_succ_cons,List.drop_zero]
  omega

end Lax109476Proofs.RamDecoder

end

section

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

def instructionBound (m n S:ℕ):ℕ:=RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound (m + n) n
    (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)

end Lax109476Proofs.RamIntegerFeasibility

end

section

namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep RationalArithmeticBounds

def sizeBound (m n M:ℕ):ℕ:=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M:ℕ):ℕ:=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)

end Lax109476Proofs.RamRecoveryThreshold

end

section

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem view_setVar (f:String→ String) (σ:Env) (x:String) (v:ℕ):
    view f (σ.setVar x v)=(view f σ).setVar x v:=rfl

end Lax109476Proofs.RamArrayRelabel

end

section

namespace Lax109476Proofs.RamDecodedProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBody RamRationalArrays RationalArithmeticBounds

theorem canonicalBound_ge (L:ℕ):L≤ canonicalBound L:=by
  unfold canonicalBound
  omega

end Lax109476Proofs.RamDecodedProgram

end

section

namespace Lax109476Proofs.RamResourcePolynomial

theorem constant (k:ℕ):HasPolynomial (fun _ => k):=by
  unfold HasPolynomial at *
  exact ⟨Polynomial.C k,fun n => by simp⟩

theorem identity:HasPolynomial (fun n => n):=by
  unfold HasPolynomial at *
  exact ⟨Polynomial.X,fun n => by simp⟩

theorem add {f g:ℕ→ ℕ} (hf:HasPolynomial f) (hg:HasPolynomial g):
    HasPolynomial (fun n => f n + g n):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p + q,fun n => by simp [hp,hq]⟩

theorem mul {f g:ℕ→ ℕ} (hf:HasPolynomial f) (hg:HasPolynomial g):
    HasPolynomial (fun n => f n * g n):=by
  unfold HasPolynomial at *
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hg
  exact ⟨p * q,fun n => by simp [hp,hq]⟩

theorem parameter:Lax109476Proofs.RamResourcePolynomial.HasPolynomial Lax109476Proofs.RamCertificateSetup.parameter:=
@Lax109476Proofs.RamResourcePolynomial.mul (fun (x:Nat) => (2:Nat))
  (fun (n:Nat) =>
    Nat.add n ((4:Nat)))
  (Lax109476Proofs.RamResourcePolynomial.constant ((2:Nat)))
  (@Lax109476Proofs.RamResourcePolynomial.add (fun (n:Nat) => n)
    (fun (x:Nat) => (4:Nat))
    Lax109476Proofs.RamResourcePolynomial.identity
    (Lax109476Proofs.RamResourcePolynomial.constant ((4:Nat))))

end Lax109476Proofs.RamResourcePolynomial

end

section

namespace Lax109476Proofs.RamUniformSolverBounds

open RamResourcePolynomial

theorem positive (L:ℕ):0 < wordWidth L:=by unfold wordWidth; omega

end Lax109476Proofs.RamUniformSolverBounds

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax109476Proofs.RamSolverAllocation

open Lax808846Proofs.Imp
open RamSolverWorkspace RamUniformSolverBounds

def splitChars:List Char→ List (List Char)
  | [] => [[]]
  | c::cs => if c='.' then []::splitChars cs else
    match splitChars cs with
    | [] => [[c]]
    | part::parts => (c::part)::parts

def feasibilityLength (m n:ℕ) (group entry:List Char):ℕ:=
  match group,entry with
  | ['q', 'u', 'e', 'r', 'y'], ['A'] => m * n
  | ['q', 'u', 'e', 'r', 'y'], ['b'] => m
  | ['p', 'a', 'd'], ['A'] => (m + 2) * (n + 2)
  | ['p', 'a', 'd'], ['b'] => m + 2
  | ['s', 'e', 'a', 'r', 'c', 'h'], ['r', 'o', 'w', 's'] => ((m + 2) + (n + 2)) * (n + 2)
  | ['s', 'e', 'a', 'r', 'c', 'h'], ['r', 'h', 's'] => (m + 2) + (n + 2)
  | ['e', 'l', 'l'], ['c', 'e', 'n', 't', 'e', 'r'] | ['e', 'l', 'l'], ['u'] | ['e', 'l', 'l'], ['n', 'e', 'x', 't', 'c', 'e', 'n', 't', 'e', 'r'] | ['e', 'l', 'l'], ['n', 'o', 'r', 'm', 'a', 'l'] => n + 2
  | ['e', 'l', 'l'], ['s', 'h', 'a', 'p', 'e'] | ['e', 'l', 'l'], ['n', 'e', 'x', 't', 's', 'h', 'a', 'p', 'e'] => (n + 2) * (n + 2)
  | ['e', 'l', 'l'], ['c', 'o', 'e', 'f', 'f'] => 5
  | _,_ => 0

def decisionLength (m n:ℕ) (group entry:List Char):ℕ:=
  match group,entry with
  | ['l', 'p'], ['A'] | ['i', 'n', 't'], ['A'] => m * n
  | ['l', 'p'], ['b'] | ['i', 'n', 't'], ['b'] => m
  | ['l', 'p'], ['c'] | ['i', 'n', 't'], ['c'] => n
  | _,_ => feasibilityLength m n group entry

def recoveryLength (r s N:ℕ) (group entry:List Char):ℕ:=
  match group,entry with
  | ['c', 'f'], ['s', 't', 'a', 'c', 'k'] => N
  | ['s', 'y', 's', 't', 'e', 'm'], ['A'] => r * s
  | ['s', 'y', 's', 't', 'e', 'm'], ['b'] => r
  | ['p', 'o', 'i', 'n', 't'], ['A'] => (r + r) * (s + r)
  | ['p', 'o', 'i', 'n', 't'], ['b'] => r + r
  | ['p', 'o', 'i', 'n', 't'], ['x'] => s + r
  | _,_ => decisionLength ((r + r) + ((s + r) + (s + r)) + 1) (s + r) group entry

def extent (m n N r s:ℕ) (a:String):ℕ:=
  match splitChars a.toList with
  | [['l', 'p'], ['A'],_] | [['i', 'n', 't'], ['A'],_] => r * s
  | [['l', 'p'], ['b'],_] | [['i', 'n', 't'], ['b'],_] => r
  | [['l', 'p'], ['c'],_] | [['i', 'n', 't'], ['c'],_] => s
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['A'],_] => m * n
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['b'],_] => m
  | [['s', 'o', 'u', 'r', 'c', 'e'], ['c'],_] => n
  | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry,_] | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry] =>
    recoveryLength (m + (n + 2)) (n + m) N group entry
  | [['o', 'p', 't', 'i', 'm', 'a', 'l'], ['d', 'e', 'c', 'i', 's', 'i', 'o', 'n'],group,entry,_] => decisionLength (m + (n + 2)) (n + m) group entry
  | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry,_] | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry] =>
    recoveryLength (n + 1) m N group entry
  | [['i', 'n', 'f', 'e', 'a', 's', 'i', 'b', 'l', 'e'], ['d', 'e', 'c', 'i', 's', 'i', 'o', 'n'],group,entry,_] => decisionLength (n + 1) m group entry
  | [['u', 'n', 'b', 'o', 'u', 'n', 'd', 'e', 'd'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry,_] | [['u', 'n', 'b', 'o', 'u', 'n', 'd', 'e', 'd'], ['r', 'e', 'c', 'o', 'v', 'e', 'r', 'y'],group,entry] =>
    recoveryLength (m + (m + 1)) (n + n) N group entry
  | _ => 0

def ext (xs:List ℕ):String→ ℕ:=extent (xs.headD 0) (xs.tail.headD 0)
  (stackLength (Lax759944.BinaryWordEncoding.bitSize xs))
  (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0)
  (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0)

theorem allocated (m n N r s:ℕ) (tape:List ℕ):
    RamEllipsoidStep.Extents "lp.A" (r * s) (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "lp.b" r (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "lp.c" s (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "int.A" (r * s) (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "int.b" r (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "int.c" s (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "source.A" (m * n) (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "source.b" m (initEnv (extent m n N r s) tape)∧
    RamEllipsoidStep.Extents "source.c" n (initEnv (extent m n N r s) tape)∧
    All m n N (initEnv (extent m n N r s) tape):=by
  simp only [All,Recovery,Decision,RamRecoveryThreshold.Workspace,RamRecoveryQuery.Extent,
    RamFeasibilityQuery.Workspace,RamEllipsoidStep.Workspace,recoveryView,
    RamCertificateDecision.prefixedView,RamArrayRelabel.view]
  repeat' apply And.intro
  all_goals try intro t ht
  all_goals try (simp only [List.mem_cons,List.not_mem_nil,or_false] at ht)
  all_goals try (rcases ht with rfl | rfl | rfl)
  all_goals simp only [initEnv,List.length_replicate]
  all_goals try simp [RamCertificateArrayRelabel.relabel,RamCertificateArrayRelabel.sourceNames]
  all_goals rfl

theorem initialized (xs:List ℕ) (B:ℕ) (hB:∀ v∈ xs.length::xs,v < B):
    RamSolverTotalExecution.Input B xs (initEnv (ext xs) (xs.length::xs)):=by
  have h:=allocated (xs.headD 0) (xs.tail.headD 0) (stackLength (Lax759944.BinaryWordEncoding.bitSize xs))
    (if RamReadHeader.ValidDimensions xs then xs.headD 0 else 0)
    (if RamReadHeader.ValidDimensions xs then xs.tail.headD 0 else 0) (xs.length::xs)
  by_cases hd:RamReadHeader.ValidDimensions xs
  all_goals simp only [hd, ↓reduceIte] at h
  all_goals rcases h with ⟨hA,hb,hc,hIA,hIb,hIc,hSA,hSb,hSc,hAll⟩
  all_goals refine ⟨⟨⟨rfl,hB, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simp only [ext,hd, ↓reduceIte]
  all_goals assumption

end Lax109476Proofs.RamSolverAllocation

end

section

namespace Lax109476Proofs.RamSolverOutputBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax759944.BinaryWordEncoding

theorem output_of_bigStepB {B k:ℕ} {c:Com} {σ τ:Env} (h:BigStepB B c σ τ k):
    (∀ v∈ σ.out,v < B)→ ∀ v∈ τ.out,v < B:=by
  induction h with
  | skip => exact fun h => h
  | assign he => simpa [Env.setVar]
  | store hi he hk => simpa [Env.setArr]
  | seq _ _ ih ih' => exact fun h => ih' (ih h)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun h => ih' (ih h)
  | while_false _ => exact fun h => h
  | read he => simpa [Env.setVar]
  | write he =>
    intro h v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h v hv
    · exact Expr.lt_of_evalB he

theorem output_of_run {B k:ℕ} {c:Com} {σ τ:Env} (h:Run B c σ τ k)
    (hσ:∀ v∈ σ.out,v < B):∀ v∈ τ.out,v < B:=by
  obtain ⟨k',hk',hstep⟩:=h
  exact output_of_bigStepB hstep hσ

theorem input_fits (xs:List ℕ):
    ∀ v∈ xs.length::xs,v < 2 ^ RamUniformSolverBounds.wordWidth (bitSize xs):=by
  let L:=bitSize xs
  let W:=RamUniformSolverBounds.wordWidth L
  have hLW:L≤ W:=by
    have hC:=RamDecodedProgram.canonicalBound_ge L
    dsimp only [W,RamUniformSolverBounds.wordWidth,RamFrontEndTotal.wordWidth,
      RamInitializationTotal.wordWidth,RamDecoder.wordWidth]
    omega
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact ((WordSolverSize.length_le_bitSize xs).trans hLW).trans_lt (Nat.lt_two_pow_self (n:=W))
  · exact (Nat.lt_size_self v).trans_le (Nat.pow_le_pow_right (by decide)
      ((WordSolverSize.member_size_le hv).trans hLW))

end Lax109476Proofs.RamSolverOutputBounds

end

section

namespace Lax109476Proofs.RamTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

def physicalInputs:Set (List ℕ):= {tape | ∃ x,tape=x.length::x}

def layoutAllowance (L:Layout):ℕ:=
  L.temps + 2 + L.scalars.length + L.arrays.length + 1

theorem layout_fits {L:Layout} {v w:ℕ} (hv:0 < v)
    (hw:v + layoutAllowance L≤ w):L.FitsWords (2 ^ v) w:=by
  have hB:1 < 2 ^ v:=Nat.one_lt_pow (ne_of_gt hv) (by decide)
  have hc:layoutAllowance L≤ 2 ^ layoutAllowance L:=Nat.lt_two_pow_self.le
  have hs:max (2 ^ v) (L.span (2 ^ v))≤ 2 ^ (v + layoutAllowance L):=by
    rw [pow_add]
    apply max_le
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · unfold Layout.span
      have hp:1≤ 2 ^ v:=hB.le
      calc
        _≤ (L.temps + 2 + L.scalars.length) * 2 ^ v + L.arrays.length * 2 ^ v:=by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hp) _
        _≤ layoutAllowance L * 2 ^ v:=by unfold layoutAllowance; nlinarith
        _≤ _:=by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ v) hc
  exact fitsWords_of_max_le hB (hs.trans (Nat.pow_le_pow_right (by decide) hw))

theorem ramPolytime_of_solves (L:Layout) (c:Com) (f:List ℕ→ List ℕ)
    (W T:Polynomial ℕ)
    (hW:∀ x,0 < W.eval (bitSize x))
    (hfit:∀ x,FitsInWords (W.eval (bitSize x)) ((x.length::x) ++ f x))
    (h:Solves L c physicalInputs (fun tape => f tape.tail)
      (fun tape => 2 ^ W.eval (bitSize tape.tail))
      (fun tape => T.eval (bitSize tape.tail))):RamPolytime f:=by
  refine ⟨compileProgram L c,W + Polynomial.C (layoutAllowance L),
    Polynomial.C L.const * T + Polynomial.C 1, ?_⟩
  intro x
  simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul]
  constructor
  · intro a ha
    exact (hfit x a ha).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · intro w hw
    obtain ⟨ext,σ', ⟨k,hk,hbs⟩,hout⟩:=h.run (x.length::x) ⟨x,rfl⟩
    have hi:=h.inp (x.length::x) ⟨x,rfl⟩
    simp only [List.tail_cons] at hi hk hbs hout
    obtain ⟨t,ht,hrun⟩:=Lax808846Proofs.Simulation.compileProgram_runsTo
      (layout_fits (hW x) hw) h.ok hi hbs
    exact ⟨t,ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 1),
      by simpa only [hout] using hrun⟩

end Lax109476Proofs.RamTransfer

end

section

namespace Lax109476Proofs.RamAutomaticLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile

def expressionNames:Expr→ List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old:=expressionNames i; (old.1,a::old.2)
  | .bin _ e f => let a:=expressionNames e; let b:=expressionNames f; (a.1 ++ b.1,a.2 ++ b.2)

def conditionNames (b:Cond):List String × List String:=expressionNames (condExpr b)

def commandNames:Com→ List String × List String
  | .skip => ([], [])
  | .assign x e => let a:=expressionNames e; (x::a.1,a.2)
  | .store x i e => let a:=expressionNames i; let b:=expressionNames e; (a.1 ++ b.1,x::(a.2 ++ b.2))
  | .seq c d => let a:=commandNames c; let b:=commandNames d; (a.1 ++ b.1,a.2 ++ b.2)
  | .ite b c d => let a:=conditionNames b; let x:=commandNames c; let y:=commandNames d;
      (a.1 ++ x.1 ++ y.1,a.2 ++ x.2 ++ y.2)
  | .while b c => let a:=conditionNames b; let x:=commandNames c; (a.1 ++ x.1,a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def commandDepth:Com→ ℕ
  | .skip | .read _ => 1
  | .assign _ e | .write e => e.size + 2
  | .store _ i e => max i.size e.size + 2
  | .seq c d => max (commandDepth c) (commandDepth d)
  | .ite b c d => max (condExpr b).size (max (commandDepth c) (commandDepth d)) + 2
  | .while b c => max (condExpr b).size (commandDepth c) + 2

def layout (c:Com):Layout:= ⟨(commandNames c).1, (commandNames c).2,commandDepth c + 2⟩

theorem expression_ok (e:Expr) (L:Layout) (d:ℕ)
    (hv:(expressionNames e).1 ⊆ L.scalars) (ha:(expressionNames e).2 ⊆ L.arrays)
    (hd:d + e.size < L.temps):Expr.Ok L e d:=by
  induction e generalizing d with
  | lit v => trivial
  | var x => exact hv (by simp [expressionNames])
  | get a i ih =>
    refine ⟨ha (by simp [expressionNames]),ih d
      (by simpa [expressionNames] using hv)
      (fun x hx => ha (by simp [expressionNames,hx])) ?_, ?_⟩
    all_goals simp only [Expr.size] at hd; omega
  | bin op e f ihe ihf =>
    have hve:(expressionNames e).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hvf:(expressionNames f).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hae:(expressionNames e).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    have haf:(expressionNames f).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    simp only [Expr.Ok]
    exact ⟨ihf d hvf haf (by simp only [Expr.size] at hd; omega),
      ihe (d + 1) hve hae (by simp only [Expr.size] at hd; omega),
      by simp only [Expr.size] at hd; omega⟩

theorem command_ok (c:Com) (L:Layout)
    (hv:(commandNames c).1 ⊆ L.scalars) (ha:(commandNames c).2 ⊆ L.arrays)
    (hd:commandDepth c < L.temps):Com.Ok L c:=by
  induction c with
  | skip => trivial
  | read x => exact hv (by simp [commandNames])
  | assign x e =>
    refine ⟨hv (by simp [commandNames]),expression_ok e L 0
      (fun x hx => hv (by simp [commandNames,hx])) (by simpa [commandNames] using ha) ?_⟩
    simp only [commandDepth] at hd; omega
  | store a i e =>
    refine ⟨ha (by simp [commandNames]),expression_ok i L 0
      (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      expression_ok e L 1 (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | write e =>
    refine ⟨expression_ok e L 0 hv ha ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | seq c d ihc ihd =>
    refine ⟨ihc (fun x hx => hv (by simp [commandNames,hx]))
      (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | ite b c d ihc ihd =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ihc (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | «while» b c ih =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ih (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega

theorem layout_ok (c:Com):Com.Ok (layout c) c:=
  command_ok c (layout c) (fun _ h => h) (fun _ h => h) (by simp [layout])

end Lax109476Proofs.RamAutomaticLayout

end

section

namespace Lax109476Proofs.RamUniformSolver

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Transfer

theorem run_exists (xs:List ℕ):∃ τ,
    Run (2 ^ RamUniformSolverBounds.wordWidth (bitSize xs)) RamExactSolverProgram.solve
      (initEnv (RamSolverAllocation.ext xs) (xs.length::xs)) τ
      (RamUniformSolverBounds.instructionBound (bitSize xs)):=by
  obtain ⟨τ,hr,_⟩:=RamSolverTotalExecution.solve_spec xs _ le_rfl _
    (RamSolverAllocation.initialized xs _ (RamSolverOutputBounds.input_fits xs))
  exact ⟨τ,hr⟩

noncomputable def finalEnv (xs:List ℕ):Env:=Classical.choose (run_exists xs)
noncomputable def solve (xs:List ℕ):List ℕ:=(finalEnv xs).out

theorem run_spec (xs:List ℕ):
    Run (2 ^ RamUniformSolverBounds.wordWidth (bitSize xs)) RamExactSolverProgram.solve
      (initEnv (RamSolverAllocation.ext xs) (xs.length::xs)) (finalEnv xs)
      (RamUniformSolverBounds.instructionBound (bitSize xs)):=Classical.choose_spec (run_exists xs)

theorem polynomial_time:RamPolytime solve:=by
  have hWidth:=RamUniformSolverBounds.width_polynomial
  have hCost:=RamUniformSolverBounds.cost_polynomial
  unfold RamResourcePolynomial.HasPolynomial at hWidth hCost
  obtain ⟨W,hW⟩:=hWidth
  obtain ⟨T,hT⟩:=hCost
  apply RamTransfer.ramPolytime_of_solves (_root_.Lax109476Proofs.RamAutomaticLayout.layout RamExactSolverProgram.solve)
    RamExactSolverProgram.solve solve W T
  · intro xs; rw [hW]; exact RamUniformSolverBounds.positive _
  · intro xs v hv
    rw [hW]
    simp only [List.mem_append] at hv
    rcases hv with hv | hv
    · exact RamSolverOutputBounds.input_fits xs v hv
    · exact RamSolverOutputBounds.output_of_run (run_spec xs) (by simp [initEnv]) v hv
  · refine ⟨RamAutomaticLayout.layout_ok _, ?_, ?_⟩
    · rintro tape ⟨xs,rfl⟩
      simp only [List.tail_cons]
      rw [hW]
      exact RamSolverOutputBounds.input_fits xs
    · rintro tape ⟨xs,rfl⟩
      refine ⟨RamSolverAllocation.ext xs,finalEnv xs, ?_,rfl⟩
      simp only [List.tail_cons]
      rw [hW,hT]
      exact run_spec xs

theorem initialized_canonical (m n:ℕ) (P:Program ℚ m n):
    RamSolverCanonicalExecution.Input
      (2 ^ RamUniformSolverBounds.wordWidth (bitSize (encodeProgram P))) P
      (initEnv (RamSolverAllocation.ext (encodeProgram P)) ((encodeProgram P).length::encodeProgram P)):=by
  have h:=RamSolverAllocation.initialized (encodeProgram P) _ (RamSolverOutputBounds.input_fits _)
  have hdim:=(RamDecoder.encodedHeader_accepted m n P).2
  have hm:(encodeProgram P).headD 0=m:=by rw [WordDecoding.encodeProgram_rows]; rfl
  have hn:(encodeProgram P).tail.headD 0=n:=by rw [WordDecoding.encodeProgram_rows]; rfl
  rcases h with ⟨⟨hDecoder,hIntA,hIntb,hIntc⟩,hSourceA,hSourceb,hSourcec,hAll⟩
  simp only [if_pos hdim,hm,hn] at hIntA hIntb hIntc hSourceA hSourceb hSourcec hAll
  exact ⟨⟨hDecoder,hIntA,hIntb,hIntc⟩,hSourceA,hSourceb,hSourcec,hAll⟩

theorem correct (m n:ℕ) (P:Program ℚ m n):∃ certificate:Certificate m n,
    solve (encodeProgram P)=encodeCertificate certificate∧ IsValidCertificate P certificate:=by
  obtain ⟨τ,hr,cert,hout,hvalid⟩:=RamSolverCanonicalExecution.solve_spec m n _ P le_rfl _
    (initialized_canonical m n P)
  obtain ⟨_,_,hbig⟩:=hr.bigStep
  obtain ⟨_,_,hactual⟩:=(run_spec (encodeProgram P)).bigStep
  have heq:=(BigStep.unique hbig hactual).1
  refine ⟨cert, ?_,hvalid⟩
  change (finalEnv (encodeProgram P)).out=encodeCertificate cert
  rw [← heq]
  simpa [initEnv] using hout

theorem exists_exact_polynomial_time_solver:
    ∃ solve:List ℕ→ List ℕ,RamPolytime solve∧
      ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
        solve (encodeProgram P)=encodeCertificate certificate∧ IsValidCertificate P certificate:=
  ⟨solve,polynomial_time,correct⟩

end Lax109476Proofs.RamUniformSolver

end

theorem solution:∃ (solve:List ℕ→ List ℕ),
  Lax759944.RamPolytime.RamPolytime solve∧
    ∀ (m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n),
      ∃ (certificate:Lax109476.RationalCertificates.Certificate m n),
        solve (Lax109476.RationalEncoding.encodeProgram P)=Lax109476.RationalEncoding.encodeCertificate certificate∧
          Lax109476.RationalCertificates.IsValidCertificate P certificate:= @Lax109476Proofs.RamUniformSolver.exists_exact_polynomial_time_solver
