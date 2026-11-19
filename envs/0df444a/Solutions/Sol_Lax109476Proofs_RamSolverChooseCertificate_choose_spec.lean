-- Prove2me | solution 1 for Lax109476Proofs.RamSolverChooseCertificate.choose_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:36.682287+00:00
-- url     : https://prove2.me/submissions/182c70f5-246a-48d1-831c-ec1f4f3e72dc

import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.WellFounded
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamCertificateDecision_decideFeasible_spec
import Theorems.Thm_Lax109476Proofs_RamCertificateFamilies_optimal_spec
import Theorems.Thm_Lax109476Proofs_RamCertificateFamilies_unbounded_spec
import Theorems.Thm_Lax109476Proofs_RamRecoverFeasibleSystem_recover_spec
import Theorems.Thm_Lax109476Proofs_RamCertificateBuilder_buildSystem_spec_native

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

namespace Lax109476Proofs.RamCertificateBuilder
end Lax109476Proofs.RamCertificateBuilder
theorem Lax109476Proofs.RamCertificateBuilder.buildSystem_spec:∀ (B M m n r s matrixCost boundCost:Nat) (P:Lax109476.LinearProgram.Program Int m n)
  (F:Lax109476.LinearProgram.Program Int r s) (matrixSelector boundSelector:Lax808846Proofs.Imp.Com),
  Nat.le ((1:Nat)) M→
    Nat.lt M B→
      Nat.lt
          (HAdd.hAdd
            (HAdd.hAdd
              (HAdd.hAdd (HMul.hMul r s)
                r)
              s)
            ((4:Nat)))
          B→
        (∀ (i:Fin r) (j:Fin s),Nat.le (@Lax109476.LinearProgram.Program.A Int r s F i j).natAbs M)→
          (∀ (i:Fin r),Nat.le (@Lax109476.LinearProgram.Program.b Int r s F i).natAbs M)→
            (∀ (i:Fin r) (j:Fin s),
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                      (And (@Eq Nat (σ.vars "query.row") (@Fin.val r i)) (@Eq Nat (σ.vars "query.col") (@Fin.val s j))))
                  matrixSelector
                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                      (Lax109476Proofs.RamRational.FractionOutput
                        (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.A Int r s F i j)) τ))
                  matrixCost)→
              (∀ (i:Fin r),
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P σ)
                        (@Eq Nat (σ.vars "query.row") (@Fin.val r i)))
                    boundSelector
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                        (Lax109476Proofs.RamRational.FractionOutput
                          (@Int.cast Rat Rat.instIntCast (@Lax109476.LinearProgram.Program.b Int r s F i)) τ))
                    boundCost)→
                (∀ (a:String),
                    @Membership.mem String (List String) (@List.instMembership String)
                        Lax109476Proofs.RamCertificateContext.fields a→
                      a∉ matrixSelector.wvars)→
                  (∀ (a:String),
                      @Membership.mem String (List String) (@List.instMembership String)
                          Lax109476Proofs.RamCertificateContext.fields a→
                        a∉ boundSelector.wvars)→
                    "build.i" ∉ matrixSelector.wvars→
                      "build.count" ∉ matrixSelector.wvars→
                        "build.i" ∉ boundSelector.wvars→
                          "build.count" ∉ boundSelector.wvars→
                            @Eq (List String) matrixSelector.warrs (@List.nil String)→
                              @Eq (List String) boundSelector.warrs (@List.nil String)→
                                Lax808846Proofs.Reasoning.Spec B
                                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateContext.Context m n P r s σ)
                                      (And
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.A"
                                          (HMul.hMul r s) σ)
                                        (Lax109476Proofs.RamEllipsoidStep.Extents "system.b" r σ)))
                                  (Lax109476Proofs.RamCertificateBuilder.buildSystem matrixSelector boundSelector)
                                  (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                    And (@Lax109476Proofs.RamCertificateSource.Data m n P τ)
                                      (@Lax109476Proofs.RamEquationData.Data r s F τ))
                                  (HAdd.hAdd
                                    (HAdd.hAdd
                                      (HMul.hMul
                                        (HAdd.hAdd matrixCost
                                          ((70:Nat)))
                                        (HMul.hMul r s))
                                      (HMul.hMul
                                        (HAdd.hAdd boundCost
                                          ((58:Nat)))
                                        r))
                                    ((62:Nat))):= @Lax109476Proofs.RamCertificateBuilder.buildSystem_spec_native

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

open Matrix

namespace Lax109476Proofs.Elimination

lemma mulVec_lastCases_split
    {m:Type*} {F:Type*} [Semiring F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F)
    (xₙ:F)
    (x':Fin n→ F)
    (i:m):
    A.mulVec (Fin.lastCases xₙ x') i
     =(A.submatrix id Fin.castSucc i ⬝ᵥ x') + A i (Fin.last n) * xₙ:=by
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc]

lemma dotProduct_mul_right
  {F:Type*} [CommSemiring F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F):
    ((fun j:Fin n => a j * c) ⬝ᵥ x)=(a ⬝ᵥ x) * c:=by
  calc
    ((fun j:Fin n => a j * c) ⬝ᵥ x)
       =∑ j:Fin n, (a j * c) * x j:=by simp [dotProduct]
    _=∑ j:Fin n, (a j * x j) * c:=by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _=(∑ j:Fin n,a j * x j) * c:=by
          rw [← Finset.sum_mul]
    _=(a ⬝ᵥ x) * c:=by simp [dotProduct]

lemma dotProduct_scaled_inv_mul
    {F:Type*} [Field F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F)
    (hc:c ≠ 0):
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x) * c=a ⬝ᵥ x:=by
  calc
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x) * c
       =((a ⬝ᵥ x) * c⁻¹) * c:=by
            rw [dotProduct_mul_right]
    _=a ⬝ᵥ x:=by
          field_simp [hc]

lemma dotProduct_mul_inv
  {F:Type*} [Field F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F):
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x)=(a ⬝ᵥ x) * c⁻¹:=by
  simpa using dotProduct_mul_right a x c⁻¹

lemma split_add_mul_inv
    {F:Type*} [Field F]
    (u x c:F)
    (hc:c ≠ 0):
    ((u + c * x) * c⁻¹)=u * c⁻¹ + x:=by
  calc
    ((u + c * x) * c⁻¹)
       =u * c⁻¹ + (c * x) * c⁻¹:=by ring
    _=u * c⁻¹ + x:=by
          have hx:(c * x) * c⁻¹=x:=by
            calc
              (c * x) * c⁻¹=x * (c * c⁻¹):=by ring
              _=x:=by simp [mul_inv_cancel₀ hc]
          simp [hx]

lemma mul_inv_cancel_right
    {F:Type*} [Field F]
    (a c:F)
    (hc:c ≠ 0):
    (a * c⁻¹) * c=a:=by
  calc
    (a * c⁻¹) * c=a * (c⁻¹ * c):=by ring
    _=a:=by simp [inv_mul_cancel₀ hc]

lemma upper_bound_from_linear_pos
  {F:Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c:F)
    (hc:0 < c)
    (hlin:u + c * x≤ b):
    x + u * c⁻¹≤ b * c⁻¹:=by
  have hscaled:(u + c * x) * c⁻¹≤ b * c⁻¹:=
    mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr (le_of_lt hc))
  calc
    x + u * c⁻¹=u * c⁻¹ + x:=by ring
    _=(u + c * x) * c⁻¹:=by
          symm
          exact split_add_mul_inv u x c (ne_of_gt hc)
    _≤ b * c⁻¹:=hscaled

lemma lower_bound_from_linear_neg
  {F:Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c:F)
    (hc:c < 0)
    (hlin:u + c * x≤ b):
    b * c⁻¹≤ x + u * c⁻¹:=by
  have hscaled:b * c⁻¹≤ (u + c * x) * c⁻¹:=
    mul_le_mul_of_nonpos_right hlin (inv_nonpos.mpr (le_of_lt hc))
  calc
    b * c⁻¹≤ (u + c * x) * c⁻¹:=hscaled
    _=u * c⁻¹ + x:=split_add_mul_inv u x c (ne_of_lt hc)
    _=x + u * c⁻¹:=by ring

end Lax109476Proofs.Elimination

end

section

universe u v

namespace Lax109476Proofs.Elimination

private lemma finite_bounds_witness
    {ι:Type*} [Finite ι]
    {κ:Type*} [Finite κ]
    {F:Type*} [Lattice F]
    (h_nonempty:Nonempty F)
    (lhss:ι→ F)
    (rhss:κ→ F)
    (h:∀ i j,lhss i≤ rhss j):
    ∃ x:F, ((∀ i,lhss i≤ x)∧ (∀ j,x≤ rhss j)):=by
  let:=Fintype.ofFinite ι
  let:=Fintype.ofFinite κ
  by_cases hi:Nonempty ι
  ·
    exact ⟨ Finset.univ.sup' Finset.univ_nonempty lhss,
            fun i => Finset.univ.le_sup' lhss (Finset.mem_univ i),
            fun j => Finset.sup'_le _ _ (fun i _ => h i j) ⟩
  · by_cases hj:Nonempty κ
    ·
      exact ⟨ Finset.univ.inf' Finset.univ_nonempty rhss,
              fun i => False.elim (hi ⟨i⟩),
              fun j => Finset.univ.inf'_le _ (Finset.mem_univ j) ⟩
    ·
      obtain ⟨x⟩:=h_nonempty
      exact ⟨x,fun i => False.elim (hi ⟨i⟩),
               fun j => False.elim (hj ⟨j⟩)⟩

theorem Fourier_Motzkin
  {m:Type u}
  {F:Type v}
  [Fintype m]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {n:ℕ}
  (A:Matrix m (Fin (n + 1)) F)
  (b:m→ F):
  ∃ κ:Type u, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
      (∀ i j,0≤ M i j)∧
      (∀ i, (M * A) i (Fin.last n)=0)∧
      (∀ x':Fin n→ F,
        (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b↔
          ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b):=by

  let Aₙ:m→ F:=fun i => A i (Fin.last n)
  let A₀:Matrix m (Fin n) F:=A.submatrix id Fin.castSucc

  let posRow:Finset m:=Finset.univ.filter (fun i => 0 < Aₙ i)
  let negRow:Finset m:=Finset.univ.filter (fun i => Aₙ i < 0)
  let zeroRow:Finset m:=Finset.univ.filter (fun i => Aₙ i=0)

  let κ:Type _:=((↥posRow × ↥negRow) ⊕ ↥zeroRow)

  let posCoeffs:posRow -> Fin n -> F:=fun i j => A₀ i j * (Aₙ i)⁻¹
  let posb:posRow -> F:=fun i => b i * (Aₙ i)⁻¹
  let negCoeffs:negRow -> Fin n -> F:=fun i j => A₀ i j * (Aₙ i)⁻¹
  let negb:negRow -> F:=fun i => b i * (Aₙ i)⁻¹
  let zeroCoeffs:zeroRow -> Fin n -> F:=fun i j => A₀ i j
  let zerob:zeroRow -> F:=fun i => b i

  let A':Matrix κ (Fin n) F:=fun i j => match i with
    | Sum.inl (iPos,iNeg) => posCoeffs iPos j - negCoeffs iNeg j
    | Sum.inr iZero => zeroCoeffs iZero j
  let b':κ -> F:=fun i => match i with
    | Sum.inl (iPos,iNeg) => posb iPos - negb iNeg
    | Sum.inr iZero => zerob iZero

  have hlft:∀ x:Fin (n + 1)→ F,
        A.mulVec x≤ b→ A'.mulVec (fun j => x (Fin.castSucc j))≤ b':=by
    intro x hx

    let x':Fin n→ F:=fun j => x (Fin.castSucc j)
    let xₙ:=x (Fin.last n)
    intro i
    match i with
    | Sum.inl (iPos,iNeg) =>

      have h₁:xₙ≤ posb iPos - (posCoeffs iPos) ⬝ᵥ x':=by
        have hpos:0 < Aₙ iPos:=(Finset.mem_filter.mp iPos.property).2
        have hrow_pos:=hx iPos
        have hpos_ne:Aₙ iPos ≠ 0:=ne_of_gt hpos
        have hlin_pos:
            (A₀ iPos ⬝ᵥ x') + Aₙ iPos * xₙ≤ b iPos:=by
          simpa [Matrix.mulVec,dotProduct,x',xₙ,Aₙ,Fin.sum_univ_castSucc,
            add_assoc,add_left_comm,add_comm,A₀] using hrow_pos
        have hdot_pos:
            (posCoeffs iPos) ⬝ᵥ x'=(A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹:=by
          simpa [posCoeffs] using dotProduct_mul_inv (A₀ iPos) x' (Aₙ iPos)
        have hbound_pos:xₙ + (posCoeffs iPos) ⬝ᵥ x'≤ posb iPos:=by
          calc
            xₙ + (posCoeffs iPos) ⬝ᵥ x'
               =xₙ + (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹:=by rw [hdot_pos]
            _≤ b iPos * (Aₙ iPos)⁻¹:=
              upper_bound_from_linear_pos
                (A₀ iPos ⬝ᵥ x') xₙ (b iPos) (Aₙ iPos) hpos hlin_pos
            _=posb iPos:=by simp [posb]
        simpa [le_sub_iff_add_le] using hbound_pos

      have h₂:negb iNeg - (negCoeffs iNeg) ⬝ᵥ x'≤ xₙ:=by
        have hneg:Aₙ iNeg < 0:=(Finset.mem_filter.mp iNeg.property).2
        have hrow_neg:=hx iNeg
        have hneg_ne:Aₙ iNeg ≠ 0:=ne_of_lt hneg
        have hlin_neg:
            (A₀ iNeg ⬝ᵥ x') + Aₙ iNeg * xₙ≤ b iNeg:=by
          simpa [Matrix.mulVec,dotProduct,x',xₙ,Aₙ,Fin.sum_univ_castSucc,
            add_assoc,add_left_comm,add_comm,A₀] using hrow_neg
        have hdot_neg:
            (negCoeffs iNeg) ⬝ᵥ x'=(A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹:=by
          simpa [negCoeffs] using dotProduct_mul_inv (A₀ iNeg) x' (Aₙ iNeg)
        have hbound_neg:negb iNeg≤ xₙ + (negCoeffs iNeg) ⬝ᵥ x':=by
          calc
            negb iNeg=b iNeg * (Aₙ iNeg)⁻¹:=by simp [negb]
            _≤ xₙ + (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹:=
              lower_bound_from_linear_neg
                (A₀ iNeg ⬝ᵥ x') xₙ (b iNeg) (Aₙ iNeg) hneg hlin_neg
            _=xₙ + (negCoeffs iNeg) ⬝ᵥ x':=by rw [hdot_neg]
        simpa [sub_le_iff_le_add] using hbound_neg

      have h_combined:(posCoeffs iPos) ⬝ᵥ x' - negCoeffs iNeg ⬝ᵥ x'
                          ≤ posb iPos - negb iNeg:=by
        linarith [h₁,h₂]
      simpa [A',b',Matrix.mulVec,dotProduct,sub_mul,Finset.sum_sub_distrib] using h_combined

    | Sum.inr iZero =>

      simp only [A',b',Matrix.mulVec,zeroCoeffs,zerob]
      have hzero:Aₙ iZero=0:=(Finset.mem_filter.mp iZero.property).2
      have hzero':A iZero (Fin.last n)=0:=by simpa [Aₙ] using hzero
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,hzero',A₀,x'] using hx iZero

  have hright:∀ x':Fin n→ F,
        A'.mulVec x'≤ b'→ ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b:=by
    intro x' hsol

    let valpos:posRow→ F:=fun i => posb i - (posCoeffs i) ⬝ᵥ x'
    let valneg:negRow→ F:=fun i => negb i - (negCoeffs i) ⬝ᵥ x'

    have hbounds:∀ iNeg iPos,valneg iNeg≤ valpos iPos:=by
      intro iNeg iPos
      have:=hsol (Sum.inl (iPos,iNeg))
      dsimp [A',b'] at this
      have hlin:
          (posCoeffs iPos) ⬝ᵥ x' - (negCoeffs iNeg) ⬝ᵥ x'≤ posb iPos - negb iNeg:=by
        simpa [Matrix.mulVec,dotProduct,sub_mul,Finset.sum_sub_distrib] using this
      have hbound:
          negb iNeg - (negCoeffs iNeg) ⬝ᵥ x'≤
        posb iPos - (posCoeffs iPos) ⬝ᵥ x':=by
        linarith [hlin]
      simpa [valpos,valneg] using hbound

    obtain ⟨xₙ,h_xₙn,h_xₙp⟩:=finite_bounds_witness ⟨0⟩ valneg valpos hbounds

    let x:Fin (n + 1)→ F:=Fin.lastCases xₙ x'

    refine ⟨xₙ,fun i => ?_⟩
    by_cases hlast:Aₙ i=0

    · let iZero:zeroRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hlast⟩⟩
      have hlast':A i (Fin.last n)=0:=by simpa [Aₙ] using hlast
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,hlast',x,A',b',zeroCoeffs,zerob,A₀,iZero]
        using hsol (Sum.inr iZero)
    · cases lt_or_gt_of_ne hlast with
      | inl hneg =>

        let iNeg:negRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hneg⟩⟩
        have hiNeg:(iNeg:m)=i:=rfl
        have h:=h_xₙn iNeg
        dsimp [valneg] at h
        rw [sub_le_iff_le_add] at h
        rw [add_comm] at h
        have h_scaled:=mul_le_mul_of_nonpos_right h (le_of_lt hneg)
        have h_scaled':(xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg≤ negb iNeg * Aₙ iNeg:=by
          simpa [hiNeg,add_comm] using h_scaled
        have hdot_neg:A₀ i ⬝ᵥ x'=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by
          calc
            A₀ i ⬝ᵥ x'=A₀ iNeg ⬝ᵥ x':=by simp [hiNeg]
            _=((fun j:Fin n => A₀ iNeg j * (Aₙ iNeg)⁻¹) ⬝ᵥ x') * Aₙ iNeg:=by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iNeg) x' (Aₙ iNeg) (ne_of_lt hneg)
            _=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by rfl
        calc
          A.mulVec x i
             =(A₀ i ⬝ᵥ x') + Aₙ i * xₙ:=by
                  simpa [x,A₀,Aₙ] using mulVec_lastCases_split A xₙ x' i
          _=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg + xₙ * Aₙ iNeg:=by
                rw [hdot_neg]
                simp [Aₙ,hiNeg,mul_comm]
          _=(xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by ring
          _≤ negb iNeg * Aₙ iNeg:=h_scaled'
          _=b i:=by
                calc
                  negb iNeg * Aₙ iNeg
                     =(b iNeg * (Aₙ iNeg)⁻¹) * Aₙ iNeg:=by simp [negb]
                  _=b iNeg:=by
                    simpa using mul_inv_cancel_right (b iNeg) (Aₙ iNeg) (ne_of_lt hneg)
                  _=b i:=by simp [hiNeg]
      | inr hpos =>

        let iPos:posRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hpos⟩⟩
        have hiPos:(iPos:m)=i:=rfl
        have h:=h_xₙp iPos
        dsimp [valpos] at h
        rw [le_sub_iff_add_le,add_comm] at h
        have h_scaled:=mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        have h_scaled':((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos≤ posb iPos * Aₙ iPos:=by
          simpa [hiPos] using h_scaled
        have hdot_pos:A₀ i ⬝ᵥ x'=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos:=by
          calc
            A₀ i ⬝ᵥ x'=A₀ iPos ⬝ᵥ x':=by simp [hiPos]
            _=((fun j:Fin n => A₀ iPos j * (Aₙ iPos)⁻¹) ⬝ᵥ x') * Aₙ iPos:=by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iPos) x' (Aₙ iPos) hpos.ne'
            _=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos:=by rfl
        calc
          A.mulVec x i
             =(A₀ i ⬝ᵥ x') + Aₙ i * xₙ:=by
                  simpa [x,A₀,Aₙ] using mulVec_lastCases_split A xₙ x' i
          _=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos + xₙ * Aₙ iPos:=by
                rw [hdot_pos]
                simp [Aₙ,hiPos,mul_comm]
          _=((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos:=by ring
          _≤ posb iPos * Aₙ iPos:=h_scaled'
          _=b i:=by
                calc
                  posb iPos * Aₙ iPos
                     =(b iPos * (Aₙ iPos)⁻¹) * Aₙ iPos:=by simp [posb]
                  _=b iPos:=by
                    simpa using mul_inv_cancel_right (b iPos) (Aₙ iPos) hpos.ne'
                  _=b i:=by simp [hiPos]

  classical

  let M:Matrix κ m F:=fun i j =>
    match i with
    | Sum.inl (iPos,iNeg) =>
      (if (j:m)=(iPos:m) then (Aₙ iPos)⁻¹ else 0) +
      (if (j:m)=(iNeg:m) then -(Aₙ iNeg)⁻¹ else 0)
    | Sum.inr iZero =>
        if (j:m)=(iZero:m) then 1 else 0

  have hA'_eq:A'=M * A₀:=by
    ext i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      rw [Matrix.mul_apply]
      simp [A',M,posCoeffs,negCoeffs,A₀,add_mul,Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [A',M,zeroCoeffs,A₀]
  have hb'_eq:b'=M.mulVec b:=by
    ext i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      rw [Matrix.mulVec,dotProduct]
      simp [b',M,posb,negb,add_mul,Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mulVec,dotProduct]
      simp [b',M,zerob]

  have hM_nonneg:∀ i j,0≤ M i j:=by
    intro i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      refine add_nonneg ?_ ?_
      · by_cases h:(j:m)=(iPos:m)
        · simpa [M,h] using inv_nonneg.mpr (le_of_lt (Finset.mem_filter.mp iPos.property).2)
        · simp [h]
      · by_cases h:(j:m)=(iNeg:m)
        · simpa [M,h]
            using neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt (Finset.mem_filter.mp iNeg.property).2))
        · simp [h]
    | inr iZero =>
      by_cases h0:(j:m)=(iZero:m)
      · simp [M,h0]
      · simp [M,h0]

  have hM_last_zero:∀ i, (M * A) i (Fin.last n)=0:=by
    intro i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      have hposnz:Aₙ iPos ≠ 0:=ne_of_gt (Finset.mem_filter.mp iPos.property).2
      have hnegnz:Aₙ iNeg ≠ 0:=ne_of_lt (Finset.mem_filter.mp iNeg.property).2
      rw [Matrix.mul_apply]
      simp [M,Aₙ,hposnz,hnegnz,add_mul,Finset.sum_add_distrib]
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [M,Aₙ, (Finset.mem_filter.mp iZero.property).2]

  have h_equiv_M:∀ x':Fin n→ F,
      (M * A₀).mulVec x'≤ M.mulVec b↔
        ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b:=by
    intro x'
    constructor
    · intro hxElim
      apply hright x'
      simpa only [hA'_eq,hb'_eq] using hxElim
    · rintro ⟨t,ht⟩
      have hElim:=hlft (Fin.lastCases t x') ht
      simpa only [Fin.lastCases_castSucc,hA'_eq,hb'_eq] using hElim
  exact ⟨κ,inferInstance,M,hM_nonneg,hM_last_zero,by simpa [A₀] using h_equiv_M⟩

theorem feasibility_iff_of_projection
    {m κ:Type u} {F:Type v} [Fintype m] [Fintype κ]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F) (M:Matrix κ m F)
    (hprojection:∀ x':Fin n→ F,
      (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b↔
        ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b):
    (∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
      ∃ x':Fin n→ F,
        (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b:=by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun j => x (Fin.castSucc j), (hprojection _).mpr ?_⟩
    refine ⟨x (Fin.last n), ?_⟩
    have hreconstruct:Fin.lastCases (x (Fin.last n)) (fun j => x (Fin.castSucc j))=x:=by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    simpa only [hreconstruct] using hx
  · rintro ⟨x',hx'⟩
    obtain ⟨t,ht⟩:=(hprojection x').mp hx'
    exact ⟨Fin.lastCases t x',ht⟩

theorem Fourier_Motzkin_feasibility
    {m:Type u} {F:Type v} [Fintype m]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F):
    ∃ κ:Type u, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
      (∀ i j,0≤ M i j)∧
      (∀ i, (M * A) i (Fin.last n)=0)∧
      ((∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
        ∃ x':Fin n→ F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b):=by
  obtain ⟨κ,inst,M,hM,hzero,hprojection⟩:=Fourier_Motzkin A b
  exact ⟨κ,inst,M,hM,hzero,feasibility_iff_of_projection A b M hprojection⟩

end Lax109476Proofs.Elimination

end

section

open Matrix

namespace Lax109476Proofs.Elimination

variable {F:Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m:Type} [Fintype m]

def Farkas1Primal {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):Prop:=
  ∃ x:Fin n→ F,A.mulVec x≤  b

def Farkas1Dual {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):Prop:=
  ∃ y:m→ F, (∀ j,0≤ y j)∧ (y ᵥ* A=0)∧ (y ⬝ᵥ b < 0)

private theorem liftDual_of_fourierMotzkin {κ:Type*} [Fintype κ] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F) (M:Matrix κ m F)
    (hM_last:∀ i, (M * A) i (Fin.last n)=0)
    (hMt_nonneg:∀ i j,0≤ (M.transpose) i j)
  (y':κ→ F)
  (hy'_nonneg:∀ j,0≤ y' j)
  (hy'_Ared:y' ᵥ* (M * (A.submatrix id Fin.castSucc))=0)
  (hy'_bred:y' ⬝ᵥ M.mulVec b < 0):
  let y:m→ F:=M.transpose.mulVec y'
  (∀ j,0≤ y j)∧ (y ᵥ* A=0)∧ (y ⬝ᵥ b < 0):=by
  have hy_nonneg:∀ j,0≤ (M.transpose.mulVec y') j:=by
    intro j
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hMt_nonneg j i) (hy'_nonneg i)
  have hy'_Acast:y' ᵥ* ((M * A).submatrix id Fin.castSucc)=0:=by
    have hAred_eq:M * (A.submatrix id Fin.castSucc)=(M * A).submatrix id Fin.castSucc:=by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA:y' ᵥ* (M * A)=0:=by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul,dotProduct,hM_last]
    · intro k
      simpa [Matrix.vecMul,dotProduct] using congr_fun hy'_Acast k
  have hyA:(M.transpose.mulVec y') ᵥ* A=0:=by
    calc
      (M.transpose.mulVec y') ᵥ* A=(y' ᵥ* M) ᵥ* A:=by
        rw [Matrix.mulVec_transpose]
      _=y' ᵥ* (M * A):=by
        rw [Matrix.vecMul_vecMul]
      _=0:=hy'_MA
  have hyb:(M.transpose.mulVec y') ⬝ᵥ b < 0:=by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b=(y' ᵥ* M) ⬝ᵥ b:=by
        rw [Matrix.mulVec_transpose]
      _=y' ⬝ᵥ M.mulVec b:=by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0:=hy'_bred
  simpa using
    (show (∀ j,0≤ (M.transpose.mulVec y') j)∧
        ((M.transpose.mulVec y') ᵥ* A=0)∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg,hyA,hyb⟩)

theorem Farkas1ExhaustWith
    (eliminate:∀ (m:Type) [Fintype m] (n:ℕ)
      (A:Matrix m (Fin (n + 1)) F) (b:m→ F),
      ∃ κ:Type, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
        (∀ i j,0≤ M i j)∧ (∀ i, (M * A) i (Fin.last n)=0)∧
        ((∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
          ∃ x':Fin n→ F, (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b))
    {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):
  Farkas1Primal A b∨ Farkas1Dual A b:=by
  induction n generalizing m b with
  | zero =>
      by_cases hb:0≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi:∃ i:m,b i < 0:=by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i,lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i,hbi⟩
        classical
        let y:m→ F:=fun j => if j=i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji:j=i <;> simp [y,hji]
        · ext j
          exact j.elim0
        · have hyb:y ⬝ᵥ b=b i:=by
            simp [y,dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP:Farkas1Primal A b
      · exact Or.inl hP
      · right
        rcases eliminate m n A b with ⟨κ,_,M,hM_nonneg,hM_last,hFM⟩
        let Ared:Matrix κ (Fin n) F:=M * (A.submatrix id Fin.castSucc)
        let bred:κ→ F:=M.mulVec b
        have hFM':Farkas1Primal A b↔ Farkas1Primal (m:=κ) Ared bred:=by
          simpa [Farkas1Primal,Ared,bred] using hFM
        have hred_noPrimal:¬ Farkas1Primal (m:=κ) Ared bred:=by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust:Farkas1Primal (m:=κ) Ared bred∨ Farkas1Dual (m:=κ) Ared bred:=
          ih (m:=κ) (A:=Ared) (b:=bred)
        have hred_dual:Farkas1Dual (m:=κ) Ared bred:=by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y',hy'_nonneg,hy'_Ared,hy'_bred⟩
        have hMt_nonneg:∀ i j,0≤ (M.transpose) i j:=by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift:Farkas1Dual A b:=by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared,bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift

theorem Farkas1Exhaust {n:ℕ} (A:Matrix m (Fin n) ℝ) (b:m→ ℝ):
    Farkas1Primal A b∨ Farkas1Dual A b:=
  Farkas1ExhaustWith (fun _ _ _ A b => Fourier_Motzkin_feasibility A b) A b

theorem Farkas1ExhaustRat {n:ℕ} (A:Matrix m (Fin n) ℚ) (b:m→ ℚ):
    Farkas1Primal A b∨ Farkas1Dual A b:=
  Farkas1ExhaustWith (fun _ _ _ A b => Fourier_Motzkin_feasibility A b) A b
end Lax109476Proofs.Elimination

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

namespace Lax109476Proofs.Farkas

open Lax109476.LinearProgram Lax109476.FarkasCertificate

private def augmentedMatrix {m n:ℕ} (P:Program ℝ m n):
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ:=
  Sum.elim P.A (fun k j => if k=j then -1 else 0)

private def augmentedBound {m n:ℕ} (P:Program ℝ m n):
    (Fin m ⊕ Fin n)→ ℝ:=Sum.elim P.b (fun _ => 0)

theorem farkas_certificate_exists:
    ∀ (m n:ℕ) (P:Program ℝ m n), ¬ IsFeasible P→
      ∃ y:Fin m→ ℝ,IsInfeasibilityCertificate P y:=by
  intro m n P hP
  classical
  have hno:¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P):=by
    rintro ⟨x,hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj:=hx (.inr j)
      simp [augmentedMatrix,augmentedBound,Matrix.mulVec,dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1Exhaust
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y,hy,hA,hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i),fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq:=congr_fun hA j
      simp only [Matrix.vecMul,dotProduct,Fintype.sum_sum_type,
        augmentedMatrix,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] at heq
      have hsum:(∑ k,y (Sum.inr k) * (if k=j then (-1:ℝ) else 0)) =
          -y (.inr j):=by simp
      rw [hsum] at heq
      have hid:columnValue P (fun i => y (.inl i)) j =
          ∑ i,y (.inl i) * P.A i j:=by
        simp only [columnValue,mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue,dotProduct,Fintype.sum_sum_type,
        augmentedBound,mul_comm] using hb

end Lax109476Proofs.Farkas

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

namespace Lax109476Proofs.Attainment

open Lax109476.LinearProgram Lax109476.FarkasCertificate

private def thresholdProgram {m n:ℕ} (P:Program ℝ m n) (α:ℝ):
    Program ℝ (m + 1) n where
  A r j:=Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r:=Fin.lastCases (-α) P.b r
  c _:=0

private theorem threshold_column {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (m + 1)→ ℝ) (j:Fin n):
    columnValue (thresholdProgram P α) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m):=by
  simp [columnValue,thresholdProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem threshold_objective {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (m + 1)→ ℝ):
    dualValue (thresholdProgram P α) z =
      dualValue P (fun i => z i.castSucc) - α * z (Fin.last m):=by
  simp [dualValue,thresholdProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem column_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ) (j:Fin n):
    columnValue P (fun i => t * y i) j=t * columnValue P y j:=by
  simp only [columnValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dual_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ):
    dualValue P (fun i => t * y i)=t * dualValue P y:=by
  simp only [dualValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem primal_attainment:
    ∀ (m n:ℕ) (P:Program ℝ m n),IsFeasible P→ IsBoundedAbove P→
      ∃ x:Fin n→ ℝ,IsPrimalOptimal P x:=by
  intro m n P hf hb
  classical
  let S:Set ℝ:= {v | ∃ x,PrimalFeasible P x∧ primalValue P x=v}
  obtain ⟨x₀,hx₀⟩:=hf
  have hS:S.Nonempty:= ⟨primalValue P x₀,x₀,hx₀,rfl⟩
  have hbounded:BddAbove S:=by
    obtain ⟨B,hB⟩:=hb
    refine ⟨B, ?_⟩
    rintro v ⟨x,hx,rfl⟩
    exact hB x hx
  let α:ℝ:=sSup S
  let Q:=thresholdProgram P α
  have hQ:IsFeasible Q:=by
    by_contra hn
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (m + 1) n Q hn
    let y:Fin m→ ℝ:=fun i => z i.castSucc
    let t:ℝ:=z (Fin.last m)
    have hy:∀ i,0≤ y i:=fun i => hz.1 i.castSucc
    have ht:0≤ t:=hz.1 (Fin.last m)
    have hcol:∀ j,P.c j * t≤ columnValue P y j:=by
      intro j
      have h:=hz.2.1 j
      change 0≤ columnValue (thresholdProgram P α) z j at h
      rw [threshold_column] at h
      change 0≤ columnValue P y j - P.c j * t at h
      linarith
    have hgap:dualValue P y < α * t:=by
      have h:=hz.2.2
      change dualValue (thresholdProgram P α) z < 0 at h
      rw [threshold_objective] at h
      change dualValue P y - α * t < 0 at h
      linarith
    by_cases hpos:0 < t
    · let w:Fin m→ ℝ:=fun i => t⁻¹ * y i
      have hw:DualFeasible P w:=by
        refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht) (hy i), ?_⟩
        intro j
        change P.c j≤ columnValue P (fun i => t⁻¹ * y i) j
        rw [column_scale]
        calc
          P.c j=t⁻¹ * (P.c j * t):=by field_simp
          _≤ t⁻¹ * columnValue P y j:=
            mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht)
      have hsup:α≤ dualValue P w:=by
        apply csSup_le hS
        rintro v ⟨x,hx,rfl⟩
        exact Lax109476Proofs.Basic.weak_duality m n P x w hx hw
      change α≤ dualValue P (fun i => t⁻¹ * y i) at hsup
      rw [dual_scale] at hsup
      have hscaled:=mul_le_mul_of_nonneg_left hsup ht
      have heq:t * (t⁻¹ * dualValue P y)=dualValue P y:=by field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0:t=0:=le_antisymm (le_of_not_gt hpos) ht
      have hcert:IsInfeasibilityCertificate P y:=by
        refine ⟨hy, ?_, ?_⟩
        · intro j
          simpa only [ht0,mul_zero] using hcol j
        · simpa only [ht0,mul_zero] using hgap
      exact Lax109476Proofs.Basic.farkas_soundness m n P y hcert ⟨x₀,hx₀⟩
  obtain ⟨x,hx⟩:=hQ
  have hxP:PrimalFeasible P x:=by
    refine ⟨hx.1, ?_⟩
    intro i
    simpa [Q,thresholdProgram,rowValue] using hx.2 i.castSucc
  have hlower:α≤ primalValue P x:=by
    have h:=hx.2 (Fin.last m)
    simpa [Q,thresholdProgram,rowValue,primalValue,Finset.sum_neg_distrib] using h
  refine ⟨x,hxP, ?_⟩
  intro w hw
  exact (le_csSup hbounded (show primalValue P w∈ S from ⟨w,hw,rfl⟩)).trans hlower

end Lax109476Proofs.Attainment

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

private def multiplierProgram {m n:ℕ} (P:Program ℝ m n) (α:ℝ):
    Program ℝ (n + 1) m where
  A r i:=Fin.lastCases (P.b i) (fun j => -P.A i j) r
  b r:=Fin.lastCases α (fun j => -P.c j) r
  c _:=0

private theorem multiplier_row {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (y:Fin m→ ℝ) (j:Fin n):
    rowValue (multiplierProgram P α) y j.castSucc=-columnValue P y j:=by
  simp [rowValue,columnValue,multiplierProgram,Finset.sum_neg_distrib]

private theorem multiplier_last {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (y:Fin m→ ℝ):
    rowValue (multiplierProgram P α) y (Fin.last n)=dualValue P y:=by
  simp [rowValue,dualValue,multiplierProgram]

private theorem certificate_column {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (n + 1)→ ℝ) (i:Fin m):
    columnValue (multiplierProgram P α) z i =
      -rowValue P (fun j => z j.castSucc) i + P.b i * z (Fin.last n):=by
  simp [columnValue,rowValue,multiplierProgram,Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

private theorem certificate_objective {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (n + 1)→ ℝ):
    dualValue (multiplierProgram P α) z =
      -primalValue P (fun j => z j.castSucc) + α * z (Fin.last n):=by
  simp [dualValue,primalValue,multiplierProgram,Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

theorem optimal_dual_multipliers:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x:Fin n→ ℝ),IsPrimalOptimal P x→
      ∃ y:Fin m→ ℝ,DualFeasible P y∧ primalValue P x=dualValue P y:=by
  intro m n P x hx
  classical
  let Q:=multiplierProgram P (primalValue P x)
  have hQ:IsFeasible Q:=by
    by_contra hQ
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (n + 1) m Q hQ
    let d:Fin n→ ℝ:=fun j => z j.castSucc
    let t:ℝ:=z (Fin.last n)
    have hd:∀ j,0≤ d j:=fun j => hz.1 j.castSucc
    have ht:0≤ t:=hz.1 (Fin.last n)
    have hrow:∀ i,rowValue P d i≤ P.b i * t:=by
      intro i
      have h:=hz.2.1 i
      change 0≤ columnValue (multiplierProgram P (primalValue P x)) z i at h
      rw [certificate_column] at h
      change 0≤ -rowValue P d i + P.b i * t at h
      linarith
    have hobj:primalValue P x * t < primalValue P d:=by
      have h:=hz.2.2
      change dualValue (multiplierProgram P (primalValue P x)) z < 0 at h
      rw [certificate_objective] at h
      change -primalValue P d + primalValue P x * t < 0 at h
      linarith
    by_cases hpos:0 < t
    · let w:Fin n→ ℝ:=fun j => t⁻¹ * d j
      have hw:PrimalFeasible P w:=by
        refine ⟨fun j => mul_nonneg (inv_nonneg.mpr ht) (hd j), ?_⟩
        intro i
        change rowValue P (fun j => t⁻¹ * d j) i≤ P.b i
        rw [row_scale]
        calc
          t⁻¹ * rowValue P d i≤ t⁻¹ * (P.b i * t):=
            mul_le_mul_of_nonneg_left (hrow i) (inv_nonneg.mpr ht)
          _=P.b i:=by field_simp
      have hbest:=hx.2 w hw
      change primalValue P (fun j => t⁻¹ * d j)≤ primalValue P x at hbest
      rw [objective_scale] at hbest
      have hscaled:=mul_le_mul_of_nonneg_left hbest ht
      have heq:t * (t⁻¹ * primalValue P d)=primalValue P d:=by
        field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0:t=0:=le_antisymm (le_of_not_gt hpos) ht
      have hw:PrimalFeasible P (fun j => x j + d j):=by
        refine ⟨fun j => add_nonneg (hx.1.1 j) (hd j), ?_⟩
        intro i
        rw [row_add]
        have hi:=hrow i
        rw [ht0,mul_zero] at hi
        linarith [hx.1.2 i]
      have hbest:=hx.2 _ hw
      rw [objective_add] at hbest
      rw [ht0,mul_zero] at hobj
      linarith
  obtain ⟨y,hy⟩:=hQ
  have hdual:DualFeasible P y:=by
    refine ⟨hy.1, ?_⟩
    intro j
    have h:=hy.2 j.castSucc
    change rowValue (multiplierProgram P (primalValue P x)) y j.castSucc≤ _ at h
    rw [multiplier_row] at h
    simp only [Q,multiplierProgram,Fin.lastCases_castSucc] at h
    linarith
  refine ⟨y,hdual,le_antisymm
    (Lax109476Proofs.Basic.weak_duality m n P x y hx.1 hdual) ?_⟩
  have h:=hy.2 (Fin.last n)
  change rowValue (multiplierProgram P (primalValue P x)) y (Fin.last n)≤ _ at h
  rw [multiplier_last] at h
  simpa only [Q,multiplierProgram,Fin.lastCases_last] using h

theorem strong_duality:
    ∀ (m n:ℕ) (P:Program ℝ m n),IsFeasible P→ IsBoundedAbove P→
      ∃ (x:Fin n→ ℝ) (y:Fin m→ ℝ),
        PrimalFeasible P x∧ DualFeasible P y∧ primalValue P x=dualValue P y:=by
  intro m n P hf hb
  obtain ⟨x,hx⟩:=Lax109476Proofs.Attainment.primal_attainment m n P hf hb
  obtain ⟨y,hy,heq⟩:=Lax109476Proofs.Duality.optimal_dual_multipliers m n P x hx
  exact ⟨x,y,hx.1,hy,heq⟩

end Lax109476Proofs.Duality

end

section

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def realVector {n:ℕ} (x:Fin n→ ℚ):Fin n→ ℝ:=fun j => x j

end Lax109476.RationalCertificates

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate

private def augmentedMatrix {m n:ℕ} (P:Program ℚ m n):
    Matrix (Fin m ⊕ Fin n) (Fin n) ℚ:=
  Sum.elim P.A (fun k j => if k=j then -1 else 0)

private def augmentedBound {m n:ℕ} (P:Program ℚ m n):
    (Fin m ⊕ Fin n)→ ℚ:=Sum.elim P.b (fun _ => 0)

theorem rational_farkas_exists {m n:ℕ} (P:Program ℚ m n)
    (hP:¬ ∃ x,PrimalFeasible P x):
    ∃ y:Fin m→ ℚ,IsInfeasibilityCertificate P y:=by
  classical
  have hno:¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P):=by
    rintro ⟨x,hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj:=hx (.inr j)
      simp [augmentedMatrix,augmentedBound,Matrix.mulVec,dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1ExhaustRat
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y,hy,hA,hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i),fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq:=congr_fun hA j
      simp only [Matrix.vecMul,dotProduct,Fintype.sum_sum_type,
        augmentedMatrix,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] at heq
      have hsum:(∑ k,y (Sum.inr k) * (if k=j then (-1:ℚ) else 0)) =
          -y (.inr j):=by simp
      rw [hsum] at heq
      have hid:columnValue P (fun i => y (.inl i)) j =
          ∑ i,y (.inl i) * P.A i j:=by
        simp only [columnValue,mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue,dotProduct,Fintype.sum_sum_type,
        augmentedBound,mul_comm] using hb

theorem cast_feasible {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hx:PrimalFeasible P x):PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℚ)
    exact_mod_cast hx.1 j
  · intro i
    have h:=(Rat.cast_le (K:=ℝ)).mpr (hx.2 i)
    simpa [rowValue,toReal,realVector] using h

theorem cast_farkas {m n:ℕ} (P:Program ℚ m n) (y:Fin m→ ℚ)
    (hy:IsInfeasibilityCertificate P y):
    IsInfeasibilityCertificate (toReal P) (realVector y):=by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    have h:=(Rat.cast_nonneg (K:=ℝ)).mpr (hy.2.1 j)
    simpa [columnValue,toReal,realVector] using h
  · have h:=(Rat.cast_lt_zero (K:=ℝ)).mpr hy.2.2
    simpa [dualValue,toReal,realVector] using h

theorem rational_feasibility:
    ∀ (m n:ℕ) (P:Program ℚ m n),IsFeasible (toReal P)→
      ∃ x:Fin n→ ℚ,PrimalFeasible P x:=by
  intro m n P hf
  by_contra h
  obtain ⟨y,hy⟩:=rational_farkas_exists P h
  exact Lax109476Proofs.Basic.farkas_soundness m n (toReal P)
    (realVector y) (cast_farkas P y hy) hf

theorem finite_rational_feasibility {ι κ:Type} [Fintype ι] [Fintype κ]
    (A:Matrix κ ι ℚ) (b:κ→ ℚ) (x:ι→ ℝ)
    (hx:∀ j,0≤ x j)
    (hrows:∀ i, (∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ)):
    ∃ z:ι→ ℚ, (∀ j,0≤ z j)∧ ∀ i, (∑ j,A i j * z j)≤ b i:=by
  classical
  let s:=Fintype.equivFin ι
  let t:=Fintype.equivFin κ
  let P:Program ℚ (Fintype.card κ) (Fintype.card ι):=
    ⟨fun i j => A (t.symm i) (s.symm j),fun i => b (t.symm i),fun _ => 0⟩
  have hP:IsFeasible (toReal P):=by
    refine ⟨fun j => x (s.symm j),fun j => hx _, ?_⟩
    intro i
    change (∑ j, (A (t.symm i) (s.symm j):ℝ) * x (s.symm j))≤ (b (t.symm i):ℝ)
    have heq:=Fintype.sum_equiv s.symm
      (fun j => (A (t.symm i) (s.symm j):ℝ) * x (s.symm j))
      (fun j => (A (t.symm i) j:ℝ) * x j) (fun _ => rfl)
    exact heq.le.trans (hrows _)
  obtain ⟨z,hz⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility _ _ P hP
  refine ⟨fun j => z (s j),fun j => hz.1 _, ?_⟩
  intro i
  calc
    _=∑ j,A i (s.symm j) * z j:=
      Fintype.sum_equiv s _ _ (fun j => by simp)
    _≤ _:=by simpa [P,rowValue] using hz.2 (t i)

end Lax109476Proofs.RationalFeasibility

end

section

open scoped BigOperators

namespace Lax109476Proofs.Recession

open Lax109476.LinearProgram Lax109476.RecessionDirection

private def directionProgram {m n:ℕ} (P:Program ℝ m n):
    Program ℝ (m + 1) n where
  A r j:=Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r:=Fin.lastCases (-1) (fun _ => 0) r
  c _:=0

private theorem direction_column {m n:ℕ} (P:Program ℝ m n)
    (z:Fin (m + 1)→ ℝ) (j:Fin n):
    columnValue (directionProgram P) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m):=by
  simp [columnValue,directionProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem column_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ) (j:Fin n):
    columnValue P (fun i => t * y i) j=t * columnValue P y j:=by
  simp only [columnValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem recession_existence:
    ∀ (m n:ℕ) (P:Program ℝ m n), ¬ IsBoundedAbove P→
      ∃ d:Fin n→ ℝ,IsImprovingDirection P d:=by
  intro m n P hb
  let Q:=directionProgram P
  have hQ:IsFeasible Q:=by
    by_contra hn
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (m + 1) n Q hn
    let y:Fin m→ ℝ:=fun i => z i.castSucc
    let t:ℝ:=z (Fin.last m)
    have hy:∀ i,0≤ y i:=fun i => hz.1 i.castSucc
    have ht:0 < t:=by
      have h:=hz.2.2
      change dualValue (directionProgram P) z < 0 at h
      simpa [dualValue,directionProgram,Fin.sum_univ_castSucc,t] using h
    have hcol:∀ j,P.c j * t≤ columnValue P y j:=by
      intro j
      have h:=hz.2.1 j
      change 0≤ columnValue (directionProgram P) z j at h
      rw [direction_column] at h
      change 0≤ columnValue P y j - P.c j * t at h
      linarith
    let w:Fin m→ ℝ:=fun i => t⁻¹ * y i
    have hw:DualFeasible P w:=by
      refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hy i), ?_⟩
      intro j
      change P.c j≤ columnValue P (fun i => t⁻¹ * y i) j
      rw [column_scale]
      calc
        P.c j=t⁻¹ * (P.c j * t):=by field_simp
        _≤ t⁻¹ * columnValue P y j:=
          mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht.le)
    exact hb ⟨dualValue P w,fun x hx =>
      Lax109476Proofs.Basic.weak_duality m n P x w hx hw⟩
  obtain ⟨d,hd⟩:=hQ
  refine ⟨d,hd.1, ?_, ?_⟩
  · intro i
    have h:=hd.2 i.castSucc
    simpa [Q,directionProgram,rowValue] using h
  · have h:=hd.2 (Fin.last m)
    have hvalue:-primalValue P d≤ -1:=by
      simpa [Q,directionProgram,rowValue,primalValue,Finset.sum_neg_distrib] using h
    linarith

end Lax109476Proofs.Recession

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateExistence

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RecessionDirection
open Lax109476Proofs.RationalFeasibility

private def pairMatrix {m n:ℕ} (P:Program ℚ m n):
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℚ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

private def pairBound {m n:ℕ} (P:Program ℚ m n):
    (Fin m ⊕ (Fin n ⊕ Bool))→ ℚ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0

private theorem rational_matching_pair {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℝ) (y:Fin m→ ℝ)
    (hx:PrimalFeasible (toReal P) x) (hy:DualFeasible (toReal P) y)
    (heq:primalValue (toReal P) x=dualValue (toReal P) y):
    ∃ xr:Fin n→ ℚ, ∃ yr:Fin m→ ℚ,
      PrimalFeasible P xr∧ DualFeasible P yr∧ primalValue P xr=dualValue P yr:=by
  let z:(Fin n ⊕ Fin m)→ ℝ:=Sum.elim x y
  have hz:∀ j,0≤ z j:=by
    intro j
    cases j with
    | inl j => exact hx.1 j
    | inr i => exact hy.1 i
  have hrows:∀ i, (∑ j, (pairMatrix P i j:ℝ) * z j)≤ (pairBound P i:ℝ):=by
    intro i
    cases i with
    | inl i => simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,rowValue,toReal] using hx.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,columnValue,toReal,
          Finset.sum_neg_distrib] using neg_le_neg (hy.2 j)
      | inr b =>
        cases b
        · have h:primalValue (toReal P) x - dualValue (toReal P) y≤ 0:=by rw [heq]; simp
          simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,primalValue,dualValue,
            toReal,Finset.sum_neg_distrib,sub_eq_add_neg] using h
        · have h:-primalValue (toReal P) x + dualValue (toReal P) y≤ 0:=by rw [heq]; simp
          simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,primalValue,dualValue,
            toReal,Finset.sum_neg_distrib] using h
  obtain ⟨zr,hzr,hr⟩:=finite_rational_feasibility (pairMatrix P) (pairBound P) z hz hrows
  let xr:Fin n→ ℚ:=fun j => zr (.inl j)
  let yr:Fin m→ ℚ:=fun i => zr (.inr i)
  refine ⟨xr,yr, ⟨fun j => hzr _, ?_⟩, ⟨fun i => hzr _, ?_⟩, ?_⟩
  · intro i
    simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,rowValue] using hr (.inl i)
  · intro j
    have h:=hr (.inr (.inl j))
    have h':-columnValue P yr j≤ -P.c j:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,yr,columnValue,
        Finset.sum_neg_distrib] using h
    exact neg_le_neg_iff.mp h'
  · have h₁:=hr (.inr (.inr false))
    have h₂:=hr (.inr (.inr true))
    have hg₁:primalValue P xr - dualValue P yr≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,yr,primalValue,
        dualValue,Finset.sum_neg_distrib,sub_eq_add_neg] using h₁
    have hg₂:-primalValue P xr + dualValue P yr≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,yr,primalValue,
        dualValue,Finset.sum_neg_distrib] using h₂
    linarith

private theorem sum_scale {ι:Type} [Fintype ι] (a d:ι→ ℝ) (t:ℝ):
    (∑ j,a j * (t * d j))=t * ∑ j,a j * d j:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rational_improving_direction {m n:ℕ} (P:Program ℚ m n)
    (d:Fin n→ ℝ) (hd:IsImprovingDirection (toReal P) d):
    ∃ dr:Fin n→ ℚ,IsImprovingDirection P dr:=by
  let A:Matrix (Fin m ⊕ Unit) (Fin n) ℚ:=Sum.elim P.A (fun _ j => -P.c j)
  let b:(Fin m ⊕ Unit)→ ℚ:=Sum.elim (fun _ => 0) (fun _ => -1)
  let t:=(primalValue (toReal P) d)⁻¹
  let z:=fun j => t * d j
  have ht:0 < t:=inv_pos.mpr hd.2.2
  have hz:∀ j,0≤ z j:=fun j => mul_nonneg ht.le (hd.1 j)
  have hrows:∀ i, (∑ j, (A i j:ℝ) * z j)≤ (b i:ℝ):=by
    intro i
    cases i with
    | inl i =>
      simp only [A,b,z,Sum.elim_inl,Rat.cast_zero]
      rw [sum_scale]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hd.2.1 i)
    | inr _ =>
      simp only [A,b,z,Sum.elim_inr,Rat.cast_neg,Rat.cast_one,neg_mul,
        Finset.sum_neg_distrib]
      rw [sum_scale]
      change -(t * primalValue (toReal P) d)≤ -1
      dsimp [t]
      rw [inv_mul_cancel₀ (ne_of_gt hd.2.2)]
  obtain ⟨dr,hdr,hr⟩:=finite_rational_feasibility A b z hz hrows
  refine ⟨dr,hdr, ?_, ?_⟩
  · intro i
    exact hr (.inl i)
  · have h:-primalValue P dr≤ -1:=by
      simpa [A,b,primalValue,Finset.sum_neg_distrib] using hr (.inr ())
    linarith

theorem certificate_existence:
    ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
      IsValidCertificate P certificate:=by
  intro m n P
  classical
  by_cases hf:IsFeasible (toReal P)
  · by_cases hb:IsBoundedAbove (toReal P)
    · obtain ⟨x,y,hx,hy,heq⟩:=
        Lax109476Proofs.Duality.strong_duality m n (toReal P) hf hb
      obtain ⟨xr,yr,hxr,hyr,heqr⟩:=rational_matching_pair P x y hx hy heq
      exact ⟨.optimal xr yr,hxr,hyr,heqr⟩
    · obtain ⟨xr,hxr⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility m n P hf
      obtain ⟨d,hd⟩:=Lax109476Proofs.Recession.recession_existence m n (toReal P) hb
      obtain ⟨dr,hdr⟩:=rational_improving_direction P d hd
      exact ⟨.unbounded xr dr,hxr,hdr⟩
  · have hq:¬ ∃ x:Fin n→ ℚ,PrimalFeasible P x:=by
      rintro ⟨x,hx⟩
      exact hf ⟨realVector x,cast_feasible P x hx⟩
    obtain ⟨y,hy⟩:=rational_farkas_exists P hq
    exact ⟨.infeasible y,hy⟩

end Lax109476Proofs.CertificateExistence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.StandardForm

variable {ι E:Type*} [Fintype ι] [AddCommGroup E] [Module ℚ E]

noncomputable def support (x:ι→ ℚ):Finset ι:=by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

theorem mem_support (x:ι→ ℚ) (i:ι):i∈ support x↔ x i ≠ 0:=by
  classical
  simp [support]

private theorem positive_relation (v:ι→ E) (s:Finset ι)
    (h:¬ LinearIndepOn ℚ v (s:Set ι)):
    ∃ d:ι→ ℚ, (∀ i,i∉ s→ d i=0)∧
      (∑ i,d i • v i)=0∧ ∃ i∈ s,0 < d i:=by
  classical
  obtain ⟨g,hg,i,hi,hgi⟩:=not_linearIndepOn_finset_iff.mp h
  let f:ι→ ℚ:=fun j => if j∈ s then g j else 0
  have hf:(∑ j,f j • v j)=0:=by
    simpa [f, ← Finset.sum_filter] using hg
  by_cases hp:0 < g i
  · exact ⟨f,by intro j hj; simp [f,hj],hf,i,hi,
      by simpa [f,hi] using hp⟩
  · refine ⟨-f, ?_, ?_,i,hi, ?_⟩
    · intro j hj
      simp [f,hj]
    · simp only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,hf,neg_zero]
    · simp only [Pi.neg_apply,f,if_pos hi]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hgi)

theorem exists_independent_support (v:ι→ E) (b:E)
    (h:∃ x:ι→ ℚ, (∀ i,0≤ x i)∧ ∑ i,x i • v i=b):
    ∃ x:ι→ ℚ, (∀ i,0≤ x i)∧ (∑ i,x i • v i)=b∧
      LinearIndepOn ℚ v (support x:Set ι):=by
  classical
  let S:Set (ι→ ℚ):= {x | (∀ i,0≤ x i)∧ ∑ i,x i • v i=b}
  let x:=Function.argminOn (fun x:ι→ ℚ => (support x).card) S h
  have hx:x∈ S:=Function.argminOn_mem _ S h
  have hmin:∀ y∈ S, (support x).card≤ (support y).card:=
    fun y hy => Function.argminOn_le (fun x:ι→ ℚ => (support x).card) S hy
  refine ⟨x,hx.1,hx.2, ?_⟩
  by_contra hdep
  obtain ⟨d,hd,hsum,i₀,hi₀,hdi₀⟩:=positive_relation v (support x) hdep
  let s:=(support x).filter (fun i => 0 < d i)
  obtain ⟨i,hi,hratio⟩:=s.exists_min_image (fun j => x j / d j)
    ⟨i₀,by simp [s,hi₀,hdi₀]⟩
  have his:i∈ support x:=(Finset.mem_filter.mp hi).1
  have hdi:0 < d i:=(Finset.mem_filter.mp hi).2
  let t:=x i / d i
  have ht:0≤ t:=div_nonneg (hx.1 i) hdi.le
  let y:ι→ ℚ:=fun j => x j - t * d j
  have hypos:∀ j,0≤ y j:=by
    intro j
    by_cases hj:0 < d j
    · have hjs:j∈ support x:=by
        by_contra hn
        rw [hd j hn] at hj
        exact (lt_irrefl 0) hj
      have hr:=hratio j (Finset.mem_filter.mpr ⟨hjs,hj⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hj).mp hr)
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht
        (le_of_not_gt hj)).trans (hx.1 j))
  have hyb:(∑ j,y j • v j)=b:=by
    simp only [y,sub_smul,mul_smul,Finset.sum_sub_distrib,
      ← Finset.smul_sum,hsum,smul_zero,sub_zero]
    exact hx.2
  have hyi:y i=0:=by simp [y,t,ne_of_gt hdi]
  have hsub:support y ⊆ (support x).erase i:=by
    intro j hj
    have hyj:=(mem_support y j).mp hj
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      subst j
      exact hyj hyi
    · by_contra hn
      have hxj:x j=0:=by simpa [mem_support] using hn
      exact hyj (by simp [y,hxj,hd j hn])
  have hc:=(hmin y ⟨hypos,hyb⟩).trans (Finset.card_le_card hsub)
  have hlt:=Finset.card_erase_lt_of_mem his
  omega

section Matrices

variable {κ:Type*} [Fintype κ] [DecidableEq ι]

theorem gram_det_ne_zero (C:Matrix κ ι ℚ)
    (hC:LinearIndependent ℚ C.col):(Cᵀ * C).det ≠ 0:=by
  classical
  have hc:=Matrix.mulVec_injective_iff.mpr hC
  have hg:Function.Injective (Cᵀ * C).mulVec:=by
    intro x y hxy
    let z:=x - y
    have hz:(Cᵀ * C) *ᵥ z=0:=by
      simp only [z,Matrix.mulVec_sub,hxy,sub_self]
    have hnorm:dotProduct (C *ᵥ z) (C *ᵥ z)=0:=by
      have heq:dotProduct z ((Cᵀ * C) *ᵥ z) =
          dotProduct (C *ᵥ z) (C *ᵥ z):=by
        rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
      rw [← heq,hz,dotProduct_zero]
    have hcz:C *ᵥ z=0:=by
      funext i
      exact (Finset.sum_mul_self_eq_zero_iff Finset.univ (C *ᵥ z)).mp hnorm i
        (Finset.mem_univ i)
    have hz0:z=0:=hc (by simpa using hcz)
    exact sub_eq_zero.mp hz0
  exact ((Cᵀ * C).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hg)).ne_zero

theorem gram_recovers (C:Matrix κ ι ℚ) (b:κ→ ℚ) (x:ι→ ℚ)
    (hx:C *ᵥ x=b):(Cᵀ * C) *ᵥ x=Cᵀ *ᵥ b:=by
  rw [← Matrix.mulVec_mulVec,hx]

end Matrices

end Lax109476Proofs.StandardForm

end

section

namespace Lax109476Proofs.RationalRounding

theorem roundDown_le (q:ℚ) (D:ℕ) (hD:0 < D):roundDown q D≤ q:=by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q:ℚ) (D:ℕ) (hD:0 < D):
    q < roundDown q D + 1 / D:=by
  have hp:(0:ℚ) < D:=by exact_mod_cast hD
  unfold roundDown
  rw [← add_div,lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem roundDown_error (q:ℚ) (D:ℕ) (hD:0 < D):
    0≤ (q:ℝ) - (roundDown q D:ℝ)∧
      (q:ℝ) - (roundDown q D:ℝ) < 1 / (D:ℝ):=by
  have h₁:(roundDown q D:ℝ)≤ (q:ℝ):=by
    exact_mod_cast roundDown_le q D hD
  have h₂:(q:ℝ) < (roundDown q D:ℝ) + 1 / (D:ℝ):=by
    have h:=(Rat.cast_lt (K:=ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  constructor <;> linarith

theorem roundDown_vector_error (n:ℕ) (x:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    (∑ i, ((x i:ℝ) - (roundDown (x i) D:ℝ)) ^ 2)≤
      (n:ℝ) * (1 / (D:ℝ)) ^ 2:=by
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  calc
    _≤ ∑ _i:Fin n, (1 / (D:ℝ)) ^ 2:=by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁,h₂⟩:=roundDown_error (x i) D hD
      nlinarith [show (0:ℝ) < 1 / (D:ℝ) by positivity]
    _=_:=by simp

theorem sqrtUpper_bounds (q:ℚ) (hq:0≤ q) (D:ℕ) (hD:0 < D):
    Real.sqrt (q:ℝ)≤ (sqrtUpper q D:ℝ)∧
      (sqrtUpper q D:ℝ) < Real.sqrt (q:ℝ) + 2 / (D:ℝ):=by
  let c:=Nat.ceil (q * (D:ℚ) ^ 2)
  let s:=Nat.sqrt c
  have hqR:(0:ℝ)≤ q:=by exact_mod_cast hq
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  have hcl:(q:ℝ) * (D:ℝ) ^ 2≤ c:=by
    have h:q * (D:ℚ) ^ 2≤ (c:ℚ):=Nat.le_ceil _
    have h':=(Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast] using h'
  have hcu:(c:ℝ) < (q:ℝ) * (D:ℝ) ^ 2 + 1:=by
    have h:(c:ℚ) < q * (D:ℚ) ^ 2 + 1:=
      Nat.ceil_lt_add_one (show (0:ℚ)≤ q * (D:ℚ) ^ 2 by positivity)
    have h':=(Rat.cast_lt (K:=ℝ)).mpr h
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl:(s:ℝ) ^ 2≤ c:=by
    have h:s ^ 2≤ c:=Nat.sqrt_le' c
    have h':=(Nat.cast_le (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu:(c:ℝ) < ((s:ℝ) + 1) ^ 2:=by
    have h:c < (s + 1) ^ 2:=Nat.lt_succ_sqrt' c
    have h':=(Nat.cast_lt (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h'
  have hs:(0:ℝ)≤ s:=Nat.cast_nonneg _
  have hroot:=Real.sq_sqrt hqR
  have hrootpos:=Real.sqrt_nonneg (q:ℝ)
  have hsqr:(Real.sqrt (q:ℝ) * (D:ℝ)) ^ 2=(q:ℝ) * (D:ℝ) ^ 2:=by
    rw [mul_pow,hroot]
  have hl:Real.sqrt (q:ℝ) * D≤ (s:ℝ) + 1:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl,hsu,hsqr,ht,hs]
  have hu:(s:ℝ) + 1 < Real.sqrt (q:ℝ) * D + 2:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl,hcu,hsqr,ht,hs,
      sq_nonneg ((s:ℝ) - Real.sqrt (q:ℝ) * D)]
  have heq:(sqrtUpper q D:ℝ)=((s:ℝ) + 1) / D:=by
    simp [sqrtUpper,c,s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q:ℝ) * D + 2) / D:=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _=_:=by field_simp

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

theorem determinant_bound {ι:Type*} [Fintype ι] [DecidableEq ι]
    (A:Matrix ι ι ℤ) (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H):
    A.det.natAbs≤ (Fintype.card ι).factorial * H ^ Fintype.card ι:=by
  have hentry:∀ i j, |A i j|≤ (H:ℤ):=by
    intro i j
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr (hA i j))
  have hd:|A.det|≤ ((Fintype.card ι).factorial:ℤ) * (H:ℤ) ^ Fintype.card ι:=by
    rw [Matrix.det_apply']
    calc
      _≤ ∑ σ:Equiv.Perm ι, |(Equiv.Perm.sign σ:ℤ) * ∏ i,A (σ i) i|:=
        Finset.abs_sum_le_sum_abs _ _
      _=∑ σ:Equiv.Perm ι, ∏ i, |A (σ i) i|:=by
        congr 1
        funext σ
        have hs:|(Equiv.Perm.sign σ:ℤ)|=1:=by
          exact Int.isUnit_iff_abs_eq.mp (Equiv.Perm.sign σ).isUnit
        rw [abs_mul,hs,one_mul,Finset.abs_prod]
      _≤ ∑ _σ:Equiv.Perm ι, ∏ _i:ι, (H:ℤ):=by
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hentry _ i)
      _=_:=by simp [Fintype.card_perm]
  have hd':(A.det.natAbs:ℤ)≤
      ((Fintype.card ι).factorial * H ^ Fintype.card ι:ℕ):=by
    simpa only [Int.natCast_natAbs,Nat.cast_mul,Nat.cast_pow] using hd
  exact Int.ofNat_le.mp hd'

end Lax109476Proofs.DeterminantBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.SmallFeasiblePoint

open StandardForm DeterminantBounds

variable {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem integer_system_coordinate_bound (A:Matrix ι ι ℤ) (b:ι→ ℤ)
    (x:ι→ ℚ) (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H) (hdet:A.det ≠ 0)
    (hx:(A.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial * H ^ Fintype.card ι∧
      (x j).den≤ (Fintype.card ι).factorial * H ^ Fintype.card ι:=by
  let Q:Matrix ι ι ℚ:=A.map (fun z => (z:ℚ))
  let r:ι→ ℚ:=fun i => (b i:ℚ)
  have hxr:Q *ᵥ x=r:=hx
  have hcr:Q.det • x=Q.cramer r:=by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hxr,Matrix.mulVec_mulVec,
      Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hd:(A.det:ℚ) ≠ 0:=by exact_mod_cast hdet
  intro j
  have hupdate:Q.updateCol j r =
      (A.updateCol j b).map (fun z => (z:ℚ)):=
    (Matrix.map_updateCol (M:=A) (j:=j) (c:=b) (fun z => (z:ℚ))).symm
  have heq:(A.det:ℚ) * x j=((A.updateCol j b).det:ℚ):=by
    have h:=congrFun hcr j
    simpa only [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,hupdate,
      Q, ← Int.cast_det] using h
  have hxj:x j=((A.updateCol j b).det:ℚ) / (A.det:ℚ):=by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using heq
  rw [hxj]
  obtain ⟨hn,hdn⟩:=integer_ratio_num_den_bound (A.updateCol j b).det A.det hdet
  refine ⟨hn.trans (determinant_bound _ H ?_),
    hdn.trans (determinant_bound A H hA)⟩
  intro i k
  simp only [Matrix.updateCol_apply]
  split_ifs <;> first | exact hb i | exact hA i k

theorem integer_gram_entry_bound (C:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hC:∀ i j, (C i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H):
    (∀ i j, ((Cᵀ * C) i j).natAbs≤ Fintype.card κ * H ^ 2)∧
      (∀ i, ((Cᵀ *ᵥ b) i).natAbs≤ Fintype.card κ * H ^ 2):=by
  constructor
  · intro i j
    calc
      _≤ ∑ k, (C k i * C k j).natAbs:=Int.natAbs_sum_le _ _
      _≤ ∑ _k:κ,H ^ 2:=by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul,pow_two]
        exact Nat.mul_le_mul (hC k i) (hC k j)
      _=_:=by simp
  · intro i
    calc
      _≤ ∑ k, (C k i * b k).natAbs:=Int.natAbs_sum_le _ _
      _≤ ∑ _k:κ,H ^ 2:=by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul,pow_two]
        exact Nat.mul_le_mul (hC k i) (hb k)
      _=_:=by simp

theorem independent_integer_coordinate_bound (C:Matrix κ ι ℤ) (b:κ→ ℤ)
    (x:ι→ ℚ) (H:ℕ) (hC:∀ i j, (C i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H)
    (hind:LinearIndependent ℚ (C.map (fun z => (z:ℚ))).col)
    (hx:(C.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι∧
      (x j).den≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι:=by
  let Q:Matrix κ ι ℚ:=C.map (fun z => (z:ℚ))
  have hmap:(Cᵀ * C).map (fun z => (z:ℚ))=Qᵀ * Q:=by
    ext i j
    simp [Matrix.mul_apply,Q]
  have hright:(Qᵀ *ᵥ fun i => (b i:ℚ)) =
      fun i => ((Cᵀ *ᵥ b) i:ℚ):=by
    ext i
    simp [Matrix.mulVec,dotProduct,Q]
  have hdet:(Cᵀ * C).det ≠ 0:=by
    intro h
    have hz:((Cᵀ * C).det:ℚ)=0:=by simp [h]
    rw [Int.cast_det,hmap] at hz
    exact gram_det_ne_zero Q hind hz
  have hgram:((Cᵀ * C).map (fun z => (z:ℚ))) *ᵥ x =
      fun i => ((Cᵀ *ᵥ b) i:ℚ):=by
    rw [hmap,gram_recovers Q _ x hx,hright]
  obtain ⟨hentries,hbound⟩:=integer_gram_entry_bound C b H hC hb
  exact integer_system_coordinate_bound (Cᵀ * C) (Cᵀ *ᵥ b) x
    (Fintype.card κ * H ^ 2) hentries hbound hdet hgram

theorem exists_bounded_integer_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (A.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (A.map (fun z => (z:ℚ))) *ᵥ x=(fun i => (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι∧
        (x j).den≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by
  classical
  obtain ⟨x,hxpos,hxeq⟩:=hf
  have hrep:(∑ j,x j • (A.map (fun z => (z:ℚ))).col j) =
      fun i => (b i:ℚ):=by
    ext i
    simpa [Matrix.col,Matrix.mulVec,dotProduct,mul_comm] using congrFun hxeq i
  obtain ⟨z,hzpos,hzeq,hind⟩:=exists_independent_support
    (A.map (fun z => (z:ℚ))).col (fun i => (b i:ℚ)) ⟨x,hxpos,hrep⟩
  let s:=support z
  let C:Matrix κ s ℤ:=fun i j => A i j.1
  have hcpos:∀ i j, (C i j).natAbs≤ H:=fun i j => hA i j.1
  have hcind:LinearIndependent ℚ (C.map (fun a => (a:ℚ))).col:=hind
  have hzfull:(A.map (fun a => (a:ℚ))) *ᵥ z=fun i => (b i:ℚ):=by
    ext i
    simpa [Matrix.col,Matrix.mulVec,dotProduct,mul_comm] using congrFun hzeq i
  have hceq:(C.map (fun a => (a:ℚ))) *ᵥ (fun j:s => z j.1) =
      fun i => (b i:ℚ):=by
    ext i
    change (∑ j:s, (A i j.1:ℚ) * z j.1)=(b i:ℚ)
    calc
      _=∑ j∈ s, (A i j:ℚ) * z j:=Finset.sum_coe_sort s _
      _=∑ j, (A i j:ℚ) * z j:=by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hzj:z j=0:=by simpa [s,mem_support] using hj
        simp [hzj]
      _=_:=congrFun hzfull i
  have hbnd:=independent_integer_coordinate_bound C b (fun j:s => z j.1)
    H hcpos hb hcind hceq
  have hk:Fintype.card s≤ Fintype.card ι:=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hbound:(Fintype.card s).factorial *
      (Fintype.card κ * H ^ 2) ^ Fintype.card s≤
      (Fintype.card ι).factorial * (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by
    apply Nat.mul_le_mul (Nat.factorial_le hk)
    exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbpos:0 < (Fintype.card ι).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by positivity
  refine ⟨z,hzpos,hzfull, ?_⟩
  intro j
  by_cases hj:j∈ s
  · exact ⟨(hbnd ⟨j,hj⟩).1.trans hbound, (hbnd ⟨j,hj⟩).2.trans hbound⟩
  · have hzj:z j=0:=by simpa [s,mem_support] using hj
    simp only [hzj,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    omega

theorem exists_bounded_integer_inequality_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (A i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      ∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ)∧
        (x j).den≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ):=by
  classical
  let C:Matrix κ (ι ⊕ κ) ℤ:=fun i =>
    Sum.elim (A i) (fun k => if i=k then 1 else 0)
  have hC:∀ i j, (C i j).natAbs≤ H:=by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr k => simp only [C,Sum.elim_inr]; split_ifs <;> simp_all
  obtain ⟨x,hxpos,hxrows⟩:=hf
  let z:(ι ⊕ κ)→ ℚ:=Sum.elim x (fun i => (b i:ℚ) - ∑ j, (A i j:ℚ) * x j)
  have hzpos:∀ j,0≤ z j:=by
    intro j
    cases j with
    | inl j => exact hxpos j
    | inr i => exact sub_nonneg.mpr (hxrows i)
  have hzeq:(C.map (fun z => (z:ℚ))) *ᵥ z=fun i => (b i:ℚ):=by
    ext i
    simp [Matrix.mulVec,Matrix.map,dotProduct,C,z,Fintype.sum_sum_type]
  obtain ⟨w,hwpos,hweq,hwbnd⟩:=exists_bounded_integer_point C b H hC hb
    ⟨z,hzpos,hzeq⟩
  refine ⟨fun j => w (.inl j),fun j => hwpos _, ?_, ?_⟩
  · intro i
    have h:=congrFun hweq i
    have heq:(∑ j, (A i j:ℚ) * w (.inl j)) + w (.inr i)=(b i:ℚ):=by
      simpa [Matrix.mulVec,Matrix.map,dotProduct,C,Fintype.sum_sum_type] using h
    linarith [hwpos (.inr i)]
  · intro j
    simpa only [Fintype.card_sum] using hwbnd (.inl j)

theorem exists_capped_integer_inequality_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H K:ℕ) (hH:1≤ H) (hK:Fintype.card ι + Fintype.card κ≤ K)
    (hA:∀ i j, (A i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      ∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ K.factorial * (K * H ^ 2 + 1) ^ K∧
        (x j).den≤ K.factorial * (K * H ^ 2 + 1) ^ K:=by
  obtain ⟨x,hxpos,hxrows,hxbnd⟩:=exists_bounded_integer_inequality_point A b H hH hA hb hf
  have hr:Fintype.card κ≤ K:=by omega
  have hbound:(Fintype.card ι + Fintype.card κ).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ)≤
      K.factorial * (K * H ^ 2 + 1) ^ K:=by
    apply Nat.mul_le_mul (Nat.factorial_le hK)
    have hbase:Fintype.card κ * H ^ 2 + 1≤ K * H ^ 2 + 1:=
      Nat.add_le_add_right (Nat.mul_le_mul_right (H ^ 2) hr) 1
    exact (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (by omega) hK)
  exact ⟨x,hxpos,hxrows,fun j =>
    ⟨(hxbnd j).1.trans hbound, (hxbnd j).2.trans hbound⟩⟩

end Lax109476Proofs.SmallFeasiblePoint

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem commonDenominator_pos (q:ι→ ℚ):0 < commonDenominator q:=by
  exact Finset.prod_pos (fun i _ => (q i).den_pos)

theorem denominator_dvd (q:ι→ ℚ) (i:ι):(q i).den ∣ commonDenominator q:=by
  classical
  exact Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)

theorem clearedNumerator_cast (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i:ℚ)=(commonDenominator q:ℚ) * q i:=by
  have hdiv:(commonDenominator q:ℚ) =
      (commonDenominator q / (q i).den:ℕ) * ((q i).den:ℚ):=by
    exact_mod_cast (Nat.div_mul_cancel (denominator_dvd q i)).symm
  rw [clearedNumerator,Int.cast_mul,Int.cast_natCast]
  conv_rhs => rw [← (q i).num_div_den,hdiv]
  have hd:((q i).den:ℚ) ≠ 0:=by exact_mod_cast (q i).den_ne_zero
  field_simp

theorem clearedNumerator_bound (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i).natAbs≤ (q i).num.natAbs * commonDenominator q:=by
  simp only [clearedNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

theorem product_le_two_pow_sum_size (s:Finset ι) (f:ι→ ℕ):
    (∏ i∈ s,f i)≤ 2 ^ (∑ i∈ s,Nat.size (f i)):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self (f i)).le ih

theorem commonDenominator_bound (q:ι→ ℚ):
    commonDenominator q≤ 2 ^ (∑ i,Nat.size (q i).den):=
  product_le_two_pow_sum_size Finset.univ (fun i => (q i).den)

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

open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram

theorem bitSize_append (x y:List ℕ):bitSize (x ++ y)=bitSize x + bitSize y:=by
  simp [bitSize,encode]

theorem bitSize_cons (n:ℕ) (x:List ℕ):
    bitSize (n::x)=Nat.size n + 1 + bitSize x:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len]
  omega

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_flatMap {α:Type*} (x:List α) (f:α→ List ℕ):
    bitSize (x.flatMap f)=(x.map (fun a => bitSize (f a))).sum:=by
  induction x with
  | nil => rfl
  | cons a x ih => simp only [List.flatMap_cons,bitSize_append,
      List.map_cons,List.sum_cons,ih]

theorem rational_size_bounds (q:ℚ):
    3≤ bitSize (encodeRational q)∧
      Nat.size q.num.natAbs + Nat.size q.den≤ bitSize (encodeRational q):=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  omega

theorem vector_size {n:ℕ} (x:Fin n→ ℚ):
    bitSize (encodeVector x)=∑ j,bitSize (encodeRational (x j)):=by
  rw [encodeVector,bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
  rfl

theorem program_size {m n:ℕ} (P:Program ℚ m n):
    bitSize (encodeProgram P)=Nat.size m + Nat.size n + 2 +
      (∑ i, ∑ j,bitSize (encodeRational (P.A i j))) +
      (∑ i,bitSize (encodeRational (P.b i))) +
      (∑ j,bitSize (encodeRational (P.c j))):=by
  have hmatrix:bitSize ((List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap
      encodeRational)=∑ i, ∑ j,bitSize (encodeRational (P.A i j)):=by
    rw [List.flatten_eq_flatMap,List.flatMap_assoc,bitSize_flatMap,
      List.map_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    change bitSize ((List.ofFn (P.A i)).flatMap encodeRational)=_
    rw [bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
    rfl
  unfold encodeProgram
  rw [bitSize_append,bitSize_append,bitSize_append,bitSize_cons,
    bitSize_cons,bitSize_nil,vector_size,vector_size,hmatrix]
  omega

theorem data_size_sum {m n:ℕ} (P:Program ℚ m n):
    (∑ i,bitSize (encodeRational (programData P i)))≤ bitSize (encodeProgram P):=by
  rw [program_size]
  simp only [programData,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr]
  omega

theorem denominator_size_sum {m n:ℕ} (P:Program ℚ m n):
    (∑ i,Nat.size (programData P i).den)≤ bitSize (encodeProgram P):=by
  apply le_trans _ (data_size_sum P)
  apply Finset.sum_le_sum
  intro i _
  have h:=(rational_size_bounds (programData P i)).2
  omega

theorem datum_numerator_size {m n:ℕ} (P:Program ℚ m n) (i):
    Nat.size (programData P i).num.natAbs≤ bitSize (encodeProgram P):=by
  have h:=(rational_size_bounds (programData P i)).2
  have hs:=Finset.single_le_sum (fun j _ => Nat.zero_le
    (bitSize (encodeRational (programData P j)))) (Finset.mem_univ i)
  have hb:=data_size_sum P
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

def scaledProgram {m n:ℕ} (P:Program ℚ m n) (s:ℚ):Program ℚ m n where
  A i j:=s * P.A i j
  b i:=s * P.b i
  c j:=s * P.c j

theorem integerProgram_eq_scaled {m n:ℕ} (P:Program ℚ m n):
    rationalProgram (integerProgram P)=scaledProgram P (programDenominator P):=by
  unfold rationalProgram integerProgram scaledProgram
  congr 1
  · funext i j
    exact clearedNumerator_cast (programData P) (.inl (i,j))
  · funext i
    exact clearedNumerator_cast (programData P) (.inr (.inl i))
  · funext j
    exact clearedNumerator_cast (programData P) (.inr (.inr j))

theorem programDenominator_bound {m n:ℕ} (P:Program ℚ m n):
    programDenominator P≤ 2 ^ bitSize (encodeProgram P):=
  (commonDenominator_bound (programData P)).trans
    (Nat.pow_le_pow_right (by decide) (denominator_size_sum P))

theorem cleared_datum_bound {m n:ℕ} (P:Program ℚ m n) (i):
    (clearedNumerator (programData P) i).natAbs≤
      2 ^ (2 * bitSize (encodeProgram P)):=by
  have hn:(programData P i).num.natAbs≤ 2 ^ bitSize (encodeProgram P):=
    (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide) (datum_numerator_size P i))
  calc
    _≤ (programData P i).num.natAbs * programDenominator P:=
      clearedNumerator_bound _ i
    _≤ 2 ^ bitSize (encodeProgram P) * 2 ^ bitSize (encodeProgram P):=
      Nat.mul_le_mul hn (programDenominator_bound P)
    _=_:=by rw [← pow_add]; congr 1; omega

theorem integerProgram_bounds {m n:ℕ} (P:Program ℚ m n):
    (∀ i j, ((integerProgram P).A i j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ i, ((integerProgram P).b i).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ j, ((integerProgram P).c j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P))):=
  ⟨fun i j => cleared_datum_bound P (.inl (i,j)),
    fun i => cleared_datum_bound P (.inr (.inl i)),
    fun j => cleared_datum_bound P (.inr (.inr j))⟩

end Lax109476Proofs.IntegerEncoding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding SmallFeasiblePoint

def BoundedVector {ι:Type*} (B:ℕ) (x:ι→ ℚ):Prop:=
  ∀ i, (x i).num.natAbs≤ B∧ (x i).den≤ B

def BoundedCertificate {m n:ℕ} (B:ℕ):Certificate m n→ Prop
  | .optimal x y => BoundedVector B x∧ BoundedVector B y
  | .infeasible y => BoundedVector B y
  | .unbounded x d => BoundedVector B x∧ BoundedVector B d

private theorem sum_scale {ι:Type*} [Fintype ι] (a x:ι→ ℚ) (t:ℚ):
    (∑ i,a i * (t * x i))=t * ∑ i,a i * x i:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalized_small_infeasibility_certificate {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H) (y:Fin m→ ℚ)
    (hy:IsInfeasibilityCertificate (rationalProgram P) y):
    ∃ yr:Fin m→ ℚ,IsValidCertificate (rationalProgram P) (.infeasible yr)∧
      BoundedCertificate (n:=n) (coordinateCap m n H) (.infeasible yr)∧
        dualValue (rationalProgram P) yr≤ -1:=by
  let A:Matrix (Fin n ⊕ Unit) (Fin m) ℤ:=
    Sum.elim (fun j i => -P.A i j) (fun _ => P.b)
  let b:(Fin n ⊕ Unit)→ ℤ:=Sum.elim (fun _ => 0) (fun _ => -1)
  let t:=(-dualValue (rationalProgram P) y)⁻¹
  let z:=fun i => t * y i
  have ht:0 < t:=inv_pos.mpr (neg_pos.mpr hy.2.2)
  have hzpos:∀ i,0≤ z i:=fun i => mul_nonneg ht.le (hy.1 i)
  have hzrows:∀ j, (∑ i, (A j i:ℚ) * z i)≤ (b j:ℚ):=by
    intro j
    cases j with
    | inl j =>
      simp only [A,b,z,Sum.elim_inl,Int.cast_neg,Int.cast_zero]
      rw [sum_scale]
      simp only [neg_mul,Finset.sum_neg_distrib]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (neg_nonpos.mpr (hy.2.1 j))
    | inr _ =>
      simp only [A,b,z,Sum.elim_inr,Int.cast_neg,Int.cast_one]
      rw [sum_scale]
      change t * dualValue (rationalProgram P) y≤ -1
      dsimp [t]
      rw [inv_neg,neg_mul,inv_mul_cancel₀ (ne_of_lt hy.2.2)]
  have hmat:∀ j i, (A j i).natAbs≤ H:=by
    intro j i
    cases j with
    | inl j => simpa [A] using hA i j
    | inr _ => exact hb i
  have hbound:∀ j, (b j).natAbs≤ H:=by
    intro j
    cases j <;> simp [b,hH]
  obtain ⟨w,hwpos,hwrows,hwsize⟩:=exists_capped_integer_inequality_point A b H
    (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]; omega)
    hmat hbound ⟨z,hzpos,hzrows⟩
  refine ⟨w, ⟨hwpos, ?_, ?_⟩,hwsize, ?_⟩
  · intro j
    have h:-columnValue (rationalProgram P) w j≤ 0:=by
      simpa [A,b,columnValue,rationalProgram,Finset.sum_neg_distrib] using hwrows (.inl j)
    linarith
  · have h:dualValue (rationalProgram P) w≤ -1:=by
      simpa [A,b,dualValue,rationalProgram] using hwrows (.inr ())
    linarith
  · simpa [A,b,dualValue,rationalProgram] using hwrows (.inr ())

end Lax109476Proofs.IntegerCertificates

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates RationalFeasibility

def RelaxedFeasible {m n:ℕ} (P:Program ℝ m n) (ε:ℝ) (x:Fin n→ ℝ):Prop:=
  (∀ j, -ε≤ x j)∧ ∀ i,rowValue P x i≤ P.b i + ε

theorem farkas_excludes_relaxation {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (B H ε:ℝ) (_hB:0≤ B) (hH:0≤ H) (hε:0≤ ε)
    (hy:IsInfeasibilityCertificate P y) (hdual:dualValue P y≤ -1)
    (hyB:∀ i,y i≤ B) (hAH:∀ i j, |P.A i j|≤ H)
    (hgap:ε * ((m:ℝ) * B + (n:ℝ) * m * H * B) < 1):
    ¬ ∃ x,RelaxedFeasible P ε x:=by
  have hysum:(∑ i,y i)≤ (m:ℝ) * B:=by
    calc
      _≤ ∑ _i:Fin m,B:=Finset.sum_le_sum (fun i _ => hyB i)
      _=_:=by simp
  have hcol:∀ j,columnValue P y j≤ (m:ℝ) * H * B:=by
    intro j
    calc
      _≤ ∑ _i:Fin m,H * B:=by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul ((le_abs_self _).trans (hAH i j)) (hyB i) (hy.1 i) hH
      _=_:=by simp; ring
  have hcolsum:(∑ j,columnValue P y j)≤ (n:ℝ) * m * H * B:=by
    calc
      _≤ ∑ _j:Fin n, ((m:ℝ) * H * B):=Finset.sum_le_sum (fun j _ => hcol j)
      _=_:=by simp; ring
  rintro ⟨x,hx⟩
  have hlo:-ε * ∑ j,columnValue P y j≤ ∑ j,columnValue P y j * x j:=by
    calc
      _=∑ j,columnValue P y j * -ε:=by rw [← Finset.sum_mul]; ring
      _≤ _:=Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hx.1 j) (hy.2.1 j))
  have hup:(∑ j,columnValue P y j * x j)≤ dualValue P y + ε * ∑ i,y i:=by
    rw [Lax109476Proofs.Basic.transpose_identity]
    calc
      _≤ ∑ i, (P.b i + ε) * y i:=Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i))
      _=_:=by simp [dualValue,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hlob:=mul_le_mul_of_nonpos_left hcolsum (neg_nonpos.mpr hε)
  have hupb:=add_le_add hdual (mul_le_mul_of_nonneg_left hysum hε)
  have hcontr:=(hlob.trans hlo).trans (hup.trans hupb)
  nlinarith

theorem row_perturbation_bound {m n:ℕ} (P:Program ℝ m n)
    (x e:Fin n→ ℝ) (H r:ℝ) (hH:0≤ H) (_hr:0≤ r)
    (hA:∀ i j, |P.A i j|≤ H) (he:∀ j, |e j|≤ r) (i:Fin m):
    |rowValue P (x + e) i - rowValue P x i|≤ (n:ℝ) * H * r:=by
  have hrow:rowValue P (x + e) i - rowValue P x i=∑ j,P.A i j * e j:=by
    simp [rowValue,mul_add,Finset.sum_add_distrib]
  rw [hrow]
  calc
    _≤ ∑ j, |P.A i j * e j|:=Finset.abs_sum_le_sum_abs _ _
    _≤ ∑ _j:Fin n,H * r:=by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (he j) (abs_nonneg _) hH
    _=_:=by simp; ring

theorem perturbation_feasible {m n:ℕ} (P:Program ℝ m n)
    (x e:Fin n→ ℝ) (H r ε:ℝ) (hH:0≤ H) (hr:0≤ r)
    (hrε:r≤ ε) (hrowε:(n:ℝ) * H * r≤ ε)
    (hA:∀ i j, |P.A i j|≤ H) (he:∀ j, |e j|≤ r)
    (hx:PrimalFeasible P x):RelaxedFeasible P ε (x + e):=by
  constructor
  · intro j
    have h:=(abs_le.mp (he j)).1
    change -ε≤ x j + e j
    linarith [hx.1 j]
  · intro i
    have h:=(abs_le.mp (row_perturbation_bound P x e H r hH hr hA he i)).2
    linarith [hx.2 i]

theorem rational_magnitude_bound (q:ℚ) (B:ℕ) (hq:q.num.natAbs≤ B):
    |(q:ℝ)|≤ (B:ℝ):=by
  have hd:(0:ℝ) < q.den:=by exact_mod_cast q.den_pos
  have hd₁:(1:ℝ)≤ q.den:=by exact_mod_cast q.den_pos
  have hn:|(q.num:ℝ)|≤ (B:ℝ):=by
    have h:(q.num.natAbs:ℝ)≤ (B:ℝ):=by exact_mod_cast hq
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have heq:|(q:ℝ)|=|(q.num:ℝ)| / q.den:=by
    conv_lhs => rw [← q.num_div_den]
    simp only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,abs_div,
      abs_of_pos hd]
  rw [heq]
  apply (div_le_iff₀ hd).mpr
  exact hn.trans (by simpa using mul_le_mul_of_nonneg_left hd₁ (Nat.cast_nonneg B))

theorem relaxation_gap (m n H B:ℕ):
    (1 / (relaxationDenominator m n H B:ℝ)) *
      ((m:ℝ) * B + (n:ℝ) * m * H * B) < 1:=by
  let G:ℝ:=(m:ℝ) * B + (n:ℝ) * m * H * B
  have hG:0≤ G:=by dsimp [G]; positivity
  have hden:0 < 2 * (G + 1):=by linarith
  change (1 / (relaxationDenominator m n H B:ℝ)) * G < 1
  have hd:(relaxationDenominator m n H B:ℝ)=2 * (G + 1):=by
    simp [relaxationDenominator,G]
  rw [hd,one_div,inv_mul_eq_div]
  exact (div_lt_one hden).mpr (by linarith)

theorem integer_relaxation_infeasible {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:¬ IsFeasible (toReal (rationalProgram P))):
    ¬ ∃ x,RelaxedFeasible (toReal (rationalProgram P))
      (1 / (relaxationDenominator m n H (coordinateCap m n H):ℝ)) x:=by
  have hrat:¬ ∃ x:Fin n→ ℚ,PrimalFeasible (rationalProgram P) x:=by
    rintro ⟨x,hx⟩
    exact hf ⟨realVector x,cast_feasible _ x hx⟩
  obtain ⟨y,hy⟩:=rational_farkas_exists (rationalProgram P) hrat
  obtain ⟨yr,hyr,hsize,hdual⟩:=normalized_small_infeasibility_certificate
    P H hH hA hb y hy
  let B:=coordinateCap m n H
  have hyreal:=cast_farkas (rationalProgram P) yr hyr
  have hdy:dualValue (toReal (rationalProgram P)) (realVector yr)≤ -1:=by
    have h:=(Rat.cast_le (K:=ℝ)).mpr hdual
    simpa [dualValue,toReal,rationalProgram,realVector] using h
  have hmag:∀ i,realVector yr i≤ (B:ℝ):=fun i =>
    (le_abs_self _).trans (rational_magnitude_bound (yr i) B (hsize i).1)
  have ha:∀ i j, |(toReal (rationalProgram P)).A i j|≤ (H:ℝ):=by
    intro i j
    have h:((P.A i j).natAbs:ℝ)≤ (H:ℝ):=by exact_mod_cast hA i j
    simpa [toReal,rationalProgram,Nat.cast_natAbs,Int.cast_abs] using h
  apply farkas_excludes_relaxation _ (realVector yr) (B:ℝ) (H:ℝ) _
    (by positivity) (by positivity) (by positivity) hyreal hdy hmag ha
  exact relaxation_gap m n H B

theorem bounded_real_feasible_point {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):
    ∃ x:Fin n→ ℝ,PrimalFeasible (toReal (rationalProgram P)) x∧
      ∀ j, |x j|≤ (coordinateCap m n H:ℝ):=by
  obtain ⟨x,hx⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility
    m n (rationalProgram P) hf
  obtain ⟨yr,hypos,hyrows,hysize⟩:=SmallFeasiblePoint.exists_capped_integer_inequality_point
    (P.A:Matrix (Fin m) (Fin n) ℤ) P.b H (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_fin]; omega) hA hb ⟨x,hx⟩
  have hy:PrimalFeasible (rationalProgram P) yr:= ⟨hypos,hyrows⟩
  exact ⟨realVector yr,cast_feasible _ yr hy,
    fun j => rational_magnitude_bound (yr j) _ (hysize j).1⟩

theorem coordinate_bound_of_ball {n:ℕ} (e:Fin n→ ℝ) (r:ℝ) (hr:0≤ r)
    (he:dotProduct e e≤ r ^ 2) (j:Fin n):|e j|≤ r:=by
  have hj:e j * e j≤ dotProduct e e:=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (e i)) (Finset.mem_univ j)
  nlinarith [sq_abs (e j),abs_nonneg (e j)]

noncomputable def cubeRadius (n:ℕ) (H ε:ℝ):ℝ:=ε / ((n:ℝ) * H + 1)

theorem cubeRadius_bounds (n:ℕ) (H ε:ℝ) (hH:0≤ H) (hε:0 < ε):
    0 < cubeRadius n H ε∧ cubeRadius n H ε≤ ε∧
      (n:ℝ) * H * cubeRadius n H ε≤ ε:=by
  have hnH:0≤ (n:ℝ) * H:=by positivity
  have hden:0 < (n:ℝ) * H + 1:=by linarith
  refine ⟨div_pos hε hden, ?_, ?_⟩
  · exact (div_le_iff₀ hden).mpr (by nlinarith)
  · dsimp [cubeRadius]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)

theorem ball_in_relaxation {m n:ℕ} (P:Program ℝ m n) (H ε:ℝ)
    (hH:0≤ H) (hε:0 < ε) (hA:∀ i j, |P.A i j|≤ H)
    (x:Fin n→ ℝ) (hx:PrimalFeasible P x):
    ∀ e:Fin n→ ℝ,dotProduct e e≤ (cubeRadius n H ε) ^ 2→
      RelaxedFeasible P ε (x + e):=by
  obtain ⟨hr,hrε,hnHr⟩:=cubeRadius_bounds n H ε hH hε
  intro e he
  exact perturbation_feasible P x e H _ ε hH hr.le hrε hnHr hA
    (fun j => coordinate_bound_of_ball e _ hr.le he j) hx

end Lax109476Proofs.Relaxation

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

theorem firstViolation_none {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ):
    firstViolation A b c=none↔ ∀ i,rowValue A c i≤ b i:=by
  simp [firstViolation,List.find?_eq_none,not_lt]

theorem firstViolation_violates {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i):b i < rowValue A c i:=by
  have hp:=List.find?_some h
  simpa using hp

theorem integer_normal_norm {n:ℕ} (a:Fin n→ ℤ) (ha:a ≠ 0):
    1≤ (fun j => (a j:ℝ)) ⬝ᵥ (fun j => (a j:ℝ)):=by
  obtain ⟨j,hj⟩:∃ j,a j ≠ 0:=by
    by_contra! h
    exact ha (funext h)
  have habs:(1:ℝ)≤ |(a j:ℝ)|:=by
    have h:(1:ℕ)≤ (a j).natAbs:=Int.natAbs_pos.mpr hj
    have hh:(1:ℝ)≤ ((a j).natAbs:ℝ):=by exact_mod_cast h
    simpa [Nat.cast_natAbs,Int.cast_abs] using hh
  have hsq:(1:ℝ)≤ (a j:ℝ) * (a j:ℝ):=by nlinarith [sq_abs (a j:ℝ)]
  exact hsq.trans (Finset.single_le_sum (fun k _ => mul_self_nonneg (a k:ℝ))
    (Finset.mem_univ j))

theorem violation_retains_points {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i) (x:Fin n→ ℝ)
    (hx:(∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ)):
    realVector (rationalRow A i) ⬝ᵥ (x - realVector c) < 0:=by
  have hc:=(Rat.cast_lt (K:=ℝ)).mpr (firstViolation_violates A b c i h)
  have hid:realVector (rationalRow A i) ⬝ᵥ (x - realVector c) =
      (∑ j, (A i j:ℝ) * x j) - (rowValue A c i:ℝ):=by
    simp [realVector,rationalRow,dotProduct,rowValue,mul_sub,Finset.sum_sub_distrib]
  rw [hid]
  linarith

theorem zero_row_infeasible {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i) (hzero:A i=0):
    ¬ ∃ x:Fin n→ ℝ, ∀ k, (∑ j, (A k j:ℝ) * x j)≤ (b k:ℝ):=by
  have hv:=firstViolation_violates A b c i h
  have hneg:b i < 0:=by simpa [rowValue,hzero] using hv
  rintro ⟨x,hx⟩
  have hi:=hx i
  have hpos:(0:ℝ)≤ (b i:ℝ):=by simpa [hzero] using hi
  exact (not_lt_of_ge hpos) ((Rat.cast_lt_zero (K:=ℝ)).mpr hneg)

end Lax109476Proofs.RationalSeparation

end

section

namespace Lax109476Proofs.EllipsoidStep

noncomputable def centralCutForm (n r t:ℝ):ℝ:=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

theorem centralCutForm_le_one (n r t:ℝ) (hn:2≤ n)
    (hr:r≤ 1) (ht₁:-1≤ t) (ht₂:t≤ 0):
    centralCutForm n r t≤ 1:=by
  have hnpos:0 < n:=by linarith
  have hnzero:n ≠ 0:=ne_of_gt hnpos
  have hnplus:n + 1 ≠ 0:=by linarith
  have hid:centralCutForm n r t =
      ((n ^ 2 - 1) * r + 2 * (n + 1) * t * (t + 1) + 1) / n ^ 2:=by
    unfold centralCutForm
    field_simp
    ring
  rw [hid]
  apply (div_le_one (sq_pos_of_pos hnpos)).mpr
  have hcoeff:0≤ n ^ 2 - 1:=by nlinarith
  have hrad:=mul_le_mul_of_nonneg_left hr hcoeff
  have htprod:t * (t + 1)≤ 0:=
    mul_nonpos_of_nonpos_of_nonneg ht₂ (by linarith)
  have hterm:2 * (n + 1) * (t * (t + 1))≤ 0:=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) htprod
  nlinarith

noncomputable def determinantFactor (n:ℕ):ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2

theorem determinantFactor_pos (n:ℕ) (hn:2≤ n):0 < determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  unfold determinantFactor
  apply mul_pos
  · apply pow_pos
    apply div_pos <;> nlinarith
  · apply sq_pos_of_pos
    apply div_pos <;> linarith

theorem log_determinantFactor_le (n:ℕ) (hn:2≤ n):
    Real.log (determinantFactor n)≤ -1 / ((n:ℝ) + 1):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hdiff:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  let a:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let b:=(n:ℝ) / ((n:ℝ) + 1)
  have ha:0 < a:=div_pos (sq_pos_of_pos hnp) hdiff
  have hb:0 < b:=div_pos hnp hplus
  have hlogA:=Real.log_le_sub_one_of_pos ha
  have hlogB:=Real.log_le_sub_one_of_pos hb
  have hk:((n - 1:ℕ):ℝ)=(n:ℝ) - 1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have heqA:((n - 1:ℕ):ℝ) * (a - 1)=1 / ((n:ℝ) + 1):=by
    rw [hk]
    dsimp [a]
    field_simp
    ring
  have heqB:2 * (b - 1)=-2 / ((n:ℝ) + 1):=by
    dsimp [b]
    field_simp
    ring
  have hA:=mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (n - 1))
  have hB:=mul_le_mul_of_nonneg_left hlogB (show (0:ℝ)≤ 2 by norm_num)
  rw [heqA] at hA
  rw [heqB] at hB
  change Real.log (a ^ (n - 1) * b ^ 2)≤ _
  rw [Real.log_mul (ne_of_gt (pow_pos ha _)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _≤ 1 / ((n:ℝ) + 1) + -2 / ((n:ℝ) + 1):=add_le_add hA hB
    _=-1 / ((n:ℝ) + 1):=by ring

open Matrix

theorem enlarged_shrink_bound (n:ℕ) (hn:2≤ n) (δ:ℝ) (hδ:0≤ δ)
    (hδsmall:δ≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):
    (1 + δ) ^ n * Real.sqrt (determinantFactor n)≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hbase:0 < 1 + δ:=by linarith
  have hsqrt:=Real.sqrt_pos.mpr (determinantFactor_pos n hn)
  have hlogbase:Real.log (1 + δ)≤ δ:=by
    simpa using Real.log_le_sub_one_of_pos hbase
  have hlogshrink:Real.log (Real.sqrt (determinantFactor n))≤
      -1 / (2 * ((n:ℝ) + 1)):=by
    rw [Real.log_sqrt (le_of_lt (determinantFactor_pos n hn))]
    calc
      _≤ (-1 / ((n:ℝ) + 1)) / 2:=
        div_le_div_of_nonneg_right (log_determinantFactor_le n hn) (by norm_num)
      _=_:=by field_simp
  have hδmul:(n:ℝ) * δ≤ 1 / (4 * ((n:ℝ) + 1)):=by
    calc
      _≤ (n:ℝ) * (1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hδsmall (le_of_lt hnp)
      _=_:=by field_simp
  have hlogbound:Real.log ((1 + δ) ^ n * Real.sqrt (determinantFactor n))≤
      -1 / (4 * ((n:ℝ) + 1)):=by
    rw [Real.log_mul (ne_of_gt (pow_pos hbase n)) (ne_of_gt hsqrt),Real.log_pow]
    calc
      _≤ (n:ℝ) * δ + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add (mul_le_mul_of_nonneg_left hlogbase (le_of_lt hnp)) hlogshrink
      _≤ 1 / (4 * ((n:ℝ) + 1)) + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add hδmul (le_refl _)
      _=_:=by field_simp; ring
  simpa only [Real.exp_log (mul_pos (pow_pos hbase n) hsqrt)] using
    Real.exp_le_exp.mpr hlogbound

theorem iterated_shrink_bound (n:ℕ) (v:ℕ→ ℝ)
    (hstep:∀ k,v (k + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k)
    (k:ℕ):
    v k≤ Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0:=by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k:=hstep k
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) *
            (Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0):=
          mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
        _=_:=by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

end Lax109476Proofs.EllipsoidStep

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

theorem symmetric_form {ι:Type} [Fintype ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (u v:ι→ ℝ):
    u ⬝ᵥ (A *ᵥ v)=v ⬝ᵥ (A *ᵥ u):=by
  have ht:Aᵀ=A:=(Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem quadratic_error_bound {n:ℕ} (E:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (hE:∀ i j, |E i j|≤ ε) (x:Fin n→ ℝ):
    |x ⬝ᵥ (E *ᵥ x)|≤ (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have hcs:(∑ i, |x i|) ^ 2≤ (n:ℝ) * (x ⬝ᵥ x):=by
    have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _:Fin n => (1:ℝ)) (fun i => |x i|)
    simpa [dotProduct,sq_abs,pow_two] using h
  calc
    _=|∑ i, ∑ j,x i * E i j * x j|:=by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _≤ ∑ i, ∑ j, |x i * E i j * x j|:=by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _≤ ∑ i, ∑ j,ε * |x i| * |x j|:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _≤ |x i| * ε * |x j|:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _=_:=by ring
    _=ε * (∑ i, |x i|) ^ 2:=by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤ ε * ((n:ℝ) * (x ⬝ᵥ x)):=mul_le_mul_of_nonneg_left hcs hε
    _=_:=by ring

theorem posDef_of_quadratic_le {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.IsHermitian)
    (hAB:∀ x,x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ (B *ᵥ x)):B.PosDef:=by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos:0 < x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

theorem inverse_variational_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (x y:ι→ ℝ):
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:A *ᵥ (A⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hnonneg:0≤ (y - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (y - A⁻¹ *ᵥ x)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub,hcancel,sub_dotProduct,dotProduct_sub,
    dotProduct_sub,symmetric_form hA.1 (A⁻¹ *ᵥ x) y,hcancel,
    dotProduct_comm y x,dotProduct_comm (A⁻¹ *ᵥ x) x] at hnonneg
  linarith

theorem inverse_quadratic_antitone {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef)
    (hAB:∀ y,y ⬝ᵥ (A *ᵥ y)≤ y ⬝ᵥ (B *ᵥ y)) (x:ι→ ℝ):
    x ⬝ᵥ (B⁻¹ *ᵥ x)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:B *ᵥ (B⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit),Matrix.one_mulVec]
  have hvar:=inverse_variational_bound hA x (B⁻¹ *ᵥ x)
  have hle:=hAB (B⁻¹ *ᵥ x)
  rw [hcancel,dotProduct_comm (B⁻¹ *ᵥ x) x] at hle
  linarith

def realShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ):
    Matrix (Fin n) (Fin n) ℝ:=fun i j => (A i j:ℝ)

theorem enlargement_sandwich {n:ℕ} (A R:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (herr:∀ i j, |R i j - A i j|≤ ε)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)∧
      x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have h:=quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec,dotProduct_sub] at h
  have hh:=abs_le.mp h
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  constructor <;> linarith [hh.1,hh.2]

theorem roundedShape_sandwich {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape A *ᵥ x)≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n:ℝ) / D) * (x ⬝ᵥ x):=by
  let R:Matrix (Fin n) (Fin n) ℝ:=
    fun i j => (RationalRounding.roundDown (A i j) D:ℝ)
  have herr:∀ i j, |R i j - realShape A i j|≤ 1 / (D:ℝ):=by
    intro i j
    have h:=RationalRounding.roundDown_error (A i j) D hD
    dsimp [R,realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid:realShape (roundedShape A D)=R + ((n:ℝ) * (1 / D)) • 1:=by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n:ℚ) / D) * (if i=j then 1 else 0):ℚ):ℝ) =
      (RationalRounding.roundDown (A i j) D:ℝ) +
        ((n:ℝ) * (1 / D)) * (if i=j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

theorem roundedShape_isHermitian {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:A.IsSymm) (D:ℕ):(realShape (roundedShape A D)).IsHermitian:=by
  rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape,roundedShape,hA.apply i j,Matrix.one_apply,eq_comm]

theorem roundedShape_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape A D)).PosDef:=by
  have hsym:A.IsSymm:=by
    apply Matrix.IsSymm.ext
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

theorem roundedShape_contains {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ)
    (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1):
    x ⬝ᵥ ((realShape (roundedShape A D))⁻¹ *ᵥ x)≤ 1:=
  (inverse_quadratic_antitone hA (roundedShape_posDef A hA D hD)
    (fun y => (roundedShape_sandwich A D hD y).1) x).trans hx

theorem roundedShape_relative_bound {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (lowerBound η:ℝ) (hη:0≤ η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ η * lowerBound) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  have hxx:0≤ x ⬝ᵥ x:=by
    simpa using dotProduct_star_self_nonneg x
  have herror:=mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative:=mul_le_mul_of_nonneg_left (hlower x) hη
  have hround:=(roundedShape_sandwich A D hD x).2
  nlinarith only [herror,hrelative,hround]

theorem inverse_smul {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (k:ℝ) (hk:k ≠ 0):
    (k • A)⁻¹=k⁻¹ • A⁻¹:=by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    inv_mul_cancel₀ hk,one_smul]

theorem inverse_form_upper_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x)) (x:ι→ ℝ):
    x ⬝ᵥ (A⁻¹ *ᵥ x)≤ lowerBound⁻¹ * (x ⬝ᵥ x):=by
  have hI:(1:Matrix ι ι ℝ).PosDef:=Matrix.PosDef.one
  have hlI:(lowerBound • (1:Matrix ι ι ℝ)).PosDef:=hI.smul hl
  have horder:∀ y,y ⬝ᵥ ((lowerBound • (1:Matrix ι ι ℝ)) *ᵥ y)≤
      y ⬝ᵥ (A *ᵥ y):=by
    intro y
    simpa only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
      smul_eq_mul] using hbound y
  have h:=inverse_quadratic_antitone hlI hA horder x
  rw [inverse_smul hI lowerBound (ne_of_gt hl)] at h
  simpa only [inv_one,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul] using h

theorem center_displacement_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ (A *ᵥ (x + e))≤ (1 + η) ^ 2:=by
  have hnonneg:0≤ (η • x - e) ⬝ᵥ (A *ᵥ (η • x - e)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (η • x - e)
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    symmetric_form hA.1 e x] at hnonneg
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hA.1 e x]
  have hb₁:=mul_le_mul_of_nonneg_left hx (show 0≤ η ^ 2 + η by positivity)
  have hb₂:=mul_le_mul_of_nonneg_left he (show 0≤ 1 + η by positivity)
  nlinarith only [hnonneg,hb₁,hb₂,hη]

theorem enlargedShape_contains_displaced {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ ((((1 + η) ^ 2) • A)⁻¹ *ᵥ (x + e))≤ 1:=by
  have hk:0 < (1 + η) ^ 2:=by positivity
  rw [inverse_smul hA _ (ne_of_gt hk),Matrix.smul_mulVec,
    dotProduct_smul,smul_eq_mul]
  calc
    _≤ ((1 + η) ^ 2)⁻¹ * (1 + η) ^ 2:=
      mul_le_mul_of_nonneg_left (center_displacement_bound hA.inv η hη x e hx he)
        (inv_nonneg.mpr (le_of_lt hk))
    _=1:=inv_mul_cancel₀ (ne_of_gt hk)

theorem roundedCenter_error {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x))
    (c:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    let e:Fin n→ ℝ:=fun i => (c i:ℝ) - RationalRounding.roundDown (c i) D
    e ⬝ᵥ (A⁻¹ *ᵥ e)≤ lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2):=by
  dsimp only
  apply (inverse_form_upper_bound hA lowerBound hl hbound _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hl))
  simpa only [dotProduct, ← pow_two] using
    RationalRounding.roundDown_vector_error n c D hD

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

theorem form_cauchy_schwarz {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (a x:ι→ ℝ) (ha:a ≠ 0):
    (x ⬝ᵥ (A *ᵥ a)) ^ 2≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg:0≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid:(q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2):=by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
      dotProduct_sub,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q,t]
    ring
  rw [hid] at hnonneg
  have h:=nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

noncomputable def realCutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ)
    (a:Fin n→ ℝ):Matrix (Fin n) (Fin n) ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) •
    (A - (2 / (((n:ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

theorem realShape_cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    realShape (cutShape n A a)=realCutShape n (realShape A) (fun i => (a i:ℝ)):=by
  ext i j
  simp [realShape,cutShape,realCutShape,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Rat.cast_sum,smul_eq_mul]

theorem realCutShape_sandwich (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x))≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x)≤
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα:0 < α:=by dsimp [α]; apply div_pos <;> nlinarith
  have hβ:0≤ β:=by dsimp [β]; positivity
  have hcs:t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x)):=form_cauchy_schwarz hA a x ha
  have hcs':t ^ 2 / q≤ x ⬝ᵥ (A *ᵥ x):=(div_le_iff₀ hq).mpr (by nlinarith)
  have hterm:0≤ β * (t ^ 2 / q):=by positivity
  have htermUpper:=mul_le_mul_of_nonneg_left hcs' hβ
  have hid:x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)):=by
    simp only [realCutShape,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec,dotProduct_smul,dotProduct_sub,
      smul_eq_mul]
    dsimp [α,β,q,t]
    simp only [dotProduct_comm (A *ᵥ a) x,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hfactor:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h:=mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h:=mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

theorem realCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):(realCutShape n A a).PosDef:=by
  have hsym:(realCutShape n A a).IsHermitian:=by
    rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape,Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec,
      smul_eq_mul,h,mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by positivity
  have hxx:0 < x ⬝ᵥ (A *ᵥ x):=by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

theorem realCutShape_inverse (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a)⁻¹ =
      (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) •
        (A⁻¹ + (2 / (((n:ℝ) - 1) * (a ⬝ᵥ (A *ᵥ a)))) •
          Matrix.vecMulVec a a):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnzero:(n:ℝ) ≠ 0:=by linarith
  have hminus:(n:ℝ) - 1 ≠ 0:=by linarith
  have hplus:(n:ℝ) + 1 ≠ 0:=by linarith
  have hdiff:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hAA:A * A⁻¹=1:=Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hrow:(A *ᵥ a) ᵥ* A⁻¹=a:=by
    rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hA.1).eq,
      hAA,Matrix.vecMul_one]
  have hcross:Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) * Matrix.vecMulVec a a =
      (a ⬝ᵥ (A *ᵥ a)) • Matrix.vecMulVec (A *ᵥ a) a:=by
    rw [Matrix.vecMulVec_mul_vecMulVec,dotProduct_comm]
    ext i j
    simp [Matrix.vecMulVec,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]
  apply Matrix.inv_eq_right_inv
  unfold realCutShape
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc:(((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1))=1:=by field_simp
  rw [hc,one_smul]
  simp only [mul_add,sub_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hAA,hcross,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hrow]
  simp only [smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ring

theorem det_realCutShape (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a).det=A.det * EllipsoidStep.determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:q ≠ 0:=by
    have hp:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hfactor:A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) =
      A * (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)):=by
    rw [mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec]
  have hdet:(1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)).det=1 - β:=by
    have h:=Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι:=Unit) a (-(β / q) • (A *ᵥ a))
    have hd:a ⬝ᵥ (-(β / q) • (A *ᵥ a))=-β:=by
      rw [dotProduct_smul]
      change -(β / q) * q=-β
      field_simp
    have hd':(-(β / q) • (A *ᵥ a)) ⬝ᵥ a=-β:=by
      rw [dotProduct_comm]
      exact hd
    rw [hd'] at h
    simpa [← Matrix.vecMulVec_eq Unit,sub_eq_add_neg,neg_smul] using h
  have hform:realCutShape n A a =
      α • (A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)):=by
    dsimp [realCutShape,α,β,q]
    congr 2
    congr 1
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [hform,Matrix.det_smul,Fintype.card_fin,hfactor,Matrix.det_mul,hdet]
  have hαβ:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  unfold EllipsoidStep.determinantFactor
  calc
    _=A.det * (α ^ (n - 1) * (α * (1 - β))):=by
      nth_rewrite 1 [show n=(n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _=_:=by rw [hαβ]

theorem realCutShape_quadratic (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) =
      EllipsoidStep.centralCutForm n (x ⬝ᵥ (A⁻¹ *ᵥ x))
        ((a ⬝ᵥ x) / Real.sqrt q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let s:=1 / (((n:ℝ) + 1) * Real.sqrt q)
  let z:=x + s • (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hzz:z ⬝ᵥ (A⁻¹ *ᵥ z) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q:=by
    dsimp [z]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hc,add_dotProduct,
      dotProduct_add,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.inv.1 (A *ᵥ a) x,dotProduct_comm x a,
      dotProduct_comm (A *ᵥ a) a]
    dsimp [q]
    ring
  have haz:a ⬝ᵥ z=a ⬝ᵥ x + s * q:=by
    simp [z,q,dotProduct_add,dotProduct_smul]
  change z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)=_
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    dotProduct_smul,dotProduct_add,smul_eq_mul,dotProduct_comm z a]
  rw [hzz,haz]
  simp only [op_smul_eq_smul,smul_eq_mul]
  change (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
    ((x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q) +
      (2 / (((n:ℝ) - 1) * q)) * (((a ⬝ᵥ x) + s * q) * ((a ⬝ᵥ x) + s * q)))=_
  dsimp [s,EllipsoidStep.centralCutForm]
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  rw [← htsq]
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem realCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1) (hcut:a ⬝ᵥ x≤ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)≤ 1:=by
  dsimp only
  rw [realCutShape_quadratic n hn A hA a x ha]
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hav:A *ᵥ a ≠ 0:=by
    intro h
    have h':=hc
    rw [h,Matrix.mulVec_zero] at h'
    exact ha h'.symm
  have hcs:=form_cauchy_schwarz hA.inv (A *ᵥ a) x hav
  rw [hc,dotProduct_comm x a,dotProduct_comm (A *ᵥ a) a] at hcs
  have hcs':((a ⬝ᵥ x) / Real.sqrt q) ^ 2≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
    rw [div_pow,Real.sq_sqrt (le_of_lt hq)]
    apply (div_le_iff₀ hq).mpr
    simpa [q,mul_comm] using hcs
  have ht:-1≤ (a ⬝ᵥ x) / Real.sqrt q:=by nlinarith
  exact EllipsoidStep.centralCutForm_le_one n _ _ (by exact_mod_cast hn)
    hx ht (div_nonpos_of_nonpos_of_nonneg hcut (le_of_lt hs))

theorem roundedCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape (cutShape n A a) D)).PosDef:=by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

theorem roundedCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D)
    (x:Fin n→ ℝ) (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1)
    (hcut:(fun i => (a i:ℝ)) ⬝ᵥ x≤ 0):
    let ar:Fin n→ ℝ:=fun i => (a i:ℝ)
    let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (realShape A *ᵥ ar)
    z ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ z)≤ 1:=by
  have hQ:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA _ ha
  apply roundedShape_contains _ hQ D hD
  rw [realShape_cutShape]
  exact realCutShape_contains n hn (realShape A) hA _ x ha hx hcut

theorem realCutShape_coarse_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    (1 / 4:ℝ) * (x ⬝ᵥ (A *ᵥ x))≤ x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x)≤ 2 * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hxx:0≤ x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp:0 < (n:ℝ) + 1:=by linarith
  have hd:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  have hratio:(1 / 2:ℝ)≤ (n:ℝ) / ((n:ℝ) + 1):=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo:(1 / 4:ℝ)≤ ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    nlinarith
  have hhi:(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)≤ 2:=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h:=realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

theorem dyadic_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (2:ℝ) ^ (l + s + n + 1)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hpow:(0:ℝ) < 2 ^ (l + s + n + 1):=by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add,pow_one]
  have hl:(2:ℝ) ^ l ≠ 0:=by positivity
  have hs:(2:ℝ) ^ s ≠ 0:=by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

theorem cut_direction_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (A *ᵥ a) ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ (A *ᵥ a)) =
      (((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * (a ⬝ᵥ (A *ᵥ a)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    hc,dotProduct_smul,dotProduct_add,smul_eq_mul,
    op_smul_eq_smul,dotProduct_comm (A *ᵥ a) a]
  field_simp
  ring

theorem center_approximation_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r:ℝ) (hr:0 < r):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) =
      ((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2:=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hrz:r ≠ 0:=ne_of_gt hr
  dsimp only
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [cut_direction_form n hn A hA a ha]
  change _=((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  change (1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
    ((1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
      ((((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * q))=_
  rw [← htsq]
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem center_approximation_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r ε:ℝ)
    (hr:Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ r)
    (herr:r - Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ ε):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e)≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hrp:0 < r:=hs.trans_le hr
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have ht:0≤ r - Real.sqrt q:=by linarith
  have hε:0≤ ε:=ht.trans herr
  have hsquare:q≤ r ^ 2:=by nlinarith [Real.sq_sqrt (le_of_lt hq)]
  dsimp only
  rw [center_approximation_form n hn A hA a ha r hrp,div_pow,mul_pow]
  change (r - Real.sqrt q) ^ 2 / ((n:ℝ) ^ 2 * r ^ 2)≤ _
  calc
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * r ^ 2):=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=
      div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

theorem form_add_le_two {ι:Type} [Fintype ι] [DecidableEq ι]
    {B:Matrix ι ι ℝ} (hB:B.PosDef) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (B *ᵥ (u + v))≤
      2 * (u ⬝ᵥ (B *ᵥ u)) + 2 * (v ⬝ᵥ (B *ᵥ v)):=by
  have h:0≤ (u - v) ⬝ᵥ (B *ᵥ (u - v)):=by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (u - v)
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,
    symmetric_form hB.1 v u] at h
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hB.1 v u]
  linarith

noncomputable def exactCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ):Fin n→ ℝ:=
  realVector c -
    (1 / (((n:ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

theorem cast_direction_form (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ)=realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
  simp [dotProduct,Matrix.mulVec,realShape,realVector,Rat.cast_sum]

theorem approximateCenter_difference (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    exactCenter n A a c - realVector (approximateCenter n A a c D) =
      (1 / (((n:ℝ) + 1) * (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ)) -
        1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
        (realShape A *ᵥ realVector a):=by
  ext i
  simp [exactCenter,approximateCenter,realVector,realShape,Matrix.mulVec,
    dotProduct,Rat.cast_sum,smul_eq_mul]
  ring

theorem roundedCenter_total_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound η:ℝ) (hl:0 < lowerBound)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ η ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ η ^ 2 / 4):
    let e:=exactCenter n A a c - realVector (roundedCenter n A a c D)
    e ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ e)≤ η ^ 2:=by
  let ar:=realVector a
  let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
  let Q:=realShape (roundedShape (cutShape n A a) D)
  let e₁:=exactCenter n A a c - realVector (approximateCenter n A a c D)
  let e₂:=realVector (approximateCenter n A a c D) - realVector (roundedCenter n A a c D)
  have hq:0 < q:=by simpa [q,ar] using hA.dotProduct_mulVec_pos ha
  have hqrat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    have hp:(0:ℝ)≤ ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ):=by
      rw [cast_direction_form]
      exact le_of_lt hq
    exact_mod_cast hp
  have hQ:Q.PosDef:=roundedCutShape_posDef n hn A hA a ha D hD
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA ar ha
  have horder:∀ y,y ⬝ᵥ (realShape (cutShape n A a) *ᵥ y)≤ y ⬝ᵥ (Q *ᵥ y):=
    fun y => (roundedShape_sandwich (cutShape n A a) D hD y).1
  have h₁:e₁ ⬝ᵥ (Q⁻¹ *ᵥ e₁)≤ η ^ 2 / 4:=by
    apply (inverse_quadratic_antitone hC hQ horder e₁).trans
    rw [realShape_cutShape]
    obtain ⟨hr,herr⟩:=RationalRounding.sqrtUpper_bounds (a ⬝ᵥ (A *ᵥ a)) hqrat D hD
    rw [cast_direction_form] at hr herr
    have hb:=center_approximation_error n hn (realShape A) hA ar ha
      (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ) (2 / D) hr (by linarith)
    change e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤ _
    have hid:(2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q) =
        4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 * q):=by ring
    have hb':e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤
        (2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q):=by
      dsimp [e₁]
      rw [approximateCenter_difference]
      exact hb
    exact hb'.trans (hid ▸ hsqrt)
  have h₂:e₂ ⬝ᵥ (Q⁻¹ *ᵥ e₂)≤ η ^ 2 / 4:=by
    have h:=roundedCenter_error hQ lowerBound hl hlower (approximateCenter n A a c D) D hD
    exact h.trans hgrid
  have he:exactCenter n A a c - realVector (roundedCenter n A a c D)=e₁ + e₂:=by
    dsimp [e₁,e₂]
    abel
  dsimp only
  rw [he]
  have h:=form_add_le_two hQ.inv e₁ e₂
  linarith

theorem realShape_roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):
    realShape (roundedStepShape n A a D η) =
      ((1 + (η:ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D):=by
  ext i j
  simp [realShape,roundedStepShape,Matrix.smul_apply,smul_eq_mul]

theorem roundedStepShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η):(realShape (roundedStepShape n A a D η)).PosDef:=by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  positivity

theorem roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound:ℝ) (hl:0 < lowerBound) (η:ℚ) (hη:0 < η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ (η:ℝ) ^ 2 / 4)
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  have hQ:=roundedCutShape_posDef n hn A hA a ha D hD
  have he:=roundedCenter_total_error n hn A hA a c ha D hD lowerBound η hl hlower hsqrt hgrid
  have hxe:(x - exactCenter n A a c) ⬝ᵥ
      ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ
        (x - exactCenter n A a c))≤ 1:=by
    have h:=roundedCutShape_contains n hn A hA a ha D hD (x - realVector c) hx hcut
    have hid:x - exactCenter n A a c=x - realVector c +
        (1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
            (realShape A *ᵥ realVector a):=by
      unfold exactCenter
      abel
    rw [hid]
    exact h
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have h:=enlargedShape_contains_displaced hQ η hp
    (x - exactCenter n A a c)
    (exactCenter n A a c - realVector (roundedCenter n A a c D)) hxe he
  rw [realShape_roundedStepShape]
  simpa only [sub_add_sub_cancel] using h

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

theorem gridDenominator_pos (l s n:ℕ):0 < gridDenominator l s n:=by
  unfold gridDenominator
  positivity

theorem grid_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (gridDenominator l s n:ℝ)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hp:(2:ℝ) ^ (l + s + n + 1)≤ (gridDenominator l s n:ℝ):=by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

theorem dyadic_center_precision (l s n:ℕ):
    4 / (((gridDenominator l s n:ℕ):ℝ) ^ 2 * ((2:ℝ) ^ l)⁻¹)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4∧
    (((2:ℝ) ^ l)⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4:=by
  let L:=(2:ℝ) ^ l
  let S:=(2:ℝ) ^ s
  let N:=(2:ℝ) ^ (n + 3)
  have hL:1≤ L:=one_le_pow₀ (by norm_num)
  have hS:0 < S:=by dsimp [S]; positivity
  have hN:8≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    have h:=one_le_pow₀ (show (1:ℝ)≤ 2 by norm_num) (n:=n)
    linarith
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hnN:8 * (n:ℝ)≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    nlinarith
  have hLN:N ^ 2≤ L * N ^ 2:=by
    simpa using mul_le_mul_of_nonneg_right hL (sq_nonneg N)
  have hid:(gridDenominator l s n:ℝ)=L * S * N:=by
    simp only [gridDenominator,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [L,S,N]
    rw [show l + s + n + 3=l + s + (n + 3) by omega,pow_add,pow_add]
  have hLz:L ≠ 0:=by linarith
  have hSz:S ≠ 0:=ne_of_gt hS
  have hNz:N ≠ 0:=by linarith
  change 4 / ((gridDenominator l s n:ℝ) ^ 2 * L⁻¹)≤ (S⁻¹) ^ 2 / 4∧
    (L⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤ (S⁻¹) ^ 2 / 4
  rw [hid,inv_inv]
  constructor
  · field_simp
    nlinarith only [hN,hLN]
  · field_simp
    nlinarith only [hN,hnN,hLN]

theorem exactCut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
  have he:((2:ℝ) ^ (l + 2))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _=(1 / 4:ℝ) * (((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)):=by ring
    _≤ (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)):=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

theorem cut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=
  (exactCut_lower_bound n hn A hA a ha l hbound x).trans
    (roundedShape_sandwich (cutShape n A a) D hD x).1

theorem uniform_roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l s:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    let D:=gridDenominator (l + 2) s n
    let η:ℚ:=1 / (2:ℚ) ^ s
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  let D:=gridDenominator (l + 2) s n
  let η:ℚ:=1 / (2:ℚ) ^ s
  let lowerBound:=((2:ℝ) ^ (l + 2))⁻¹
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hη:0 < η:=by dsimp [η]; positivity
  have hl:0 < lowerBound:=by dsimp [lowerBound]; positivity
  have hcast:(η:ℝ)=((2:ℝ) ^ s)⁻¹:=by simp [η]
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hlower:=cut_lower_bound n hn A hA a ha D hD l hbound
  have hq:lowerBound≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
    have he:lowerBound=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
      dsimp [lowerBound]
      rw [pow_add]
      norm_num
    have hp:0≤ ((2:ℝ) ^ l)⁻¹:=by positivity
    have h:=hbound (realVector a)
    have h':=mul_le_mul_of_nonneg_left hanorm hp
    rw [he]
    nlinarith only [h,h',hp]
  have hprec:=dyadic_center_precision (l + 2) s n
  have hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4:=by
    rw [hcast]
    apply le_trans _ hprec.1
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    have hn₂:1≤ (n:ℝ) ^ 2:=by nlinarith
    have hprod:=mul_le_mul_of_nonneg_left hq (sq_nonneg (D:ℝ))
    have hqp:0≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by linarith
    have h:=mul_le_mul_of_nonneg_right hn₂
      (mul_nonneg (sq_nonneg (D:ℝ)) hqp)
    nlinarith only [hprod,h]
  apply roundedStep_contains n hn A hA a c ha D hD lowerBound hl η hη hlower hsqrt
  · simpa only [hcast] using hprec.2
  · exact hx
  · exact hcut

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidDeterminant

open Matrix EllipsoidRounding

theorem eigenvalue_le_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)) (i:ι):
    hA.eigenvalues i≤ k:=by
  let v:ι→ ℝ:=(hA.eigenvectorBasis i).ofLp
  have hv:v ≠ 0:=by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx:0 < v ⬝ᵥ v:=by
    simpa using (dotProduct_star_self_pos_iff (v:=v)).mpr hv
  have he:A *ᵥ v=hA.eigenvalues i • v:=hA.mulVec_eigenvectorBasis i
  have h:=hbound v
  rw [he,dotProduct_smul,smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

theorem det_le_pow_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosSemidef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)):
    A.det≤ k ^ Fintype.card ι:=by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s:=Finset.univ (α:=ι)) (g:=fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)

theorem det_le_relative_pow {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (B *ᵥ x)≤ k * (x ⬝ᵥ (A *ᵥ x))):
    B.det≤ k ^ Fintype.card ι * A.det:=by
  open scoped MatrixOrder in
  have hsqrt:∃ R:Matrix ι ι ℝ,R.IsHermitian∧ IsUnit R∧ R * R=A:=by
    let R:=CFC.sqrt A
    have hRR:R * R=A:=by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hu:IsUnit (R * R):=hRR.symm ▸ hA.isUnit
    exact ⟨R, (CFC.sqrt_nonneg A).posSemidef.1,
      isUnit_of_mul_isUnit_left hu,hRR⟩
  obtain ⟨R,hR,hu,hRR⟩:=hsqrt
  have hRinv:R⁻¹.IsHermitian:=hR.inv
  have hRi:IsUnit R⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hRRi:R * R⁻¹=1:=Matrix.mul_nonsing_inv R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRiR:R⁻¹ * R=1:=Matrix.nonsing_inv_mul R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  let C:=R⁻¹ * B * R⁻¹
  have hC:C.PosDef:=by
    simpa only [hRinv.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hRi)
  have hid:R⁻¹ * A * R⁻¹=1:=by
    rw [← hRR, ← Matrix.mul_assoc,hRiR,Matrix.one_mul,hRRi]
  have hform (M:Matrix ι ι ℝ) (x:ι→ ℝ):
      x ⬝ᵥ ((R⁻¹ * M * R⁻¹) *ᵥ x) =
        (R⁻¹ *ᵥ x) ⬝ᵥ (M *ᵥ (R⁻¹ *ᵥ x)):=by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (symmetric_form hRinv x (M *ᵥ (R⁻¹ *ᵥ x))).trans (dotProduct_comm _ _)
  have hb:∀ x,x ⬝ᵥ (C *ᵥ x)≤ k * (x ⬝ᵥ x):=by
    intro x
    have h:=hbound (R⁻¹ *ᵥ x)
    rw [← hform B x, ← hform A x,hid,Matrix.one_mulVec] at h
    exact h
  have hc:=det_le_pow_of_form_bound hC.posSemidef k hb
  have hdet:B.det=C.det * A.det:=by
    dsimp [C]
    rw [Matrix.det_mul,Matrix.det_mul, ← hRR,Matrix.det_mul]
    have hd:R.det * (R⁻¹).det=1:=by
      rw [← Matrix.det_mul,hRRi,Matrix.det_one]
    calc
      _=B.det * (R.det * (R⁻¹).det) ^ 2:=by rw [hd]; ring
      _=_:=by ring
  rw [hdet]
  exact mul_le_mul_of_nonneg_right hc (le_of_lt hA.det_pos)

end Lax109476Proofs.EllipsoidDeterminant

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

theorem stepAccuracy_pos (n:ℕ):0 < stepAccuracy n:=by
  unfold stepAccuracy
  positivity

theorem stepAccuracy_small (n:ℕ) (hn:2≤ n):
    (stepAccuracy n:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < 8 * (n:ℝ) * ((n:ℝ) + 1):=by positivity
  have h₁:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have h₂:(n:ℝ) + 1≤ (2:ℝ) ^ (n + 1):=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n + 1)).le
  have hprod:=mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he:(2:ℝ) ^ (2 * n + 4)=8 * ((2:ℝ) ^ n * (2:ℝ) ^ (n + 1)):=by
    rw [← pow_add,show 2 * n + 4=(n + (n + 1)) + 3 by omega,pow_add]
    norm_num
    ring
  have hb:8 * (n:ℝ) * ((n:ℝ) + 1)≤ (2:ℝ) ^ (2 * n + 4):=by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

theorem storedShape_relative_bound (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (hD:0 < D) (η:ℚ) (hη:0≤ η)
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + (η:ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
  have hp:(0:ℝ)≤ η:=by exact_mod_cast hη
  have h:=roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  calc
    _≤ (1 + (η:ℝ)) ^ 2 *
        ((1 + (η:ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))):=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_:=by ring

theorem storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η)
    (hsmall:(η:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)))
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound):
    Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have hη₁:(η:ℝ)≤ 1:=by
    have hh:1 / (8 * (n:ℝ) * ((n:ℝ) + 1))≤ 1:=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact hsmall.trans hh
  have hscalar:(1 + (η:ℝ)) ^ 3≤ (1 + 2 * (η:ℝ)) ^ 2:=by
    have hsq:(η:ℝ) ^ 2≤ η:=by nlinarith
    have hcube:=mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
    nlinarith only [hcube,hp,sq_nonneg (η:ℝ)]
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hP:=roundedStepShape_posDef n hn A hA a ha D hD η hη
  have hrelative:∀ x,x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + 2 * (η:ℝ)) ^ 2 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
    intro x
    have hnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
    exact (storedShape_relative_bound n A a D hD η (le_of_lt hη) lowerBound hlower hprecision x).trans
      (mul_le_mul_of_nonneg_right hscalar hnonneg)
  have hdet:=det_le_relative_pow hC hP ((1 + 2 * (η:ℝ)) ^ 2) hrelative
  rw [Fintype.card_fin] at hdet
  have hpow:((1 + 2 * (η:ℝ)) ^ 2) ^ n=((1 + 2 * (η:ℝ)) ^ n) ^ 2:=by
    rw [← pow_mul, ← pow_mul,Nat.mul_comm]
  have hsqrt:Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realShape (cutShape n A a)).det:=by
    have h:=Real.sqrt_le_sqrt hdet
    rw [hpow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h
  have hδ:2 * (η:ℝ)≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1)):=by
    calc
      _≤ 2 * (1 / (8 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _=_:=by
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]
        norm_num
        ring
  have hshrink:=EllipsoidStep.enlarged_shrink_bound n hn (2 * (η:ℝ))
    (by positivity) hδ
  rw [realShape_cutShape] at hsqrt
  change Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
    (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realCutShape n (realShape A) (realVector a)).det at hsqrt
  rw [det_realCutShape n hn (realShape A) hA (realVector a) ha] at hsqrt
  rw [Real.sqrt_mul (le_of_lt hA.det_pos)] at hsqrt
  calc
    _≤ ((1 + 2 * (η:ℝ)) ^ n * Real.sqrt (EllipsoidStep.determinantFactor n)) *
        Real.sqrt (realShape A).det:=by nlinarith only [hsqrt]
    _≤ _:=mul_le_mul_of_nonneg_right hshrink (Real.sqrt_nonneg _)

theorem uniform_storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)):
    Real.sqrt (realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hprec:=grid_shape_precision (l + 2) (2 * n + 4) n
  have hcast:(stepAccuracy n:ℝ)=((2:ℝ) ^ (2 * n + 4))⁻¹:=by
    simp [stepAccuracy]
  apply storedStep_shrink n hn A hA a ha _ (gridDenominator_pos _ _ _)
    (stepAccuracy n) (stepAccuracy_pos n) (stepAccuracy_small n hn)
    (((2:ℝ) ^ (l + 2))⁻¹) (exactCut_lower_bound n hn A hA a ha l hbound)
  simpa only [hcast] using hprec

theorem uniform_storedStep_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)) (x:Fin n→ ℝ):
    let P:=realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤ x ⬝ᵥ (P *ᵥ x)∧
      x ⬝ᵥ (P *ᵥ x)≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  let D:=gridDenominator (l + 2) (2 * n + 4) n
  let η:=stepAccuracy n
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hp:(0:ℝ) < η:=by exact_mod_cast stepAccuracy_pos n
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη:(η:ℝ)≤ 1 / 8:=by
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR:=roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg:0≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor:1≤ (1 + (η:ℝ)) ^ 2:=by nlinarith
  have hfactorUpper:(1 + (η:ℝ)) ^ 3≤ 2:=by
    calc
      _≤ (9 / 8:ℝ) ^ 3:=pow_le_pow_left₀ (by positivity) (by linarith) 3
      _≤ _:=by norm_num
  have hprec:2 * (n:ℝ) / D≤ (η:ℝ) * ((2:ℝ) ^ (l + 2))⁻¹:=by
    simpa [η,stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative:=storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse:=realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse':(1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h:=mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h,hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def shapes (n:ℕ) (a:ℕ→ Fin n→ ℚ):ℕ→ Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

def centers (n:ℕ) (a:ℕ→ Fin n→ ℚ) (c₀:Fin n→ ℚ):ℕ→ Fin n→ ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

theorem shapes_invariant (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    (realShape (shapes n a k)).PosDef∧
    ∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)≤ (4:ℝ) ^ k * (x ⬝ᵥ x):=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one,by simp⟩
  | succ k ih =>
      have hne:realVector (a k) ≠ 0:=by
        intro h
        have hh:=ha k
        rw [h,dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs:=uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he:((2:ℝ) ^ (2 * (k + 1)))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ (2 * k))⁻¹:=by
          rw [show 2 * (k + 1)=2 * k + 2 by omega,pow_add]
          norm_num
        constructor
        · rw [he]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0:ℝ)≤ 1 / 4 by norm_num)
          change _≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh,hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)≤ _
          rw [pow_succ]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0:ℝ)≤ 4 by norm_num)
          nlinarith only [hh,hs.2]

theorem shapes_shrink (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    Real.sqrt (realShape (shapes n a k)).det≤
      Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))):=by
  let v:=fun j => Real.sqrt (realShape (shapes n a j)).det
  have hstep:∀ j,v (j + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v j:=by
    intro j
    have hi:=shapes_invariant n hn a ha j
    exact uniform_storedStep_shrink n hn (shapes n a j) hi.1 (a j) (ha j)
      (2 * j) (fun x => (hi.2 x).1)
  have h:=EllipsoidStep.iterated_shrink_bound n v hstep k
  have hid:realShape (shapes n a 0)=1:=by
    ext i j
    simp [shapes,realShape,Matrix.one_apply,apply_ite]
  simpa only [v,hid,Matrix.det_one,Real.sqrt_one,mul_one] using h

theorem preserves_points_up_to (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (x:Fin n→ ℝ) (hx:(x - realVector c₀) ⬝ᵥ (x - realVector c₀)≤ 1)
    (k:ℕ)
    (hcut:∀ j < k,realVector (a j) ⬝ᵥ (x - realVector (centers n a c₀ j))≤ 0):
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k)))≤ 1:=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      simpa only [centers,hid,inv_one,Matrix.one_mulVec] using hx
  | succ k ih =>
      have hi:=shapes_invariant n hn a ha k
      exact uniform_roundedStep_contains n hn (shapes n a k) hi.1 (a k) (centers n a c₀ k)
        (ha k) (2 * k) (2 * n + 4) (fun y => (hi.2 y).1) x
        (ih (fun j hj => hcut j (by omega))) (hcut k (by omega))

theorem shapes_below_threshold (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (B:ℕ):
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2:ℝ) ^ B)⁻¹) ^ n:=by
  have htarget:0 < (((2:ℝ) ^ B)⁻¹) ^ n:=by positivity
  have hlog:Real.log (2:ℝ)≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlogtarget:Real.log ((((2:ℝ) ^ B)⁻¹) ^ n) =
      -((B * n:ℕ):ℝ) * Real.log 2:=by
    rw [Real.log_pow,Real.log_inv,Real.log_pow]
    push_cast
    ring
  have he:-(thresholdSteps n B:ℝ) / (4 * ((n:ℝ) + 1)) =
      -(((B * n:ℕ):ℝ) + 1):=by
    have hp:(n:ℝ) + 1 ≠ 0:=by positivity
    unfold thresholdSteps
    push_cast
    field_simp
  have hlt:-(((B * n:ℕ):ℝ) + 1) < -((B * n:ℕ):ℝ) * Real.log 2:=by
    have h:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (B * n))
    linarith
  have h:=shapes_shrink n hn a ha (thresholdSteps n B)
  rw [he] at h
  apply h.trans_lt
  rw [← Real.exp_log htarget,hlogtarget]
  exact Real.exp_lt_exp.mpr hlt

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι:Type} [Fintype ι] [DecidableEq ι]

theorem quadratic_parallelogram (A:Matrix ι ι ℝ) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)):=by
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub]
  ring

theorem inverse_form_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    ∀ u:ι→ ℝ,u ⬝ᵥ (A⁻¹ *ᵥ u)≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u):=by
  intro u
  by_cases hu:u=0
  · simp [hu]
  have hnorm:0 < u ⬝ᵥ u:=by
    simpa using (dotProduct_star_self_pos_iff (v:=u)).mpr hu
  let t:=r / Real.sqrt (u ⬝ᵥ u)
  let e:=t • u
  have ht:0 < t:=div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq:(Real.sqrt (u ⬝ᵥ u)) ^ 2=u ⬝ᵥ u:=Real.sq_sqrt hnorm.le
  have he:e ⬝ᵥ e=r ^ 2:=by
    simp only [e,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp:=hball e he.le
  have hm:=hball (-e) (by simpa using he.le)
  have hbase:0≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)):=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid:=quadratic_parallelogram A⁻¹ (z - c) e
  have hp':((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e))≤ 1:=by
    have heq:(z - c) + e=z + e - c:=by abel_nf
    rw [heq]
    exact hp
  have hm':((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e))≤ 1:=by
    have heq:(z - c) - e=z + -e - c:=by abel_nf
    rw [heq]
    exact hm
  have hqe:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ 1:=by linarith
  have hqe':t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ 1:=by
    simpa only [e,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform:t ^ 2=r ^ 2 / (u ⬝ᵥ u):=by
    dsimp [t]
    rw [div_pow,hsq]
  rw [htform,div_mul_eq_mul_div] at hqe'
  have hscale:r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ u ⬝ᵥ u:=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

theorem sqrt_det_lower_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    r ^ Fintype.card ι≤ Real.sqrt A.det:=by
  have hbound:=inverse_form_bound_of_ball hA z c r hr hball
  have hdet:=det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_pow] at hdet
  have ha:=hA.det_pos
  have hrpow:0 < (r ^ 2) ^ Fintype.card ι:=pow_pos (sq_pos_of_pos hr) _
  have hd:(r ^ 2) ^ Fintype.card ι≤ A.det:=(inv_le_inv₀ ha hrpow).mp hdet
  have hs:=Real.sq_sqrt ha.le
  have hsr:=Real.sqrt_nonneg A.det
  have hrr:(r ^ Fintype.card ι) ^ 2=(r ^ 2) ^ Fintype.card ι:=by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end Lax109476Proofs.EllipsoidBall

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidTermination

open Lax109476.RationalCertificates
open EllipsoidRounding EllipsoidSequence EllipsoidBall

theorem cannot_retain_ball (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector c₀) ⬝ᵥ (z + e - realVector c₀)≤ 1):
    ¬ ∀ k < thresholdSteps n B, ∀ e:Fin n→ ℝ,
      e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      realVector (a k) ⬝ᵥ (z + e - realVector (centers n a c₀ k))≤ 0:=by
  intro hcut
  let K:=thresholdSteps n B
  have hshape:=(shapes_invariant n hn a ha K).1
  have hball:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector (centers n a c₀ K)) ⬝ᵥ
        ((realShape (shapes n a K))⁻¹ *ᵥ (z + e - realVector (centers n a c₀ K)))≤ 1:=by
    intro e he
    exact preserves_points_up_to n hn a ha c₀ (z + e) (hunit e he) K
      (fun j hj => hcut j hj e he)
  have hlo:=sqrt_det_lower_bound_of_ball hshape z (realVector (centers n a c₀ K))
    (((2:ℝ) ^ B)⁻¹) (by positivity) hball
  have hhi:=shapes_below_threshold n hn a ha B
  simp only [Fintype.card_fin] at hlo
  exact (not_lt_of_ge hlo) hhi

end Lax109476Proofs.EllipsoidTermination

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

@[simp] theorem cacheState_eq {n:ℕ}
    (state:Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)):cacheState state=state:=by
  apply Prod.ext
  · funext i j
    simp [cacheState,Vector.get]
    rfl
  · funext i
    simp [cacheState,Vector.get]
    rfl

def trajectory {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ):
    ℕ→ Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)
  | 0 => (1,0)
  | k + 1 => nextState A b k (trajectory A b k)

def normalSchedule {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (k:ℕ):Fin n→ ℚ:=selectedNormal A b (trajectory A b k).2

theorem fallbackNormal_norm (n:ℕ) (hn:0 < n):
    1≤ realVector (fallbackNormal n) ⬝ᵥ realVector (fallbackNormal n):=by
  let a:Fin n→ ℤ:=fun j => if j.val=0 then 1 else 0
  have ha:a ≠ 0:=by
    intro h
    have hz:=congrFun h ⟨0,hn⟩
    simp [a] at hz
  have hc:realVector (fallbackNormal n) =
      (fun j:Fin n => (if j.val=0 then 1 else 0:ℝ)):=by
    funext j
    change ((if j.val=0 then 1 else 0:ℚ):ℝ)=_
    split_ifs <;> norm_num
  rw [hc]
  simpa [a,apply_ite] using integer_normal_norm a ha

theorem selectedNormal_norm {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (hn:0 < n):
    1≤ realVector (selectedNormal A b c) ⬝ᵥ realVector (selectedNormal A b c):=by
  unfold selectedNormal
  split
  · exact fallbackNormal_norm n hn
  · split_ifs with hz
    · exact fallbackNormal_norm n hn
    · change 1≤ (fun j => (A _ j:ℝ)) ⬝ᵥ (fun j => (A _ j:ℝ))
      exact integer_normal_norm _ hz

theorem trajectory_eq_sequences {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (k:ℕ):
    (trajectory A b k).1=shapes n (normalSchedule A b) k∧
      (trajectory A b k).2=centers n (normalSchedule A b) 0 k:=by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [trajectory,nextState,shapes,centers,cacheState_eq]
    have ha:selectedNormal A b (trajectory A b k).2=normalSchedule A b k:=rfl
    rw [ha,ih.1,ih.2]
    exact ⟨rfl,rfl⟩

def findFirst (p:ℕ→ Bool):ℕ→ ℕ→ Option ℕ
  | _,0 => none
  | start,count + 1 => if p start then some start else findFirst p (start + 1) count

theorem findFirst_eq_find (p:ℕ→ Bool) (start count:ℕ):
    findFirst p start count=(List.range' start count).find? p:=by
  induction count generalizing start with
  | zero => simp [findFirst]
  | succ count ih =>
    cases hp:p start <;> simp [findFirst,List.range'_succ,ih,hp]

theorem scanStates_eq_findFirst {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (start count:ℕ):
    scanStates A b start count (trajectory A b start) =
      findFirst (fun k => decide (firstViolation A b (trajectory A b k).2=none)) start count:=by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [scanStates,findFirst,decide_eq_true_eq]
    by_cases h:firstViolation A b (trajectory A b start).2=none
    · rw [if_pos h,if_pos h]
    · rw [if_neg h,if_neg h]
      exact ih (start + 1)

theorem findIteration_eq_find {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):findIteration A b K =
      (List.range (K + 1)).find? (fun k => decide (firstViolation A b (trajectory A b k).2=none)):=by
  change scanStates A b 0 (K + 1) (trajectory A b 0)=_
  rw [scanStates_eq_findFirst,findFirst_eq_find,List.range_eq_range']

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

theorem foundIteration_feasible {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (K k:ℕ) (h:findIteration A b K=some k):
    ∀ i,rowValue A (trajectory A b k).2 i≤ b i:=by
  rw [findIteration_eq_find] at h
  have hp:=List.find?_some h
  have hv:firstViolation A b (trajectory A b k).2=none:=by simpa using hp
  exact (firstViolation_none A b _).mp hv

theorem noIteration_violated {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (K:ℕ) (h:findIteration A b K=none):
    ∀ k≤ K,firstViolation A b (trajectory A b k).2 ≠ none:=by
  rw [findIteration_eq_find] at h
  have hp:=List.find?_eq_none.mp h
  intro k hk
  simpa using hp k (List.mem_range.mpr (by omega))

theorem search_finds_ball {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (hn:2≤ n) (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e) ⬝ᵥ (z + e)≤ 1)
    (hfeas:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      ∀ i, (∑ j, (A i j:ℝ) * (z + e) j)≤ (b i:ℝ)):
    ∃ k,findIteration A b (thresholdSteps n B)=some k:=by
  by_contra h
  have hnone:findIteration A b (thresholdSteps n B)=none:=by
    cases hfind:findIteration A b (thresholdSteps n B) with
    | none => rfl
    | some k => exact False.elim (h ⟨k,hfind⟩)
  have hnorm:∀ k,1≤ realVector (normalSchedule A b k) ⬝ᵥ
      realVector (normalSchedule A b k):=fun k => selectedNormal_norm A b _ (by omega)
  have hzero:realVector (0:Fin n→ ℚ)=0:=by funext j; simp [realVector]
  apply cannot_retain_ball n hn (normalSchedule A b) hnorm 0 z B
    (by simpa only [hzero,sub_zero] using hunit)
  intro k hk e he
  have hvne:=noIteration_violated A b _ hnone k (by omega)
  cases hv:firstViolation A b (trajectory A b k).2 with
  | none => exact False.elim (hvne hv)
  | some i =>
    have haz:A i ≠ 0:=by
      intro haz
      apply zero_row_infeasible A b _ i hv haz
      exact ⟨z + e,hfeas e he⟩
    have hnormal:normalSchedule A b k=rationalRow A i:=by
      simp [normalSchedule,selectedNormal,hv,haz]
    have hcenter:=(trajectory_eq_sequences A b k).2
    rw [hnormal, ← hcenter]
    exact (violation_retains_points A b _ i hv (z + e) (hfeas e he i)).le

end Lax109476Proofs.EllipsoidSearch

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

theorem normalized_iff_relaxed {m n:ℕ} (P:Program ℤ m n) (R:ℕ) (ε:ℚ)
    (z:Fin n→ ℝ):
    (∀ i, (∑ j, (normalizedMatrix P R i j:ℝ) * z j)≤ (normalizedBound P ε i:ℝ))↔
      RelaxedFeasible (toReal (rationalProgram P)) (ε:ℝ) ((R:ℝ) • z):=by
  constructor
  · intro h
    constructor
    · intro j
      have hj:=h (Fin.natAdd m j)
      have hh:-(R:ℝ) * z j≤ (ε:ℝ):=by
        simpa [normalizedMatrix,normalizedBound,apply_ite] using hj
      change -(ε:ℝ)≤ (R:ℝ) * z j
      linarith
    · intro i
      have hi:=h (Fin.castAdd n i)
      simpa [normalizedMatrix,normalizedBound,rowValue,toReal,
        rationalProgram,Finset.mul_sum,mul_assoc,mul_left_comm] using hi
  · rintro ⟨hnonneg,hrows⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [normalizedMatrix,normalizedBound,rowValue,toReal,
        rationalProgram,Finset.mul_sum,mul_assoc,mul_left_comm] using hrows i
    · intro j
      have hj:-(R:ℝ) * z j≤ (ε:ℝ):=by
        have h:=hnonneg j
        change -(ε:ℝ)≤ (R:ℝ) * z j at h
        linarith
      simpa [normalizedMatrix,normalizedBound,apply_ite] using hj

theorem outerScale_pos (n B:ℕ):0 < outerScale n B:=by
  unfold outerScale
  positivity

theorem outerScale_large (n B:ℕ):
    (n:ℝ) * (B:ℝ) ^ 2≤ (outerScale n B:ℝ) ^ 2 / 16:=by
  have hn:(n:ℝ)≤ ((n:ℝ) + 1) ^ 2:=by nlinarith
  have hb:(B:ℝ) ^ 2≤ ((B:ℝ) + 1) ^ 2:=by
    nlinarith [(Nat.cast_nonneg B:(0:ℝ)≤ B)]
  have h:=mul_le_mul hn hb (sq_nonneg (B:ℝ)) (sq_nonneg ((n:ℝ) + 1))
  simp only [outerScale,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  nlinarith

theorem scaled_point_norm {n:ℕ} (x:Fin n→ ℝ) (B:ℕ)
    (hx:∀ j, |x j|≤ (B:ℝ)):
    ((outerScale n B:ℝ)⁻¹ • x) ⬝ᵥ ((outerScale n B:ℝ)⁻¹ • x)≤ 1 / 16:=by
  have hr:(0:ℝ) < outerScale n B:=by exact_mod_cast outerScale_pos n B
  have hs:x ⬝ᵥ x≤ (n:ℝ) * (B:ℝ) ^ 2:=by
    calc
      _≤ ∑ _j:Fin n, (B:ℝ) ^ 2:=by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [(abs_le.mp (hx j)).1, (abs_le.mp (hx j)).2]
      _=_:=by simp
  have hlarge:=outerScale_large n B
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [← mul_assoc, ← pow_two,inv_pow,inv_mul_eq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  linarith

theorem ball_inside_unit {n:ℕ} (z:Fin n→ ℝ) (hz:z ⬝ᵥ z≤ 1 / 16)
    (r:ℝ) (hr:0≤ r) (hrsmall:r≤ 1 / 2):
    ∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ r ^ 2→ (z + e) ⬝ᵥ (z + e)≤ 1:=by
  intro e he
  have h:=EllipsoidCenter.form_add_le_two
    (show (1:Matrix (Fin n) (Fin n) ℝ).PosDef from Matrix.PosDef.one) z e
  simp only [Matrix.one_mulVec] at h
  nlinarith

theorem precisionDenominator_pos (m n H:ℕ):0 < precisionDenominator m n H:=by
  unfold precisionDenominator relaxationDenominator
  positivity

theorem ballDenominator_pos (m n H:ℕ):0 < ballDenominator m n H:=by
  unfold ballDenominator
  exact Nat.mul_pos (Nat.mul_pos (precisionDenominator_pos _ _ _) (by omega))
    (outerScale_pos _ _)

theorem ballDenominator_ge_two (m n H:ℕ):2≤ ballDenominator m n H:=by
  have hD:2≤ precisionDenominator m n H:=by
    unfold precisionDenominator relaxationDenominator
    omega
  exact hD.trans ((Nat.le_mul_of_pos_right _ (by omega:0 < n * H + 1)).trans
    (Nat.le_mul_of_pos_right _ (outerScale_pos _ _)))

theorem dyadic_radius_bound (m n H:ℕ):
    ((2:ℝ) ^ ballExponent m n H)⁻¹≤ 1 / (ballDenominator m n H:ℝ):=by
  have hN:(0:ℝ) < ballDenominator m n H:=by exact_mod_cast ballDenominator_pos m n H
  have hpow:(0:ℝ) < 2 ^ ballExponent m n H:=by positivity
  rw [one_div]
  apply (inv_le_inv₀ hpow hN).mpr
  exact_mod_cast (Nat.lt_size_self (ballDenominator m n H)).le

theorem dyadic_radius_small (m n H:ℕ):
    ((2:ℝ) ^ ballExponent m n H)⁻¹≤ 1 / 2:=by
  have hN:(0:ℝ) < ballDenominator m n H:=by exact_mod_cast ballDenominator_pos m n H
  have hN₂:(2:ℝ)≤ ballDenominator m n H:=by exact_mod_cast ballDenominator_ge_two m n H
  apply (dyadic_radius_bound m n H).trans
  rw [one_div]
  simpa only [one_div] using (inv_le_inv₀ hN (by norm_num:(0:ℝ) < 2)).mpr hN₂

theorem normalized_feasible_ball {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):
    ∃ z:Fin n→ ℝ,
      (∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ ballExponent m n H)⁻¹) ^ 2→
        (z + e) ⬝ᵥ (z + e)≤ 1)∧
      ∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ ballExponent m n H)⁻¹) ^ 2→
        ∀ i, (∑ j, (normalizedMatrix P (outerScale n (coordinateCap m n H)) i j:ℝ) *
          (z + e) j)≤ (normalizedBound P (1 / (precisionDenominator m n H:ℚ)) i:ℝ):=by
  let B:=coordinateCap m n H
  let R:=outerScale n B
  let D:=precisionDenominator m n H
  let ε:ℝ:=1 / (D:ℝ)
  let r:=((2:ℝ) ^ ballExponent m n H)⁻¹
  obtain ⟨x,hx,hxb⟩:=bounded_real_feasible_point P H hH hA hb hf
  let z:=(R:ℝ)⁻¹ • x
  have hR:(0:ℝ) < R:=by exact_mod_cast outerScale_pos n B
  have hD:(0:ℝ) < D:=by exact_mod_cast precisionDenominator_pos m n H
  have hε:0 < ε:=by dsimp [ε]; positivity
  have hHR:(0:ℝ)≤ H:=by positivity
  have hAR:∀ i j, |(toReal (rationalProgram P)).A i j|≤ (H:ℝ):=by
    intro i j
    have h:((P.A i j).natAbs:ℝ)≤ (H:ℝ):=by exact_mod_cast hA i j
    simpa [toReal,rationalProgram,Nat.cast_natAbs,Int.cast_abs] using h
  have hrad:r≤ cubeRadius n (H:ℝ) ε / (R:ℝ):=by
    have hid:cubeRadius n (H:ℝ) ε / (R:ℝ)=1 / (ballDenominator m n H:ℝ):=by
      dsimp only [cubeRadius,ε]
      rw [div_div,div_div]
      congr 1
      simp only [ballDenominator,D,R,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_assoc]
    rw [hid]
    exact dyadic_radius_bound m n H
  refine ⟨z,ball_inside_unit z (scaled_point_norm x B hxb) r
    (by dsimp [r]; positivity) (dyadic_radius_small m n H), ?_⟩
  intro e he
  change e ⬝ᵥ e≤ r ^ 2 at he
  have hrscale:(R:ℝ) * r≤ cubeRadius n (H:ℝ) ε:=by
    have h:=(le_div_iff₀ hR).mp hrad
    simpa [mul_comm] using h
  have heR:((R:ℝ) • e) ⬝ᵥ ((R:ℝ) • e)≤ (cubeRadius n (H:ℝ) ε) ^ 2:=by
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
    have h:=mul_le_mul_of_nonneg_left he (sq_nonneg (R:ℝ))
    have hrpos:0≤ r:=by dsimp [r]; positivity
    have hrhopos:=(cubeRadius_bounds n (H:ℝ) ε hHR hε).1
    have hs:((R:ℝ) * r) ^ 2≤ (cubeRadius n (H:ℝ) ε) ^ 2:=
      pow_le_pow_left₀ (mul_nonneg hR.le hrpos) hrscale 2
    nlinarith
  have hrelax:=ball_in_relaxation (toReal (rationalProgram P)) (H:ℝ) ε
    hHR hε hAR x hx ((R:ℝ) • e) heR
  have hscale:(R:ℝ) • (z + e)=x + (R:ℝ) • e:=by
    simp only [z,smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt hR),one_smul]
  apply (normalized_iff_relaxed P R (1 / (D:ℚ)) (z + e)).mpr
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,hscale] using hrelax

end Lax109476Proofs.NormalizedFeasibility

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation NormalizedFeasibility
open EllipsoidSearch EllipsoidSequence

theorem feasible_of_feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):feasible P H=true:=by
  obtain ⟨z,hunit,hball⟩:=normalized_feasible_ball P H hH hA hb hf
  obtain ⟨k,hk⟩:=search_finds_ball
    (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H:ℚ))) hn z
    (ballExponent m n H) hunit hball
  simp only [feasible,iterationResult,hk,Option.isSome_some]

theorem feasible_sound {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H) (h:feasible P H=true):
    IsFeasible (toReal (rationalProgram P)):=by
  let R:=outerScale n (coordinateCap m n H)
  let D:=precisionDenominator m n H
  let A:=normalizedMatrix P R
  let b:=normalizedBound P (1 / (D:ℚ))
  cases hi:iterationResult P H with
  | none => simp [feasible,hi] at h
  | some k =>
    have hr:=foundIteration_feasible A b (thresholdSteps n (ballExponent m n H)) k hi
    let x:=realVector (trajectory A b k).2
    have hrreal:∀ i, (∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ):=by
      intro i
      have h:=(Rat.cast_le (K:=ℝ)).mpr (hr i)
      simpa [RationalSeparation.rowValue,x,realVector] using h
    have hrelax:=(normalized_iff_relaxed P R (1 / (D:ℚ)) x).mp hrreal
    by_contra hf
    apply integer_relaxation_infeasible P H hH hA hb hf
    refine ⟨(R:ℝ) • x, ?_⟩
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,D,precisionDenominator] using hrelax

theorem feasible_correct {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H):
    feasible P H=true↔ IsFeasible (toReal (rationalProgram P)):=
  ⟨feasible_sound P H hH hA hb,feasible_of_feasible P H hn hH hA hb⟩

end Lax109476Proofs.IntegerFeasibilityDecision

end

section

open scoped BigOperators

namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

theorem extend_feasible {m n:ℕ} (P:Program ℝ m n) (x:Fin n→ ℝ)
    (hx:PrimalFeasible P x):
    PrimalFeasible (pad P) (Fin.addCases x (fun _ => 0)):=by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simpa using hx.1 j
    · intro j
      simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad,rowValue,Fin.sum_univ_add] using hx.2 i
    · intro i
      simp [pad,rowValue,Fin.sum_univ_add]

theorem restrict_feasible {m n:ℕ} (P:Program ℝ m n) (x:Fin (n + 2)→ ℝ)
    (hx:PrimalFeasible (pad P) x):
    PrimalFeasible P (fun j => x (Fin.castAdd 2 j)):=by
  constructor
  · intro j
    exact hx.1 (Fin.castAdd 2 j)
  · intro i
    simpa [pad,rowValue,Fin.sum_univ_add] using hx.2 (Fin.castAdd 2 i)

theorem pad_feasible_iff {m n:ℕ} (P:Program ℝ m n):
    IsFeasible (pad P)↔ IsFeasible P:=by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨_,restrict_feasible P x hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨_,extend_feasible P x hx⟩

theorem cast_pad {m n:ℕ} (P:Program ℤ m n):
    toReal (rationalProgram (pad P))=pad (toReal (rationalProgram P)):=by
  unfold pad toReal rationalProgram
  congr 1
  · funext i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [apply_ite]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

theorem padded_bounds {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H):
    (∀ i j, ((pad P).A i j).natAbs≤ H)∧ (∀ i, ((pad P).b i).natAbs≤ H):=by
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simpa [pad] using hA i j
      · intro j
        simp [pad]
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp [pad]
      · intro j
        simp only [pad,Fin.addCases_right]
        split_ifs <;> simp_all
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad] using hb i
    · intro i
      simp [pad]

theorem feasible_correct {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H):
    feasible P H=true↔ IsFeasible (toReal (rationalProgram P)):=by
  obtain ⟨ha,hb⟩:=padded_bounds P H hH hA hb
  rw [feasible,IntegerFeasibilityDecision.feasible_correct (pad P) H (by omega) hH ha hb,
    cast_pad,pad_feasible_iff]

end Lax109476Proofs.FeasibilityPadding

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding EncodingSize NormalizedFeasibility EllipsoidSequence

theorem scaled_real_feasible_iff {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (x:Fin n→ ℝ):
    PrimalFeasible (toReal (scaledProgram P s)) x↔ PrimalFeasible (toReal P) x:=by
  have hsR:(0:ℝ) < (s:ℝ):=by exact_mod_cast hs
  have hrow:∀ i,rowValue (toReal (scaledProgram P s)) x i =
      (s:ℝ) * rowValue (toReal P) x i:=by
    intro i
    simp only [rowValue,toReal,scaledProgram,Rat.cast_mul,Finset.mul_sum,mul_assoc]
  constructor
  · rintro ⟨hxpos,hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    have h:=hxrows i
    rw [hrow] at h
    have hi:(s:ℝ) * rowValue (toReal P) x i≤ (s:ℝ) * (P.b i:ℝ):=by
      simpa [toReal,scaledProgram] using h
    exact (mul_le_mul_iff_of_pos_left hsR).mp hi
  · rintro ⟨hxpos,hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    rw [hrow]
    simpa [toReal,scaledProgram] using (mul_le_mul_iff_of_pos_left hsR).mpr (hxrows i)

theorem integerProgram_feasible_iff {m n:ℕ} (P:Program ℚ m n):
    IsFeasible (toReal (rationalProgram (integerProgram P)))↔ IsFeasible (toReal P):=by
  rw [integerProgram_eq_scaled]
  have hs:0 < (programDenominator P:ℚ):=by
    exact_mod_cast RationalSizeBounds.commonDenominator_pos (programData P)
  exact exists_congr (fun x => scaled_real_feasible_iff P _ hs x)

theorem coefficient_bounds {m n:ℕ} (P:Program ℚ m n):
    (∀ i j, ((integerProgram P).A i j).natAbs≤ 2 ^ (2 * sizeParameter P))∧
      (∀ i, ((integerProgram P).b i).natAbs≤ 2 ^ (2 * sizeParameter P)):=by
  obtain ⟨hA,hb,_⟩:=integerProgram_bounds P
  have hp:2 ^ (2 * bitSize (encodeProgram P))≤ 2 ^ (2 * sizeParameter P):=
    Nat.pow_le_pow_right (by decide) (by unfold sizeParameter; omega)
  exact ⟨fun i j => (hA i j).trans hp,fun i => (hb i).trans hp⟩

theorem feasible_correct {m n:ℕ} (P:Program ℚ m n):
    feasible P=true↔ IsFeasible (toReal P):=by
  obtain ⟨hA,hb⟩:=coefficient_bounds P
  have hH:1≤ 2 ^ (2 * sizeParameter P):=by
    have hp:0 < 2 ^ (2 * sizeParameter P):=by positivity
    omega
  rw [feasible,FeasibilityPadding.feasible_correct _ _ hH hA hb,
    integerProgram_feasible_iff]

end Lax109476Proofs.RationalFeasibilityDecision

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

namespace Lax109476Proofs.IndexedPointRecovery

open Lax109476.LinearProgram IntegerEncoding

theorem reindex_row {κ ι:Type*} [Fintype ι] {r n:ℕ} (A:κ→ ι→ ℤ) (b:κ→ ℤ)
    (er:κ ≃ Fin r) (ec:ι ≃ Fin n) (x:Fin n→ ℚ) (i:κ):
    rowValue (rationalProgram (reindexProgram A b er ec)) x (er i) =
      ∑ j, (A i j:ℚ) * x (ec j):=by
  have h:=ec.sum_comp (fun j:Fin n => (A i (ec.symm j):ℚ) * x j)
  simpa [rowValue,rationalProgram,reindexProgram] using h.symm

end Lax109476Proofs.IndexedPointRecovery

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateSystems

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding IntegerCertificates

def NonnegativeFeasible {κ ι:Type*} [Fintype ι]
    (A:κ→ ι→ ℤ) (b:κ→ ℤ) (z:ι→ ℚ):Prop:=
  (∀ j,0≤ z j)∧ ∀ i, (∑ j, (A i j:ℚ) * z j)≤ (b i:ℚ)

theorem pair_valid {m n:ℕ} (P:Program ℤ m n) (z:(Fin n ⊕ Fin m)→ ℚ)
    (hz:NonnegativeFeasible (pairMatrix P) (pairBound P) z):
    IsValidCertificate (rationalProgram P) (.optimal (fun j => z (.inl j)) (fun i => z (.inr i))):=by
  refine ⟨⟨fun j => hz.1 _,fun i => ?_⟩, ⟨fun i => hz.1 _,fun j => ?_⟩, ?_⟩
  · simpa [pairMatrix,pairBound,Fintype.sum_sum_type,rowValue,rationalProgram]
      using hz.2 (.inl i)
  · have h:-columnValue (rationalProgram P) (fun i => z (.inr i)) j≤ -(P.c j:ℚ):=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,columnValue,
        rationalProgram,Finset.sum_neg_distrib] using hz.2 (.inr (.inl j))
    exact neg_le_neg_iff.mp h
  · have h₁:primalValue (rationalProgram P) (fun j => z (.inl j)) -
        dualValue (rationalProgram P) (fun i => z (.inr i))≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,primalValue,
        dualValue,rationalProgram,Finset.sum_neg_distrib,sub_eq_add_neg]
        using hz.2 (.inr (.inr false))
    have h₂:-primalValue (rationalProgram P) (fun j => z (.inl j)) +
        dualValue (rationalProgram P) (fun i => z (.inr i))≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,primalValue,
        dualValue,rationalProgram,Finset.sum_neg_distrib]
        using hz.2 (.inr (.inr true))
    linarith

theorem pair_feasible {m n:ℕ} (P:Program ℤ m n) (x:Fin n→ ℚ) (y:Fin m→ ℚ)
    (hv:IsValidCertificate (rationalProgram P) (.optimal x y)):
    ∃ z,NonnegativeFeasible (pairMatrix P) (pairBound P) z:=by
  refine ⟨Sum.elim x y, ?_, ?_⟩
  · intro j
    cases j with
    | inl j => exact hv.1.1 j
    | inr i => exact hv.2.1.1 i
  · intro i
    cases i with
    | inl i => simpa [pairMatrix,pairBound,Fintype.sum_sum_type,
        rowValue,rationalProgram] using hv.1.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix,pairBound,Fintype.sum_sum_type,columnValue,
          rationalProgram,Finset.sum_neg_distrib] using neg_le_neg (hv.2.1.2 j)
      | inr v =>
        cases v
        · have h:primalValue (rationalProgram P) x - dualValue (rationalProgram P) y≤ 0:=
            by rw [hv.2.2]; simp
          simpa [pairMatrix,pairBound,Fintype.sum_sum_type,primalValue,
            dualValue,rationalProgram,Finset.sum_neg_distrib,sub_eq_add_neg] using h
        · have h:-primalValue (rationalProgram P) x + dualValue (rationalProgram P) y≤ 0:=
            by rw [hv.2.2]; simp
          simpa [pairMatrix,pairBound,Fintype.sum_sum_type,primalValue,
            dualValue,rationalProgram,Finset.sum_neg_distrib] using h

def farkasMatrix {m n:ℕ} (P:Program ℤ m n):(Fin n ⊕ Unit)→ Fin m→ ℤ:=
  Sum.elim (fun j i => -P.A i j) (fun _ => P.b)

def farkasBound {n:ℕ}:(Fin n ⊕ Unit)→ ℤ:=
  Sum.elim (fun _ => 0) (fun _ => -1)

theorem farkas_valid {m n:ℕ} (P:Program ℤ m n) (y:Fin m→ ℚ)
    (hy:NonnegativeFeasible (farkasMatrix P) farkasBound y):
    IsValidCertificate (rationalProgram P) (.infeasible y):=by
  refine ⟨hy.1,fun j => ?_, ?_⟩
  · have h:-columnValue (rationalProgram P) y j≤ 0:=by
      simpa [farkasMatrix,farkasBound,columnValue,rationalProgram,
        Finset.sum_neg_distrib] using hy.2 (.inl j)
    linarith
  · have h:dualValue (rationalProgram P) y≤ -1:=by
      simpa [farkasMatrix,farkasBound,dualValue,rationalProgram] using hy.2 (.inr ())
    linarith

theorem farkas_feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H)
    (y:Fin m→ ℚ) (hy:IsValidCertificate (rationalProgram P) (.infeasible y)):
    ∃ z,NonnegativeFeasible (farkasMatrix P) farkasBound z:=by
  obtain ⟨z,hz,_,hn⟩:=normalized_small_infeasibility_certificate P H hH hA hb y hy
  refine ⟨z,hz.1,fun i => ?_⟩
  cases i with
  | inl j =>
    simpa [farkasMatrix,farkasBound,columnValue,rationalProgram,Finset.sum_neg_distrib]
      using neg_nonpos.mpr (hz.2.1 j)
  | inr _ => simpa [farkasMatrix,farkasBound,dualValue,rationalProgram] using hn

theorem ray_valid {m n:ℕ} (P:Program ℤ m n) (z:(Fin n ⊕ Fin n)→ ℚ)
    (hz:NonnegativeFeasible (rayMatrix P) (rayBound P) z):
    IsValidCertificate (rationalProgram P) (.unbounded (fun j => z (.inl j)) (fun j => z (.inr j))):=by
  refine ⟨⟨fun j => hz.1 _,fun i => ?_⟩,fun j => hz.1 _,fun i => ?_, ?_⟩
  · simpa [rayMatrix,rayBound,Fintype.sum_sum_type,rowValue,rationalProgram]
      using hz.2 (.inl i)
  · simpa [rayMatrix,rayBound,Fintype.sum_sum_type,rowValue,rationalProgram]
      using hz.2 (.inr (.inl i))
  · have h:-primalValue (rationalProgram P) (fun j => z (.inr j))≤ -1:=by
      simpa [rayMatrix,rayBound,Fintype.sum_sum_type,primalValue,
        rationalProgram,Finset.sum_neg_distrib] using hz.2 (.inr (.inr ()))
    linarith

theorem ray_feasible {m n:ℕ} (P:Program ℤ m n) (x d:Fin n→ ℚ)
    (hv:IsValidCertificate (rationalProgram P) (.unbounded x d)):
    ∃ z,NonnegativeFeasible (rayMatrix P) (rayBound P) z:=by
  let t:=(primalValue (rationalProgram P) d)⁻¹
  have ht:0 < t:=inv_pos.mpr hv.2.2.2
  refine ⟨Sum.elim x (fun j => t * d j), ?_, ?_⟩
  · intro j
    cases j with
    | inl j => exact hv.1.1 j
    | inr j => exact mul_nonneg ht.le (hv.2.1 j)
  · intro i
    cases i with
    | inl i => simpa [rayMatrix,rayBound,Fintype.sum_sum_type,rowValue,
        rationalProgram] using hv.1.2 i
    | inr i =>
      cases i with
      | inl i =>
        have hscale:(∑ j, (P.A i j:ℚ) * (t * d j)) =
            t * rowValue (rationalProgram P) d i:=by
          simp only [rowValue,rationalProgram,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [rayMatrix,rayBound,Fintype.sum_sum_type,Sum.elim_inl,
          Sum.elim_inr,Int.cast_zero,zero_mul,Finset.sum_const_zero,zero_add]
        rw [hscale]
        exact mul_nonpos_of_nonneg_of_nonpos ht.le (hv.2.2.1 i)
      | inr _ =>
        have hscale:(∑ j, -(P.c j:ℚ) * (t * d j)) =
            -(t * primalValue (rationalProgram P) d):=by
          simp only [primalValue,rationalProgram,Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [rayMatrix,rayBound,Fintype.sum_sum_type,Sum.elim_inl,
          Sum.elim_inr,Int.cast_zero,Int.cast_neg,Int.cast_one,zero_mul,
          Finset.sum_const_zero,zero_add]
        rw [hscale]
        dsimp [t]
        rw [inv_mul_cancel₀ (ne_of_gt hv.2.2.2)]

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

theorem reindex_feasible {κ ι:Type*} [Fintype ι] {r s:ℕ} (A:κ→ ι→ ℤ) (b:κ→ ℤ)
    (er:κ ≃ Fin r) (ec:ι ≃ Fin s) (x:Fin s→ ℚ)
    (hx:PrimalFeasible (rationalProgram (reindexProgram A b er ec)) x):
    NonnegativeFeasible A b (fun j => x (ec j)):=by
  refine ⟨fun j => hx.1 _,fun i => ?_⟩
  have hr:=hx.2 (er i)
  rw [reindex_row] at hr
  simpa [rationalProgram,reindexProgram] using hr

theorem reindex_exists {κ ι:Type*} [Fintype ι] {r s:ℕ} (A:κ→ ι→ ℤ) (b:κ→ ℤ)
    (er:κ ≃ Fin r) (ec:ι ≃ Fin s) (hf:∃ x,NonnegativeFeasible A b x):
    IsFeasible (toReal (rationalProgram (reindexProgram A b er ec))):=by
  obtain ⟨x,hx⟩:=hf
  let z:Fin s→ ℚ:=fun j => x (ec.symm j)
  have hz:PrimalFeasible (rationalProgram (reindexProgram A b er ec)) z:=by
    refine ⟨fun j => hx.1 _,fun i => ?_⟩
    have hr:=hx.2 (er.symm i)
    have he:=reindex_row A b er ec z (er.symm i)
    rw [Equiv.apply_symm_apply] at he
    rw [he]
    simpa [z,rationalProgram,reindexProgram] using hr
  exact ⟨realVector z,RationalFeasibility.cast_feasible _ _ hz⟩

theorem optimal_valid {m n:ℕ} (P:Program ℤ m n) (x:Fin (n + m)→ ℚ)
    (hx:PrimalFeasible (rationalProgram (optimal P)) x):
    IsValidCertificate (rationalProgram P)
      (.optimal (fun j => x (Fin.castAdd m j)) (fun i => x (Fin.natAdd n i))):=by
  have h:=pair_valid P (fun j => x (finSumFinEquiv j))
    (reindex_feasible (pairMatrix P) (pairBound P) (pairRows m n) finSumFinEquiv x hx)
  simpa [finSumFinEquiv] using h

theorem infeasible_valid {m n:ℕ} (P:Program ℤ m n) (x:Fin m→ ℚ)
    (hx:PrimalFeasible (rationalProgram (infeasible P)) x):
    IsValidCertificate (rationalProgram P) (.infeasible x):=
  farkas_valid P x (reindex_feasible (farkasMatrix P) farkasBound (farkasRows n) (Equiv.refl _) x hx)

theorem unbounded_valid {m n:ℕ} (P:Program ℤ m n) (x:Fin (n + n)→ ℚ)
    (hx:PrimalFeasible (rationalProgram (unbounded P)) x):
    IsValidCertificate (rationalProgram P)
      (.unbounded (fun j => x (Fin.castAdd n j)) (fun j => x (Fin.natAdd n j))):=by
  have h:=ray_valid P (fun j => x (finSumFinEquiv j))
    (reindex_feasible (rayMatrix P) (rayBound P) (rayRows m) finSumFinEquiv x hx)
  simpa [finSumFinEquiv] using h

theorem some_family_feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H):
    IsFeasible (toReal (rationalProgram (optimal P)))∨
      IsFeasible (toReal (rationalProgram (infeasible P)))∨
        IsFeasible (toReal (rationalProgram (unbounded P))):=by
  obtain ⟨cert,hv⟩:=Lax109476Proofs.CertificateExistence.certificate_existence m n (rationalProgram P)
  cases cert with
  | optimal x y => exact Or.inl (reindex_exists _ _ _ _ (pair_feasible P x y hv))
  | infeasible y => exact Or.inr (Or.inl (reindex_exists _ _ _ _ (farkas_feasible P H hH hA hb y hv)))
  | unbounded x d => exact Or.inr (Or.inr (reindex_exists _ _ _ _ (ray_feasible P x d hv)))

end Lax109476Proofs.CertificateFamilyPrograms

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

theorem Spec.pre (h:Spec B P c Q K) (hP:∀ σ,P' σ→ P σ):Spec B P' c Q K:=
  h.conseq hP (fun _ _ _ hq => hq) le_rfl

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

inductive SeqSplit:Com→ Com→ Com→ Prop

  | one (a r:Com):SeqSplit a r (.seq a r)

  | cons (a p r w:Com) (h:SeqSplit p r w):SeqSplit (.seq a p) r (.seq a w)

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

theorem writeReducedFraction_spec (B:ℕ) (q:ℚ) (hB:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) writeReducedFraction
      (fun σ τ => τ.out=σ.out ++ encodeRational q) 10:=by
  intro σ hσ
  obtain ⟨hv,hσn,hσd,hσs⟩:=hσ
  have hnB:σ.vars "rat.n" < B:=hσn ▸ hn
  have hdB:σ.vars "rat.d" < B:=hσd ▸ hd
  have hsB:σ.vars "rat.s" < B:=hσs.trans_lt hB
  have hsign:=fractionValue_sign (σ.vars "rat.s") (σ.vars "rat.n")
    (σ.vars "rat.d") hσs (hσd ▸ q.den_pos)
  rw [hv] at hsign
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:List Nat→ List Nat→ List Nat:= @HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)); let c3:Env→ Prop:=(fun (σ_1 τ:Env) => @Eq (List Nat) (Env.out τ) (c2 (Env.out σ_1) (encodeRational q))) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B writeReducedFraction σ σ' ((10:Nat))) (c3 σ'); let c5:List Nat→ Env:=Env.mk (Env.vars σ) (Env.arrs σ) (Env.inp σ); let c6:List Nat→ List Nat:=c2 (Env.out σ); let c7:Env:=c5 (c6 (@List.cons Nat ((0:Nat)) (@List.nil Nat))); let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "rat.n"; let c10:Env:=Env.mk c8 (Env.arrs c7) (Env.inp c7) (c2 (Env.out c7) (@List.cons Nat c9 (@List.nil Nat))); let c11:String→ Nat:=Env.vars c10; let c12:Nat:=c11 "rat.d"; let c13:Env:=Env.mk c11 (Env.arrs c10) (Env.inp c10) (c2 (Env.out c10) (@List.cons Nat c12 (@List.nil Nat))); let c14:Nat→ Nat→ Nat:=Nat.add; let c15:Nat→ Nat:=c14 ((1:Nat)); let c16:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c17:Nat→ Nat:=c14 (c15 (Cond.size c16)); let c18:Nat:=c15 (Expr.size (Expr.lit ((0:Nat)))); let c19:Nat:=c17 c18; let c20:Nat:=c15 (Expr.size (Expr.var "rat.n")); let c21:Nat:=c15 (Expr.size (Expr.var "rat.d")); let c22:Nat:=c14 c20 c21; let c23:Com:=Com.write (Expr.lit ((0:Nat))); let c24:List Nat:=c6 (encodeRational q); let c25:Env:=c5 (c6 (@List.cons Nat (Env.vars σ "rat.s") (@List.nil Nat))); let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "rat.n"; let c28:Env:=Env.mk c26 (Env.arrs c25) (Env.inp c25) (c2 (Env.out c25) (@List.cons Nat c27 (@List.nil Nat))); let c29:String→ Nat:=Env.vars c28; let c30:Nat:=c29 "rat.d"; let c31:Env:=Env.mk c29 (Env.arrs c28) (Env.inp c28) (c2 (Env.out c28) (@List.cons Nat c30 (@List.nil Nat))); let c32:Nat:=c15 (Expr.size (Expr.var "rat.s")); let c33:Nat:=c17 c32; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c13 (@And.intro (Run B writeReducedFraction σ c13 ((10:Nat))) (c3 c13) (RunStep.mono B writeReducedFraction σ c13 (c14 c19 c22) ((10:Nat)) (RunStep.seq B (Com.ite c16 c23 (Com.write (Expr.var "rat.s"))) (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))) σ c7 c13 c19 c22 (RunStep.ite_true B c16 c23 (Com.write (Expr.var "rat.s")) σ c7 c18 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3947_0_0_0)) hcase) (RunStep.write B σ (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3947_0_0_1)))) (RunStep.seq B (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d")) c7 c10 c13 c20 c21 (RunStep.write B c7 (Expr.var "rat.n") c9 (RunStep.eval_var B c7 "rat.n" hnB)) (RunStep.write B c10 (Expr.var "rat.d") c12 (RunStep.eval_var B c10 "rat.d" hdB)))) (?nAX_g3947_0_0_2)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c31 (@And.intro (Run B writeReducedFraction σ c31 ((10:Nat))) (c3 c31) (RunStep.mono B writeReducedFraction σ c31 (c14 c33 c22) ((10:Nat)) (RunStep.seq B (Com.ite c16 c23 (Com.write (Expr.var "rat.s"))) (Com.seq (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d"))) σ c25 c31 c33 c22 (RunStep.ite_false B c16 c23 (Com.write (Expr.var "rat.s")) σ c25 c32 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" hnB) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g3947_0_0_3)) hcase) (RunStep.write B σ (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB))) (RunStep.seq B (Com.write (Expr.var "rat.n")) (Com.write (Expr.var "rat.d")) c25 c28 c31 c20 c21 (RunStep.write B c25 (Expr.var "rat.n") c27 (RunStep.eval_var B c25 "rat.n" hnB)) (RunStep.write B c28 (Expr.var "rat.d") c30 (RunStep.eval_var B c28 "rat.d" hdB)))) (?nAX_g3947_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3947_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3947_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3947_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3947_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3947_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [encodeRational,List.append_assoc]

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

end Lax109476Proofs.RamRationalArrays

end

section

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRounding RationalArithmeticBounds

theorem fractionValue_flip (s n d:ℕ) (hs:s≤ 1):
    fractionValue (1 - s) n d=-fractionValue s n d:=by
  interval_cases s <;> simp [fractionValue,neg_div]

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

end Lax109476Proofs.RamFrame

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

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem leftToResult_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (LeftOutput q) leftToResult (fun _ τ => FractionOutput q τ) 6:=by
  rintro σ ⟨hσs,hσn,hσd⟩
  have hs:σ.vars "left.s" < B:=hσs ▸ (rationalSign_le_one q).trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat:=Env.vars c1 "left.d"; let c3:Env:=Env.setVar c1 "rat.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "left.s")); let c7:Nat:=c5 (Expr.size (Expr.var "left.n")); let c8:Nat:=c5 (Expr.size (Expr.var "left.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B leftToResult σ σ' ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ σ')) c3 (@And.intro (Run B leftToResult σ c3 ((6:Nat))) ((fun (x τ:Env) => FractionOutput q τ) σ c3) (RunStep.mono B leftToResult σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hs)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4081_0_0_0))) (RunStep.assign B c1 "rat.d" (Expr.var "left.d") c2 (RunStep.eval_var B c1 "left.d" (?nAX_g4081_0_0_1))))) (?nAX_g4081_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4081_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4081_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,canonical_fractionValue,rationalSign_le_one]

end Lax109476Proofs.RamCopy

end

section

namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars

theorem load_spec (B:ℕ) (a:String) (xs:List ℚ) (i:ℕ) (hi:i < xs.length)
    (h1:1 < B) (hiB:i < B) (hn:xs[i].num.natAbs < B) (hd:xs[i].den < B):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "vec.i"=i) (load a)
      (fun _ τ => FractionOutput xs[i] τ) 15:=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=loadLeft_spec B a xs i hi h1 hiB hn hd σ hσ
  obtain ⟨υ,hr₂,hυ⟩:=RamCopy.leftToResult_spec B xs[i] h1 hn hd τ hτ
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

end Lax109476Proofs.RamArrayResult

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

end Lax109476Proofs.RamMatrixStorage

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamMatrixStorage

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

namespace Lax109476Proofs.RamCertificateSource

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def fields:List String:= ["source.m", "source.n"]
def arrays:List String:= ["source.A", "source.b", "source.c"]

theorem data_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (hσ:Data P σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):Data P τ:=by
  rcases hσ with ⟨hA,hb,hc,hm,hn⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hc hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn⟩

end Lax109476Proofs.RamCertificateSource

end

section

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax109476Proofs.RamPadSelector

end

section

namespace Lax109476Proofs.RamResultNegation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface

theorem negateResult_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (FractionOutput q) negateResult (fun _ τ => FractionOutput (-q) τ) 4:=by
  rintro σ ⟨hval,hn,hd,hs⟩
  have hsB:σ.vars "rat.s" < B:=hs.trans_lt h1
  have hflip:=fractionValue_flip (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d") hs
  rw [hval] at hflip
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negateResult σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negateResult σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negateResult σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" hsB) (?nAX_g4454_0_0_0))) (?nAX_g4454_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4454_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4454_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax109476Proofs.RamResultNegation

end

section

namespace Lax109476Proofs.RamCoordinateCap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNaturalPower RamFrame IntegerCertificates

def magnitude (m n H:ℕ):ℕ:=
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  m + n + H + K + K * H * H + a + K.factorial + a ^ K + coordinateCap m n H + 10

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

end Lax109476Proofs.RamCoordinateCapBounds

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

namespace Lax109476Proofs.RamStoredFeasibilityBounds

theorem wordWidth_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.wordWidth L≤ RamStoredFeasibility.wordWidth S:=by
  unfold RamStoredFeasibility.wordWidth RamRationalFeasibility.wordWidth
    RamPaddedFeasibility.wordWidth RamIntegerFeasibility.wordWidth RamFeasibilitySetup.wordWidth
    RamFeasibilityScaleBounds.wordWidth RamSearchBounds.wordWidth RamEllipsoidBitBounds.wordWidth
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamTrajectoryBounds.stateBits RamNormalizedBounds.coefficientBits
    RamIntegerFeasibility.iterationBound RamDecoder.wordWidth
  gcongr

set_option maxRecDepth 30000 in
theorem instructionBound_monotone {L S:ℕ} (h:L≤ S):
    RamStoredFeasibility.instructionBound L≤ RamStoredFeasibility.instructionBound S:=by
  unfold RamStoredFeasibility.instructionBound RamRationalFeasibility.instructionBound
    RamPaddedFeasibility.instructionBound RamIntegerFeasibility.uniformInstructionBound
    RamFeasibilitySetup.instructionBound RamFeasibilityParameters.instructionBound
    RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
    RamNormalizedBounds.coefficientBits RamIntegerFeasibility.iterationBound
  dsimp only
  gcongr

end Lax109476Proofs.RamStoredFeasibilityBounds

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

namespace Lax109476Proofs.RamCertificateMetadata

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamCertificateSource RamCertificateContext

theorem infeasible_spec (B m n:ℕ) (P:Program ℤ m n) (hB:m + n + 2 < B):
    Spec B (Data P) infeasible (fun _ τ => Context P (n + 1) m τ) 6:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hr:n + 1 < B:=by omega
  have hbase:Spec B (fun σ => σ.vars "source.m"=m∧ σ.vars "source.n"=n) infeasible
      (fun _ τ => τ.vars "system.m"=n + 1∧ τ.vars "system.n"=m) 6:=by
    rintro σ ⟨hσm,hσn⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 n ((1:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "system.m") c1) (@Eq Nat (Env.vars τ "system.n") m)) σ; let c3:Nat:=c0 (Env.vars σ "source.n") ((1:Nat)); let c4:Env:=Env.setVar σ "system.m" c3; let c5:Nat:=Env.vars c4 "source.m"; let c6:Env:=Env.setVar c4 "system.n" c5; let c7:Nat→ Nat:=c0 ((1:Nat)); let c8:Expr:=Expr.add (Expr.var "source.n") (Expr.lit ((1:Nat))); let c9:Nat:=c7 (Expr.size c8); let c10:Nat:=c7 (Expr.size (Expr.var "source.m")); let c11:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (Run B infeasible σ σ' ((6:Nat))) (c2 σ')) c6 (@And.intro (Run B infeasible σ c6 ((6:Nat))) (c2 c6) (RunStep.mono B infeasible σ c6 (c0 c9 c10) ((6:Nat)) (RunStep.seq B (Com.assign "system.m" c8) (Com.assign "system.n" (Expr.var "source.m")) σ c4 c6 c9 c10 (RunStep.assign B σ "system.m" c8 c3 (RunStep.eval_add B σ (Expr.var "source.n") (Expr.lit ((1:Nat))) (Env.vars σ "source.n") ((1:Nat)) (RunStep.eval_var B σ "source.n" (?nAX_g5020_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5020_0_0_1))) (RunStep.assign B c4 "system.n" (Expr.var "source.m") c5 (RunStep.eval_var B c4 "source.m" (?nAX_g5020_0_0_2)))) (?nAX_g5020_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5020_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5020_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5020_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5020_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ ⟨hσ.2.2.2.1,hσ.2.2.2.2⟩
  refine ⟨τ,hr,data_frame hr P hσ ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha t ht; change a ++ t∉ ([]:List String); simp

end Lax109476Proofs.RamCertificateMetadata

end

section

namespace Lax109476Proofs.RamCertificateLoad

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

def loadFields:List String:= ["source.m", "source.n", "query.row", "query.col", "query.a.row", "query.a.col", "certificate.kind"]

set_option maxHeartbeats 0 in
theorem matrix_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin m) (j:Fin n)
    (hM:1≤ M) (hMB:M < B) (hB:m * n + m + n + 4 < B) (hq:(P.A i j).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val∧ σ.vars "query.a.col"=j.val) matrix
      (fun _ τ => Data P τ∧ FractionOutput (P.A i j:ℚ) τ) 21:=by
  have h1:1 < B:=by omega
  have hi:i.val < B:=i.isLt.trans (by omega)
  have hj:j.val < B:=j.isLt.trans (by omega)
  have hn:n < B:=by omega
  let index:=i.val * n + j.val
  have hindex:index < (RamMatrixStorage.flatten (rationalProgram P).A).length:=by
    simpa [RamMatrixStorage.flatten,index] using RamMatrixStorage.row_index_lt i j
  have hindexB:index < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hindex:index < m * n).trans (by omega)
  have hmul:i.val * n < B:=by dsimp only [index] at hindexB; omega
  have he:(RamMatrixStorage.flatten (rationalProgram P).A)[index]=(P.A i j:ℚ):=
    RamMatrixStorage.flatten_entry (rationalProgram P).A i j
  have hqH:Height (P.A i j:ℚ) M:= ⟨by simpa using hq,by simpa using hM⟩
  have hload:=spec_with_fields loadFields
    (RamArrayResult.load_spec B "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) index hindex h1 hindexB
      (by rw [he]; exact hqH.1.trans_lt hMB) (by rw [he]; exact hqH.2.trans_lt hMB))
    (by intro a ha; simp [loadFields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val∧ σ.vars "query.a.col"=j.val) matrix
      (fun _ τ => FractionOutput (P.A i j:ℚ) τ) 21:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσi,hσj⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=Nat.mul (Env.vars σ "query.a.row") (Env.vars σ "source.n"); let c2:Nat:=c0 c1 (Env.vars σ "query.a.col"); let c3:Env:=Env.setVar σ "vec.i" c2; let c4:Env→ Nat→ Prop:=Run B (RamArrayResult.load "source.A") c3; let c5:List Rat:= @RamMatrixStorage.flatten m n (@Program.A Rat m n (@rationalProgram m n P)); let c6:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c5 index hindex); let c7:Env→ Prop:=FieldsAgree loadFields c3; let c8:String→ List Nat:=Env.arrs c3; let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((15:Nat))) (And (c6 σ') (And (c7 σ') (@Eq (String→ List Nat) (Env.arrs σ') c8))); let c10:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.A Int m n P i j)); let c11:Env→ Prop:=(fun (x τ:Env) => c10 τ) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B matrix σ σ' ((21:Nat))) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Env→ Prop:=Represents "source.A" c5; let c15:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c16:Nat:=c0 ((1:Nat)) (Expr.size c15); @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c13) (RunStep.use B (fun (σ_1:Env) => And (c14 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") index)) (RamArrayResult.load "source.A") (fun (σ_1 τ:Env) => And (c6 τ) (And (FieldsAgree loadFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((15:Nat)) hload c3 ?_) fun (w:Env) (h:And (c4 w ((15:Nat))) (And (c6 w) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) c8)))) => let c0_1:Prop:=c4 w ((15:Nat)); let c1_1:Prop:=And (c6 w) (And (c7 w) (@Eq (String→ List Nat) (Env.arrs w) c8)); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c12 w (@And.intro (Run B matrix σ w ((21:Nat))) (c11 w) (RunStep.mono B matrix σ w (c0 c16 ((15:Nat))) ((21:Nat)) (RunStep.seq B (Com.assign "vec.i" c15) (RamArrayResult.load "source.A") σ c3 w c16 ((15:Nat)) (RunStep.assign B σ "vec.i" c15 c2 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c1 (Env.vars σ "query.a.col") (RunStep.eval_mul B σ (Expr.var "query.a.row") (Expr.var "source.n") (Env.vars σ "query.a.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.a.row" (?nAX_g5024_0_0_0)) (RunStep.eval_var B σ "source.n" (?nAX_g5024_0_0_1)) ?_) (RunStep.eval_var B σ "query.a.col" (?nAX_g5024_0_0_2)) ?_)) left) (?nAX_g5024_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5024_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5024_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5024_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5024_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hload
    all_goals simp_all [loadFields,FieldsAgree,Represents,index]
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

theorem vector_wvars (a:String):(vector a).wvars=(vector "").wvars:=by rfl

theorem vector_spec (B m n r:ℕ) (P:Program ℤ m n) (a:String) (v:Fin r→ ℚ) (i:Fin r)
    (h1:1 < B) (hi:i.val < B) (hn:(v i).num.natAbs < B) (hd:(v i).den < B):
    Spec B (fun σ => Data P σ∧ Represents a (List.ofFn v) σ∧ σ.vars "query.a.row"=i.val) (vector a)
      (fun _ τ => Data P τ∧ FractionOutput (v i) τ) 17:=by
  have hload:=RamArrayResult.load_spec B a (List.ofFn v) i.val (by simpa using i.isLt) h1 hi
    (by simpa using hn) (by simpa using hd)
  have hbase:Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "query.a.row"=i.val) (vector a)
      (fun _ τ => FractionOutput (v i) τ) 17:=by
    rintro σ ⟨hσa,hσi⟩
    (expose_names;
      (refine let c0:Env→ Nat→ Prop:=Run B (RamArrayResult.load a) (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")); let c1:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) (@List.ofFn Rat r v) (@Fin.val r i) (?nAX_g5027_0_0_0)); let c2:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((15:Nat))) (c1 σ'); let c3:Env→ Prop:=(fun (x τ:Env) => FractionOutput (v i) τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (vector a) σ σ' ((17:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 ((1:Nat)) (Expr.size (Expr.var "query.a.row")); @Exists.casesOn Env c2 (fun (x:@Exists Env c2) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents a (@List.ofFn Rat r v) σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") (@Fin.val r i))) (RamArrayResult.load a) (fun (x τ:Env) => c1 τ) ((15:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) ?_) fun (w:Env) (h:And (c0 w ((15:Nat))) (c1 w)) => let c0_1:Prop:=c0 w ((15:Nat)); @And.casesOn c0_1 (c1 w) (fun (x:And c0_1 (c1 w)) => c5) h fun (left:c0_1) (right:c1 w) => @Exists.intro Env c4 w (@And.intro (Run B (vector a) σ w ((17:Nat))) (c3 w) (RunStep.mono B (vector a) σ w (c6 c7 ((15:Nat))) ((17:Nat)) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load a) σ (Env.setVar σ "vec.i" (Env.vars σ "query.a.row")) w c7 ((15:Nat)) (RunStep.assign B σ "vec.i" (Expr.var "query.a.row") (Env.vars σ "query.a.row") (RunStep.eval_var B σ "query.a.row" (?nAX_g5027_0_0_1))) left) (?nAX_g5027_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5027_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5027_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5027_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hload
    all_goals simp_all [Represents,arrs_setVar]
  rintro σ ⟨hσData,hσa,hσi⟩
  obtain ⟨τ,hr,hτ⟩:=hbase σ ⟨hσa,hσi⟩
  refine ⟨τ,hr,data_frame hr P hσData ?_ ?_,hτ⟩
  · intro f hf; rw [vector_wvars]; simp [RamCertificateSource.fields] at hf; rcases hf with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

theorem bound_spec (B m n:ℕ) (P:Program ℤ m n) (i:Fin m)
    (h1:1 < B) (hi:i.val < B) (hn:(P.b i).natAbs < B):
    Spec B (fun σ => Data P σ∧ σ.vars "query.a.row"=i.val) (vector "source.b")
      (fun _ τ => Data P τ∧ FractionOutput (P.b i:ℚ) τ) 17:=by
  exact (vector_spec B m n m P "source.b" (rationalProgram P).b i h1 hi
    (by simpa [rationalProgram] using hn) (by simpa [rationalProgram] using h1)).pre
      (fun _ h => ⟨h.1,h.1.2.1,h.2⟩)

end Lax109476Proofs.RamCertificateLoad

end

section

namespace Lax109476Proofs.CertificateFamilyEntries

open Lax109476.LinearProgram
open CertificateFamilyPrograms IntegerCertificates CertificateSystems CertificateSearch IndexedPointRecovery

def farkasEntry {m n:ℕ} (P:Program ℤ m n) (i:Fin (n + 1)) (j:Fin m):ℤ:=
  if hi:i.val < n then -P.A j ⟨i.val,hi⟩ else P.b j

def farkasRhs {n:ℕ} (i:Fin (n + 1)):ℤ:=if i.val < n then 0 else -1

def rayEntry {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))) (j:Fin (n + n)):ℤ:=
  if hi:i.val < m then
    if hj:j.val < n then P.A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else if hir:i.val < m + m then
    if hj:j.val < n then 0 else P.A ⟨i.val - m,by omega⟩ ⟨j.val - n,by omega⟩
  else if hj:j.val < n then 0 else -P.c ⟨j.val - n,by omega⟩

def rayRhs {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))):ℤ:=
  if hi:i.val < m then P.b ⟨i.val,hi⟩ else if i.val < m + m then 0 else -1

set_option maxHeartbeats 0 in
theorem pairEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (n + 2))) (j:Fin (n + m)):
    pairEntry P i j=(optimal P).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,i.isLt,j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,i.isLt,j.isLt]
      all_goals omega
    · fin_cases i
      all_goals refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,pairEntry,optimal,reindexProgram,pairRows,pairMatrix,
        finTwoEquiv,j.isLt,Nat.add_assoc]
      all_goals omega

theorem pairRhs_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (n + 2))):
    pairRhs P i=(optimal P).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [pairRhs,optimal,reindexProgram,pairRows,pairBound,i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat,pairRhs,optimal,reindexProgram,pairRows,pairBound,i.isLt]
    · fin_cases i
      all_goals simp [-Fin.natAdd_eq_addNat,pairRhs,optimal,reindexProgram,pairRows,pairBound,finTwoEquiv]
      all_goals omega

theorem farkasEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (n + 1)) (j:Fin m):
    farkasEntry P i j=(infeasible P).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [farkasEntry,infeasible,reindexProgram,farkasRows,farkasMatrix,i.isLt]
  · have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat,farkasEntry,infeasible,reindexProgram,farkasRows,farkasMatrix,unitFin]

theorem farkasRhs_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (n + 1)):
    farkasRhs i=(infeasible P).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [farkasRhs,infeasible,reindexProgram,farkasRows,farkasBound,i.isLt]
  · have hi:i=0:=Subsingleton.elim _ _
    subst i
    simp [-Fin.natAdd_eq_addNat,farkasRhs,infeasible,reindexProgram,farkasRows,farkasBound,unitFin]

theorem rayEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))) (j:Fin (n + n)):
    rayEntry P i j=(unbounded P).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,i.isLt,j.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,i.isLt,j.isLt]
      all_goals omega
    · have hi:i=0:=Subsingleton.elim _ _
      subst i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      all_goals simp [-Fin.natAdd_eq_addNat,rayEntry,unbounded,reindexProgram,rayRows,rayMatrix,unitFin,j.isLt,Nat.add_assoc]
      all_goals omega

theorem rayRhs_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + (m + 1))):
    rayRhs P i=(unbounded P).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [rayRhs,unbounded,reindexProgram,rayRows,rayBound,i.isLt]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp [-Fin.natAdd_eq_addNat,rayRhs,unbounded,reindexProgram,rayRows,rayBound,i.isLt]
    · have hi:i=0:=Subsingleton.elim _ _
      subst i
      simp [-Fin.natAdd_eq_addNat,rayRhs,unbounded,reindexProgram,rayRows,rayBound,unitFin]

end Lax109476Proofs.CertificateFamilyEntries

end

section

namespace Lax109476Proofs.RamFarkasSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCertificateSource IntegerEncoding

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (n + 1)) (j:Fin m)
    (hM:1≤ M) (hMB:M < B) (hB:m * n + 2 * m + 2 * n + 8 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M) (hb:∀ r, (P.b r).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.farkasEntry P i j:ℚ) τ) 40:=by
  have h1:1 < B:=by omega
  have hn:n < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => FractionOutput (CertificateFamilyEntries.farkasEntry P i j:ℚ) τ) 40:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσrow,hσcol⟩
    by_cases hi:i.val < n
    · let ii:Fin n:= ⟨i.val,hi⟩
      have hload:=RamCertificateLoad.matrix_spec B M m n P j ii hM hMB (by omega) (hA j ii)
      have hneg:=RamResultNegation.negateResult_spec B (P.A j ii:ℚ) h1
      (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.n"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.farkasEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:String→ Nat→ Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.col")); let c6:String→ Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.col")); let c7:Nat:=c6 "query.row"; let c8:Env:=c5 "query.a.col" c7; let c9:Env→ Nat→ Prop:=Run B RamCertificateLoad.matrix c8; let c10:Rat:= @Int.cast Rat Rat.instIntCast (@Program.A Int m n P j ii); let c11:Env→ Prop:=FractionOutput c10; let c12:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((21:Nat))) (And (@Data m n P σ') (c11 σ')); let c13:String→ Nat:=Env.vars c8; let c14:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg c10); let c15:Nat→ Nat→ Nat:=Nat.add; let c16:Nat→ Nat:=c15 ((1:Nat)); let c17:Nat→ Nat:=c15 (c16 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.n")))); let c18:Nat:=c16 (Expr.size (Expr.var "query.col")); let c19:Nat→ Nat:=c15 c18; let c20:Nat:=c16 (Expr.size (Expr.var "query.row")); let c21:Nat:=c15 ((21:Nat)) ((4:Nat)); let c22:Nat:=c15 c20 c21; let c23:Nat:=c19 c22; let c24:Com:=Com.seq (Com.assign "query.a.col" (Expr.var "query.row")) (Com.seq RamCertificateLoad.matrix RamResultNegation.negateResult); let c25:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.col")) c24; let c26:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.col")) (RamCertificateLoad.vector "source.b"); let c27:Nat:=c6 "query.a.row"; let c28:Env:=c5 "vec.i" c27; let c29:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.b"; let c30:String:=c29 ".s"; let c31:Nat:=Env.vars c28 "vec.i"; let c32:Nat:= @List.getD Nat (Env.arrs c28 c30) c31 ((0:Nat)); let c33:Env:=Env.setVar c28 "left.s" c32; let c34:String:=c29 ".n"; let c35:Nat:=Env.vars c33 "vec.i"; let c36:Nat:= @List.getD Nat (Env.arrs c33 c34) c35 ((0:Nat)); let c37:Env:=Env.setVar c33 "left.n" c36; let c38:String:=c29 ".d"; let c39:Nat:=Env.vars c37 "vec.i"; let c40:Nat:= @List.getD Nat (Env.arrs c37 c38) c39 ((0:Nat)); let c41:Env:=Env.setVar c37 "left.d" c40; let c42:Nat:=Env.vars c41 "left.s"; let c43:Env:=Env.setVar c41 "rat.s" c42; let c44:Nat:=Env.vars c43 "left.n"; let c45:Env:=Env.setVar c43 "rat.n" c44; let c46:Nat:=Env.vars c45 "left.d"; let c47:Env:=Env.setVar c45 "rat.d" c46; let c48:Nat:=c16 (Expr.size (Expr.var "query.a.row")); let c49:Expr:=Expr.get c30 (Expr.var "vec.i"); let c50:Nat:=c16 (Expr.size c49); let c51:Expr:=Expr.get c34 (Expr.var "vec.i"); let c52:Nat:=c16 (Expr.size c51); let c53:Expr:=Expr.get c38 (Expr.var "vec.i"); let c54:Nat:=c16 (Expr.size c53); let c55:Nat:=c15 c52 c54; let c56:Nat:=c15 c50 c55; let c57:Nat:=c16 (Expr.size (Expr.var "left.s")); let c58:Nat:=c16 (Expr.size (Expr.var "left.n")); let c59:Nat:=c16 (Expr.size (Expr.var "left.d")); let c60:Nat:=c15 c58 c59; let c61:Nat:=c15 c57 c60; let c62:Nat:=c15 c56 c61; let c63:Nat:=c15 c48 c62; let c64:Nat:=c19 c63; let c65:Com:=Com.assign "left.n" c51; let c66:Com:=Com.assign "left.d" c53; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c12 (fun (x:@Exists Env c12) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (And (@Eq Nat (Env.vars σ_1 "query.a.row") (@Fin.val m j)) (@Eq Nat (Env.vars σ_1 "query.a.col") (@Fin.val n ii)))) RamCertificateLoad.matrix (fun (x τ:Env) => And (@Data m n P τ) (c11 τ)) ((21:Nat)) hload c8 ?_) fun (w:Env) (h:And (c9 w ((21:Nat))) (And (@Data m n P w) (c11 w))) => let c0_1:Prop:=c9 w ((21:Nat)); let c1_1:Prop:=And (@Data m n P w) (c11 w); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult w σ' ((4:Nat))) (c14 σ'); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c4) (RunStep.use B c11 RamResultNegation.negateResult (fun (x τ:Env) => c14 τ) ((4:Nat)) hneg w ?_) fun (w_1:Env) (h_1:And (Run B RamResultNegation.negateResult w w_1 ((4:Nat))) (c14 w_1)) => let c0_2:Prop:=Run B RamResultNegation.negateResult w w_1 ((4:Nat)); @And.casesOn c0_2 (c14 w_1) (fun (x:And c0_2 (c14 w_1)) => @Exists Env c4) h_1 fun (left_1:c0_2) (right_1:c14 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectEntry σ w_1 ((40:Nat))) (c3 w_1) (RunStep.mono B selectEntry σ w_1 (c17 c23) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.n")) c25 c26 σ w_1 c23 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.row" (?nAX_g5050_0_0_0)) (RunStep.eval_var B σ "source.n" (?nAX_g5050_0_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.col")) c24 σ (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) w_1 c18 c22 (RunStep.assign B σ "query.a.row" (Expr.var "query.col") (Env.vars σ "query.col") (RunStep.eval_var B σ "query.col" (?nAX_g5050_0_0_2))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.row")) (Com.seq RamCertificateLoad.matrix RamResultNegation.negateResult) (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) c8 w_1 c20 c21 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.a.col" (Expr.var "query.row") c7 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.row" (?nAX_g5050_0_0_3))) (RunStep.seq B RamCertificateLoad.matrix RamResultNegation.negateResult c8 w w_1 ((21:Nat)) ((4:Nat)) left left_1)))) (?nAX_g5050_0_0_4)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c47 (@And.intro (Run B selectEntry σ c47 ((40:Nat))) (c3 c47) (RunStep.mono B selectEntry σ c47 (c17 c64) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.n")) c25 c26 σ c47 c64 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.row" (?nAX_g5050_0_0_5)) (RunStep.eval_var B σ "source.n" (?nAX_g5050_0_0_6)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.col")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) c47 c18 c63 (RunStep.assign B σ "query.a.row" (Expr.var "query.col") (Env.vars σ "query.col") (RunStep.eval_var B σ "query.col" (?nAX_g5050_0_0_7))) (RunStep.seq B (Com.assign "vec.i" (Expr.var "query.a.row")) (RamArrayResult.load "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) c28 c47 c48 c62 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "vec.i" (Expr.var "query.a.row") c27 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.a.row" (?nAX_g5050_0_0_8))) (RunStep.seq B (loadLeft "source.b") RamCopy.leftToResult c28 c41 c47 c56 c61 (RunStep.seq B (Com.assign "left.s" c49) (Com.seq c65 c66) c28 c33 c41 c50 c55 (RunStep.assign B c28 "left.s" c49 c32 (RunStep.eval_get B c28 c30 (Expr.var "vec.i") c31 (RunStep.eval_var B c28 "vec.i" (?nAX_g5050_0_0_9)) (?nAX_g5050_0_0_10) (?nAX_g5050_0_0_11))) (RunStep.seq B c65 c66 c33 c37 c41 c52 c54 (RunStep.assign B c33 "left.n" c51 c36 (RunStep.eval_get B c33 c34 (Expr.var "vec.i") c35 (RunStep.eval_var B c33 "vec.i" (?nAX_g5050_0_0_12)) (?nAX_g5050_0_0_13) (?nAX_g5050_0_0_14))) (RunStep.assign B c37 "left.d" c53 c40 (RunStep.eval_get B c37 c38 (Expr.var "vec.i") c39 (RunStep.eval_var B c37 "vec.i" (?nAX_g5050_0_0_15)) (?nAX_g5050_0_0_16) (?nAX_g5050_0_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c41 c43 c47 c57 c60 (RunStep.assign B c41 "rat.s" (Expr.var "left.s") c42 (RunStep.eval_var B c41 "left.s" (?nAX_g5050_0_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c43 c45 c47 c58 c59 (RunStep.assign B c43 "rat.n" (Expr.var "left.n") c44 (RunStep.eval_var B c43 "left.n" (?nAX_g5050_0_0_19))) (RunStep.assign B c45 "rat.d" (Expr.var "left.d") c46 (RunStep.eval_var B c45 "left.d" (?nAX_g5050_0_0_20))))))))) (?nAX_g5050_0_0_21)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5050_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
      all_goals clear hload hneg
      all_goals simp_all [CertificateFamilyEntries.farkasEntry,ii,Data,Represents,arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · have hload:=RamCertificateLoad.bound_spec B m n P j h1 hjB ((hb j).trans_lt hMB)
      (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.n"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.farkasEntry m n P i j)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:String→ Nat:=Env.vars (Env.setVar σ "query.a.row" (Env.vars σ "query.col")); let c6:Nat:=c5 "query.row"; let c7:Env:=Env.setVar (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.a.col" c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:String→ Nat:=Env.vars c7; let c10:Nat:=c9 "query.a.row"; let c11:Nat:=c9 "source.n"; let c12:Nat:=Nat.mul c10 c11; let c13:Nat:=c9 "query.a.col"; let c14:Nat:=c8 c12 c13; let c15:Env:=Env.setVar c7 "vec.i" c14; let c16:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "source.A"; let c17:String:=c16 ".s"; let c18:Nat:=Env.vars c15 "vec.i"; let c19:Nat:= @List.getD Nat (Env.arrs c15 c17) c18 ((0:Nat)); let c20:Env:=Env.setVar c15 "left.s" c19; let c21:String:=c16 ".n"; let c22:Nat:=Env.vars c20 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c20 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c20 "left.n" c23; let c25:String:=c16 ".d"; let c26:Nat:=Env.vars c24 "vec.i"; let c27:Nat:= @List.getD Nat (Env.arrs c24 c25) c26 ((0:Nat)); let c28:Env:=Env.setVar c24 "left.d" c27; let c29:Nat:=Env.vars c28 "left.s"; let c30:Env:=Env.setVar c28 "rat.s" c29; let c31:Nat:=Env.vars c30 "left.n"; let c32:Env:=Env.setVar c30 "rat.n" c31; let c33:Nat:=Env.vars c32 "left.d"; let c34:Env:=Env.setVar c32 "rat.d" c33; let c35:Nat:=Env.vars c34 "rat.s"; let c36:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c35; let c37:Env:=Env.setVar c34 "rat.s" c36; let c38:Nat→ Nat:=c8 ((1:Nat)); let c39:Nat→ Nat:=c8 (c38 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.n")))); let c40:Nat:=c38 (Expr.size (Expr.var "query.col")); let c41:Nat→ Nat:=c8 c40; let c42:Nat:=c38 (Expr.size (Expr.var "query.row")); let c43:Expr:=Expr.add (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col"); let c44:Nat:=c38 (Expr.size c43); let c45:Expr:=Expr.get c17 (Expr.var "vec.i"); let c46:Nat:=c38 (Expr.size c45); let c47:Expr:=Expr.get c21 (Expr.var "vec.i"); let c48:Nat:=c38 (Expr.size c47); let c49:Expr:=Expr.get c25 (Expr.var "vec.i"); let c50:Nat:=c38 (Expr.size c49); let c51:Nat:=c8 c48 c50; let c52:Nat:=c8 c46 c51; let c53:Nat:=c38 (Expr.size (Expr.var "left.s")); let c54:Nat:=c38 (Expr.size (Expr.var "left.n")); let c55:Nat:=c38 (Expr.size (Expr.var "left.d")); let c56:Nat:=c8 c54 c55; let c57:Nat:=c8 c53 c56; let c58:Nat:=c8 c52 c57; let c59:Nat:=c8 c44 c58; let c60:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); let c61:Nat:=c38 (Expr.size c60); let c62:Nat:=c8 c59 c61; let c63:Nat:=c8 c42 c62; let c64:Nat:=c41 c63; let c65:Com:=Com.seq (Com.assign "query.a.col" (Expr.var "query.row")) (Com.seq RamCertificateLoad.matrix RamResultNegation.negateResult); let c66:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.col")) c65; let c67:Com:=Com.seq (Com.assign "query.a.row" (Expr.var "query.col")) (RamCertificateLoad.vector "source.b"); let c68:Com:=Com.assign "left.n" c47; let c69:Com:=Com.assign "left.d" c49; let c70:Env→ Nat→ Prop:=Run B (RamCertificateLoad.vector "source.b") (Env.setVar σ "query.a.row" (Env.vars σ "query.col")); let c71:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@Program.b Int m n P j)); let c72:Env→ Prop:=fun (σ':Env) => And (c70 σ' ((17:Nat))) (And (@Data m n P σ') (c71 σ')); let c73:Nat:=c41 ((17:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c37 (@And.intro (Run B selectEntry σ c37 ((40:Nat))) (c3 c37) (RunStep.mono B selectEntry σ c37 (c39 c64) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.n")) c66 c67 σ c37 c64 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.row" (?nAX_g5050_1_0_0)) (RunStep.eval_var B σ "source.n" (?nAX_g5050_1_0_1)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.col")) c65 σ (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) c37 c40 c63 (RunStep.assign B σ "query.a.row" (Expr.var "query.col") (Env.vars σ "query.col") (RunStep.eval_var B σ "query.col" (?nAX_g5050_1_0_2))) (RunStep.seq B (Com.assign "query.a.col" (Expr.var "query.row")) (Com.seq RamCertificateLoad.matrix RamResultNegation.negateResult) (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) c7 c37 c42 c62 (RunStep.assign B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.a.col" (Expr.var "query.row") c6 (RunStep.eval_var B (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) "query.row" (?nAX_g5050_1_0_3))) (RunStep.seq B RamCertificateLoad.matrix RamResultNegation.negateResult c7 c34 c37 c59 c61 (RunStep.seq B (Com.assign "vec.i" c43) (RamArrayResult.load "source.A") c7 c15 c34 c44 c58 (RunStep.assign B c7 "vec.i" c43 c14 (RunStep.eval_add B c7 (Expr.mul (Expr.var "query.a.row") (Expr.var "source.n")) (Expr.var "query.a.col") c12 c13 (RunStep.eval_mul B c7 (Expr.var "query.a.row") (Expr.var "source.n") c10 c11 (RunStep.eval_var B c7 "query.a.row" (?nAX_g5050_1_0_4)) (RunStep.eval_var B c7 "source.n" (?nAX_g5050_1_0_5)) (?nAX_g5050_1_0_6)) (RunStep.eval_var B c7 "query.a.col" (?nAX_g5050_1_0_7)) (?nAX_g5050_1_0_8))) (RunStep.seq B (loadLeft "source.A") RamCopy.leftToResult c15 c28 c34 c52 c57 (RunStep.seq B (Com.assign "left.s" c45) (Com.seq c68 c69) c15 c20 c28 c46 c51 (RunStep.assign B c15 "left.s" c45 c19 (RunStep.eval_get B c15 c17 (Expr.var "vec.i") c18 (RunStep.eval_var B c15 "vec.i" (?nAX_g5050_1_0_9)) (?nAX_g5050_1_0_10) (?nAX_g5050_1_0_11))) (RunStep.seq B c68 c69 c20 c24 c28 c48 c50 (RunStep.assign B c20 "left.n" c47 c23 (RunStep.eval_get B c20 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c20 "vec.i" (?nAX_g5050_1_0_12)) (?nAX_g5050_1_0_13) (?nAX_g5050_1_0_14))) (RunStep.assign B c24 "left.d" c49 c27 (RunStep.eval_get B c24 c25 (Expr.var "vec.i") c26 (RunStep.eval_var B c24 "vec.i" (?nAX_g5050_1_0_15)) (?nAX_g5050_1_0_16) (?nAX_g5050_1_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c28 c30 c34 c53 c56 (RunStep.assign B c28 "rat.s" (Expr.var "left.s") c29 (RunStep.eval_var B c28 "left.s" (?nAX_g5050_1_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c30 c32 c34 c54 c55 (RunStep.assign B c30 "rat.n" (Expr.var "left.n") c31 (RunStep.eval_var B c30 "left.n" (?nAX_g5050_1_0_19))) (RunStep.assign B c32 "rat.d" (Expr.var "left.d") c33 (RunStep.eval_var B c32 "left.d" (?nAX_g5050_1_0_20))))))) (RunStep.assign B c34 "rat.s" c60 c36 (RunStep.eval_sub B c34 (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) c35 (RunStep.eval_lit B ((1:Nat)) c34 h1) (RunStep.eval_var B c34 "rat.s" (?nAX_g5050_1_0_21)) (?nAX_g5050_1_0_22))))))) (?nAX_g5050_1_0_23)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c72 (fun (x:@Exists Env c72) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (@Eq Nat (Env.vars σ_1 "query.a.row") (@Fin.val m j))) (RamCertificateLoad.vector "source.b") (fun (x τ:Env) => And (@Data m n P τ) (c71 τ)) ((17:Nat)) hload (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) ?_) fun (w:Env) (h:And (c70 w ((17:Nat))) (And (@Data m n P w) (c71 w))) => let c0_1:Prop:=c70 w ((17:Nat)); let c1_1:Prop:=And (@Data m n P w) (c71 w); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c39 c73) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.n")) c66 c67 σ w c73 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "query.row" (?nAX_g5050_1_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g5050_1_0_25)) hcase) (RunStep.seq B (Com.assign "query.a.row" (Expr.var "query.col")) (RamCertificateLoad.vector "source.b") σ (Env.setVar σ "query.a.row" (Env.vars σ "query.col")) w c40 ((17:Nat)) (RunStep.assign B σ "query.a.row" (Expr.var "query.col") (Env.vars σ "query.col") (RunStep.eval_var B σ "query.col" (?nAX_g5050_1_0_26))) left)) (?nAX_g5050_1_0_27)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5050_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5050_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals clear hload
      all_goals simp_all [CertificateFamilyEntries.farkasEntry,Data,Represents,arrs_setVar]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

theorem selectBound_spec (B m n:ℕ) (P:Program ℤ m n) (i:Fin (n + 1))
    (hB:n + 2 < B):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => Data P τ∧ FractionOutput (CertificateFamilyEntries.farkasRhs i:ℚ) τ) 16:=by
  have h1:1 < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hn:n < B:=by omega
  have hz:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have ho:=RamPadSelector.constantFraction_spec B 1 h1 h1
  have hneg:=RamResultNegation.negateResult_spec B 1 h1
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val) selectBound
      (fun _ τ => FractionOutput (CertificateFamilyEntries.farkasRhs i:ℚ) τ) 16:=by
    rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn⟩,hσrow⟩
    by_cases hi:i.val < n
    all_goals (expose_names;
                (refine
                    let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "source.n");
                    let c1:Prop:=Not c0;
                    let c2:Env→ Prop:=FractionOutput (@Int.cast Rat Rat.instIntCast (@CertificateFamilyEntries.farkasRhs n i));
                    let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ;
                    let c4:Env→ Prop:=fun (σ':Env) =>
                      And (Run B selectBound σ σ' ((16:Nat))) (c3 σ');
                    let c5:Prop:= @Exists Env c4;
                    let c6:Env→ Nat→ Prop:=
                      Run B (RamPadSelector.constantFraction ((0:Nat))) σ;
                    let c7:Env→ Prop:=
                      FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat)));
                    let c8:Env→ Prop:=fun (σ':Env) =>
                      And (c6 σ' ((6:Nat))) (c7 σ');
                    let c9:Nat→ Nat→ Nat:=Nat.add;
                    let c10:Nat→ Nat:=
                      c9
                        (c9 ((1:Nat))
                          (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "source.n"))));
                    let c11:Com:=
                      Com.seq (RamPadSelector.constantFraction ((1:Nat)))
                        RamResultNegation.negateResult;
                    let c12:Env→ Nat→ Prop:=
                      Run B (RamPadSelector.constantFraction ((1:Nat))) σ;
                    let c13:Env→ Prop:=
                      FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat)));
                    let c14:Env→ Prop:=fun (σ':Env) =>
                      And (c12 σ' ((6:Nat))) (c13 σ');
                    let c15:Env→ Prop:=
                      FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))));
                    let c16:Nat:=
                      c9 ((6:Nat))
                        ((4:Nat));
                    @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0)
                      (fun (hcase:c0) =>
                        @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c5)
                          (RunStep.use B (fun (x:Env) => True)
                            (RamPadSelector.constantFraction ((0:Nat)))
                            (fun (x τ:Env) => c7 τ) ((6:Nat)) hz σ ?_)
                          fun (w:Env) (h:And (c6 w ((6:Nat))) (c7 w)) =>
                          let c0_1:Prop:=c6 w ((6:Nat));
                          @And.casesOn c0_1 (c7 w) (fun (x:And c0_1 (c7 w)) => c5) h fun (left:c0_1) (right:c7 w) =>
                            @Exists.intro Env c4 w
                              (@And.intro (Run B selectBound σ w ((16:Nat))) (c3 w)
                                (RunStep.mono B selectBound σ w (c10 ((6:Nat)))
                                  ((16:Nat))
                                  (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "source.n"))
                                    (RamPadSelector.constantFraction ((0:Nat))) c11 σ
                                    w ((6:Nat))
                                    (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row")
                                      (Env.vars σ "source.n")
                                      (RunStep.eval_var B σ "query.row"
                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                      (RunStep.eval_var B σ "source.n"
                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                      hcase)
                                    left)
                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                ?_))
                      fun (hcase:c1) =>
                      @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => c5)
                        (RunStep.use B (fun (x:Env) => True)
                          (RamPadSelector.constantFraction ((1:Nat)))
                          (fun (x τ:Env) => c13 τ) ((6:Nat)) ho σ ?_)
                        fun (w:Env) (h:And (c12 w ((6:Nat))) (c13 w)) =>
                        let c0_1:Prop:=c12 w ((6:Nat));
                        let c1_1:Env→ Prop:=fun (σ':Env) =>
                          And (Run B RamResultNegation.negateResult w σ' ((4:Nat)))
                            (c15 σ');
                        @And.casesOn c0_1 (c13 w) (fun (x:And c0_1 (c13 w)) => c5) h fun (left:c0_1) (right:c13 w) =>
                          @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c5)
                            (RunStep.use B (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                              RamResultNegation.negateResult (fun (x τ:Env) => c15 τ)
                              ((4:Nat)) hneg w
                              ?_)
                            fun (w_1:Env)
                              (h_1:
                                And
                                  (Run B RamResultNegation.negateResult w w_1
                                    ((4:Nat)))
                                  (c15 w_1)) =>
                            let c0_2:Prop:=
                              Run B RamResultNegation.negateResult w w_1 ((4:Nat));
                            @And.casesOn c0_2 (c15 w_1) (fun (x:And c0_2 (c15 w_1)) => c5) h_1
                              fun (left_1:c0_2) (right_1:c15 w_1) =>
                              @Exists.intro Env c4 w_1
                                (@And.intro (Run B selectBound σ w_1 ((16:Nat)))
                                  (c3 w_1)
                                  (RunStep.mono B selectBound σ w_1 (c10 c16)
                                    ((16:Nat))
                                    (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "source.n"))
                                      (RamPadSelector.constantFraction ((0:Nat))) c11
                                      σ w_1 c16
                                      (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "source.n") (Env.vars σ "query.row")
                                        (Env.vars σ "source.n")
                                        (RunStep.eval_var B σ "query.row"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        (RunStep.eval_var B σ "source.n"
                                          ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                        hcase)
                                      (RunStep.seq B
                                        (RamPadSelector.constantFraction ((1:Nat)))
                                        RamResultNegation.negateResult σ w w_1
                                        ((6:Nat))
                                        ((4:Nat)) left left_1))
                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                  ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals clear hz ho hneg
    all_goals simp_all [CertificateFamilyEntries.farkasRhs]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamCertificateSource.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

end Lax109476Proofs.RamFarkasSelector

end

section

namespace Lax109476Proofs.CertificateFamilyHeight

open Lax109476.LinearProgram
open CertificateFamilyPrograms CertificateFamilyEntries

theorem optimal_A_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M)
    (hc:∀ j, (P.c j).natAbs≤ M):∀ i j, ((optimal P).A i j).natAbs≤ M:=by
  intro i j
  rw [← pairEntry_eq]
  unfold pairEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem optimal_b_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hb:∀ i, (P.b i).natAbs≤ M) (hc:∀ j, (P.c j).natAbs≤ M):
    ∀ i, ((optimal P).b i).natAbs≤ M:=by
  intro i
  rw [← pairRhs_eq]
  unfold pairRhs
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem infeasible_A_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M):
    ∀ i j, ((infeasible P).A i j).natAbs≤ M:=by
  intro i j
  rw [← farkasEntry_eq]
  unfold farkasEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem infeasible_b_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ) (hM:1≤ M):
    ∀ i, ((infeasible P).b i).natAbs≤ M:=by
  intro i
  rw [← farkasRhs_eq]
  unfold farkasRhs
  split_ifs <;> simp_all

theorem unbounded_A_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hc:∀ j, (P.c j).natAbs≤ M):
    ∀ i j, ((unbounded P).A i j).natAbs≤ M:=by
  intro i j
  rw [← rayEntry_eq]
  unfold rayEntry
  split_ifs <;> simp_all [Int.natAbs_neg]

theorem unbounded_b_bound {m n:ℕ} (P:Program ℤ m n) (M:ℕ) (hM:1≤ M)
    (hb:∀ i, (P.b i).natAbs≤ M):∀ i, ((unbounded P).b i).natAbs≤ M:=by
  intro i
  rw [← rayRhs_eq]
  unfold rayRhs
  split_ifs <;> simp_all

end Lax109476Proofs.CertificateFamilyHeight

end

section

namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource CertificateFamilyPrograms CertificateFamilyEntries

theorem withMetadata_spec (B m n r s metadataCost buildCost:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (metadata matrixSelector boundSelector:Com)
    (hmetadata:Spec B (Data P) metadata (fun _ τ => RamCertificateContext.Context P r s τ) metadataCost)
    (hbuild:Spec B (fun σ => RamCertificateContext.Context P r s σ∧ Extents "system.A" (r * s) σ∧ Extents "system.b" r σ)
      (RamCertificateBuilder.buildSystem matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) buildCost):
    Spec B (Input P r s) (withMetadata metadata matrixSelector boundSelector)
      (fun _ τ => Data P τ∧ RamEquationData.Data F τ) (metadataCost + buildCost):=by
  rintro σ ⟨hσData,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτContext⟩:=hmetadata σ hσData
  obtain ⟨υ,hr₂,hυ⟩:=hbuild τ ⟨hτContext,
    RamAdvanceState.extents_of_run hr₁ "system.A" (r * s) hσA,
    RamAdvanceState.extents_of_run hr₁ "system.b" r hσb⟩
  exact ⟨υ,hr₁.seq hr₂,hυ⟩

theorem infeasible_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hSource:m * n + 2 * m + 2 * n + 8 < B)
    (hSystem:(n + 1) * m + (n + 1) + m + 4 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (Input P (n + 1) m) infeasible
      (fun _ τ => Data P τ∧ RamEquationData.Data (CertificateFamilyPrograms.infeasible P) τ)
      (110 * ((n + 1) * m) + 74 * (n + 1) + 68):=by
  have hbuild:=RamCertificateBuilder.buildSystem_spec B M m n (n + 1) m 40 16 P
    (CertificateFamilyPrograms.infeasible P) RamFarkasSelector.selectEntry RamFarkasSelector.selectBound hM hMB hSystem
    (CertificateFamilyHeight.infeasible_A_bound P M hA hb) (CertificateFamilyHeight.infeasible_b_bound P M hM)
    (fun i j => by simpa only [farkasEntry_eq] using RamFarkasSelector.selectEntry_spec B M m n P i j hM hMB hSource hA hb)
    (fun i => by simpa only [farkasRhs_eq P i] using RamFarkasSelector.selectBound_spec B m n P i (by omega))
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by intro a ha; simp [RamCertificateContext.fields] at ha; rcases ha with rfl | rfl | rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by rfl) (by rfl)
  exact (withMetadata_spec B m n (n + 1) m 6 _ P (CertificateFamilyPrograms.infeasible P)
    RamCertificateMetadata.infeasible RamFarkasSelector.selectEntry RamFarkasSelector.selectBound
    (RamCertificateMetadata.infeasible_spec B m n P (by omega)) hbuild).mono (by omega)

end Lax109476Proofs.RamCertificateFamilies

end

section

namespace Lax109476Proofs.RamFamilyQueryCopy

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep RationalArithmeticBounds RamCopy

theorem copy_wvars (sourceA sourceB targetA targetB targetC:String):
    (copy sourceA sourceB targetA targetB targetC).wvars=(copy "" "" "" "" "").wvars:=by rfl

end Lax109476Proofs.RamFamilyQueryCopy

end

section

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem expression_size (f:String→ String) (e:Expr):
    (expression f e).size=e.size:=by
  induction e <;> simp_all [expression,Expr.size]

@[simp] theorem condition_size (f:String→ String) (b:Cond):
    (condition f b).size=b.size:=by
  cases b <;> simp [condition,Cond.size]

@[simp] theorem expression_eval (f:String→ String) (e:Expr) (B:ℕ) (σ:Env):
    (expression f e).evalB B σ=e.evalB B (view f σ):=by
  induction e <;> simp_all [expression,Expr.evalB,view]

@[simp] theorem condition_eval (f:String→ String) (b:Cond) (B:ℕ) (σ:Env):
    (condition f b).evalB B σ=b.evalB B (view f σ):=by
  cases b <;> simp [condition,Cond.evalB]

@[simp] theorem view_setVar (f:String→ String) (σ:Env) (x:String) (v:ℕ):
    view f (σ.setVar x v)=(view f σ).setVar x v:=rfl

@[simp] theorem view_setArr (f:String→ String) (hf:Function.Injective f)
    (σ:Env) (a:String) (k v:ℕ):
    view f (σ.setArr (f a) k v)=(view f σ).setArr a k v:=by
  cases σ
  simp only [view,Env.setArr]
  congr 1
  funext x
  by_cases hx:x=a
  · subst x; simp
  · have hfx:f x ≠ f a:=fun h => hx (hf h)
    simp [hx,hfx]

theorem run_relabel {B k:ℕ} {c:Com} {σ τ:Env} (f:String→ String)
    (hf:Function.Injective f) (h:BigStepB B c σ τ k):
    ∀ β,view f β=σ→ ∃ γ,BigStepB B (command f c) β γ k∧ view f γ=τ:=by
  induction h with
  | skip => intro β hβ; exact ⟨β, .skip,hβ⟩
  | @assign σ x e v he =>
    intro β hβ
    refine ⟨β.setVar x v, ?_,by simp [hβ]⟩
    simpa only [command,expression_size] using
      (BigStepB.assign (B:=B) (σ:=β) (x:=x) (e:=expression f e) (by simpa only [expression_eval,hβ] using he))
  | @store σ a i e k v hi he hk =>
    intro β hβ
    have hlen:k < (β.arrs (f a)).length:=by simpa only [← hβ,view] using hk
    refine ⟨β.setArr (f a) k v, ?_,by simp [hf,hβ]⟩
    simpa only [command,expression_size] using BigStepB.store (B:=B) (σ:=β) (a:=f a) (i:=expression f i) (e:=expression f e)
      (by simpa only [expression_eval,hβ] using hi)
      (by simpa only [expression_eval,hβ] using he) hlen
  | seq hc hd ihc ihd =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ihc β hβ
    obtain ⟨δ,hδ,heδ⟩:=ihd γ heγ
    exact ⟨δ,hγ.seq hδ,heδ⟩
  | @ite_true b c d σ σ' k hb hc ih =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ih β hβ
    exact ⟨γ,by simpa only [command,condition_size] using
      BigStepB.ite_true (B:=B) (σ:=β) (b:=condition f b) (d:=command f d) (by simpa only [condition_eval,hβ] using hb) hγ,heγ⟩
  | @ite_false b c d σ σ' k hb hd ih =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ih β hβ
    exact ⟨γ,by simpa only [command,condition_size] using
      BigStepB.ite_false (B:=B) (σ:=β) (b:=condition f b) (c:=command f c) (by simpa only [condition_eval,hβ] using hb) hγ,heγ⟩
  | @while_true b c σ σ' σ'' k k' hb hc hw ihc ihw =>
    intro β hβ
    obtain ⟨γ,hγ,heγ⟩:=ihc β hβ
    obtain ⟨δ,hδ,heδ⟩:=ihw γ heγ
    exact ⟨δ,by simpa only [command,condition_size] using
      BigStepB.while_true (B:=B) (σ:=β) (b:=condition f b) (by simpa only [condition_eval,hβ] using hb) hγ hδ,heδ⟩
  | @while_false b c σ hb =>
    intro β hβ
    exact ⟨β,by simpa only [command,condition_size] using
      BigStepB.while_false (B:=B) (σ:=β) (b:=condition f b) (c:=command f c) (by simpa only [condition_eval,hβ] using hb),hβ⟩
  | @read σ x v rest hi =>
    intro β hβ
    refine ⟨{β.setVar x v with inp:=rest}, ?_, ?_⟩
    · exact BigStepB.read (by simpa only [← hβ,view] using hi)
    · change {view f (β.setVar x v) with inp:=rest}=_
      simp only [view_setVar,hβ]
  | @write σ e v he =>
    intro β hβ
    refine ⟨{β with out:=β.out ++ [v]}, ?_, ?_⟩
    · simpa only [command,expression_size] using BigStepB.write (B:=B) (σ:=β) (e:=expression f e)
        (by simpa only [expression_eval,hβ] using he)
    · change {view f β with out:=(view f β).out ++ [v]}=_
      rw [hβ]

theorem spec_relabel {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (f:String→ String) (hf:Function.Injective f) (h:Spec B P c Q K):
    Spec B (fun σ => P (view f σ)) (command f c)
      (fun σ τ => Q (view f σ) (view f τ)) K:=by
  intro β hβ
  obtain ⟨τ, ⟨k,hk,hr⟩,hτ⟩:=h (view f β) hβ
  obtain ⟨γ,hγ,heγ⟩:=run_relabel f hf hr β rfl
  exact ⟨γ, ⟨k,hk,hγ⟩,by change Q (view f β) (view f γ); rw [heγ]; exact hτ⟩

end Lax109476Proofs.RamArrayRelabel

end

section

namespace Lax109476Proofs.RamCertificateArrayRelabel

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem relabel_injective (name:String) (hname:∀ a∈ sourceNames,a.length < name.length):
    Function.Injective (relabel name):=by
  intro a b hab
  by_cases ha:a∈ sourceNames <;> by_cases hb:b∈ sourceNames
  · simpa [relabel,ha,hb] using hab
  · have he:a=name ++ b:=by simpa [relabel,ha,hb] using hab
    have hl:=congrArg String.length he
    have hh:=hname a ha
    simp only [String.length_append] at hl
    omega
  · have he:name ++ a=b:=by simpa [relabel,ha,hb] using hab
    have hl:=congrArg String.length he
    have hh:=hname b hb
    simp only [String.length_append] at hl
    omega
  · exact (String.append_right_inj name).mp (by simpa [relabel,ha,hb] using hab)

theorem spec_isolated {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (name:String) (hname:∀ a∈ sourceNames,a.length < name.length) (h:Spec B P c Q K):
    Spec B (fun σ => P (RamArrayRelabel.view (relabel name) σ)) (isolated name c)
      (fun σ τ => Q (RamArrayRelabel.view (relabel name) σ) (RamArrayRelabel.view (relabel name) τ)) K:=
  RamArrayRelabel.spec_relabel _ (relabel_injective name hname) h

@[simp] theorem source_data_view {m n:ℕ} (P:Program ℤ m n) (name:String) (σ:Env):
    RamCertificateSource.Data P (RamArrayRelabel.view (relabel name) σ)↔ RamCertificateSource.Data P σ:=by
  simp [RamCertificateSource.Data,RamRationalArrays.Represents,RamArrayRelabel.view,relabel,sourceNames]

@[simp] theorem command_wvars (f:String→ String) (c:Com):
    (RamArrayRelabel.command f c).wvars=c.wvars:=by
  induction c <;> simp_all [RamArrayRelabel.command,Com.wvars]

theorem optimal_prefix:∀ a∈ sourceNames,a.length < "optimal.recovery.".length:=by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem infeasible_prefix:∀ a∈ sourceNames,a.length < "infeasible.recovery.".length:=by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem unbounded_prefix:∀ a∈ sourceNames,a.length < "unbounded.recovery.".length:=by
  intro a ha; simp [sourceNames] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Lax109476Proofs.RamCertificateArrayRelabel

end

section

namespace Lax109476Proofs.RamCertificateDecision

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem decide_wvars (source target:String):
    (decideFeasible source target).wvars=(decideFeasible "" "").wvars:=by
  simp [decideFeasible,prepare,RamFamilyQueryCopy.copy_wvars,RamArrayRelabel.prefixed,
    RamCertificateArrayRelabel.command_wvars,Com.wvars]

end Lax109476Proofs.RamCertificateDecision

end

section

namespace Lax109476Proofs.RamWriteVector

open Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds

def Invariant (a:String) (xs:List ℚ) (O:List ℕ) (N:ℕ) (σ:Env):Prop:=
  Represents a xs σ∧ σ.vars "output.i" ≤ N∧ σ.vars "output.count"=N∧
    σ.out=O ++ (xs.take (σ.vars "output.i")).flatMap encodeRational

theorem step_spec (B M N:ℕ) (a:String) (xs:List ℚ) (O:List ℕ)
    (h1:1 < B) (hMB:M < B) (hNB:N < B) (hN:N≤ xs.length)
    (hq:∀ q∈ xs,Height q M):
    Spec B (fun σ => Invariant a xs O N σ∧ σ.vars "output.i" < N) (step a)
      (fun σ τ => Invariant a xs O N τ∧ τ.vars "output.i"=σ.vars "output.i" + 1) 31:=by
  rintro σ ⟨⟨hσa,hσi,hσcount,hσout⟩,hi⟩
  let i:=σ.vars "output.i"
  have hil:i < xs.length:=hi.trans_le hN
  have hiB:i < B:=hi.trans hNB
  have hheight:=hq xs[i] (List.getElem_mem hil)
  have hr₁:Run B (.assign "vec.i" (.var "output.i")) σ (σ.setVar "vec.i" i) 2:=
    Run.assign (evalB_var hiB)
  obtain ⟨τ,hr₂,hτq⟩:=RamArrayResult.load_spec B a xs i hil h1 hiB
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) (σ.setVar "vec.i" i) ⟨hσa,by simp⟩
  obtain ⟨υ,hr₃,hυout⟩:=RamEncoding.writeReducedFraction_spec B xs[i] h1
    (hheight.1.trans_lt hMB) (hheight.2.trans_lt hMB) τ hτq
  have hυi:υ.vars "output.i"=i:=
    ((hr₁.seq (hr₂.seq hr₃)).frame_var _ (by
      change "output.i" ∉ (Com.seq (.assign "vec.i" (.var "output.i"))
        (.seq (RamArrayResult.load "") RamEncoding.writeReducedFraction)).wvars
      decide)).trans rfl
  have hsum:Bop.add.apply (υ.vars "output.i") 1 < B:=by simpa [hυi] using (show i + 1 < B by dsimp only [i]; omega)
  have hr₄:Run B increment υ (υ.setVar "output.i" (i + 1)) 4:=
    Run.assign (by simpa only [hυi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "output.i") (hυi ▸ hiB)) (evalB_lit h1) hsum))
  let ρ:=υ.setVar "output.i" (i + 1)
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hτout:τ.out=σ.out:=(hr₁.seq hr₂).out_eq (by
    change (Com.seq (.assign "vec.i" (.var "output.i")) (RamArrayResult.load "")).NoWrite
    decide)
  have hρout:ρ.out=O ++ (xs.take (i + 1)).flatMap encodeRational:=by
    change υ.out=_
    rw [hυout,hτout,hσout,List.take_succ_eq_append_getElem hil,List.flatMap_append]
    simp [i,List.append_assoc]
  refine ⟨ρ,hr, ⟨RamReadBody.represents_frame _ _ hσa hr (by intro s hs; change _∉ ([]:List String); simp),
    ?_, (hr.frame_var "output.count" (by change "output.count" ∉ (step "").wvars; decide)).trans hσcount, ?_⟩, ?_⟩
  · change i + 1≤ N; dsimp only [i]; omega
  · simpa only [ρ,vars_setVar,ite_true] using hρout
  · simp [ρ,i]

theorem writePrefix_spec (B M N:ℕ) (a:String) (xs:List ℚ)
    (h1:1 < B) (hMB:M < B) (hNB:N < B) (hN:N≤ xs.length)
    (hq:∀ q∈ xs,Height q M):
    Spec B (fun σ => Represents a xs σ∧ σ.vars "output.count"=N) (writePrefix a)
      (fun σ τ => τ.out=σ.out ++ (xs.take N).flatMap encodeRational) (35 * N + 6):=by
  rintro σ ⟨hσa,hσcount⟩
  have hlo:=Spec.forRangeZero "output.i" "output.count" (Invariant a xs σ.out N) N 31 hNB
    (fun _ h => h.2.1) (fun _ h => h.2.2.1) (step_spec B M N a xs σ.out h1 hMB hNB hN hq)
  obtain ⟨τ,hr,hτ,hcounter⟩:=hlo σ ⟨hσa,by simp,by simpa using hσcount,by simp⟩
  exact ⟨τ,hr,by simpa only [hcounter] using hτ.2.2.2⟩

theorem encodeVector_split {m n:ℕ} (z:Fin (m + n)→ ℚ):
    encodeVector z=encodeVector (fun i => z (Fin.castAdd n i)) ++ encodeVector (fun i => z (Fin.natAdd m i)):=by
  simp only [encodeVector,List.ofFn_add,List.flatMap_append]
  congr 2

end Lax109476Proofs.RamWriteVector

end

section

namespace Lax109476Proofs.RamWriteCertificate

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds

theorem prefix_encoding {r s:ℕ} (z:Fin (s + r)→ ℚ):
    ((List.ofFn z).take s).flatMap encodeRational=encodeVector (fun j => z (Fin.castAdd r j)):=by
  rw [List.ofFn_add]
  simp [encodeVector]
  congr 2

theorem emit_spec (B M r s tag:ℕ) (z:Fin (s + r)→ ℚ)
    (h1:1 < B) (hMB:M < B) (hsB:s < B) (htag:tag < B)
    (hz:∀ j,Height (z j) M):
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ∧ σ.vars "system.n"=s) (emit tag)
      (fun σ τ => τ.out=σ.out ++ [tag] ++ encodeVector (fun j => z (Fin.castAdd r j)))
      (35 * s + 10):=by
  have hwrite:=RamWriteVector.writePrefix_spec B M s "point.x" (List.ofFn z) h1 hMB hsB
    (by simp) (by intro q hq; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq; exact hz j)
  rintro σ ⟨hσx,hσn⟩
  (expose_names;
    (refine let c0:List Nat→ List Nat→ List Nat:= @HAppend.hAppend (List Nat) (List Nat) (List Nat) (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)); let c1:List Nat:=c0 (Env.out σ) (@List.cons Nat tag (@List.nil Nat)); let c2:Env:=Env.mk (Env.vars σ) (Env.arrs σ) (Env.inp σ) c1; let c3:Nat:=Env.vars c2 "system.n"; let c4:Env:=Env.setVar c2 "output.count" c3; let c5:Env→ Nat→ Prop:=Run B (RamWriteVector.writePrefix "point.x") c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (Nat.mul ((35:Nat)) s); let c8:Nat:=c7 ((6:Nat)); let c9:List Rat:= @List.ofFn Rat (c6 s r) z; let c10:List Nat:= @List.flatMap Rat Nat encodeRational (@List.take Rat s c9); let c11:List Nat:=c0 (Env.out c4) c10; let c12:Env→ Prop:=fun (σ':Env) => And (c5 σ' c8) (@Eq (List Nat) (Env.out σ') c11); let c13:Nat:=c7 ((10:Nat)); let c14:List Nat:= @encodeVector s fun (j:Fin s) => z (@Fin.castAdd s r j); let c15:Env→ Prop:=(fun (σ_1 τ:Env) => @Eq (List Nat) (Env.out τ) (c0 (c0 (Env.out σ_1) (@List.cons Nat tag (@List.nil Nat))) c14)) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B (emit tag) σ σ' c13) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Env→ Prop:=Represents "point.x" c9; let c19:Nat→ Nat:=c6 ((1:Nat)); let c20:Nat:=c19 (Expr.size (Expr.lit tag)); let c21:Nat:=c19 (Expr.size (Expr.var "system.n")); let c22:Nat:=c6 c21 c8; @Exists.casesOn Env c12 (fun (x:@Exists Env c12) => c17) (RunStep.use B (fun (σ_1:Env) => And (c18 σ_1) (@Eq Nat (Env.vars σ_1 "output.count") s)) (RamWriteVector.writePrefix "point.x") (fun (σ_1 τ:Env) => @Eq (List Nat) (Env.out τ) (c0 (Env.out σ_1) c10)) c8 hwrite c4 ?_) fun (w:Env) (h:And (c5 w c8) (@Eq (List Nat) (Env.out w) c11)) => @And.casesOn (c5 w c8) (@Eq (List Nat) (Env.out w) c11) (fun (x:And (c5 w c8) (@Eq (List Nat) (Env.out w) c11)) => c17) h fun (left:c5 w c8) (right:@Eq (List Nat) (Env.out w) c11) => @Exists.intro Env c16 w (@And.intro (Run B (emit tag) σ w c13) (c15 w) (RunStep.mono B (emit tag) σ w (c6 c20 c22) c13 (RunStep.seq B (Com.write (Expr.lit tag)) (Com.seq (Com.assign "output.count" (Expr.var "system.n")) (RamWriteVector.writePrefix "point.x")) σ c2 w c20 c22 (RunStep.write B σ (Expr.lit tag) tag (RunStep.eval_lit B tag σ htag)) (RunStep.seq B (Com.assign "output.count" (Expr.var "system.n")) (RamWriteVector.writePrefix "point.x") c2 c4 w c21 c8 (RunStep.assign B c2 "output.count" (Expr.var "system.n") c3 (RunStep.eval_var B c2 "system.n" (?nAX_g5173_0_0_0))) left)) (?nAX_g5173_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5173_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5173_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hwrite
  all_goals simp_all [Represents,arrs_setVar,prefix_encoding,List.append_assoc]

def optimalCertificate {m n r:ℕ} (z:Fin ((n + m) + r)→ ℚ):Certificate m n:=
  .optimal (fun j => z (Fin.castAdd r (Fin.castAdd m j))) (fun i => z (Fin.castAdd r (Fin.natAdd n i)))

def infeasibleCertificate {m n r:ℕ} (z:Fin (m + r)→ ℚ):Certificate m n:=
  .infeasible (fun i => z (Fin.castAdd r i))

def unboundedCertificate {m n r:ℕ} (z:Fin ((n + n) + r)→ ℚ):Certificate m n:=
  .unbounded (fun j => z (Fin.castAdd r (Fin.castAdd n j))) (fun j => z (Fin.castAdd r (Fin.natAdd n j)))

theorem optimal_spec (B M m n r:ℕ) (z:Fin ((n + m) + r)→ ℚ)
    (h1:1 < B) (hMB:M < B) (hsB:n + m < B) (hz:∀ j,Height (z j) M):
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ∧ σ.vars "system.n"=n + m) (emit 0)
      (fun σ τ => τ.out=σ.out ++ encodeCertificate (optimalCertificate z:Certificate m n))
      (35 * (n + m) + 10):=by
  apply (emit_spec B M r (n + m) 0 z h1 hMB hsB (by omega) hz).post
  intro σ τ hσ hτ
  simpa only [RamWriteVector.encodeVector_split,encodeCertificate,optimalCertificate,List.append_assoc] using hτ

theorem infeasible_spec (B M m n r:ℕ) (z:Fin (m + r)→ ℚ)
    (h1:1 < B) (hMB:M < B) (hsB:m < B) (hz:∀ j,Height (z j) M):
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ∧ σ.vars "system.n"=m) (emit 1)
      (fun σ τ => τ.out=σ.out ++ encodeCertificate (infeasibleCertificate z:Certificate m n))
      (35 * m + 10):=by
  apply (emit_spec B M r m 1 z h1 hMB hsB h1 hz).post
  intro σ τ hσ hτ
  simpa only [encodeCertificate,infeasibleCertificate,List.append_assoc] using hτ

theorem unbounded_spec (B M m n r:ℕ) (z:Fin ((n + n) + r)→ ℚ)
    (h2:2 < B) (hMB:M < B) (hsB:n + n < B) (hz:∀ j,Height (z j) M):
    Spec B (fun σ => Represents "point.x" (List.ofFn z) σ∧ σ.vars "system.n"=n + n) (emit 2)
      (fun σ τ => τ.out=σ.out ++ encodeCertificate (unboundedCertificate z:Certificate m n))
      (35 * (n + n) + 10):=by
  apply (emit_spec B M r (n + n) 2 z (by omega) hMB hsB h2 hz).post
  intro σ τ hσ hτ
  simpa only [RamWriteVector.encodeVector_split,encodeCertificate,unboundedCertificate,List.append_assoc] using hτ

theorem optimal_valid {m n:ℕ} (P:Program ℤ m n)
    (z:Fin ((n + m) + (m + (n + 2)))→ ℚ)
    (hz:PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.optimal P))
      (fun j => z (Fin.castAdd _ j))):
    IsValidCertificate (IntegerEncoding.rationalProgram P) (optimalCertificate z:Certificate m n):=
  CertificateFamilyPrograms.optimal_valid P _ hz

theorem infeasible_valid {m n:ℕ} (P:Program ℤ m n) (z:Fin (m + (n + 1))→ ℚ)
    (hz:PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.infeasible P))
      (fun j => z (Fin.castAdd _ j))):
    IsValidCertificate (IntegerEncoding.rationalProgram P) (infeasibleCertificate z:Certificate m n):=
  CertificateFamilyPrograms.infeasible_valid P _ hz

theorem unbounded_valid {m n:ℕ} (P:Program ℤ m n)
    (z:Fin ((n + n) + (m + (m + 1)))→ ℚ)
    (hz:PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.unbounded P))
      (fun j => z (Fin.castAdd _ j))):
    IsValidCertificate (IntegerEncoding.rationalProgram P) (unboundedCertificate z:Certificate m n):=
  CertificateFamilyPrograms.unbounded_valid P _ hz

end Lax109476Proofs.RamWriteCertificate

end

section

namespace Lax109476Proofs.RamRecoverCertificate

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

set_option maxRecDepth 30000 in
theorem recovery_no_write:RamRecoverFeasibleSystem.recover.NoWrite:=by decide

set_option maxRecDepth 30000 in
theorem recovery_preserves_dimension:"system.n" ∉ RamRecoverFeasibleSystem.recover.wvars:=by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_spec (m n r s S N w tag:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (makeCertificate:(Fin (s + r)→ ℚ)→ Certificate m n)
    (hdim:r + s≤ S) (hw:RamRecoverFeasibleSystem.wordWidth r s S≤ w)
    (hN:RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1≤ N)
    (hA:∀ i j, (F.A i j).natAbs≤ 2 ^ (2 * S)) (hb:∀ i, (F.b i).natAbs≤ 2 ^ (2 * S))
    (hf:∃ x,PrimalFeasible (rationalProgram F) x)
    (hvalid:∀ z,PrimalFeasible (rationalProgram F) (fun j => z (Fin.castAdd r j))→
      IsValidCertificate (rationalProgram P) (makeCertificate z))
    (hemit:∀ z, (∀ j,Height (z j) (IntegerCertificates.coordinateCap r s (2 ^ (2 * S))))→ Spec (2 ^ w)
      (fun σ => Represents "point.x" (List.ofFn z) σ∧ σ.vars "system.n"=s)
      (RamWriteCertificate.emit tag)
      (fun σ τ => τ.out=σ.out ++ encodeCertificate (makeCertificate z)) (35 * s + 10)):
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input F S N) (recover tag)
      (fun σ τ => ∃ certificate:Certificate m n,
        τ.out=σ.out ++ encodeCertificate certificate∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound r s S + 35 * s + 10):=by
  intro σ hσ
  obtain ⟨τ,hr₁,z,hτState,hz,hzHeight⟩:=RamRecoverFeasibleSystem.recover_spec r s S N w F
    hdim hw hN hA hb hf σ hσ
  have hτx:Represents "point.x" (List.ofFn z) τ:=hτState.1.2.2.1
  have hτn:τ.vars "system.n"=s:=(hr₁.frame_var _ recovery_preserves_dimension).trans hσ.1.2.2.2
  obtain ⟨υ,hr₂,hυout⟩:=hemit z hzHeight τ ⟨hτx,hτn⟩
  refine ⟨υ, (hr₁.seq hr₂).mono (by omega),makeCertificate z, ?_,hvalid z hz⟩
  simpa only [hr₁.out_eq recovery_no_write] using hυout

theorem emission_guards (r s S w:ℕ) (hdim:r + s≤ S)
    (hw:RamRecoverFeasibleSystem.wordWidth r s S≤ w):
    2 < 2 ^ w∧ s < 2 ^ w∧ IntegerCertificates.coordinateCap r s (2 ^ (2 * S)) < 2 ^ w:=by
  have hwCap:RamCoordinateCapBounds.wordWidth S≤ w:=by
    unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have hmag:=RamCoordinateCapBounds.magnitude_fits r s S w hdim hwCap
  have hs:s≤ w:=by unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have h2:2≤ w:=by unfold RamRecoverFeasibleSystem.wordWidth at hw; omega
  have hp:4≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) h2
  refine ⟨by omega,hs.trans_lt (Nat.lt_two_pow_self (n:=w)), ?_⟩
  have hle:IntegerCertificates.coordinateCap r s (2 ^ (2 * S))≤
      RamCoordinateCap.magnitude r s (2 ^ (2 * S)):=by
    dsimp only [RamCoordinateCap.magnitude]
    exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ 10)
  exact hle.trans_lt hmag

theorem optimal_spec (m n S N w:ℕ) (P:Program ℤ m n)
    (hdim:(m + (n + 2)) + (n + m)≤ S)
    (hw:RamRecoverFeasibleSystem.wordWidth (m + (n + 2)) (n + m) S≤ w)
    (hN:RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1≤ N)
    (hA:∀ i j, ((CertificateFamilyPrograms.optimal P).A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, ((CertificateFamilyPrograms.optimal P).b i).natAbs≤ 2 ^ (2 * S))
    (hf:∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.optimal P)) x):
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.optimal P) S N) (recover 0)
      (fun σ τ => ∃ certificate:Certificate m n,
        τ.out=σ.out ++ encodeCertificate certificate∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (m + (n + 2)) (n + m) S + 35 * (n + m) + 10):=by
  obtain ⟨h2,hs,hD⟩:=emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 0 P _ RamWriteCertificate.optimalCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.optimal_valid P) (fun z hz => RamWriteCertificate.optimal_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z (by omega) hD hs hz)

theorem infeasible_spec (m n S N w:ℕ) (P:Program ℤ m n)
    (hdim:(n + 1) + m≤ S)
    (hw:RamRecoverFeasibleSystem.wordWidth (n + 1) m S≤ w)
    (hN:RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1≤ N)
    (hA:∀ i j, ((CertificateFamilyPrograms.infeasible P).A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, ((CertificateFamilyPrograms.infeasible P).b i).natAbs≤ 2 ^ (2 * S))
    (hf:∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) x):
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.infeasible P) S N) (recover 1)
      (fun σ τ => ∃ certificate:Certificate m n,
        τ.out=σ.out ++ encodeCertificate certificate∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (n + 1) m S + 35 * m + 10):=by
  obtain ⟨h2,hs,hD⟩:=emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 1 P _ RamWriteCertificate.infeasibleCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.infeasible_valid P) (fun z hz => RamWriteCertificate.infeasible_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z (by omega) hD hs hz)

theorem unbounded_spec (m n S N w:ℕ) (P:Program ℤ m n)
    (hdim:(m + (m + 1)) + (n + n)≤ S)
    (hw:RamRecoverFeasibleSystem.wordWidth (m + (m + 1)) (n + n) S≤ w)
    (hN:RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits S) + 1≤ N)
    (hA:∀ i j, ((CertificateFamilyPrograms.unbounded P).A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, ((CertificateFamilyPrograms.unbounded P).b i).natAbs≤ 2 ^ (2 * S))
    (hf:∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x):
    Spec (2 ^ w) (RamRecoverFeasibleSystem.Input (CertificateFamilyPrograms.unbounded P) S N) (recover 2)
      (fun σ τ => ∃ certificate:Certificate m n,
        τ.out=σ.out ++ encodeCertificate certificate∧ IsValidCertificate (rationalProgram P) certificate)
      (RamRecoverFeasibleSystem.instructionBound (m + (m + 1)) (n + n) S + 35 * (n + n) + 10):=by
  obtain ⟨h2,hs,hD⟩:=emission_guards _ _ S w hdim hw
  exact recover_spec m n _ _ S N w 2 P _ RamWriteCertificate.unboundedCertificate hdim hw hN hA hb hf
    (RamWriteCertificate.unbounded_valid P) (fun z hz => RamWriteCertificate.unbounded_spec (2 ^ w)
      (IntegerCertificates.coordinateCap _ _ (2 ^ (2 * S))) m n _ z h2 hD hs hz)

end Lax109476Proofs.RamRecoverCertificate

end

section

namespace Lax109476Proofs.RamCertificateSetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RamEllipsoidStep IntegerEncoding RationalArithmeticBounds

theorem restore_spec (B m n:ℕ) (hm:m < B) (hn:n < B):
    Spec B (fun σ => σ.vars "certificate.m"=m∧ σ.vars "certificate.n"=n) restore
      (fun _ τ => τ.vars "source.m"=m∧ τ.vars "source.n"=n) 4:=by
  rintro σ ⟨hσm,hσn⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "source.m") m) (@Eq Nat (Env.vars τ "source.n") n)) σ; let c1:Nat:=Env.vars (Env.setVar σ "source.m" (Env.vars σ "certificate.m")) "certificate.n"; let c2:Env:=Env.setVar (Env.setVar σ "source.m" (Env.vars σ "certificate.m")) "source.n" c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 ((1:Nat)); let c5:Nat:=c4 (Expr.size (Expr.var "certificate.m")); let c6:Nat:=c4 (Expr.size (Expr.var "certificate.n")); let c7:String→ Nat:=Env.vars c2; @Exists.intro Env (fun (σ':Env) => And (Run B restore σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B restore σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B restore σ c2 (c3 c5 c6) ((4:Nat)) (RunStep.seq B (Com.assign "source.m" (Expr.var "certificate.m")) (Com.assign "source.n" (Expr.var "certificate.n")) σ (Env.setVar σ "source.m" (Env.vars σ "certificate.m")) c2 c5 c6 (RunStep.assign B σ "source.m" (Expr.var "certificate.m") (Env.vars σ "certificate.m") (RunStep.eval_var B σ "certificate.m" (?nAX_g5200_0_0_0))) (RunStep.assign B (Env.setVar σ "source.m" (Env.vars σ "certificate.m")) "source.n" (Expr.var "certificate.n") c1 (RunStep.eval_var B (Env.setVar σ "source.m" (Env.vars σ "certificate.m")) "certificate.n" (?nAX_g5200_0_0_1)))) (?nAX_g5200_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5200_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5200_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5200_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

end Lax109476Proofs.RamCertificateSetup

end

section

namespace Lax109476Proofs.RamExactSolverProgram

open Lax808846Proofs.Imp
open RamCertificateArrayRelabel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem saved_dimension_preserved:"certificate.m" ∉ chooseCertificate.wvars∧
    "certificate.n" ∉ chooseCertificate.wvars∧ "certificate.bits" ∉ chooseCertificate.wvars∧
    "certificate.parameter" ∉ chooseCertificate.wvars∧ "system.H" ∉ chooseCertificate.wvars:=by
  simp only [chooseCertificate,optimalSystem,infeasibleSystem,unboundedSystem,optimalDecision,
    infeasibleDecision,optimalRecovery,infeasibleRecovery,unboundedRecovery,
    afterOptimal,afterInfeasible,isolated,RamCertificateArrayRelabel.command_wvars,
    RamCertificateDecision.decide_wvars,Com.wvars]
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem optimal_stored_system_preserved:
    "optimal.recovery.system.A.s" ∉ optimalDecision.warrs∧
    "optimal.recovery.system.A.n" ∉ optimalDecision.warrs∧
    "optimal.recovery.system.A.d" ∉ optimalDecision.warrs∧
    "optimal.recovery.system.b.s" ∉ optimalDecision.warrs∧
    "optimal.recovery.system.b.n" ∉ optimalDecision.warrs∧
    "optimal.recovery.system.b.d" ∉ optimalDecision.warrs:=by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem infeasible_stored_system_preserved:
    "infeasible.recovery.system.A.s" ∉ infeasibleDecision.warrs∧
    "infeasible.recovery.system.A.n" ∉ infeasibleDecision.warrs∧
    "infeasible.recovery.system.A.d" ∉ infeasibleDecision.warrs∧
    "infeasible.recovery.system.b.s" ∉ infeasibleDecision.warrs∧
    "infeasible.recovery.system.b.n" ∉ infeasibleDecision.warrs∧
    "infeasible.recovery.system.b.d" ∉ infeasibleDecision.warrs:=by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem original_coefficients_preserved:
    "source.A.s" ∉ chooseCertificate.warrs∧ "source.A.n" ∉ chooseCertificate.warrs∧
    "source.A.d" ∉ chooseCertificate.warrs∧ "source.b.s" ∉ chooseCertificate.warrs∧
    "source.b.n" ∉ chooseCertificate.warrs∧ "source.b.d" ∉ chooseCertificate.warrs∧
    "source.c.s" ∉ chooseCertificate.warrs∧ "source.c.n" ∉ chooseCertificate.warrs∧
    "source.c.d" ∉ chooseCertificate.warrs:=by decide

end Lax109476Proofs.RamExactSolverProgram

end

section

namespace Lax109476Proofs.RamSolverWorkspace

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateArrayRelabel

theorem recovery_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (r s N:ℕ) (hσ:Recovery name r s N σ):Recovery name r s N τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  have hlen:=RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Recovery,recoveryView,RamArrayRelabel.view,Extents,
    RamRecoveryThreshold.Workspace,RamRecoveryQuery.Extent,RamFeasibilityQuery.Workspace,
    RamEllipsoidStep.Workspace,hlen] using hσ

theorem decision_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (r s:ℕ) (hσ:Decision name r s σ):Decision name r s τ:=by
  obtain ⟨_,_,hstep⟩:=hr.bigStep
  have hlen:=RamAdvanceState.array_length_of_bigStep hstep
  simpa only [Decision,RamCertificateDecision.prefixedView,RamArrayRelabel.view,Extents,
    RamFeasibilityQuery.Workspace,RamEllipsoidStep.Workspace,hlen] using hσ

theorem all_of_run {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (m n N:ℕ) (hσ:All m n N σ):All m n N τ:=
  ⟨recovery_of_run hr _ _ _ _ hσ.1,decision_of_run hr _ _ _ hσ.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.1,decision_of_run hr _ _ _ hσ.2.2.2.1,
    recovery_of_run hr _ _ _ _ hσ.2.2.2.2⟩

theorem recovery_input {r s S N:ℕ} (F:Program ℤ r s) (name:String) (σ:Env)
    (hData:RamEquationData.Data F (recoveryView name σ)) (hH:σ.vars "system.H"=2 ^ (2 * S))
    (hW:Recovery name r s N σ):RamRecoverFeasibleSystem.Input F S N (recoveryView name σ):=
  ⟨hData,hH,hW.2.2.1,hW.2.2.2.1,hW.2.2.2.2.1,hW.2.2.2.2.2.1,hW.2.2.2.2.2.2⟩

theorem decision_input {r s:ℕ} (F:Program ℤ r s) (source target:String) (σ:Env)
    (hData:RamEquationData.Data F (RamCertificateDecision.prefixedView source σ))
    (hW:Decision target r s σ):RamCertificateDecision.Input F source target σ:=by
  simpa only [RamCertificateDecision.Input,Decision,RamCertificateDecision.prefixedView,
    RamArrayRelabel.view,Extents,String.append_assoc] using And.intro hData hW

theorem equation_data_view {r s:ℕ} (F:Program ℤ r s) (name:String) (σ:Env):
    RamEquationData.Data F (recoveryView name σ)↔
      RamEquationData.Data F (RamCertificateDecision.prefixedView name σ):=by
  simp [RamEquationData.Data,recoveryView,RamCertificateDecision.prefixedView,
    RamArrayRelabel.view,RamRationalArrays.Represents,relabel,sourceNames]

end Lax109476Proofs.RamSolverWorkspace

end

section

namespace Lax109476Proofs.RamSolverOriginalContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

theorem context_of_run {B k m n L:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (P:Program ℤ m n) (hσ:Context P L σ)
    (hv:c.wvars ⊆ RamExactSolverProgram.chooseCertificate.wvars)
    (ha:c.warrs ⊆ RamExactSolverProgram.chooseCertificate.warrs):Context P L τ:=by
  have hs:=RamExactSolverProgram.saved_dimension_preserved
  have hc:=RamExactSolverProgram.original_coefficients_preserved
  have hfA:∀ t∈ RamCopy.suffixes, "source.A" ++ t∉ c.warrs:=by
    intro t ht hmem
    have hh:=ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.1 hh
    · exact hc.2.1 hh
    · exact hc.2.2.1 hh
  have hfb:∀ t∈ RamCopy.suffixes, "source.b" ++ t∉ c.warrs:=by
    intro t ht hmem
    have hh:=ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.2.2.2.1 hh
    · exact hc.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.1 hh
  have hfc:∀ t∈ RamCopy.suffixes, "source.c" ++ t∉ c.warrs:=by
    intro t ht hmem
    have hh:=ha hmem
    simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact hc.2.2.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.2.2.1 hh
    · exact hc.2.2.2.2.2.2.2.2 hh
  refine ⟨⟨RamReadBody.represents_frame _ _ hσ.1.1 hr hfA,
    RamReadBody.represents_frame _ _ hσ.1.2.1 hr hfb,
    RamReadBody.represents_frame _ _ hσ.1.2.2 hr hfc⟩, ?_, ?_⟩
  · exact ⟨(hr.frame_var _ (fun h => hs.1 (hv h))).trans hσ.2.1.1,
      (hr.frame_var _ (fun h => hs.2.1 (hv h))).trans hσ.2.1.2.1,
      (hr.frame_var _ (fun h => hs.2.2.1 (hv h))).trans hσ.2.1.2.2.1,
      (hr.frame_var _ (fun h => hs.2.2.2.1 (hv h))).trans hσ.2.1.2.2.2⟩
  · exact (hr.frame_var _ (fun h => hs.2.2.2.2 (hv h))).trans hσ.2.2

theorem restore_spec (B m n L:ℕ) (P:Program ℤ m n) (hm:m < B) (hn:n < B):
    Spec B (Context P L) RamCertificateSetup.restore
      (fun _ τ => RamCertificateSource.Data P τ∧ Context P L τ) 4:=by
  intro σ hσ
  obtain ⟨τ,hr,hm',hn'⟩:=RamCertificateSetup.restore_spec B m n hm hn σ
    ⟨hσ.2.1.1,hσ.2.1.2.1⟩
  have hτ:=context_of_run hr P hσ
    (by simp [RamCertificateSetup.restore,Com.wvars,RamExactSolverProgram.chooseCertificate,
      RamExactSolverProgram.afterOptimal,RamExactSolverProgram.afterInfeasible,Com.wvars])
    (by simp [RamCertificateSetup.restore,Com.warrs])
  exact ⟨τ,hr, ⟨hτ.1.1,hτ.1.2.1,hτ.1.2.2,hm',hn'⟩,hτ⟩

end Lax109476Proofs.RamSolverOriginalContext

end

section

namespace Lax109476Proofs.RamSolverBranchFrames

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamExactSolverProgram

def leaves:List Com:= [optimalSystem,infeasibleSystem,unboundedSystem,
  optimalDecision,infeasibleDecision,optimalRecovery,infeasibleRecovery,unboundedRecovery,
  RamCertificateSetup.restore]

theorem included (c:Com) (hc:c∈ leaves):
    (c.wvars ⊆ chooseCertificate.wvars)∧ (c.warrs ⊆ chooseCertificate.warrs):=by
  simp only [leaves,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor <;> intro a ha
  all_goals simp only [chooseCertificate,afterOptimal,afterInfeasible,Com.wvars,Com.warrs,
    List.mem_append] at *
  all_goals tauto

theorem context_of_leaf {B k m n L:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (hc:c∈ leaves) (P:Program ℤ m n) (hσ:RamSolverOriginalContext.Context P L σ):
    RamSolverOriginalContext.Context P L τ:=
  RamSolverOriginalContext.context_of_run hr P hσ (included c hc).1 (included c hc).2

theorem relabel_noWrite (f:String→ String) (c:Com):
    (RamArrayRelabel.command f c).NoWrite↔ c.NoWrite:=by
  induction c <;> simp_all [RamArrayRelabel.command,Com.NoWrite]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem build_noWrite:optimalSystem.NoWrite∧ infeasibleSystem.NoWrite∧ unboundedSystem.NoWrite:=by
  simp only [optimalSystem,infeasibleSystem,unboundedSystem,RamCertificateArrayRelabel.isolated,
    relabel_noWrite]
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem stored_decision_noWrite:RamStoredFeasibility.decideFeasible.NoWrite:=by decide

theorem decision_noWrite:optimalDecision.NoWrite∧ infeasibleDecision.NoWrite:=by
  simp only [optimalDecision,infeasibleDecision,RamCertificateDecision.decideFeasible,
    Com.NoWrite,RamArrayRelabel.prefixed,relabel_noWrite,stored_decision_noWrite,and_true]
  constructor
  all_goals unfold RamCertificateDecision.prepare
  all_goals decide

theorem restore_noWrite:RamCertificateSetup.restore.NoWrite:=by decide

end Lax109476Proofs.RamSolverBranchFrames

end

section

namespace Lax109476Proofs.RamSolverAlternative

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

theorem feasible_point {m n:ℕ} (P:Program ℤ m n)
    (h:RationalFeasibilityDecision.feasible (rationalProgram P)=true):
    ∃ x,PrimalFeasible (rationalProgram P) x:=
  RationalFeasibility.rational_feasibility m n _ ((RationalFeasibilityDecision.feasible_correct _).mp h)

theorem remaining_unbounded {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H)
    (ho:RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.optimal P))=false)
    (hi:RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.infeasible P))=false):
    ∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x:=by
  have hno:¬ IsFeasible (toReal (rationalProgram (CertificateFamilyPrograms.optimal P))):=by
    intro h
    have ht:=(RationalFeasibilityDecision.feasible_correct _).mpr h
    rw [ho] at ht
    cases ht
  have hni:¬ IsFeasible (toReal (rationalProgram (CertificateFamilyPrograms.infeasible P))):=by
    intro h
    have ht:=(RationalFeasibilityDecision.feasible_correct _).mpr h
    rw [hi] at ht
    cases ht
  rcases CertificateFamilyPrograms.some_family_feasible P H hH hA hb with h | h | h
  · exact False.elim (hno h)
  · exact False.elim (hni h)
  · exact RationalFeasibility.rational_feasibility _ _ _ h

end Lax109476Proofs.RamSolverAlternative

end

section

namespace Lax109476Proofs.RamSolverBranchComposition

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerEncoding RamExactSolverProgram

def BuildPost (State Data:Env→ Prop) (σ τ:Env):Prop:=State τ∧ Data τ∧ τ.out=σ.out
def DecisionPost (State Data:Env→ Prop) (B:ℕ) (f:Bool) (σ τ:Env):Prop:=
  State τ∧ Data τ∧ RamBisectionCommit.condition.evalB B τ=some f∧ τ.out=σ.out

theorem choose_spec (B m n H KO KI KU DO DI KR:ℕ) (P:Program ℤ m n)
    (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H)
    (State DataO DataI DataU:Env→ Prop)
    (hoBuild:Spec B (fun σ => RamCertificateSource.Data P σ∧ State σ) optimalSystem
      (BuildPost State DataO) KO)
    (hiBuild:Spec B (fun σ => RamCertificateSource.Data P σ∧ State σ) infeasibleSystem
      (BuildPost State DataI) KI)
    (huBuild:Spec B (fun σ => RamCertificateSource.Data P σ∧ State σ) unboundedSystem
      (BuildPost State DataU) KU)
    (hoDecide:Spec B (fun σ => State σ∧ DataO σ) optimalDecision
      (DecisionPost State DataO B (RationalFeasibilityDecision.feasible
        (rationalProgram (CertificateFamilyPrograms.optimal P)))) DO)
    (hiDecide:Spec B (fun σ => State σ∧ DataI σ) infeasibleDecision
      (DecisionPost State DataI B (RationalFeasibilityDecision.feasible
        (rationalProgram (CertificateFamilyPrograms.infeasible P)))) DI)
    (hrestore:Spec B State RamCertificateSetup.restore
      (fun σ τ => RamCertificateSource.Data P τ∧ State τ∧ τ.out=σ.out) 4)
    (hoRecover:(∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.optimal P)) x)→
      Spec B (fun σ => State σ∧ DataO σ) optimalRecovery (Result P) KR)
    (hiRecover:(∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) x)→
      Spec B (fun σ => State σ∧ DataI σ) infeasibleRecovery (Result P) KR)
    (huRecover:(∃ x,PrimalFeasible (rationalProgram (CertificateFamilyPrograms.unbounded P)) x)→
      Spec B (fun σ => State σ∧ DataU σ) unboundedRecovery (Result P) KR):
    Spec B (fun σ => RamCertificateSource.Data P σ∧ State σ) chooseCertificate (Result P)
      (KO + KI + KU + DO + DI + KR + 10 + 2 * RamBisectionCommit.condition.size):=by
  intro σ hσ
  obtain ⟨τ,hrO,hτState,hτData,hτout⟩:=hoBuild σ hσ
  obtain ⟨υ,hrDO,hυState,hυData,hυcond,hυout⟩:=hoDecide τ ⟨hτState,hτData⟩
  cases hfO:RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.optimal P)) with
  | true =>
    obtain ⟨ρ,hrR,cert,hρout,hvalid⟩:=hoRecover (RamSolverAlternative.feasible_point _ hfO) υ ⟨hυState,hυData⟩
    have hr:=hrO.seq (hrDO.seq (Run.ite_true (d:=.seq RamCertificateSetup.restore
      (.seq infeasibleSystem (.seq infeasibleDecision afterInfeasible))) (hfO ▸ hυcond) hrR))
    exact ⟨ρ,hr.mono (by omega),cert,by simpa only [hυout,hτout] using hρout,hvalid⟩
  | false =>
    obtain ⟨ρ,hrReset,hρSource,hρState,hρout⟩:=hrestore υ hυState
    obtain ⟨ξ,hrI,hξState,hξData,hξout⟩:=hiBuild ρ ⟨hρSource,hρState⟩
    obtain ⟨ζ,hrDI,hζState,hζData,hζcond,hζout⟩:=hiDecide ξ ⟨hξState,hξData⟩
    cases hfI:RationalFeasibilityDecision.feasible (rationalProgram (CertificateFamilyPrograms.infeasible P)) with
    | true =>
      obtain ⟨η,hrR,cert,hηout,hvalid⟩:=hiRecover (RamSolverAlternative.feasible_point _ hfI) ζ ⟨hζState,hζData⟩
      have hrAfterI:=Run.ite_true (d:=.seq RamCertificateSetup.restore (.seq unboundedSystem unboundedRecovery))
        (hfI ▸ hζcond) hrR
      have hrAfterO:=Run.ite_false (c:=optimalRecovery) (hfO ▸ hυcond)
        (hrReset.seq (hrI.seq (hrDI.seq hrAfterI)))
      have hr:=hrO.seq (hrDO.seq hrAfterO)
      exact ⟨η,hr.mono (by omega),cert,
        by simpa only [hζout,hξout,hρout,hυout,hτout] using hηout,hvalid⟩
    | false =>
      obtain ⟨η,hrResetI,hηSource,hηState,hηout⟩:=hrestore ζ hζState
      obtain ⟨θ,hrU,hθState,hθData,hθout⟩:=huBuild η ⟨hηSource,hηState⟩
      have hfU:=RamSolverAlternative.remaining_unbounded P H hH hA hb hfO hfI
      obtain ⟨ι,hrR,cert,hιout,hvalid⟩:=huRecover hfU θ ⟨hθState,hθData⟩
      have hrAfterI:=Run.ite_false (c:=infeasibleRecovery) (hfI ▸ hζcond) (hrResetI.seq (hrU.seq hrR))
      have hrAfterO:=Run.ite_false (c:=optimalRecovery) (hfO ▸ hυcond)
        (hrReset.seq (hrI.seq (hrDI.seq hrAfterI)))
      have hr:=hrO.seq (hrDO.seq hrAfterO)
      exact ⟨ι,hr.mono (by omega),cert,
        by simpa only [hθout,hηout,hζout,hξout,hρout,hυout,hτout] using hιout,hvalid⟩

end Lax109476Proofs.RamSolverBranchComposition

end

section

namespace Lax109476Proofs.RamSolverBranchSpecs

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCertificateArrayRelabel RamSolverWorkspace RamSolverOriginalContext

theorem state_of_leaf {B k m n L N:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (hc:c∈ RamSolverBranchFrames.leaves) (P:Program ℤ m n) (hσ:State P L N σ):State P L N τ:=
  ⟨RamSolverBranchFrames.context_of_leaf hr hc P hσ.1,all_of_run hr _ _ _ hσ.2⟩

theorem build_spec (B m n r s L N K:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (name:String) (c:Com) (hname:∀ a∈ sourceNames,a.length < name.length)
    (hleaf:isolated name c∈ RamSolverBranchFrames.leaves) (hNoWrite:(isolated name c).NoWrite)
    (hWork:∀ σ,All m n N σ→ Recovery name r s N σ)
    (hbuild:Spec B (RamCertificateFamilies.Input P r s) c
      (fun _ τ => RamCertificateSource.Data P τ∧ RamEquationData.Data F τ) K):
    Spec B (fun σ => RamCertificateSource.Data P σ∧ State P L N σ) (isolated name c)
      (RamSolverBranchComposition.BuildPost (State P L N) (fun σ => RamEquationData.Data F (recoveryView name σ))) K:=by
  rintro σ ⟨hσSource,hσState⟩
  have hσW:=hWork σ hσState.2
  have hσInput:RamCertificateFamilies.Input P r s (recoveryView name σ):=
    ⟨(source_data_view P name σ).mpr hσSource,hσW.1,hσW.2.1⟩
  obtain ⟨τ,hr,_,hτData⟩:=spec_isolated name hname hbuild σ hσInput
  exact ⟨τ,hr,state_of_leaf hr hleaf P hσState,hτData,hr.out_eq hNoWrite⟩

theorem decision_spec (B m n r s L N K:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (source target:String) (f:Bool)
    (hleaf:RamCertificateDecision.decideFeasible source target∈ RamSolverBranchFrames.leaves)
    (hNoWrite:(RamCertificateDecision.decideFeasible source target).NoWrite)
    (hWork:∀ σ,All m n N σ→ Decision target r s σ)
    (hdecision:Spec B (RamCertificateDecision.Input F source target)
      (RamCertificateDecision.decideFeasible source target)
      (fun _ τ => RamEquationData.Data F (RamCertificateDecision.prefixedView source τ)∧
        RamBisectionCommit.condition.evalB B τ=some f) K):
    Spec B (fun σ => State P L N σ∧ RamEquationData.Data F (recoveryView source σ))
      (RamCertificateDecision.decideFeasible source target)
      (RamSolverBranchComposition.DecisionPost (State P L N)
        (fun σ => RamEquationData.Data F (recoveryView source σ)) B f) K:=by
  rintro σ ⟨hσState,hσData⟩
  have hσInput:=decision_input F source target σ ((equation_data_view F source σ).mp hσData)
    (hWork σ hσState.2)
  obtain ⟨τ,hr,hτData,hτcond⟩:=hdecision σ hσInput
  exact ⟨τ,hr,state_of_leaf hr hleaf P hσState,
    (equation_data_view F source τ).mpr hτData,hτcond,hr.out_eq hNoWrite⟩

theorem recovery_spec (B m n r s L N K tag:ℕ) (P:Program ℤ m n) (F:Program ℤ r s)
    (name:String) (hname:∀ a∈ sourceNames,a.length < name.length)
    (hWork:∀ σ,All m n N σ→ Recovery name r s N σ)
    (hrecovery:Spec B (RamRecoverFeasibleSystem.Input F (RamCertificateSetup.parameter L) N)
      (RamRecoverCertificate.recover tag) (RamSolverBranchComposition.Result P) K):
    Spec B (fun σ => State P L N σ∧ RamEquationData.Data F (recoveryView name σ))
      (isolated name (RamRecoverCertificate.recover tag)) (RamSolverBranchComposition.Result P) K:=by
  rintro σ ⟨hσState,hσData⟩
  have hσInput:=recovery_input F name σ hσData hσState.1.2.2 (hWork σ hσState.2)
  obtain ⟨τ,hr,cert,hτout,hvalid⟩:=spec_isolated name hname hrecovery σ hσInput
  exact ⟨τ,hr,cert,hτout,hvalid⟩

theorem restore_spec (B m n L N:ℕ) (P:Program ℤ m n) (hm:m < B) (hn:n < B):
    Spec B (State P L N) RamCertificateSetup.restore
      (fun σ τ => RamCertificateSource.Data P τ∧ State P L N τ∧ τ.out=σ.out) 4:=by
  intro σ hσ
  obtain ⟨τ,hr,hτSource,hτContext⟩:=RamSolverOriginalContext.restore_spec B m n L P hm hn σ hσ.1
  exact ⟨τ,hr,hτSource, ⟨hτContext,all_of_run hr _ _ _ hσ.2⟩,
    hr.out_eq RamSolverBranchFrames.restore_noWrite⟩

end Lax109476Proofs.RamSolverBranchSpecs

end

section

namespace Lax109476Proofs.RamRecoveryResourceMonotonicity

attribute [gcongr] RamStoredFeasibilityBounds.wordWidth_monotone
attribute [gcongr] RamStoredFeasibilityBounds.instructionBound_monotone

@[gcongr] theorem reconstruction_width {S T:ℕ} (h:S≤ T):
    RamRationalReconstruction.wordWidth S≤ RamRationalReconstruction.wordWidth T:=by
  unfold RamRationalReconstruction.wordWidth RamRationalReconstruction.depthBound
    RamConvergentBounds.wordWidth RamConvergentBounds.exponent RamDecoder.wordWidth
  gcongr

@[gcongr] theorem reconstruction_cost {S T:ℕ} (h:S≤ T):
    RamRationalReconstruction.instructionBound S≤ RamRationalReconstruction.instructionBound T:=by
  unfold RamRationalReconstruction.instructionBound RamRationalReconstruction.depthBound
    RamConvergentBounds.instructionBound RamConvergentBounds.exponent
  gcongr

@[gcongr] theorem point_query_size {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.querySize m n S≤ RamPointRecoveryBounds.querySize r s T:=by
  unfold RamPointRecoveryBounds.querySize
  gcongr

@[gcongr] theorem point_query_cost {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.queryCost m n S≤ RamPointRecoveryBounds.queryCost r s T:=by
  unfold RamPointRecoveryBounds.queryCost
  gcongr

@[gcongr] theorem point_width {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamPointRecoveryBounds.wordWidth m n S≤ RamPointRecoveryBounds.wordWidth r s T:=by
  unfold RamPointRecoveryBounds.wordWidth RamDecoder.wordWidth
  gcongr

@[gcongr] theorem point_cost {m n S C r s T D:ℕ}
    (hm:m≤ r) (hn:n≤ s) (hS:S≤ T) (hC:C≤ D):
    RamPointRecoveryBounds.instructionBound m n S C≤ RamPointRecoveryBounds.instructionBound r s T D:=by
  unfold RamPointRecoveryBounds.instructionBound
  gcongr

@[gcongr] theorem cap_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.capBits S≤ RamRecoverFeasibleSystem.capBits T:=by
  unfold RamRecoverFeasibleSystem.capBits
  gcongr

@[gcongr] theorem recovery_bits {S T:ℕ} (h:S≤ T):
    RamRecoverFeasibleSystem.recoveryBits S≤ RamRecoverFeasibleSystem.recoveryBits T:=by
  unfold RamRecoverFeasibleSystem.recoveryBits
  gcongr

@[gcongr] theorem recovery_width {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamRecoverFeasibleSystem.wordWidth m n S≤ RamRecoverFeasibleSystem.wordWidth r s T:=by
  unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth
  gcongr

@[gcongr] theorem recovery_cost {m n S r s T:ℕ} (hm:m≤ r) (hn:n≤ s) (hS:S≤ T):
    RamRecoverFeasibleSystem.instructionBound m n S≤ RamRecoverFeasibleSystem.instructionBound r s T:=by
  unfold RamRecoverFeasibleSystem.instructionBound
  gcongr

end Lax109476Proofs.RamRecoveryResourceMonotonicity

end

section

namespace Lax109476Proofs.RamSolverBranchBounds

theorem guards (S w:ℕ) (hw:wordWidth S≤ w):
    2 ^ (2 * S) < 2 ^ w∧ S * S + 2 * S + 8 < 2 ^ w:=by
  have hh:RamRecoverFeasibleSystem.wordWidth S S S≤ w:=by unfold wordWidth at hw; omega
  have hguard:S * S + 2 * S + 8≤ w:=by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  have hexp:2 * S < w:=by
    unfold RamRecoverFeasibleSystem.wordWidth RamCoordinateCapBounds.wordWidth at hh
    nlinarith
  exact ⟨Nat.pow_lt_pow_right (by decide) hexp,hguard.trans_lt (Nat.lt_two_pow_self (n:=w))⟩

theorem product_guard {r s S w:ℕ} (hr:r≤ S) (hs:s≤ S) (hw:wordWidth S≤ w):
    r * s + r + s + 4 < 2 ^ w:=by
  have hprod:=Nat.mul_le_mul hr hs
  have hh:=(guards S w hw).2
  omega

theorem source_guard {m n S w:ℕ} (hm:m≤ S) (hn:n≤ S) (hDim:m + n≤ S)
    (hw:wordWidth S≤ w):m * n + 2 * m + 2 * n + 8 < 2 ^ w:=by
  have hprod:=Nat.mul_le_mul hm hn
  have hh:=(guards S w hw).2
  omega

theorem recovery_width {r s S w:ℕ} (hr:r≤ S) (hs:s≤ S) (hw:wordWidth S≤ w):
    RamRecoverFeasibleSystem.wordWidth r s S≤ w:=
  (RamRecoveryResourceMonotonicity.recovery_width hr hs le_rfl).trans (by unfold wordWidth at hw; omega)

theorem recovery_cost {r s S:ℕ} (hr:r≤ S) (hs:s≤ S):
    RamRecoverFeasibleSystem.instructionBound r s S + 35 * s + 10≤ recoveryCost S:=by
  have h:=RamRecoveryResourceMonotonicity.recovery_cost hr hs (show S≤ S from le_rfl)
  unfold recoveryCost
  omega

theorem decision_width {r s S w:ℕ} (hr:r≤ S) (hs:s≤ S) (hw:wordWidth S≤ w):
    RamStoredFeasibility.wordWidth (RamCertificateDecision.sizeBound r s S)≤ w:=by
  have hsize:RamCertificateDecision.sizeBound r s S≤ RamCertificateDecision.sizeBound S S S:=by
    unfold RamCertificateDecision.sizeBound
    gcongr
  exact (RamStoredFeasibilityBounds.wordWidth_monotone hsize).trans (by unfold wordWidth at hw; omega)

theorem decision_cost {r s S:ℕ} (hr:r≤ S) (hs:s≤ S):
    RamCertificateDecision.instructionBound r s S≤ decisionCost S:=by
  unfold decisionCost RamCertificateDecision.instructionBound
  have hsize:RamCertificateDecision.sizeBound r s S≤ RamCertificateDecision.sizeBound S S S:=by
    unfold RamCertificateDecision.sizeBound
    gcongr
  have hstored:=RamStoredFeasibilityBounds.instructionBound_monotone hsize
  have hp:=Nat.mul_le_mul hr hs
  omega

theorem build_cost {r s S:ℕ} (hr:r≤ S) (hs:s≤ S):
    142 * (r * s) + 98 * r + 74≤ buildCost S:=by
  have hp:=Nat.mul_le_mul hr hs
  unfold buildCost
  omega

end Lax109476Proofs.RamSolverBranchBounds

end

section

namespace Lax109476Proofs.RamSolverChooseCertificate

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamExactSolverProgram RamCertificateArrayRelabel RamSolverBranchSpecs RamSolverWorkspace

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem choose_spec (m n L N w:ℕ) (P:Program ℤ m n) (hdim:m + n≤ L)
    (hw:RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter L)≤ w)
    (hN:RamRationalReconstruction.depthBound
      (RamRecoverFeasibleSystem.recoveryBits (RamCertificateSetup.parameter L)) + 1≤ N)
    (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * RamCertificateSetup.parameter L))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * RamCertificateSetup.parameter L))
    (hc:∀ j, (P.c j).natAbs≤ 2 ^ (2 * RamCertificateSetup.parameter L)):
    Spec (2 ^ w) (fun σ => RamCertificateSource.Data P σ∧ State P L N σ)
      chooseCertificate (RamSolverBranchComposition.Result P)
      (RamSolverBranchBounds.instructionBound (RamCertificateSetup.parameter L)):=by
  let S:=RamCertificateSetup.parameter L
  let H:=2 ^ (2 * S)
  let KO:=RamSolverBranchBounds.buildCost S
  let KD:=RamSolverBranchBounds.decisionCost S
  let KR:=RamSolverBranchBounds.recoveryCost S
  have hS:2 * (m + n) + 2≤ S:=by dsimp only [S,RamCertificateSetup.parameter]; omega
  have hm:m≤ S:=by omega
  have hn:n≤ S:=by omega
  have hoR:m + (n + 2)≤ S:=by omega
  have hoC:n + m≤ S:=by omega
  have hiR:n + 1≤ S:=by omega
  have huR:m + (m + 1)≤ S:=by omega
  have huC:n + n≤ S:=by omega
  have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have hHB:H < 2 ^ w:=(RamSolverBranchBounds.guards S w hw).1
  have hSource:=RamSolverBranchBounds.source_guard hm hn (by omega) hw
  have hoGuard:=RamSolverBranchBounds.product_guard hoR hoC hw
  have hiGuard:=RamSolverBranchBounds.product_guard hiR hm hw
  have huGuard:=RamSolverBranchBounds.product_guard huR huC hw
  have hoA:=CertificateFamilyHeight.optimal_A_bound P H hA hb hc
  have hob:=CertificateFamilyHeight.optimal_b_bound P H hb hc
  have hiA:=CertificateFamilyHeight.infeasible_A_bound P H hA hb
  have hib:=CertificateFamilyHeight.infeasible_b_bound P H hH
  have huA:=CertificateFamilyHeight.unbounded_A_bound P H hA hc
  have hub:=CertificateFamilyHeight.unbounded_b_bound P H hH hb
  have hoBuildRaw:=(RamCertificateFamilies.optimal_spec (2 ^ w) H m n P hH hHB hSource hoGuard hA hb hc).mono (K':=KO)
    (by have hh:=RamSolverBranchBounds.build_cost hoR hoC; dsimp only [KO]; omega)
  have hiBuildRaw:=(RamCertificateFamilies.infeasible_spec (2 ^ w) H m n P hH hHB hSource hiGuard hA hb).mono (K':=KO)
    (by have hh:=RamSolverBranchBounds.build_cost hiR hm; dsimp only [KO]; omega)
  have huBuildRaw:=(RamCertificateFamilies.unbounded_spec (2 ^ w) H m n P hH hHB hSource huGuard hA hb hc).mono (K':=KO)
    (by have hh:=RamSolverBranchBounds.build_cost huR huC; dsimp only [KO]; omega)
  have hoBuild:=build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." RamCertificateFamilies.optimal optimal_prefix
    (by change optimalSystem∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.1 (fun _ h => h.1) hoBuildRaw
  have hiBuild:=build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." RamCertificateFamilies.infeasible infeasible_prefix
    (by change infeasibleSystem∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.2.1 (fun _ h => h.2.2.1) hiBuildRaw
  have huBuild:=build_spec (2 ^ w) m n _ _ L N KO P (CertificateFamilyPrograms.unbounded P)
    "unbounded.recovery." RamCertificateFamilies.unbounded unbounded_prefix
    (by change unboundedSystem∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.build_noWrite.2.2 (fun _ h => h.2.2.2.2) huBuildRaw
  have hoFrameA:∀ t∈ RamCopy.suffixes,
      "optimal.recovery." ++ ("system.A" ++ t)∉ optimalDecision.warrs:=by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact optimal_stored_system_preserved.1
    · exact optimal_stored_system_preserved.2.1
    · exact optimal_stored_system_preserved.2.2.1
  have hoFrameb:∀ t∈ RamCopy.suffixes,
      "optimal.recovery." ++ ("system.b" ++ t)∉ optimalDecision.warrs:=by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact optimal_stored_system_preserved.2.2.2.1
    · exact optimal_stored_system_preserved.2.2.2.2.1
    · exact optimal_stored_system_preserved.2.2.2.2.2
  have hiFrameA:∀ t∈ RamCopy.suffixes,
      "infeasible.recovery." ++ ("system.A" ++ t)∉ infeasibleDecision.warrs:=by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact infeasible_stored_system_preserved.1
    · exact infeasible_stored_system_preserved.2.1
    · exact infeasible_stored_system_preserved.2.2.1
  have hiFrameb:∀ t∈ RamCopy.suffixes,
      "infeasible.recovery." ++ ("system.b" ++ t)∉ infeasibleDecision.warrs:=by
    intro t ht; simp [RamCopy.suffixes] at ht
    rcases ht with rfl | rfl | rfl
    · exact infeasible_stored_system_preserved.2.2.2.1
    · exact infeasible_stored_system_preserved.2.2.2.2.1
    · exact infeasible_stored_system_preserved.2.2.2.2.2
  have hoDecideRaw:=(RamCertificateDecision.decideFeasible_spec _ _ S w (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." "optimal.decision." hHB hoGuard (RamSolverBranchBounds.decision_width hoR hoC hw)
    hoA hob (fun _ => rfl)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) hoFrameA hoFrameb).mono
    (RamSolverBranchBounds.decision_cost hoR hoC)
  have hiDecideRaw:=(RamCertificateDecision.decideFeasible_spec _ _ S w (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." "infeasible.decision." hHB hiGuard (RamSolverBranchBounds.decision_width hiR hm hw)
    hiA hib (fun _ => rfl)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) hiFrameA hiFrameb).mono
    (RamSolverBranchBounds.decision_cost hiR hm)
  have hoDecide:=decision_spec (2 ^ w) m n _ _ L N KD P (CertificateFamilyPrograms.optimal P)
    "optimal.recovery." "optimal.decision." _
    (by change optimalDecision∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.decision_noWrite.1 (fun _ h => h.2.1) hoDecideRaw
  have hiDecide:=decision_spec (2 ^ w) m n _ _ L N KD P (CertificateFamilyPrograms.infeasible P)
    "infeasible.recovery." "infeasible.decision." _
    (by change infeasibleDecision∈ RamSolverBranchFrames.leaves; simp [RamSolverBranchFrames.leaves])
    RamSolverBranchFrames.decision_noWrite.2 (fun _ h => h.2.2.2.1) hiDecideRaw
  have hoRecover:(∃ x,PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.optimal P)) x)→
      Spec (2 ^ w) (fun σ => State P L N σ∧ RamEquationData.Data (CertificateFamilyPrograms.optimal P)
        (recoveryView "optimal.recovery." σ)) optimalRecovery (RamSolverBranchComposition.Result P) KR:=by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 0 P _ "optimal.recovery." optimal_prefix (fun _ h => h.1)
      ((RamRecoverCertificate.optimal_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width hoR hoC hw) hN hoA hob hf).mono
          (RamSolverBranchBounds.recovery_cost hoR hoC))
  have hiRecover:(∃ x,PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.infeasible P)) x)→
      Spec (2 ^ w) (fun σ => State P L N σ∧ RamEquationData.Data (CertificateFamilyPrograms.infeasible P)
        (recoveryView "infeasible.recovery." σ)) infeasibleRecovery (RamSolverBranchComposition.Result P) KR:=by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 1 P _ "infeasible.recovery." infeasible_prefix (fun _ h => h.2.2.1)
      ((RamRecoverCertificate.infeasible_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width hiR hm hw) hN hiA hib hf).mono
          (RamSolverBranchBounds.recovery_cost hiR hm))
  have huRecover:(∃ x,PrimalFeasible (IntegerEncoding.rationalProgram (CertificateFamilyPrograms.unbounded P)) x)→
      Spec (2 ^ w) (fun σ => State P L N σ∧ RamEquationData.Data (CertificateFamilyPrograms.unbounded P)
        (recoveryView "unbounded.recovery." σ)) unboundedRecovery (RamSolverBranchComposition.Result P) KR:=by
    intro hf
    exact recovery_spec (2 ^ w) m n _ _ L N KR 2 P _ "unbounded.recovery." unbounded_prefix (fun _ h => h.2.2.2.2)
      ((RamRecoverCertificate.unbounded_spec m n S N w P (by omega)
        (RamSolverBranchBounds.recovery_width huR huC hw) hN huA hub hf).mono
          (RamSolverBranchBounds.recovery_cost huR huC))
  have hsmall:=(RamSolverBranchBounds.guards S w hw).2
  have hmB:m < 2 ^ w:=by nlinarith
  have hnB:n < 2 ^ w:=by nlinarith
  have hcombined:=RamSolverBranchComposition.choose_spec (2 ^ w) m n H KO KO KO KD KD KR P hH hA hb
    (State P L N) _ _ _ hoBuild hiBuild huBuild hoDecide hiDecide
    (restore_spec (2 ^ w) m n L N P hmB hnB) hoRecover hiRecover huRecover
  exact hcombined.mono (by
    dsimp only [RamSolverBranchBounds.instructionBound,KO,KD,KR,S]
    simp only [RamBisectionCommit.condition,Cond.size,Expr.size]
    omega)

end Lax109476Proofs.RamSolverChooseCertificate

end

theorem solution:∀ (m n L N w:ℕ) (P:Lax109476.LinearProgram.Program ℤ m n),
  m + n≤ L→
    Lax109476Proofs.RamSolverBranchBounds.wordWidth (Lax109476Proofs.RamCertificateSetup.parameter L)≤ w→
      Lax109476Proofs.RamRationalReconstruction.depthBound
              (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits
                (Lax109476Proofs.RamCertificateSetup.parameter L)) +
            1≤
          N→
        (∀ (i:Fin m) (j:Fin n), (P.A i j).natAbs≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L))→
          (∀ (i:Fin m), (P.b i).natAbs≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L))→
            (∀ (j:Fin n), (P.c j).natAbs≤ 2 ^ (2 * Lax109476Proofs.RamCertificateSetup.parameter L))→
              Lax808846Proofs.Reasoning.Spec (2 ^ w)
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamCertificateSource.Data P σ∧ Lax109476Proofs.RamSolverBranchSpecs.State P L N σ)
                Lax109476Proofs.RamExactSolverProgram.chooseCertificate
                (Lax109476Proofs.RamSolverBranchComposition.Result P)
                (Lax109476Proofs.RamSolverBranchBounds.instructionBound
                  (Lax109476Proofs.RamCertificateSetup.parameter L)):= @Lax109476Proofs.RamSolverChooseCertificate.choose_spec
