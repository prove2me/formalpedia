-- Prove2me | solution 1 for Lax455465Proofs.RamInputOptimal.exists_program_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:58.802525+00:00
-- url     : https://prove2.me/submissions/83b9498e-810a-4c5b-8978-680f84bf87c1

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamUniformSolver_exists_exact_polynomial_time_solver
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax455465Proofs_RamVirtualExecution_execute_spec_native

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

namespace Lax109476Proofs.RamArithmetic
end Lax109476Proofs.RamArithmetic
theorem Lax109476Proofs.RamArithmetic.normalizeFraction_spec:∀ (B n d:Nat),
  LT.lt n B→
    LT.lt d B→
      LT.lt ((0:Nat)) d→
        Lax808846Proofs.Reasoning.Spec B
          (fun (σ:Lax808846Proofs.Imp.Env) => And (@Eq Nat (σ.vars "rat.n") n) (@Eq Nat (σ.vars "rat.d") d))
          Lax109476Proofs.RamArithmetic.normalizeFraction
          (fun (x σ':Lax808846Proofs.Imp.Env) =>
            And (@Eq Nat (σ'.vars "rat.n") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) n (n.gcd d)))
              (@Eq Nat (σ'.vars "rat.d") (@HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) d (n.gcd d))))
          (HAdd.hAdd
            (HMul.hMul
              ((36:Nat)) d.size)
            ((16:Nat))):= @Lax109476Proofs.RamArithmetic.normalizeFraction_spec_native
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.multiplyFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    LE.le s₁ ((1:Nat))→
      LE.le s₂ ((1:Nat))→
        LE.le n₁ M→
          LE.le d₁ M→
            LE.le n₂ M→
              LE.le d₂ M→
                LT.lt ((0:Nat)) d₁→
                  LT.lt ((0:Nat)) d₂→
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
namespace Lax455465Proofs.RamVirtualExecution
end Lax455465Proofs.RamVirtualExecution
theorem Lax455465Proofs.RamVirtualExecution.execute_spec:∀ (B w k:Nat) (p:Lax808846.Ram.Program) (input:List Nat) (f:Lax455465Proofs.SparseRam.SparseState),
  LT.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            ((2:Nat))))
        ((3:Nat)))
      B→
    LT.lt
        (HAdd.hAdd k ((1:Nat)))
        B→
      LT.lt
          (HAdd.hAdd (@List.length Lax808846.Ram.Instr p)
            ((1:Nat)))
          B→
        (∀ (i:Lax808846.Ram.Instr),
            @Membership.mem Lax808846.Ram.Instr Lax808846.Ram.Program (@List.instMembership Lax808846.Ram.Instr) p i→
              Lax455465Proofs.RamVirtualInstruction.LiteralsFit
                (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) B
                  ((1:Nat)))
                i)→
          LT.lt (@List.length Nat input) B→
            (∀ (x:Nat),
                @Membership.mem Nat (List Nat) (@List.instMembership Nat) input x→ LT.lt x B)→
              @Eq (Option Lax455465Proofs.SparseRam.SparseState)
                  (Lax455465Proofs.SparseRam.run w p k (Lax455465Proofs.SparseRam.init input))
                  (@Option.some Lax455465Proofs.SparseRam.SparseState f)→
                @Eq (Option Lax455465Proofs.SparseRam.SparseState) (Lax455465Proofs.SparseRam.step w p f)
                    (@Option.none Lax455465Proofs.SparseRam.SparseState)→
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And (@Eq Nat (σ.vars "vm.width") w)
                        (And (Lax455465Proofs.RamVirtualState.Prefix input "vm.input" σ)
                          (And (@Eq Nat (σ.vars "vm.inputLength") (@List.length Nat input))
                            (And (LT.lt k (@List.length Nat (σ.arrs "vm.addresses")))
                              (And (LT.lt k (@List.length Nat (σ.arrs "vm.values")))
                                (LT.lt k (@List.length Nat (σ.arrs "vm.output"))))))))
                    (Lax455465Proofs.RamVirtualProgram.execute p)
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (Lax455465Proofs.RamVirtualState.Represents w f τ)
                        (@Eq Nat (τ.vars "vm.running") ((0:Nat))))
                    (HAdd.hAdd
                      (HMul.hMul
                        (HAdd.hAdd k
                          ((1:Nat)))
                        (HAdd.hAdd
                          (HAdd.hAdd
                            (HMul.hMul
                              ((4:Nat))
                              (@List.length Lax808846.Ram.Instr p))
                            (HMul.hMul
                              ((32:Nat)) k))
                          ((104:Nat))))
                      ((18:Nat))):= @Lax455465Proofs.RamVirtualExecution.execute_spec_native

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

@[simp] theorem evalB_get_iff {B:ℕ} {a:String} {i:Expr} {σ:Env} {v:ℕ}:
    (Expr.get a i).evalB B σ=some v↔
      ∃ k,i.evalB B σ=some k∧ (σ.arrs a)[k]?=some v∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨k,hk,u,hu,rfl,hlt⟩; exact ⟨k,hk,hu,hlt⟩
  · rintro ⟨k,hk,hu,hlt⟩; exact ⟨k,hk,v,hu,rfl,hlt⟩

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

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_nil:bitSize []=0:=rfl

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem bitSize_append (xs ys:List ℕ):bitSize (xs ++ ys)=bitSize xs + bitSize ys:=by
  simp [bitSize,encode]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

theorem size_half (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h ih =>
    have hne:Nat.bit b n ≠ 0:=by omega
    rw [Nat.bit_div_two,Nat.size_bit hne]

end Lax455465Proofs.WordSize

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

namespace Lax455465Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem normalizeFraction_spec (B n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d) (36 * d.size + 16)  :=by
  exact Lax109476Proofs.RamArithmetic.normalizeFraction_spec B n d hn hd hdpos

end Lax455465Proofs.RamArithmetic

end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

theorem fractionValue_reduce (s n d:ℕ):
    fractionValue s (n / Nat.gcd n d) (d / Nat.gcd n d)=fractionValue s n d:=by
  have h:((n / Nat.gcd n d:ℕ):ℚ) / ((d / Nat.gcd n d:ℕ):ℚ)=(n:ℚ) / d:=
    Nat.cast_div_div_div_cancel_right (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  unfold fractionValue
  split_ifs
  · simpa only [neg_div] using congrArg Neg.neg h
  · exact h

theorem normalizeFraction_signed_spec (B s n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d∧ σ'.vars "rat.s"=s) (36 * d.size + 16):=by
  rintro σ ⟨hσn,hσd,hσs⟩
  obtain ⟨τ,hr,hτn,hτd⟩:=normalizeFraction_spec B n d hn hd hdpos σ ⟨hσn,hσd⟩
  have hτs:=hr.frame_var "rat.s" (by decide)
  exact ⟨τ,hr,hτn,hτd,hτs.trans hσs⟩

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

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

theorem normalizeFraction_output_spec (B s n d:ℕ) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧ σ.vars "rat.s"=s)
      normalizeFraction (fun _ σ' => FractionOutput (fractionValue s n d) σ')
      (36 * d.size + 16):=by
  apply (normalizeFraction_signed_spec B s n d hn hd hdpos).post
  rintro σ τ _ ⟨hτn,hτd,hτs⟩
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hτs,hτn,hτd]; exact fractionValue_reduce s n d,
    hτn.trans hnum.symm,hτd.trans hden.symm,hτs ▸ hs⟩

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

theorem multiplyFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 64)  :=by
  exact Lax109476Proofs.RamRational.multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

end Lax455465Proofs.RamRational

end

section

namespace Lax455465Proofs.SparseRam

open Lax808846.Ram

theorem lookup_write (w:ℕ) (m:Memory) (a v:ℕ):
    lookup (write w m a v)=setCell w (lookup m) a v:=by
  funext b
  rfl

def expand (s:SparseState):State:= ⟨s.pc,lookup s.memory,s.input,s.inp,s.out⟩

theorem effect_expand (w:ℕ) (i:Instr) (s:SparseState):
    (effect w i s).map expand=i.effect w (expand s):=by
  cases i <;> simp only [effect,Instr.effect,assign,expand,lookup_write,Option.map_some,Option.map_none] <;> try rfl
  rename_i a
  cases s.inp.head? <;> simp only [Option.map_some,Option.map_none,expand,lookup_write]

theorem step_expand (w:ℕ) (p:Program) (s:SparseState):
    (step w p s).map expand=Lax808846.Ram.step w p (expand s):=by
  change (p[s.pc]?.bind fun i => effect w i s).map expand =
    p[s.pc]?.bind fun i => i.effect w (expand s)
  cases hi:p[s.pc]? with
  | none => rfl
  | some i => exact effect_expand w i s

theorem init_expand (x:List ℕ):expand (init x)=initState x:=rfl

theorem run_expand (w:ℕ) (p:Program) (t:ℕ) (s:SparseState):
    (run w p t s).map expand=Lax808846.Ram.run w p t (expand s):=by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [run,Lax808846.Ram.run]
    have he:=step_expand w p s
    cases hs:step w p s with
    | none =>
      have hn:Lax808846.Ram.step w p (expand s)=none:=by
        simpa only [hs,Option.map_none] using he.symm
      simp only [hn,Option.bind_none,Option.map_none]
    | some τ =>
      have hn:Lax808846.Ram.step w p (expand s)=some (expand τ):=by
        simpa only [hs,Option.map_some] using he.symm
      simp only [hn,Option.bind_some]
      exact ih τ

theorem effect_memory_le (w:ℕ) (i:Instr) (s τ:SparseState)
    (hs:effect w i s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs; simp [assign,write])
    | solve | (cases hi:s.inp.head? <;> (try simp only [hi,Option.map_some,Option.map_none] at hs) <;> cases hs <;> simp [assign,write])

theorem step_memory_le (w:ℕ) (p:Program) (s τ:SparseState)
    (hs:step w p s=some τ):τ.memory.length≤ s.memory.length + 1:=by
  unfold step at hs
  cases hi:p[s.pc]? with
  | none => simp only [hi,Option.bind_none] at hs; cases hs
  | some i =>
    simp only [hi,Option.bind_some] at hs
    exact effect_memory_le w i s τ hs

theorem run_memory_le (w:ℕ) (p:Program) (t:ℕ) (s τ:SparseState)
    (hs:run w p t s=some τ):τ.memory.length≤ s.memory.length + t:=by
  induction t generalizing s τ with
  | zero =>
    simp only [run,Option.some.injEq] at hs
    subst τ
    omega
  | succ t ih =>
    obtain ⟨ν,hstep,hrest⟩:=Option.bind_eq_some_iff.mp hs
    have hfirst:=step_memory_le w p s ν hstep
    have hlast:=ih ν τ hrest
    omega

theorem exists_execution (w:ℕ) (p:Program) (x y:List ℕ) (t:ℕ)
    (h:RunsTo w p x y t):
    ∃ k≤ t, ∃ s:SparseState,
      run w p k (init x)=some s∧ step w p s=none∧ s.out=y∧
      s.memory.length≤ k∧ t=k + terminalCost p (expand s):=by
  obtain ⟨k,τ,hrun,hhalt,hout,htime⟩:=h
  have hexpand:=run_expand w p k (init x)
  rw [init_expand,hrun] at hexpand
  cases hs:run w p k (init x) with
  | none => simp only [hs,Option.map_none] at hexpand; cases hexpand
  | some s =>
    have heq:expand s=τ:=by simpa only [hs,Option.map_some,Option.some.injEq] using hexpand
    have hstop:step w p s=none:=by
      have he:=step_expand w p s
      rw [heq,hhalt] at he
      exact Option.map_eq_none_iff.mp he
    have hm:=run_memory_le w p k (init x) s hs
    have htime':t=k + terminalCost p (expand s):=by rw [heq]; exact htime
    refine ⟨k,by omega,s,hs,hstop, ?_, ?_,htime'⟩
    · change (expand s).out=y
      rw [heq]
      exact hout
    · simpa only [init,List.length_nil,Nat.zero_add] using hm

theorem polynomial_execution (solve:List ℕ→ List ℕ)
    (hsolve:Lax759944.RamPolytime.RamPolytime solve):
    ∃ (p:Program) (wordBound timeBound:Polynomial ℕ), ∀ x:List ℕ,
      Lax759944.RamPolytime.FitsInWords (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x))
        ((x.length::x) ++ solve x)∧
      ∃ k≤ timeBound.eval (Lax759944.BinaryWordEncoding.bitSize x), ∃ s:SparseState,
        run (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p k (init (x.length::x))=some s∧
        step (wordBound.eval (Lax759944.BinaryWordEncoding.bitSize x)) p s=none∧
        s.out=solve x∧ s.memory.length≤ k:=by
  obtain ⟨p,wordBound,timeBound,hprogram⟩:=hsolve
  refine ⟨p,wordBound,timeBound, ?_⟩
  intro x
  obtain ⟨hfit,hwidth⟩:=hprogram x
  obtain ⟨t,ht,hrun⟩:=hwidth _ le_rfl
  obtain ⟨k,hkt,s,hs,hhalt,hout,hmemory,_⟩:=exists_execution _ p _ _ t hrun
  exact ⟨hfit,k,hkt.trans ht,s,hs,hhalt,hout,hmemory⟩

end Lax455465Proofs.SparseRam

end

section

namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

@[simp] theorem length_encode (qs:List ℚ≥0):(encode qs).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [encode] at ih
    simp [encode,encodeRational,ih]; omega

theorem numerator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i]?=some qs[i].num:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)=Nat.succ (Nat.succ (2*i)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem denominator_at (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (encode qs)[2*i+1]?=some qs[i].den:=by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp [encode,encodeRational]
    | succ i =>
      have hi':i < qs.length:=by simpa using hi
      simpa only [encode,List.flatMap_cons,encodeRational,List.cons_append,List.nil_append,
        show 2*(i+1)+1=Nat.succ (Nat.succ (2*i+1)) by omega,List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih i hi'

theorem read_spec (B:ℕ) (array index:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s"):
    Spec B (fun σ => Prefix (encode qs) array σ∧ σ.vars index=i) (read array index)
      (fun _ τ => FractionOutput (qs[i]:ℚ) τ∧ τ.vars "rat.s"=0) 14:=by
  have hnum:=numerator_at qs i hi
  have hden:=denominator_at qs i hi
  rintro σ ⟨hp,hv⟩
  have hni:2*i < (encode qs).length:=by simp only [length_encode]; omega
  have hdi:2*i+1 < (encode qs).length:=by simp only [length_encode]; omega
  have hnumval:(encode qs)[2*i]=qs[i].num:=by simpa only [List.getElem?_eq_getElem hni,Option.some.injEq] using hnum
  have hdenval:(encode qs)[2*i+1]=qs[i].den:=by simpa only [List.getElem?_eq_getElem hdi,Option.some.injEq] using hden
  have hgN:=(hp (2*i) hni).trans (congrArg some hnumval)
  have hgD:=(hp (2*i+1) hdi).trans (congrArg some hdenval)
  have hN:2*i < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgN; cases hgN
  have hD:2*i+1 < (σ.arrs array).length:=by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hgD; cases hgD
  have hni':i < B:=by omega
  have hmul:2*i < B:=by omega
  have hvalue:fractionValue 0 qs[i].num qs[i].den=(qs[i]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den qs[i])
  (expose_names;
    (refine let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (@getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i_1:Nat) => Nat.lt i_1 (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) qs i hi)); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (@Eq Nat (Env.vars τ "rat.s") ((0:Nat)))) σ; let c2:Nat→ Nat:=Nat.mul ((2:Nat)); let c3:Nat:=c2 (Env.vars σ index); let c4:Nat:= @List.getD Nat (Env.arrs σ array) c3 ((0:Nat)); let c5:Env:=Env.setVar σ "rat.n" c4; let c6:List Nat:=Env.arrs c5 array; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c5 index; let c9:Nat:=c2 c8; let c10:Nat:=c7 c9 ((1:Nat)); let c11:Nat:= @List.getD Nat c6 c10 ((0:Nat)); let c12:Env:=Env.setVar c5 "rat.d" c11; let c13:Env:=Env.setVar c12 "rat.s" ((0:Nat)); let c14:Nat→ Nat:=c7 ((1:Nat)); let c15:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var index); let c16:Expr:=Expr.get array c15; let c17:Nat:=c14 (Expr.size c16); let c18:Expr:=Expr.add c15 (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get array c18; let c20:Nat:=c14 (Expr.size c19); let c21:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c22:Nat:=c7 c20 c21; let c23:Com:=Com.assign "rat.d" c19; let c24:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c25:Nat→ Prop:=Nat.lt c10; @Exists.intro Env (fun (σ':Env) => And (Run B (read array index) σ σ' ((14:Nat))) (c1 σ')) c13 (@And.intro (Run B (read array index) σ c13 ((14:Nat))) (c1 c13) (RunStep.mono B (read array index) σ c13 (c7 c17 c22) ((14:Nat)) (RunStep.seq B (Com.assign "rat.n" c16) (Com.seq c23 c24) σ c5 c13 c17 c22 (RunStep.assign B σ "rat.n" c16 c4 (RunStep.eval_get B σ array c15 c3 (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) (Env.vars σ index) (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_var B σ index (?nAX_g5778_0_0_0)) (?nAX_g5778_0_0_1)) (?nAX_g5778_0_0_2) ?_)) (RunStep.seq B c23 c24 c5 c12 c13 c20 c21 (RunStep.assign B c5 "rat.d" c19 c11 (RunStep.eval_get B c5 array c18 c10 (RunStep.eval_add B c5 c15 (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_mul B c5 (Expr.lit ((2:Nat))) (Expr.var index) ((2:Nat)) c8 (RunStep.eval_lit B ((2:Nat)) c5 h2) (RunStep.eval_var B c5 index ?_) ?_) (RunStep.eval_lit B ((1:Nat)) c5 (?nAX_g5778_0_0_3)) ?_) ?_ ?_)) (RunStep.assign B c12 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c12 (?nAX_g5778_0_0_4))))) (?nAX_g5778_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5778_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5778_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

end Lax455465Proofs.RamUnsignedBuffer

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

theorem keep_scalar {B K:ℕ} {P:Env→ Prop} {Q:Env→ Env→ Prop} {c:Com}
    (h:Spec B P c Q K) (x:String) (v:ℕ) (hx:x∉ c.wvars):
    Spec B (fun σ => P σ∧ σ.vars x=v) c (fun σ τ => Q σ τ∧ τ.vars x=v) K:=by
  rintro σ ⟨hp,hv⟩
  obtain ⟨τ,hr,hq⟩:=h σ hp
  exact ⟨τ,hr,hq, (hr.frame_var x hx).trans hv⟩

end Lax455465Proofs.RamFrames

end

section

namespace Lax455465Proofs.RamWeightProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def copyLeft:Com:=.seq (.assign "left.s" (.var "rat.s"))
  (.seq (.assign "left.n" (.var "rat.n")) (.assign "left.d" (.var "rat.d")))
def copyRight:Com:=.seq (.assign "right.s" (.var "rat.s"))
  (.seq (.assign "right.n" (.var "rat.n")) (.assign "right.d" (.var "rat.d")))

def command:Com:=.seq (RamUnsignedBuffer.read "flow.weights" "lp.s")
  (.seq copyLeft (.seq (RamUnsignedBuffer.read "flow.weights" "lp.t")
    (.seq copyRight multiplyFraction)))

theorem command_spec (B M:ℕ) (weights:List ℚ≥0) (s t:ℕ)
    (hs:s < weights.length) (ht:t < weights.length)
    (hB:2*M^2+3 < B) (hsi:2*s+1 < B) (hti:2*t+1 < B)
    (hsn:weights[s].num≤ M) (hsd:weights[s].den≤ M)
    (htn:weights[t].num≤ M) (htd:weights[t].den≤ M):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ∧
      σ.vars "lp.s"=s∧ σ.vars "lp.t"=t) command
      (fun _ τ => FractionOutput ((weights[s]:ℚ) * (weights[t]:ℚ)) τ)
      (36*(weights[s].den*weights[t].den).size+104):=by
  have hM:M < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  have hreadS:=RamUnsignedBuffer.read_spec B "flow.weights" "lp.s" weights s hs h2 hsi
    (hsn.trans_lt hM) (hsd.trans_lt hM) (by decide)
  have hreadT:=RamUnsignedBuffer.read_spec B "flow.weights" "lp.t" weights t ht h2 hti
    (htn.trans_lt hM) (htd.trans_lt hM) (by decide)
  have hleft:Spec B (fun σ => FractionOutput (weights[s]:ℚ) σ∧ σ.vars "rat.s"=0)
      copyLeft (fun _ τ => τ.vars "left.s"=0∧ τ.vars "left.n"=weights[s].num∧
        τ.vars "left.d"=weights[s].den) 6:=by
    rintro σ ⟨⟨hv,hn,hd,hsg⟩,hzero⟩
    have hns:σ.vars "rat.n"=weights[s].num:=by simpa only [NNRat.natAbs_num_coe] using hn
    have hds:σ.vars "rat.d"=weights[s].den:=by simpa only [NNRat.den_coe] using hd
    have hnB:=hsn.trans_lt hM
    have hdB:=hsd.trans_lt hM
    (expose_names;
      (refine let c0:NNRat:= @getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i:Nat) => Nat.lt i (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) weights s hs; let c1:Nat:=NNRat.num c0; let c2:Nat:=NNRat.den c0; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "left.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "left.n") c1) (@Eq Nat (Env.vars τ "left.d") c2))) σ; let c4:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n"; let c5:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" c4; let c6:Nat:=Env.vars c5 "rat.d"; let c7:Env:=Env.setVar c5 "left.d" c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat→ Nat:=c8 ((1:Nat)); let c10:Nat:=c9 (Expr.size (Expr.var "rat.s")); let c11:Nat:=c9 (Expr.size (Expr.var "rat.n")); let c12:Nat:=c9 (Expr.size (Expr.var "rat.d")); let c13:Nat:=c8 c11 c12; let c14:String→ Nat:=Env.vars c7; @Exists.intro Env (fun (σ':Env) => And (Run B copyLeft σ σ' ((6:Nat))) (c3 σ')) c7 (@And.intro (Run B copyLeft σ c7 ((6:Nat))) (c3 c7) (RunStep.mono B copyLeft σ c7 (c8 c10 c13) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.var "rat.s")) (Com.seq (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d"))) σ (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c7 c10 c13 (RunStep.assign B σ "left.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5786_0_0_0))) (RunStep.seq B (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d")) (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c5 c7 c11 c12 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" (Expr.var "rat.n") c4 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g5786_0_0_1))) (RunStep.assign B c5 "left.d" (Expr.var "rat.d") c6 (RunStep.eval_var B c5 "rat.d" (?nAX_g5786_0_0_2))))) (?nAX_g5786_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5786_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  have hright:Spec B (fun σ => FractionOutput (weights[t]:ℚ) σ∧ σ.vars "rat.s"=0)
      copyRight (fun _ τ => τ.vars "right.s"=0∧ τ.vars "right.n"=weights[t].num∧
        τ.vars "right.d"=weights[t].den) 6:=by
    rintro σ ⟨⟨hv,hn,hd,hsg⟩,hzero⟩
    have hns:σ.vars "rat.n"=weights[t].num:=by simpa only [NNRat.natAbs_num_coe] using hn
    have hds:σ.vars "rat.d"=weights[t].den:=by simpa only [NNRat.den_coe] using hd
    have hnB:=htn.trans_lt hM
    have hdB:=htd.trans_lt hM
    (expose_names;
      (refine let c0:NNRat:= @getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i:Nat) => Nat.lt i (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) weights t ht; let c1:Nat:=NNRat.num c0; let c2:Nat:=NNRat.den c0; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "right.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "right.n") c1) (@Eq Nat (Env.vars τ "right.d") c2))) σ; let c4:Nat:=Env.vars (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n"; let c5:Env:=Env.setVar (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" c4; let c6:Nat:=Env.vars c5 "rat.d"; let c7:Env:=Env.setVar c5 "right.d" c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat→ Nat:=c8 ((1:Nat)); let c10:Nat:=c9 (Expr.size (Expr.var "rat.s")); let c11:Nat:=c9 (Expr.size (Expr.var "rat.n")); let c12:Nat:=c9 (Expr.size (Expr.var "rat.d")); let c13:Nat:=c8 c11 c12; let c14:String→ Nat:=Env.vars c7; @Exists.intro Env (fun (σ':Env) => And (Run B copyRight σ σ' ((6:Nat))) (c3 σ')) c7 (@And.intro (Run B copyRight σ c7 ((6:Nat))) (c3 c7) (RunStep.mono B copyRight σ c7 (c8 c10 c13) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.var "rat.s")) (Com.seq (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d"))) σ (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c7 c10 c13 (RunStep.assign B σ "right.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5786_1_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "rat.n")) (Com.assign "right.d" (Expr.var "rat.d")) (Env.setVar σ "right.s" (Env.vars σ "rat.s")) c5 c7 c11 c12 (RunStep.assign B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "right.n" (Expr.var "rat.n") c4 (RunStep.eval_var B (Env.setVar σ "right.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g5786_1_0_1))) (RunStep.assign B c5 "right.d" (Expr.var "rat.d") c6 (RunStep.eval_var B c5 "rat.d" (?nAX_g5786_1_0_2))))) (?nAX_g5786_1_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5786_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5786_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all
  have hmul:=multiplyFraction_spec B M 0 weights[s].num weights[s].den
    0 weights[t].num weights[t].den hB (by omega) (by omega) hsn hsd htn htd
      weights[s].den_pos weights[t].den_pos
  have hvs:fractionValue 0 weights[s].num weights[s].den=(weights[s]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den weights[s])
  have hvt:fractionValue 0 weights[t].num weights[t].den=(weights[t]:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den weights[t])
  rintro σ ⟨hp,hσs,hσt⟩
  obtain ⟨ν,hrS,hsPost⟩:=hreadS σ ⟨hp,hσs⟩
  obtain ⟨μ,hcpS,hleftPost⟩:=hleft ν hsPost
  have hpμ:Prefix (RamUnsignedBuffer.encode weights) "flow.weights" μ:=by
    simpa only [Prefix,hcpS.frame_arr "flow.weights" (by simp [copyLeft,Com.warrs]),
      hrS.frame_arr "flow.weights" (by simp [RamUnsignedBuffer.read,Com.warrs])] using hp
  have htμ:μ.vars "lp.t"=t:=
    (hcpS.frame_var "lp.t" (by simp [copyLeft,Com.wvars])).trans
      ((hrS.frame_var "lp.t" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hσt)
  obtain ⟨ρ,hrT,htPost⟩:=hreadT μ ⟨hpμ,htμ⟩
  obtain ⟨κ,hcpT,hrightPost⟩:=hright ρ htPost
  have hls:κ.vars "left.s"=0:=
    (hcpT.frame_var "left.s" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.s" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.1)
  have hln:κ.vars "left.n"=weights[s].num:=
    (hcpT.frame_var "left.n" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.n" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.2.1)
  have hld:κ.vars "left.d"=weights[s].den:=
    (hcpT.frame_var "left.d" (by simp [copyRight,Com.wvars])).trans
      ((hrT.frame_var "left.d" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hleftPost.2.2)
  obtain ⟨τ,hrMul,hpost⟩:=hmul κ ⟨hls,hln,hld,hrightPost⟩
  exact ⟨τ,(hrS.seq (hcpS.seq (hrT.seq (hcpT.seq hrMul)))).mono (by omega),
    by simpa only [hvs,hvt] using hpost⟩

end Lax455465Proofs.RamWeightProduct

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

namespace Lax455465Proofs.RamFlowContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

def Context (n i j:ℕ) (weights:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n*n∧ σ.vars "lp.n3"=(n*n)*n∧
    σ.vars "lp.i"=i∧ σ.vars "lp.j"=j∧
      Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ

theorem frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    (n i j:ℕ) (weights:List ℚ≥0) (h:Context n i j weights σ)
    (ha:"flow.weights" ∉ c.warrs)
    (hx:∀ x∈ ["lp.n","lp.n2","lp.n3","lp.i","lp.j"],x∉ c.wvars):
    Context n i j weights τ:=by
  have hn:=hr.frame_var "lp.n" (hx _ (by simp))
  have hn2:=hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3:=hr.frame_var "lp.n3" (hx _ (by simp))
  have hi:=hr.frame_var "lp.i" (hx _ (by simp))
  have hj:=hr.frame_var "lp.j" (hx _ (by simp))
  have harr:=hr.frame_arr "flow.weights" ha
  simpa only [Context,Prefix,hn,hn2,hn3,hi,hj,harr] using h

end Lax455465Proofs.RamFlowContext

end

section

namespace Lax455465Proofs.RamFlowData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

theorem frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K)
    {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (h:Data I σ)
    (ha:∀ a∈ ["flow.weights","flow.capacities"],a∉ c.warrs)
    (hx:∀ x∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"],x∉ c.wvars):
    Data I τ:=by
  have hn:=hr.frame_var "lp.n" (hx _ (by simp))
  have hn2:=hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3:=hr.frame_var "lp.n3" (hx _ (by simp))
  have hrows:=hr.frame_var "lp.rows" (hx _ (by simp))
  have hcols:=hr.frame_var "lp.columns" (hx _ (by simp))
  have htotal:=hr.frame_var "lp.matrixLength" (hx _ (by simp))
  have hw:=hr.frame_arr "flow.weights" (ha _ (by simp))
  have hc:=hr.frame_arr "flow.capacities" (ha _ (by simp))
  simpa only [Data,Prefix,hn,hn2,hn3,hrows,hcols,htotal,hw,hc] using h

theorem set_index {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (σ:Env)
    (index:String) (k:ℕ) (h:Data I σ)
    (hx:∀ x∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"],x ≠ index):
    Data I (σ.setVar index k):=by
  simpa only [Data,Prefix,vars_setVar,arrs_setVar,if_neg (hx "lp.n" (by simp)),if_neg (hx "lp.n2" (by simp)),
    if_neg (hx "lp.n3" (by simp)),if_neg (hx "lp.rows" (by simp)),
    if_neg (hx "lp.columns" (by simp)),if_neg (hx "lp.matrixLength" (by simp))] using h

end Lax455465Proofs.RamFlowData

end

section

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem zero_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zero σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zero σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5825_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5825_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5825_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5825_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem one_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) one (fun _ τ => FractionOutput 1 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((1:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c8:Nat:=c4 c7 c7; let c9:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B one σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B one σ c3 (c4 c6 c8) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c9 c10) σ c1 c3 c6 c8 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5826_0_0_0))) (RunStep.seq B c9 c10 c1 c2 c3 c7 c7 (RunStep.assign B c1 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c1 h1)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5826_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5826_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5826_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem negativeOne_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) negativeOne (fun _ τ => FractionOutput (-1) τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Env:=Env.setVar σ "rat.s" ((1:Nat)); let c3:Env:=Env.setVar c2 "rat.n" ((1:Nat)); let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=c5 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); let c7:Nat→ Nat:=c5 c6; let c8:Nat:=c7 c6; let c9:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B negativeOne σ σ' ((6:Nat))) (c1 σ')) c4 (@And.intro (Run B negativeOne σ c4 ((6:Nat))) (c1 c4) (RunStep.mono B negativeOne σ c4 (c7 c8) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((1:Nat)))) (Com.seq c9 c10) σ c2 c4 c6 c8 (RunStep.assign B σ "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B c9 c10 c2 c3 c4 c6 c6 (RunStep.assign B c2 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)) (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g5827_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5827_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem negate_spec (B:ℕ) (q:ℚ) (h1:1 < B):
    Spec B (FractionOutput q) negate (fun _ τ => FractionOutput (-q) τ) 4:=by
  rintro σ ⟨hvalue,hn,hd,hs⟩
  have hsign:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by omega
  rcases hsign with hs₀ | hs₁
  · (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negate σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negate σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negate σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" (?nAX_g5828_0_0_0)) (?nAX_g5828_0_0_1))) (?nAX_g5828_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5828_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
  · (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) σ; let c1:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) (Env.vars σ "rat.s"); let c2:Env:=Env.setVar σ "rat.s" c1; let c3:Expr:=Expr.sub (Expr.lit ((1:Nat))) (Expr.var "rat.s"); @Exists.intro Env (fun (σ':Env) => And (Run B negate σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B negate σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B negate σ c2 (Nat.add ((1:Nat)) (Expr.size c3)) ((4:Nat)) (RunStep.assign B σ "rat.s" c3 c1 (RunStep.eval_sub B σ (Expr.lit ((1:Nat))) (Expr.var "rat.s") ((1:Nat)) (Env.vars σ "rat.s") (RunStep.eval_lit B ((1:Nat)) σ h1) (RunStep.eval_var B σ "rat.s" (?nAX_g5828_1_0_0)) (?nAX_g5828_1_0_1))) (?nAX_g5828_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5828_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5828_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [FractionOutput,fractionValue,Rat.neg_num,Int.natAbs_neg,Rat.neg_den,neg_div]
    all_goals linarith

end Lax455465Proofs.RamFractionPrimitives

end

section

namespace Lax455465Proofs.RamFlowDemand

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def value (s t u:ℕ) (product:ℚ):ℚ:=
  if s=t then 0 else if u=s then -product else if u=t then product else 0

def command:Com:=.ite (.eq (.var "lp.s") (.var "lp.t")) RamFractionPrimitives.zero
  (.ite (.eq (.var "lp.u") (.var "lp.s"))
    (.seq RamWeightProduct.command RamFractionPrimitives.negate)
    (.ite (.eq (.var "lp.u") (.var "lp.t")) RamWeightProduct.command RamFractionPrimitives.zero))

theorem command_spec (B M:ℕ) (weights:List ℚ≥0) (s t u:ℕ)
    (hs:s < weights.length) (ht:t < weights.length) (hu:u < B)
    (hB:2*M^2+3 < B) (hsi:2*s+1 < B) (hti:2*t+1 < B)
    (hsn:weights[s].num≤ M) (hsd:weights[s].den≤ M)
    (htn:weights[t].num≤ M) (htd:weights[t].den≤ M):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ∧
      σ.vars "lp.s"=s∧ σ.vars "lp.t"=t∧ σ.vars "lp.u"=u) command
      (fun _ τ => FractionOutput (value s t u ((weights[s]:ℚ)*(weights[t]:ℚ))) τ)
      (36*(weights[s].den*weights[t].den).size+120):=by
  have h1:1 < B:=by nlinarith
  have hsB:s < B:=by omega
  have htB:t < B:=by omega
  have hproduct:=RamWeightProduct.command_spec B M weights s t hs ht hB hsi hti hsn hsd htn htd
  have hneg:=RamFractionPrimitives.negate_spec B ((weights[s]:ℚ)*(weights[t]:ℚ)) h1
  have hzero:=RamFractionPrimitives.zero_spec B h1
  rintro σ ⟨hp,hσs,hσt,hσu⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "lp.s") (Env.vars σ "lp.t"); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:(i:Nat)→ Nat.lt i (@List.length NNRat weights)→ NNRat:= @getElem (List NNRat) Nat NNRat (fun (as:List NNRat) (i:Nat) => Nat.lt i (@List.length NNRat as)) (@List.instGetElemNatLtLength NNRat) weights; let c5:NNRat:=c4 s hs; let c6:NNRat:=c4 t ht; let c7:Nat→ Nat:=c2 (c3 ((36:Nat)) (Nat.size (c3 (NNRat.den c5) (NNRat.den c6)))); let c8:Nat:=c7 ((120:Nat)); let c9:Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@NNRat.cast Rat Rat.instNNRatCast c5) (@NNRat.cast Rat Rat.instNNRatCast c6); let c10:Env→ Prop:=FractionOutput (value s t u c9); let c11:Env→ Prop:=(fun (x τ:Env) => c10 τ) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B command σ σ' c8) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Env→ Prop:=fun (σ':Env) => And (Run B RamFractionPrimitives.zero σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ'); let c15:Nat→ Nat:=c2 ((1:Nat)); let c16:Nat→ Nat:=c2 (c15 (Cond.size (Cond.eq (Expr.var "lp.s") (Expr.var "lp.t")))); let c17:Com:=Com.ite (Cond.eq (Expr.var "lp.u") (Expr.var "lp.t")) RamWeightProduct.command RamFractionPrimitives.zero; let c18:Com:=Com.ite (Cond.eq (Expr.var "lp.u") (Expr.var "lp.s")) (Com.seq RamWeightProduct.command RamFractionPrimitives.negate) c17; let c19:Prop:= @Eq Nat (Env.vars σ "lp.u") (Env.vars σ "lp.s"); let c20:Prop:=Not c19; let c21:Nat:=c7 ((104:Nat)); let c22:Env→ Prop:=FractionOutput c9; let c23:Env→ Prop:=fun (σ':Env) => And (Run B RamWeightProduct.command σ σ' c21) (c22 σ'); let c24:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg c9); let c25:Nat→ Nat:=c2 (c15 (Cond.size (Cond.eq (Expr.var "lp.u") (Expr.var "lp.s")))); let c26:Nat:=c2 c21 ((4:Nat)); let c27:Nat:=c25 c26; let c28:Prop:= @Eq Nat (Env.vars σ "lp.u") (Env.vars σ "lp.t"); let c29:Prop:=Not c28; let c30:Nat→ Nat:=c2 (c15 (Cond.size (Cond.eq (Expr.var "lp.u") (Expr.var "lp.t")))); let c31:Nat:=c30 c21; let c32:Nat:=c25 c31; let c33:Nat:=c30 ((6:Nat)); let c34:Nat:=c25 c33; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c13) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => c13) (RunStep.use B (fun (x:Env) => True) RamFractionPrimitives.zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B RamFractionPrimitives.zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B RamFractionPrimitives.zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c12 w (@And.intro (Run B command σ w c8) (c11 w) (RunStep.mono B command σ w (c16 ((6:Nat))) c8 (RunStep.ite_true B (Cond.eq (Expr.var "lp.s") (Expr.var "lp.t")) RamFractionPrimitives.zero c18 σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.s") (Expr.var "lp.t") (Env.vars σ "lp.s") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_0)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_1)) hcase) left) (?nAX_g5831_0_0_2)) ?_)) fun (hcase:c1) => @Or.casesOn c19 c20 (fun (x:Or c19 c20) => c13) (Classical.em c19) (fun (hcase_1:c19) => @Exists.casesOn Env c23 (fun (x:@Exists Env c23) => c13) (RunStep.use B (fun (σ_1:Env) => And (Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ_1) (And (@Eq Nat (Env.vars σ_1 "lp.s") s) (@Eq Nat (Env.vars σ_1 "lp.t") t))) RamWeightProduct.command (fun (x τ:Env) => c22 τ) c21 hproduct σ ?_) fun (w:Env) (h:And (Run B RamWeightProduct.command σ w c21) (c22 w)) => let c0_1:Env→ Prop:=fun (σ':Env) => And (Run B RamFractionPrimitives.negate w σ' ((4:Nat))) (c24 σ'); @And.casesOn (Run B RamWeightProduct.command σ w c21) (c22 w) (fun (x:And (Run B RamWeightProduct.command σ w c21) (c22 w)) => c13) h fun (left:Run B RamWeightProduct.command σ w c21) (right:c22 w) => @Exists.casesOn Env c0_1 (fun (x:@Exists Env c0_1) => c13) (RunStep.use B c22 RamFractionPrimitives.negate (fun (x τ:Env) => c24 τ) ((4:Nat)) hneg w ?_) fun (w_1:Env) (h_1:And (Run B RamFractionPrimitives.negate w w_1 ((4:Nat))) (c24 w_1)) => let c0_2:Prop:=Run B RamFractionPrimitives.negate w w_1 ((4:Nat)); @And.casesOn c0_2 (c24 w_1) (fun (x:And c0_2 (c24 w_1)) => c13) h_1 fun (left_1:c0_2) (right_1:c24 w_1) => @Exists.intro Env c12 w_1 (@And.intro (Run B command σ w_1 c8) (c11 w_1) (RunStep.mono B command σ w_1 (c16 c27) c8 (RunStep.ite_false B (Cond.eq (Expr.var "lp.s") (Expr.var "lp.t")) RamFractionPrimitives.zero c18 σ w_1 c27 (RunStep.cond_eq_false B σ (Expr.var "lp.s") (Expr.var "lp.t") (Env.vars σ "lp.s") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_3)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_4)) hcase) (RunStep.ite_true B (Cond.eq (Expr.var "lp.u") (Expr.var "lp.s")) (Com.seq RamWeightProduct.command RamFractionPrimitives.negate) c17 σ w_1 c26 (RunStep.cond_eq_true B σ (Expr.var "lp.u") (Expr.var "lp.s") (Env.vars σ "lp.u") (Env.vars σ "lp.s") (RunStep.eval_var B σ "lp.u" (?nAX_g5831_0_0_5)) (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_6)) hcase_1) (RunStep.seq B RamWeightProduct.command RamFractionPrimitives.negate σ w w_1 c21 ((4:Nat)) left left_1))) (?nAX_g5831_0_0_7)) ?_)) fun (hcase_1:c20) => @Or.casesOn c28 c29 (fun (x:Or c28 c29) => c13) (Classical.em c28) (fun (hcase_2:c28) => @Exists.casesOn Env c23 (fun (x:@Exists Env c23) => c13) (RunStep.use B (fun (σ_1:Env) => And (Prefix (RamUnsignedBuffer.encode weights) "flow.weights" σ_1) (And (@Eq Nat (Env.vars σ_1 "lp.s") s) (@Eq Nat (Env.vars σ_1 "lp.t") t))) RamWeightProduct.command (fun (x τ:Env) => c22 τ) c21 hproduct σ ?_) fun (w:Env) (h:And (Run B RamWeightProduct.command σ w c21) (c22 w)) => @And.casesOn (Run B RamWeightProduct.command σ w c21) (c22 w) (fun (x:And (Run B RamWeightProduct.command σ w c21) (c22 w)) => c13) h fun (left:Run B RamWeightProduct.command σ w c21) (right:c22 w) => @Exists.intro Env c12 w (@And.intro (Run B command σ w c8) (c11 w) (RunStep.mono B command σ w (c16 c32) c8 (RunStep.ite_false B (Cond.eq (Expr.var "lp.s") (Expr.var "lp.t")) RamFractionPrimitives.zero c18 σ w c32 (RunStep.cond_eq_false B σ (Expr.var "lp.s") (Expr.var "lp.t") (Env.vars σ "lp.s") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_8)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_9)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "lp.u") (Expr.var "lp.s")) (Com.seq RamWeightProduct.command RamFractionPrimitives.negate) c17 σ w c31 (RunStep.cond_eq_false B σ (Expr.var "lp.u") (Expr.var "lp.s") (Env.vars σ "lp.u") (Env.vars σ "lp.s") (RunStep.eval_var B σ "lp.u" (?nAX_g5831_0_0_10)) (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_11)) hcase_1) (RunStep.ite_true B (Cond.eq (Expr.var "lp.u") (Expr.var "lp.t")) RamWeightProduct.command RamFractionPrimitives.zero σ w c21 (RunStep.cond_eq_true B σ (Expr.var "lp.u") (Expr.var "lp.t") (Env.vars σ "lp.u") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.u" (?nAX_g5831_0_0_12)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_13)) hcase_2) left))) (?nAX_g5831_0_0_14)) ?_)) fun (hcase_2:c29) => @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => c13) (RunStep.use B (fun (x:Env) => True) RamFractionPrimitives.zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B RamFractionPrimitives.zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B RamFractionPrimitives.zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c12 w (@And.intro (Run B command σ w c8) (c11 w) (RunStep.mono B command σ w (c16 c34) c8 (RunStep.ite_false B (Cond.eq (Expr.var "lp.s") (Expr.var "lp.t")) RamFractionPrimitives.zero c18 σ w c34 (RunStep.cond_eq_false B σ (Expr.var "lp.s") (Expr.var "lp.t") (Env.vars σ "lp.s") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_15)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_16)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "lp.u") (Expr.var "lp.s")) (Com.seq RamWeightProduct.command RamFractionPrimitives.negate) c17 σ w c33 (RunStep.cond_eq_false B σ (Expr.var "lp.u") (Expr.var "lp.s") (Env.vars σ "lp.u") (Env.vars σ "lp.s") (RunStep.eval_var B σ "lp.u" (?nAX_g5831_0_0_17)) (RunStep.eval_var B σ "lp.s" (?nAX_g5831_0_0_18)) hcase_1) (RunStep.ite_false B (Cond.eq (Expr.var "lp.u") (Expr.var "lp.t")) RamWeightProduct.command RamFractionPrimitives.zero σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.u") (Expr.var "lp.t") (Env.vars σ "lp.u") (Env.vars σ "lp.t") (RunStep.eval_var B σ "lp.u" (?nAX_g5831_0_0_19)) (RunStep.eval_var B σ "lp.t" (?nAX_g5831_0_0_20)) hcase_2) left))) (?nAX_g5831_0_0_21)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5831_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5831_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals simp_all [value]

end Lax455465Proofs.RamFlowDemand

end

section

namespace Lax455465Proofs.RamFlowUnits

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamFractionPrimitives

def arcValue (commodity rowCommodity source target vertex:ℕ):ℚ:=
  if commodity=rowCommodity then
    (if source=vertex then 1 else 0) - (if target=vertex then 1 else 0)
  else 0

def arc:Com:=.ite (.eq (.var "lp.arcCommodity") (.var "lp.commodity"))
  (.ite (.eq (.var "lp.arcSource") (.var "lp.u"))
    (.ite (.eq (.var "lp.arcTarget") (.var "lp.u")) zero one)
    (.ite (.eq (.var "lp.arcTarget") (.var "lp.u")) negativeOne zero)) zero

theorem arc_spec (B a b u v z:ℕ) (h1:1 < B)
    (ha:a < B) (hb:b < B) (hu:u < B) (hv:v < B) (hz:z < B):
    Spec B (fun σ => σ.vars "lp.arcCommodity"=a∧ σ.vars "lp.commodity"=b∧
      σ.vars "lp.arcSource"=u∧ σ.vars "lp.arcTarget"=v∧ σ.vars "lp.u"=z) arc
      (fun _ τ => FractionOutput (arcValue a b u v z) τ) 18:=by
  have hzero:=zero_spec B h1
  have hone:=one_spec B h1
  have hnegative:=negativeOne_spec B h1
  rintro σ ⟨haσ,hbσ,huσ,hvσ,hzσ⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (arcValue a b u v z); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B arc σ σ' ((18:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:= @Eq Nat (Env.vars σ "lp.arcSource") (Env.vars σ "lp.u"); let c7:Prop:=Not c6; let c8:Prop:= @Eq Nat (Env.vars σ "lp.arcTarget") (Env.vars σ "lp.u"); let c9:Prop:=Not c8; let c10:Env→ Prop:=fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ'); let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Nat→ Nat:=c11 (c12 (Cond.size (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")))); let c14:Nat:=c11 (c12 (Cond.size (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")))) ((6:Nat)); let c15:Nat:=c11 (c12 (Cond.size (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")))) c14; let c16:Com:=Com.ite (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) zero one; let c17:Com:=Com.ite (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) negativeOne zero; let c18:Com:=Com.ite (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")) c16 c17; let c19:Env→ Prop:=fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) σ'); let c20:Env→ Prop:=FractionOutput (@Neg.neg Rat Rat.instNeg (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c21:Env→ Prop:=fun (σ':Env) => And (Run B negativeOne σ σ' ((6:Nat))) (c20 σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c5) (Classical.em c8) (fun (hcase_2:c8) => @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c5) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B arc σ w ((18:Nat))) (c3 w) (RunStep.mono B arc σ w (c13 c15) ((18:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")) c18 zero σ w c15 (RunStep.cond_eq_true B σ (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity") (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity") (RunStep.eval_var B σ "lp.arcCommodity" (?nAX_g5834_0_0_0)) (RunStep.eval_var B σ "lp.commodity" (?nAX_g5834_0_0_1)) hcase) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")) c16 c17 σ w c14 (RunStep.cond_eq_true B σ (Expr.var "lp.arcSource") (Expr.var "lp.u") (Env.vars σ "lp.arcSource") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcSource" (?nAX_g5834_0_0_2)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_3)) hcase_1) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) zero one σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.arcTarget") (Expr.var "lp.u") (Env.vars σ "lp.arcTarget") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcTarget" (?nAX_g5834_0_0_4)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_5)) hcase_2) left))) (?nAX_g5834_0_0_6)) ?_)) fun (hcase_2:c9) => @Exists.casesOn Env c19 (fun (x:@Exists Env c19) => c5) (RunStep.use B (fun (x:Env) => True) one (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (Run B one σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w)) => let c0_1:Prop:=Run B one σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B arc σ w ((18:Nat))) (c3 w) (RunStep.mono B arc σ w (c13 c15) ((18:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")) c18 zero σ w c15 (RunStep.cond_eq_true B σ (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity") (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity") (RunStep.eval_var B σ "lp.arcCommodity" (?nAX_g5834_0_0_7)) (RunStep.eval_var B σ "lp.commodity" (?nAX_g5834_0_0_8)) hcase) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")) c16 c17 σ w c14 (RunStep.cond_eq_true B σ (Expr.var "lp.arcSource") (Expr.var "lp.u") (Env.vars σ "lp.arcSource") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcSource" (?nAX_g5834_0_0_9)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_10)) hcase_1) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) zero one σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.arcTarget") (Expr.var "lp.u") (Env.vars σ "lp.arcTarget") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcTarget" (?nAX_g5834_0_0_11)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_12)) hcase_2) left))) (?nAX_g5834_0_0_13)) ?_)) fun (hcase_1:c7) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c5) (Classical.em c8) (fun (hcase_2:c8) => @Exists.casesOn Env c21 (fun (x:@Exists Env c21) => c5) (RunStep.use B (fun (x:Env) => True) negativeOne (fun (x τ:Env) => c20 τ) ((6:Nat)) hnegative σ ?_) fun (w:Env) (h:And (Run B negativeOne σ w ((6:Nat))) (c20 w)) => let c0_1:Prop:=Run B negativeOne σ w ((6:Nat)); @And.casesOn c0_1 (c20 w) (fun (x:And c0_1 (c20 w)) => c5) h fun (left:c0_1) (right:c20 w) => @Exists.intro Env c4 w (@And.intro (Run B arc σ w ((18:Nat))) (c3 w) (RunStep.mono B arc σ w (c13 c15) ((18:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")) c18 zero σ w c15 (RunStep.cond_eq_true B σ (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity") (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity") (RunStep.eval_var B σ "lp.arcCommodity" (?nAX_g5834_0_0_14)) (RunStep.eval_var B σ "lp.commodity" (?nAX_g5834_0_0_15)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")) c16 c17 σ w c14 (RunStep.cond_eq_false B σ (Expr.var "lp.arcSource") (Expr.var "lp.u") (Env.vars σ "lp.arcSource") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcSource" (?nAX_g5834_0_0_16)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_17)) hcase_1) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) negativeOne zero σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.arcTarget") (Expr.var "lp.u") (Env.vars σ "lp.arcTarget") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcTarget" (?nAX_g5834_0_0_18)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_19)) hcase_2) left))) (?nAX_g5834_0_0_20)) ?_)) fun (hcase_2:c9) => @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c5) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B arc σ w ((18:Nat))) (c3 w) (RunStep.mono B arc σ w (c13 c15) ((18:Nat)) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")) c18 zero σ w c15 (RunStep.cond_eq_true B σ (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity") (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity") (RunStep.eval_var B σ "lp.arcCommodity" (?nAX_g5834_0_0_21)) (RunStep.eval_var B σ "lp.commodity" (?nAX_g5834_0_0_22)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arcSource") (Expr.var "lp.u")) c16 c17 σ w c14 (RunStep.cond_eq_false B σ (Expr.var "lp.arcSource") (Expr.var "lp.u") (Env.vars σ "lp.arcSource") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcSource" (?nAX_g5834_0_0_23)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_24)) hcase_1) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arcTarget") (Expr.var "lp.u")) negativeOne zero σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.arcTarget") (Expr.var "lp.u") (Env.vars σ "lp.arcTarget") (Env.vars σ "lp.u") (RunStep.eval_var B σ "lp.arcTarget" (?nAX_g5834_0_0_25)) (RunStep.eval_var B σ "lp.u" (?nAX_g5834_0_0_26)) hcase_2) left))) (?nAX_g5834_0_0_27)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c5) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B arc σ w ((18:Nat))) (c3 w) (RunStep.mono B arc σ w (c13 ((6:Nat))) ((18:Nat)) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity")) c18 zero σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.arcCommodity") (Expr.var "lp.commodity") (Env.vars σ "lp.arcCommodity") (Env.vars σ "lp.commodity") (RunStep.eval_var B σ "lp.arcCommodity" (?nAX_g5834_0_0_28)) (RunStep.eval_var B σ "lp.commodity" (?nAX_g5834_0_0_29)) hcase) left) (?nAX_g5834_0_0_30)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5834_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5834_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [arcValue]

def capacityValue (column arc row:ℕ):ℚ:=
  if column=0 then 0 else if arc=row then 1 else 0

def capacity:Com:=.ite (.eq (.var "lp.j") (.lit 0)) zero
  (.ite (.eq (.var "lp.arc") (.var "lp.i")) one zero)

theorem capacity_spec (B column arcIndex row:ℕ) (h1:1 < B)
    (hc:column < B) (ha:arcIndex < B) (hr:row < B):
    Spec B (fun σ => σ.vars "lp.j"=column∧ σ.vars "lp.arc"=arcIndex∧ σ.vars "lp.i"=row)
      capacity (fun _ τ => FractionOutput (capacityValue column arcIndex row) τ) 14:=by
  have hzero:=zero_spec B h1
  have hone:=one_spec B h1
  rintro σ ⟨hcol,harc,hrow⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "lp.j") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => FractionOutput (capacityValue column arcIndex row) τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B capacity σ σ' ((14:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Env→ Prop:=fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ'); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "lp.j") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Com:=Com.ite (Cond.eq (Expr.var "lp.arc") (Expr.var "lp.i")) one zero; let c11:Prop:= @Eq Nat (Env.vars σ "lp.arc") (Env.vars σ "lp.i"); let c12:Prop:=Not c11; let c13:Env→ Prop:=fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) σ'); let c14:Nat:=c6 (c7 (Cond.size (Cond.eq (Expr.var "lp.arc") (Expr.var "lp.i")))) ((6:Nat)); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c4) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c3 w (@And.intro (Run B capacity σ w ((14:Nat))) (c2 w) (RunStep.mono B capacity σ w (c9 ((6:Nat))) ((14:Nat)) (RunStep.ite_true B c8 zero c10 σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.j") (Expr.lit ((0:Nat))) (Env.vars σ "lp.j") ((0:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5837_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5837_0_0_1)) hcase) left) (?nAX_g5837_0_0_2)) ?_)) fun (hcase:c1) => @Or.casesOn c11 c12 (fun (x:Or c11 c12) => c4) (Classical.em c11) (fun (hcase_1:c11) => @Exists.casesOn Env c13 (fun (x:@Exists Env c13) => c4) (RunStep.use B (fun (x:Env) => True) one (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (Run B one σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w)) => let c0_1:Prop:=Run B one σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c3 w (@And.intro (Run B capacity σ w ((14:Nat))) (c2 w) (RunStep.mono B capacity σ w (c9 c14) ((14:Nat)) (RunStep.ite_false B c8 zero c10 σ w c14 (RunStep.cond_eq_false B σ (Expr.var "lp.j") (Expr.lit ((0:Nat))) (Env.vars σ "lp.j") ((0:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5837_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5837_0_0_4)) hcase) (RunStep.ite_true B (Cond.eq (Expr.var "lp.arc") (Expr.var "lp.i")) one zero σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.arc") (Expr.var "lp.i") (Env.vars σ "lp.arc") (Env.vars σ "lp.i") (RunStep.eval_var B σ "lp.arc" (?nAX_g5837_0_0_5)) (RunStep.eval_var B σ "lp.i" (?nAX_g5837_0_0_6)) hcase_1) left)) (?nAX_g5837_0_0_7)) ?_)) fun (hcase_1:c12) => @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c4) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c3 w (@And.intro (Run B capacity σ w ((14:Nat))) (c2 w) (RunStep.mono B capacity σ w (c9 c14) ((14:Nat)) (RunStep.ite_false B c8 zero c10 σ w c14 (RunStep.cond_eq_false B σ (Expr.var "lp.j") (Expr.lit ((0:Nat))) (Env.vars σ "lp.j") ((0:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5837_0_0_8)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5837_0_0_9)) hcase) (RunStep.ite_false B (Cond.eq (Expr.var "lp.arc") (Expr.var "lp.i")) one zero σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.arc") (Expr.var "lp.i") (Env.vars σ "lp.arc") (Env.vars σ "lp.i") (RunStep.eval_var B σ "lp.arc" (?nAX_g5837_0_0_10)) (RunStep.eval_var B σ "lp.i" (?nAX_g5837_0_0_11)) hcase_1) left)) (?nAX_g5837_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5837_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5837_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [capacityValue]

def objective:Com:=.ite (.eq (.var "lp.j") (.lit 0)) one zero

theorem objective_spec (B column:ℕ) (h1:1 < B) (hc:column < B):
    Spec B (fun σ => σ.vars "lp.j"=column) objective
      (fun _ τ => FractionOutput (if column=0 then 1 else 0) τ) 10:=by
  have hzero:=zero_spec B h1
  have hone:=one_spec B h1
  rintro σ hcol
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "lp.j") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@ite Rat (@Eq Nat column ((0:Nat))) (instDecidableEqNat column ((0:Nat))) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B objective σ σ' ((10:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Env→ Prop:=fun (σ':Env) => And (Run B one σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) σ'); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Cond:=Cond.eq (Expr.var "lp.j") (Expr.lit ((0:Nat))); let c9:Env→ Prop:=fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c5) (RunStep.use B (fun (x:Env) => True) one (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (Run B one σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w)) => let c0_1:Prop:=Run B one σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B objective σ w ((10:Nat))) (c3 w) (RunStep.mono B objective σ w (c7 (c7 ((1:Nat)) (Cond.size c8)) ((6:Nat))) ((10:Nat)) (RunStep.ite_true B c8 one zero σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.j") (Expr.lit ((0:Nat))) (Env.vars σ "lp.j") ((0:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5839_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5839_0_0_1)) hcase) left) (?nAX_g5839_0_0_2)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c5) (RunStep.use B (fun (x:Env) => True) zero (fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (Run B zero σ w ((6:Nat))) (FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w)) => let c0_1:Prop:=Run B zero σ w ((6:Nat)); let c1_1:Prop:=FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) w; @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c5) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B objective σ w ((10:Nat))) (c3 w) (RunStep.mono B objective σ w (c7 (c7 ((1:Nat)) (Cond.size c8)) ((6:Nat))) ((10:Nat)) (RunStep.ite_false B c8 one zero σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.j") (Expr.lit ((0:Nat))) (Env.vars σ "lp.j") ((0:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5839_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5839_0_0_4)) hcase) left) (?nAX_g5839_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5839_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5839_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5839_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5839_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5839_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5839_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

def rowSign:Com:=.ite (.eq (.var "lp.sign") (.lit 0)) .skip negate

theorem rowSign_spec (B flag:ℕ) (q:ℚ) (h1:1 < B) (hf:flag < B):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "lp.sign"=flag) rowSign
      (fun _ τ => FractionOutput (if flag=0 then q else -q) τ) 8:=by
  have hneg:=negate_spec B q h1
  rintro σ ⟨hvalue,hflag⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "lp.sign") ((0:Nat)); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@ite Rat (@Eq Nat flag ((0:Nat))) (instDecidableEqNat flag ((0:Nat))) q (@Neg.neg Rat Rat.instNeg q)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B rowSign σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Cond:=Cond.eq (Expr.var "lp.sign") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c6 (c6 ((1:Nat)) (Cond.size c7)); let c9:Env→ Prop:=fun (σ':Env) => And (Run B negate σ σ' ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 σ (@And.intro (Run B rowSign σ σ ((8:Nat))) (c3 σ) (RunStep.mono B rowSign σ σ (c8 ((1:Nat))) ((8:Nat)) (RunStep.ite_true B c7 Com.skip negate σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "lp.sign") (Expr.lit ((0:Nat))) (Env.vars σ "lp.sign") ((0:Nat)) (RunStep.eval_var B σ "lp.sign" (?nAX_g5841_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5841_0_0_1)) hcase) (RunStep.skip B σ)) (?nAX_g5841_0_0_2)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c5) (RunStep.use B (FractionOutput q) negate (fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) ((4:Nat)) hneg σ ?_) fun (w:Env) (h:And (Run B negate σ w ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => let c0_1:Prop:=Run B negate σ w ((4:Nat)); @And.casesOn c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w) (fun (x:And c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => c5) h fun (left:c0_1) (right:FractionOutput (@Neg.neg Rat Rat.instNeg q) w) => @Exists.intro Env c4 w (@And.intro (Run B rowSign σ w ((8:Nat))) (c3 w) (RunStep.mono B rowSign σ w (c8 ((4:Nat))) ((8:Nat)) (RunStep.ite_false B c7 Com.skip negate σ w ((4:Nat)) (RunStep.cond_eq_false B σ (Expr.var "lp.sign") (Expr.lit ((0:Nat))) (Env.vars σ "lp.sign") ((0:Nat)) (RunStep.eval_var B σ "lp.sign" (?nAX_g5841_0_0_3)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5841_0_0_4)) hcase) left) (?nAX_g5841_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5841_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5841_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5841_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5841_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5841_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5841_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

end Lax455465Proofs.RamFlowUnits

end

section

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val=s.val * n + t.val:=by
  simp [edgeIndex,finProdFinEquiv]
  ring

theorem balance_value {n:ℕ} (s t u:Fin n):
    (balanceIndex n ((s,t),u)).val=(s.val * n + t.val) * n + u.val:=by
  simp [balanceIndex,edgeIndex,finProdFinEquiv]
  ring

theorem value_variable {n:ℕ} (v:Fin 1):(variableIndex n (.inl v)).val=0:=by
  simp [variableIndex,finSumFinEquiv,Equiv.sumCongr]

theorem arc_variable {n:ℕ} (s t u v:Fin n):
    (variableIndex n (.inr ((s,t), (u,v)))).val =
      1 + (s.val * n + t.val) * (n * n) + (u.val * n + v.val):=by
  simp [variableIndex,arcIndex,edgeIndex,finProdFinEquiv,finSumFinEquiv,Equiv.sumCongr]
  ring

theorem capacity_row {n:ℕ} (u v:Fin n):(rowIndex n (.inl (u,v))).val=u.val * n + v.val:=by
  simp [rowIndex,edgeIndex,finProdFinEquiv,finSumFinEquiv,Equiv.sumCongr]
  ring

theorem balance_row {n:ℕ} (sign:Fin 2) (s t u:Fin n):
    (rowIndex n (.inr (sign, ((s,t),u)))).val =
      n * n + sign.val * ((n * n) * n) + (s.val * n + t.val) * n + u.val:=by
  simp [rowIndex,balanceIndex,edgeIndex,finProdFinEquiv,finSumFinEquiv,Equiv.sumCongr]
  ring

private theorem code_div (a b n:ℕ) (hn:0 < n) (hb:b < n):
    (a * n + b) / n=a:=by
  rw [Nat.add_comm,Nat.add_mul_div_right b a hn,Nat.div_eq_of_lt hb,Nat.zero_add]

private theorem code_mod (a b n:ℕ) (hb:b < n):(a * n + b) % n=b:=by
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hb]

theorem edge_div {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val / n=s.val:=by
  rw [edge_value]
  exact code_div _ _ _ ((Nat.zero_le t.val).trans_lt t.isLt) t.isLt

theorem edge_mod {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val % n=t.val:=by
  rw [edge_value]
  exact code_mod _ _ _ t.isLt

theorem arc_div {n:ℕ} (s t u v:Fin n):
    ((variableIndex n (.inr ((s,t), (u,v)))).val - 1) / (n * n)=(edgeIndex n (s,t)).val:=by
  have hcol:(variableIndex n (.inr ((s,t), (u,v)))).val - 1 =
      (edgeIndex n (s,t)).val * (n * n) + (edgeIndex n (u,v)).val:=by
    rw [arc_variable,edge_value,edge_value]
    omega
  rw [hcol]
  exact code_div _ _ _ (by nlinarith [s.isLt]) (edgeIndex n (u,v)).isLt

theorem arc_mod {n:ℕ} (s t u v:Fin n):
    ((variableIndex n (.inr ((s,t), (u,v)))).val - 1) % (n * n)=(edgeIndex n (u,v)).val:=by
  have hcol:(variableIndex n (.inr ((s,t), (u,v)))).val - 1 =
      (edgeIndex n (s,t)).val * (n * n) + (edgeIndex n (u,v)).val:=by
    rw [arc_variable,edge_value,edge_value]
    omega
  rw [hcol]
  exact code_mod _ _ _ (edgeIndex n (u,v)).isLt

theorem balance_div {n:ℕ} (s t u:Fin n):
    (balanceIndex n ((s,t),u)).val / n=(edgeIndex n (s,t)).val:=by
  rw [balance_value,edge_value]
  exact code_div _ _ _ ((Nat.zero_le u.val).trans_lt u.isLt) u.isLt

theorem balance_mod {n:ℕ} (s t u:Fin n):
    (balanceIndex n ((s,t),u)).val % n=u.val:=by
  rw [balance_value]
  exact code_mod _ _ _ u.isLt

theorem row_div {n:ℕ} (sign:Fin 2) (s t u:Fin n):
    ((rowIndex n (.inr (sign, ((s,t),u)))).val - n * n) / ((n * n) * n)=sign.val:=by
  have hrow:(rowIndex n (.inr (sign, ((s,t),u)))).val - n * n =
      sign.val * ((n * n) * n) + (balanceIndex n ((s,t),u)).val:=by
    rw [_root_.Lax455465Proofs.FlowLpIndices.balance_row,balance_value]
    omega
  rw [hrow]
  exact code_div _ _ _ (by nlinarith [s.isLt]) (balanceIndex n ((s,t),u)).isLt

theorem row_mod {n:ℕ} (sign:Fin 2) (s t u:Fin n):
    ((rowIndex n (.inr (sign, ((s,t),u)))).val - n * n) % ((n * n) * n) =
      (balanceIndex n ((s,t),u)).val:=by
  have hrow:(rowIndex n (.inr (sign, ((s,t),u)))).val - n * n =
      sign.val * ((n * n) * n) + (balanceIndex n ((s,t),u)).val:=by
    rw [_root_.Lax455465Proofs.FlowLpIndices.balance_row,balance_value]
    omega
  rw [hrow]
  exact code_mod _ _ _ (balanceIndex n ((s,t),u)).isLt

theorem edge_equal {n:ℕ} (a b:Edge n):
    (edgeIndex n a).val=(edgeIndex n b).val↔ a=b:=by
  rw [Fin.val_inj]
  exact (edgeIndex n).apply_eq_iff_eq

end Lax455465Proofs.FlowLpIndices

end

section

namespace Lax455465Proofs.FlowLpFlat

open DirectedFlowLP FlowLpIndices

def objective (column:ℕ):ℚ:=if column=0 then 1 else 0

theorem objective_eq {n:ℕ} (v:Variable n):
    objective (variableIndex n v).val=DirectedFlowLP.objective v:=by
  cases v with
  | inl v => simp only [objective,value_variable,if_true,DirectedFlowLP.objective]
  | inr a =>
    rcases a with ⟨⟨s,t⟩,⟨u,v⟩⟩
    have hcol:(variableIndex n (.inr ((s,t),(u,v)))).val ≠ 0:=by rw [arc_variable]; omega
    simp only [objective,if_neg hcol,DirectedFlowLP.objective]

end Lax455465Proofs.FlowLpFlat

end

section

namespace Lax455465Proofs.RamFlowBalance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP FlowLpIndices
open scoped NNRat

def command:Com:=.ite (.eq (.var "lp.j") (.lit 0)) RamFlowDemand.command RamFlowUnits.arc

def Ready {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (s t u:Fin n) (v:Variable n) (σ:Env):Prop:=
  Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ∧
    σ.vars "lp.s"=s.val∧ σ.vars "lp.t"=t.val∧ σ.vars "lp.u"=u.val∧
    σ.vars "lp.commodity"=(edgeIndex n (s,t)).val∧
    σ.vars "lp.j"=(variableIndex n v).val∧
    σ.vars "lp.arcCommodity"=((variableIndex n v).val-1)/(n*n)∧
    σ.vars "lp.arcSource"=(((variableIndex n v).val-1)%(n*n))/n∧
    σ.vars "lp.arcTarget"=(((variableIndex n v).val-1)%(n*n))%n

private theorem demand_eq {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (s t u:Fin n):
    RamFlowDemand.value s.val t.val u.val ((I.weight s:ℚ)*(I.weight t:ℚ)) =
      -DirectedFlowLP.divergence I s t u:=by
  by_cases hst:s=t
  · subst t; simp [RamFlowDemand.value,DirectedFlowLP.divergence]
  · have hst':s.val ≠ t.val:=fun h => hst (Fin.ext h)
    by_cases hus:u=s
    · subst u
      have hst'':¬s=t:=hst
      simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst']
    · have hus':u.val ≠ s.val:=fun h => hus (Fin.ext h)
      by_cases hut:u=t
      · subst u; simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst',hus,hus']
      · have hut':u.val ≠ t.val:=fun h => hut (Fin.ext h)
        simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst',hus,hus',hut,hut']

theorem command_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (s t u:Fin n) (v:Variable n) (hB:2*M^2+3 < B)
    (hni:2*n+1 < B) (hn2:n*n < B) (hv:(variableIndex n v).val < B)
    (hnum:∀ z, (I.weight z).num≤ M) (hden:∀ z, (I.weight z).den≤ M):
    Spec B (Ready I s t u v) command
      (fun _ τ => FractionOutput (DirectedFlowLP.balanceCoefficient I ((s,t),u) v) τ)
      (36*(M*M).size+124):=by
  have h1:1 < B:=by nlinarith
  have hu:u.val < B:=by have:=u.isLt; omega
  have hs:s.val < B:=by have:=s.isLt; omega
  have ht:t.val < B:=by have:=t.isLt; omega
  have hcommodity:(edgeIndex n (s,t)).val < B:=(edgeIndex n (s,t)).isLt.trans hn2
  rintro σ ⟨hp,hσs,hσt,hσu,hσcommodity,hσj,hσac,hσas,hσat⟩
  cases v with
  | inl v =>
    have hj0:σ.vars "lp.j"=0:=hσj.trans (value_variable v)
    have hcond:(Cond.eq (.var "lp.j") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq_iff]
      exact ⟨0,0,by rw [evalB_var_iff]; simp [hj0]; omega,evalB_lit (by omega),by decide⟩
    have hprod:=RamFlowDemand.command_spec B M (List.ofFn I.weight) s.val t.val u.val
      (by simp) (by simp) hu hB
      (by have:=s.isLt; omega) (by have:=t.isLt; omega)
      (by simpa using hnum s) (by simpa using hden s) (by simpa using hnum t) (by simpa using hden t)
    obtain ⟨τ,hr,hpost⟩:=hprod σ ⟨hp,hσs,hσt,hσu⟩
    have hdprod:(I.weight s).den*(I.weight t).den≤ M*M:=Nat.mul_le_mul (hden s) (hden t)
    have hsz:=Nat.size_le_size hdprod
    refine ⟨τ,(Run.ite_true hcond hr).mono (by simp only [Cond.size,Expr.size,List.getElem_ofFn,Fin.eta]; omega), ?_⟩
    simpa only [List.getElem_ofFn,demand_eq,DirectedFlowLP.balanceCoefficient] using hpost
  | inr a =>
    rcases a with ⟨⟨s',t'⟩,⟨u',v'⟩⟩
    have hjpos:(variableIndex n (.inr ((s',t'),(u',v')))).val ≠ 0:=by rw [arc_variable]; omega
    have hcond:(Cond.eq (.var "lp.j") (.lit 0)).evalB B σ=some false:=by
      rw [evalB_condEq_iff]
      exact ⟨(variableIndex n (.inr ((s',t'),(u',v')))).val,0,
        by rw [evalB_var_iff]; exact ⟨hσj.symm,hσj ▸ hv⟩,evalB_lit (by omega),by simp [hjpos]⟩
    have hac:σ.vars "lp.arcCommodity"=(edgeIndex n (s',t')).val:=by rwa [arc_div] at hσac
    have has:σ.vars "lp.arcSource"=u'.val:=by rwa [arc_mod,edge_div] at hσas
    have hat:σ.vars "lp.arcTarget"=v'.val:=by rwa [arc_mod,edge_mod] at hσat
    obtain ⟨τ,hr,hpost⟩:=RamFlowUnits.arc_spec B (edgeIndex n (s',t')).val
      (edgeIndex n (s,t)).val u'.val v'.val u.val h1 ((edgeIndex n (s',t')).isLt.trans hn2)
      hcommodity (by have:=u'.isLt; omega) (by have:=v'.isLt; omega) hu σ
        ⟨hac,hσcommodity,has,hat,hσu⟩
    refine ⟨τ,(Run.ite_false hcond hr).mono (by simp [Cond.size,Expr.size]), ?_⟩
    simpa only [RamFlowUnits.arcValue,DirectedFlowLP.balanceCoefficient,Fin.val_inj,
      (edgeIndex n).apply_eq_iff_eq] using hpost

end Lax455465Proofs.RamFlowBalance

end

section

namespace Lax455465Proofs.RamFlowIndices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def column:Com:=.seq (.assign "lp.offset" (.sub (.var "lp.j") (.lit 1)))
  (.seq (.assign "lp.arcCommodity" (.div (.var "lp.offset") (.var "lp.n2")))
    (.seq (.assign "lp.arc" (.sub (.var "lp.offset")
      (.mul (.var "lp.arcCommodity") (.var "lp.n2"))))
      (.seq (.assign "lp.arcSource" (.div (.var "lp.arc") (.var "lp.n")))
        (.assign "lp.arcTarget" (.sub (.var "lp.arc")
          (.mul (.var "lp.arcSource") (.var "lp.n")))))))

theorem column_spec (B n n2 j:ℕ) (h1:1 < B) (hn:n < B) (hn2:n2 < B) (hj:j < B):
    Spec B (fun σ => σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n2∧ σ.vars "lp.j"=j) column
      (fun _ τ => τ.vars "lp.arcCommodity"=(j-1)/n2∧ τ.vars "lp.arc"=(j-1)%n2∧
        τ.vars "lp.arcSource"=((j-1)%n2)/n∧ τ.vars "lp.arcTarget"=((j-1)%n2)%n) 24:=by
  have ho:j-1 < B:=(Nat.sub_le _ _).trans_lt hj
  have hac:(j-1)/n2 < B:=(Nat.div_le_self _ _).trans_lt ho
  have hacp:(j-1)/n2*n2 < B:=(Nat.div_mul_le_self _ _).trans_lt ho
  have har:(j-1)%n2 < B:=(Nat.mod_le _ _).trans_lt ho
  have has:((j-1)%n2)/n < B:=(Nat.div_le_self _ _).trans_lt har
  have hasp:((j-1)%n2)/n*n < B:=(Nat.div_mul_le_self _ _).trans_lt har
  have hat:((j-1)%n2)%n < B:=(Nat.mod_le _ _).trans_lt har
  rintro σ ⟨hσn,hσn2,hσj⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c2:Nat:=c1 j ((1:Nat)); let c3:Nat:=c0 c2 n2; let c4:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c5:Nat:=c4 c2 n2; let c6:Nat:=c0 c5 n; let c7:Nat:=c4 c5 n; let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.arcCommodity") c3) (And (@Eq Nat (Env.vars τ "lp.arc") c5) (And (@Eq Nat (Env.vars τ "lp.arcSource") c6) (@Eq Nat (Env.vars τ "lp.arcTarget") c7)))) σ; let c9:Nat:=c1 (Env.vars σ "lp.j") ((1:Nat)); let c10:Env:=Env.setVar σ "lp.offset" c9; let c11:String→ Nat:=Env.vars c10; let c12:Nat:=c11 "lp.offset"; let c13:Nat:=c11 "lp.n2"; let c14:Nat:=c0 c12 c13; let c15:Env:=Env.setVar c10 "lp.arcCommodity" c14; let c16:String→ Nat:=Env.vars c15; let c17:Nat:=c16 "lp.offset"; let c18:Nat→ Nat→ Nat:=Nat.mul; let c19:Nat:=c16 "lp.arcCommodity"; let c20:Nat:=c16 "lp.n2"; let c21:Nat:=c18 c19 c20; let c22:Nat:=c1 c17 c21; let c23:Env:=Env.setVar c15 "lp.arc" c22; let c24:String→ Nat:=Env.vars c23; let c25:Nat:=c24 "lp.arc"; let c26:Nat:=c24 "lp.n"; let c27:Nat:=c0 c25 c26; let c28:Env:=Env.setVar c23 "lp.arcSource" c27; let c29:String→ Nat:=Env.vars c28; let c30:Nat:=c29 "lp.arc"; let c31:Nat:=c29 "lp.arcSource"; let c32:Nat:=c29 "lp.n"; let c33:Nat:=c18 c31 c32; let c34:Nat:=c1 c30 c33; let c35:Env:=Env.setVar c28 "lp.arcTarget" c34; let c36:Nat→ Nat→ Nat:=Nat.add; let c37:Nat→ Nat:=c36 ((1:Nat)); let c38:Expr:=Expr.sub (Expr.var "lp.j") (Expr.lit ((1:Nat))); let c39:Nat:=c37 (Expr.size c38); let c40:Nat:=c37 (Expr.size (Expr.div (Expr.var "lp.offset") (Expr.var "lp.n2"))); let c41:Expr:=Expr.sub (Expr.var "lp.offset") (Expr.mul (Expr.var "lp.arcCommodity") (Expr.var "lp.n2")); let c42:Nat:=c37 (Expr.size c41); let c43:Nat:=c37 (Expr.size (Expr.div (Expr.var "lp.arc") (Expr.var "lp.n"))); let c44:Expr:=Expr.sub (Expr.var "lp.arc") (Expr.mul (Expr.var "lp.arcSource") (Expr.var "lp.n")); let c45:Nat:=c37 (Expr.size c44); let c46:Nat:=c36 c43 c45; let c47:Nat:=c36 c42 c46; let c48:Nat:=c36 c40 c47; let c49:Com:=Com.assign "lp.arcCommodity" (Expr.div (Expr.var "lp.offset") (Expr.var "lp.n2")); let c50:Com:=Com.assign "lp.arc" c41; let c51:Com:=Com.assign "lp.arcSource" (Expr.div (Expr.var "lp.arc") (Expr.var "lp.n")); let c52:Com:=Com.assign "lp.arcTarget" c44; let c53:Com:=Com.seq c51 c52; let c54:Com:=Com.seq c50 c53; let c55:String→ Nat:=Env.vars c35; @Exists.intro Env (fun (σ':Env) => And (Run B column σ σ' ((24:Nat))) (c8 σ')) c35 (@And.intro (Run B column σ c35 ((24:Nat))) (c8 c35) (RunStep.mono B column σ c35 (c36 c39 c48) ((24:Nat)) (RunStep.seq B (Com.assign "lp.offset" c38) (Com.seq c49 c54) σ c10 c35 c39 c48 (RunStep.assign B σ "lp.offset" c38 c9 (RunStep.eval_sub B σ (Expr.var "lp.j") (Expr.lit ((1:Nat))) (Env.vars σ "lp.j") ((1:Nat)) (RunStep.eval_var B σ "lp.j" (?nAX_g5876_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g5876_0_0_1))) (RunStep.seq B c49 c54 c10 c15 c35 c40 c47 (RunStep.assign B c10 "lp.arcCommodity" (Expr.div (Expr.var "lp.offset") (Expr.var "lp.n2")) c14 (RunStep.eval_div B c10 (Expr.var "lp.offset") (Expr.var "lp.n2") c12 c13 (RunStep.eval_var B c10 "lp.offset" (?nAX_g5876_0_0_2)) (RunStep.eval_var B c10 "lp.n2" (?nAX_g5876_0_0_3)) ?_)) (RunStep.seq B c50 c53 c15 c23 c35 c42 c46 (RunStep.assign B c15 "lp.arc" c41 c22 (RunStep.eval_sub B c15 (Expr.var "lp.offset") (Expr.mul (Expr.var "lp.arcCommodity") (Expr.var "lp.n2")) c17 c21 (RunStep.eval_var B c15 "lp.offset" (?nAX_g5876_0_0_4)) (RunStep.eval_mul B c15 (Expr.var "lp.arcCommodity") (Expr.var "lp.n2") c19 c20 (RunStep.eval_var B c15 "lp.arcCommodity" ?_) (RunStep.eval_var B c15 "lp.n2" (?nAX_g5876_0_0_5)) ?_) (?nAX_g5876_0_0_6))) (RunStep.seq B c51 c52 c23 c28 c35 c43 c45 (RunStep.assign B c23 "lp.arcSource" (Expr.div (Expr.var "lp.arc") (Expr.var "lp.n")) c27 (RunStep.eval_div B c23 (Expr.var "lp.arc") (Expr.var "lp.n") c25 c26 (RunStep.eval_var B c23 "lp.arc" (?nAX_g5876_0_0_7)) (RunStep.eval_var B c23 "lp.n" (?nAX_g5876_0_0_8)) ?_)) (RunStep.assign B c28 "lp.arcTarget" c44 c34 (RunStep.eval_sub B c28 (Expr.var "lp.arc") (Expr.mul (Expr.var "lp.arcSource") (Expr.var "lp.n")) c30 c33 (RunStep.eval_var B c28 "lp.arc" (?nAX_g5876_0_0_9)) (RunStep.eval_mul B c28 (Expr.var "lp.arcSource") (Expr.var "lp.n") c31 c32 (RunStep.eval_var B c28 "lp.arcSource" ?_) (RunStep.eval_var B c28 "lp.n" (?nAX_g5876_0_0_10)) ?_) (?nAX_g5876_0_0_11))))))) (?nAX_g5876_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5876_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5876_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def row:Com:=.seq (.assign "lp.balanceOffset" (.sub (.var "lp.i") (.var "lp.n2")))
  (.seq (.assign "lp.sign" (.div (.var "lp.balanceOffset") (.var "lp.n3")))
    (.seq (.assign "lp.balance" (.sub (.var "lp.balanceOffset") (.mul (.var "lp.sign") (.var "lp.n3"))))
      (.seq (.assign "lp.commodity" (.div (.var "lp.balance") (.var "lp.n")))
        (.seq (.assign "lp.u" (.sub (.var "lp.balance") (.mul (.var "lp.commodity") (.var "lp.n"))))
          (.seq (.assign "lp.s" (.div (.var "lp.commodity") (.var "lp.n")))
            (.assign "lp.t" (.sub (.var "lp.commodity") (.mul (.var "lp.s") (.var "lp.n")))))))))

theorem row_spec (B n n2 n3 i:ℕ) (hn:n < B) (hn2:n2 < B) (hn3:n3 < B) (hi:i < B):
    Spec B (fun σ => σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n2∧ σ.vars "lp.n3"=n3∧
      σ.vars "lp.i"=i) row
      (fun _ τ => τ.vars "lp.sign"=(i-n2)/n3∧ τ.vars "lp.balance"=(i-n2)%n3∧
        τ.vars "lp.commodity"=((i-n2)%n3)/n∧ τ.vars "lp.u"=((i-n2)%n3)%n∧
        τ.vars "lp.s"=(((i-n2)%n3)/n)/n∧ τ.vars "lp.t"=(((i-n2)%n3)/n)%n) 34:=by
  have ho:i-n2 < B:=(Nat.sub_le _ _).trans_lt hi
  have hf:(i-n2)/n3 < B:=(Nat.div_le_self _ _).trans_lt ho
  have hfp:(i-n2)/n3*n3 < B:=(Nat.div_mul_le_self _ _).trans_lt ho
  have hb:(i-n2)%n3 < B:=(Nat.mod_le _ _).trans_lt ho
  have hc:((i-n2)%n3)/n < B:=(Nat.div_le_self _ _).trans_lt hb
  have hcp:((i-n2)%n3)/n*n < B:=(Nat.div_mul_le_self _ _).trans_lt hb
  have hu:((i-n2)%n3)%n < B:=(Nat.mod_le _ _).trans_lt hb
  have hs:(((i-n2)%n3)/n)/n < B:=(Nat.div_le_self _ _).trans_lt hc
  have hsp:(((i-n2)%n3)/n)/n*n < B:=(Nat.div_mul_le_self _ _).trans_lt hc
  have ht:(((i-n2)%n3)/n)%n < B:=(Nat.mod_le _ _).trans_lt hc
  rintro σ ⟨hσn,hσn2,hσn3,hσi⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c2:Nat:=c1 i n2; let c3:Nat:=c0 c2 n3; let c4:Nat→ Nat→ Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod); let c5:Nat:=c4 c2 n3; let c6:Nat:=c0 c5 n; let c7:Nat:=c4 c5 n; let c8:Nat:=c0 c6 n; let c9:Nat:=c4 c6 n; let c10:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.sign") c3) (And (@Eq Nat (Env.vars τ "lp.balance") c5) (And (@Eq Nat (Env.vars τ "lp.commodity") c6) (And (@Eq Nat (Env.vars τ "lp.u") c7) (And (@Eq Nat (Env.vars τ "lp.s") c8) (@Eq Nat (Env.vars τ "lp.t") c9)))))) σ; let c11:Nat:=c1 (Env.vars σ "lp.i") (Env.vars σ "lp.n2"); let c12:Env:=Env.setVar σ "lp.balanceOffset" c11; let c13:String→ Nat:=Env.vars c12; let c14:Nat:=c13 "lp.balanceOffset"; let c15:Nat:=c13 "lp.n3"; let c16:Nat:=c0 c14 c15; let c17:Env:=Env.setVar c12 "lp.sign" c16; let c18:String→ Nat:=Env.vars c17; let c19:Nat:=c18 "lp.balanceOffset"; let c20:Nat→ Nat→ Nat:=Nat.mul; let c21:Nat:=c18 "lp.sign"; let c22:Nat:=c18 "lp.n3"; let c23:Nat:=c20 c21 c22; let c24:Nat:=c1 c19 c23; let c25:Env:=Env.setVar c17 "lp.balance" c24; let c26:String→ Nat:=Env.vars c25; let c27:Nat:=c26 "lp.balance"; let c28:Nat:=c26 "lp.n"; let c29:Nat:=c0 c27 c28; let c30:Env:=Env.setVar c25 "lp.commodity" c29; let c31:String→ Nat:=Env.vars c30; let c32:Nat:=c31 "lp.balance"; let c33:Nat:=c31 "lp.commodity"; let c34:Nat:=c31 "lp.n"; let c35:Nat:=c20 c33 c34; let c36:Nat:=c1 c32 c35; let c37:Env:=Env.setVar c30 "lp.u" c36; let c38:String→ Nat:=Env.vars c37; let c39:Nat:=c38 "lp.commodity"; let c40:Nat:=c38 "lp.n"; let c41:Nat:=c0 c39 c40; let c42:Env:=Env.setVar c37 "lp.s" c41; let c43:String→ Nat:=Env.vars c42; let c44:Nat:=c43 "lp.commodity"; let c45:Nat:=c43 "lp.s"; let c46:Nat:=c43 "lp.n"; let c47:Nat:=c20 c45 c46; let c48:Nat:=c1 c44 c47; let c49:Env:=Env.setVar c42 "lp.t" c48; let c50:Nat→ Nat→ Nat:=Nat.add; let c51:Nat→ Nat:=c50 ((1:Nat)); let c52:Nat:=c51 (Expr.size (Expr.sub (Expr.var "lp.i") (Expr.var "lp.n2"))); let c53:Nat:=c51 (Expr.size (Expr.div (Expr.var "lp.balanceOffset") (Expr.var "lp.n3"))); let c54:Expr:=Expr.sub (Expr.var "lp.balanceOffset") (Expr.mul (Expr.var "lp.sign") (Expr.var "lp.n3")); let c55:Nat:=c51 (Expr.size c54); let c56:Nat:=c51 (Expr.size (Expr.div (Expr.var "lp.balance") (Expr.var "lp.n"))); let c57:Expr:=Expr.sub (Expr.var "lp.balance") (Expr.mul (Expr.var "lp.commodity") (Expr.var "lp.n")); let c58:Nat:=c51 (Expr.size c57); let c59:Nat:=c51 (Expr.size (Expr.div (Expr.var "lp.commodity") (Expr.var "lp.n"))); let c60:Expr:=Expr.sub (Expr.var "lp.commodity") (Expr.mul (Expr.var "lp.s") (Expr.var "lp.n")); let c61:Nat:=c51 (Expr.size c60); let c62:Nat:=c50 c59 c61; let c63:Nat:=c50 c58 c62; let c64:Nat:=c50 c56 c63; let c65:Nat:=c50 c55 c64; let c66:Nat:=c50 c53 c65; let c67:Com:=Com.assign "lp.sign" (Expr.div (Expr.var "lp.balanceOffset") (Expr.var "lp.n3")); let c68:Com:=Com.assign "lp.balance" c54; let c69:Com:=Com.assign "lp.commodity" (Expr.div (Expr.var "lp.balance") (Expr.var "lp.n")); let c70:Com:=Com.assign "lp.u" c57; let c71:Com:=Com.assign "lp.s" (Expr.div (Expr.var "lp.commodity") (Expr.var "lp.n")); let c72:Com:=Com.assign "lp.t" c60; let c73:Com:=Com.seq c71 c72; let c74:Com:=Com.seq c70 c73; let c75:Com:=Com.seq c69 c74; let c76:Com:=Com.seq c68 c75; let c77:String→ Nat:=Env.vars c49; @Exists.intro Env (fun (σ':Env) => And (Run B row σ σ' ((34:Nat))) (c10 σ')) c49 (@And.intro (Run B row σ c49 ((34:Nat))) (c10 c49) (RunStep.mono B row σ c49 (c50 c52 c66) ((34:Nat)) (RunStep.seq B (Com.assign "lp.balanceOffset" (Expr.sub (Expr.var "lp.i") (Expr.var "lp.n2"))) (Com.seq c67 c76) σ c12 c49 c52 c66 (RunStep.assign B σ "lp.balanceOffset" (Expr.sub (Expr.var "lp.i") (Expr.var "lp.n2")) c11 (RunStep.eval_sub B σ (Expr.var "lp.i") (Expr.var "lp.n2") (Env.vars σ "lp.i") (Env.vars σ "lp.n2") (RunStep.eval_var B σ "lp.i" (?nAX_g5878_0_0_0)) (RunStep.eval_var B σ "lp.n2" (?nAX_g5878_0_0_1)) (?nAX_g5878_0_0_2))) (RunStep.seq B c67 c76 c12 c17 c49 c53 c65 (RunStep.assign B c12 "lp.sign" (Expr.div (Expr.var "lp.balanceOffset") (Expr.var "lp.n3")) c16 (RunStep.eval_div B c12 (Expr.var "lp.balanceOffset") (Expr.var "lp.n3") c14 c15 (RunStep.eval_var B c12 "lp.balanceOffset" (?nAX_g5878_0_0_3)) (RunStep.eval_var B c12 "lp.n3" (?nAX_g5878_0_0_4)) ?_)) (RunStep.seq B c68 c75 c17 c25 c49 c55 c64 (RunStep.assign B c17 "lp.balance" c54 c24 (RunStep.eval_sub B c17 (Expr.var "lp.balanceOffset") (Expr.mul (Expr.var "lp.sign") (Expr.var "lp.n3")) c19 c23 (RunStep.eval_var B c17 "lp.balanceOffset" (?nAX_g5878_0_0_5)) (RunStep.eval_mul B c17 (Expr.var "lp.sign") (Expr.var "lp.n3") c21 c22 (RunStep.eval_var B c17 "lp.sign" ?_) (RunStep.eval_var B c17 "lp.n3" (?nAX_g5878_0_0_6)) ?_) (?nAX_g5878_0_0_7))) (RunStep.seq B c69 c74 c25 c30 c49 c56 c63 (RunStep.assign B c25 "lp.commodity" (Expr.div (Expr.var "lp.balance") (Expr.var "lp.n")) c29 (RunStep.eval_div B c25 (Expr.var "lp.balance") (Expr.var "lp.n") c27 c28 (RunStep.eval_var B c25 "lp.balance" (?nAX_g5878_0_0_8)) (RunStep.eval_var B c25 "lp.n" (?nAX_g5878_0_0_9)) ?_)) (RunStep.seq B c70 c73 c30 c37 c49 c58 c62 (RunStep.assign B c30 "lp.u" c57 c36 (RunStep.eval_sub B c30 (Expr.var "lp.balance") (Expr.mul (Expr.var "lp.commodity") (Expr.var "lp.n")) c32 c35 (RunStep.eval_var B c30 "lp.balance" (?nAX_g5878_0_0_10)) (RunStep.eval_mul B c30 (Expr.var "lp.commodity") (Expr.var "lp.n") c33 c34 (RunStep.eval_var B c30 "lp.commodity" ?_) (RunStep.eval_var B c30 "lp.n" (?nAX_g5878_0_0_11)) ?_) (?nAX_g5878_0_0_12))) (RunStep.seq B c71 c72 c37 c42 c49 c59 c61 (RunStep.assign B c37 "lp.s" (Expr.div (Expr.var "lp.commodity") (Expr.var "lp.n")) c41 (RunStep.eval_div B c37 (Expr.var "lp.commodity") (Expr.var "lp.n") c39 c40 (RunStep.eval_var B c37 "lp.commodity" ?_) (RunStep.eval_var B c37 "lp.n" (?nAX_g5878_0_0_13)) ?_)) (RunStep.assign B c42 "lp.t" c60 c48 (RunStep.eval_sub B c42 (Expr.var "lp.commodity") (Expr.mul (Expr.var "lp.s") (Expr.var "lp.n")) c44 c47 (RunStep.eval_var B c42 "lp.commodity" ?_) (RunStep.eval_mul B c42 (Expr.var "lp.s") (Expr.var "lp.n") c45 c46 (RunStep.eval_var B c42 "lp.s" ?_) (RunStep.eval_var B c42 "lp.n" (?nAX_g5878_0_0_14)) ?_) ?_)))))))) (?nAX_g5878_0_0_15)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5878_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5878_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

end Lax455465Proofs.RamFlowIndices

end

section

namespace Lax455465Proofs.RamFlowCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP FlowLpIndices
open RamFlowContext
open scoped NNRat

def prepare:Com:=.seq RamFlowIndices.column RamFlowIndices.row

def Prepared (n i j:ℕ) (weights:List ℚ≥0) (σ:Env):Prop:=
  Context n i j weights σ∧
    σ.vars "lp.arcCommodity"=(j-1)/(n*n)∧ σ.vars "lp.arc"=(j-1)%(n*n)∧
    σ.vars "lp.arcSource"=((j-1)%(n*n))/n∧ σ.vars "lp.arcTarget"=((j-1)%(n*n))%n∧
    σ.vars "lp.sign"=(i-n*n)/((n*n)*n)∧ σ.vars "lp.balance"=(i-n*n)%((n*n)*n)∧
    σ.vars "lp.commodity"=((i-n*n)%((n*n)*n))/n∧ σ.vars "lp.u"=((i-n*n)%((n*n)*n))%n∧
    σ.vars "lp.s"=(((i-n*n)%((n*n)*n))/n)/n∧ σ.vars "lp.t"=(((i-n*n)%((n*n)*n))/n)%n

theorem prepare_spec (B n i j:ℕ) (weights:List ℚ≥0) (h1:1 < B)
    (hn:n < B) (hn2:n*n < B) (hn3:(n*n)*n < B) (hi:i < B) (hj:j < B):
    Spec B (Context n i j weights) prepare (fun _ τ => Prepared n i j weights τ) 58:=by
  rintro σ hctx
  obtain ⟨ν,hcol,hcolPost⟩:=RamFlowIndices.column_spec B n (n*n) j h1 hn hn2 hj σ
    ⟨hctx.1,hctx.2.1,hctx.2.2.2.2.1⟩
  have hctxν:=frame hcol n i j weights hctx (by decide) (by decide)
  obtain ⟨τ,hrow,hrowPost⟩:=RamFlowIndices.row_spec B n (n*n) ((n*n)*n) i hn hn2 hn3 hi ν
    ⟨hctxν.1,hctxν.2.1,hctxν.2.2.1,hctxν.2.2.2.1⟩
  have hctxτ:=frame hrow n i j weights hctxν (by decide) (by decide)
  have hca:=(hrow.frame_var "lp.arcCommodity" (by decide)).trans hcolPost.1
  have hcar:=(hrow.frame_var "lp.arc" (by decide)).trans hcolPost.2.1
  have hcas:=(hrow.frame_var "lp.arcSource" (by decide)).trans hcolPost.2.2.1
  have hcat:=(hrow.frame_var "lp.arcTarget" (by decide)).trans hcolPost.2.2.2
  exact ⟨τ,hcol.seq hrow,hctxτ,hca,hcar,hcas,hcat,hrowPost⟩

def command:Com:=.seq prepare (.ite (.lt (.var "lp.i") (.var "lp.n2")) RamFlowUnits.capacity
  (.seq RamFlowBalance.command RamFlowUnits.rowSign))

theorem command_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (r:Row n) (v:Variable n) (hB:2*M^2+3 < B)
    (hni:2*n+1 < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:(rowIndex n r).val < B) (hv:(variableIndex n v).val < B)
    (hnum:∀ z, (I.weight z).num≤ M) (hden:∀ z, (I.weight z).den≤ M):
    Spec B (Context n (rowIndex n r).val (variableIndex n v).val (List.ofFn I.weight)) command
      (fun _ τ => FractionOutput (DirectedFlowLP.coefficient I r v) τ) (36*(M*M).size+194):=by
  have h1:1 < B:=by nlinarith
  have hn:n < B:=by omega
  rintro σ hctx
  obtain ⟨ν,hprep,hprepared⟩:=prepare_spec B n (rowIndex n r).val (variableIndex n v).val
    (List.ofFn I.weight) h1 hn hn2 hn3 hr hv σ hctx
  have hctxν:=hprepared.1
  rcases hprepared.2 with ⟨hac,harc,has,hat,hflag,hbal,hcom,hu,hs,ht⟩
  cases r with
  | inl e =>
    rcases e with ⟨a,b⟩
    have hi:(rowIndex n (.inl (a,b))).val < n*n:=by
      rw [_root_.Lax455465Proofs.FlowLpIndices.capacity_row,←edge_value]; exact (edgeIndex n (a,b)).isLt
    have hcond:(Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B ν=some true:=by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inl (a,b))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.2.2.1.symm,hctxν.2.2.2.1 ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.1.symm,hctxν.2.1 ▸ hn2⟩,by simp [hi]⟩
    have hcarB:((variableIndex n v).val-1)%(n*n) < B:=
      (Nat.mod_le _ _).trans_lt ((Nat.sub_le _ _).trans_lt hv)
    obtain ⟨τ,hcap,hpost⟩:=RamFlowUnits.capacity_spec B (variableIndex n v).val
      (((variableIndex n v).val-1)%(n*n)) (rowIndex n (.inl (a,b))).val h1 hv hcarB hr ν
        ⟨hctxν.2.2.2.2.1,harc,hctxν.2.2.2.1⟩
    refine ⟨τ,(hprep.seq (Run.ite_true hcond hcap)).mono (by simp [Cond.size,Expr.size]), ?_⟩
    cases v with
    | inl v => simpa only [RamFlowUnits.capacityValue,value_variable,if_true,DirectedFlowLP.coefficient] using hpost
    | inr ca =>
      rcases ca with ⟨⟨s,t⟩,⟨u,v⟩⟩
      have hcol:(variableIndex n (.inr ((s,t),(u,v)))).val ≠ 0:=by rw [arc_variable]; omega
      simpa only [RamFlowUnits.capacityValue,if_neg hcol,arc_mod,_root_.Lax455465Proofs.FlowLpIndices.capacity_row,←edge_value,
        edge_equal,DirectedFlowLP.coefficient] using hpost
  | inr b =>
    rcases b with ⟨flag,⟨⟨s,t⟩,u⟩⟩
    have hi:¬(rowIndex n (.inr (flag,((s,t),u)))).val < n*n:=by rw [_root_.Lax455465Proofs.FlowLpIndices.balance_row]; omega
    have hcond:(Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B ν=some false:=by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inr (flag,((s,t),u)))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.2.2.1.symm,hctxν.2.2.2.1 ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hctxν.2.1.symm,hctxν.2.1 ▸ hn2⟩,by simp [hi]⟩
    have hs':ν.vars "lp.s"=s.val:=by rwa [row_mod,balance_div,edge_div] at hs
    have ht':ν.vars "lp.t"=t.val:=by rwa [row_mod,balance_div,edge_mod] at ht
    have hu':ν.vars "lp.u"=u.val:=by rwa [row_mod,balance_mod] at hu
    have hc':ν.vars "lp.commodity"=(edgeIndex n (s,t)).val:=by rwa [row_mod,balance_div] at hcom
    have hf':ν.vars "lp.sign"=flag.val:=by rwa [row_div] at hflag
    obtain ⟨μ,hbase,hbasePost⟩:=RamFlowBalance.command_spec B M I s t u v hB hni hn2 hv hnum hden ν
      ⟨hctxν.2.2.2.2.2,hs',ht',hu',hc',hctxν.2.2.2.2.1,hac,has,hat⟩
    have hfμ:μ.vars "lp.sign"=flag.val:=(hbase.frame_var "lp.sign" (by decide)).trans hf'
    have hflagB:flag.val < B:=flag.isLt.trans_le (by omega:2≤ B)
    obtain ⟨τ,hsign,hpost⟩:=RamFlowUnits.rowSign_spec B flag.val
      (DirectedFlowLP.balanceCoefficient I ((s,t),u) v) h1 hflagB μ ⟨hbasePost,hfμ⟩
    refine ⟨τ,(hprep.seq (Run.ite_false hcond (hbase.seq hsign))).mono
      (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    have hz:flag.val=0↔ flag=0:=by rw [←Fin.val_inj]; rfl
    simpa only [DirectedFlowLP.coefficient,hz] using hpost

end Lax455465Proofs.RamFlowCoefficient

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

namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

theorem canonical_sign (q:ℚ) (σ:Env) (h:FractionOutput q σ):
    (if σ.vars "rat.n"=0 then 0 else σ.vars "rat.s")=if q.num < 0 then 1 else 0:=by
  by_cases hn:σ.vars "rat.n"=0
  · have hnum:q.num=0:=by
      have he:q.num.natAbs=0:=h.2.1.symm.trans hn
      exact Int.natAbs_eq_zero.mp he
    simp [hn,hnum]
  · have hs:σ.vars "rat.s"=0∨ σ.vars "rat.s"=1:=by have:=h.2.2.2; omega
    rcases hs with hs | hs
    · have hnonneg:0≤ q:=by
        rw [← h.1]
        simp only [fractionValue,hs,show ¬(0:ℕ)=1 by decide,if_false]
        positivity
      have hnum:=Rat.num_nonneg.mpr hnonneg
      simp [hn,hs,not_lt.mpr hnum]
    · have hnpos:(0:ℚ) < σ.vars "rat.n" :=by exact_mod_cast (show 0 < σ.vars "rat.n" by omega)
      have hdpos:(0:ℚ) < σ.vars "rat.d" :=by
        rw [h.2.2.1]
        exact_mod_cast q.den_pos
      have hneg:q < 0:=by
        rw [← h.1]
        simp only [fractionValue,hs,if_true]
        exact div_neg_of_neg_of_pos (by linarith) hdpos
      have hnum:q.num < 0:=by
        by_contra hnum
        have hq:=Rat.num_nonneg.mp (show 0≤ q.num by omega)
        linarith
      simp [hn,hs,hnum]

theorem sign_spec (B:ℕ) (q:ℚ) (h1:1 < B) (hn:q.num.natAbs < B):
    Spec B (FractionOutput q) sign
      (fun _ τ => τ.vars "emit.s"=if q.num < 0 then 1 else 0) 6:=by
  intro σ h
  have hvalue:=h.2.1
  have hsign:=h.2.2.2
  have hcanonical:=canonical_sign q σ h
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "rat.n") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@LT.lt Int Int.instLTInt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (Int.decLt (Rat.num q) (@OfNat.ofNat Int (nat_lit 0) (@instOfNat (nat_lit 0)))) ((1:Nat)) ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "emit.s") c2) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B sign σ σ' ((6:Nat))) (c3 σ'); let c5:Env:=Env.setVar σ "emit.s" ((0:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Cond:=Cond.eq (Expr.var "rat.n") (Expr.lit ((0:Nat))); let c9:Nat→ Nat:=c6 (c7 (Cond.size c8)); let c10:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c11:Com:=Com.assign "emit.s" (Expr.lit ((0:Nat))); let c12:Nat:=c7 (Expr.size (Expr.var "rat.s")); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c5 (@And.intro (Run B sign σ c5 ((6:Nat))) (c3 c5) (RunStep.mono B sign σ c5 (c9 c10) ((6:Nat)) (RunStep.ite_true B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ c5 c10 (RunStep.cond_eq_true B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_1)) hcase) (RunStep.assign B σ "emit.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_2)))) (?nAX_g5889_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (@And.intro (Run B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) ((6:Nat))) (c3 (Env.setVar σ "emit.s" (Env.vars σ "rat.s"))) (RunStep.mono B sign σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) (c9 c12) ((6:Nat)) (RunStep.ite_false B c8 c11 (Com.assign "emit.s" (Expr.var "rat.s")) σ (Env.setVar σ "emit.s" (Env.vars σ "rat.s")) c12 (RunStep.cond_eq_false B σ (Expr.var "rat.n") (Expr.lit ((0:Nat))) (Env.vars σ "rat.n") ((0:Nat)) (RunStep.eval_var B σ "rat.n" (?nAX_g5889_0_0_4)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5889_0_0_5)) hcase) (RunStep.assign B σ "emit.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" (?nAX_g5889_0_0_6)))) (?nAX_g5889_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5889_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5889_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem emit_spec (B:ℕ) (q:ℚ) (words:List ℕ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hlen:words.length + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ Prefix words "lp.word" σ∧
      σ.vars "lp.position"=words.length∧ words.length + 2 < (σ.arrs "lp.word").length) emit
      (fun _ τ => Prefix (words ++ Lax109476.RationalEncoding.encodeRational q) "lp.word" τ∧
        τ.vars "lp.position"=words.length + 3) 27:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  let tag:=if q.num < 0 then 1 else 0
  have htag:tag < B:=by dsimp only [tag]; split_ifs <;> omega
  obtain ⟨ν,hsign,htagν⟩:=sign_spec B q h1 hn σ hf
  have hnumν:=(hsign.frame_var "rat.n" (by simp [sign,Com.wvars])).trans hf.2.1
  have hdenν:=(hsign.frame_var "rat.d" (by simp [sign,Com.wvars])).trans hf.2.2.1
  have hposν:=(hsign.frame_var "lp.position" (by simp [sign,Com.wvars])).trans hpos
  have hpν:Prefix words "lp.word" ν:=by
    simpa only [Prefix,hsign.frame_arr "lp.word" (by simp [sign,Com.warrs])] using hp
  have hroomν:words.length + 2 < (ν.arrs "lp.word").length:=by
    rwa [RamFrames.run_array_length hsign "lp.word"]
  have hnum:=RamFrames.keep_scalar (RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" words tag (.var "emit.s") h1 (by omega))
    "rat.n" q.num.natAbs (by simp [RamWordBuffer.append,Com.wvars]))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨μ,hfirst,hfirstPost⟩:=hnum ν ⟨⟨⟨hpν,hposν,by omega,
    by rw [evalB_var_iff]; exact ⟨htagν.symm,htagν ▸ htag⟩⟩,hnumν⟩,hdenν⟩
  have hroomμ:(words ++ [tag]).length + 1 < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hfirst "lp.word",List.length_append,List.length_singleton]
    exact hroomν
  have hden:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B "lp.word" "lp.position" (words ++ [tag]) q.num.natAbs (.var "rat.n") h1
      (by simp only [List.length_append,List.length_singleton]; omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars])
  obtain ⟨ρ,hsecond,hsecondPost⟩:=hden μ ⟨⟨hfirstPost.1.1.1,
    by simpa only [List.length_append,List.length_singleton] using hfirstPost.1.1.2,
    by omega,by rw [evalB_var_iff]; exact ⟨hfirstPost.1.2.symm,hfirstPost.1.2 ▸ hn⟩⟩,hfirstPost.2⟩
  have hroomρ:((words ++ [tag]) ++ [q.num.natAbs]).length < (ρ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hsecond "lp.word",List.length_append,List.length_singleton]
    exact hroomμ
  obtain ⟨τ,hthird,hthirdPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position"
    ((words ++ [tag]) ++ [q.num.natAbs]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ρ
    ⟨hsecondPost.1.1,by simpa only [List.length_append,List.length_singleton] using hsecondPost.1.2,
      hroomρ,by rw [evalB_var_iff]; exact ⟨hsecondPost.2.symm,hsecondPost.2 ▸ hd⟩⟩
  refine ⟨τ, (hsign.seq (hfirst.seq (hsecond.seq hthird))).mono (by simp [Expr.size]), ?_⟩
  simpa only [Lax109476.RationalEncoding.encodeRational,tag,List.append_assoc,
    List.cons_append,List.nil_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc]
    using hthirdPost

end Lax455465Proofs.RamFractionEncoding

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

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ) (words:List ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ encode (qs.take (σ.vars index))) "lp.word" σ∧
    σ.vars "lp.position"=words.length+3*σ.vars index∧
    words.length+3*qs.length < (σ.arrs "lp.word").length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+3*qs.length+3 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num.natAbs < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput qs[i] τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:"lp.position" ∉ body.wvars)
    (hbodyArray:"lp.word" ∉ body.warrs)
    (hemitIndex:index∉ RamFractionEncoding.emit.wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B RamFractionEncoding.emit σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ "lp.position"):
    Spec B (fun σ => R σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*qs.length < (σ.arrs "lp.word").length) (command index limit body)
      (fun _ τ => R τ∧ Prefix (words ++ encode qs) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*qs.length) ((K+35)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs words τ∧ τ.vars index=σ.vars index+1)
      (K+31):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ encode (qs.take i)).length=words.length+3*i:=by
      simp only [List.length_append,length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars "lp.position"=words.length+3*i:=
      (hproduce.frame_var "lp.position" hbodyPosition).trans hpos
    have hpν:Prefix (words ++ encode (qs.take i)) "lp.word" ν:=by
      simpa only [Prefix,hproduce.frame_arr "lp.word" hbodyArray] using hp
    have hroomν:words.length+3*qs.length < (ν.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hproduce "lp.word"]
    obtain ⟨μ,hemit,hemitted⟩:=RamFractionEncoding.emit_spec B qs[i] (words ++ encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+3*qs.length < (μ.arrs "lp.word").length:=by
      rwa [RamFrames.run_array_length hemit "lp.word"]
    have hpμ:Prefix (words ++ encode (qs.take (i+1))) "lp.word" μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars "lp.position"=words.length+3*(i+1):=by rw [hpLen] at hemitted; omega
    have hnext:i+1 < B:=by omega
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) hnext)
    refine ⟨μ.setVar index (i+1),hproduce.seq (hemit.seq hinc),?_,?_⟩
    · refine ⟨hset μ (i+1) hRμ,by simp; omega,?_,?_,?_⟩
      · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hpμ
      · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true] using hposμ
      · simpa only [arrs_setVar] using hroomμ
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words) qs.length (K+31)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamVectorEncoding

end

section

namespace Lax455465Proofs.FlowLpMatrixList

open Lax109476.LinearProgram

def entry {m n:ℕ} (P:Program ℚ m n) (k:Fin (m*n)):ℚ:=
  P.A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def values {m n:ℕ} (P:Program ℚ m n):List ℚ:=List.ofFn (entry P)

theorem rowIndex_value {m n:ℕ} (k:Fin (m*n)):
    (finProdFinEquiv.symm k).1.val=k.val/n:=rfl

theorem columnIndex_value {m n:ℕ} (k:Fin (m*n)):
    (finProdFinEquiv.symm k).2.val=k.val%n:=rfl

theorem values_eq {m n:ℕ} (P:Program ℚ m n):
    values P=(List.ofFn fun i => List.ofFn (P.A i)).flatten:=by
  unfold values
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij:i.val*n+j.val < m*n:=calc
    _ < (i.val+1)*n:=by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left j.isLt _
    _≤ m*n:=Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr i.isLt)
  have hpair:(⟨i.val*n+j.val,hij⟩:Fin (m*n))=finProdFinEquiv (i,j):=by
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  rw [hpair]
  simp only [entry,Equiv.symm_apply_apply]

end Lax455465Proofs.FlowLpMatrixList

end

section

open scoped NNRat

namespace Lax455465Proofs.InstanceParser

open Lax455465.RationalEncoding Lax455465.ProductNetwork RationalParser

theorem encoded_length (qs:List ℚ≥0):(qs.flatMap encodeRational).length=2 * qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.flatMap_cons,encodeRational,ih]; omega

end Lax455465Proofs.InstanceParser

end

section

namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

theorem height_zero {M:ℕ} (hM:1≤ M):Height M 0:=by simp [Height]; omega

theorem height_one {M:ℕ} (hM:1≤ M):Height M 1:=by simp [Height]; omega

theorem height_neg {M:ℕ} {q:ℚ} (h:Height M q):Height M (-q):=by simpa [Height] using h

theorem height_mono {M N:ℕ} {q:ℚ} (h:Height M q) (hmn:M≤ N):Height N q:=
  ⟨h.1.trans hmn,h.2.trans hmn⟩

theorem height_mul {M N:ℕ} {q r:ℚ} (hq:Height M q) (hr:Height N r):
    Height (M * N) (q * r):=by
  constructor
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1)
  · rw [Rat.mul_den]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hq.2 hr.2)

theorem input_dimension {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    n≤ bitSize (encodeInput kind I):=by
  apply le_trans (b:=(encodeInput kind I).length) _ (WordSize.length_le _)
  simp only [encodeInput,List.length_append,InstanceParser.encoded_length,List.length_ofFn,
    List.length_cons,List.length_nil]
  omega

theorem weight_members {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u:Fin n)
    (x:ℕ) (hx:x∈ encodeRational (I.weight u)):x∈ encodeInput kind I:=by
  simp only [encodeInput,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  exact ⟨I.weight u,List.mem_ofFn.mpr ⟨u,rfl⟩,hx⟩

theorem capacity_members {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u v:Fin n)
    (x:ℕ) (hx:x∈ encodeRational (I.capacity u v)):x∈ encodeInput kind I:=by
  simp only [encodeInput,List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨I.capacity u v, ?_,hx⟩
  apply List.mem_flatten.mpr
  exact ⟨List.ofFn (I.capacity u),List.mem_ofFn.mpr ⟨u,rfl⟩,List.mem_ofFn.mpr ⟨v,rfl⟩⟩

theorem weight_height {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u:Fin n):
    Height (2 ^ bitSize (encodeInput kind I)) (I.weight u:ℚ):=by
  have hn:=WordSize.member_bound (encodeInput kind I) (I.weight u).num
    (weight_members kind I u _ (by simp [encodeRational]))
  have hd:=WordSize.member_bound (encodeInput kind I) (I.weight u).den
    (weight_members kind I u _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le,by simpa only [NNRat.den_coe] using hd.le⟩

theorem capacity_height {n:ℕ} (kind:EdgeKind) (I:RationalInstance n) (u v:Fin n):
    Height (2 ^ bitSize (encodeInput kind I)) (I.capacity u v:ℚ):=by
  have hn:=WordSize.member_bound (encodeInput kind I) (I.capacity u v).num
    (capacity_members kind I u v _ (by simp [encodeRational]))
  have hd:=WordSize.member_bound (encodeInput kind I) (I.capacity u v).den
    (capacity_members kind I u v _ (by simp [encodeRational]))
  exact ⟨by simpa only [NNRat.natAbs_num_coe] using hn.le,by simpa only [NNRat.den_coe] using hd.le⟩

theorem divergence_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (s t u:Fin n):
    Height (M * M) (divergence I s t u):=by
  have hMM:1≤ M * M:=by nlinarith
  have hm:=height_mul (hw s) (hw t)
  by_cases hst:s=t
  · simpa only [divergence,if_pos hst] using height_zero hMM
  by_cases hus:u=s
  · have hut:u ≠ t:=by intro he; exact hst (hus.symm.trans he)
    simpa [divergence,hst,hus,hut,Ne.symm hst] using hm
  · by_cases hut:u=t
    · simpa [divergence,hst,hus,hut,Ne.symm hst] using height_neg hm
    · simpa [divergence,hst,hus,hut,Ne.symm hst] using height_zero hMM

theorem balance_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (b:Balance n) (v:Variable n):
    Height (M * M) (balanceCoefficient I b v):=by
  have hMM:1≤ M * M:=by nlinarith
  cases v with
  | inl _ => exact height_neg (divergence_height I M hM hw _ _ _)
  | inr a =>
    simp only [balanceCoefficient]
    split_ifs <;>
      first | simpa only [sub_self,sub_zero,zero_sub] using height_zero hMM
            | simpa only [sub_self,sub_zero,zero_sub] using height_one hMM
            | simpa only [sub_self,sub_zero,zero_sub] using height_neg (height_one hMM)

theorem coefficient_height {n:ℕ} (I:RationalInstance n) (M:ℕ) (hM:1≤ M)
    (hw:∀ u,Height M (I.weight u:ℚ)) (r:Row n) (v:Variable n):
    Height (M * M) (coefficient I r v):=by
  have hMM:1≤ M * M:=by nlinarith
  cases r with
  | inl e =>
    cases v with
    | inl _ => exact height_zero hMM
    | inr a =>
      simp only [coefficient]
      split_ifs <;> first | exact height_one hMM | exact height_zero hMM
  | inr sb =>
    simp only [coefficient]
    split_ifs
    · exact balance_height I M hM hw _ _
    · exact height_neg (balance_height I M hM hw _ _)

theorem program_heights {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    let M:=2 ^ bitSize (encodeInput kind I)
    (∀ i j,Height (M * M) ((program I).A i j))∧
    (∀ i,Height (M * M) ((program I).b i))∧
    (∀ j,Height (M * M) ((program I).c j)):=by
  dsimp only
  let M:=2 ^ bitSize (encodeInput kind I)
  have hM:1≤ M:=by have:=Nat.two_pow_pos (bitSize (encodeInput kind I)); omega
  have hMM:1≤ M * M:=by nlinarith
  refine ⟨fun i j => coefficient_height I M hM (weight_height kind I) _ _, ?_, ?_⟩
  · intro i
    dsimp only [program,rowBound]
    cases (rowIndex n).symm i with
    | inl e => exact height_mono (capacity_height kind I e.1 e.2) (by nlinarith)
    | inr _ => exact height_zero hMM
  · intro j
    dsimp only [program,objective]
    cases (variableIndex n).symm j with
    | inl _ => exact height_one hMM
    | inr _ => exact height_zero hMM

theorem rational_size (q:ℚ) (K:ℕ) (h:Height (2 ^ K) q):
    bitSize (Lax109476.RationalEncoding.encodeRational q)≤ 2 * K + 6:=by
  have hp:2 ^ K < 2 ^ (K + 1):=by rw [pow_succ]; have:=Nat.two_pow_pos K; omega
  have hn:=Nat.size_le.mpr (h.1.trans_lt hp)
  have hd:=Nat.size_le.mpr (h.2.trans_lt hp)
  simp only [Lax109476.RationalEncoding.encodeRational,WordSize.bitSize_cons,WordSize.bitSize_nil]
  split_ifs <;> simp only [Nat.size_one,Nat.size_zero] <;> omega

private theorem rational_list_size (qs:List ℚ) (K:ℕ)
    (h:∀ q∈ qs,Height (2 ^ K) q):
    bitSize (qs.flatMap Lax109476.RationalEncoding.encodeRational)≤ qs.length * (2 * K + 6):=by
  induction qs with
  | nil => simp [WordSize.bitSize_nil]
  | cons q qs ih =>
    have hq:=rational_size q K (h q List.mem_cons_self)
    have ht:=ih (fun r hr => h r (List.mem_cons_of_mem q hr))
    simp only [List.flatMap_cons,WordSize.bitSize_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem encoded_program_size {m n:ℕ} (P:Lax109476.LinearProgram.Program ℚ m n) (K:ℕ)
    (hA:∀ i j,Height (2 ^ K) (P.A i j)) (hb:∀ i,Height (2 ^ K) (P.b i))
    (hc:∀ j,Height (2 ^ K) (P.c j)):
    bitSize (Lax109476.RationalEncoding.encodeProgram P)≤
      m.size + n.size + 2 + (m * n + m + n) * (2 * K + 6):=by
  have hmat:∀ q∈ (List.ofFn fun i => List.ofFn (P.A i)).flatten,Height (2 ^ K) q:=by
    intro q hq
    obtain ⟨row,hrow,hq⟩:=List.mem_flatten.mp hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hrow
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq
    exact hA i j
  have hmatrix:=rational_list_size _ K hmat
  have hrowlength:(List.ofFn fun i => List.ofFn (P.A i)).flatten.length=m * n:=by
    simp [List.length_flatten,Function.comp_def,List.ofFn_const]
  rw [hrowlength] at hmatrix
  have hbsize:=rational_list_size (List.ofFn P.b) K (by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq; exact hb i)
  have hcsize:=rational_list_size (List.ofFn P.c) K (by
    intro q hq; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq; exact hc j)
  simp only [List.length_ofFn] at hbsize hcsize
  simp only [Lax109476.RationalEncoding.encodeProgram,Lax109476.RationalEncoding.encodeVector,
    WordSize.bitSize_append,WordSize.bitSize_cons,WordSize.bitSize_nil]
  nlinarith

theorem flow_program_size {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
      128 * (bitSize (encodeInput kind I) + 1) ^ 8:=by
  let L:=bitSize (encodeInput kind I)
  let A:=L + 1
  let m:=n * n + 2 * ((n * n) * n)
  let v:=1 + (n * n) * (n * n)
  have hn:n≤ L:=input_dimension kind I
  have hA:1≤ A:=by omega
  have hheights:=program_heights kind I
  have hp:2 ^ L * 2 ^ L=2 ^ (2 * L):=by rw [← pow_add]; congr 1; omega
  have hencoded:=encoded_program_size (program I) (2 * L)
    (fun i j => by simpa only [← hp] using hheights.1 i j)
    (fun i => by simpa only [← hp] using hheights.2.1 i)
    (fun j => by simpa only [← hp] using hheights.2.2 j)
  have hm:m≤ 3 * A ^ 3:=by
    have hs:m≤ 3 * (n + 1) ^ 3:=by dsimp only [m]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by omega:n + 1≤ A) 3))
  have hv:v≤ 2 * A ^ 4:=by
    have hs:v≤ 2 * (n + 1) ^ 4:=by dsimp only [v]; nlinarith
    exact hs.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by omega:n + 1≤ A) 4))
  have hpow3:A ^ 3≤ A ^ 7:=Nat.pow_le_pow_right hA (by decide)
  have hpow4:A ^ 4≤ A ^ 7:=Nat.pow_le_pow_right hA (by decide)
  have hpow7:A ^ 7≤ A ^ 8:=Nat.pow_le_pow_right hA (by decide)
  have hpowpos:1≤ A ^ 7:=by have:=pow_pos (by omega:0 < A) 7; omega
  have hmv:m * v≤ 6 * A ^ 7:=by
    have h:=Nat.mul_le_mul hm hv
    convert h using 1 <;> ring
  have hentries:m * v + m + v≤ 11 * A ^ 7:=by nlinarith
  have hms:m.size≤ m:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hvs:v.size≤ v:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hheader:m.size + v.size + 2≤ 7 * A ^ 7:=by nlinarith
  have hq:2 * (2 * L) + 6≤ 6 * A:=by omega
  have hproduct:=Nat.mul_le_mul hentries hq
  have hprodEq:(11 * A ^ 7) * (6 * A)=66 * A ^ 8:=by ring
  rw [hprodEq] at hproduct
  change bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
    m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6) at hencoded
  have htotal:m.size + v.size + 2 + (m * v + m + v) * (2 * (2 * L) + 6)≤
      128 * A ^ 8:=by omega
  exact hencoded.trans htotal

noncomputable def sizeBound:Polynomial ℕ:=Polynomial.C 128 * (Polynomial.X + Polynomial.C 1) ^ 8

theorem sizeBound_eval (L:ℕ):sizeBound.eval L=128 * (L + 1) ^ 8:=by simp [sizeBound]

theorem flow_program_polynomial_size {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    bitSize (Lax109476.RationalEncoding.encodeProgram (program I))≤
      sizeBound.eval (bitSize (encodeInput kind I)):=by
  rw [sizeBound_eval]
  exact flow_program_size kind I

end Lax455465Proofs.LpInputSize

end

section

namespace Lax455465Proofs.RamFlowMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP
open RamFlowData
open scoped NNRat

def decode:Com:=.seq (.assign "lp.i" (.div (.var "lp.entry") (.var "lp.columns")))
  (.assign "lp.j" (.sub (.var "lp.entry") (.mul (.var "lp.i") (.var "lp.columns"))))

theorem decode_spec (B k c:ℕ) (hk:k < B) (hc:c < B):
    Spec B (fun σ => σ.vars "lp.entry"=k∧ σ.vars "lp.columns"=c) decode
      (fun _ τ => τ.vars "lp.i"=k/c∧ τ.vars "lp.j"=k%c) 10:=by
  have hdiv:k/c < B:=(Nat.div_le_self _ _).trans_lt hk
  have hprod:k/c*c < B:=(Nat.div_mul_le_self _ _).trans_lt hk
  have hmod:k%c < B:=(Nat.mod_le _ _).trans_lt hk
  rintro σ ⟨he,hcσ⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 k c; let c2:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) k c; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.i") c1) (@Eq Nat (Env.vars τ "lp.j") c2)) σ; let c4:Nat:=c0 (Env.vars σ "lp.entry") (Env.vars σ "lp.columns"); let c5:Env:=Env.setVar σ "lp.i" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "lp.entry"; let c8:Nat:=c6 "lp.i"; let c9:Nat:=c6 "lp.columns"; let c10:Nat:=Nat.mul c8 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c7 c10; let c12:Env:=Env.setVar c5 "lp.j" c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat→ Nat:=c13 ((1:Nat)); let c15:Nat:=c14 (Expr.size (Expr.div (Expr.var "lp.entry") (Expr.var "lp.columns"))); let c16:Expr:=Expr.sub (Expr.var "lp.entry") (Expr.mul (Expr.var "lp.i") (Expr.var "lp.columns")); let c17:Nat:=c14 (Expr.size c16); let c18:String→ Nat:=Env.vars c12; @Exists.intro Env (fun (σ':Env) => And (Run B decode σ σ' ((10:Nat))) (c3 σ')) c12 (@And.intro (Run B decode σ c12 ((10:Nat))) (c3 c12) (RunStep.mono B decode σ c12 (c13 c15 c17) ((10:Nat)) (RunStep.seq B (Com.assign "lp.i" (Expr.div (Expr.var "lp.entry") (Expr.var "lp.columns"))) (Com.assign "lp.j" c16) σ c5 c12 c15 c17 (RunStep.assign B σ "lp.i" (Expr.div (Expr.var "lp.entry") (Expr.var "lp.columns")) c4 (RunStep.eval_div B σ (Expr.var "lp.entry") (Expr.var "lp.columns") (Env.vars σ "lp.entry") (Env.vars σ "lp.columns") (RunStep.eval_var B σ "lp.entry" (?nAX_g5938_0_0_0)) (RunStep.eval_var B σ "lp.columns" (?nAX_g5938_0_0_1)) ?_)) (RunStep.assign B c5 "lp.j" c16 c11 (RunStep.eval_sub B c5 (Expr.var "lp.entry") (Expr.mul (Expr.var "lp.i") (Expr.var "lp.columns")) c7 c10 (RunStep.eval_var B c5 "lp.entry" (?nAX_g5938_0_0_2)) (RunStep.eval_mul B c5 (Expr.var "lp.i") (Expr.var "lp.columns") c8 c9 (RunStep.eval_var B c5 "lp.i" ?_) (RunStep.eval_var B c5 "lp.columns" (?nAX_g5938_0_0_3)) ?_) (?nAX_g5938_0_0_4)))) (?nAX_g5938_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5938_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5938_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5938_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5938_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5938_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5938_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def entry:Com:=.seq decode RamFlowCoefficient.command

theorem entry_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (k:Fin (rows n*columns n)) (hB:2*M^2+3 < B)
    (hni:2*n+1 < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B)
    (hnum:∀ z, (I.weight z).num≤ M) (hden:∀ z, (I.weight z).den≤ M):
    Spec B (fun σ => Data I σ∧ σ.vars "lp.entry"=k.val) entry
      (fun _ τ => Data I τ∧ FractionOutput (FlowLpMatrixList.entry (program I) k) τ)
      (36*(M*M).size+204):=by
  rintro σ ⟨hdata,hk⟩
  obtain ⟨ν,hdecode,hdecoded⟩:=decode_spec B k.val (columns n) (k.isLt.trans hm) hc σ
    ⟨hk,hdata.2.2.2.2.1⟩
  have hdataν:=RamFlowData.frame hdecode I hdata (by decide) (by decide)
  let ij:Fin (rows n) × Fin (columns n):=finProdFinEquiv.symm k
  let r:Row n:=(rowIndex n).symm ij.1
  let v:Variable n:=(variableIndex n).symm ij.2
  have hiν:ν.vars "lp.i"=(rowIndex n r).val:=by
    simpa only [r,Equiv.apply_symm_apply,ij,FlowLpMatrixList.rowIndex_value] using hdecoded.1
  have hjν:ν.vars "lp.j"=(variableIndex n v).val:=by
    simpa only [v,Equiv.apply_symm_apply,ij,FlowLpMatrixList.columnIndex_value] using hdecoded.2
  have hctx:RamFlowContext.Context n (rowIndex n r).val (variableIndex n v).val (List.ofFn I.weight) ν:=
    ⟨hdataν.1,hdataν.2.1,hdataν.2.2.1,hiν,hjν,hdataν.2.2.2.2.2.2.1⟩
  obtain ⟨τ,hcoefficient,hpost⟩:=RamFlowCoefficient.command_spec B M I r v hB hni hn2 hn3
    (by simpa only [r,Equiv.apply_symm_apply] using ij.1.isLt.trans hr)
    (by simpa only [v,Equiv.apply_symm_apply] using ij.2.isLt.trans hc) hnum hden ν hctx
  have hdataτ:=RamFlowData.frame hcoefficient I hdataν (by decide) (by decide)
  refine ⟨τ,(hdecode.seq hcoefficient).mono (by omega),hdataτ,?_⟩
  simpa only [FlowLpMatrixList.entry,program,r,v,ij] using hpost

def command:Com:=RamVectorEncoding.command "lp.entry" "lp.matrixLength" entry

theorem command_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (words:List ℕ) (hM:1≤ M) (hB:2*M^2+3 < B)
    (hni:2*n+1 < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B)
    (hlen:words.length+3*(rows n*columns n)+3 < B)
    (hnum:∀ z, (I.weight z).num≤ M) (hden:∀ z, (I.weight z).den≤ M):
    Spec B (fun σ => Data I σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*(rows n*columns n) < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I τ∧ Prefix (words ++ (FlowLpMatrixList.values (program I)).flatMap
        Lax109476.RationalEncoding.encodeRational) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*(rows n*columns n))
      ((36*(M*M).size+239)*(rows n*columns n)+6):=by
  have h1:1 < B:=by nlinarith
  let qs:=FlowLpMatrixList.values (program I)
  have hlength:qs.length=rows n*columns n:=by simp [qs,FlowLpMatrixList.values]
  have hheight:∀ i, ∀ hi:i < qs.length,LpInputSize.Height (M*M) qs[i]:=by
    intro i hi
    have hix:i < rows n*columns n:=by rwa [hlength] at hi
    have hw:∀ z,LpInputSize.Height M (I.weight z:ℚ):=fun z => by
      simpa only [LpInputSize.Height,NNRat.natAbs_num_coe,NNRat.den_coe] using And.intro (hnum z) (hden z)
    simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn,FlowLpMatrixList.entry,program]
      using LpInputSize.coefficient_height I M hM hw
        ((rowIndex n).symm (finProdFinEquiv.symm (⟨i,hix⟩:Fin (rows n*columns n))).1)
        ((variableIndex n).symm (finProdFinEquiv.symm (⟨i,hix⟩:Fin (rows n*columns n))).2)
  have hMM:M*M < B:=by nlinarith
  have hloop:=RamVectorEncoding.command_spec B (36*(M*M).size+204) (Data I)
    "lp.entry" "lp.matrixLength" qs words entry h1 (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt hMM) (fun i hi => (hheight i hi).2.trans_lt hMM)
    (fun σ h => by simpa only [hlength] using h.2.2.2.2.2.1)
    (fun σ k h => RamFlowData.set_index I σ "lp.entry" k h (by decide))
    (fun i hi => by
      have hix:i < rows n*columns n:=by rwa [hlength] at hi
      simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn] using
        entry_spec B M I ⟨i,hix⟩ hB hni hn2 hn3 hr hc hm hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamFlowData.frame hrun I h (by decide) (by decide)) (by decide)
  simpa only [command,hlength,qs,RamVectorEncoding.encode,Nat.add_assoc,Nat.reduceAdd] using hloop

end Lax455465Proofs.RamFlowMatrix

end

section

namespace Lax455465Proofs.RamFlowVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP FlowLpIndices
open RamFlowData
open scoped NNRat

def bound:Com:=.ite (.lt (.var "lp.i") (.var "lp.n2"))
  (RamUnsignedBuffer.read "flow.capacities" "lp.i") RamFractionPrimitives.zero

theorem bound_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (r:Row n) (h1:1 < B) (hn2:n*n < B) (hr:(rowIndex n r).val < B)
    (hcindex:2*(n*n)+1 < B) (hM:M < B)
    (hnum:∀ u v, (I.capacity u v).num≤ M) (hden:∀ u v, (I.capacity u v).den≤ M):
    Spec B (fun σ => Data I σ∧ σ.vars "lp.i"=(rowIndex n r).val) bound
      (fun _ τ => Data I τ∧ FractionOutput (rowBound I r) τ) 18:=by
  rintro σ ⟨hdata,hi⟩
  cases r with
  | inl e =>
    rcases e with ⟨u,v⟩
    have he:(rowIndex n (.inl (u,v))).val=(edgeIndex n (u,v)).val:=by rw [_root_.Lax455465Proofs.FlowLpIndices.capacity_row,edge_value]
    have hrow:(rowIndex n (.inl (u,v))).val < n*n:=he ▸ (edgeIndex n (u,v)).isLt
    have hcond:(Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B σ=some true:=by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inl (u,v))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hdata.2.1.symm,hdata.2.1 ▸ hn2⟩,by simp [hrow]⟩
    have hlen:(capacities I).length=n*n:=by simp [capacities]
    have hlt:(rowIndex n (.inl (u,v))).val < (capacities I).length:=by rwa [hlen]
    have hvalue:(capacities I)[(rowIndex n (.inl (u,v))).val]=I.capacity u v:=by
      simp only [capacities,List.getElem_ofFn,he,Fin.eta,Equiv.symm_apply_apply]
    obtain ⟨τ,hrun,hpost⟩:=RamUnsignedBuffer.read_spec B "flow.capacities" "lp.i" (capacities I)
      (rowIndex n (.inl (u,v))).val hlt (by omega) (by omega)
      (by rw [hvalue]; exact (hnum u v).trans_lt hM)
      (by rw [hvalue]; exact (hden u v).trans_lt hM) (by decide) σ ⟨hdata.2.2.2.2.2.2.2,hi⟩
    have hdτ:=RamFlowData.frame hrun I hdata (by decide) (by decide)
    exact ⟨τ,(Run.ite_true hcond hrun).mono (by simp [Cond.size,Expr.size]),hdτ,
      by simpa only [hvalue,rowBound] using hpost.1⟩
  | inr b =>
    rcases b with ⟨flag,⟨⟨s,t⟩,u⟩⟩
    have hrow:¬(rowIndex n (.inr (flag,((s,t),u)))).val < n*n:=by rw [_root_.Lax455465Proofs.FlowLpIndices.balance_row]; omega
    have hcond:(Cond.lt (.var "lp.i") (.var "lp.n2")).evalB B σ=some false:=by
      rw [evalB_condLt_iff]
      exact ⟨(rowIndex n (.inr (flag,((s,t),u)))).val,n*n,
        by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hr⟩,
        by rw [evalB_var_iff]; exact ⟨hdata.2.1.symm,hdata.2.1 ▸ hn2⟩,by simp [hrow]⟩
    obtain ⟨τ,hrun,hpost⟩:=RamFractionPrimitives.zero_spec B h1 σ True.intro
    exact ⟨τ,(Run.ite_false hcond hrun).mono (by simp [Cond.size,Expr.size]),
      RamFlowData.frame hrun I hdata (by decide) (by decide),hpost⟩

def objective:Com:=RamFlowUnits.objective

theorem objective_spec (B:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (v:Variable n) (h1:1 < B) (hv:(variableIndex n v).val < B):
    Spec B (fun σ => Data I σ∧ σ.vars "lp.j"=(variableIndex n v).val) objective
      (fun _ τ => Data I τ∧ FractionOutput (DirectedFlowLP.objective v) τ) 10:=by
  rintro σ ⟨hdata,hj⟩
  obtain ⟨τ,hrun,hpost⟩:=RamFlowUnits.objective_spec B (variableIndex n v).val h1 hv σ hj
  change FractionOutput (FlowLpFlat.objective (variableIndex n v).val) τ at hpost
  rw [FlowLpFlat.objective_eq] at hpost
  exact ⟨τ,hrun,RamFlowData.frame hrun I hdata (by decide) (by decide),hpost⟩

def bounds:Com:=RamVectorEncoding.command "lp.i" "lp.rows" bound

def objectives:Com:=RamVectorEncoding.command "lp.j" "lp.columns" objective

theorem bounds_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (words:List ℕ) (h1:1 < B) (hn2:n*n < B) (hr:rows n < B)
    (hcindex:2*(n*n)+1 < B) (hMpos:1≤ M) (hM:M < B)
    (hlen:words.length+3*rows n+3 < B)
    (hnum:∀ u v, (I.capacity u v).num≤ M) (hden:∀ u v, (I.capacity u v).den≤ M):
    Spec B (fun σ => Data I σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*rows n < (σ.arrs "lp.word").length) bounds
      (fun _ τ => Data I τ∧ Prefix (words ++ Lax109476.RationalEncoding.encodeVector (program I).b) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*rows n) (53*rows n+6):=by
  let qs:=List.ofFn (program I).b
  have hlength:qs.length=rows n:=by simp [qs]
  have hheight:∀ i, ∀ hi:i < qs.length,LpInputSize.Height M qs[i]:=by
    intro i hi
    have hi':i < rows n:=by rwa [hlength] at hi
    change LpInputSize.Height M ((List.ofFn (program I).b)[i])
    simp only [List.getElem_ofFn,program]
    cases (rowIndex n).symm ⟨i,hi'⟩ with
    | inl e =>
      exact ⟨by simpa only [rowBound,NNRat.natAbs_num_coe] using hnum e.1 e.2,
        by simpa only [rowBound,NNRat.den_coe] using hden e.1 e.2⟩
    | inr b => exact LpInputSize.height_zero hMpos
  have hloop:=RamVectorEncoding.command_spec B 18 (Data I) "lp.i" "lp.rows" qs words bound h1
    (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt hM) (fun i hi => (hheight i hi).2.trans_lt hM)
    (fun σ h => by simpa only [hlength] using h.2.2.2.1)
    (fun σ k h => RamFlowData.set_index I σ "lp.i" k h (by decide))
    (fun i hi => by
      have hi':i < rows n:=by rwa [hlength] at hi
      simpa only [qs,List.getElem_ofFn,program,Equiv.apply_symm_apply] using
        bound_spec B M I ((rowIndex n).symm ⟨i,hi'⟩) h1 hn2
          (by simpa only [Equiv.apply_symm_apply] using hi'.trans hr) hcindex hM hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamFlowData.frame hrun I h (by decide) (by decide)) (by decide)
  simpa only [bounds,hlength,qs,RamVectorEncoding.encode,Lax109476.RationalEncoding.encodeVector,
    Nat.reduceAdd] using hloop

theorem objectives_spec (B:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (words:List ℕ) (h1:1 < B) (hc:columns n < B)
    (hlen:words.length+3*columns n+3 < B):
    Spec B (fun σ => Data I σ∧ Prefix words "lp.word" σ∧ σ.vars "lp.position"=words.length∧
      words.length+3*columns n < (σ.arrs "lp.word").length) objectives
      (fun _ τ => Data I τ∧ Prefix (words ++ Lax109476.RationalEncoding.encodeVector (program I).c) "lp.word" τ∧
        τ.vars "lp.position"=words.length+3*columns n) (45*columns n+6):=by
  let qs:=List.ofFn (program I).c
  have hlength:qs.length=columns n:=by simp [qs]
  have hheight:∀ i, ∀ hi:i < qs.length,LpInputSize.Height 1 qs[i]:=by
    intro i hi
    have hi':i < columns n:=by rwa [hlength] at hi
    change LpInputSize.Height 1 ((List.ofFn (program I).c)[i])
    simp only [List.getElem_ofFn,program]
    cases (variableIndex n).symm ⟨i,hi'⟩ with
    | inl v => exact LpInputSize.height_one (by rfl)
    | inr a => exact LpInputSize.height_zero (by rfl)
  have hloop:=RamVectorEncoding.command_spec B 10 (Data I) "lp.j" "lp.columns" qs words objective h1
    (by simpa only [hlength] using hlen)
    (fun i hi => (hheight i hi).1.trans_lt h1) (fun i hi => (hheight i hi).2.trans_lt h1)
    (fun σ h => by simpa only [hlength] using h.2.2.2.2.1)
    (fun σ k h => RamFlowData.set_index I σ "lp.j" k h (by decide))
    (fun i hi => by
      have hi':i < columns n:=by rwa [hlength] at hi
      simpa only [qs,List.getElem_ofFn,program,Equiv.apply_symm_apply] using
        objective_spec B I ((variableIndex n).symm ⟨i,hi'⟩) h1
          (by simpa only [Equiv.apply_symm_apply] using hi'.trans hc))
    (by decide) (by decide) (by decide) (by decide)
    (fun hrun h => RamFlowData.frame hrun I h (by decide) (by decide)) (by decide)
  simpa only [objectives,hlength,qs,RamVectorEncoding.encode,Lax109476.RationalEncoding.encodeVector,
    Nat.reduceAdd] using hloop

end Lax455465Proofs.RamFlowVectors

end

section

namespace Lax455465Proofs.RamFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP
open RamFlowData Lax109476.RationalEncoding
open scoped NNRat

def header:Com:=.seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.rows"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.columns")))

theorem header_spec (B:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (h2:2 < B) (hr:rows n < B) (hc:columns n < B):
    Spec B (fun σ => Data I σ∧ 2 < (σ.arrs "lp.word").length) header
      (fun _ τ => Data I τ∧ Prefix [rows n,columns n] "lp.word" τ∧ τ.vars "lp.position"=2) 16:=by
  rintro σ ⟨hdata,hroom⟩
  let ν:=σ.setVar "lp.position" 0
  have hzero:Run B (.assign "lp.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hdataν:=RamFlowData.frame hzero I hdata (by decide) (by decide)
  obtain ⟨μ,hrow,hrowPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position" [] (rows n)
    (.var "lp.rows") (by omega) (by simp; omega) ν
      ⟨by intro i hi; simp at hi,by simp [ν],by simp [ν]; omega,
        by rw [evalB_var_iff]; exact ⟨hdataν.2.2.2.1.symm,hdataν.2.2.2.1 ▸ hr⟩⟩
  have hdataμ:=RamFlowData.frame hrow I hdataν (by decide) (by decide)
  have hroomμ:2 < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hrow "lp.word"]; simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hcol,hcolPost⟩:=RamWordBuffer.append_spec B "lp.word" "lp.position" [rows n] (columns n)
    (.var "lp.columns") (by omega) (by simp; omega) μ
      ⟨hrowPost.1,by simpa using hrowPost.2,by simp; omega,
        by rw [evalB_var_iff]; exact ⟨hdataμ.2.2.2.2.1.symm,hdataμ.2.2.2.2.1 ▸ hc⟩⟩
  exact ⟨τ,hzero.seq (hrow.seq hcol),RamFlowData.frame hcol I hdataμ (by decide) (by decide),
    by simpa using hcolPost.1,by simpa using hcolPost.2⟩

def cost (n M:ℕ):ℕ:=
  (36*(M*M).size+239)*(rows n*columns n)+53*rows n+45*columns n+34

def command:Com:=.seq header (.seq RamFlowMatrix.command
  (.seq RamFlowVectors.bounds RamFlowVectors.objectives))

theorem command_spec (B M:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (hM:1≤ M) (hB:2*M^2+3 < B)
    (hni:2*n+1 < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B)
    (hcindex:2*(n*n)+1 < B) (hlen:wordLength n+3 < B)
    (hnum:∀ z, (I.weight z).num≤ M) (hden:∀ z, (I.weight z).den≤ M)
    (hcapnum:∀ u v, (I.capacity u v).num≤ M) (hcapden:∀ u v, (I.capacity u v).den≤ M):
    Spec B (fun σ => Data I σ∧ wordLength n < (σ.arrs "lp.word").length) command
      (fun _ τ => Data I τ∧ Prefix (encodeProgram (program I)) "lp.word" τ∧
        τ.vars "lp.position"=(encodeProgram (program I)).length) (cost n M):=by
  have h2:2 < B:=by nlinarith
  have hMB:M < B:=by nlinarith
  rintro σ ⟨hdata,hroom⟩
  obtain ⟨ν,hhead,hheadPost⟩:=header_spec B I h2 hr hc σ ⟨hdata,by dsimp only [wordLength] at hroom; omega⟩
  obtain ⟨μ,hmat,hmatPost⟩:=RamFlowMatrix.command_spec B M I [rows n,columns n] hM hB hni hn2 hn3 hr hc hm
    (by simp only [List.length_cons,List.length_nil,wordLength] at *; omega) hnum hden ν
      ⟨hheadPost.1,hheadPost.2.1,by simpa using hheadPost.2.2,
        by rw [RamFrames.run_array_length hhead "lp.word"]; simp only [List.length_cons,List.length_nil];
           dsimp only [wordLength] at hroom; omega⟩
  let matrixWords:= [rows n,columns n] ++ (FlowLpMatrixList.values (program I)).flatMap encodeRational
  have hmatrixLength:matrixWords.length=2+3*(rows n*columns n):=by
    change ([rows n,columns n] ++ RamVectorEncoding.encode (FlowLpMatrixList.values (program I))).length=_
    simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
      FlowLpMatrixList.values,List.length_ofFn]
  have hroomμ:wordLength n < (μ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hmat "lp.word",RamFrames.run_array_length hhead "lp.word"]; exact hroom
  obtain ⟨ρ,hbounds,hboundsPost⟩:=RamFlowVectors.bounds_spec B M I matrixWords (by omega) hn2 hr hcindex hM hMB
    (by rw [hmatrixLength]; dsimp only [wordLength] at hlen; omega) hcapnum hcapden μ
      ⟨hmatPost.1,hmatPost.2.1,by simpa only [List.length_cons,List.length_nil,hmatrixLength] using hmatPost.2.2,
        by rw [hmatrixLength]; dsimp only [wordLength] at hroomμ; omega⟩
  let boundWords:=matrixWords ++ encodeVector (program I).b
  have hboundLength:boundWords.length=2+3*(rows n*columns n)+3*rows n:=by
    change (matrixWords ++ RamVectorEncoding.encode (List.ofFn (program I).b)).length=_
    simp only [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hmatrixLength]
  have hroomρ:wordLength n < (ρ.arrs "lp.word").length:=by
    rw [RamFrames.run_array_length hbounds "lp.word"]; exact hroomμ
  obtain ⟨τ,hobj,hobjPost⟩:=RamFlowVectors.objectives_spec B I boundWords (by omega) hc
    (by rw [hboundLength]; dsimp only [wordLength] at hlen; omega) ρ
      ⟨hboundsPost.1,hboundsPost.2.1,by rw [hboundLength]; simpa only [hmatrixLength] using hboundsPost.2.2,
        by rw [hboundLength]; dsimp only [wordLength] at hroomρ; omega⟩
  have hencoded:boundWords ++ encodeVector (program I).c=encodeProgram (program I):=by
    simp only [boundWords,matrixWords,FlowLpMatrixList.values_eq,encodeProgram]
  have hencodedLength:(encodeProgram (program I)).length=2+3*(rows n*columns n)+3*rows n+3*columns n:=by
    rw [←hencoded]
    change (boundWords ++ RamVectorEncoding.encode (List.ofFn (program I).c)).length=_
    simp only [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hboundLength]
  refine ⟨τ,(hhead.seq (hmat.seq (hbounds.seq hobj))).mono (by simp only [cost]; omega),hobjPost.1,?_,?_⟩
  · simpa only [hencoded] using hobjPost.2.1
  · simpa only [hencodedLength,hboundLength] using hobjPost.2.2

end Lax455465Proofs.RamFlowLp

end

section

namespace Lax455465Proofs.RegisteredLpExecution

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

theorem exists_program:
    ∃ (p:Lax808846.Ram.Program) (wordBound timeBound:Polynomial ℕ),
      ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
        IsValidCertificate P certificate∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length::encodeProgram P) ++ encodeCertificate certificate)∧
        ∃ k≤ timeBound.eval (bitSize (encodeProgram P)), ∃ s:SparseRam.SparseState,
          SparseRam.run (wordBound.eval (bitSize (encodeProgram P))) p k
            (SparseRam.init ((encodeProgram P).length::encodeProgram P))=some s∧
          SparseRam.step (wordBound.eval (bitSize (encodeProgram P))) p s=none∧
          s.out=encodeCertificate certificate∧ s.memory.length≤ k:=by
  obtain ⟨solve,htime,hcorrect⟩:=Lax109476Proofs.RamUniformSolver.exists_exact_polynomial_time_solver
  obtain ⟨p,wordBound,timeBound,hprogram⟩:=SparseRam.polynomial_execution solve htime
  refine ⟨p,wordBound,timeBound, ?_⟩
  intro m n P
  obtain ⟨certificate,hencode,hvalid⟩:=hcorrect m n P
  have hrun:=hprogram (encodeProgram P)
  rw [hencode] at hrun
  exact ⟨certificate,hvalid,hrun⟩

end Lax455465Proofs.RegisteredLpExecution

end

section

namespace Lax455465Proofs.RamVirtualTraceBounds

open Lax808846.Ram SparseRam RamVirtualInstruction

theorem literals_mono (i:Instr) {A B:ℕ} (h:LiteralsFit A i) (hab:A≤ B):
    LiteralsFit B i:=by
  cases i <;> simp_all [LiteralsFit] <;> omega

end Lax455465Proofs.RamVirtualTraceBounds

end

section

namespace Lax455465Proofs.RamVirtualConstants

open Lax808846.Ram RamVirtualInstruction RamVirtualTraceBounds

theorem literal_fits (i:Instr):LiteralsFit (literalBound i - 1) i:=by
  cases i <;> simp [LiteralsFit,literalBound]

theorem length_bound (p:Program):p.length + 1 < allowance p:=by
  unfold allowance
  omega

theorem literals_fit (p:Program):∀ i∈ p,LiteralsFit (allowance p - 1) i:=by
  intro i hi
  have hsum:literalBound i≤ (p.map literalBound).sum:=List.single_le_sum
    (fun j hj => Nat.zero_le _) (literalBound i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
  exact literals_mono i (literal_fits i) (by unfold allowance; omega)

end Lax455465Proofs.RamVirtualConstants

end

section

namespace Lax455465Proofs.RegisteredLpNative

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamVirtualState RamVirtualProgram

theorem exists_program:
    ∃ (p:Lax808846.Ram.Program) (wordBound timeBound:Polynomial ℕ),
      ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
        IsValidCertificate P certificate∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length::encodeProgram P) ++ encodeCertificate certificate)∧
        ∀ B:ℕ,
          2 * (2 ^ wordBound.eval (bitSize (encodeProgram P))) ^ 2 + 3 < B→
          timeBound.eval (bitSize (encodeProgram P)) + 1 < B→
          RamVirtualConstants.allowance p < B→
          Spec B (fun σ => σ.vars "vm.width"=wordBound.eval (bitSize (encodeProgram P))∧
            Prefix ((encodeProgram P).length::encodeProgram P) "vm.input" σ∧
            σ.vars "vm.inputLength"=(encodeProgram P).length + 1∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.addresses").length∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.values").length∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.output").length)
            (execute p)
            (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ∧
              τ.vars "vm.outputLength"=(encodeCertificate certificate).length∧
              τ.vars "vm.running"=0)
            ((timeBound.eval (bitSize (encodeProgram P)) + 1) *
              (4 * p.length + 32 * timeBound.eval (bitSize (encodeProgram P)) + 104) + 18):=by
  obtain ⟨p,wordBound,timeBound,hprogram⟩:=RegisteredLpExecution.exists_program
  refine ⟨p,wordBound,timeBound, ?_⟩
  intro m n P
  obtain ⟨certificate,hvalid,hfit,k,hk,s,hrun,hhalt,hout,_⟩:=hprogram m n P
  refine ⟨certificate,hvalid,hfit, ?_⟩
  intro B hB htime hallow
  let w:=wordBound.eval (bitSize (encodeProgram P))
  let T:=timeBound.eval (bitSize (encodeProgram P))
  let input:=(encodeProgram P).length::encodeProgram P
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have hinput:FitsInWords w input:=fun x hx => hfit x (List.mem_append_left _ hx)
  have hlenWord:(encodeProgram P).length < 2 ^ w:=hinput _ List.mem_cons_self
  have hlen:input.length < B:=by simp only [input,List.length_cons]; omega
  have hwords:∀ x∈ input,x < B:=fun x hx => (hinput x hx).trans hM
  have hp:p.length + 1 < B:=(RamVirtualConstants.length_bound p).trans hallow
  have hlit:∀ i∈ p,RamVirtualInstruction.LiteralsFit (B - 1) i:=fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  have hnative:=RamVirtualExecution.execute_spec B w k p input s hB (by omega) hp hlit
    hlen hwords hrun hhalt
  apply ((hnative.pre ?_).post ?_).mono ?_
  · rintro σ ⟨hwidth,hprefix,hinputlen,hA,hV,hO⟩
    exact ⟨hwidth,hprefix,hinputlen,by omega,by omega,by omega⟩
  · rintro σ τ _ ⟨hrep,hflag⟩
    have htapes:=hrep.2
    exact ⟨by simpa only [hout] using htapes.2.2.2.2.1,
      by simpa only [hout] using htapes.2.2.2.2.2,hflag⟩
  · have hprod:=Nat.mul_le_mul (Nat.add_le_add_right hk 1)
      (show 4 * p.length + 32 * k + 104≤ 4 * p.length + 32 * T + 104 by omega)
    dsimp only [T] at hprod
    omega

end Lax455465Proofs.RegisteredLpNative

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

private theorem take_size_le (xs:List ℕ) (i:ℕ):
    Lax759944.BinaryWordEncoding.bitSize (xs.take i)≤ Lax759944.BinaryWordEncoding.bitSize xs:=by
  have h:=WordSize.bitSize_append (xs.take i) (xs.drop i)
  rw [List.take_append_drop] at h
  omega

private theorem take_size_step (xs:List ℕ) (i:ℕ) (hi:i < xs.length):
    Lax759944.BinaryWordEncoding.bitSize (xs.take (i + 1)) =
      Lax759944.BinaryWordEncoding.bitSize (xs.take i) + xs[i].size + 1:=by
  rw [List.take_succ_eq_append_getElem hi,WordSize.bitSize_append,WordSize.bitSize_cons,
    WordSize.bitSize_nil]
  omega

open RamVirtualState Lax759944.BinaryWordEncoding

def ArrayInvariant (xs:List ℕ) (data lengthVar:String) (σ:Env):Prop:=
  σ.vars lengthVar=xs.length∧ σ.vars "size.i" ≤ xs.length∧
  σ.vars "size.total"=bitSize (xs.take (σ.vars "size.i"))∧ Prefix xs data σ

theorem arrayStep_spec (B:ℕ) (xs:List ℕ) (data lengthVar:String)
    (hfresh:∀ x∈ ["size.i", "size.value", "size.count", "size.total"],x ≠ lengthVar) (h2:2 < B) (hlen:xs.length < B)
    (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => ArrayInvariant xs data lengthVar σ∧ σ.vars "size.i" < xs.length) (arrayStep data)
      (fun σ τ => ArrayInvariant xs data lengthVar τ∧ τ.vars "size.i"=σ.vars "size.i" + 1)
      (12 * bitSize xs + 19):=by
  have hfi:=hfresh "size.i" (by simp)
  have hfv:=hfresh "size.value" (by simp)
  have hfc:=hfresh "size.count" (by simp)
  have hft:=hfresh "size.total" (by simp)
  have hfi':=Ne.symm hfi
  have hfv':=Ne.symm hfv
  have hfc':=Ne.symm hfc
  have hft':=Ne.symm hft
  rintro σ ⟨⟨hcount,hi,htotal,hp⟩,hpos⟩
  let i:=σ.vars "size.i"
  let value:=xs[i]
  have hvalue:value < B:=hwords _ (List.getElem_mem hpos)
  have hget:=hp i hpos
  have harray:i < (σ.arrs data).length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have hiB:σ.vars "size.i" < B:=hpos.trans hlen
  have hread:(Expr.get data (.var "size.i")).evalB B σ=some value:=by
    rw [evalB_get_iff]
    exact ⟨i,evalB_var hiB,hget,hvalue⟩
  let ν:=σ.setVar "size.value" value
  have hload:Run B (.assign "size.value" (.get data (.var "size.i"))) σ ν 3:=
    Run.assign hread
  obtain ⟨μ,hword,hzero,hbits⟩:=word_spec B value h2 hvalue ν (by simp [ν])
  have hiμ:μ.vars "size.i"=i:=(hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars])).trans
    (by simp [ν,i])
  have htotalμ:μ.vars "size.total"=bitSize (xs.take i):=
    (hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars])).trans (by simpa [ν,i] using htotal)
  have hlenμ:μ.vars lengthVar=xs.length:=
    (hword.frame_var _ (by simp [word,wordLoop,wordStep,Com.wvars,Ne.symm hfv,Ne.symm hfc])).trans (by simpa [ν,hfv,Ne.symm hfv] using hcount)
  have hdataμ:=hword.frame_arr data (by simp [word,wordLoop,wordStep,Com.warrs])
  have hpμ:Prefix xs data μ:=by simpa only [Prefix,hdataμ,ν,arrs_setVar] using hp
  have hstep:=take_size_step xs i hpos
  have hbound:=take_size_le xs (i + 1)
  have hsum:bitSize (xs.take i) + value.size + 1 < B:=by dsimp only [value]; omega
  have htotalB:bitSize (xs.take i) < B:=(take_size_le xs i).trans_lt (by omega)
  have hcountB:value.size < B:=by
    have hs:=WordSize.member_size xs value (List.getElem_mem hpos)
    omega
  have hiNext:i + 1 < B:=by omega
  have hfinish:Spec B (fun τ => τ.vars "size.i"=i∧ τ.vars "size.total"=bitSize (xs.take i)∧
      τ.vars "size.count"=value.size∧ τ.vars lengthVar=xs.length∧ Prefix xs data τ)
      (.seq (.assign "size.total" (.add (.add (.var "size.total") (.var "size.count")) (.lit 1)))
        (.assign "size.i" (.add (.var "size.i") (.lit 1))))
      (fun _ τ => ArrayInvariant xs data lengthVar τ∧ τ.vars "size.i"=i + 1) 10:=by
    rintro τ ⟨hiτ,htτ,hcτ,hlτ,hpτ⟩
    (expose_names;
      (refine let c0:Expr:=Expr.add (Expr.add (Expr.var "size.total") (Expr.var "size.count")) (Expr.lit ((1:Nat))); let c1:Com:=Com.assign "size.total" c0; let c2:Expr:=Expr.add (Expr.var "size.i") (Expr.lit ((1:Nat))); let c3:Com:=Com.assign "size.i" c2; let c4:Com:=Com.seq c1 c3; let c5:Env→ Nat→ Prop:=Run B c4 τ; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=c6 i ((1:Nat)); let c8:Env→ Prop:=(fun (x τ_1:Env) => And (ArrayInvariant xs data lengthVar τ_1) (@Eq Nat (Env.vars τ_1 "size.i") c7)) τ; let c9:Nat:=c6 (Env.vars τ "size.total") (Env.vars τ "size.count"); let c10:Nat:=c6 c9 ((1:Nat)); let c11:Env:=Env.setVar τ "size.total" c10; let c12:Nat:=Env.vars c11 "size.i"; let c13:Nat:=c6 c12 ((1:Nat)); let c14:Env:=Env.setVar c11 "size.i" c13; let c15:Nat→ Nat:=c6 ((1:Nat)); let c16:Nat:=c15 (Expr.size c0); let c17:Nat:=c15 (Expr.size c2); @Exists.intro Env (fun (σ':Env) => And (c5 σ' ((10:Nat))) (c8 σ')) c14 (@And.intro (c5 c14 ((10:Nat))) (c8 c14) (RunStep.mono B c4 τ c14 (c6 c16 c17) ((10:Nat)) (RunStep.seq B c1 c3 τ c11 c14 c16 c17 (RunStep.assign B τ "size.total" c0 c10 (RunStep.eval_add B τ (Expr.add (Expr.var "size.total") (Expr.var "size.count")) (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_add B τ (Expr.var "size.total") (Expr.var "size.count") (Env.vars τ "size.total") (Env.vars τ "size.count") (RunStep.eval_var B τ "size.total" (?nAX_g6028_0_0_0)) (RunStep.eval_var B τ "size.count" (?nAX_g6028_0_0_1)) (?nAX_g6028_0_0_2)) (RunStep.eval_lit B ((1:Nat)) τ (?nAX_g6028_0_0_3)) (?nAX_g6028_0_0_4))) (RunStep.assign B c11 "size.i" c2 c13 (RunStep.eval_add B c11 (Expr.var "size.i") (Expr.lit ((1:Nat))) c12 ((1:Nat)) (RunStep.eval_var B c11 "size.i" (?nAX_g6028_0_0_5)) (RunStep.eval_lit B ((1:Nat)) c11 (?nAX_g6028_0_0_6)) (?nAX_g6028_0_0_7)))) (?nAX_g6028_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6028_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6028_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear hload); (all_goals try clear hword))
    all_goals simp_all [ArrayInvariant,Prefix,value]
    all_goals omega
  obtain ⟨τ,hfinish,hpost⟩:=hfinish μ ⟨hiμ,htotalμ,hbits,hlenμ,hpμ⟩
  exact ⟨τ, (hload.seq (hword.seq hfinish)).mono (by
    have hs:=WordSize.member_size xs value (List.getElem_mem hpos)
    omega),hpost⟩

theorem array_spec (B:ℕ) (xs:List ℕ) (data lengthVar:String)
    (hfresh:∀ x∈ ["size.i", "size.value", "size.count", "size.total"],x ≠ lengthVar) (h2:2 < B) (hlen:xs.length < B)
    (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => σ.vars lengthVar=xs.length∧ Prefix xs data σ) (array data lengthVar)
      (fun _ τ => τ.vars "size.total"=bitSize xs)
      ((12 * bitSize xs + 23) * xs.length + 8):=by
  have hfi:=hfresh "size.i" (by simp)
  have hfv:=hfresh "size.value" (by simp)
  have hfc:=hfresh "size.count" (by simp)
  have hft:=hfresh "size.total" (by simp)
  have hfi':=Ne.symm hfi
  have hfv':=Ne.symm hfv
  have hfc':=Ne.symm hfc
  have hft':=Ne.symm hft
  have hscan:=Spec.forRangeZero "size.i" lengthVar (ArrayInvariant xs data lengthVar) xs.length
    (12 * bitSize xs + 19) hlen (fun _ h => h.2.1) (fun _ h => h.1)
    (arrayStep_spec B xs data lengthVar hfresh h2 hlen hsize hwords)
  have hfinish:Spec B (fun σ => ArrayInvariant xs data lengthVar (σ.setVar "size.i" 0))
      (.seq (.assign "size.i" (.lit 0)) (.while (.lt (.var "size.i") (.var lengthVar)) (arrayStep data)))
      (fun _ τ => τ.vars "size.total"=bitSize xs) ((12 * bitSize xs + 23) * xs.length + 6):=
    hscan.post (fun _ τ _ h => by simpa only [h.2,List.take_length] using h.1.2.2.1)
  rintro σ ⟨hlenσ,hpσ⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "size.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "size.i") (Expr.var lengthVar)) (arrayStep data)); let c1:Env:=Env.setVar σ "size.total" ((0:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat→ Nat:=c3 (c4 (c3 (c4 ((12:Nat)) (bitSize xs)) ((23:Nat))) (@List.length Nat xs)); let c6:Nat:=c5 ((6:Nat)); let c7:Env→ Prop:=fun (σ':Env) => And (c2 σ' c6) (@Eq Nat (Env.vars σ' "size.total") (bitSize xs)); let c8:Nat:=c5 ((8:Nat)); let c9:Env→ Env→ Prop:=fun (x τ:Env) => @Eq Nat (Env.vars τ "size.total") (bitSize xs); let c10:Env→ Prop:=c9 σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B (array data lengthVar) σ σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c7 (fun (x:@Exists Env c7) => c12) (RunStep.use B (fun (σ_1:Env) => ArrayInvariant xs data lengthVar (Env.setVar σ_1 "size.i" ((0:Nat)))) c0 c9 c6 hfinish c1 ?_) fun (w:Env) (h:And (c2 w c6) (@Eq Nat (Env.vars w "size.total") (bitSize xs))) => let c0_1:Prop:= @Eq Nat (Env.vars w "size.total") (bitSize xs); @And.casesOn (c2 w c6) c0_1 (fun (x:And (c2 w c6) c0_1) => c12) h fun (left:c2 w c6) (right:c0_1) => @Exists.intro Env c11 w (@And.intro (Run B (array data lengthVar) σ w c8) (c10 w) (RunStep.mono B (array data lengthVar) σ w (c3 c13 c6) c8 (RunStep.seq B (Com.assign "size.total" (Expr.lit ((0:Nat)))) c0 σ c1 w c13 c6 (RunStep.assign B σ "size.total" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6030_0_0_0))) left) (?nAX_g6030_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6030_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6030_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [ArrayInvariant,Prefix,WordSize.bitSize_nil]

end Lax455465Proofs.RamBitSize

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem argument_frame (coefficients:List ℕ):"poly.argument" ∉ (command coefficients).wvars:=by
  induction coefficients with
  | nil => simp [command,Com.wvars]
  | cons a rest ih => simp [command,Com.wvars,ih]

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

theorem command_spec (B:ℕ) (coefficients:List ℕ) (x:ℕ)
    (hB:0 < B) (hx:x < B) (hvalue:value coefficients (x + 1) < B):
    Spec B (fun σ => σ.vars "poly.argument"=x) (command coefficients)
      (fun _ τ => τ.vars "poly.value"=value coefficients x)
      (6 * coefficients.length + 2):=by
  induction coefficients with
  | nil =>
    intro σ hσ
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Nat.mul ((6:Nat)) (@List.length Nat (@List.nil Nat))) ((2:Nat)); let c2:Env→ Prop:=(fun (x_1 τ:Env) => @Eq Nat (Env.vars τ "poly.value") (value (@List.nil Nat) x)) σ; let c3:Env:=Env.setVar σ "poly.value" ((0:Nat)); @Exists.intro Env (fun (σ':Env) => And (Run B (command (@List.nil Nat)) σ σ' c1) (c2 σ')) c3 (@And.intro (Run B (command (@List.nil Nat)) σ c3 c1) (c2 c3) (RunStep.mono B (command (@List.nil Nat)) σ c3 (c0 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat))))) c1 (RunStep.assign B σ "poly.value" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hB)) (?nAX_g6037_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6037_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [value]
  | cons a rest ih =>
    have htail:value rest (x + 1)≤ value (a::rest) (x + 1):=by
      simp only [value]
      nlinarith
    have hrest:=ih (htail.trans_lt hvalue)
    have hrest':=RamFrames.keep_scalar hrest "poly.argument" x (argument_frame rest)
    have hsmall:=value_mono (a::rest) (show x≤ x + 1 by omega)
    have hresult:a + x * value rest x < B:=hsmall.trans_lt hvalue
    have ha:a < B:=by omega
    have hproduct:x * value rest x < B:=by omega
    have htailSmall:=value_mono rest (show x≤ x + 1 by omega)
    have hv:value rest x < B:=htailSmall.trans_lt (htail.trans_lt hvalue)
    rintro σ hσ
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((6:Nat)); let c3:Nat:=c0 (c2 (@List.length Nat rest)) ((2:Nat)); let c4:Env→ Prop:=fun (σ':Env) => And (Run B (command rest) σ σ' c3) (And (@Eq Nat (Env.vars σ' "poly.value") (value rest x)) (@Eq Nat (Env.vars σ' "poly.argument") x)); let c5:Env→ Nat→ Prop:=Run B (command (@List.cons Nat a rest)) σ; let c6:Nat:=c0 (c2 (@List.length Nat (@List.cons Nat a rest))) ((2:Nat)); let c7:Env→ Prop:=(fun (x_1 τ:Env) => @Eq Nat (Env.vars τ "poly.value") (value (@List.cons Nat a rest) x)) σ; let c8:Env→ Prop:=fun (σ':Env) => And (c5 σ' c6) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Expr:=Expr.add (Expr.lit a) (Expr.mul (Expr.var "poly.argument") (Expr.var "poly.value")); let c11:Nat:=c0 ((1:Nat)) (Expr.size c10); @Exists.casesOn Env c4 (fun (x_1:@Exists Env c4) => c9) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "poly.argument") x) (@Eq Nat (Env.vars σ_1 "poly.argument") x)) (command rest) (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "poly.value") (value rest x)) (@Eq Nat (Env.vars τ "poly.argument") x)) c3 hrest' σ ?_) fun (w:Env) (h:And (Run B (command rest) σ w c3) (And (@Eq Nat (Env.vars w "poly.value") (value rest x)) (@Eq Nat (Env.vars w "poly.argument") x))) => let c0_1:Prop:=Run B (command rest) σ w c3; let c1_1:Prop:=And (@Eq Nat (Env.vars w "poly.value") (value rest x)) (@Eq Nat (Env.vars w "poly.argument") x); let c2_1:Nat:=c1 (Env.vars w "poly.argument") (Env.vars w "poly.value"); let c3_1:Nat:=c0 a c2_1; let c4_1:Env:=Env.setVar w "poly.value" c3_1; @And.casesOn c0_1 c1_1 (fun (x_1:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c8 c4_1 (@And.intro (c5 c4_1 c6) (c7 c4_1) (RunStep.mono B (command (@List.cons Nat a rest)) σ c4_1 (c0 c3 c11) c6 (RunStep.seq B (command rest) (Com.assign "poly.value" c10) σ w c4_1 c3 c11 left (RunStep.assign B w "poly.value" c10 c3_1 (RunStep.eval_add B w (Expr.lit a) (Expr.mul (Expr.var "poly.argument") (Expr.var "poly.value")) a c2_1 (RunStep.eval_lit B a w ha) (RunStep.eval_mul B w (Expr.var "poly.argument") (Expr.var "poly.value") (Env.vars w "poly.argument") (Env.vars w "poly.value") (RunStep.eval_var B w "poly.argument" (?nAX_g6037_1_0_0)) (RunStep.eval_var B w "poly.value" (?nAX_g6037_1_0_1)) ?_) ?_))) (?nAX_g6037_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6037_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6037_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6037_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals simp_all [value]

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

namespace Lax455465Proofs.RamLpInputFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Invariant (xs:List ℕ) (σ:Env):Prop:=
  σ.vars "lp.position"=xs.length∧ σ.vars "frame.i" ≤ xs.length∧
  Prefix xs "lp.word" σ∧ Prefix (xs.length::xs.take (σ.vars "frame.i")) "vm.input" σ∧
  σ.vars "vm.inputLength"=σ.vars "frame.i" + 1∧ xs.length < (σ.arrs "vm.input").length

theorem step_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length + 1 < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Invariant xs σ∧ σ.vars "frame.i" < xs.length) step
      (fun σ τ => Invariant xs τ∧ τ.vars "frame.i"=σ.vars "frame.i" + 1) 12:=by
  rintro σ ⟨⟨hpos,hi,hsource,hp,hcursor,hroom⟩,hlt⟩
  let i:=σ.vars "frame.i"
  let value:=xs[i]
  have hi':i≤ xs.length:=hi
  have hlt':i < xs.length:=hlt
  have hv:=hwords xs[i] (List.getElem_mem hlt)
  have hget:=hsource i hlt
  have hsourceRoom:i < (σ.arrs "lp.word").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hget
    cases hget
  have he:(Expr.get "lp.word" (.var "frame.i")).evalB B σ=some value:=by
    rw [evalB_get_iff]
    exact ⟨i,evalB_var (by omega),hget,hv⟩
  have hprefixlen:(xs.length::xs.take i).length=i + 1:=by simp [List.length_take,Nat.min_eq_left hi']
  obtain ⟨ν,hwrite,hpost⟩:=RamWordBuffer.append_spec B "vm.input" "vm.inputLength"
    (xs.length::xs.take i) value (.get "lp.word" (.var "frame.i")) h1
    (by rw [hprefixlen]; omega) σ ⟨hp,by rwa [hprefixlen],by rw [hprefixlen]; omega,he⟩
  have hiν:ν.vars "frame.i"=i:=(hwrite.frame_var _ (by simp [RamWordBuffer.append,Com.wvars])).trans rfl
  have hposν:=(hwrite.frame_var "lp.position" (by simp [RamWordBuffer.append,Com.wvars])).trans hpos
  have hsourceν:Prefix xs "lp.word" ν:=by
    simpa only [Prefix,hwrite.frame_arr "lp.word" (by simp [RamWordBuffer.append,Com.warrs])] using hsource
  have hroomν:xs.length < (ν.arrs "vm.input").length:=by
    rwa [RamFrames.run_array_length hwrite "vm.input"]
  have htake:xs.take (i + 1)=xs.take i ++ [value]:=List.take_succ_eq_append_getElem hlt'
  have hpν:Prefix (xs.length::xs.take (i + 1)) "vm.input" ν:=by
    rw [htake]
    simpa only [List.cons_append] using hpost.1
  have hlenν:ν.vars "vm.inputLength"=i + 1 + 1:=by simpa only [hprefixlen] using hpost.2
  have hiNext:i + 1 < B:=by omega
  have hinc:Run B (.assign "frame.i" (.add (.var "frame.i") (.lit 1))) ν (ν.setVar "frame.i" (i + 1)) 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i < B)⟩)
      (evalB_lit h1) hiNext)
  refine ⟨ν.setVar "frame.i" (i + 1), (hwrite.seq hinc).mono (by simp [Expr.size]), ?_⟩
  constructor
  · simpa only [Invariant,Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true,if_false]
      using And.intro hposν (And.intro (by omega:i + 1≤ xs.length)
        (And.intro hsourceν (And.intro hpν (And.intro hlenν hroomν))))
  · simp [i]

theorem command_spec (B:ℕ) (xs:List ℕ) (h1:1 < B) (hlen:xs.length + 1 < B)
    (hwords:∀ x∈ xs,x < B):
    Spec B (fun σ => Prefix xs "lp.word" σ∧ σ.vars "lp.position"=xs.length∧
      xs.length < (σ.arrs "vm.input").length) command
      (fun _ τ => Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      (16 * xs.length + 15):=by
  have hscan:=Spec.forRangeZero "frame.i" "lp.position" (Invariant xs) xs.length 12
    (by omega) (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B xs h1 hlen hwords)
  have hfinish:Spec B (fun σ => Invariant xs (σ.setVar "frame.i" 0))
      (.seq (.assign "frame.i" (.lit 0)) (.while (.lt (.var "frame.i") (.var "lp.position")) step))
      (fun _ τ => Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      (16 * xs.length + 6):=hscan.post (fun _ τ _ h => by
        exact ⟨by simpa only [h.2,List.take_length] using h.1.2.2.2.1,by simpa only [h.2] using h.1.2.2.2.2.1⟩)
  have hprefix:=RamWordBuffer.append_spec B "vm.input" "vm.inputLength" [] xs.length (.var "lp.position") h1
    (by simp; omega)
  rintro σ ⟨hp,hpos,hroom⟩
  let ν:=σ.setVar "vm.inputLength" 0
  have hzero:Run B (.assign "vm.inputLength" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨μ,hhead,hheadPost⟩:=hprefix ν ⟨by intro i hi; simp at hi,by simp [ν],
    by simp [ν]; omega,by rw [evalB_var_iff]; exact ⟨by simp [ν,hpos],by simp [ν,hpos]; omega⟩⟩
  have hposμ:μ.vars "lp.position"=xs.length:=
    (hhead.frame_var _ (by simp [RamWordBuffer.append,Com.wvars])).trans (by simp [ν,hpos])
  have hpμ:Prefix xs "lp.word" μ:=by
    simpa only [Prefix,hhead.frame_arr "lp.word" (by simp [RamWordBuffer.append,Com.warrs]),
      ν,arrs_setVar] using hp
  have hroomμ:xs.length < (μ.arrs "vm.input").length:=by
    rw [RamFrames.run_array_length hhead "vm.input"]
    simpa only [ν,arrs_setVar] using hroom
  have hpre:Invariant xs (μ.setVar "frame.i" 0):=by
    simpa only [Invariant,Prefix,vars_setVar,String.reduceEq,if_true,if_false,
      arrs_setVar,List.take_zero,List.length_nil,List.nil_append,Nat.zero_add]
      using And.intro hposμ (And.intro (Nat.zero_le xs.length)
        (And.intro hpμ (And.intro hheadPost.1 (And.intro hheadPost.2 hroomμ))))
  obtain ⟨τ,hscan,hpost⟩:=hfinish μ hpre
  exact ⟨τ, (hzero.seq (hhead.seq hscan)).mono (by simp [Expr.size]; omega),hpost⟩

end Lax455465Proofs.RamLpInputFrame

end

section

namespace Lax455465Proofs.RamLpPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax759944.BinaryWordEncoding

theorem command_spec (B:ℕ) (coefficients:List ℕ) (xs:List ℕ) (h2:2 < B)
    (hlen:xs.length + 1 < B) (hsize:bitSize xs + 1 < B) (hwords:∀ x∈ xs,x < B)
    (hvalue:RamPolynomial.value coefficients (bitSize xs + 1) < B):
    Spec B (fun σ => Prefix xs "lp.word" σ∧ σ.vars "lp.position"=xs.length∧
      xs.length < (σ.arrs "vm.input").length) (command coefficients)
      (fun _ τ => τ.vars "vm.width"=RamPolynomial.value coefficients (bitSize xs)∧
        Prefix (xs.length::xs) "vm.input" τ∧ τ.vars "vm.inputLength"=xs.length + 1)
      ((12 * bitSize xs + 39) * xs.length + 6 * coefficients.length + 29):=by
  rintro σ ⟨hp,hpos,hroom⟩
  obtain ⟨ν,hcount,htotal⟩:=RamBitSize.array_spec B xs "lp.word" "lp.position"
    (by decide) h2 (by omega) hsize hwords σ ⟨hpos,hp⟩
  let δ:=ν.setVar "poly.argument" (bitSize xs)
  have harg:Run B (.assign "poly.argument" (.var "size.total")) ν δ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨htotal.symm,htotal ▸ (by omega:bitSize xs < B)⟩)
  obtain ⟨μ,hpoly,hpolyValue⟩:=RamPolynomial.command_spec B coefficients (bitSize xs)
    (by omega) (by omega) hvalue δ (by simp [δ])
  have hv:RamPolynomial.value coefficients (bitSize xs) < B:=
    (RamPolynomial.value_mono coefficients (show bitSize xs≤ bitSize xs + 1 by omega)).trans_lt hvalue
  let ε:=μ.setVar "vm.width" (RamPolynomial.value coefficients (bitSize xs))
  have hwidth:Run B (.assign "vm.width" (.var "poly.value")) μ ε 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hpolyValue.symm,hpolyValue ▸ hv⟩)
  have hpν:Prefix xs "lp.word" ν:=by
    simpa only [Prefix,hcount.frame_arr "lp.word" (by simp [RamBitSize.array,
      RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,Com.warrs])] using hp
  have hposν:=(hcount.frame_var "lp.position" (by simp [RamBitSize.array,RamBitSize.arrayStep,
    RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,Com.wvars])).trans hpos
  have hpμ:Prefix xs "lp.word" μ:=by
    simpa only [Prefix,hpoly.frame_arr "lp.word" (by simp [RamPolynomial.arrays_frame]),δ,arrs_setVar] using hpν
  have hposμ:=(hpoly.frame_var "lp.position" (RamPolynomial.variable_frame coefficients _ (by decide))).trans
    (show δ.vars "lp.position"=xs.length by simpa [δ] using hposν)
  have hpε:Prefix xs "lp.word" ε:=by simpa only [Prefix,ε,arrs_setVar] using hpμ
  have hposε:ε.vars "lp.position"=xs.length:=by simpa [ε] using hposμ
  have hroomε:xs.length < (ε.arrs "vm.input").length:=by
    rw [show ε.arrs "vm.input"=μ.arrs "vm.input" from rfl,
      RamFrames.run_array_length hpoly "vm.input",show δ.arrs "vm.input"=ν.arrs "vm.input" from rfl,
      RamFrames.run_array_length hcount "vm.input"]
    exact hroom
  obtain ⟨τ,hframe,hpost⟩:=RamLpInputFrame.command_spec B xs (by omega) hlen hwords ε ⟨hpε,hposε,hroomε⟩
  have hwτ:τ.vars "vm.width"=RamPolynomial.value coefficients (bitSize xs):=
    (hframe.frame_var "vm.width" (by simp [RamLpInputFrame.command,RamLpInputFrame.step,
      RamWordBuffer.append,Com.wvars])).trans (by simp [ε])
  refine ⟨τ, (hcount.seq (harg.seq (hpoly.seq (hwidth.seq hframe)))).mono ?_,hwτ,hpost⟩
  nlinarith

end Lax455465Proofs.RamLpPrepare

end

section

namespace Lax455465Proofs.RegisteredLpInvocation

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def command (p:Lax808846.Ram.Program) (coefficients:List ℕ):Com:=
  .seq (RamLpPrepare.command coefficients) (RamVirtualProgram.execute p)

theorem exists_program:
    ∃ (p:Lax808846.Ram.Program) (wordBound timeBound:Polynomial ℕ) (coefficients:List ℕ),
      (∀ x:ℕ,RamPolynomial.value coefficients x=wordBound.eval x)∧
      ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
        IsValidCertificate P certificate∧
        FitsInWords (wordBound.eval (bitSize (encodeProgram P)))
          (((encodeProgram P).length::encodeProgram P) ++ encodeCertificate certificate)∧
        ∀ B:ℕ,
          bitSize (encodeProgram P) + 1 < B→
          wordBound.eval (bitSize (encodeProgram P) + 1) < B→
          2 * (2 ^ wordBound.eval (bitSize (encodeProgram P))) ^ 2 + 3 < B→
          timeBound.eval (bitSize (encodeProgram P)) + 1 < B→
          RamVirtualConstants.allowance p < B→
          Spec B (fun σ => Prefix (encodeProgram P) "lp.word" σ∧
            σ.vars "lp.position"=(encodeProgram P).length∧
            (encodeProgram P).length < (σ.arrs "vm.input").length∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.addresses").length∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.values").length∧
            timeBound.eval (bitSize (encodeProgram P)) < (σ.arrs "vm.output").length)
            (command p coefficients)
            (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ∧
              τ.vars "vm.outputLength"=(encodeCertificate certificate).length∧
              τ.vars "vm.running"=0)
            (((12 * bitSize (encodeProgram P) + 39) * (encodeProgram P).length +
                6 * coefficients.length + 29) +
              ((timeBound.eval (bitSize (encodeProgram P)) + 1) *
                (4 * p.length + 32 * timeBound.eval (bitSize (encodeProgram P)) + 104) + 18)):=by
  obtain ⟨p,wordBound,timeBound,hnative⟩:=RegisteredLpNative.exists_program
  obtain ⟨coefficients,hcoeff⟩:=RamPolynomial.exists_coefficients wordBound
  refine ⟨p,wordBound,timeBound,coefficients,hcoeff, ?_⟩
  intro m n P
  obtain ⟨certificate,hvalid,hfit,hrun⟩:=hnative m n P
  refine ⟨certificate,hvalid,hfit, ?_⟩
  intro B hsize hpoly hB htime hallow
  let w:=wordBound.eval (bitSize (encodeProgram P))
  let T:=timeBound.eval (bitSize (encodeProgram P))
  have hM:2 ^ w < B:=by nlinarith [Nat.two_pow_pos w]
  have hlenWord:(encodeProgram P).length < 2 ^ w:=
    hfit _ (List.mem_append_left _ List.mem_cons_self)
  have hlen:(encodeProgram P).length + 1 < B:=by omega
  have hwords:∀ x∈ encodeProgram P,x < B:=fun x hx =>
    (hfit x (List.mem_append_left _ (List.mem_cons_of_mem _ hx))).trans hM
  have hprepare:=RamLpPrepare.command_spec B coefficients (encodeProgram P) (by omega)
    hlen hsize hwords (by simpa only [hcoeff] using hpoly)
  rintro σ ⟨hp,hpos,hinputRoom,hA,hV,hO⟩
  obtain ⟨ν,hprep,hprepared⟩:=hprepare σ ⟨hp,hpos,hinputRoom⟩
  have hAν:T < (ν.arrs "vm.addresses").length:=by
    rwa [RamFrames.run_array_length hprep "vm.addresses"]
  have hVν:T < (ν.arrs "vm.values").length:=by
    rwa [RamFrames.run_array_length hprep "vm.values"]
  have hOν:T < (ν.arrs "vm.output").length:=by
    rwa [RamFrames.run_array_length hprep "vm.output"]
  obtain ⟨τ,hsolve,hpost⟩:=hrun B hB htime hallow ν
    ⟨by simpa only [hcoeff] using hprepared.1,hprepared.2.1,hprepared.2.2,hAν,hVν,hOν⟩
  exact ⟨τ,hprep.seq hsolve,hpost⟩

end Lax455465Proofs.RegisteredLpInvocation

end

section

namespace Lax455465Proofs.RamFlowLpSolver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP RamFlowData
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

def command (p:Lax808846.Ram.Program) (coefficients:List ℕ):Com:=
  .seq RamFlowLp.command (RegisteredLpInvocation.command p coefficients)

def BuildFits (B M n:ℕ):Prop:=
  1≤ M∧ 2*M^2+3 < B∧ 2*n+1 < B∧ n*n < B∧ (n*n)*n < B∧
    rows n < B∧ columns n < B∧ rows n*columns n < B∧ 2*(n*n)+1 < B∧ RamFlowLp.wordLength n+3 < B

def InvokeFits (B:ℕ) (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ) (s:ℕ):Prop:=
  s+1 < B∧ WB.eval (s+1) < B∧ 2*(2^WB.eval s)^2+3 < B∧ TB.eval s+1 < B∧
    RamVirtualConstants.allowance p < B

def invocationCost (p:Lax808846.Ram.Program) (coefficients:List ℕ) (TB:Polynomial ℕ)
    (s len:ℕ):ℕ:=
  ((12*s+39)*len+6*coefficients.length+29)+((TB.eval s+1)*(4*p.length+32*TB.eval s+104)+18)

theorem exists_program:
    ∃ (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ) (coefficients:List ℕ),
      ∀ {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n),
        ∃ certificate:Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate∧
          FitsInWords (WB.eval (bitSize (encodeProgram (program I)))) (encodeCertificate certificate)∧
          ∀ (B M:ℕ),BuildFits B M n→
            InvokeFits B p WB TB (bitSize (encodeProgram (program I)))→
            (∀ z, (I.weight z).num≤ M)→ (∀ z, (I.weight z).den≤ M)→
            (∀ u v, (I.capacity u v).num≤ M)→ (∀ u v, (I.capacity u v).den≤ M)→
            Spec B (fun σ => Data I σ∧ RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.output").length)
              (command p coefficients)
              (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ∧
                τ.vars "vm.outputLength"=(encodeCertificate certificate).length∧ τ.vars "vm.running"=0)
              (RamFlowLp.cost n M+invocationCost p coefficients TB
                (bitSize (encodeProgram (program I))) (encodeProgram (program I)).length):=by
  obtain ⟨p,WB,TB,coefficients,hcoeff,hinvoke⟩:=RegisteredLpInvocation.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n I
  obtain ⟨certificate,hvalid,hfit,hsolve⟩:=hinvoke (rows n) (columns n) (program I)
  refine ⟨certificate,hvalid,fun x hx => hfit x (List.mem_append_right _ hx),?_⟩
  rintro B M ⟨hM,hB,hni,hn2,hn3,hr,hc,hm,hcapindex,hlen⟩
    ⟨hsize,hpoly,hvirtual,htime,hallow⟩ hnum hden hcapnum hcapden
  rintro σ ⟨hdata,hroom,hinputRoom,hA,hV,hO⟩
  obtain ⟨ν,hbuild,hbuilt⟩:=RamFlowLp.command_spec B M I hM hB hni hn2 hn3 hr hc hm hcapindex hlen
    hnum hden hcapnum hcapden σ ⟨hdata,hroom⟩
  have hinputν:(encodeProgram (program I)).length < (ν.arrs "vm.input").length:=by
    rwa [RamFrames.run_array_length hbuild "vm.input"]
  have hAν:TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.addresses").length:=by
    rwa [RamFrames.run_array_length hbuild "vm.addresses"]
  have hVν:TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.values").length:=by
    rwa [RamFrames.run_array_length hbuild "vm.values"]
  have hOν:TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.output").length:=by
    rwa [RamFrames.run_array_length hbuild "vm.output"]
  obtain ⟨τ,hrun,hpost⟩:=hsolve B hsize hpoly hvirtual htime hallow ν
    ⟨hbuilt.2.1,hbuilt.2.2,hinputν,hAν,hVν,hOν⟩
  exact ⟨τ,hbuild.seq hrun,hpost⟩

end Lax455465Proofs.RamFlowLpSolver

end

section

namespace Lax455465Proofs.RamFlowLpBounds

open RamFlowData

theorem cost_bound (n L:ℕ) (hn:n≤ L):
    RamFlowLp.cost n (2^L)≤ 10000*(L+1)^8:=by
  let a:=L+1
  have ha:1≤ a:=by omega
  have hnA:n≤ a:=by omega
  have hsz:((2^L)*(2^L)).size=2*L+1:=by
    rw [←pow_add,Nat.size_pow]
    omega
  have hn2:n*n≤ a^2:=by nlinarith
  have hn3:(n*n)*n≤ a^3:=by
    calc _≤ a^2*a:=Nat.mul_le_mul hn2 hnA
         _=a^3:=by ring
  have hn4:(n*n)*(n*n)≤ a^4:=by
    calc _≤ a^2*a^2:=Nat.mul_le_mul hn2 hn2
         _=a^4:=by ring
  have ha23:a^2≤ a^3:=by exact Nat.pow_le_pow_right ha (by decide)
  have hrows:rows n≤ 3*a^3:=by dsimp only [rows]; omega
  have hcols:columns n≤ 2*a^4:=by
    have ha4:1≤ a^4:=by have:=pow_pos (by omega:0< a) 4; omega
    dsimp only [columns]; omega
  have hmatrix:rows n*columns n≤ 6*a^7:=by
    calc _≤ (3*a^3)*(2*a^4):=Nat.mul_le_mul hrows hcols
         _=6*a^7:=by ring
  have hfactor:36*((2^L)*(2^L)).size+239≤ 400*a:=by rw [hsz]; omega
  have hmain:(36*((2^L)*(2^L)).size+239)*(rows n*columns n)≤ 2400*a^8:=by
    calc _≤ (400*a)*(6*a^7):=Nat.mul_le_mul hfactor hmatrix
         _=2400*a^8:=by ring
  have ha38:a^3≤ a^8:=Nat.pow_le_pow_right ha (by decide)
  have ha48:a^4≤ a^8:=Nat.pow_le_pow_right ha (by decide)
  have ha8:1≤ a^8:=by have:=pow_pos (by omega:0< a) 8; omega
  have hrow8:rows n≤ 3*a^8:=by omega
  have hcol8:columns n≤ 2*a^8:=by omega
  change (36*((2^L)*(2^L)).size+239)*(rows n*columns n)+53*rows n+45*columns n+34≤ 10000*a^8
  omega

end Lax455465Proofs.RamFlowLpBounds

end

section

namespace Lax455465Proofs.RamFlowSolverBounds

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding DirectedFlowLP

theorem eval_mono (p:Polynomial ℕ) {x y:ℕ} (h:x≤ y):p.eval x≤ p.eval y:=by
  obtain ⟨coefficients,hcoeff⟩:=RamPolynomial.exists_coefficients p
  rw [←hcoeff x,←hcoeff y]
  exact RamPolynomial.value_mono coefficients h

noncomputable def timeBound (p:Lax808846.Ram.Program) (coefficients:List ℕ) (TB:Polynomial ℕ):Polynomial ℕ:=
  let S:=LpInputSize.sizeBound
  let T:=TB.comp S
  Polynomial.C 10000*(Polynomial.X+Polynomial.C 1)^8 +
    (Polynomial.C 12*S+Polynomial.C 39)*S+Polynomial.C (6*coefficients.length+29)+
    (T+Polynomial.C 1)*(Polynomial.C (4*p.length+104)+Polynomial.C 32*T)+Polynomial.C 18

theorem timeBound_eval (p:Lax808846.Ram.Program) (coefficients:List ℕ) (TB:Polynomial ℕ) (L:ℕ):
    (timeBound p coefficients TB).eval L=10000*(L+1)^8+
      (12*LpInputSize.sizeBound.eval L+39)*LpInputSize.sizeBound.eval L+6*coefficients.length+29+
      (TB.eval (LpInputSize.sizeBound.eval L)+1)*(4*p.length+32*TB.eval (LpInputSize.sizeBound.eval L)+104)+18:=by
  simp [timeBound,Polynomial.eval_comp]
  ring

theorem cost_bound (p:Lax808846.Ram.Program) (coefficients:List ℕ) (TB:Polynomial ℕ)
    {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:RationalInstance n):
    let L:=bitSize (encodeInput kind I)
    RamFlowLp.cost n (2^L)+RamFlowLpSolver.invocationCost p coefficients TB
      (bitSize (Lax109476.RationalEncoding.encodeProgram (program I)))
      (Lax109476.RationalEncoding.encodeProgram (program I)).length≤ (timeBound p coefficients TB).eval L:=by
  let L:=bitSize (encodeInput kind I)
  let s:=bitSize (Lax109476.RationalEncoding.encodeProgram (program I))
  let S:=LpInputSize.sizeBound.eval L
  have hs:s≤ S:=LpInputSize.flow_program_polynomial_size kind I
  have hlen:(Lax109476.RationalEncoding.encodeProgram (program I)).length≤ S:=
    (WordSize.length_le _).trans hs
  have hT:TB.eval s≤ TB.eval S:=eval_mono TB hs
  have hsize:(12*s+39)*(Lax109476.RationalEncoding.encodeProgram (program I)).length≤ (12*S+39)*S:=
    Nat.mul_le_mul (by omega) hlen
  have hsimulation:(TB.eval s+1)*(4*p.length+32*TB.eval s+104)≤
      (TB.eval S+1)*(4*p.length+32*TB.eval S+104):=Nat.mul_le_mul (by omega) (by omega)
  have hbuild:=RamFlowLpBounds.cost_bound n L (LpInputSize.input_dimension kind I)
  change RamFlowLp.cost n (2^L)+RamFlowLpSolver.invocationCost p coefficients TB s
    (Lax109476.RationalEncoding.encodeProgram (program I)).length≤ (timeBound p coefficients TB).eval L
  rw [timeBound_eval]
  dsimp only [RamFlowLpSolver.invocationCost]
  dsimp only [S] at hsize hsimulation
  omega

end Lax455465Proofs.RamFlowSolverBounds

end

section

namespace Lax455465Proofs.FlowEncodingSizes

open Lax109476.LinearProgram Lax109476.RationalEncoding

theorem program_length {m n:ℕ} (P:Program ℚ m n):
    (encodeProgram P).length=2+3*(m*n+m+n):=by
  unfold encodeProgram
  rw [←FlowLpMatrixList.values_eq]
  change ([m,n] ++ RamVectorEncoding.encode (FlowLpMatrixList.values P) ++
    RamVectorEncoding.encode (List.ofFn P.b) ++ RamVectorEncoding.encode (List.ofFn P.c)).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
    FlowLpMatrixList.values,List.length_ofFn]
  ring

theorem flow_length {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n):
    (encodeProgram (DirectedFlowLP.program I)).length=RamFlowLp.wordLength n:=program_length _

end Lax455465Proofs.FlowEncodingSizes

end

section

namespace Lax455465Proofs.RamHostBounds

theorem sufficient_bounds (w time allowance inputLength W:ℕ)
    (hW:sufficient w time allowance inputLength≤ W):
    2 * (2 ^ w) ^ 2 + 3 < 2 ^ W∧ time + 1 < 2 ^ W∧
      allowance < 2 ^ W∧ inputLength + 1 < 2 ^ W:=by
  have hshift:2 * w + 4≤ W:=by unfold sufficient at hW; omega
  have hpow:=Nat.pow_le_pow_right (show 1≤ 2 by decide) hshift
  have heq:2 ^ (2 * w + 4)=16 * (2 ^ w) ^ 2:=by
    rw [pow_add,show 2 * w=w + w by omega,pow_add]
    ring
  rw [heq] at hpow
  have hpos:=Nat.two_pow_pos w
  refine ⟨by nlinarith, ?_, ?_, ?_⟩
  · have ht:time + 1≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) ht)
  · have hc:allowance≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hc)
  · have hl:inputLength + 1≤ W:=by unfold sufficient at hW; omega
    exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hl)

end Lax455465Proofs.RamHostBounds

end

section

namespace Lax455465Proofs.RamFlowHostWidth

open Lax759944.BinaryWordEncoding Lax455465.RationalEncoding DirectedFlowLP RamFlowData

noncomputable def wordBound (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ):Polynomial ℕ:=
  let S:=LpInputSize.sizeBound
  Polynomial.C 2*(Polynomial.X+WB.comp (S+Polynomial.C 1)) + TB.comp S +
    Polynomial.C (RamVirtualConstants.allowance p) + S + Polynomial.C 11

theorem wordBound_eval (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ) (L:ℕ):
    (wordBound p WB TB).eval L =
      RamHostBounds.sufficient (L+WB.eval (LpInputSize.sizeBound.eval L+1))
        (TB.eval (LpInputSize.sizeBound.eval L)) (RamVirtualConstants.allowance p)
        (LpInputSize.sizeBound.eval L+3):=by
  simp [wordBound,Polynomial.eval_comp,RamHostBounds.sufficient]
  ring

theorem sufficient (p:Lax808846.Ram.Program) (WB TB:Polynomial ℕ)
    {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:RationalInstance n) (W:ℕ)
    (hW:(wordBound p WB TB).eval (bitSize (encodeInput kind I))≤ W):
    let L:=bitSize (encodeInput kind I)
    RamFlowLpSolver.BuildFits (2^W) (2^L) n∧
      RamFlowLpSolver.InvokeFits (2^W) p WB TB
        (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))):=by
  let L:=bitSize (encodeInput kind I)
  let s:=bitSize (Lax109476.RationalEncoding.encodeProgram (program I))
  let S:=LpInputSize.sizeBound.eval L
  let w:=L+WB.eval (S+1)
  change RamFlowLpSolver.BuildFits (2^W) (2^L) n∧ RamFlowLpSolver.InvokeFits (2^W) p WB TB s
  have hs:s≤ S:=LpInputSize.flow_program_polynomial_size kind I
  have hword:RamFlowLp.wordLength n≤ S:=by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans hs
  have hW':RamHostBounds.sufficient w (TB.eval S) (RamVirtualConstants.allowance p) (S+3)≤ W:=by
    simpa only [wordBound_eval] using hW
  obtain ⟨hvirtual,hT,hallow,hsize⟩:=RamHostBounds.sufficient_bounds w (TB.eval S)
    (RamVirtualConstants.allowance p) (S+3) W hW'
  have hwW:w≤ W:=by dsimp only [RamHostBounds.sufficient] at hW'; omega
  have hwB:w < 2^W:=Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) hwW)
  have hLP:WB.eval s≤ w:=by
    have:=RamFlowSolverBounds.eval_mono WB (show s≤ S+1 by omega); dsimp only [w]; omega
  have hLPnext:WB.eval (s+1)≤ w:=by
    have:=RamFlowSolverBounds.eval_mono WB (show s+1≤ S+1 by omega); dsimp only [w]; omega
  have hpLP:2^WB.eval s≤ 2^w:=Nat.pow_le_pow_right (by decide) hLP
  have hTmono:=RamFlowSolverBounds.eval_mono TB hs
  have hL:L≤ w:=by dsimp only [w]; omega
  have hpL:2^L≤ 2^w:=Nat.pow_le_pow_right (by decide) hL
  have hbuildWord:2*(2^L)^2+3 < 2^W:=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpL 2)) 3).trans_lt hvirtual
  have hlpWord:2*(2^WB.eval s)^2+3 < 2^W:=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpLP 2)) 3).trans_lt hvirtual
  have hrows:rows n≤ S:=by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hcols:columns n≤ S:=by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hmatrix:rows n*columns n≤ S:=by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hn2:n*n≤ rows n:=by dsimp only [rows]; omega
  have hn3:(n*n)*n≤ rows n:=by dsimp only [rows]; omega
  have hcap:2*(n*n)+1≤ S+3:=by dsimp only [RamFlowLp.wordLength] at hword; omega
  have hni:2*n+1≤ S+3:=by
    have hnn:n≤ n*n+1:=by nlinarith
    dsimp only [RamFlowLp.wordLength] at hword; omega
  refine ⟨?_,?_⟩
  · exact ⟨Nat.succ_le_iff.mpr (Nat.two_pow_pos L),hbuildWord,hni.trans_lt (by omega),
      (hn2.trans hrows).trans_lt (by omega),(hn3.trans hrows).trans_lt (by omega),
      hrows.trans_lt (by omega),hcols.trans_lt (by omega),hmatrix.trans_lt (by omega),
      hcap.trans_lt (by omega),by omega⟩
  · exact ⟨by omega,hLPnext.trans_lt hwB,hlpWord,(Nat.add_le_add_right hTmono 1).trans_lt hT,hallow⟩

end Lax455465Proofs.RamFlowHostWidth

end

section

namespace Lax455465Proofs.RamLpScope

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def protectedVars:List String:=
  ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength","flow.kind","input.length"]
def arrays:List String:= ["input.data","flow.weights","flow.capacities"]

theorem instruction_vars (i:Lax808846.Ram.Instr) (x:String) (hx:x∈ protectedVars):
    x∉ (RamVirtualProgram.instruction i).wvars:=by
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars,Com.warrs] <;> decide

theorem instruction_arrays (i:Lax808846.Ram.Instr) (a:String) (ha:a∈ arrays):
    a∉ (RamVirtualProgram.instruction i).warrs:=by
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;> cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars,Com.warrs] <;> decide

theorem dispatch_vars (p:List Lax808846.Ram.Instr) (offset:ℕ) (x:String) (hx:x∈ protectedVars):
    x∉ (RamVirtualProgram.dispatch p offset).wvars:=by
  induction p generalizing offset with
  | nil =>
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars] <;> decide
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨instruction_vars i x hx,ih (offset+1)⟩

theorem dispatch_arrays (p:List Lax808846.Ram.Instr) (offset:ℕ) (a:String) (ha:a∈ arrays):
    a∉ (RamVirtualProgram.dispatch p offset).warrs:=by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simp only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or]
    exact ⟨instruction_arrays i a ha,ih (offset+1)⟩

theorem execute_vars (p:Lax808846.Ram.Program) (x:String) (hx:x∈ protectedVars):
    x∉ (RamVirtualProgram.execute p).wvars:=by
  have hdispatch:=dispatch_vars p 0 x hx
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [RamVirtualProgram.execute,RamVirtualProgram.initCommand,RamWordOps.modulus,Com.wvars] using hdispatch

theorem execute_arrays (p:Lax808846.Ram.Program) (a:String) (ha:a∈ arrays):
    a∉ (RamVirtualProgram.execute p).warrs:=by
  simpa [RamVirtualProgram.execute,RamVirtualProgram.initCommand,RamWordOps.modulus,Com.warrs]
    using dispatch_arrays p 0 a ha

theorem prepare_vars (coefficients:List ℕ) (x:String) (hx:x∈ protectedVars):
    x∉ (RamLpPrepare.command coefficients).wvars:=by
  have hxp:x ≠ "poly.value" :=by
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hp:=RamPolynomial.variable_frame coefficients x hxp
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
      RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.wvars] using hp

theorem prepare_arrays (coefficients:List ℕ) (a:String) (ha:a∈ arrays):
    a∉ (RamLpPrepare.command coefficients).warrs:=by
  have hp:=RamPolynomial.arrays_frame coefficients
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;>
    simp [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
      RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.warrs,hp]

theorem invocation_vars (p:Lax808846.Ram.Program) (coefficients:List ℕ) (x:String) (hx:x∈ protectedVars):
    x∉ (RegisteredLpInvocation.command p coefficients).wvars:=by
  simpa only [RegisteredLpInvocation.command,Com.wvars,List.mem_append,not_or] using
    And.intro (prepare_vars coefficients x hx) (execute_vars p x hx)

theorem invocation_arrays (p:Lax808846.Ram.Program) (coefficients:List ℕ) (a:String) (ha:a∈ arrays):
    a∉ (RegisteredLpInvocation.command p coefficients).warrs:=by
  simpa only [RegisteredLpInvocation.command,Com.warrs,List.mem_append,not_or] using
    And.intro (prepare_arrays coefficients a ha) (execute_arrays p a ha)

theorem build_vars (x:String) (hx:x∈ protectedVars):
    x∉ RamFlowLp.command.wvars:=by
  simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem build_arrays (a:String) (ha:a∈ arrays):
    a∉ RamFlowLp.command.warrs:=by
  simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl <;> decide

theorem solver_vars (p:Lax808846.Ram.Program) (coefficients:List ℕ)
    (x:String) (hx:x∈ protectedVars):
    x∉ (RamFlowLpSolver.command p coefficients).wvars:=by
  simpa only [RamFlowLpSolver.command,Com.wvars,List.mem_append,not_or] using
    And.intro (build_vars x hx) (invocation_vars p coefficients x hx)

theorem solver_arrays (p:Lax808846.Ram.Program) (coefficients:List ℕ)
    (a:String) (ha:a∈ arrays):
    a∉ (RamFlowLpSolver.command p coefficients).warrs:=by
  simpa only [RamFlowLpSolver.command,Com.warrs,List.mem_append,not_or] using
    And.intro (build_arrays a ha) (invocation_arrays p coefficients a ha)

theorem solver_data {B K:ℕ} {p:Lax808846.Ram.Program} {coefficients:List ℕ}
    {σ τ:Env} (hr:Run B (RamFlowLpSolver.command p coefficients) σ τ K)
    {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (h:RamFlowData.Data I σ):
    RamFlowData.Data I τ:=by
  apply RamFlowData.frame hr I h
  · intro a ha
    apply solver_arrays p coefficients a
    simp only [arrays]
    simp_all
  · intro x hx
    apply solver_vars p coefficients x
    simp only [protectedVars]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h <;> simp [h]

end Lax455465Proofs.RamLpScope

end

section

namespace Lax455465Proofs.RamLpNoWrite
open Lax808846Proofs.Imp

theorem instruction (i:Lax808846.Ram.Instr):(RamVirtualProgram.instruction i).NoWrite:=by
  cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.NoWrite] <;> decide

theorem dispatch (p:List Lax808846.Ram.Instr) (offset:ℕ):(RamVirtualProgram.dispatch p offset).NoWrite:=by
  induction p generalizing offset with
  | nil => trivial
  | cons i p ih => exact ⟨instruction i,ih (offset+1)⟩

theorem execute (p:Lax808846.Ram.Program):(RamVirtualProgram.execute p).NoWrite:=by
  exact ⟨by decide,by decide,dispatch p 0⟩

theorem polynomial (coefficients:List ℕ):(RamPolynomial.command coefficients).NoWrite:=by
  induction coefficients with
  | nil => trivial
  | cons a rest ih => exact ⟨ih,by trivial⟩

theorem prepare (coefficients:List ℕ):(RamLpPrepare.command coefficients).NoWrite:=by
  simpa [RamLpPrepare.command,RamBitSize.array,RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,
    RamBitSize.wordStep,RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,Com.NoWrite] using polynomial coefficients

theorem solver (p:Lax808846.Ram.Program) (coefficients:List ℕ):
    (RamFlowLpSolver.command p coefficients).NoWrite:=by
  exact ⟨by decide,prepare coefficients,execute p⟩

end Lax455465Proofs.RamLpNoWrite

end

section

namespace Lax455465Proofs.RamUniformFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP RamFlowData
open Lax455465.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime sourceWord:Polynomial ℕ),
      c.NoWrite∧ ∀ {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind) (I:RationalInstance n),
        ∃ certificate:Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate certificate)∧
          ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
            Spec (2^W) (fun σ => Data I σ∧ RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length)
              c (fun σ τ => Data I τ∧
                τ.vars "flow.kind"=σ.vars "flow.kind" ∧
                (∀ x∈ Lax109476.RationalEncoding.encodeCertificate certificate,x < 2^W)∧ Prefix (Lax109476.RationalEncoding.encodeCertificate certificate) "vm.output" τ∧
                τ.vars "vm.outputLength"=(Lax109476.RationalEncoding.encodeCertificate certificate).length∧
                τ.vars "vm.running"=0) (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨p,WB,TB,coefficients,hsolve⟩:=RamFlowLpSolver.exists_program
  refine ⟨RamFlowLpSolver.command p coefficients,RamFlowSolverBounds.timeBound p coefficients TB,
    RamFlowHostWidth.wordBound p WB TB,TB,WB,RamLpNoWrite.solver p coefficients,?_⟩
  intro n kind I
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩:=hsolve I
  refine ⟨certificate,hvalid,hfit,?_⟩
  intro W hW
  let L:=bitSize (encodeInput kind I)
  let M:=2^L
  obtain ⟨hbuildFits,hinvokeFits⟩:=RamFlowHostWidth.sufficient p WB TB kind I W hW
  have hnum:∀ z, (I.weight z).num≤ M:=fun z => by
    simpa only [NNRat.natAbs_num_coe] using (LpInputSize.weight_height kind I z).1
  have hden:∀ z, (I.weight z).den≤ M:=fun z => by
    simpa only [NNRat.den_coe] using (LpInputSize.weight_height kind I z).2
  have hcapnum:∀ u v, (I.capacity u v).num≤ M:=fun u v => by
    simpa only [NNRat.natAbs_num_coe] using (LpInputSize.capacity_height kind I u v).1
  have hcapden:∀ u v, (I.capacity u v).den≤ M:=fun u v => by
    simpa only [NNRat.den_coe] using (LpInputSize.capacity_height kind I u v).2
  have hbounded:=hcorrect (2^W) M hbuildFits hinvokeFits hnum hden hcapnum hcapden
  intro σ hpre
  obtain ⟨τ,hrun,hpost⟩:=hbounded σ hpre
  exact ⟨τ,hrun.mono (RamFlowSolverBounds.cost_bound p coefficients TB kind I),
    RamLpScope.solver_data hrun I hpre.1,
    hrun.frame_var "flow.kind" (RamLpScope.solver_vars p coefficients _ (by simp [RamLpScope.protectedVars])),
    fun x hx => lt_trans (hfit x hx) (by
      obtain ⟨_,_,hv,_,_⟩:=hinvokeFits
      nlinarith [Nat.two_pow_pos (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))]),hpost⟩

end Lax455465Proofs.RamUniformFlowLp

end

section

namespace Lax455465Proofs.RamFlowDimensions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def command:Com:=
  .seq (.assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")))
    (.seq (.assign "lp.n3" (.mul (.var "lp.n2") (.var "lp.n")))
      (.seq (.assign "lp.rows" (.add (.var "lp.n2") (.mul (.lit 2) (.var "lp.n3"))))
        (.assign "lp.columns" (.add (.lit 1) (.mul (.var "lp.n2") (.var "lp.n2"))))))

theorem command_spec (B n:ℕ) (h2:2 < B) (hn:n < B)
    (hn2:n*n < B) (hn3:(n*n)*n < B) (hrows:n*n+2*((n*n)*n) < B)
    (hcols:1+(n*n)*(n*n) < B):
    Spec B (fun σ => σ.vars "lp.n"=n) command
      (fun _ τ => τ.vars "lp.n"=n∧ τ.vars "lp.n2"=n*n∧
        τ.vars "lp.n3"=(n*n)*n∧ τ.vars "lp.rows"=n*n+2*((n*n)*n)∧
        τ.vars "lp.columns"=1+(n*n)*(n*n)) 20:=by
  have htwice:2*((n*n)*n) < B:=by omega
  have hn4:(n*n)*(n*n) < B:=by omega
  rintro σ hσ
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 n n; let c2:Nat→ Nat:=c0 c1; let c3:Nat:=c2 n; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c0 ((2:Nat)); let c6:Nat:=c4 c1 (c5 c3); let c7:Nat→ Nat:=c4 ((1:Nat)); let c8:Nat:=c7 (c2 c1); let c9:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.n") n) (And (@Eq Nat (Env.vars τ "lp.n2") c1) (And (@Eq Nat (Env.vars τ "lp.n3") c3) (And (@Eq Nat (Env.vars τ "lp.rows") c6) (@Eq Nat (Env.vars τ "lp.columns") c8))))) σ; let c10:Nat:=c0 (Env.vars σ "lp.n") (Env.vars σ "lp.n"); let c11:Env:=Env.setVar σ "lp.n2" c10; let c12:String→ Nat:=Env.vars c11; let c13:Nat:=c12 "lp.n2"; let c14:Nat:=c12 "lp.n"; let c15:Nat:=c0 c13 c14; let c16:Env:=Env.setVar c11 "lp.n3" c15; let c17:String→ Nat:=Env.vars c16; let c18:Nat:=c17 "lp.n2"; let c19:Nat:=c17 "lp.n3"; let c20:Nat:=c5 c19; let c21:Nat:=c4 c18 c20; let c22:Env:=Env.setVar c16 "lp.rows" c21; let c23:Nat:=Env.vars c22 "lp.n2"; let c24:Nat:=c0 c23 c23; let c25:Nat:=c7 c24; let c26:Env:=Env.setVar c22 "lp.columns" c25; let c27:Nat:=c7 (Expr.size (Expr.mul (Expr.var "lp.n") (Expr.var "lp.n"))); let c28:Nat:=c7 (Expr.size (Expr.mul (Expr.var "lp.n2") (Expr.var "lp.n"))); let c29:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "lp.n3"); let c30:Expr:=Expr.add (Expr.var "lp.n2") c29; let c31:Nat:=c7 (Expr.size c30); let c32:Expr:=Expr.add (Expr.lit ((1:Nat))) (Expr.mul (Expr.var "lp.n2") (Expr.var "lp.n2")); let c33:Nat:=c7 (Expr.size c32); let c34:Nat:=c4 c31 c33; let c35:Nat:=c4 c28 c34; let c36:Com:=Com.assign "lp.n3" (Expr.mul (Expr.var "lp.n2") (Expr.var "lp.n")); let c37:Com:=Com.assign "lp.rows" c30; let c38:Com:=Com.assign "lp.columns" c32; let c39:Com:=Com.seq c37 c38; let c40:String→ Nat:=Env.vars c26; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((20:Nat))) (c9 σ')) c26 (@And.intro (Run B command σ c26 ((20:Nat))) (c9 c26) (RunStep.mono B command σ c26 (c4 c27 c35) ((20:Nat)) (RunStep.seq B (Com.assign "lp.n2" (Expr.mul (Expr.var "lp.n") (Expr.var "lp.n"))) (Com.seq c36 c39) σ c11 c26 c27 c35 (RunStep.assign B σ "lp.n2" (Expr.mul (Expr.var "lp.n") (Expr.var "lp.n")) c10 (RunStep.eval_mul B σ (Expr.var "lp.n") (Expr.var "lp.n") (Env.vars σ "lp.n") (Env.vars σ "lp.n") (RunStep.eval_var B σ "lp.n" (?nAX_g6091_0_0_0)) (RunStep.eval_var B σ "lp.n" (?nAX_g6091_0_0_1)) ?_)) (RunStep.seq B c36 c39 c11 c16 c26 c28 c34 (RunStep.assign B c11 "lp.n3" (Expr.mul (Expr.var "lp.n2") (Expr.var "lp.n")) c15 (RunStep.eval_mul B c11 (Expr.var "lp.n2") (Expr.var "lp.n") c13 c14 (RunStep.eval_var B c11 "lp.n2" ?_) (RunStep.eval_var B c11 "lp.n" (?nAX_g6091_0_0_2)) ?_)) (RunStep.seq B c37 c38 c16 c22 c26 c31 c33 (RunStep.assign B c16 "lp.rows" c30 c21 (RunStep.eval_add B c16 (Expr.var "lp.n2") c29 c18 c20 (RunStep.eval_var B c16 "lp.n2" ?_) (RunStep.eval_mul B c16 (Expr.lit ((2:Nat))) (Expr.var "lp.n3") ((2:Nat)) c19 (RunStep.eval_lit B ((2:Nat)) c16 h2) (RunStep.eval_var B c16 "lp.n3" ?_) ?_) ?_)) (RunStep.assign B c22 "lp.columns" c32 c25 (RunStep.eval_add B c22 (Expr.lit ((1:Nat))) (Expr.mul (Expr.var "lp.n2") (Expr.var "lp.n2")) ((1:Nat)) c24 (RunStep.eval_lit B ((1:Nat)) c22 (?nAX_g6091_0_0_3)) (RunStep.eval_mul B c22 (Expr.var "lp.n2") (Expr.var "lp.n2") c23 c23 (RunStep.eval_var B c22 "lp.n2" ?_) (RunStep.eval_var B c22 "lp.n2" ?_) ?_) ?_))))) (?nAX_g6091_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6091_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6091_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6091_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6091_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6091_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

end Lax455465Proofs.RamFlowDimensions

end

section

namespace Lax455465Proofs.RamGraphDimensions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamFlowData

def Dimensions (n:ℕ) (σ:Env):Prop:=
  σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n*n∧ σ.vars "lp.n3"=(n*n)*n∧
    σ.vars "lp.rows"=rows n∧ σ.vars "lp.columns"=columns n∧
    σ.vars "lp.matrixLength"=rows n*columns n

def command:Com:=.seq RamFlowDimensions.command
  (.assign "lp.matrixLength" (.mul (.var "lp.rows") (.var "lp.columns")))

theorem command_spec (B n:ℕ) (h2:2 < B) (hn:n < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B):
    Spec B (fun σ => σ.vars "lp.n"=n) command (fun _ τ => Dimensions n τ) 24:=by
  rintro σ hN
  obtain ⟨ν,hdims,hpost⟩:=RamFlowDimensions.command_spec B n h2 hn hn2 hn3 hr hc σ hN
  have he:(Expr.mul (.var "lp.rows") (.var "lp.columns")).evalB B ν=some (rows n*columns n):=
    evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hpost.2.2.2.1.symm,hpost.2.2.2.1 ▸ hr⟩)
      (by rw [evalB_var_iff]; exact ⟨hpost.2.2.2.2.symm,hpost.2.2.2.2 ▸ hc⟩) hm
  refine ⟨ν.setVar "lp.matrixLength" (rows n*columns n),hdims.seq (Run.assign he),?_,?_,?_,?_,?_,?_⟩
  all_goals simp only [vars_setVar,String.reduceEq,if_false,if_true]
  all_goals first | assumption | rfl | exact hpost.1 | exact hpost.2.1 | exact hpost.2.2.1 | exact hpost.2.2.2.1 | exact hpost.2.2.2.2

theorem frame {B K:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ K) (n:ℕ) (h:Dimensions n σ)
    (hx:∀ x∈ ["lp.n","lp.n2","lp.n3","lp.rows","lp.columns","lp.matrixLength"],x∉ c.wvars):
    Dimensions n τ:=by
  have hn:=hr.frame_var "lp.n" (hx _ (by simp))
  have hn2:=hr.frame_var "lp.n2" (hx _ (by simp))
  have hn3:=hr.frame_var "lp.n3" (hx _ (by simp))
  have hrows:=hr.frame_var "lp.rows" (hx _ (by simp))
  have hcols:=hr.frame_var "lp.columns" (hx _ (by simp))
  have htotal:=hr.frame_var "lp.matrixLength" (hx _ (by simp))
  simpa only [Dimensions,hn,hn2,hn3,hrows,hcols,htotal] using h

end Lax455465Proofs.RamGraphDimensions

end

section

namespace Lax455465Proofs.FlowInputLists

open DirectedFlowLP FlowLpIndices RamFlowData

theorem capacity_flat {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n):
    capacities I=(List.ofFn fun u => List.ofFn (I.capacity u)).flatten:=by
  unfold capacities
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have huv:u.val*n+v.val < n*n:=calc
    _ < (u.val+1)*n:=by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left v.isLt _
    _≤ n*n:=Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr u.isLt)
  have he:(⟨u.val*n+v.val,huv⟩:Fin (n*n))=edgeIndex n (u,v):=by
    apply Fin.ext
    rw [edge_value]
  rw [he]
  simp only [Equiv.symm_apply_apply]

theorem input_eq {n:ℕ} (kind:Lax455465.ProductNetwork.EdgeKind)
    (I:Lax455465.RationalEncoding.RationalInstance n):
    Lax455465.RationalEncoding.encodeInput kind I =
      [match kind with | .undirected => 0 | .directed => 1,n] ++
        (RamUnsignedBuffer.encode (List.ofFn I.weight) ++ RamUnsignedBuffer.encode (capacities I)):=by
  simp only [Lax455465.RationalEncoding.encodeInput,RamUnsignedBuffer.encode,capacity_flat,List.append_assoc]
  rfl

end Lax455465Proofs.FlowInputLists

end

section

namespace Lax455465Proofs.RamGraphHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork

def command:Com:=.seq (.assign "flow.kind" (.get "input.data" (.lit 0)))
  (.seq (.assign "lp.n" (.get "input.data" (.lit 1))) RamGraphDimensions.command)

theorem command_spec (B:ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (h2:2 < B) (hn:n < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B):
    Spec B (Prefix (encodeInput kind I) "input.data") command
      (fun _ τ => Prefix (encodeInput kind I) "input.data" τ∧
        RamGraphDimensions.Dimensions n τ∧ τ.vars "flow.kind"=tag kind) 30:=by
  intro σ hp
  have hlen:2≤ (encodeInput kind I).length:=by
    simp only [encodeInput,List.length_append,List.length_cons,List.length_nil]; omega
  have ht:tag kind < B:=by cases kind <;> simp only [tag] <;> omega
  have hget0:(σ.arrs "input.data")[0]?=some (tag kind):=by
    have:=hp 0 (by omega)
    cases kind <;> simpa only [encodeInput,List.cons_append,List.nil_append,List.getElem_cons_zero,tag] using this
  have hget1:(σ.arrs "input.data")[1]?=some n:=by
    have:=hp 1 (by omega)
    simpa only [encodeInput,List.cons_append,List.nil_append,List.getElem_cons_succ,List.getElem_cons_zero] using this
  let ν:=σ.setVar "flow.kind" (tag kind)
  have hkind:Run B (.assign "flow.kind" (.get "input.data" (.lit 0))) σ ν 3:=
    Run.assign (evalB_get (evalB_lit (by omega)) hget0 ht)
  let μ:=ν.setVar "lp.n" n
  have hget1ν:(ν.arrs "input.data")[1]?=some n:=by simpa only [ν,arrs_setVar] using hget1
  have horder:Run B (.assign "lp.n" (.get "input.data" (.lit 1))) ν μ 3:=
    Run.assign (evalB_get (evalB_lit (by omega)) hget1ν hn)
  obtain ⟨τ,hdims,hpost⟩:=RamGraphDimensions.command_spec B n h2 hn hn2 hn3 hr hc hm μ (by simp [μ])
  have hpτ:Prefix (encodeInput kind I) "input.data" τ:=by
    simpa only [Prefix,hdims.frame_arr "input.data" (by decide),μ,ν,arrs_setVar] using hp
  have hkτ:τ.vars "flow.kind"=tag kind:=
    (hdims.frame_var "flow.kind" (by decide)).trans (by simp [μ,ν])
  exact ⟨τ,hkind.seq (horder.seq hdims),hpτ,hpost,hkτ⟩

end Lax455465Proofs.RamGraphHeader

end

section

namespace Lax455465Proofs.RamDecodeFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState

def normalize:Com:=.seq (.assign "rat.s" (.lit 0))
  (.ite (.eq (.var "rat.d") (.lit 0))
    (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1))) RamArithmetic.normalizeFraction)

theorem normalize_spec (B n d:ℕ) (h1:1 < B) (hn:n < B) (hd:d < B):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalize
      (fun _ τ => FractionOutput (NNRat.divNat n d:ℚ) τ) (36 * d.size + 22):=by
  by_cases hz:d=0
  · subst d
    have hzero:Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
        (fun _ τ => τ.vars "rat.n"=0∧ τ.vars "rat.d"=1) 4:=by
      (expose_names;
        (refine fun (σ:Env) (a:True) => let c0:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c1:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c2:Com:=Com.seq c0 c1; let c3:Env→ Nat→ Prop:=Run B c2 σ; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "rat.n") ((0:Nat))) (@Eq Nat (Env.vars τ "rat.d") ((1:Nat)))) σ; let c5:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c6:Env:=Env.setVar c5 "rat.d" ((1:Nat)); let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.lit ((0:Nat)))); let c10:Nat:=c8 (Expr.size (Expr.lit ((1:Nat)))); let c11:String→ Nat:=Env.vars c6; @Exists.intro Env (fun (σ':Env) => And (c3 σ' ((4:Nat))) (c4 σ')) c6 (@And.intro (c3 c6 ((4:Nat))) (c4 c6) (RunStep.mono B c2 σ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B c0 c1 σ c5 c6 c9 c10 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hd)) (RunStep.assign B c5 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c5 h1))) (?nAX_g6102_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6102_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp
    rintro σ ⟨hnum,hden⟩
    let ν:=σ.setVar "rat.s" 0
    have hfirst:Run B (.assign "rat.s" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
    obtain ⟨τ,hrun,hnτ,hdτ⟩:=hzero ν True.intro
    have hsτ:τ.vars "rat.s"=0:=(hrun.frame_var "rat.s" (by decide)).trans (by simp [ν])
    have hcond:(Cond.eq (.var "rat.d") (.lit 0)).evalB B ν=some true:=by
      rw [evalB_condEq_iff]
      exact ⟨0,0,by rw [evalB_var_iff]; simp [ν,hden]; omega,evalB_lit (by omega),by decide⟩
    refine ⟨τ, (hfirst.seq (Run.ite_true hcond hrun)).mono (by simp [Cond.size,Expr.size]), ?_⟩
    simp [FractionOutput,fractionValue,hnτ,hdτ,hsτ]

  · have hnorm:=normalizeFraction_output_spec B 0 n d (by omega) hn hd (Nat.pos_of_ne_zero hz)
    have hvalue:fractionValue 0 n d=(NNRat.divNat n d:ℚ):=by simp [fractionValue]
    rintro σ ⟨hnum,hden⟩
    (expose_names;
      (refine let c0:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c1:String→ Nat:=Env.vars c0; let c2:Nat:=c1 "rat.d"; let c3:Nat→ Prop:= @Eq Nat c2; let c4:Prop:=c3 ((0:Nat)); let c5:Prop:=Not c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (Nat.mul ((36:Nat)) (Nat.size d)); let c8:Nat:=c7 ((22:Nat)); let c9:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (NNRat.divNat n d)); let c10:Env→ Prop:=(fun (x τ:Env) => c9 τ) σ; let c11:Env→ Prop:=fun (σ':Env) => And (Run B normalize σ σ' c8) (c10 σ'); let c12:Prop:= @Exists Env c11; let c13:Env:=Env.setVar c0 "rat.n" ((0:Nat)); let c14:Env:=Env.setVar c13 "rat.d" ((1:Nat)); let c15:Nat→ Nat:=c6 ((1:Nat)); let c16:Nat:=c15 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat→ Nat:=c6 c16; let c18:Cond:=Cond.eq (Expr.var "rat.d") (Expr.lit ((0:Nat))); let c19:Nat→ Nat:=c6 (c15 (Cond.size c18)); let c20:Nat:=c15 (Expr.size (Expr.lit ((1:Nat)))); let c21:Nat:=c17 c20; let c22:Nat:=c19 c21; let c23:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c24:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c25:Com:=Com.seq c23 c24; let c26:Env→ Nat→ Prop:=Run B RamArithmetic.normalizeFraction c0; let c27:Nat:=c7 ((16:Nat)); let c28:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) n d); let c29:Env→ Prop:=fun (σ':Env) => And (c26 σ' c27) (c28 σ'); let c30:Nat:=c19 c27; @Or.casesOn c4 c5 (fun (x:Or c4 c5) => c12) (Classical.em c4) (fun (hcase:c4) => @Exists.intro Env c11 c14 (@And.intro (Run B normalize σ c14 c8) (c10 c14) (RunStep.mono B normalize σ c14 (c17 c22) c8 (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.ite c18 c25 RamArithmetic.normalizeFraction) σ c0 c14 c16 c22 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6102_1_0_0))) (RunStep.ite_true B c18 c25 RamArithmetic.normalizeFraction c0 c14 c21 (RunStep.cond_eq_true B c0 (Expr.var "rat.d") (Expr.lit ((0:Nat))) c2 ((0:Nat)) (RunStep.eval_var B c0 "rat.d" (?nAX_g6102_1_0_1)) (RunStep.eval_lit B ((0:Nat)) c0 (?nAX_g6102_1_0_2)) hcase) (RunStep.seq B c23 c24 c0 c13 c14 c16 c20 (RunStep.assign B c0 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c0 (?nAX_g6102_1_0_3))) (RunStep.assign B c13 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c13 h1))))) (?nAX_g6102_1_0_4)) ?_)) fun (hcase:c5) => @Exists.casesOn Env c29 (fun (x:@Exists Env c29) => c12) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") n) (And (@Eq Nat (Env.vars σ_1 "rat.d") d) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) RamArithmetic.normalizeFraction (fun (x σ':Env) => c28 σ') c27 hnorm c0 ?_) fun (w:Env) (h:And (c26 w c27) (c28 w)) => @And.casesOn (c26 w c27) (c28 w) (fun (x:And (c26 w c27) (c28 w)) => c12) h fun (left:c26 w c27) (right:c28 w) => @Exists.intro Env c11 w (@And.intro (Run B normalize σ w c8) (c10 w) (RunStep.mono B normalize σ w (c17 c30) c8 (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.ite c18 c25 RamArithmetic.normalizeFraction) σ c0 w c16 c30 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6102_1_0_5))) (RunStep.ite_false B c18 c25 RamArithmetic.normalizeFraction c0 w c27 (RunStep.cond_eq_false B c0 (Expr.var "rat.d") (Expr.lit ((0:Nat))) c2 ((0:Nat)) (RunStep.eval_var B c0 "rat.d" (?nAX_g6102_1_0_6)) (RunStep.eval_lit B ((0:Nat)) c0 (?nAX_g6102_1_0_7)) hcase) left)) (?nAX_g6102_1_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6102_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6102_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals simp_all

def pair:Com:=.seq (.assign "rat.n" (.get "input.data" (.var "decode.cursor")))
  (.seq (.assign "rat.d" (.get "input.data" (.add (.var "decode.cursor") (.lit 1))))
    (.seq normalize (.assign "decode.cursor" (.add (.var "decode.cursor") (.lit 2)))))

theorem pair_spec (B:ℕ) (words:List ℕ) (i:ℕ) (h2:2 < B)
    (hi:i + 1 < words.length) (hindex:i + 2 < B) (hwords:∀ x∈ words,x < B):
    Spec B (fun σ => Prefix words "input.data" σ∧ σ.vars "decode.cursor"=i) pair
      (fun _ τ => Prefix words "input.data" τ∧ τ.vars "decode.cursor"=i + 2∧
        FractionOutput (NNRat.divNat words[i] words[i + 1]:ℚ) τ)
      (36 * words[i + 1].size + 34):=by
  have hi0:i < words.length:=by omega
  have hn:=hwords words[i] (List.getElem_mem hi0)
  have hd:=hwords words[i + 1] (List.getElem_mem hi)
  have hnorm:=RamFrames.keep_scalar (normalize_spec B words[i] words[i + 1] (by omega) hn hd)
    "decode.cursor" i (by simp [normalize,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
      RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars])
  rintro σ ⟨hp,hcursor⟩
  have hgetN:=hp i hi0
  have hgetD:=hp (i + 1) hi
  have harray:i + 1 < (σ.arrs "input.data").length:=by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  have hfinish:Spec B (fun τ => FractionOutput (NNRat.divNat words[i] words[i + 1]:ℚ) τ∧
      τ.vars "decode.cursor"=i) (.assign "decode.cursor" (.add (.var "decode.cursor") (.lit 2)))
      (fun _ τ => τ.vars "decode.cursor"=i + 2∧
        FractionOutput (NNRat.divNat words[i] words[i + 1]:ℚ) τ) 4:=by
    rintro τ ⟨hf,hc⟩
    have he:(Expr.add (.var "decode.cursor") (.lit 2)).evalB B τ=some (i + 2):=by
      apply evalB_bin (op:=.add) _ (evalB_lit h2) hindex
      rw [evalB_var_iff]
      exact ⟨hc.symm,hc ▸ (by omega:i < B)⟩
    exact ⟨τ.setVar "decode.cursor" (i + 2),Run.assign he,by simp,
      by simpa only [FractionOutput,vars_setVar,String.reduceEq,if_false] using hf⟩

  obtain ⟨τ,hrun,hpost⟩:∃ τ,Run B pair σ τ (36 * words[i + 1].size + 34)∧
      τ.vars "decode.cursor"=i + 2∧ FractionOutput (NNRat.divNat words[i] words[i + 1]:ℚ) τ:=by
    (expose_names;
      (refine let c0:Nat:= @List.getD Nat (Env.arrs σ "input.data") (Env.vars σ "decode.cursor") ((0:Nat)); let c1:Env:=Env.setVar σ "rat.n" c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=Env.vars c1 "decode.cursor"; let c4:Nat:=c2 c3 ((1:Nat)); let c5:Nat:= @List.getD Nat (Env.arrs c1 "input.data") c4 ((0:Nat)); let c6:Env:=Env.setVar c1 "rat.d" c5; let c7:Env→ Nat→ Prop:=Run B normalize c6; let c8:(i_1:Nat)→ Nat.lt i_1 (@List.length Nat words)→ Nat:= @getElem (List Nat) Nat Nat (fun (as:List Nat) (i_1:Nat) => Nat.lt i_1 (@List.length Nat as)) (@List.instGetElemNatLtLength Nat) words; let c9:Nat→ Nat:=c2 i; let c10:Nat:=c8 (c9 ((1:Nat))) hi; let c11:Nat→ Nat:=c2 (Nat.mul ((36:Nat)) (Nat.size c10)); let c12:Nat:=c11 ((22:Nat)); let c13:Nat:=c8 i hi0; let c14:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (NNRat.divNat c13 c10)); let c15:Env→ Prop:=fun (σ':Env) => And (c7 σ' c12) (And (c14 σ') (@Eq Nat (Env.vars σ' "decode.cursor") i)); let c16:Nat:=c11 ((34:Nat)); let c17:Nat:=c9 ((2:Nat)); let c18:Env→ Prop:=fun (τ:Env) => And (Run B pair σ τ c16) (And (@Eq Nat (Env.vars τ "decode.cursor") c17) (c14 τ)); let c19:Prop:= @Exists Env c18; let c20:Env→ Prop:=fun (τ:Env) => And (c14 τ) (@Eq Nat (Env.vars τ "decode.cursor") i); let c21:String→ Nat:=Env.vars c6; let c22:Com:=Com.assign "decode.cursor" (Expr.add (Expr.var "decode.cursor") (Expr.lit ((2:Nat)))); let c23:Env→ Env→ Nat→ Prop:=Run B c22; let c24:Nat→ Nat:=c2 ((1:Nat)); let c25:Nat:=c24 (Expr.size (Expr.get "input.data" (Expr.var "decode.cursor"))); let c26:Expr:=Expr.add (Expr.var "decode.cursor") (Expr.lit ((1:Nat))); let c27:Expr:=Expr.get "input.data" c26; let c28:Nat:=c24 (Expr.size c27); let c29:Nat:=c2 c12 ((4:Nat)); let c30:Nat:=c2 c28 c29; let c31:Com:=Com.assign "rat.d" c27; let c32:Com:=Com.seq normalize c22; @Exists.casesOn Env c15 (fun (x:@Exists Env c15) => c19) (RunStep.use B (fun (σ_1:Env) => And (And (@Eq Nat (Env.vars σ_1 "rat.n") c13) (@Eq Nat (Env.vars σ_1 "rat.d") c10)) (@Eq Nat (Env.vars σ_1 "decode.cursor") i)) normalize (fun (σ_1:Env) => c20) c12 hnorm c6 ?_) fun (w:Env) (h:And (c7 w c12) (And (c14 w) (@Eq Nat (Env.vars w "decode.cursor") i))) => let c0_1:Prop:=And (c14 w) (@Eq Nat (Env.vars w "decode.cursor") i); let c1_1:Env→ Prop:=fun (σ':Env) => And (c23 w σ' ((4:Nat))) (And (@Eq Nat (Env.vars σ' "decode.cursor") c17) (c14 σ')); @And.casesOn (c7 w c12) c0_1 (fun (x:And (c7 w c12) c0_1) => c19) h fun (left:c7 w c12) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c19) (RunStep.use B c20 c22 (fun (x τ:Env) => And (@Eq Nat (Env.vars τ "decode.cursor") c17) (c14 τ)) ((4:Nat)) hfinish w ?_) fun (w_1:Env) (h_1:And (c23 w w_1 ((4:Nat))) (And (@Eq Nat (Env.vars w_1 "decode.cursor") c17) (c14 w_1))) => let c0_2:Prop:=c23 w w_1 ((4:Nat)); let c1_2:Prop:=And (@Eq Nat (Env.vars w_1 "decode.cursor") c17) (c14 w_1); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c19) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c18 w_1 (@And.intro (Run B pair σ w_1 c16) c1_2 (RunStep.mono B pair σ w_1 (c2 c25 c30) c16 (RunStep.seq B (Com.assign "rat.n" (Expr.get "input.data" (Expr.var "decode.cursor"))) (Com.seq c31 c32) σ c1 w_1 c25 c30 (RunStep.assign B σ "rat.n" (Expr.get "input.data" (Expr.var "decode.cursor")) c0 (RunStep.eval_get B σ "input.data" (Expr.var "decode.cursor") (Env.vars σ "decode.cursor") (RunStep.eval_var B σ "decode.cursor" (?nAX_g6104_0_0_0)) (?nAX_g6104_0_0_1) ?_)) (RunStep.seq B c31 c32 c1 c6 w_1 c28 c29 (RunStep.assign B c1 "rat.d" c27 c5 (RunStep.eval_get B c1 "input.data" c26 c4 (RunStep.eval_add B c1 (Expr.var "decode.cursor") (Expr.lit ((1:Nat))) c3 ((1:Nat)) (RunStep.eval_var B c1 "decode.cursor" (?nAX_g6104_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c1 (?nAX_g6104_0_0_3)) (?nAX_g6104_0_0_4)) (?nAX_g6104_0_0_5) ?_)) (RunStep.seq B normalize c22 c6 w w_1 c12 ((4:Nat)) left left_1))) (?nAX_g6104_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6104_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6104_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals simp_all
  have harr:=hrun.frame_arr "input.data" (by simp [pair,normalize,
    RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,
    RamArithmetic.gcdStep,Com.warrs])
  exact ⟨τ,hrun,by simpa only [Prefix,harr] using hp,hpost⟩

end Lax455465Proofs.RamDecodeFraction

end

section

namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B:ℕ) (array cursor:String) (q:ℚ≥0) (words:List ℕ) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B) (hlen:words.length+2 < B) (hfresh:cursor ≠ "rat.d"):
    Spec B (fun σ => FractionOutput (q:ℚ) σ∧ Prefix words array σ∧
      σ.vars cursor=words.length∧ words.length+1 < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (words ++ Lax455465.RationalEncoding.encodeRational q) array τ∧
        τ.vars cursor=words.length+2) 14:=by
  rintro σ ⟨hf,hp,hpos,hroom⟩
  have hnum:σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hf.2.1
  have hden:σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hf.2.2.1
  have hfirst:=RamFrames.keep_scalar
    (RamWordBuffer.append_spec B array cursor words q.num (.var "rat.n") h1 (by omega))
    "rat.d" q.den (by simp [RamWordBuffer.append,Com.wvars,Ne.symm hfresh])
  obtain ⟨ν,hrn,hnPost⟩:=hfirst σ ⟨⟨hp,hpos,by omega,
    by rw [evalB_var_iff]; exact ⟨hnum.symm,hnum ▸ hn⟩⟩,hden⟩
  have hroomν:(words ++ [q.num]).length < (ν.arrs array).length:=by
    rw [RamFrames.run_array_length hrn array,List.length_append,List.length_singleton]; exact hroom
  obtain ⟨τ,hrd,hdPost⟩:=RamWordBuffer.append_spec B array cursor (words ++ [q.num]) q.den (.var "rat.d") h1
    (by simp only [List.length_append,List.length_singleton]; omega) ν
      ⟨hnPost.1.1,by simpa only [List.length_append,List.length_singleton] using hnPost.1.2,hroomν,
        by rw [evalB_var_iff]; exact ⟨hnPost.2.symm,hnPost.2 ▸ hd⟩⟩
  refine ⟨τ,hrn.seq hrd,?_,?_⟩
  · simpa only [Lax455465.RationalEncoding.encodeRational,List.append_assoc,List.cons_append,List.nil_append] using hdPost.1
  · simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hdPost.2

end Lax455465Proofs.RamUnsignedEncoding

end

section

namespace Lax455465Proofs.RamInputSlice

open scoped NNRat

theorem numerator (front tail:List ℕ) (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (front ++ (RamUnsignedBuffer.encode qs ++ tail))[front.length+2*i]?=some qs[i].num:=by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [RamUnsignedBuffer.length_encode]; omega)]
  exact RamUnsignedBuffer.numerator_at qs i hi

theorem denominator (front tail:List ℕ) (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    (front ++ (RamUnsignedBuffer.encode qs ++ tail))[front.length+2*i+1]?=some qs[i].den:=by
  rw [List.getElem?_append_right (by omega),show front.length+2*i+1-front.length=2*i+1 by omega,
    List.getElem?_append_left (by rw [RamUnsignedBuffer.length_encode]; omega)]
  exact RamUnsignedBuffer.denominator_at qs i hi

theorem index_bound (front tail:List ℕ) (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    front.length+2*i+1 < (front ++ (RamUnsignedBuffer.encode qs ++ tail)).length:=by
  simp only [List.length_append,RamUnsignedBuffer.length_encode]
  omega

end Lax455465Proofs.RamInputSlice

end

section

namespace Lax455465Proofs.RamDecodeVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def step (array cursor:String):Com:=.seq RamDecodeFraction.pair
  (.seq (RamUnsignedEncoding.command array cursor)
    (.assign "decode.i" (.add (.var "decode.i") (.lit 1))))

def command (array cursor:String):Com:=.seq (.assign cursor (.lit 0))
  (.seq (.assign "decode.i" (.lit 0))
    (.while (.lt (.var "decode.i") (.var "decode.count")) (step array cursor)))

def Invariant (front tail:List ℕ) (qs:List ℚ≥0) (array cursor:String) (σ:Env):Prop:=
  Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" σ∧
    σ.vars "decode.count"=qs.length∧ σ.vars "decode.i" ≤ qs.length∧
    σ.vars "decode.cursor"=front.length+2*σ.vars "decode.i" ∧
    Prefix (RamUnsignedBuffer.encode (qs.take (σ.vars "decode.i"))) array σ∧
    σ.vars cursor=2*σ.vars "decode.i" ∧ 2*qs.length < (σ.arrs array).length

theorem step_spec (B K:ℕ) (front tail:List ℕ) (qs:List ℚ≥0) (array cursor:String)
    (h2:2 < B) (hlen:(front ++ (RamUnsignedBuffer.encode qs ++ tail)).length+2 < B)
    (hwords:∀ x∈ front ++ (RamUnsignedBuffer.encode qs ++ tail),x < B)
    (hsize:∀ q∈ qs,q.den.size≤ K) (harray:array ≠ "input.data")
    (hfresh:cursor∉ RamDecodeFraction.pair.wvars)
    (hf:cursor ≠ "decode.count" ∧ cursor ≠ "decode.i" ∧ cursor ≠ "decode.cursor" ∧ cursor ≠ "rat.d"):
    Spec B (fun σ => Invariant front tail qs array cursor σ∧ σ.vars "decode.i" < qs.length)
      (step array cursor) (fun σ τ => Invariant front tail qs array cursor τ∧
        τ.vars "decode.i"=σ.vars "decode.i"+1) (36*K+52):=by
  rintro σ ⟨⟨hp,hcount,hi,hcursor,htarget,hpos,hroom⟩,hlt⟩
  let i:=σ.vars "decode.i"
  let words:=front ++ (RamUnsignedBuffer.encode qs ++ tail)
  have hi':i < qs.length:=hlt
  have hi0:i≤ qs.length:=hi
  have hindex:front.length+2*i+1 < words.length:=RamInputSlice.index_bound front tail qs i hi'
  have hindex0:front.length+2*i < words.length:=by omega
  have hnum:words[front.length+2*i]=qs[i].num:=by
    have ho:words[front.length+2*i]?=some qs[i].num:=RamInputSlice.numerator front tail qs i hi'
    rw [List.getElem?_eq_getElem hindex0] at ho
    exact Option.some.inj ho
  have hden:words[front.length+2*i+1]=qs[i].den:=by
    have ho:words[front.length+2*i+1]?=some qs[i].den:=RamInputSlice.denominator front tail qs i hi'
    rw [List.getElem?_eq_getElem hindex] at ho
    exact Option.some.inj ho
  have hnB:qs[i].num < B:=by rw [←hnum]; exact hwords _ (List.getElem_mem hindex0)
  have hdB:qs[i].den < B:=by rw [←hden]; exact hwords _ (List.getElem_mem hindex)
  have hdSize:qs[i].den.size≤ K:=hsize _ (List.getElem_mem hi')
  have hlength:(RamUnsignedBuffer.encode (qs.take i)).length=2*i:=by
    simp only [RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
  obtain ⟨ν,hpair,hpairPost⟩:=RamDecodeFraction.pair_spec B words (front.length+2*i) h2 hindex
    (by dsimp only [words] at hindex; omega) hwords σ ⟨hp,hcursor⟩
  have hfraction:FractionOutput (qs[i]:ℚ) ν:=by
    simpa only [hnum,hden,NNRat.num_divNat_den] using hpairPost.2.2
  have htν:Prefix (RamUnsignedBuffer.encode (qs.take i)) array ν:=by
    simpa only [Prefix,hpair.frame_arr array (by simp [RamDecodeFraction.pair,RamDecodeFraction.normalize,
      RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.warrs])]
      using htarget
  have hposν:ν.vars cursor=2*i:=(hpair.frame_var cursor hfresh).trans hpos
  have hiν:ν.vars "decode.i"=i:=(hpair.frame_var "decode.i" (by decide)).trans rfl
  have hcν:ν.vars "decode.count"=qs.length:=(hpair.frame_var "decode.count" (by decide)).trans hcount
  have hroomν:2*qs.length < (ν.arrs array).length:=by rwa [RamFrames.run_array_length hpair array]
  obtain ⟨μ,hemit,hemitPost⟩:=RamUnsignedEncoding.command_spec B array cursor qs[i]
    (RamUnsignedBuffer.encode (qs.take i)) (by omega) hnB hdB
    (by rw [hlength]; simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega) hf.2.2.2 ν
      ⟨hfraction,htν,by rwa [hlength],by rw [hlength]; omega⟩
  have hpμ:Prefix words "input.data" μ:=by
    simpa only [Prefix,hemit.frame_arr "input.data" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,
      Com.warrs,Ne.symm harray])] using hpairPost.1
  have hcurμ:μ.vars "decode.cursor"=front.length+2*i+2:=
    (hemit.frame_var "decode.cursor" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.2.2.1])).trans hpairPost.2.1
  have hcμ:μ.vars "decode.count"=qs.length:=
    (hemit.frame_var "decode.count" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.1])).trans hcν
  have hiμ:μ.vars "decode.i"=i:=
    (hemit.frame_var "decode.i" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars,
      Ne.symm hf.2.1])).trans hiν
  have htμ:Prefix (RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
    rw [List.take_succ_eq_append_getElem hi']
    simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hemitPost.1
  have hposμ:μ.vars cursor=2*(i+1):=by rw [hlength] at hemitPost; omega
  have hroomμ:2*qs.length < (μ.arrs array).length:=by rwa [RamFrames.run_array_length hemit array]
  have hiNext:i+1 < B:=by
    simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega
  have hinc:Run B (.assign "decode.i" (.add (.var "decode.i") (.lit 1))) μ (μ.setVar "decode.i" (i+1)) 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
      (evalB_lit (by omega)) hiNext)
  refine ⟨μ.setVar "decode.i" (i+1),(hpair.seq (hemit.seq hinc)).mono
    (by simp only [hden]; omega),?_,?_⟩
  · refine ⟨?_,?_,by simpa only [vars_setVar,String.reduceEq,if_true] using (Nat.succ_le_iff.mpr hi'),?_,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hpμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using
        hcurμ.trans (by omega:front.length+2*i+2=front.length+2*(i+1))
    · simpa only [Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true] using htμ
    · simpa only [vars_setVar,if_neg hf.2.1,String.reduceEq,if_true] using hposμ
    · simpa only [arrs_setVar] using hroomμ
  · simp [i]

theorem command_spec (B K:ℕ) (front tail:List ℕ) (qs:List ℚ≥0) (array cursor:String)
    (h2:2 < B) (hlen:(front ++ (RamUnsignedBuffer.encode qs ++ tail)).length+2 < B)
    (hwords:∀ x∈ front ++ (RamUnsignedBuffer.encode qs ++ tail),x < B)
    (hsize:∀ q∈ qs,q.den.size≤ K) (harray:array ≠ "input.data")
    (hfresh:cursor∉ RamDecodeFraction.pair.wvars)
    (hf:cursor ≠ "decode.count" ∧ cursor ≠ "decode.i" ∧ cursor ≠ "decode.cursor" ∧ cursor ≠ "rat.d"):
    Spec B (fun σ => Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" σ∧
      σ.vars "decode.count"=qs.length∧ σ.vars "decode.cursor"=front.length∧
      2*qs.length < (σ.arrs array).length) (command array cursor)
      (fun _ τ => Prefix (front ++ (RamUnsignedBuffer.encode qs ++ tail)) "input.data" τ∧
        τ.vars "decode.cursor"=front.length+2*qs.length∧ Prefix (RamUnsignedBuffer.encode qs) array τ∧
        τ.vars cursor=2*qs.length) ((36*K+56)*qs.length+8):=by
  have hcount:qs.length < B:=by
    simp only [List.length_append,RamUnsignedBuffer.length_encode] at hlen; omega
  have hscan:=Spec.forRangeZero "decode.i" "decode.count" (Invariant front tail qs array cursor)
    qs.length (36*K+52) hcount (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (step_spec B K front tail qs array cursor h2 hlen hwords hsize harray hfresh hf)
  rintro σ ⟨hp,hcountσ,hcursorσ,hroom⟩
  let ν:=σ.setVar cursor 0
  have hzero:Run B (.assign cursor (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hinit:Invariant front tail qs array cursor (ν.setVar "decode.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar] using hp
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_neg (Ne.symm hf.1)] using hcountσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_true,if_neg (Ne.symm hf.2.2.1),
        Nat.mul_zero,Nat.add_zero] using hcursorσ
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,RamUnsignedBuffer.encode,
        List.flatMap_nil,List.length_nil] at hi
      omega
    · simp only [ν,vars_setVar,if_neg hf.2.1,if_true,Nat.mul_zero]
    · simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan ν hinit
  refine ⟨τ,(hzero.seq hr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hpost.1.1,?_,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2.1

end Lax455465Proofs.RamDecodeVector

end

section

namespace Lax455465Proofs.RamGraphInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def weightsSetup:Com:=.seq (.assign "decode.count" (.var "lp.n"))
  (.assign "decode.cursor" (.lit 2))

def capacitySetup:Com:=.assign "decode.count" (.var "lp.n2")

def weights:Com:=RamDecodeVector.command "flow.weights" "flow.weightPosition"
def capacity:Com:=RamDecodeVector.command "flow.capacities" "flow.capacityPosition"

def command:Com:=.seq RamGraphHeader.command
  (.seq weightsSetup (.seq weights (.seq capacitySetup capacity)))

theorem weightsSetup_spec (B n:ℕ) (h2:2 < B) (hn:n < B):
    Spec B (fun σ => σ.vars "lp.n"=n) weightsSetup
      (fun _ τ => τ.vars "decode.count"=n∧ τ.vars "decode.cursor"=2) 4:=by
  rintro σ hN
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "decode.count") n) (@Eq Nat (Env.vars τ "decode.cursor") ((2:Nat)))) σ; let c1:Env:=Env.setVar (Env.setVar σ "decode.count" (Env.vars σ "lp.n")) "decode.cursor" ((2:Nat)); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 ((1:Nat)); let c4:Nat:=c3 (Expr.size (Expr.var "lp.n")); let c5:Nat:=c3 (Expr.size (Expr.lit ((2:Nat)))); let c6:String→ Nat:=Env.vars c1; @Exists.intro Env (fun (σ':Env) => And (Run B weightsSetup σ σ' ((4:Nat))) (c0 σ')) c1 (@And.intro (Run B weightsSetup σ c1 ((4:Nat))) (c0 c1) (RunStep.mono B weightsSetup σ c1 (c2 c4 c5) ((4:Nat)) (RunStep.seq B (Com.assign "decode.count" (Expr.var "lp.n")) (Com.assign "decode.cursor" (Expr.lit ((2:Nat)))) σ (Env.setVar σ "decode.count" (Env.vars σ "lp.n")) c1 c4 c5 (RunStep.assign B σ "decode.count" (Expr.var "lp.n") (Env.vars σ "lp.n") (RunStep.eval_var B σ "lp.n" (?nAX_g6120_0_0_0))) (RunStep.assign B (Env.setVar σ "decode.count" (Env.vars σ "lp.n")) "decode.cursor" (Expr.lit ((2:Nat))) ((2:Nat)) (RunStep.eval_lit B ((2:Nat)) (Env.setVar σ "decode.count" (Env.vars σ "lp.n")) h2))) (?nAX_g6120_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6120_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6120_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem capacitySetup_spec (B n:ℕ) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "lp.n2"=n*n) capacitySetup
      (fun _ τ => τ.vars "decode.count"=n*n) 2:=by
  rintro σ hN
  (expose_names;
    (refine let c0:Nat:=Nat.mul n n; let c1:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "decode.count") c0) σ; @Exists.intro Env (fun (σ':Env) => And (Run B capacitySetup σ σ' ((2:Nat))) (c1 σ')) (Env.setVar σ "decode.count" (Env.vars σ "lp.n2")) (@And.intro (Run B capacitySetup σ (Env.setVar σ "decode.count" (Env.vars σ "lp.n2")) ((2:Nat))) (c1 (Env.setVar σ "decode.count" (Env.vars σ "lp.n2"))) (RunStep.mono B capacitySetup σ (Env.setVar σ "decode.count" (Env.vars σ "lp.n2")) (Nat.add ((1:Nat)) (Expr.size (Expr.var "lp.n2"))) ((2:Nat)) (RunStep.assign B σ "decode.count" (Expr.var "lp.n2") (Env.vars σ "lp.n2") (RunStep.eval_var B σ "lp.n2" (?nAX_g6121_0_0_0))) (?nAX_g6121_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6121_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6121_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem command_spec (B K:ℕ) {n:ℕ} (kind:EdgeKind) (I:RationalInstance n)
    (h2:2 < B) (hn:n < B) (hn2:n*n < B) (hn3:(n*n)*n < B)
    (hr:rows n < B) (hc:columns n < B) (hm:rows n*columns n < B)
    (hlen:(encodeInput kind I).length+2 < B)
    (hwords:∀ x∈ encodeInput kind I,x < B)
    (hweightSize:∀ u, (I.weight u).den.size≤ K)
    (hcapacitySize:∀ u v, (I.capacity u v).den.size≤ K):
    Spec B (fun σ => Prefix (encodeInput kind I) "input.data" σ∧
      2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length) command
      (fun _ τ => Data I τ∧ τ.vars "flow.kind"=RamGraphHeader.tag kind)
      ((36*K+56)*(n+n*n)+52):=by
  let ws:=List.ofFn I.weight
  let cs:=capacities I
  let front:= [RamGraphHeader.tag kind,n]
  have hwl:ws.length=n:=by simp [ws]
  have hcl:cs.length=n*n:=by simp [cs,capacities]
  have hinput:encodeInput kind I=front ++ (RamUnsignedBuffer.encode ws ++ RamUnsignedBuffer.encode cs):=
    FlowInputLists.input_eq kind I
  have hweightDen:∀ q∈ ws,q.den.size≤ K:=by
    intro q hq
    obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hq
    exact hweightSize u
  have hcapacityDen:∀ q∈ cs,q.den.size≤ K:=by
    intro q hq
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    exact hcapacitySize _ _
  have hwdecode:=RamDecodeVector.command_spec B K front (RamUnsignedBuffer.encode cs) ws
    "flow.weights" "flow.weightPosition" h2 (by rwa [←hinput])
    (by rwa [←hinput]) hweightDen (by decide) (by decide) (by decide)
  let cfront:=front ++ RamUnsignedBuffer.encode ws
  have hcinput:encodeInput kind I=cfront ++ (RamUnsignedBuffer.encode cs ++ []):=by
    simp only [hinput,cfront,List.append_nil,List.append_assoc]
  have hcdecode:=RamDecodeVector.command_spec B K cfront [] cs
    "flow.capacities" "flow.capacityPosition" h2 (by rwa [←hcinput])
    (by rwa [←hcinput]) hcapacityDen (by decide) (by decide) (by decide)
  rintro σ ⟨hp,hwroom,hcroom⟩
  obtain ⟨ν,hheader,hheaderPost⟩:=RamGraphHeader.command_spec B kind I h2 hn hn2 hn3 hr hc hm σ hp
  obtain ⟨μ,hwsetup,hwsetupPost⟩:=weightsSetup_spec B n h2 hn ν hheaderPost.2.1.1
  have hdμ:=RamGraphDimensions.frame hwsetup n hheaderPost.2.1 (by decide)
  have hpμ:Prefix (encodeInput kind I) "input.data" μ:=by
    simpa only [Prefix,hwsetup.frame_arr "input.data" (by decide)] using hheaderPost.1
  have hwroomμ:2*ws.length < (μ.arrs "flow.weights").length:=by
    rw [hwl,RamFrames.run_array_length hwsetup "flow.weights",RamFrames.run_array_length hheader "flow.weights"]
    exact hwroom
  obtain ⟨ρ,hwrun,hwpost⟩:=hwdecode μ ⟨by rwa [←hinput],by simpa only [hwl] using hwsetupPost.1,by simpa [front] using hwsetupPost.2,hwroomμ⟩
  have hdρ:=RamGraphDimensions.frame hwrun n hdμ (by decide)
  obtain ⟨κ,hcsetup,hcsetupPost⟩:=capacitySetup_spec B n hn2 ρ hdρ.2.1
  have hdκ:=RamGraphDimensions.frame hcsetup n hdρ (by decide)
  have hpκ:Prefix (encodeInput kind I) "input.data" κ:=by
    simpa only [Prefix,hcsetup.frame_arr "input.data" (by decide),hinput] using hwpost.1
  have hcurκ:κ.vars "decode.cursor"=cfront.length:=by
    have hcur:=(hcsetup.frame_var "decode.cursor" (by decide)).trans hwpost.2.1
    simpa only [cfront,List.length_append,RamUnsignedBuffer.length_encode,hwl,front,
      List.length_cons,List.length_nil] using hcur
  have hcroomκ:2*cs.length < (κ.arrs "flow.capacities").length:=by
    rw [hcl,RamFrames.run_array_length hcsetup "flow.capacities",RamFrames.run_array_length hwrun "flow.capacities",
      RamFrames.run_array_length hwsetup "flow.capacities",RamFrames.run_array_length hheader "flow.capacities"]
    exact hcroom
  obtain ⟨τ,hcrun,hcpost⟩:=hcdecode κ ⟨by rwa [←hcinput],by simpa only [hcl] using hcsetupPost,hcurκ,hcroomκ⟩
  have hdτ:=RamGraphDimensions.frame hcrun n hdκ (by decide)
  have hwpτ:Prefix (RamUnsignedBuffer.encode ws) "flow.weights" τ:=by
    simpa only [Prefix,hcrun.frame_arr "flow.weights" (by decide),hcsetup.frame_arr "flow.weights" (by decide)] using hwpost.2.2.1
  have hkτ:τ.vars "flow.kind"=RamGraphHeader.tag kind:=
    (hcrun.frame_var "flow.kind" (by decide)).trans ((hcsetup.frame_var "flow.kind" (by decide)).trans
      ((hwrun.frame_var "flow.kind" (by decide)).trans ((hwsetup.frame_var "flow.kind" (by decide)).trans hheaderPost.2.2)))
  refine ⟨τ,(hheader.seq (hwsetup.seq (hwrun.seq (hcsetup.seq hcrun)))).mono
    (by simp only [hwl,hcl]; ring_nf; omega),?_,hkτ⟩
  exact ⟨hdτ.1,hdτ.2.1,hdτ.2.2.1,hdτ.2.2.2.1,hdτ.2.2.2.2.1,hdτ.2.2.2.2.2,hwpτ,hcpost.2.2.1⟩

end Lax455465Proofs.RamGraphInput

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

namespace Lax455465Proofs.RamInputFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

theorem input_length {n:ℕ} (kind:EdgeKind) (I:RationalInstance n):
    (encodeInput kind I).length=2+2*n+2*(n*n):=by
  rw [FlowInputLists.input_eq]
  simp only [List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,
    List.length_ofFn,capacities]
  omega

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime sourceWord:Polynomial ℕ),
      c.NoWrite∧ ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),
        ∃ certificate:Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate certificate)∧
          ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
            Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I∧
              (encodeInput kind I).length≤ (σ.arrs "input.data").length∧
              2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length)
              c (fun _ τ => Data I τ∧ τ.vars "flow.kind"=RamGraphHeader.tag kind∧
                (∀ x∈ Lax109476.RationalEncoding.encodeCertificate certificate,x < 2^W)∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate certificate) "vm.output" τ∧
                τ.vars "vm.outputLength"=(Lax109476.RationalEncoding.encodeCertificate certificate).length∧
                τ.vars "vm.running"=0) (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩:=RamUniformFlowLp.exists_program
  let parsing:Polynomial ℕ:=Polynomial.C 200*(Polynomial.X+Polynomial.C 1)^2
  let words:Polynomial ℕ:=WB+LpInputSize.sizeBound+Polynomial.X+Polynomial.C 10
  refine ⟨.seq RamInputCopy.copy (.seq RamGraphInput.command c),T+parsing,words,TB,sourceWord,⟨by decide,by decide,hnoWrite⟩,?_⟩
  intro n kind I
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩:=hsolver kind I
  refine ⟨certificate,hvalid,hfit,?_⟩
  intro W hW
  let L:=bitSize (encodeInput kind I)
  let S:=LpInputSize.sizeBound.eval L
  have hsum:WB.eval L+S+L+10≤ W:=by simpa [words,L,S] using hW
  have hWB:WB.eval L≤ W:=by omega
  have hB:W < 2^W:=Nat.lt_two_pow_self
  have hlenL:(encodeInput kind I).length≤ L:=WordSize.length_le _
  have hLPword:RamFlowLp.wordLength n≤ S:=by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have hr:rows n < 2^W:=by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hc:columns n < 2^W:=by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hm:rows n*columns n < 2^W:=by dsimp only [RamFlowLp.wordLength] at hLPword; omega
  have hn2:n*n < 2^W:=by dsimp only [rows] at hr; omega
  have hn3:(n*n)*n < 2^W:=by dsimp only [rows] at hr; omega
  have hn:n < 2^W:=by rw [input_length] at hlenL; omega
  have h3:3 < 2^W:=by omega
  have hwords:∀ x∈ encodeInput kind I,x < 2^W:=by
    intro x hx
    exact lt_of_lt_of_le (WordSize.member_bound _ x hx)
      (Nat.pow_le_pow_right (by decide) (by omega:L≤ W))
  have hwsize:∀ u, (I.weight u).den.size≤ L:=by
    intro u
    have:=WordSize.member_size _ _ (LpInputSize.weight_members kind I u (I.weight u).den (by simp [encodeRational]))
    omega
  have hcsize:∀ u v, (I.capacity u v).den.size≤ L:=by
    intro u v
    have:=WordSize.member_size _ _ (LpInputSize.capacity_members kind I u v (I.capacity u v).den (by simp [encodeRational]))
    omega
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO⟩
  obtain ⟨ν,hcopy,hcopyPost⟩:=RamInputCopy.copy_spec (2^W) (encodeInput kind I) (by omega)
    (by omega) hwords σ ⟨hinp,hinputRoom⟩
  have hwroomν:2*n < (ν.arrs "flow.weights").length:=by rwa [RamFrames.run_array_length hcopy "flow.weights"]
  have hcroomν:2*(n*n) < (ν.arrs "flow.capacities").length:=by rwa [RamFrames.run_array_length hcopy "flow.capacities"]
  obtain ⟨μ,hgraph,hgraphPost⟩:=RamGraphInput.command_spec (2^W) L kind I (by omega) hn hn2 hn3 hr hc hm
    (by omega) hwords hwsize hcsize ν ⟨hcopyPost.2.2,hwroomν,hcroomν⟩
  have hprefixRun:=hcopy.seq hgraph
  obtain ⟨τ,hsolve,hpost⟩:=hcorrect W hWB μ ⟨hgraphPost.1,
    by rwa [RamFrames.run_array_length hprefixRun "lp.word"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.input"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.addresses"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.values"],
    by rwa [RamFrames.run_array_length hprefixRun "vm.output"]⟩
  have hcount:n+n*n≤ L:=by rw [input_length] at hlenL; omega
  have hparseCost:12*(encodeInput kind I).length+7+((36*L+56)*(n+n*n)+52)≤ parsing.eval L:=by
    have hprod:=Nat.mul_le_mul_left (36*L+56) hcount
    simp only [parsing,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X]
    nlinarith [sq_nonneg (L:ℤ)]
  refine ⟨τ,(hcopy.seq (hgraph.seq hsolve)).mono ?_,hpost.1,
    hpost.2.1.trans hgraphPost.2,hpost.2.2⟩
  simp only [Polynomial.eval_add]
  dsimp only [L] at hparseCost ⊢
  omega

end Lax455465Proofs.RamInputFlowLp

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

theorem command_spec (B:ℕ) (q:ℚ) (front tail:List ℕ) (h3:3 < B)
    (hlen:front.length+3 < B) (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Prefix (front ++ (encodeRational q ++ tail)) "vm.output" σ∧
      σ.vars "cert.cursor"=front.length) command
      (fun _ τ => FractionOutput q τ∧ τ.vars "cert.cursor"=front.length+3) 17:=by
  have hsign:sign q < B:=by unfold sign; split_ifs <;> omega
  have hsign1:sign q≤ 1:=by unfold sign; split_ifs <;> omega
  have hvalue:=value_eq q
  rintro σ ⟨hp,hcursor⟩
  let words:=front ++ (encodeRational q ++ tail)
  have hiS:front.length < words.length:=by simp [words,encodeRational]
  have hiN:front.length+1 < words.length:=by simp [words,encodeRational]
  have hiD:front.length+2 < words.length:=by simp [words,encodeRational]
  have hoS:words[front.length]?=some (sign q):=by
    rw [List.getElem?_append_right (by omega),Nat.sub_self]
    simp [encodeRational,sign]
  have hoN:words[front.length+1]?=some q.num.natAbs:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  have hoD:words[front.length+2]?=some q.den:=by
    rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    simp [encodeRational]
  rw [List.getElem?_eq_getElem hiS] at hoS
  rw [List.getElem?_eq_getElem hiN] at hoN
  rw [List.getElem?_eq_getElem hiD] at hoD
  have hgetS:=(hp front.length hiS).trans hoS
  have hgetN:=(hp (front.length+1) hiN).trans hoN
  have hgetD:=(hp (front.length+2) hiD).trans hoD
  have hroom:front.length+2 < (σ.arrs "vm.output").length:=by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hgetD
    cases hgetD
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (@List.length Nat front) ((3:Nat)); let c2:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput q τ) (@Eq Nat (Env.vars τ "cert.cursor") c1)) σ; let c3:Nat:= @List.getD Nat (Env.arrs σ "vm.output") (Env.vars σ "cert.cursor") ((0:Nat)); let c4:Env:=Env.setVar σ "rat.s" c3; let c5:Nat:=Env.vars c4 "cert.cursor"; let c6:Nat:=c0 c5 ((1:Nat)); let c7:Nat:= @List.getD Nat (Env.arrs c4 "vm.output") c6 ((0:Nat)); let c8:Env:=Env.setVar c4 "rat.n" c7; let c9:Nat:=Env.vars c8 "cert.cursor"; let c10:Nat:=c0 c9 ((2:Nat)); let c11:Nat:= @List.getD Nat (Env.arrs c8 "vm.output") c10 ((0:Nat)); let c12:Env:=Env.setVar c8 "rat.d" c11; let c13:Nat:=Env.vars c12 "cert.cursor"; let c14:Nat:=c0 c13 ((3:Nat)); let c15:Env:=Env.setVar c12 "cert.cursor" c14; let c16:Nat→ Nat:=c0 ((1:Nat)); let c17:Nat:=c16 (Expr.size (Expr.get "vm.output" (Expr.var "cert.cursor"))); let c18:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((1:Nat))); let c19:Expr:=Expr.get "vm.output" c18; let c20:Nat:=c16 (Expr.size c19); let c21:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((2:Nat))); let c22:Expr:=Expr.get "vm.output" c21; let c23:Nat:=c16 (Expr.size c22); let c24:Expr:=Expr.add (Expr.var "cert.cursor") (Expr.lit ((3:Nat))); let c25:Nat:=c16 (Expr.size c24); let c26:Nat:=c0 c23 c25; let c27:Nat:=c0 c20 c26; let c28:Com:=Com.assign "rat.n" c19; let c29:Com:=Com.assign "rat.d" c22; let c30:Com:=Com.assign "cert.cursor" c24; let c31:Com:=Com.seq c29 c30; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((17:Nat))) (c2 σ')) c15 (@And.intro (Run B command σ c15 ((17:Nat))) (c2 c15) (RunStep.mono B command σ c15 (c0 c17 c27) ((17:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor"))) (Com.seq c28 c31) σ c4 c15 c17 c27 (RunStep.assign B σ "rat.s" (Expr.get "vm.output" (Expr.var "cert.cursor")) c3 (RunStep.eval_get B σ "vm.output" (Expr.var "cert.cursor") (Env.vars σ "cert.cursor") (RunStep.eval_var B σ "cert.cursor" (?nAX_g6135_0_0_0)) (?nAX_g6135_0_0_1) ?_)) (RunStep.seq B c28 c31 c4 c8 c15 c20 c26 (RunStep.assign B c4 "rat.n" c19 c7 (RunStep.eval_get B c4 "vm.output" c18 c6 (RunStep.eval_add B c4 (Expr.var "cert.cursor") (Expr.lit ((1:Nat))) c5 ((1:Nat)) (RunStep.eval_var B c4 "cert.cursor" (?nAX_g6135_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c4 (?nAX_g6135_0_0_3)) (?nAX_g6135_0_0_4)) (?nAX_g6135_0_0_5) ?_)) (RunStep.seq B c29 c30 c8 c12 c15 c23 c25 (RunStep.assign B c8 "rat.d" c22 c11 (RunStep.eval_get B c8 "vm.output" c21 c10 (RunStep.eval_add B c8 (Expr.var "cert.cursor") (Expr.lit ((2:Nat))) c9 ((2:Nat)) (RunStep.eval_var B c8 "cert.cursor" (?nAX_g6135_0_0_6)) (RunStep.eval_lit B ((2:Nat)) c8 (?nAX_g6135_0_0_7)) (?nAX_g6135_0_0_8)) (?nAX_g6135_0_0_9) ?_)) (RunStep.assign B c12 "cert.cursor" c24 c14 (RunStep.eval_add B c12 (Expr.var "cert.cursor") (Expr.lit ((3:Nat))) c13 ((3:Nat)) (RunStep.eval_var B c12 "cert.cursor" (?nAX_g6135_0_0_10)) (RunStep.eval_lit B ((3:Nat)) c12 h3) (?nAX_g6135_0_0_11)))))) (?nAX_g6135_0_0_12)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6135_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6135_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput]

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax455465Proofs.RamCertificateVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def source (qs:List ℚ≥0):List ℕ:=
  qs.flatMap fun (q:ℚ≥0) => Lax109476.RationalEncoding.encodeRational (q:ℚ)

@[simp] theorem length_source (qs:List ℚ≥0):(source qs).length=3*qs.length:=by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [source,Lax109476.RationalEncoding.encodeRational] at *; omega

theorem source_split (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length):
    source qs=source (qs.take i) ++
      (Lax109476.RationalEncoding.encodeRational (qs[i]:ℚ) ++ source (qs.drop (i+1))):=by
  have hsplit:=congrArg source (List.take_append_drop (i+1) qs)
  rw [List.take_succ_eq_append_getElem hi] at hsplit
  simpa only [source,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.append_assoc] using hsplit.symm

def step (array:String):Com:=.seq RamLpRationalRead.command
  (.seq (RamUnsignedEncoding.command array "cert.position")
    (.assign "cert.i" (.add (.var "cert.i") (.lit 1))))

def command (array:String):Com:=.seq (.assign "cert.position" (.lit 0))
  (.seq (.assign "cert.i" (.lit 0))
    (.while (.lt (.var "cert.i") (.var "cert.count")) (step array)))

def Invariant (front tail:List ℕ) (qs:List ℚ≥0) (array:String) (σ:Env):Prop:=
  Prefix (front ++ (source qs ++ tail)) "vm.output" σ∧
    σ.vars "cert.count"=qs.length∧ σ.vars "cert.i" ≤ qs.length∧
    σ.vars "cert.cursor"=front.length+3*σ.vars "cert.i" ∧
    Prefix (RamUnsignedBuffer.encode (qs.take (σ.vars "cert.i"))) array σ∧
    σ.vars "cert.position"=2*σ.vars "cert.i" ∧ 2*qs.length < (σ.arrs array).length

theorem step_spec (B:ℕ) (front tail:List ℕ) (qs:List ℚ≥0) (array:String)
    (h3:3 < B) (hlen:front.length+3*qs.length+3 < B)
    (hnum:∀ q∈ qs,q.num < B) (hden:∀ q∈ qs,q.den < B)
    (harray:array ≠ "vm.output"):
    Spec B (fun σ => Invariant front tail qs array σ∧ σ.vars "cert.i" < qs.length)
      (step array) (fun σ τ => Invariant front tail qs array τ∧
        τ.vars "cert.i"=σ.vars "cert.i"+1) 35:=by
  rintro σ ⟨⟨hp,hcount,hi,hcursor,htarget,hpos,hroom⟩,hlt⟩
  let i:=σ.vars "cert.i"
  have hi':i < qs.length:=hlt
  have hi0:i≤ qs.length:=hi
  let front':=front ++ source (qs.take i)
  let tail':=source (qs.drop (i+1)) ++ tail
  have hfront:front'.length=front.length+3*i:=by
    simp only [front',List.length_append,length_source,List.length_take,Nat.min_eq_left hi0]
  have hsource:front ++ (source qs ++ tail) =
      front' ++ (Lax109476.RationalEncoding.encodeRational (qs[i]:ℚ) ++ tail'):=by
    rw [source_split qs i hi']; simp only [front',tail',List.append_assoc]
  have hnB:=hnum qs[i] (List.getElem_mem hi')
  have hdB:=hden qs[i] (List.getElem_mem hi')
  have hlength:(RamUnsignedBuffer.encode (qs.take i)).length=2*i:=by
    simp only [RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
  obtain ⟨ν,hread,hreadPost⟩:=RamLpRationalRead.command_spec B (qs[i]:ℚ) front' tail' h3
    (by rw [hfront]; omega) (by simpa only [NNRat.natAbs_num_coe] using hnB)
    (by simpa only [NNRat.den_coe] using hdB) σ ⟨by rwa [←hsource],by rwa [hfront]⟩
  have htν:Prefix (RamUnsignedBuffer.encode (qs.take i)) array ν:=by
    simpa only [Prefix,hread.frame_arr array (by simp [RamLpRationalRead.command,Com.warrs])] using htarget
  have hposν:ν.vars "cert.position"=2*i:=(hread.frame_var "cert.position" (by decide)).trans hpos
  have hiν:ν.vars "cert.i"=i:=(hread.frame_var "cert.i" (by decide)).trans rfl
  have hcν:ν.vars "cert.count"=qs.length:=(hread.frame_var "cert.count" (by decide)).trans hcount
  have hroomν:2*qs.length < (ν.arrs array).length:=by rwa [RamFrames.run_array_length hread array]
  obtain ⟨μ,hemit,hemitPost⟩:=RamUnsignedEncoding.command_spec B array "cert.position" qs[i]
    (RamUnsignedBuffer.encode (qs.take i)) (by omega) hnB hdB
    (by rw [hlength]; omega) (by decide) ν ⟨hreadPost.1,htν,by rwa [hlength],by rw [hlength]; omega⟩
  have hpμ:Prefix (front ++ (source qs ++ tail)) "vm.output" μ:=by
    simpa only [Prefix,hemit.frame_arr "vm.output" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,
      Com.warrs,Ne.symm harray]),hread.frame_arr "vm.output" (by decide)] using hp
  have hcurμ:μ.vars "cert.cursor"=front.length+3*i+3:=by
    simpa only [hemit.frame_var "cert.cursor" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]),hfront] using hreadPost.2
  have hcμ:μ.vars "cert.count"=qs.length:=(hemit.frame_var "cert.count" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars])).trans hcν
  have hiμ:μ.vars "cert.i"=i:=(hemit.frame_var "cert.i" (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars])).trans hiν
  have htμ:Prefix (RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
    rw [List.take_succ_eq_append_getElem hi']
    simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hemitPost.1
  have hposμ:μ.vars "cert.position"=2*(i+1):=by rw [hlength] at hemitPost; omega
  have hroomμ:2*qs.length < (μ.arrs array).length:=by rwa [RamFrames.run_array_length hemit array]
  have hiNext:i+1 < B:=by omega
  have hinc:Run B (.assign "cert.i" (.add (.var "cert.i") (.lit 1))) μ (μ.setVar "cert.i" (i+1)) 4:=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
      (evalB_lit (by omega)) hiNext)
  refine ⟨μ.setVar "cert.i" (i+1),hread.seq (hemit.seq hinc),?_,?_⟩
  · refine ⟨?_,?_,by simpa only [vars_setVar,String.reduceEq,if_true] using (Nat.succ_le_iff.mpr hi'),?_,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hpμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using
        hcurμ.trans (by omega:front.length+3*i+3=front.length+3*(i+1))
    · simpa only [Prefix,arrs_setVar,vars_setVar,String.reduceEq,if_true] using htμ
    · simpa only [vars_setVar,String.reduceEq,if_false,if_true] using hposμ
    · simpa only [arrs_setVar] using hroomμ
  · simp [i]

theorem command_spec (B:ℕ) (front tail:List ℕ) (qs:List ℚ≥0) (array:String)
    (h3:3 < B) (hlen:front.length+3*qs.length+3 < B)
    (hnum:∀ q∈ qs,q.num < B) (hden:∀ q∈ qs,q.den < B)
    (harray:array ≠ "vm.output"):
    Spec B (fun σ => Prefix (front ++ (source qs ++ tail)) "vm.output" σ∧
      σ.vars "cert.count"=qs.length∧ σ.vars "cert.cursor"=front.length∧
      2*qs.length < (σ.arrs array).length) (command array)
      (fun _ τ => Prefix (front ++ (source qs ++ tail)) "vm.output" τ∧
        τ.vars "cert.cursor"=front.length+3*qs.length∧ Prefix (RamUnsignedBuffer.encode qs) array τ∧
        τ.vars "cert.position"=2*qs.length) (39*qs.length+8):=by
  have hcount:qs.length < B:=by omega
  have hscan:=Spec.forRangeZero "cert.i" "cert.count" (Invariant front tail qs array)
    qs.length 35 hcount (fun _ h => h.2.2.1) (fun _ h => h.2.1)
      (step_spec B front tail qs array h3 hlen hnum hden harray)
  rintro σ ⟨hp,hcountσ,hcursorσ,hroom⟩
  let ν:=σ.setVar "cert.position" 0
  have hzero:Run B (.assign "cert.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hinit:Invariant front tail qs array (ν.setVar "cert.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar] using hp
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcountσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false,if_true,Nat.mul_zero,Nat.add_zero] using hcursorσ
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,List.length_nil] at hi
      omega
    · simp only [ν,vars_setVar,String.reduceEq,if_false,if_true,Nat.mul_zero]
    · simpa only [ν,arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan ν hinit
  refine ⟨τ,(hzero.seq hr).mono (by omega),hpost.1.1,?_,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2.1

end Lax455465Proofs.RamCertificateVector

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

theorem arc_bounded {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (h:Feasible I f x) (st e:Edge n):
    x (st,e)≤ (I.capacity e.1 e.2:ℚ):=by
  calc
    x (st,e)≤ ∑ q:Edge n,x (q,e):=
      Finset.single_le_sum (fun q _ => h.2.1 (q,e)) (Finset.mem_univ st)
    _≤ _:=h.2.2.1 e

theorem value_mul_demand_le {n:ℕ} (I:RationalInstance n) (f:ℚ)
    (x:CommodityArc n→ ℚ) (h:Feasible I f x) (s t:Fin n) (hne:s ≠ t):
    f * ((I.weight s:ℚ) * I.weight t)≤ ∑ v, (I.capacity s v:ℚ):=by
  have hbalance:=h.2.2.2 (s,t) s
  have hin:0≤ ∑ v,x ((s,t), (v,s)):=
    Finset.sum_nonneg (fun v _ => h.2.1 ((s,t), (v,s)))
  have hout:(∑ v,x ((s,t), (s,v)))≤ ∑ v, (I.capacity s v:ℚ):=
    Finset.sum_le_sum (fun v _ => arc_bounded I f x h (s,t) (s,v))
  simp [divergence,hne] at hbalance
  linarith

theorem positive_pair {n:ℕ} (I:RationalInstance n) (hp:2≤ supportCount I.weights):
    ∃ s t:Fin n,s ≠ t∧ 0 < (I.weight s:ℚ) * I.weight t:=by
  classical
  have hcard:1 < (Finset.univ.filter fun v => 0 < I.weights v).card:=by
    change 1 < supportCount I.weights
    omega
  obtain ⟨s,hs,t,ht,hne⟩:=Finset.one_lt_card.mp hcard
  have hsQ:0 < (I.weight s:ℚ):=by
    have hsR:=(Finset.mem_filter.mp hs).2
    change (0:ℝ≥0) < (I.weight s:ℝ≥0) at hsR
    exact_mod_cast hsR
  have htQ:0 < (I.weight t:ℚ):=by
    have htR:=(Finset.mem_filter.mp ht).2
    change (0:ℝ≥0) < (I.weight t:ℝ≥0) at htR
    exact_mod_cast htR
  exact ⟨s,t,hne,mul_pos hsQ htQ⟩

theorem no_infeasibility_certificate {n:ℕ} (I:RationalInstance n)
    (y:Fin (n * n + 2 * ((n * n) * n))→ ℚ):
    ¬ IsInfeasibilityCertificate (program I) y:=by
  intro h
  have hb:∀ i,0≤ (program I).b i:=by
    intro i
    simp only [program]
    cases (rowIndex n).symm i with
    | inl e => exact (I.capacity e.1 e.2).property
    | inr b => exact le_rfl
  have hnonneg:0≤ dualValue (program I) y:=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (h.1 i))
  exact (not_lt_of_ge hnonneg) h.2.2

def zeroCapacity {n:ℕ} (I:RationalInstance n):RationalInstance n where
  capacity _ _:=0
  loopless _:=rfl
  weight:=I.weight

private theorem zeroCapacity_matrix {n:ℕ} (I:RationalInstance n):
    (program (zeroCapacity I)).A=(program I).A:=by
  funext i j
  simp only [program]
  cases (rowIndex n).symm i with
  | inl e => cases (variableIndex n).symm j <;> rfl
  | inr b => cases (variableIndex n).symm j <;> rfl

private theorem zeroCapacity_bound {n:ℕ} (I:RationalInstance n):
    (program (zeroCapacity I)).b=fun _ => 0:=by
  funext i
  simp only [program]
  cases (rowIndex n).symm i <;> rfl

theorem no_improving_direction {n:ℕ} (I:RationalInstance n)
    (hp:2≤ supportCount I.weights)
    (d:Fin (1 + (n * n) * (n * n))→ ℚ):
    ¬ IsImprovingDirection (program I) d:=by
  intro h
  let f:=d (variableIndex n (.inl 0))
  let x:=fun a => d (variableIndex n (.inr a))
  have hreconstruct:vector f x=d:=vector_representation d
  have hd:PrimalFeasible (program (zeroCapacity I)) d:=by
    refine ⟨h.1, ?_⟩
    intro i
    rw [zeroCapacity_bound]
    simpa only [rowValue,zeroCapacity_matrix] using h.2.1 i
  rw [← hreconstruct,feasible_iff] at hd
  obtain ⟨s,t,hne,hprod⟩:=positive_pair I hp
  have hf:=value_mul_demand_le (zeroCapacity I) f x hd s t hne
  simp [zeroCapacity] at hf
  have hfzero:f≤ 0:=by nlinarith
  have hobj:primalValue (program I) d=f:=by
    rw [← hreconstruct,objective_value]
  have hpos:=h.2.2
  rw [hobj] at hpos
  exact (not_lt_of_ge hfzero) hpos

end Lax455465Proofs.DirectedFlowBounds

end

section

namespace Lax455465Proofs.FlowOptimalCertificate

open Lax455465.ProductNetwork Lax455465.RationalEncoding DirectedFlowLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem optimal {n:ℕ} (I:RationalInstance n)
    (hp:2≤ supportCount I.weights)
    (certificate:Certificate (n*n+2*((n*n)*n)) (1+(n*n)*(n*n)))
    (hvalid:IsValidCertificate (program I) certificate):
    ∃ z y,certificate=.optimal z y∧ PrimalFeasible (program I) z∧
      DualFeasible (program I) y∧ primalValue (program I) z=dualValue (program I) y:=by
  cases certificate with
  | optimal z y => exact ⟨z,y,rfl,hvalid⟩
  | infeasible y => exact False.elim (DirectedFlowBounds.no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (DirectedFlowBounds.no_improving_direction I hp d hvalid.2)

end Lax455465Proofs.FlowOptimalCertificate

end

section

namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

@[simp] theorem length_vector {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i):
    (vector x hx).length=k:=List.length_ofFn

theorem source_vector {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i):
    RamCertificateVector.source (vector x hx)=encodeVector x:=by
  have hm:(vector x hx).map (fun (q:ℚ≥0) => (q:ℚ))=List.ofFn x:=by
    change (List.ofFn (fun i:Fin k => (⟨x i,hx i⟩:ℚ≥0))).map
      (fun (q:ℚ≥0) => (q:ℚ))=List.ofFn x
    erw [List.map_ofFn]
    rfl
  unfold encodeVector
  rw [←hm]
  simp only [RamCertificateVector.source,List.flatMap_map]

theorem vector_fits (B:ℕ) {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i)
    (hwords:∀ w∈ encodeVector x,w < B):
    (∀ q∈ vector x hx,q.num < B)∧ (∀ q∈ vector x hx,q.den < B):=by
  constructor
  · intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    have hn:(x i).num.natAbs < B:=hwords _ (List.mem_flatMap.mpr
      ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [encodeRational]⟩)
    exact (show NNRat.num (⟨x i,hx i⟩:ℚ≥0) < B from by
      change (x i).num.natAbs < B
      exact hn)
  · intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    have hd:(x i).den < B:=hwords _ (List.mem_flatMap.mpr
      ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp [encodeRational]⟩)
    exact (show NNRat.den (⟨x i,hx i⟩:ℚ≥0) < B from by
      change (x i).den < B
      exact hd)

def command:Com:=.seq (.assign "cert.cursor" (.lit 1))
  (.seq (.assign "cert.count" (.var "lp.columns"))
    (.seq (RamCertificateVector.command "flow.primal")
      (.seq (.assign "cert.count" (.var "lp.rows"))
        (RamCertificateVector.command "flow.dual"))))

theorem command_spec (B:ℕ) {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n)
    (z:Fin (columns n)→ ℚ) (y:Fin (rows n)→ ℚ)
    (hz:∀ i,0≤ z i) (hy:∀ i,0≤ y i)
    (h3:3 < B) (hlen:1+3*columns n+3*rows n+3 < B)
    (hzn:∀ q∈ vector z hz,q.num < B) (hzd:∀ q∈ vector z hz,q.den < B)
    (hyn:∀ q∈ vector y hy,q.num < B) (hyd:∀ q∈ vector y hy,q.den < B):
    Spec B (fun σ => Data I σ∧ Prefix (encodeCertificate (.optimal z y)) "vm.output" σ∧
      2*columns n < (σ.arrs "flow.primal").length∧ 2*rows n < (σ.arrs "flow.dual").length)
      command (fun _ τ => Data I τ∧ Prefix (encodeCertificate (.optimal z y)) "vm.output" τ∧
        Prefix (RamUnsignedBuffer.encode (vector z hz)) "flow.primal" τ∧
        Prefix (RamUnsignedBuffer.encode (vector y hy)) "flow.dual" τ∧
        τ.vars "cert.cursor"=1+3*columns n+3*rows n) (39*(columns n+rows n)+22):=by
  rintro σ ⟨hdata,hp,hproom,hdroom⟩
  let ν:=(σ.setVar "cert.cursor" 1).setVar "cert.count" (columns n)
  have hstart1:Run B (.assign "cert.cursor" (.lit 1)) σ (σ.setVar "cert.cursor" 1) 2:=
    Run.assign (evalB_lit (by omega))
  have hstart2:Run B (.assign "cert.count" (.var "lp.columns")) (σ.setVar "cert.cursor" 1) ν 2:=
    Run.assign (by rw [evalB_var_iff]; simpa only [vars_setVar,String.reduceEq,if_false]
      using And.intro hdata.2.2.2.2.1.symm (hdata.2.2.2.2.1 ▸ (by omega:columns n < B)))
  have hsource:encodeCertificate (.optimal z y) =
      [0] ++ (RamCertificateVector.source (vector z hz) ++ encodeVector y):=by
    simp only [encodeCertificate,source_vector,List.append_assoc]
  obtain ⟨μ,hprimal,hprimalPost⟩:=RamCertificateVector.command_spec B [0] (encodeVector y)
    (vector z hz) "flow.primal" h3 (by simp; omega) hzn hzd (by decide) ν
      ⟨by simpa only [Prefix,ν,arrs_setVar,←hsource] using hp,
       by simp [ν],by simp [ν],by simpa only [length_vector,ν,arrs_setVar] using hproom⟩
  have hdataμ:=RamFlowData.frame (hstart1.seq (hstart2.seq hprimal)) I hdata (by decide) (by decide)
  let ρ:=μ.setVar "cert.count" (rows n)
  have hcount:Run B (.assign "cert.count" (.var "lp.rows")) μ ρ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hdataμ.2.2.2.1.symm,hdataμ.2.2.2.1 ▸ (by omega:rows n < B)⟩)
  let front:= [0] ++ encodeVector z
  have hfront:front.length=1+3*columns n:=by
    change ([0] ++ RamVectorEncoding.encode (List.ofFn z)).length=_
    simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,List.length_ofFn]
  have hsource2:encodeCertificate (.optimal z y) =
      front ++ (RamCertificateVector.source (vector y hy) ++ []):=by
    simp only [front,source_vector,encodeCertificate,List.append_nil]
  have hdroomρ:2*rows n < (ρ.arrs "flow.dual").length:=by
    simp only [ρ,arrs_setVar,RamFrames.run_array_length hprimal "flow.dual",ν,arrs_setVar]
    exact hdroom
  obtain ⟨τ,hdual,hdualPost⟩:=RamCertificateVector.command_spec B front [] (vector y hy) "flow.dual" h3
    (by rw [hfront,length_vector]; omega) hyn hyd (by decide) ρ
      ⟨by simpa only [Prefix,ρ,arrs_setVar,←hsource2,hsource] using hprimalPost.1,
       by simp [ρ],by simpa only [ρ,vars_setVar,String.reduceEq,if_false,List.length_cons,List.length_nil,
         length_vector,hfront] using hprimalPost.2.1,by simpa only [length_vector] using hdroomρ⟩
  have hwhole:=hstart1.seq (hstart2.seq (hprimal.seq (hcount.seq hdual)))
  refine ⟨τ,hwhole.mono (by simp only [length_vector]; omega),
    RamFlowData.frame hwhole I hdata (by decide) (by decide),?_,?_,hdualPost.2.2.1,?_⟩
  · simpa only [hsource2] using hdualPost.1
  · simpa only [Prefix,hdual.frame_arr "flow.primal" (by decide),ρ,arrs_setVar] using hprimalPost.2.2.1
  · simpa only [hfront,length_vector] using hdualPost.2.1

end Lax455465Proofs.RamOptimalDecode

end

section

namespace Lax455465Proofs.RamInputOptimal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData DirectedFlowLP
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

theorem exists_program:
    ∃ (c:Com) (timeBound wordBound sourceTime sourceWord:Polynomial ℕ),
      c.NoWrite∧ ∀ {n:ℕ} (kind:EdgeKind) (I:RationalInstance n),2≤ supportCount I.weights→
        ∃ (z:Fin (columns n)→ ℚ) (y:Fin (rows n)→ ℚ)
          (hz:PrimalFeasible (program I) z) (hy:DualFeasible (program I) y),
          primalValue (program I) z=dualValue (program I) y∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal z y))∧
          ∀ W:ℕ,wordBound.eval (bitSize (encodeInput kind I))≤ W→
            Spec (2^W) (fun σ => σ.inp=(encodeInput kind I).length::encodeInput kind I∧
              (encodeInput kind I).length≤ (σ.arrs "input.data").length∧
              2*n < (σ.arrs "flow.weights").length∧ 2*(n*n) < (σ.arrs "flow.capacities").length∧
              RamFlowLp.wordLength n < (σ.arrs "lp.word").length∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length∧
              2*columns n < (σ.arrs "flow.primal").length∧ 2*rows n < (σ.arrs "flow.dual").length)
              c (fun _ τ => Data I τ∧ τ.vars "flow.kind"=RamGraphHeader.tag kind∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector z hz.1)) "flow.primal" τ∧
                Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy.1)) "flow.dual" τ∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal z y)) "vm.output" τ∧
                τ.vars "cert.cursor"=1+3*columns n+3*rows n)
              (timeBound.eval (bitSize (encodeInput kind I))):=by
  obtain ⟨c,T,WB,TB,sourceWord,hnoWrite,hsolver⟩:=RamInputFlowLp.exists_program
  let extra:Polynomial ℕ:=Polynomial.C 39*LpInputSize.sizeBound+Polynomial.C 22
  let words:Polynomial ℕ:=WB+LpInputSize.sizeBound+Polynomial.C 10
  refine ⟨.seq c RamOptimalDecode.command,T+extra,words,TB,sourceWord,⟨hnoWrite,by decide⟩,?_⟩
  intro n kind I hp
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩:=hsolver kind I
  obtain ⟨z,y,hcertificate,hz,hy,hvalue⟩:=FlowOptimalCertificate.optimal I hp certificate hvalid
  subst certificate
  refine ⟨z,y,hz,hy,hvalue,hfit,?_⟩
  intro W hW
  let L:=bitSize (encodeInput kind I)
  let S:=LpInputSize.sizeBound.eval L
  have hsum:WB.eval L+S+10≤ W:=by simpa [words,L,S] using hW
  have hWB:WB.eval L≤ W:=by omega
  have hB:W < 2^W:=Nat.lt_two_pow_self
  have hLPword:RamFlowLp.wordLength n≤ S:=by
    rw [←FlowEncodingSizes.flow_length I]
    exact (WordSize.length_le _).trans (LpInputSize.flow_program_polynomial_size kind I)
  have h3:3 < 2^W:=by omega
  have hlen:1+3*columns n+3*rows n+3 < 2^W:=by
    dsimp only [RamFlowLp.wordLength] at hLPword
    omega
  rintro σ ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO,hpr,hdu⟩
  obtain ⟨ν,hrun,hpost⟩:=hcorrect W hWB σ
    ⟨hinp,hinputRoom,hwroom,hcroom,hlproom,hvinput,hA,hV,hO⟩
  have hzwords:∀ x∈ Lax109476.RationalEncoding.encodeVector z,x < 2^W:=by
    intro x hx
    exact hpost.2.2.1 x (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inl (Or.inr hx))
  have hywords:∀ x∈ Lax109476.RationalEncoding.encodeVector y,x < 2^W:=by
    intro x hx
    exact hpost.2.2.1 x (by
      simp only [Lax109476.RationalEncoding.encodeCertificate,List.mem_append]
      exact Or.inr hx)
  obtain ⟨hzn,hzd⟩:=RamOptimalDecode.vector_fits (2^W) z hz.1 hzwords
  obtain ⟨hyn,hyd⟩:=RamOptimalDecode.vector_fits (2^W) y hy.1 hywords
  obtain ⟨τ,hdecode,hdecoded⟩:=RamOptimalDecode.command_spec (2^W) I z y hz.1 hy.1 h3 hlen hzn hzd hyn hyd ν
    ⟨hpost.1,hpost.2.2.2.1,by rwa [RamFrames.run_array_length hrun "flow.primal"],
      by rwa [RamFrames.run_array_length hrun "flow.dual"]⟩
  have hcost:39*(columns n+rows n)+22≤ extra.eval L:=by
    simp only [extra,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    dsimp only [RamFlowLp.wordLength] at hLPword
    dsimp only [S] at hLPword
    omega
  refine ⟨τ,(hrun.seq hdecode).mono ?_,hdecoded.1,
    (hdecode.frame_var "flow.kind" (by decide)).trans hpost.2.1,
    hdecoded.2.2.1,hdecoded.2.2.2.1,hdecoded.2.1,hdecoded.2.2.2.2⟩
  simp only [Polynomial.eval_add]
  dsimp only [L] at hcost
  omega

end Lax455465Proofs.RamInputOptimal

end

theorem solution:∃ (c:Lax808846Proofs.Imp.Com) (timeBound:@Polynomial Nat Nat.instSemiring) (wordBound:
  @Polynomial Nat Nat.instSemiring) (sourceTime:@Polynomial Nat Nat.instSemiring) (sourceWord:
  @Polynomial Nat Nat.instSemiring),
  And c.NoWrite
    (∀ {n:Nat} (kind:Lax455465.ProductNetwork.EdgeKind) (I:Lax455465.RationalEncoding.RationalInstance n),
      Nat.le ((2:Nat))
          (@Lax455465.ProductNetwork.supportCount n (@Lax455465.RationalEncoding.RationalInstance.weights n I))→
        ∃ (z:Fin (Lax455465Proofs.RamFlowData.columns n)→ Rat) (y:Fin (Lax455465Proofs.RamFlowData.rows n)→ Rat)
          (hz:
          @Lax109476.LinearProgram.PrimalFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
            Rat.instPartialOrder
            (Nat.add (Nat.mul n n)
              (Nat.mul
                ((2:Nat))
                (Nat.mul
                  (Nat.mul n n) n)))
            (Nat.add ((1:Nat))
              (Nat.mul (Nat.mul n n)
                (Nat.mul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) z)
          (hy:
          @Lax109476.LinearProgram.DualFeasible Rat (@DivisionRing.toRing Rat Rat.instDivisionRing) Rat.instPartialOrder
            (Nat.add (Nat.mul n n)
              (Nat.mul
                ((2:Nat))
                (Nat.mul
                  (Nat.mul n n) n)))
            (Nat.add ((1:Nat))
              (Nat.mul (Nat.mul n n)
                (Nat.mul n n)))
            (@Lax455465Proofs.DirectedFlowLP.program n I) y),
          And
            (@Eq Rat
              (@Lax109476.LinearProgram.primalValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
                (Nat.add
                  (Nat.mul n n)
                  (Nat.mul
                    ((2:Nat))
                    (Nat.mul
                      (Nat.mul n n) n)))
                (Nat.add
                  ((1:Nat))
                  (Nat.mul
                    (Nat.mul n n)
                    (Nat.mul n n)))
                (@Lax455465Proofs.DirectedFlowLP.program n I) z)
              (@Lax109476.LinearProgram.dualValue Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)
                (Nat.add
                  (Nat.mul n n)
                  (Nat.mul
                    ((2:Nat))
                    (Nat.mul
                      (Nat.mul n n) n)))
                (Nat.add
                  ((1:Nat))
                  (Nat.mul
                    (Nat.mul n n)
                    (Nat.mul n n)))
                (@Lax455465Proofs.DirectedFlowLP.program n I) y))
            (And
              (Lax759944.RamPolytime.FitsInWords
                (@Polynomial.eval Nat Nat.instSemiring
                  (Lax759944.BinaryWordEncoding.bitSize
                    (@Lax109476.RationalEncoding.encodeProgram
                      (Nat.add
                        (Nat.mul n n)
                        (Nat.mul
                          ((2:Nat))
                          (Nat.mul
                            (Nat.mul n n) n)))
                      (Nat.add
                        ((1:Nat))
                        (Nat.mul
                          (Nat.mul n n)
                          (Nat.mul n n)))
                      (@Lax455465Proofs.DirectedFlowLP.program n I)))
                  sourceWord)
                (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                  (Lax455465Proofs.RamFlowData.columns n)
                  (@Lax109476.RationalCertificates.Certificate.optimal (Lax455465Proofs.RamFlowData.rows n)
                    (Lax455465Proofs.RamFlowData.columns n) z y)))
              (∀ (W:Nat),
                Nat.le
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      wordBound)
                    W→
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) W)
                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                      And
                        (@Eq (List Nat) σ.inp
                          (@List.cons Nat (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                            (@Lax455465.RationalEncoding.encodeInput n kind I)))
                        (And
                          (Nat.le (@List.length Nat (@Lax455465.RationalEncoding.encodeInput n kind I))
                            (@List.length Nat (σ.arrs "input.data")))
                          (And
                            (Nat.lt
                              (Nat.mul
                                ((2:Nat)) n)
                              (@List.length Nat (σ.arrs "flow.weights")))
                            (And
                              (Nat.lt
                                (Nat.mul
                                  ((2:Nat))
                                  (Nat.mul n n))
                                (@List.length Nat (σ.arrs "flow.capacities")))
                              (And
                                (Nat.lt (Lax455465Proofs.RamFlowLp.wordLength n)
                                  (@List.length Nat (σ.arrs "lp.word")))
                                (And
                                  (Nat.lt
                                    (@List.length Nat
                                      (@Lax109476.RationalEncoding.encodeProgram
                                        (Nat.add
                                          (Nat.mul n n)
                                          (Nat.mul
                                            ((2:Nat))
                                            (Nat.mul
                                              (Nat.mul n n) n)))
                                        (Nat.add
                                          ((1:Nat))
                                          (Nat.mul
                                            (Nat.mul n n)
                                            (Nat.mul n n)))
                                        (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                    (@List.length Nat (σ.arrs "vm.input")))
                                  (And
                                    (Nat.lt
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (Lax759944.BinaryWordEncoding.bitSize
                                          (@Lax109476.RationalEncoding.encodeProgram
                                            (Nat.add
                                              (Nat.mul n n)
                                              (Nat.mul
                                                ((2:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n) n)))
                                            (Nat.add
                                              ((1:Nat))
                                              (Nat.mul
                                                (Nat.mul n n)
                                                (Nat.mul n n)))
                                            (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                        sourceTime)
                                      (@List.length Nat (σ.arrs "vm.addresses")))
                                    (And
                                      (Nat.lt
                                        (@Polynomial.eval Nat Nat.instSemiring
                                          (Lax759944.BinaryWordEncoding.bitSize
                                            (@Lax109476.RationalEncoding.encodeProgram
                                              (Nat.add
                                                (Nat.mul n n)
                                                (Nat.mul
                                                  ((2:Nat))
                                                  (Nat.mul
                                                    (Nat.mul n n) n)))
                                              (Nat.add
                                                ((1:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n)
                                                  (Nat.mul n n)))
                                              (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                          sourceTime)
                                        (@List.length Nat (σ.arrs "vm.values")))
                                      (And
                                        (Nat.lt
                                          (@Polynomial.eval Nat Nat.instSemiring
                                            (Lax759944.BinaryWordEncoding.bitSize
                                              (@Lax109476.RationalEncoding.encodeProgram
                                                (Nat.add
                                                  (Nat.mul n n)
                                                  (Nat.mul
                                                    ((2:Nat))
                                                    (Nat.mul
                                                      (Nat.mul n n) n)))
                                                (Nat.add
                                                  ((1:Nat))
                                                  (Nat.mul
                                                    (Nat.mul n n)
                                                    (Nat.mul n n)))
                                                (@Lax455465Proofs.DirectedFlowLP.program n I)))
                                            sourceTime)
                                          (@List.length Nat (σ.arrs "vm.output")))
                                        (And
                                          (Nat.lt
                                            (Nat.mul
                                              ((2:Nat))
                                              (Lax455465Proofs.RamFlowData.columns n))
                                            (@List.length Nat (σ.arrs "flow.primal")))
                                          (Nat.lt
                                            (Nat.mul
                                              ((2:Nat))
                                              (Lax455465Proofs.RamFlowData.rows n))
                                            (@List.length Nat (σ.arrs "flow.dual")))))))))))))
                    c
                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                      And (@Lax455465Proofs.RamFlowData.Data n I τ)
                        (And (@Eq Nat (τ.vars "flow.kind") (Lax455465Proofs.RamGraphHeader.tag kind))
                          (And
                            (Lax455465Proofs.RamVirtualState.Prefix
                              (Lax455465Proofs.RamUnsignedBuffer.encode
                                (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.columns n) z
                                  (@And.left
                                    (∀
                                      (j:
                                        Fin
                                          (Nat.add
                                            ((1:Nat))
                                            (Nat.mul
                                              (Nat.mul n n)
                                              (Nat.mul n n)))),
                                      @LE.le Rat
                                        (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                        (@OfNat.ofNat Rat (nat_lit 0)
                                          (@Zero.toOfNat0 Rat
                                            (@MulZeroClass.toZero Rat
                                              (@instMulZeroClassOfSemiring Rat
                                                (@Ring.toSemiring Rat
                                                  (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                        (z j))
                                    (∀
                                      (i:
                                        Fin
                                          (Nat.add
                                            (Nat.mul n n)
                                            (Nat.mul
                                              ((2:Nat))
                                              (Nat.mul
                                                (Nat.mul n n) n)))),
                                      @LE.le Rat
                                        (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                        (@Lax109476.LinearProgram.rowValue Rat
                                          (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                          (Nat.add
                                            (Nat.mul n n)
                                            (Nat.mul
                                              ((2:Nat))
                                              (Nat.mul
                                                (Nat.mul n n) n)))
                                          (Nat.add
                                            ((1:Nat))
                                            (Nat.mul
                                              (Nat.mul n n)
                                              (Nat.mul n n)))
                                          (@Lax455465Proofs.DirectedFlowLP.program n I) z i)
                                        (@Lax109476.LinearProgram.Program.b Rat
                                          (Nat.add
                                            (Nat.mul n n)
                                            (Nat.mul
                                              ((2:Nat))
                                              (Nat.mul
                                                (Nat.mul n n) n)))
                                          (Nat.add
                                            ((1:Nat))
                                            (Nat.mul
                                              (Nat.mul n n)
                                              (Nat.mul n n)))
                                          (@Lax455465Proofs.DirectedFlowLP.program n I) i))
                                    hz)))
                              "flow.primal" τ)
                            (And
                              (Lax455465Proofs.RamVirtualState.Prefix
                                (Lax455465Proofs.RamUnsignedBuffer.encode
                                  (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y
                                    (@And.left
                                      (∀
                                        (i:
                                          Fin
                                            (Nat.add
                                              (Nat.mul n n)
                                              (Nat.mul
                                                ((2:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n) n)))),
                                        @LE.le Rat
                                          (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                          (@OfNat.ofNat Rat (nat_lit 0)
                                            (@Zero.toOfNat0 Rat
                                              (@MulZeroClass.toZero Rat
                                                (@instMulZeroClassOfSemiring Rat
                                                  (@Ring.toSemiring Rat
                                                    (@DivisionRing.toRing Rat Rat.instDivisionRing))))))
                                          (y i))
                                      (∀
                                        (j:
                                          Fin
                                            (Nat.add
                                              ((1:Nat))
                                              (Nat.mul
                                                (Nat.mul n n)
                                                (Nat.mul n n)))),
                                        @LE.le Rat
                                          (@Preorder.toLE Rat (@PartialOrder.toPreorder Rat Rat.instPartialOrder))
                                          (@Lax109476.LinearProgram.Program.c Rat
                                            (Nat.add
                                              (Nat.mul n n)
                                              (Nat.mul
                                                ((2:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n) n)))
                                            (Nat.add
                                              ((1:Nat))
                                              (Nat.mul
                                                (Nat.mul n n)
                                                (Nat.mul n n)))
                                            (@Lax455465Proofs.DirectedFlowLP.program n I) j)
                                          (@Lax109476.LinearProgram.columnValue Rat
                                            (@DivisionRing.toRing Rat Rat.instDivisionRing)
                                            (Nat.add
                                              (Nat.mul n n)
                                              (Nat.mul
                                                ((2:Nat))
                                                (Nat.mul
                                                  (Nat.mul n n) n)))
                                            (Nat.add
                                              ((1:Nat))
                                              (Nat.mul
                                                (Nat.mul n n)
                                                (Nat.mul n n)))
                                            (@Lax455465Proofs.DirectedFlowLP.program n I) y j))
                                      hy)))
                                "flow.dual" τ)
                              (And
                                (Lax455465Proofs.RamVirtualState.Prefix
                                  (@Lax109476.RationalEncoding.encodeCertificate (Lax455465Proofs.RamFlowData.rows n)
                                    (Lax455465Proofs.RamFlowData.columns n)
                                    (@Lax109476.RationalCertificates.Certificate.optimal
                                      (Lax455465Proofs.RamFlowData.rows n) (Lax455465Proofs.RamFlowData.columns n) z y))
                                  "vm.output" τ)
                                (@Eq Nat (τ.vars "cert.cursor")
                                  (Nat.add
                                    (Nat.add
                                      ((1:Nat))
                                      (Nat.mul
                                        ((3:Nat))
                                        (Lax455465Proofs.RamFlowData.columns n)))
                                    (Nat.mul
                                      ((3:Nat))
                                      (Lax455465Proofs.RamFlowData.rows n)))))))))
                    (@Polynomial.eval Nat Nat.instSemiring
                      (Lax759944.BinaryWordEncoding.bitSize (@Lax455465.RationalEncoding.encodeInput n kind I))
                      timeBound)))):= @Lax455465Proofs.RamInputOptimal.exists_program
