-- Prove2me | solution 1 for Lax109476Proofs.RamSolverTotalExecution.solve_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:55:59.40928+00:00
-- url     : https://prove2.me/submissions/aa367110-b493-4f31-8553-abc46b9091d0

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamSolverFinish_finish_spec
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native

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
  Nat.lt n B→
    Nat.lt d B→
      Nat.lt ((0:Nat)) d→
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
  Nat.lt
      (HAdd.hAdd
        (HMul.hMul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((2:Nat))))
        ((3:Nat)))
      B→
    Nat.le s₁ ((1:Nat))→
      Nat.le s₂ ((1:Nat))→
        Nat.le n₁ M→
          Nat.le d₁ M→
            Nat.le n₂ M→
              Nat.le d₂ M→
                Nat.lt ((0:Nat)) d₁→
                  Nat.lt ((0:Nat)) d₂→
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

theorem BigStepB.inpBounded {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStepB B c σ σ' k) (hσ:σ.InpBounded B):σ'.InpBounded B:=by
  induction h with
  | skip => exact hσ
  | assign _ => exact fun v hv => hσ v hv
  | store _ _ _ => exact fun v hv => hσ v hv
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read h =>
      intro v hv
      refine hσ v ?_
      rw [h]
      exact List.mem_cons_of_mem _ hv
  | write _ => exact fun v hv => hσ v hv

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

@[simp] theorem length_arrOf (n:ℕ) (f:ℕ→ ℕ):(arrOf n f).length=n:=by
  simp [arrOf]

theorem replicate_eq_arrOf (n v:ℕ):List.replicate n v=arrOf n (fun _ => v):=by
  simp [arrOf,List.map_const']

theorem arrOf_congr {n:ℕ} {f g:ℕ→ ℕ} (h:∀ i < n,f i=g i):
    arrOf n f=arrOf n g:=by
  refine List.ext_getElem (by simp) fun k h₁ _ => ?_
  simp only [arrOf,List.length_map,List.length_range] at h₁
  simp [arrOf,h k h₁]

theorem set_arrOf {n i:ℕ} (f:ℕ→ ℕ) (v:ℕ):
    (arrOf n f).set i v=arrOf n (fun k => if k=i then v else f k):=by
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  rw [List.getElem_set]
  by_cases hk:k=i
  · subst hk; simp [arrOf]
  · simp [arrOf,hk,Ne.symm hk]

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

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

theorem Run.inpBounded {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hσ:σ.InpBounded B):σ'.InpBounded B:=by
  obtain ⟨_,_,hbs⟩:=h; exact hbs.inpBounded hσ

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

end Lax109476Proofs.DeterminantBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

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

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

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

theorem rational_size_upper (q:ℚ):
    bitSize (encodeRational q)≤ 4 + Nat.size q.num.natAbs + Nat.size q.den:=by
  unfold encodeRational
  rw [bitSize_cons,bitSize_cons,bitSize_cons,bitSize_nil]
  split_ifs <;> norm_num [Nat.size] <;> omega

theorem vector_size {n:ℕ} (x:Fin n→ ℚ):
    bitSize (encodeVector x)=∑ j,bitSize (encodeRational (x j)):=by
  rw [encodeVector,bitSize_flatMap,List.map_ofFn,List.sum_ofFn]
  rfl

theorem bounded_vector_size {n:ℕ} (x:Fin n→ ℚ) (B:ℕ)
    (hx:∀ j, (x j).num.natAbs≤ B∧ (x j).den≤ B):
    bitSize (encodeVector x)≤ n * (4 + 2 * Nat.size B):=by
  rw [vector_size]
  calc
    _≤ ∑ _j:Fin n, (4 + 2 * Nat.size B):=by
      apply Finset.sum_le_sum
      intro j _
      have hn:=Nat.size_le_size (hx j).1
      have hd:=Nat.size_le_size (hx j).2
      have hu:=rational_size_upper (x j)
      omega
    _=_:=by simp

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

end Lax109476Proofs.IntegerEncoding

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

namespace Lax808846Proofs.Imp

def Com.reads:Com→ Prop
  | .skip => False
  | .assign _ _ => False
  | .store _ _ _ => False
  | .seq c d => c.reads∨ d.reads
  | .ite _ c d => c.reads∨ d.reads
  | .while _ c => c.reads
  | .read _ => True
  | .write _ => False

def Com.decReads:(c:Com)→ Decidable c.reads
  | .skip => decidable_of_iff False (by rw [Com.reads])
  | .assign _ _ => decidable_of_iff False (by rw [Com.reads])
  | .store _ _ _ => decidable_of_iff False (by rw [Com.reads])
  | .seq c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .ite _ c d =>
      have:=c.decReads
      have:=d.decReads
      decidable_of_iff (c.reads∨ d.reads) (by rw [Com.reads])
  | .while _ c =>
      have:=c.decReads
      decidable_of_iff c.reads (by rw [Com.reads])
  | .read _ => decidable_of_iff True (by rw [Com.reads])
  | .write _ => decidable_of_iff False (by rw [Com.reads])

instance:DecidablePred Com.reads:=Com.decReads

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

theorem _root_.Lax808846Proofs.Imp.BigStep.inp_eq {c:Com} {σ σ':Env} {k:ℕ}
    (h:BigStep c σ σ' k) (hr:¬ c.reads):σ'.inp=σ.inp:=by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => rfl
  | seq _ _ ih ih' =>
      simp only [Com.reads,not_or] at hr
      rw [ih' hr.2,ih hr.1]
  | ite_true _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.1
  | ite_false _ _ ih => simp only [Com.reads,not_or] at hr; exact ih hr.2
  | while_true _ _ _ ih ih' =>
      simp only [Com.reads] at hr
      rw [ih' (by simpa [Com.reads] using hr),ih hr]
  | while_false _ => rfl
  | read _ => exact absurd (by rw [Com.reads]; trivial) hr
  | write _ => rfl

theorem Run.frame_var {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (y:String) (hy:y∉ c.wvars):σ'.vars y=σ.vars y:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.vars_eq hy

theorem Run.frame_arr {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (a:String) (ha:a∉ c.warrs):σ'.arrs a=σ.arrs a:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.arrs_eq ha

theorem Run.frame_inp {B:ℕ} {c:Com} {σ σ':Env} {K:ℕ} (h:Run B c σ σ' K)
    (hr:¬ c.reads):σ'.inp=σ.inp:=by
  obtain ⟨_,_,hbs⟩:=h.bigStep; exact hbs.inp_eq hr

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

theorem Spec.frame (h:Spec B P c Q K):
    Spec B P c (fun σ σ' => Q σ σ'∧
      (∀ y,y∉ c.wvars→ σ'.vars y=σ.vars y)∧
      (∀ a,a∉ c.warrs→ σ'.arrs a=σ.arrs a)∧
      (¬ c.reads→ σ'.inp=σ.inp)∧
      (c.NoWrite→ σ'.out=σ.out)) K:=by
  intro σ hσ
  obtain ⟨σ',hr,hq⟩:=h σ hσ
  exact ⟨σ',hr,hq,fun y hy => hr.frame_var y hy,fun a ha => hr.frame_arr a ha,
    fun hc => hr.frame_inp hc,fun hc => hr.out_eq hc⟩

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

namespace Lax109476Proofs.RamRational

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

end Lax109476Proofs.RamRational

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_mul (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q * r) (B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q * r=((q.num * r.num:ℤ):ℚ) / ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    ring
  rw [he]
  simp only [Int.cast_mul,Int.cast_natCast]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.num) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hn hd'
  exact ⟨hn.trans (Nat.mul_le_mul hq.1 hr.1),hd'.trans (Nat.mul_le_mul hq.2 hr.2)⟩

theorem height_encoding (q:ℚ) (B:ℕ) (hq:Height q B):
    bitSize (encodeRational q)≤ 4 + 2 * B.size:=by
  have hn:=Nat.size_le_size hq.1
  have hd:=Nat.size_le_size hq.2
  have he:=EncodingSize.rational_size_upper q
  omega

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem fractionValue_height (s n d M:ℕ) (hn:n≤ M) (hd:d≤ M) (hdpos:0 < d):
    Height (fractionValue s n d) M:=by
  obtain ⟨hnum,hden⟩:=fractionValue_num_den s n d hdpos
  exact ⟨by rw [hnum]; exact (Nat.div_le_self _ _).trans hn,
    by rw [hden]; exact (Nat.div_le_self _ _).trans hd⟩

theorem multiplyFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) multiplyFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 64):=by
  apply (multiplyFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  change 36 * (d₁ * d₂).size + _ ≤ _
  omega

end Lax109476Proofs.RamPrimitiveBounds

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

namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamPrimitiveBounds RamRationalArrays RamRounding RationalArithmeticBounds

def LeftValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "left.s") (σ.vars "left.n") (σ.vars "left.d")=q∧
    σ.vars "left.n"=q.num.natAbs∧ σ.vars "left.d"=q.den∧ σ.vars "left.s" ≤ 1

def RightValue (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "right.s") (σ.vars "right.n") (σ.vars "right.d")=q∧
    σ.vars "right.n"=q.num.natAbs∧ σ.vars "right.d"=q.den∧ σ.vars "right.s" ≤ 1

theorem multiply_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) multiplyFraction
      (fun _ τ => FractionOutput (q * r) τ) (72 * M.size + 64):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=multiplyFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

end Lax109476Proofs.RamFractionInterface

end

section

namespace Lax109476Proofs.RamFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def FieldsAgree (fields:List String) (σ τ:Env):Prop:=
  ∀ x∈ fields,τ.vars x=σ.vars x

theorem fieldsAgree_trans (fields:List String) (σ τ υ:Env)
    (hστ:FieldsAgree fields σ τ) (hτυ:FieldsAgree fields τ υ):FieldsAgree fields σ υ:=
  fun x hx => (hτυ x hx).trans (hστ x hx)

theorem spec_with_fields {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars) (ha:c.warrs=[]):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  refine ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx), ?_⟩
  funext a
  exact hr.frame_arr a (by simp [ha])

theorem spec_with_write_frame {B K:ℕ} {c:Com} {P:Env→ Prop} {Q:Env→ Env→ Prop}
    (fields:List String) (h:Spec B P c Q K)
    (hf:∀ x∈ fields,x∉ c.wvars):
    Spec B P c (fun σ τ => Q σ τ∧ FieldsAgree fields σ τ∧
      ∀ a∉ c.warrs,τ.arrs a=σ.arrs a) K:=by
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=h σ hσ
  exact ⟨τ,hr,hτ,fun x hx => hr.frame_var x (hf x hx),
    fun a ha => hr.frame_arr a ha⟩

end Lax109476Proofs.RamFrame

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

@[simp] theorem upd_self (f:ℕ→ ℕ) (k v:ℕ):upd f k v k=v:=by simp [upd]

@[simp] theorem upd_of_ne {f:ℕ→ ℕ} {k i:ℕ} (v:ℕ) (h:i ≠ k):upd f k v i=f i:=by
  simp [upd,h]

theorem set_arrOf_eq_upd {n:ℕ} (f:ℕ→ ℕ) (k v:ℕ):
    (arrOf n f).set k v=arrOf n (upd f k v):=set_arrOf f v

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

theorem Fill.arr (h:Fill a x n i g F σ):σ.arrs a=arrOf n g:=h.1

theorem Fill.counter (h:Fill a x n i g F σ):σ.vars x=i:=h.2.1

theorem Fill.le (h:Fill a x n i g F σ):i≤ n:=h.2.2.1

theorem Fill.cell (h:Fill a x n i g F σ) (hj:j < i):g j=F j:=h.2.2.2 j hj

theorem Fill.length (h:Fill a x n i g F σ):(σ.arrs a).length=n:=by
  rw [h.arr,length_arrOf]

@[simp] theorem Fill.setVar_iff (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env)
    (y:String) (v:ℕ) (hy:y ≠ x):
    Fill a x n i g F (σ.setVar y v)↔ Fill a x n i g F σ:=by
  simp [Fill,Ne.symm hy]

theorem Fill.setVar (h:Fill a x n i g F σ) (hy:y ≠ x) (v:ℕ):
    Fill a x n i g F (σ.setVar y v):=
  (Fill.setVar_iff a x n i g F σ y v hy).2 h

theorem Fill.setCell (h:Fill a x n i g F σ) (v:ℕ):
    Fill a x n i (upd g i v) F (σ.setArr a i v):=
  ⟨by rw [arrs_setArr,if_pos rfl,h.arr,set_arrOf_eq_upd],by rw [vars_setArr,h.counter],
   h.2.2.1,fun j hj => by rw [upd_of_ne _ (by omega)]; exact h.cell hj⟩

theorem Fill.bump (h:Fill a x n i g F σ) (hin:i < n) (hgi:g i=F i):
    Fill a x n (i + 1) g F (σ.setVar x (i + 1)):=
  ⟨by rw [arrs_setVar,h.arr],by simp,hin,fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.cell hj
    · exact hgi⟩

namespace Fill

def Below (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ:Env):Prop:=
  ∃ g,Fill a x n (σ.vars x) g F σ

theorem Below.le (h:Below a x n F σ):σ.vars x≤ n:=by
  obtain ⟨_,hf⟩:=h; exact hf.le

theorem Below.length (h:Below a x n F σ):(σ.arrs a).length=n:=by
  obtain ⟨_,hf⟩:=h; exact hf.length

theorem below_zero (h:σ.arrs a=arrOf n g) (hx:σ.vars x=0):Below a x n F σ:=
  ⟨g,h,rfl,by omega,fun j hj => absurd hj (by omega)⟩

theorem Below.done (h:Below a x n F σ) (hx:σ.vars x=n):
    ∃ g,σ.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j:=by
  obtain ⟨g,hf⟩:=h
  exact ⟨g,hf.arr,fun j hj => hf.cell (by omega)⟩

theorem Below.step (h:Below a x n F σ) (hlt:σ.vars x < n) (hv:v=F (σ.vars x)):
    Below a x n F ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)):=by
  obtain ⟨g,hf⟩:=h
  refine ⟨upd g (σ.vars x) v, ?_⟩
  rw [show ((σ.setArr a (σ.vars x) v).setVar x (σ.vars x + 1)).vars x=σ.vars x + 1 by simp]
  exact (hf.setCell v).bump hlt (by simp [hv])

@[simp] theorem wvars_put (a x:String) (e:Expr):(put a x e).wvars=[x]:=by
  simp [put,Com.wvars]

abbrev PutPost (a x:String) (n:ℕ) (F:ℕ→ ℕ) (σ σ':Env):Prop:=
  Below a x n F σ'∧ σ'.vars x=σ.vars x + 1

theorem put_spec (B n:ℕ) (a x:String) (e:Expr) (F:ℕ→ ℕ) (P:Env→ Prop)
    (hP:∀ σ,P σ→ Below a x n F σ∧ σ.vars x < n) (hnB:n < B)
    (he:∀ σ,P σ→ e.evalB B σ=some (F (σ.vars x))):
    Spec B P (put a x e) (PutPost a x n F) (6 + e.size):=by
  intro σ hσ
  obtain ⟨hb,hlt⟩:=hP σ hσ
  obtain ⟨g,hf⟩:=hb
  refine ⟨_, (Run.seq (Run.store (idx:=σ.vars x) (v:=F (σ.vars x))
        (evalB_var (by omega)) (he σ hσ) (by rw [hf.length]; omega))
      (Run.assign (v:=σ.vars x + 1) ?_)).mono (by simp; omega), ?_,by simp⟩
  · rw [evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)]
    simp [Bop.apply]
  · exact Below.step ⟨g,hf⟩ hlt rfl

theorem loop_spec (B n:ℕ) (a x m:String) (e:Expr) (F:ℕ→ ℕ)
    (hxm:x ≠ m) (hnB:n < B)
    (he:∀ σ,Below a x n F σ→ σ.vars m=n→ σ.vars x < n→
      e.evalB B σ=some (F (σ.vars x))):
    Spec B (fun σ => (∃ g,σ.arrs a=arrOf n g)∧ σ.vars m=n)
      (.seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x e)))
      (fun _ σ' => (∃ g,σ'.arrs a=arrOf n g∧ ∀ j,j < n→ g j=F j)∧ σ'.vars x=n)
      ((10 + e.size) * n + 6):=by
  have hbody:Spec B (fun σ => (Below a x n F σ∧ σ.vars m=n)∧ σ.vars x < n) (put a x e)
      (fun σ σ' => (Below a x n F σ'∧ σ'.vars m=n)∧ σ'.vars x=σ.vars x + 1)
      (6 + e.size):=
    ((put_spec B n a x e F _ (fun _ hσ => ⟨hσ.1.1,hσ.2⟩) hnB
      (fun _ hσ => he _ hσ.1.1 hσ.1.2 hσ.2)).frame).post
      (fun _ _ hσ hq => ⟨⟨hq.1.1,by rw [hq.2.1 m (by simp [Ne.symm hxm]),hσ.1.2]⟩,hq.1.2⟩)
  refine ((Spec.forRangeZero x m (fun σ => Below a x n F σ∧ σ.vars m=n) n (6 + e.size) hnB
    (fun _ hσ => hσ.1.le) (fun _ hσ => hσ.2) hbody).pre ?_).post ?_ |>.mono (by ring_nf; omega)
  · rintro σ ⟨⟨g,harr⟩,hm⟩
    exact ⟨below_zero (by rw [arrs_setVar]; exact harr) (by simp),by simp [Ne.symm hxm,hm]⟩
  · exact fun _ σ' _ hq => ⟨hq.1.1.done hq.2,hq.2⟩

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

namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

theorem exists_arrOf (xs:List ℕ) (n:ℕ) (h:xs.length=n):∃ g,xs=arrOf n g:=by
  refine ⟨fun i => xs.getD i 0, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [arrOf,List.getD_eq_getElem?_getD,hi]

theorem fillConstant_spec (B n v:ℕ) (a:String) (hnB:n < B) (hvB:v < B):
    Spec B (fun σ => (σ.arrs a).length=n∧ σ.vars "vec.n"=n) (fillConstant a v)
      (fun σ τ => τ.arrs a=List.replicate n v∧ τ.vars "vec.n"=n∧
        ∀ b ≠ a,τ.arrs b=σ.arrs b) (11 * n + 6):=by
  have hfill:=Lib.Fill.loop_spec B n a "vec.i" "vec.n" (.lit v) (fun _ => v)
    (by decide) hnB (by intros; exact evalB_lit hvB)
  intro σ hσ
  obtain ⟨τ,hr, ⟨g,hτg,hg⟩,_⟩:=hfill σ ⟨exists_arrOf _ _ hσ.1,hσ.2⟩
  refine ⟨τ,hr, ?_, ?_, ?_⟩
  · rw [hτg,replicate_eq_arrOf]
    exact arrOf_congr hg
  · exact (hr.frame_var "vec.n" (by simp [Lib.Fill.put,Com.wvars])).trans hσ.2
  · intro b hb
    exact hr.frame_arr b (by simp [Lib.Fill.put,Com.warrs,hb])

theorem zeroRationalArray_spec (B n:ℕ) (a:String) (hnB:n < B) (h1:1 < B):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧ σ.vars "vec.n"=n)
      (zeroRationalArray a)
      (fun σ τ => Represents a (List.replicate n 0) τ∧ τ.vars "vec.n"=n∧
        ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      (33 * n + 18):=by
  have h0:0 < B:=by omega
  have hsn:a ++ ".s" ≠ a ++ ".n" :=by simp
  have hsd:a ++ ".s" ≠ a ++ ".d" :=by simp
  have hnd:a ++ ".n" ≠ a ++ ".d" :=by simp
  rintro σ ⟨hσs,hσn,hσd,hσN⟩
  obtain ⟨τ,hr₁,hτs,hτN,hτa⟩:=fillConstant_spec B n 0 (a ++ ".s") hnB h0 σ ⟨hσs,hσN⟩
  have hτn:(τ.arrs (a ++ ".n")).length=n:=by rw [hτa _ hsn.symm]; exact hσn
  obtain ⟨υ,hr₂,hυn,hυN,hυa⟩:=fillConstant_spec B n 0 (a ++ ".n") hnB h0 τ ⟨hτn,hτN⟩
  have hυd:(υ.arrs (a ++ ".d")).length=n:=by
    rw [hυa _ hnd.symm,hτa _ hsd.symm]; exact hσd
  obtain ⟨ρ,hr₃,hρd,hρN,hρa⟩:=fillConstant_spec B n 1 (a ++ ".d") hnB h1 υ ⟨hυd,hυN⟩
  have hρs:ρ.arrs (a ++ ".s")=List.replicate n 0:=by rw [hρa _ hsd,hυa _ hsn,hτs]
  have hρn:ρ.arrs (a ++ ".n")=List.replicate n 0:=by rw [hρa _ hnd,hυn]
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_,hρN, ?_⟩
  · simp [Represents,hρs,hρn,hρd,rationalSign]
  · intro b hb
    simp at hb
    exact (hρa b hb.2.2).trans ((hυa b hb.2.1).trans (hτa b hb.1))

end Lax109476Proofs.RamZeroArray

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamFrame RationalArithmeticBounds
open RamCenterCoordinate RamZeroArray

def filled {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):List ℚ:=
  List.ofFn (fun j => if j.val < k then v j else 0)

theorem filled_zero {n:ℕ} (v:Fin n→ ℚ):filled v 0=List.replicate n 0:=by simp [filled]

theorem filled_done {n:ℕ} (v:Fin n→ ℚ):filled v n=List.ofFn v:=by
  unfold filled
  congr 1
  funext j
  simp [j.isLt]

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

namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds

theorem disjoint_not_mem (a b s:String) (hab:Disjoint a b) (hs:s∈ suffixes):
    a ++ s∉ [b ++ ".s",b ++ ".n",b ++ ".d"]:=by
  intro h
  simp at h
  rcases h with h | h | h
  · exact hab s hs ".s" (by simp [suffixes]) h
  · exact hab s hs ".n" (by simp [suffixes]) h
  · exact hab s hs ".d" (by simp [suffixes]) h

end Lax109476Proofs.RamCopy

end

section

namespace Lax109476Proofs.RamInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem safeRead_spec (B:ℕ) (x:String) (xs:List ℕ) (v:ℕ)
    (h1:1 < B) (hxsB:xs.length < B) (hv:v≤ 1)
    (hxv:x ≠ "input.valid") (hxr:x ≠ "input.remaining"):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      (safeRead x)
      (fun _ τ => τ.vars x=xs.headD 0∧ τ.inp=xs.tail∧
        τ.vars "input.remaining"=xs.length - 1∧
        τ.vars "input.valid"=if xs=[] then 0 else v) 9:=by
  rintro σ ⟨hσinp,hσlen,hσvalid,hσbound⟩
  have hrv:"input.remaining" ≠ x:=Ne.symm hxr
  have hvx:"input.valid" ≠ x:=Ne.symm hxv
  cases xs with
  | nil =>
    have hb:(Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ=some false:=by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega:0 < B))
        (evalB_var (B:=B) (σ:=σ) (x:= "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁:Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2:=
      Run.assign (evalB_lit (by omega))
    have hr₂:Run B (.assign x (.lit 0)) (σ.setVar "input.valid" 0)
        ((σ.setVar "input.valid" 0).setVar x 0) 2:=Run.assign (evalB_lit (by omega))
    refine ⟨_, (Run.ite_false hb (hr₁.seq hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    simp_all [hxv,hxr,Env.setVar]
  | cons a rest =>
    have hrestB:rest.length < B:=by simp only [List.length_cons] at hxsB; omega
    have haB:a < B:=by
      apply hσbound a
      rw [hσinp]
      simp
    have hb:(Cond.lt (.lit 0) (.var "input.remaining")).evalB B σ=some true:=by
      simpa [hσlen] using (evalB_condLt (evalB_lit (by omega:0 < B))
        (evalB_var (B:=B) (σ:=σ) (x:= "input.remaining") (by simpa [hσlen] using hxsB)))
    have hr₁:Run B (.read x) σ {σ.setVar x a with inp:=rest} 1:=Run.read hσinp
    have he:(Expr.sub (.var "input.remaining") (.lit 1)).evalB B {σ.setVar x a with inp:=rest} =
        some rest.length:=by
      have hvar:({σ.setVar x a with inp:=rest}:Env).vars "input.remaining"=rest.length + 1:=by
        simp [Env.setVar,hrv,hσlen]
      apply evalB_bin_iff.mpr
      refine ⟨rest.length + 1,1, ?_,evalB_lit h1,by simp [Bop.apply],hrestB⟩
      apply evalB_var_iff.mpr
      exact ⟨hvar.symm,by rw [hvar]; exact hxsB⟩
    have hr₂:=Run.assign (x:= "input.remaining") he
    refine ⟨_, (Run.ite_true hb (hr₁.seq hr₂)).mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
    simp_all [hxv,hxr,Env.setVar]

theorem startInput_spec (B:ℕ) (xs:List ℕ) (h1:1 < B):
    Spec B (fun σ => σ.inp=xs.length::xs∧ σ.InpBounded B) startInput
      (fun _ τ => τ.inp=xs∧ τ.vars "input.remaining"=xs.length∧
        τ.vars "input.valid"=1∧ τ.InpBounded B∧ xs.length < B) 3:=by
  rintro σ ⟨hinp,hbound⟩
  have hlenB:xs.length < B:=hbound _ (by rw [hinp]; simp)
  have hr₁:Run B (.read "input.remaining") σ {σ.setVar "input.remaining" xs.length with inp:=xs} 1:=
    Run.read hinp
  have hr₂:Run B (.assign "input.valid" (.lit 1)) {σ.setVar "input.remaining" xs.length with inp:=xs}
      (({σ.setVar "input.remaining" xs.length with inp:=xs}:Env).setVar "input.valid" 1) 2:=
    Run.assign (evalB_lit h1)
  have hr:=hr₁.seq hr₂
  refine ⟨_,hr, ?_, ?_, ?_,hr.inpBounded hbound,hlenB⟩
  all_goals simp [Env.setVar]

end Lax109476Proofs.RamInput

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

namespace Lax109476Proofs.RamReadFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamRational RamArithmetic RamFrame

theorem readRawFraction_spec (B:ℕ) (xs:List ℕ) (v:ℕ)
    (h1:1 < B) (hxsB:xs.length < B) (hv:v≤ 1):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      readRawFraction
      (fun _ τ => τ.vars "rat.s"=xs.headD 0∧ τ.vars "rat.n"=xs.tail.headD 0∧
        τ.vars "rat.d"=xs.tail.tail.headD 0∧ τ.inp=xs.drop 3∧
        τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if xs.length < 3 then 0 else v)∧ τ.InpBounded B) 27:=by
  rintro σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  obtain ⟨τ,hr₁,hτs,hτinp,hτrem,hτvalid⟩:=
    safeRead_spec B "rat.s" xs v h1 hxsB hv (by decide) (by decide)
      σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  have hτvle:(if xs=[] then 0 else v)≤ 1:=by split_ifs <;> omega
  have htailB:xs.tail.length < B:=by simp only [List.length_tail]; omega
  obtain ⟨υ,hr₂,hυn,hυinp,hυrem,hυvalid⟩:=
    safeRead_spec B "rat.n" xs.tail (if xs=[] then 0 else v) h1 htailB hτvle (by decide) (by decide)
      τ ⟨hτinp,by simpa using hτrem,hτvalid,hr₁.inpBounded hσbound⟩
  have hυs:υ.vars "rat.s"=xs.headD 0:=(hr₂.frame_var _ (by decide)).trans hτs
  have hυvle:(if xs.tail=[] then 0 else if xs=[] then 0 else v)≤ 1:=by split_ifs <;> omega
  have htailtailB:xs.tail.tail.length < B:=by simp only [List.length_tail]; omega
  obtain ⟨ξ,hr₃,hξd,hξinp,hξrem,hξvalid⟩:=
    safeRead_spec B "rat.d" xs.tail.tail (if xs.tail=[] then 0 else if xs=[] then 0 else v)
      h1 htailtailB hυvle (by decide) (by decide) υ
      ⟨hυinp,by simpa using hυrem,hυvalid, (hr₁.seq hr₂).inpBounded hσbound⟩
  have hξs:=(hr₃.frame_var "rat.s" (by decide)).trans hυs
  have hξn:=(hr₃.frame_var "rat.n" (by decide)).trans hυn
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨ξ,hrun,hξs,hξn,hξd, ?_, ?_, ?_,hrun.inpBounded hσbound⟩
  · simpa only [← List.drop_one,List.drop_drop] using hξinp
  · simp only [List.length_tail] at hξrem
    omega
  · cases xs with
    | nil => simpa using hξvalid
    | cons s ys => cases ys with
      | nil => simpa using hξvalid
      | cons n zs => cases zs with
        | nil => simpa using hξvalid
        | cons d rest =>
          have hn:¬rest.length + 1 + 1 + 1 < 3:=by omega
          simpa [hn] using hξvalid

theorem decoded_fractionValue (s n d:ℕ):
    (WordDecoding.signedNumerator s n:ℚ) / d=fractionValue s n d:=by
  simp only [WordDecoding.signedNumerator,fractionValue,Int.cast_ite,Int.cast_neg,Int.cast_natCast]
  split_ifs <;> rfl

theorem validateFraction_valid_spec (B s n d remaining v:ℕ) (h2:2 < B) (hs:s≤ 1)
    (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.s"=s∧ σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧
        σ.vars "input.remaining"=remaining∧ σ.vars "input.valid"=v)
      validateFraction
      (fun _ τ => FractionOutput (fractionValue s n d) τ∧
        τ.vars "input.remaining"=remaining∧ τ.vars "input.valid"=v)
      (36 * d.size + 24):=by
  have hsB:s < B:=by omega
  have hnrm:=spec_with_fields ["input.remaining", "input.valid"]
    (normalizeFraction_output_spec B s n d hs hn hd hdpos)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
    (by decide)
  rintro σ ⟨hσs,hσn,hσd,hσr,hσv⟩
  (expose_names;
    (refine let c0:Prop:=Nat.lt (Env.vars σ "rat.s") ((2:Nat)); let c1:Prop:=Not c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((36:Nat)) (Nat.size d)); let c4:Nat:=c3 ((24:Nat)); let c5:Env→ Prop:=(fun (x τ:Env) => And (FractionOutput (fractionValue s n d) τ) (And (@Eq Nat (Env.vars τ "input.remaining") remaining) (@Eq Nat (Env.vars τ "input.valid") v))) σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B validateFraction σ σ' c4) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:=Nat.lt ((0:Nat)) (Env.vars σ "rat.d"); let c9:Prop:=Not c8; let c10:Nat:=c3 ((16:Nat)); let c11:Env→ Env→ Prop:=FieldsAgree (@List.cons String "input.remaining" (@List.cons String "input.valid" (@List.nil String))); let c12:Env→ Prop:=c11 σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B normalizeFraction σ σ' c10) (And (FractionOutput (fractionValue s n d) σ') (And (c12 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c14:Nat→ Nat:=c2 ((1:Nat)); let c15:Cond:=Cond.lt (Expr.var "rat.s") (Expr.lit ((2:Nat))); let c16:Nat→ Nat:=c2 (c14 (Cond.size c15)); let c17:Cond:=Cond.lt (Expr.lit ((0:Nat))) (Expr.var "rat.d"); let c18:Nat→ Nat:=c2 (c14 (Cond.size c17)); let c19:Nat:=c18 c10; let c20:Com:=Com.assign "input.valid" (Expr.lit ((0:Nat))); let c21:Com:=Com.ite c17 normalizeFraction c20; let c22:Env:=Env.setVar σ "input.valid" ((0:Nat)); let c23:Nat:=c14 (Expr.size (Expr.lit ((0:Nat)))); let c24:Nat:=c18 c23; let c25:String→ Nat:=Env.vars c22; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c7) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c7) (Classical.em c8) (fun (hcase_1:c8) => @Exists.casesOn Env c13 (fun (x:@Exists Env c13) => c7) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") n) (And (@Eq Nat (Env.vars σ_1 "rat.d") d) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (σ_1 τ:Env) => And (FractionOutput (fractionValue s n d) τ) (And (c11 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c10 hnrm σ ?_) fun (w:Env) (h:And (Run B normalizeFraction σ w c10) (And (FractionOutput (fractionValue s n d) w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop→ Prop:=And (FractionOutput (fractionValue s n d) w); let c1_1:Prop:=c0_1 (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); @And.casesOn (Run B normalizeFraction σ w c10) c1_1 (fun (x:And (Run B normalizeFraction σ w c10) c1_1) => c7) h fun (left:Run B normalizeFraction σ w c10) (right:c1_1) => @Exists.intro Env c6 w (@And.intro (Run B validateFraction σ w c4) (c5 w) (RunStep.mono B validateFraction σ w (c16 c19) c4 (RunStep.ite_true B c15 c21 c20 σ w c19 (RunStep.cond_lt_true B σ (Expr.var "rat.s") (Expr.lit ((2:Nat))) (Env.vars σ "rat.s") ((2:Nat)) (RunStep.eval_var B σ "rat.s" (?nAX_g4133_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ h2) hcase) (RunStep.ite_true B c17 normalizeFraction c20 σ w c10 (RunStep.cond_lt_true B σ (Expr.lit ((0:Nat))) (Expr.var "rat.d") ((0:Nat)) (Env.vars σ "rat.d") (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4133_0_0_1)) (RunStep.eval_var B σ "rat.d" (?nAX_g4133_0_0_2)) hcase_1) left)) (?nAX_g4133_0_0_3)) ?_)) fun (hcase_1:c9) => @Exists.intro Env c6 c22 (@And.intro (Run B validateFraction σ c22 c4) (c5 c22) (RunStep.mono B validateFraction σ c22 (c16 c24) c4 (RunStep.ite_true B c15 c21 c20 σ c22 c24 (RunStep.cond_lt_true B σ (Expr.var "rat.s") (Expr.lit ((2:Nat))) (Env.vars σ "rat.s") ((2:Nat)) (RunStep.eval_var B σ "rat.s" (?nAX_g4133_0_0_4)) (RunStep.eval_lit B ((2:Nat)) σ h2) hcase) (RunStep.ite_false B c17 normalizeFraction c20 σ c22 c23 (RunStep.cond_lt_false B σ (Expr.lit ((0:Nat))) (Expr.var "rat.d") ((0:Nat)) (Env.vars σ "rat.d") (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4133_0_0_5)) (RunStep.eval_var B σ "rat.d" (?nAX_g4133_0_0_6)) hcase_1) (RunStep.assign B σ "input.valid" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4133_0_0_7))))) (?nAX_g4133_0_0_8)) ?_)) fun (hcase:c1) => @Exists.intro Env c6 c22 (@And.intro (Run B validateFraction σ c22 c4) (c5 c22) (RunStep.mono B validateFraction σ c22 (c16 c23) c4 (RunStep.ite_false B c15 c21 c20 σ c22 c23 (RunStep.cond_lt_false B σ (Expr.var "rat.s") (Expr.lit ((2:Nat))) (Env.vars σ "rat.s") ((2:Nat)) (RunStep.eval_var B σ "rat.s" (?nAX_g4133_0_0_9)) (RunStep.eval_lit B ((2:Nat)) σ h2) hcase) (RunStep.assign B σ "input.valid" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4133_0_0_10)))) (?nAX_g4133_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4133_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4133_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnrm
  all_goals simp_all [FieldsAgree]
  all_goals first | omega | (exfalso; omega)

theorem validateFraction_spec (B s n d remaining v:ℕ) (h2:2 < B)
    (hsB:s < B) (hnB:n < B) (hdB:d < B):
    Spec B (fun σ => σ.vars "rat.s"=s∧ σ.vars "rat.n"=n∧ σ.vars "rat.d"=d∧
        σ.vars "input.remaining"=remaining∧ σ.vars "input.valid"=v)
      validateFraction
      (fun _ τ => (s≤ 1∧ 0 < d→ FractionOutput (fractionValue s n d) τ)∧
        τ.vars "input.remaining"=remaining∧
        τ.vars "input.valid"=if s≤ 1∧ 0 < d then v else 0)
      (36 * d.size + 24):=by
  by_cases hgood:s≤ 1∧ 0 < d
  · apply (validateFraction_valid_spec B s n d remaining v h2 hgood.1 hnB hdB hgood.2).post
    intro σ τ hσ hτ
    exact ⟨fun _ => hτ.1,hτ.2.1,by simpa only [if_pos hgood] using hτ.2.2⟩
  · rintro σ ⟨hσs,hσn,hσd,hσr,hσv⟩
    have h0:0 < B:=by omega
    have hz:Run B (.assign "input.valid" (.lit 0)) σ (σ.setVar "input.valid" 0) 2:=
      Run.assign (evalB_lit h0)
    by_cases hs:s≤ 1
    · have hd:d=0:=by omega
      have ho:(Cond.lt (.var "rat.s") (.lit 2)).evalB B σ=some true:=by
        simpa [hσs,hs] using evalB_condLt
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hi:(Cond.lt (.lit 0) (.var "rat.d")).evalB B σ=some false:=by
        simpa [hσd,hd] using evalB_condLt (evalB_lit h0)
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.d") (by rw [hσd]; exact hdB))
      have hr:=Run.ite_true (d:=Com.assign "input.valid" (.lit 0)) ho
        (Run.ite_false (c:=normalizeFraction) hi hz)
      refine ⟨_,hr.mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simp [hgood,Env.setVar,hσr]
    · have ho:(Cond.lt (.var "rat.s") (.lit 2)).evalB B σ=some false:=by
        simpa [hσs,show ¬s < 2 by omega] using evalB_condLt
          (evalB_var (B:=B) (σ:=σ) (x:= "rat.s") (by rw [hσs]; exact hsB)) (evalB_lit h2)
      have hr:=Run.ite_false (c:=.ite (.lt (.lit 0) (.var "rat.d"))
        normalizeFraction (.assign "input.valid" (.lit 0))) ho hz
      refine ⟨_,hr.mono (by simp only [Cond.size,Expr.size]; omega), ?_⟩
      simp [hgood,Env.setVar,hσr]

theorem readRational_raw (xs:List ℕ):
    WordDecoding.readRational xs =
      if xs.headD 0≤ 1∧ 0 < xs.tail.tail.headD 0 then
        some (fractionValue (xs.headD 0) (xs.tail.headD 0) (xs.tail.tail.headD 0),xs.drop 3)
      else none:=by
  cases xs with
  | nil => simp [WordDecoding.readRational]
  | cons s ys => cases ys with
    | nil => simp [WordDecoding.readRational]
    | cons n zs => cases zs with
      | nil => simp [WordDecoding.readRational]
      | cons d rest => simp [WordDecoding.readRational,decoded_fractionValue]

theorem raw_den_positive_length (xs:List ℕ) (hd:0 < xs.tail.tail.headD 0):
    3≤ xs.length:=by
  cases xs with
  | nil => simp at hd
  | cons s ys => cases ys with
    | nil => simp at hd
    | cons n zs => cases zs with
      | nil => simp at hd
      | cons d rest => simp only [List.length_cons]; omega

theorem headD_le (xs:List ℕ) (M:ℕ) (h:∀ a∈ xs,a≤ M):xs.headD 0≤ M:=by
  cases xs with
  | nil => simp
  | cons a rest => exact h a (by simp)

theorem readFraction_spec (B M:ℕ) (xs:List ℕ) (v:ℕ)
    (h2:2 < B) (hlen:xs.length < B) (hv:v≤ 1)
    (hM:M < B) (hwords:∀ a∈ xs,a≤ M):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      readFraction
      (fun _ τ => τ.inp=xs.drop 3∧ τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if WordDecoding.readRational xs=none then 0 else v)∧
        (∀ q rest,WordDecoding.readRational xs=some (q,rest)→
          FractionOutput q τ∧ τ.inp=rest)∧ τ.InpBounded B)
      (36 * M.size + 51):=by
  have hsM:=headD_le xs M hwords
  have hnM:=headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha))
  have hdM:=headD_le xs.tail.tail M
    (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))
  rintro σ ⟨hinp,hrem,hvalid,hbound⟩
  obtain ⟨τ,hr₁,hτs,hτn,hτd,hτinp,hτrem,hτvalid,hτbound⟩:=
    readRawFraction_spec B xs v (by omega) hlen hv σ ⟨hinp,hrem,hvalid,hbound⟩
  obtain ⟨υ,hr₂,hυq,hυrem,hυvalid⟩:=validateFraction_spec B (xs.headD 0)
    (xs.tail.headD 0) (xs.tail.tail.headD 0) (xs.length - 3) (if xs.length < 3 then 0 else v)
    h2 (hsM.trans_lt hM) (hnM.trans_lt hM) (hdM.trans_lt hM)
    τ ⟨hτs,hτn,hτd,hτrem,hτvalid⟩
  have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
  have hrun:=hr₁.seq hr₂
  have hds:(xs.tail.tail.headD 0).size≤ M.size:=Nat.size_le_size hdM
  refine ⟨υ,hrun.mono (by omega),hυinp,hυrem, ?_, ?_,hr₂.inpBounded hτbound⟩
  · rw [readRational_raw]
    by_cases hg:xs.headD 0≤ 1∧ 0 < xs.tail.tail.headD 0
    · have hlong:¬xs.length < 3:=by have:=raw_den_positive_length xs hg.2; omega
      simpa only [if_pos hg,if_neg hlong,reduceCtorEq,if_false] using hυvalid
    · simpa only [if_neg hg,if_true] using hυvalid
  · intro q rest hdecode
    rw [readRational_raw] at hdecode
    split_ifs at hdecode with hg
    · have he:=Option.some.inj hdecode
      have heq:=Prod.mk.inj he
      exact ⟨by rw [← heq.1]; exact hυq hg,hυinp.trans heq.2⟩

theorem zeroResult_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zeroResult (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zeroResult σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zeroResult σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zeroResult σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4141_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g4141_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4141_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4141_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4141_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4141_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

theorem safeFraction_spec (B M:ℕ) (xs:List ℕ) (v:ℕ)
    (h2:2 < B) (hlen:xs.length < B) (hv:v≤ 1)
    (hM:M < B) (hwords:∀ a∈ xs,a≤ M):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      safeFraction
      (fun _ τ => FractionOutput (safeValue xs v) τ∧ τ.inp=xs.drop 3∧
        τ.vars "input.remaining"=xs.length - 3∧
        τ.vars "input.valid"=(if WordDecoding.readRational xs=none then 0 else v)∧
        τ.InpBounded B)
      (36 * M.size + 61):=by
  intro σ hσ
  obtain ⟨τ,hr₁,hτinp,hτrem,hτvalid,hτq,hτbound⟩:=
    readFraction_spec B M xs v h2 hlen hv hM hwords σ hσ
  have hflag:τ.vars "input.valid" ≤ 1:=by rw [hτvalid]; split_ifs <;> omega
  have h1:1 < B:=by omega
  have hflagB:=hflag.trans_lt h1
  by_cases hgood:τ.vars "input.valid"=1
  · have hv1:v=1:=by rw [hτvalid] at hgood; split_ifs at hgood <;> omega
    have hdecode:WordDecoding.readRational xs ≠ none:=by
      intro hh; simp [hh] at hτvalid; omega
    obtain ⟨⟨q,rest⟩,hsome⟩:=Option.ne_none_iff_exists'.mp hdecode
    have hq:FractionOutput (safeValue xs v) τ:=by
      simpa [safeValue,hv1,hsome] using (hτq q rest hsome).1
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B τ=some true:=by
      simpa [hgood] using evalB_condEq
        (evalB_var (B:=B) (σ:=τ) (x:= "input.valid") hflagB) (evalB_lit h1)
    exact ⟨τ, (hr₁.seq (Run.ite_true (d:=zeroResult) hb Run.skip)).mono
      (by simp only [Cond.size,Expr.size]; omega),hq,hτinp,hτrem,hτvalid,hτbound⟩
  · have hzero:safeValue xs v=0:=by
      by_cases hv1:v=1
      · have hnone:WordDecoding.readRational xs=none:=by
          by_contra hh; simp only [if_neg hh,hv1] at hτvalid; exact hgood hτvalid
        simp [safeValue,hv1,hnone]
      · simp [safeValue,hv1]
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B τ=some false:=by
      simpa [hgood] using evalB_condEq
        (evalB_var (B:=B) (σ:=τ) (x:= "input.valid") hflagB) (evalB_lit h1)
    obtain ⟨υ,hr₂,hυq⟩:=zeroResult_spec B h1 τ True.intro
    have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
    have hυrem:=(hr₂.frame_var "input.remaining" (by decide)).trans hτrem
    have hυvalid:=(hr₂.frame_var "input.valid" (by decide)).trans hτvalid
    exact ⟨υ, (hr₁.seq (Run.ite_false (c:=.skip) hb hr₂)).mono
      (by simp only [Cond.size,Expr.size]; omega),hzero.symm ▸ hυq,
      hυinp,hυrem,hυvalid,hr₂.inpBounded hτbound⟩

end Lax109476Proofs.RamReadFraction

end

section

namespace Lax109476Proofs.RamReadArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadFraction RamRational RamRationalArrays RamFrame RamCenterUpdate
open RationalArithmeticBounds RamArithmetic

theorem flag_le_one (xs:List ℕ) (v k:ℕ) (hv:v≤ 1):flag xs v k≤ 1:=by
  induction k with
  | zero => exact hv
  | succ k ih => simp only [flag]; split_ifs <;> omega

theorem safeValue_height (xs:List ℕ) (v M:ℕ) (hM:1≤ M)
    (hwords:∀ a∈ xs,a≤ M):Height (safeValue xs v) M:=by
  unfold safeValue
  split_ifs with hv
  · rw [readRational_raw]
    split_ifs with hg
    · simp only [Option.map_some,Option.getD_some]
      exact RamPrimitiveBounds.fractionValue_height _ _ _ M
        (headD_le xs.tail M (fun a ha => hwords a (List.mem_of_mem_tail ha)))
        (headD_le xs.tail.tail M
          (fun a ha => hwords a (List.mem_of_mem_tail (List.mem_of_mem_tail ha)))) hg.2
    · simpa [Height] using hM
  · simpa [Height] using hM

def Invariant (B:ℕ) (a:String) (xs:List ℕ) (v n:ℕ) (σ:Env):Prop:=
  Represents a (filled (values xs v n) (σ.vars "vec.i")) σ∧
    σ.inp=xs.drop (3 * σ.vars "vec.i")∧
    σ.vars "input.remaining"=(xs.drop (3 * σ.vars "vec.i")).length∧
    σ.vars "input.valid"=flag xs v (σ.vars "vec.i")∧
    σ.InpBounded B∧ σ.vars "vec.i" ≤ n∧ σ.vars "vec.n"=n

theorem readStep_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Invariant B a xs v n σ∧ σ.vars "vec.i" < n) (readStep a)
      (fun σ τ => Invariant B a xs v n τ∧ τ.vars "vec.i"=σ.vars "vec.i" + 1)
      (36 * M.size + 78):=by
  rintro σ ⟨⟨hσa,hσinp,hσrem,hσvalid,hσbound,hσin,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "vec.i",hσi⟩
  let tail:=xs.drop (3 * i.val)
  have htailB:tail.length < B:=by dsimp [tail]; simp only [List.length_drop]; omega
  have htailwords:∀ z∈ tail,z≤ M:=by
    intro z hz; exact hwords z (List.mem_of_mem_drop hz)
  obtain ⟨τ,hr₁,hτq,hτinp,hτrem,hτvalid,hτbound⟩:=
    safeFraction_spec B M tail (flag xs v i.val) h2 htailB (flag_le_one xs v i.val hv)
      hMB htailwords σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  have hτi:τ.vars "vec.i"=i.val:=hr₁.frame_var _ (by decide)
  have hτn:τ.vars "vec.n"=n:=(hr₁.frame_var _ (by decide)).trans hσn
  have harr:τ.arrs=σ.arrs:=by
    funext b
    exact hr₁.frame_arr b (by
      simp [safeFraction,readFraction,readRawFraction,RamInput.safeRead,validateFraction,
        normalizeFraction,gcdLoop,gcdDoubleStep,gcdStep,zeroResult,Com.warrs])
  have hτa:Represents a (filled (values xs v n) i.val) τ:=by
    simpa only [Represents,harr,i] using hσa
  have hq:Height (values xs v n i) M:=safeValue_height tail (flag xs v i.val) M hM htailwords
  obtain ⟨υ,hr₂,hυa⟩:=storeReduced_spec B a (filled (values xs v n) i.val)
    (values xs v n i) i.val (by simpa [filled] using i.isLt) (by omega) (i.isLt.trans hnB)
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) τ ⟨hτa,hτi,hτq⟩
  have hυi:υ.vars "vec.i"=i.val:=(hr₂.frame_var _ (by simp [storeReduced,Com.wvars])).trans hτi
  have hυn:υ.vars "vec.n"=n:=(hr₂.frame_var _ (by simp [storeReduced,Com.wvars])).trans hτn
  have hυinp:=(hr₂.frame_inp (by simp [storeReduced,Com.reads])).trans hτinp
  have hυrem:=(hr₂.frame_var "input.remaining" (by simp [storeReduced,Com.wvars])).trans hτrem
  have hυvalid:=(hr₂.frame_var "input.valid" (by simp [storeReduced,Com.wvars])).trans hτvalid
  have hdrop:tail.drop 3=xs.drop (3 * (i.val + 1)):=by
    dsimp [tail]; rw [List.drop_drop]; congr 1
  have hnext:Represents a (filled (values xs v n) (i.val + 1)) υ:=by
    simpa only [filled_step] using hυa
  have he:(Expr.add (.var "vec.i") (.lit 1)).evalB B υ=some (i.val + 1):=by
    simpa only [hυi,Bop.apply_add] using evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "vec.i") (by rw [hυi]; exact i.isLt.trans hnB))
      (evalB_lit (by omega:1 < B))
      (show Bop.add.apply (υ.vars "vec.i") 1 < B by rw [hυi]; simp only [Bop.apply_add]; omega)
  have hr₃:=Run.assign (x:= "vec.i") he
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨_,hrun, ⟨?_, ?_, ?_, ?_,hrun.inpBounded hσbound, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · simpa only [Env.setVar,ite_true,hdrop] using hυinp
  · simp only [Env.setVar,ite_true]
    rw [← hdrop,List.length_drop]
    exact hυrem
  · simp only [Env.setVar,ite_true,flag]
    exact hυvalid
  · change i.val + 1≤ n; exact i.isLt
  · simpa [Env.setVar] using hυn
  · simp [i]

theorem readLoop_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Represents a (List.replicate n 0) σ∧ σ.inp=xs∧
        σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "vec.n"=n)
      (readLoop a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧ τ.vars "vec.n"=n)
      ((36 * M.size + 82) * n + 6):=by
  have hlo:=Spec.forRangeZero "vec.i" "vec.n" (Invariant B a xs v n) n (36 * M.size + 78)
    hnB (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2)
    (readStep_spec B M n v a xs h2 hMB hM hnB hxB hv hwords)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa,hσinp,hσrem,hσvalid,hσbound,hσn⟩
    clear hlo
    simp_all [Invariant,filled_zero,Represents,Env.setVar,flag,Env.InpBounded]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    rcases hτ with ⟨hτa,hτinp,hτrem,hτvalid,hτbound,hτi,hτn⟩
    exact ⟨by simpa only [hcounter,filled_done] using hτa,
      by simpa only [hcounter] using hτinp,by simpa only [hcounter] using hτrem,
      by simpa only [hcounter] using hτvalid,hτbound,hτn⟩

theorem readArray_spec (B M n v:ℕ) (a:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "vec.n"=n)
      (readArray a)
      (fun _ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧ τ.vars "vec.n"=n)
      ((36 * M.size + 115) * n + 24):=by
  rintro σ ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hσbound,hσn⟩
  obtain ⟨τ,hr₁,hτa,hτn,_⟩:=RamZeroArray.zeroRationalArray_spec B n a hnB (by omega)
    σ ⟨hσs,hσnum,hσd,hσn⟩
  have hτinp:=(hr₁.frame_inp (by simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,
    Lib.Fill.put,Com.reads])).trans hσinp
  have hτrem:=(hr₁.frame_var "input.remaining" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])).trans hσrem
  have hτvalid:=(hr₁.frame_var "input.valid" (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])).trans hσvalid
  obtain ⟨υ,hr₂,hυ⟩:=readLoop_spec B M n v a xs h2 hMB hM hnB hxB hv hwords
    τ ⟨hτa,hτinp,hτrem,hτvalid,hr₁.inpBounded hσbound,hτn⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_mul]; omega),hυ⟩

end Lax109476Proofs.RamReadArray

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

namespace Lax109476Proofs.RamReadMatrix

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage WordDecoding

theorem flatten_rows {m n:ℕ} (A:Fin m→ Fin n→ ℚ):
    flatten A=(List.ofFn fun i => List.ofFn (A i)).flatten:=by
  unfold flatten
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simpa only [flatten,List.getElem_ofFn] using flatten_entry A i j

theorem encodeRows_flat {m n:ℕ} (A:Fin m→ Fin n→ ℚ):
    encodeRows A=encodeVector (fun k:Fin (m * n) => A k.divNat k.modNat):=by
  change _=(flatten A).flatMap encodeRational
  rw [flatten_rows]
  unfold encodeRows encodeVector
  simp only [List.flatten_eq_flatMap,List.flatMap_assoc]
  simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,id_eq]

end Lax109476Proofs.RamReadMatrix

end

section

namespace Lax109476Proofs.RamReadBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamRationalArrays RamFrame

def fields:List String:= ["lp.m", "lp.n", "decode.count"]

theorem readArray_wvars (a:String):(readArray a).wvars=(readArray "").wvars:=by rfl

theorem readArray_warrs (a:String):(readArray a).warrs =
    [a ++ ".s",a ++ ".n",a ++ ".d",a ++ ".s",a ++ ".s",a ++ ".n",a ++ ".d"]:=by rfl

theorem readBlock_spec (B M n v:ℕ) (a field:String) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hnB:n < B)
    (hxB:xs.length < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M)
    (hfield:field∈ fields):
    Spec B (fun σ => (σ.arrs (a ++ ".s")).length=n∧
        (σ.arrs (a ++ ".n")).length=n∧ (σ.arrs (a ++ ".d")).length=n∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars field=n)
      (readBlock a field)
      (fun σ τ => Represents a (List.ofFn (values xs v n)) τ∧ τ.inp=xs.drop (3 * n)∧
        τ.vars "input.remaining"=(xs.drop (3 * n)).length∧
        τ.vars "input.valid"=flag xs v n∧ τ.InpBounded B∧
        FieldsAgree fields σ τ∧ ∀ b∉ [a ++ ".s",a ++ ".n",a ++ ".d"],τ.arrs b=σ.arrs b)
      ((36 * M.size + 115) * n + 26):=by
  have hf:∀ x∈ fields,x∉ (readArray a).wvars:=by
    intro x hx; rw [readArray_wvars]
    simp [fields] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  have harray:=spec_with_write_frame fields
    (readArray_spec B M n v a xs h2 hMB hM hnB hxB hv hwords) hf
  rintro σ ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hσbound,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ,hfields,harrs⟩:=harray (σ.setVar "vec.n" n)
    ⟨hσs,hσnum,hσd,hσinp,hσrem,hσvalid,hr₁.inpBounded hσbound,by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.1,hτ.2.1,hτ.2.2.1,hτ.2.2.2.1,hτ.2.2.2.2.1, ?_, ?_⟩
  · intro x hx
    exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])
  · intro b hb
    apply harrs b
    rw [readArray_warrs]
    simp at hb ⊢
    tauto

end Lax109476Proofs.RamReadBlock

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

theorem finishInput_spec (B r v:ℕ) (hrB:r < B):
    Spec B (fun σ => σ.vars "input.remaining"=r∧ σ.vars "input.valid"=v)
      finishInput (fun _ τ => τ.vars "input.remaining"=r∧
        τ.vars "input.valid"=if r=0 then v else 0) 6:=by
  have h0:0 < B:=by omega
  rintro σ ⟨hσr,hσv⟩
  (expose_names;
    (refine let c0:Prop:= @Eq Nat (Env.vars σ "input.remaining") ((0:Nat)); let c1:Prop:=Not c0; let c2:Nat:= @ite Nat (@Eq Nat r ((0:Nat))) (instDecidableEqNat r ((0:Nat))) v ((0:Nat)); let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "input.remaining") r) (@Eq Nat (Env.vars τ "input.valid") c2)) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B finishInput σ σ' ((6:Nat))) (c3 σ'); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Cond:=Cond.eq (Expr.var "input.remaining") (Expr.lit ((0:Nat))); let c8:Nat→ Nat:=c5 (c6 (Cond.size c7)); let c9:Com:=Com.assign "input.valid" (Expr.lit ((0:Nat))); let c10:Env:=Env.setVar σ "input.valid" ((0:Nat)); let c11:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c12:String→ Nat:=Env.vars c10; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 σ (@And.intro (Run B finishInput σ σ ((6:Nat))) (c3 σ) (RunStep.mono B finishInput σ σ (c8 ((1:Nat))) ((6:Nat)) (RunStep.ite_true B c7 Com.skip c9 σ σ ((1:Nat)) (RunStep.cond_eq_true B σ (Expr.var "input.remaining") (Expr.lit ((0:Nat))) (Env.vars σ "input.remaining") ((0:Nat)) (RunStep.eval_var B σ "input.remaining" (?nAX_g4367_0_0_0)) (RunStep.eval_lit B ((0:Nat)) σ h0) hcase) (RunStep.skip B σ)) (?nAX_g4367_0_0_1)) ?_)) fun (hcase:c1) => @Exists.intro Env c4 c10 (@And.intro (Run B finishInput σ c10 ((6:Nat))) (c3 c10) (RunStep.mono B finishInput σ c10 (c8 c11) ((6:Nat)) (RunStep.ite_false B c7 Com.skip c9 σ c10 c11 (RunStep.cond_eq_false B σ (Expr.var "input.remaining") (Expr.lit ((0:Nat))) (Env.vars σ "input.remaining") ((0:Nat)) (RunStep.eval_var B σ "input.remaining" (?nAX_g4367_0_0_2)) (RunStep.eval_lit B ((0:Nat)) σ h0) hcase) (RunStep.assign B σ "input.valid" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ h0))) (?nAX_g4367_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4367_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4367_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4367_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4367_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]

def afterC (xs:List ℕ) (m n:ℕ):List ℕ:=(afterB xs m n).drop (3 * n)
def flagC (xs:List ℕ) (v m n:ℕ):ℕ:=flag (afterB xs m n) (flagB xs v m n) n

def Result (B:ℕ) (xs:List ℕ) (v m n:ℕ) (σ:Env):Prop:=
  Represents "lp.A" (List.ofFn (values xs v (m * n))) σ∧
    Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) σ∧
    Represents "lp.c" (List.ofFn (values (afterB xs m n) (flagB xs v m n) n)) σ∧
    σ.inp=afterC xs m n∧ σ.vars "input.remaining"=(afterC xs m n).length∧
    σ.vars "input.valid"=(if (afterC xs m n).length=0 then flagC xs v m n else 0)∧
    σ.InpBounded B∧ σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n

theorem represents_frame {B K:ℕ} {c:Com} {σ τ:Env} (a:String) (qs:List ℚ)
    (hσ:Represents a qs σ) (hr:Run B c σ τ K)
    (ha:∀ s∈ [".s", ".n", ".d"],a ++ s∉ c.warrs):Represents a qs τ:=by
  simpa only [Represents,hr.frame_arr (a ++ ".s") (ha ".s" (by simp)),
    hr.frame_arr (a ++ ".n") (ha ".n" (by simp)),
    hr.frame_arr (a ++ ".d") (ha ".d" (by simp))] using hσ

theorem readBody_spec (B M m n v:ℕ) (xs:List ℕ)
    (h2:2 < B) (hMB:M < B) (hM:1≤ M) (hmB:m < B) (hnB:n < B)
    (hmnB:m * n < B) (hxB:xs.length < B) (hv:v≤ 1)
    (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => Extents "lp.A" (m * n) σ∧ Extents "lp.b" m σ∧ Extents "lp.c" n σ∧
        σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧ σ.vars "input.valid"=v∧
        σ.InpBounded B∧ σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧ σ.vars "decode.count"=m * n)
      readBody (fun _ τ => Result B xs v m n τ)
      ((36 * M.size + 115) * (m * n + m + n) + 84):=by
  rintro σ ⟨hσA,hσb,hσc,hσinp,hσrem,hσvalid,hσbound,hσm,hσn,hσcount⟩
  obtain ⟨τ,hr₁,hτA,hτinp,hτrem,hτvalid,hτbound,hτfields,_⟩:=
    readBlock_spec B M (m * n) v "lp.A" "decode.count" xs h2 hMB hM hmnB hxB hv hwords
      (by simp [fields]) σ
      ⟨hσA ".s" (by simp),hσA ".n" (by simp),
        hσA ".d" (by simp),hσinp,hσrem,hσvalid,hσbound,hσcount⟩
  have hτb:=extents_of_run hr₁ "lp.b" m hσb
  have hτc:=extents_of_run hr₁ "lp.c" n hσc
  have hxAB:(afterA xs m n).length < B:=by dsimp [afterA]; simp only [List.length_drop]; omega
  have hwordsA:∀ z∈ afterA xs m n,z≤ M:=
    fun z hz => hwords z (List.mem_of_mem_drop hz)
  have hvA:flagA xs v m n≤ 1:=flag_le_one xs v (m * n) hv
  obtain ⟨υ,hr₂,hυb,hυinp,hυrem,hυvalid,hυbound,hυfields,harr₂⟩:=
    readBlock_spec B M m (flagA xs v m n) "lp.b" "lp.m" (afterA xs m n)
      h2 hMB hM hmB hxAB hvA hwordsA (by simp [fields]) τ
      ⟨hτb ".s" (by simp),hτb ".n" (by simp),
        hτb ".d" (by simp),hτinp,hτrem,hτvalid,hτbound,
        (hτfields _ (by simp [fields])).trans hσm⟩
  have hυA:Represents "lp.A" (List.ofFn (values xs v (m * n))) υ:=by
    simpa [Represents,harr₂ "lp.A.s" (by decide),harr₂ "lp.A.n" (by decide),
      harr₂ "lp.A.d" (by decide)] using hτA
  have hυc:=extents_of_run hr₂ "lp.c" n hτc
  have hxBB:(afterB xs m n).length < B:=by dsimp [afterB]; simp only [List.length_drop]; omega
  have hwordsB:∀ z∈ afterB xs m n,z≤ M:=
    fun z hz => hwordsA z (List.mem_of_mem_drop hz)
  have hvB:flagB xs v m n≤ 1:=flag_le_one _ _ m hvA
  obtain ⟨ξ,hr₃,hξc,hξinp,hξrem,hξvalid,hξbound,hξfields,harr₃⟩:=
    readBlock_spec B M n (flagB xs v m n) "lp.c" "lp.n" (afterB xs m n)
      h2 hMB hM hnB hxBB hvB hwordsB (by simp [fields]) υ
      ⟨hυc ".s" (by simp),hυc ".n" (by simp),
        hυc ".d" (by simp),hυinp,hυrem,hυvalid,hυbound,
        (hυfields _ (by simp [fields])).trans ((hτfields _ (by simp [fields])).trans hσn)⟩
  have hξA:Represents "lp.A" (List.ofFn (values xs v (m * n))) ξ:=by
    simpa [Represents,harr₃ "lp.A.s" (by decide),harr₃ "lp.A.n" (by decide),
      harr₃ "lp.A.d" (by decide)] using hυA
  have hξb:Represents "lp.b" (List.ofFn (values (afterA xs m n) (flagA xs v m n) m)) ξ:=by
    simpa [Represents,harr₃ "lp.b.s" (by decide),harr₃ "lp.b.n" (by decide),
      harr₃ "lp.b.d" (by decide)] using hυb
  have hxCB:(afterC xs m n).length < B:=by dsimp [afterC]; simp only [List.length_drop]; omega
  obtain ⟨ρ,hr₄,hρrem,hρvalid⟩:=finishInput_spec B (afterC xs m n).length (flagC xs v m n)
    hxCB ξ ⟨hξrem,hξvalid⟩
  have hrun:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hfields:=fieldsAgree_trans fields σ τ ξ hτfields
    (fieldsAgree_trans fields τ υ ξ hυfields hξfields)
  refine ⟨ρ,hrun.mono (by simp only [Nat.mul_add]; omega), ⟨?_, ?_, ?_, ?_,hρrem,
    hρvalid,hrun.inpBounded hσbound, ?_, ?_, ?_⟩⟩
  · exact represents_frame _ _ hξA hr₄ (by decide)
  · exact represents_frame _ _ hξb hr₄ (by decide)
  · exact represents_frame _ _ hξc hr₄ (by decide)
  · exact (hr₄.frame_inp (by decide)).trans hξinp
  · exact (hr₄.frame_var "lp.m" (by decide)).trans ((hfields _ (by simp [fields])).trans hσm)
  · exact (hr₄.frame_var "lp.n" (by decide)).trans ((hfields _ (by simp [fields])).trans hσn)
  · exact (hr₄.frame_var "decode.count" (by decide)).trans ((hfields _ (by simp [fields])).trans hσcount)

end Lax109476Proofs.RamReadBody

end

section

namespace Lax109476Proofs.RamScaleCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamFractionInterface RationalArithmeticBounds RamCopy

theorem prepareFactor_spec (B D:ℕ) (h1:1 < B) (hDB:D < B):
    Spec B (fun σ => σ.vars "scale.factor"=D) prepareFactor
      (fun _ τ => RightValue (D:ℚ) τ) 6:=by
  rintro σ hσD
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => RightValue (@Nat.cast Rat Rat.instNatCast D) τ) σ; let c1:Env:=Env.setVar σ "right.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "scale.factor"; let c3:Env:=Env.setVar c1 "right.n" c2; let c4:Env:=Env.setVar c3 "right.d" ((1:Nat)); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat)))); let c8:Nat:=c6 (Expr.size (Expr.var "scale.factor")); let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat)))); let c10:Nat:=c5 c8 c9; let c11:Com:=Com.assign "right.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B prepareFactor σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B prepareFactor σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B prepareFactor σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "scale.factor")) c11) σ c1 c4 c7 c10 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4491_0_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "scale.factor")) c11 c1 c3 c4 c8 c9 (RunStep.assign B c1 "right.n" (Expr.var "scale.factor") c2 (RunStep.eval_var B c1 "scale.factor" (?nAX_g4491_0_0_1))) (RunStep.assign B c3 "right.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 h1)))) (?nAX_g4491_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4491_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4491_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4491_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RightValue,fractionValue]

def scaleFields:List String:= ["scale.i", "scale.factor", "vec.i", "vec.n"]

set_option maxHeartbeats 0 in
theorem scaleCoordinate_spec (B M i D:ℕ) (a b:String) (xs ys:List ℚ)
    (hi:i < xs.length) (hiy:i < ys.length) (hiB:i < B) (hM:1≤ M)
    (hB:2 * M ^ 2 + 3 < B) (hq:Height xs[i] M) (hD:D≤ M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Represents a xs σ∧ Represents b ys σ∧
        σ.vars "scale.i"=i∧ σ.vars "scale.factor"=D)
      (scaleCoordinate a b)
      (fun _ τ => Represents b (ys.set i (xs[i] * (D:ℚ))) τ∧ Represents a xs τ)
      (72 * M.size + 94):=by
  have h1:1 < B:=by nlinarith
  have hMB:M < B:=by nlinarith
  have hMMB:M * M < B:=by nlinarith
  have hDH:Height (D:ℚ) M:=by simpa [Height] using And.intro hD hM
  have hresult:=height_mul xs[i] (D:ℚ) M M hq hDH
  have hload:=spec_with_fields scaleFields
    (loadLeft_spec B a xs i hi h1 hiB (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [loadLeft,Com.wvars])
    (by simp [loadLeft,Com.warrs])
  have hfactor:=spec_with_fields (scaleFields ++ ["left.s", "left.n", "left.d"])
    (prepareFactor_spec B D h1 (hD.trans_lt hMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [prepareFactor,Com.wvars]) (by simp [prepareFactor,Com.warrs])
  have hmul:=spec_with_fields scaleFields (multiply_spec B M xs[i] (D:ℚ) hB hq hDH)
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by decide)
  have hstore:=spec_with_write_frame scaleFields
    (storeReduced_spec B b ys (xs[i] * (D:ℚ)) i hiy h1 hiB
      (hresult.1.trans_lt hMMB) (hresult.2.trans_lt hMMB))
    (by intro x hx; simp [scaleFields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [storeReduced,Com.wvars])
  rintro σ ⟨hσa,hσb,hσi,hσD⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (loadLeft a) (Env.setVar σ "vec.i" (Env.vars σ "scale.i")); let c1:Rat:= @getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) xs i hi; let c2:Env→ Prop:=LeftOutput c1; let c3:Env→ Prop:=FieldsAgree scaleFields (Env.setVar σ "vec.i" (Env.vars σ "scale.i")); let c4:String→ List Nat:=Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "scale.i")); let c5:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((9:Nat))) (And (c2 σ') (And (c3 σ') (@Eq (String→ List Nat) (Env.arrs σ') c4))); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (Nat.mul ((72:Nat)) (Nat.size M)); let c8:Nat:=c7 ((94:Nat)); let c9:Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) c1 (@Nat.cast Rat Rat.instNatCast D); let c10:Env→ Prop:=Represents b (@List.set Rat ys i c9); let c11:Env→ Prop:=(fun (x τ:Env) => And (c10 τ) (Represents a xs τ)) σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B (scaleCoordinate a b) σ σ' c8) (c11 σ'); let c13:Prop:= @Exists Env c12; let c14:Env→ Env→ Prop:=FieldsAgree (@HAppend.hAppend (List String) (List String) (List String) (@instHAppendOfAppend (List String) (@List.instAppend String)) scaleFields (@List.cons String "left.s" (@List.cons String "left.n" (@List.cons String "left.d" (@List.nil String))))); let c15:Nat:=c7 ((64:Nat)); let c16:Env→ Prop:=FractionOutput c9; let c17:Env→ Prop:=LeftValue c1; let c18:Nat:=c6 ((1:Nat)) (Expr.size (Expr.var "scale.i")); let c19:Nat:=c6 c15 ((13:Nat)); let c20:Nat:=c6 ((6:Nat)) c19; let c21:Nat:=c6 ((9:Nat)) c20; @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c13) (RunStep.use B (fun (σ_1:Env) => And (Represents a xs σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") i)) (loadLeft a) (fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree scaleFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "scale.i")) ?_) fun (w:Env) (h:And (c0 w ((9:Nat))) (And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)))) => let c0_1:Prop:=c0 w ((9:Nat)); let c1_1:Prop:=And (c2 w) (And (c3 w) (@Eq (String→ List Nat) (Env.arrs w) c4)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B prepareFactor w σ' ((6:Nat))) (And (RightValue (@Nat.cast Rat Rat.instNatCast D) σ') (And (c14 w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c13) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c13) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "scale.factor") D) prepareFactor (fun (σ_1 τ:Env) => And (RightValue (@Nat.cast Rat Rat.instNatCast D) τ) (And (c14 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((6:Nat)) hfactor w ?_) fun (w_1:Env) (h_1:And (Run B prepareFactor w w_1 ((6:Nat))) (And (RightValue (@Nat.cast Rat Rat.instNatCast D) w_1) (And (c14 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B prepareFactor w w_1 ((6:Nat)); let c1_2:Prop:=And (RightValue (@Nat.cast Rat Rat.instNatCast D) w_1) (And (c14 w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction w_1 σ' c15) (And (c16 σ') (And (FieldsAgree scaleFields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c13) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c13) (RunStep.use B (fun (σ_1:Env) => And (c17 σ_1) (RightValue (@Nat.cast Rat Rat.instNatCast D) σ_1)) multiplyFraction (fun (σ_1 τ:Env) => And (c16 τ) (And (FieldsAgree scaleFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c15 hmul w_1 ?_) fun (w_2:Env) (h_2:And (Run B multiplyFraction w_1 w_2 c15) (And (c16 w_2) (And (FieldsAgree scaleFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=And (c16 w_2) (And (FieldsAgree scaleFields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c1_3:Env→ Prop:=fun (σ':Env) => And (Run B (storeReduced b) w_2 σ' ((13:Nat))) (And (c10 σ') (And (FieldsAgree scaleFields w_2 σ') (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs σ' a_1) (Env.arrs w_2 a_1)))); @And.casesOn (Run B multiplyFraction w_1 w_2 c15) c0_3 (fun (x:And (Run B multiplyFraction w_1 w_2 c15) c0_3) => c13) h_2 fun (left_2:Run B multiplyFraction w_1 w_2 c15) (right_2:c0_3) => @Exists.casesOn Env c1_3 (fun (x:@Exists Env c1_3) => c13) (RunStep.use B (fun (σ_1:Env) => And (Represents b ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") i) (c16 σ_1))) (storeReduced b) (fun (σ_1 τ:Env) => And (c10 τ) (And (FieldsAgree scaleFields σ_1 τ) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs τ a_1) (Env.arrs σ_1 a_1)))) ((13:Nat)) hstore w_2 ?_) fun (w_3:Env) (h_3:And (Run B (storeReduced b) w_2 w_3 ((13:Nat))) (And (c10 w_3) (And (FieldsAgree scaleFields w_2 w_3) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_3 a_1) (Env.arrs w_2 a_1))))) => let c0_4:Prop:=Run B (storeReduced b) w_2 w_3 ((13:Nat)); let c1_4:Prop:=And (c10 w_3) (And (FieldsAgree scaleFields w_2 w_3) (∀ a_1∉ Com.warrs (storeReduced b), @Eq (List Nat) (Env.arrs w_3 a_1) (Env.arrs w_2 a_1))); @And.casesOn c0_4 c1_4 (fun (x:And c0_4 c1_4) => c13) h_3 fun (left_3:c0_4) (right_3:c1_4) => @Exists.intro Env c12 w_3 (@And.intro (Run B (scaleCoordinate a b) σ w_3 c8) (c11 w_3) (RunStep.mono B (scaleCoordinate a b) σ w_3 (c6 c18 c21) c8 (RunStep.seq B (Com.assign "vec.i" (Expr.var "scale.i")) (Com.seq (loadLeft a) (Com.seq prepareFactor (Com.seq multiplyFraction (storeReduced b)))) σ (Env.setVar σ "vec.i" (Env.vars σ "scale.i")) w_3 c18 c21 (RunStep.assign B σ "vec.i" (Expr.var "scale.i") (Env.vars σ "scale.i") (RunStep.eval_var B σ "scale.i" (?nAX_g4494_0_0_0))) (RunStep.seq B (loadLeft a) (Com.seq prepareFactor (Com.seq multiplyFraction (storeReduced b))) (Env.setVar σ "vec.i" (Env.vars σ "scale.i")) w w_3 ((9:Nat)) c20 left (RunStep.seq B prepareFactor (Com.seq multiplyFraction (storeReduced b)) w w_1 w_3 ((6:Nat)) c19 left_1 (RunStep.seq B multiplyFraction (storeReduced b) w_1 w_2 w_3 c15 ((13:Nat)) left_2 left_3)))) (?nAX_g4494_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4494_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4494_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3))
  all_goals clear hload hfactor hmul hstore
  all_goals simp_all [scaleFields,FieldsAgree,Represents,LeftOutput,RightValue,
    LeftValue,FractionOutput,canonical_fractionValue,rationalSign_le_one,
    RamCopy.Disjoint,RamCopy.suffixes,storeReduced,Com.warrs]
  all_goals aesop

end Lax109476Proofs.RamScaleCoordinate

end

section

namespace Lax109476Proofs.RamBitLength

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem size_half_succ (n:ℕ) (hn:0 < n):(n / 2).size + 1=n.size:=by
  induction n using Nat.binaryRec' with
  | zero => omega
  | bit b n h _ =>
    rw [Nat.bit_div_two,Nat.size_bit (Nat.bit_ne_zero_iff.mpr h)]

theorem bitLengthStep_spec (B v k:ℕ) (hB:2 < B) (hv:v < B)
    (hk:k + 1 < B):
    Spec B (fun σ => σ.vars "bits.v"=v∧ σ.vars "bits.k"=k) bitLengthStep
      (fun _ σ' => σ'.vars "bits.v"=v / 2∧ σ'.vars "bits.k"=k + 1) 8:=by
  have hdiv:v / 2 < B:=(Nat.div_le_self _ _).trans_lt hv
  rintro σ ⟨hσv,hσk⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c1:Nat:=c0 v ((2:Nat)); let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat:=c2 k ((1:Nat)); let c4:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "bits.v") c1) (@Eq Nat (Env.vars σ' "bits.k") c3)) σ; let c5:Nat:=c0 (Env.vars σ "bits.v") ((2:Nat)); let c6:Env:=Env.setVar σ "bits.v" c5; let c7:Nat:=Env.vars c6 "bits.k"; let c8:Nat:=c2 c7 ((1:Nat)); let c9:Env:=Env.setVar c6 "bits.k" c8; let c10:Nat→ Nat:=c2 ((1:Nat)); let c11:Expr:=Expr.div (Expr.var "bits.v") (Expr.lit ((2:Nat))); let c12:Nat:=c10 (Expr.size c11); let c13:Expr:=Expr.add (Expr.var "bits.k") (Expr.lit ((1:Nat))); let c14:Nat:=c10 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B bitLengthStep σ σ' ((8:Nat))) (c4 σ')) c9 (@And.intro (Run B bitLengthStep σ c9 ((8:Nat))) (c4 c9) (RunStep.mono B bitLengthStep σ c9 (c2 c12 c14) ((8:Nat)) (RunStep.seq B (Com.assign "bits.v" c11) (Com.assign "bits.k" c13) σ c6 c9 c12 c14 (RunStep.assign B σ "bits.v" c11 c5 (RunStep.eval_div B σ (Expr.var "bits.v") (Expr.lit ((2:Nat))) (Env.vars σ "bits.v") ((2:Nat)) (RunStep.eval_var B σ "bits.v" (?nAX_g4666_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ hB) (?nAX_g4666_0_0_1))) (RunStep.assign B c6 "bits.k" c13 c8 (RunStep.eval_add B c6 (Expr.var "bits.k") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c6 "bits.k" (?nAX_g4666_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g4666_0_0_3)) (?nAX_g4666_0_0_4)))) (?nAX_g4666_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4666_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4666_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem bitLengthLoop_spec (B n:ℕ) (hB:2 < B) (hn:n < B):
    Spec B (fun σ => σ.vars "bits.v"=n∧ σ.vars "bits.k"=0) bitLengthLoop
      (fun _ σ' => σ'.vars "bits.v"=0∧ σ'.vars "bits.k"=n.size)
      (12 * n.size + 4):=by
  let I:=fun σ:Env => σ.vars "bits.v" ≤ n∧
    σ.vars "bits.k" + (σ.vars "bits.v").size=n.size
  have hloop:Spec B (fun σ => σ.vars "bits.v"=n∧ σ.vars "bits.k"=0)
      bitLengthLoop (fun _ σ' => I σ'∧
        (Cond.lt (.lit 0) (.var "bits.v")).evalB B σ'=some false)
      (12 * n.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "bits.v").size) 8
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))⟩
    · rintro σ ⟨hI,hc⟩
      have hvpos:0 < σ.vars "bits.v" :=by
        rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
        simpa using hc
      have hs:=size_half_succ (σ.vars "bits.v") hvpos
      have hsize:=RationalSizeBounds.size_le_self n
      have hk:σ.vars "bits.k" + 1 < B:=by
        have hp:=Nat.size_pos.mpr hvpos
        dsimp [I] at hI
        omega
      obtain ⟨τ,hr,hτv,hτk⟩:=bitLengthStep_spec B _ _ hB (hI.1.trans_lt hn) hk
        σ ⟨rfl,rfl⟩
      refine ⟨τ,hr, ?_, ?_⟩
      · dsimp [I] at hI ⊢
        rw [hτv,hτk]
        exact ⟨(Nat.div_le_self _ _).trans hI.1,by omega⟩
      · rw [hτv]; omega
    · rintro σ ⟨hσv,hσk⟩
      simp [I,hσv,hσk]
    · rintro σ ⟨hσv,_⟩
      simp only [hσv,Cond.size,Expr.size]
      omega
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hz:τ.vars "bits.v"=0:=by
    rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hI.1.trans_lt hn))] at hc
    have h:¬ 0 < τ.vars "bits.v" :=of_decide_eq_false (Option.some.inj hc)
    omega
  exact ⟨hz,by simpa [I,hz] using hI.2⟩

theorem bitLength_spec (B n:ℕ) (hB:2 < B) (hn:n < B):
    Spec B (fun σ => σ.vars "bits.v"=n) bitLength
      (fun _ σ' => σ'.vars "bits.v"=0∧ σ'.vars "bits.k"=n.size)
      (12 * n.size + 6):=by
  have hl:=bitLengthLoop_spec B n hB hn
  (expose_names;
    (refine fun (σ:Env) (a:@Eq Nat (Env.vars σ "bits.v") n) => let c0:Env:=Env.setVar σ "bits.k" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B bitLengthLoop c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 (Nat.mul ((12:Nat)) (Nat.size n)); let c4:Nat:=c3 ((4:Nat)); let c5:Env→ Prop:=fun (σ':Env) => And (c1 σ' c4) (And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size n))); let c6:Nat:=c3 ((6:Nat)); let c7:Env→ Env→ Prop:=fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size n)); let c8:Env→ Prop:=c7 σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B bitLength σ σ' c6) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:String→ Nat:=Env.vars c0; let c12:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((0:Nat)))); @Exists.casesOn Env c5 (fun (x:@Exists Env c5) => c10) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "bits.v") n) (@Eq Nat (Env.vars σ_1 "bits.k") ((0:Nat)))) bitLengthLoop c7 c4 hl c0 ?_) fun (w:Env) (h:And (c1 w c4) (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size n)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size n)); @And.casesOn (c1 w c4) c0_1 (fun (x:And (c1 w c4) c0_1) => c10) h fun (left:c1 w c4) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B bitLength σ w c6) (c8 w) (RunStep.mono B bitLength σ w (c2 c12 c4) c6 (RunStep.seq B (Com.assign "bits.k" (Expr.lit ((0:Nat)))) bitLengthLoop σ c0 w c12 c4 (RunStep.assign B σ "bits.k" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4668_0_0_0))) left) (?nAX_g4668_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4668_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4668_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

end Lax109476Proofs.RamBitLength

end

section

namespace Lax109476Proofs.RamReadHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput

theorem validateDimensions_spec (B m n r v:ℕ) (hB:(r + 2) ^ 2 < B)
    (hm:m < B) (hn:n < B):
    Spec B (fun σ => σ.vars "lp.m"=m∧ σ.vars "lp.n"=n∧
        σ.vars "input.remaining"=r∧ σ.vars "input.valid"=v)
      validateDimensions
      (fun _ τ => τ.vars "lp.m"=m∧ τ.vars "lp.n"=n∧
        τ.vars "input.remaining"=r∧
        τ.vars "input.valid"=(if m≤ r + 1∧ n≤ r + 1 then v else 0)∧
        τ.vars "decode.count"=(if m≤ r + 1∧ n≤ r + 1 then m * n else 0)) 18:=by
  have h4:4≤ (r + 2) ^ 2:=by
    simpa using Nat.pow_le_pow_left (show 2≤ r + 2 by omega) 2
  have h2:2 < B:=by omega
  have hrB:r < B:=by nlinarith
  have hr2B:r + 2 < B:=by nlinarith
  have hmul:m≤ r + 1→ n≤ r + 1→ m * n < B:=by
    intro hmm hnn
    have:=Nat.mul_le_mul hmm hnn
    nlinarith
  rintro σ ⟨hσm,hσn,hσr,hσv⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "input.remaining") ((2:Nat)); let c2:Env:=Env.setVar σ "decode.bound" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "lp.m"; let c5:Nat:=c3 "decode.bound"; let c6:Prop:=Nat.lt c4 c5; let c7:Prop:=Not c6; let c8:Nat:=c0 r ((1:Nat)); let c9:Prop:=Nat.le m c8; let c10:Prop:=Nat.le n c8; let c11:Nat→ Nat→ Nat:= @ite Nat (And c9 c10) (@instDecidableAnd c9 c10 (Nat.decLe m c8) (Nat.decLe n c8)); let c12:Nat:=c11 v ((0:Nat)); let c13:Nat→ Nat→ Nat:=Nat.mul; let c14:Nat:=c11 (c13 m n) ((0:Nat)); let c15:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "lp.m") m) (And (@Eq Nat (Env.vars τ "lp.n") n) (And (@Eq Nat (Env.vars τ "input.remaining") r) (And (@Eq Nat (Env.vars τ "input.valid") c12) (@Eq Nat (Env.vars τ "decode.count") c14))))) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B validateDimensions σ σ' ((18:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Nat:=c3 "lp.n"; let c19:Prop:=Nat.lt c18 c5; let c20:Prop:=Not c19; let c21:String→ Nat→ Env:=Env.setVar c2; let c22:Nat:=c13 c4 c18; let c23:Env:=c21 "decode.count" c22; let c24:Nat→ Nat:=c0 ((1:Nat)); let c25:Expr:=Expr.add (Expr.var "input.remaining") (Expr.lit ((2:Nat))); let c26:Nat:=c24 (Expr.size c25); let c27:Nat→ Nat:=c0 c26; let c28:Nat→ Nat:=c0 (c24 (Cond.size (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")))); let c29:Nat→ Nat:=c0 (c24 (Cond.size (Cond.lt (Expr.var "lp.n") (Expr.var "decode.bound")))); let c30:Nat:=c24 (Expr.size (Expr.mul (Expr.var "lp.m") (Expr.var "lp.n"))); let c31:Nat:=c29 c30; let c32:Nat:=c28 c31; let c33:Com:=Com.assign "decode.count" (Expr.mul (Expr.var "lp.m") (Expr.var "lp.n")); let c34:Com:=Com.ite (Cond.lt (Expr.var "lp.n") (Expr.var "decode.bound")) c33 rejectDimensions; let c35:String→ Nat:=Env.vars c23; let c36:Env:=c21 "input.valid" ((0:Nat)); let c37:Env:=Env.setVar c36 "decode.count" ((0:Nat)); let c38:Nat:=c24 (Expr.size (Expr.lit ((0:Nat)))); let c39:Nat:=c0 c38 c38; let c40:Nat:=c29 c39; let c41:Nat:=c28 c40; let c42:String→ Nat:=Env.vars c37; let c43:Nat:=c28 c39; @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c17) (Classical.em c6) (fun (hcase:c6) => @Or.casesOn c19 c20 (fun (x:Or c19 c20) => c17) (Classical.em c19) (fun (hcase_1:c19) => @Exists.intro Env c16 c23 (@And.intro (Run B validateDimensions σ c23 ((18:Nat))) (c15 c23) (RunStep.mono B validateDimensions σ c23 (c27 c32) ((18:Nat)) (RunStep.seq B (Com.assign "decode.bound" c25) (Com.ite (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions) σ c2 c23 c26 c32 (RunStep.assign B σ "decode.bound" c25 c1 (RunStep.eval_add B σ (Expr.var "input.remaining") (Expr.lit ((2:Nat))) (Env.vars σ "input.remaining") ((2:Nat)) (RunStep.eval_var B σ "input.remaining" (?nAX_g4702_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4702_0_0_1))) (RunStep.ite_true B (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions c2 c23 c31 (RunStep.cond_lt_true B c2 (Expr.var "lp.m") (Expr.var "decode.bound") c4 c5 (RunStep.eval_var B c2 "lp.m" (?nAX_g4702_0_0_2)) (RunStep.eval_var B c2 "decode.bound" (?nAX_g4702_0_0_3)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "lp.n") (Expr.var "decode.bound")) c33 rejectDimensions c2 c23 c30 (RunStep.cond_lt_true B c2 (Expr.var "lp.n") (Expr.var "decode.bound") c18 c5 (RunStep.eval_var B c2 "lp.n" (?nAX_g4702_0_0_4)) (RunStep.eval_var B c2 "decode.bound" (?nAX_g4702_0_0_5)) hcase_1) (RunStep.assign B c2 "decode.count" (Expr.mul (Expr.var "lp.m") (Expr.var "lp.n")) c22 (RunStep.eval_mul B c2 (Expr.var "lp.m") (Expr.var "lp.n") c4 c18 (RunStep.eval_var B c2 "lp.m" (?nAX_g4702_0_0_6)) (RunStep.eval_var B c2 "lp.n" (?nAX_g4702_0_0_7)) ?_))))) (?nAX_g4702_0_0_8)) ?_)) fun (hcase_1:c20) => @Exists.intro Env c16 c37 (@And.intro (Run B validateDimensions σ c37 ((18:Nat))) (c15 c37) (RunStep.mono B validateDimensions σ c37 (c27 c41) ((18:Nat)) (RunStep.seq B (Com.assign "decode.bound" c25) (Com.ite (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions) σ c2 c37 c26 c41 (RunStep.assign B σ "decode.bound" c25 c1 (RunStep.eval_add B σ (Expr.var "input.remaining") (Expr.lit ((2:Nat))) (Env.vars σ "input.remaining") ((2:Nat)) (RunStep.eval_var B σ "input.remaining" (?nAX_g4702_0_0_9)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4702_0_0_10))) (RunStep.ite_true B (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions c2 c37 c40 (RunStep.cond_lt_true B c2 (Expr.var "lp.m") (Expr.var "decode.bound") c4 c5 (RunStep.eval_var B c2 "lp.m" (?nAX_g4702_0_0_11)) (RunStep.eval_var B c2 "decode.bound" (?nAX_g4702_0_0_12)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "lp.n") (Expr.var "decode.bound")) c33 rejectDimensions c2 c37 c39 (RunStep.cond_lt_false B c2 (Expr.var "lp.n") (Expr.var "decode.bound") c18 c5 (RunStep.eval_var B c2 "lp.n" (?nAX_g4702_0_0_13)) (RunStep.eval_var B c2 "decode.bound" (?nAX_g4702_0_0_14)) hcase_1) (RunStep.seq B (Com.assign "input.valid" (Expr.lit ((0:Nat)))) (Com.assign "decode.count" (Expr.lit ((0:Nat)))) c2 c36 c37 c38 c38 (RunStep.assign B c2 "input.valid" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g4702_0_0_15))) (RunStep.assign B c36 "decode.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c36 (?nAX_g4702_0_0_16))))))) (?nAX_g4702_0_0_17)) ?_)) fun (hcase:c7) => @Exists.intro Env c16 c37 (@And.intro (Run B validateDimensions σ c37 ((18:Nat))) (c15 c37) (RunStep.mono B validateDimensions σ c37 (c27 c43) ((18:Nat)) (RunStep.seq B (Com.assign "decode.bound" c25) (Com.ite (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions) σ c2 c37 c26 c43 (RunStep.assign B σ "decode.bound" c25 c1 (RunStep.eval_add B σ (Expr.var "input.remaining") (Expr.lit ((2:Nat))) (Env.vars σ "input.remaining") ((2:Nat)) (RunStep.eval_var B σ "input.remaining" (?nAX_g4702_0_0_18)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4702_0_0_19))) (RunStep.ite_false B (Cond.lt (Expr.var "lp.m") (Expr.var "decode.bound")) c34 rejectDimensions c2 c37 c39 (RunStep.cond_lt_false B c2 (Expr.var "lp.m") (Expr.var "decode.bound") c4 c5 (RunStep.eval_var B c2 "lp.m" (?nAX_g4702_0_0_20)) (RunStep.eval_var B c2 "decode.bound" (?nAX_g4702_0_0_21)) hcase) (RunStep.seq B (Com.assign "input.valid" (Expr.lit ((0:Nat)))) (Com.assign "decode.count" (Expr.lit ((0:Nat)))) c2 c36 c37 c38 c38 (RunStep.assign B c2 "input.valid" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g4702_0_0_22))) (RunStep.assign B c36 "decode.count" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c36 (?nAX_g4702_0_0_23)))))) (?nAX_g4702_0_0_24)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4702_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4702_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem readHeader_spec (B M v:ℕ) (xs:List ℕ) (hB:(xs.length + 2) ^ 2 < B)
    (hM:M < B) (hv:v≤ 1) (hwords:∀ z∈ xs,z≤ M):
    Spec B (fun σ => σ.inp=xs∧ σ.vars "input.remaining"=xs.length∧
        σ.vars "input.valid"=v∧ σ.InpBounded B)
      readHeader
      (fun _ τ => τ.vars "lp.m"=xs.headD 0∧ τ.vars "lp.n"=xs.tail.headD 0∧
        τ.inp=xs.drop 2∧ τ.vars "input.remaining"=(xs.drop 2).length∧
        τ.vars "input.valid"=(if 2≤ xs.length∧ ValidDimensions xs then v else 0)∧
        τ.vars "decode.count"=(if ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0)∧
        τ.InpBounded B) 36:=by
  have h4:4≤ (xs.length + 2) ^ 2:=by
    simpa using Nat.pow_le_pow_left (show 2≤ xs.length + 2 by omega) 2
  have h1:1 < B:=by omega
  have hxB:xs.length < B:=by nlinarith
  rintro σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  obtain ⟨τ,hr₁,hτm,hτinp,hτrem,hτvalid⟩:=safeRead_spec B "lp.m" xs v h1 hxB hv
    (by decide) (by decide) σ ⟨hσinp,hσrem,hσvalid,hσbound⟩
  obtain ⟨υ,hr₂,hυn,hυinp,hυrem,hυvalid⟩:=safeRead_spec B "lp.n" xs.tail
    (if xs=[] then 0 else v) h1 (by simp only [List.length_tail]; omega)
    (by split_ifs <;> omega) (by decide) (by decide) τ
    ⟨hτinp,by simpa using hτrem,hτvalid,hr₁.inpBounded hσbound⟩
  have hυm:=(hr₂.frame_var "lp.m" (by decide)).trans hτm
  have hυr:υ.vars "input.remaining"=(xs.drop 2).length:=by
    simp only [List.length_tail,List.length_drop] at hυrem ⊢; omega
  have hυin:υ.inp=xs.drop 2:=by
    simpa only [← List.drop_one,List.drop_drop] using hυinp
  have hυv:υ.vars "input.valid"=if 2≤ xs.length then v else 0:=by
    cases xs with
    | nil => simpa using hυvalid
    | cons m ys => cases ys with
      | nil => simpa using hυvalid
      | cons n rest =>
        have hh:2≤ (m::n::rest).length:=by simp only [List.length_cons]; omega
        simpa [hh] using hυvalid
  have hguard:((xs.drop 2).length + 2) ^ 2 < B:=
    (Nat.pow_le_pow_left (by simp only [List.length_drop]; omega) 2).trans_lt hB
  have hmB:=(RamReadFraction.headD_le xs M hwords).trans_lt hM
  have hnB:=(RamReadFraction.headD_le xs.tail M
    (fun z hz => hwords z (List.mem_of_mem_tail hz))).trans_lt hM
  obtain ⟨ξ,hr₃,hξm,hξn,hξr,hξv,hξcount⟩:=validateDimensions_spec B
    (xs.headD 0) (xs.tail.headD 0) (xs.drop 2).length (if 2≤ xs.length then v else 0)
    hguard hmB hnB υ ⟨hυm,hυn,hυr,hυv⟩
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨ξ,hrun,hξm,hξn, (hr₃.frame_inp (by decide)).trans hυin,hξr,
    ?_,hξcount,hrun.inpBounded hσbound⟩
  by_cases hd:ValidDimensions xs
  · have he:xs.headD 0≤ (xs.drop 2).length + 1∧ xs.tail.headD 0≤ (xs.drop 2).length + 1:=hd
    simpa only [if_pos he,hd,and_true] using hξv
  · have he:¬(xs.headD 0≤ (xs.drop 2).length + 1∧ xs.tail.headD 0≤ (xs.drop 2).length + 1):=hd
    simpa only [if_neg he,hd,and_false,if_false] using hξv

end Lax109476Proofs.RamReadHeader

end

section

open scoped BigOperators

namespace Lax109476Proofs.RecoveryArithmeticBounds

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open PointRecovery CoordinateOptimization RationalArithmeticBounds
open LexicographicMinima EncodingSize

theorem program_height_size {m n:ℕ} (P:Program ℚ m n) (B:ℕ)
    (hA:∀ i j,Height (P.A i j) B) (hb:∀ i,Height (P.b i) B)
    (hc:∀ j,Height (P.c j) B):
    bitSize (encodeProgram P)≤ m + n + 2 + (m * n + m + n) * (4 + 2 * B.size):=by
  have hsA:(∑ i, ∑ j,bitSize (encodeRational (P.A i j)))≤ m * n * (4 + 2 * B.size):=by
    calc
      _≤ ∑ _i:Fin m, ∑ _j:Fin n, (4 + 2 * B.size):=by
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => height_encoding _ B (hA i j)))
      _=_:=by simp; ring
  have hsb:=bounded_vector_size P.b B hb
  have hsc:=bounded_vector_size P.c B hc
  have hm:=RationalSizeBounds.size_le_self m
  have hn:=RationalSizeBounds.size_le_self n
  rw [program_size]
  rw [vector_size] at hsb hsc
  nlinarith

end Lax109476Proofs.RecoveryArithmeticBounds

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
instance (xs:List ℕ):Decidable (AcceptedHeader xs):=by unfold AcceptedHeader; infer_instance

def Output (B:ℕ) (xs:List ℕ) (σ:Env):Prop:=
  if AcceptedHeader xs then Result B (xs.drop 2) 1 (xs.headD 0) (xs.tail.headD 0) σ
  else σ.vars "input.valid"=0∧ σ.inp=xs.drop 2∧ σ.InpBounded B

theorem decode_spec (B M:ℕ) (xs:List ℕ) (hB:(xs.length + 2) ^ 2 < B)
    (hMB:M < B) (hM:1≤ M) (hwords:∀ z∈ xs,z≤ M):
    Spec B (Input B xs) decode (fun _ τ => Output B xs τ)
      (instructionBound xs.length M.size):=by
  have h4:4≤ (xs.length + 2) ^ 2:=by
    simpa using Nat.pow_le_pow_left (show 2≤ xs.length + 2 by omega) 2
  have h2:2 < B:=by omega
  have hxB:xs.length < B:=by nlinarith
  rintro σ ⟨hσinp,hσbound,hσA,hσb,hσc⟩
  obtain ⟨τ,hr₁,hτinp,hτrem,hτvalid,hτbound,_⟩:=startInput_spec B xs (by omega)
    σ ⟨hσinp,hσbound⟩
  obtain ⟨υ,hr₂,hυm,hυn,hυinp,hυrem,hυvalid,hυcount,hυbound⟩:=
    readHeader_spec B M 1 xs hB hMB (by decide) hwords τ ⟨hτinp,hτrem,hτvalid,hτbound⟩
  have hflag:υ.vars "input.valid" ≤ 1:=by rw [hυvalid]; split_ifs <;> omega
  have hflagB:υ.vars "input.valid" < B:=by omega
  by_cases hg:AcceptedHeader xs
  · have hd:ValidDimensions xs:=hg.2
    have hmm:xs.headD 0≤ xs.length + 1:=hd.1.trans (by simp only [List.length_drop]; omega)
    have hnn:xs.tail.headD 0≤ xs.length + 1:=hd.2.trans (by simp only [List.length_drop]; omega)
    have hp:=Nat.mul_le_mul hmm hnn
    have hmB:xs.headD 0 < B:=by nlinarith
    have hnB:xs.tail.headD 0 < B:=by nlinarith
    have hmnB:xs.headD 0 * xs.tail.headD 0 < B:=by nlinarith
    have hυvalid1:υ.vars "input.valid"=1:=by simpa only [if_pos (show 2≤ xs.length∧ ValidDimensions xs from hg)] using hυvalid
    have hυcount':υ.vars "decode.count"=xs.headD 0 * xs.tail.headD 0:=
      by simpa only [if_pos hd] using hυcount
    have hυA:=extents_of_run (hr₁.seq hr₂) "lp.A" _ hσA
    have hυb:=extents_of_run (hr₁.seq hr₂) "lp.b" _ hσb
    have hυc:=extents_of_run (hr₁.seq hr₂) "lp.c" _ hσc
    simp only [if_pos hd] at hυA hυb hυc
    obtain ⟨ξ,hr₃,hξ⟩:=readBody_spec B M (xs.headD 0) (xs.tail.headD 0) 1 (xs.drop 2)
      h2 hMB hM hmB hnB hmnB (by simp only [List.length_drop]; omega) (by decide)
      (fun z hz => hwords z (List.mem_of_mem_drop hz)) υ
      ⟨hυA,hυb,hυc,hυinp,hυrem,hυvalid1,hυbound,hυm,hυn,hυcount'⟩
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B υ=some true:=by
      simpa [hυvalid1] using evalB_condEq
        (evalB_var (B:=B) (σ:=υ) (x:= "input.valid") hflagB) (evalB_lit (by omega:1 < B))
    have hcount:xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0≤
        xs.length ^ 2 + 4 * xs.length + 3:=by nlinarith
    have hcost:=Nat.mul_le_mul_left (36 * M.size + 115) hcount
    refine ⟨ξ, (hr₁.seq (hr₂.seq (Run.ite_true (d:=.skip) hb hr₃))).mono ?_, ?_⟩
    · simp only [instructionBound,Cond.size,Expr.size]; omega
    · simpa only [Output,if_pos hg] using hξ
  · have hυzero:υ.vars "input.valid"=0:=by simpa only [if_neg (show ¬(2≤ xs.length∧ ValidDimensions xs) from hg)] using hυvalid
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB B υ=some false:=by
      simpa [hυzero] using evalB_condEq
        (evalB_var (B:=B) (σ:=υ) (x:= "input.valid") hflagB) (evalB_lit (by omega:1 < B))
    exact ⟨υ, (hr₁.seq (hr₂.seq (Run.ite_false (c:=readBody) hb Run.skip))).mono
      (by simp only [instructionBound,Cond.size,Expr.size]; omega),
      by simpa only [Output,if_neg hg] using And.intro hυzero (And.intro hυinp hυbound)⟩

theorem decode_bounded_spec (xs:List ℕ) (w:ℕ) (hw:wordWidth (Lax759944.BinaryWordEncoding.bitSize xs)≤ w):
    Spec (2 ^ w) (Input (2 ^ w) xs) decode (fun _ τ => Output (2 ^ w) xs τ)
      (instructionBound (Lax759944.BinaryWordEncoding.bitSize xs)
        (Lax759944.BinaryWordEncoding.bitSize xs + 1)):=by
  let L:=Lax759944.BinaryWordEncoding.bitSize xs
  have hlen:xs.length≤ L:=WordSolverSize.length_le_bitSize xs
  have hpow:L + 2 < 2 ^ (L + 2):=Nat.lt_two_pow_self
  have hsquare:(L + 2) ^ 2 < 2 ^ (2 * (L + 2)):=by
    have hh:=Nat.pow_lt_pow_left hpow (by decide:2 ≠ 0)
    simpa only [← pow_mul,Nat.mul_comm] using hh
  have hexp:2 * (L + 2)≤ w:=by dsimp only [wordWidth] at hw; omega
  have hB:(xs.length + 2) ^ 2 < 2 ^ w:=
    ((Nat.pow_le_pow_left (by omega:xs.length + 2≤ L + 2) 2).trans_lt hsquare).trans_le
      (Nat.pow_le_pow_right (by decide) hexp)
  have hMB:2 ^ L < 2 ^ w:=
    Nat.pow_lt_pow_right (by decide) (by dsimp only [wordWidth] at hw; omega)
  have hM:1≤ 2 ^ L:=Nat.one_le_pow L 2 (by decide)
  have hwords:∀ z∈ xs,z≤ 2 ^ L:=by
    intro z hz
    exact ((Nat.lt_size_self z).trans_le
      (Nat.pow_le_pow_right (by decide) (WordSolverSize.member_size_le hz))).le
  apply (decode_spec (2 ^ w) (2 ^ L) xs hB hMB hM hwords).mono
  rw [Nat.size_pow]
  have hs:=Nat.pow_le_pow_left hlen 2
  have hsum:xs.length ^ 2 + 4 * xs.length + 3≤ L ^ 2 + 4 * L + 3:=by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (36 * (L + 1) + 115) hsum) 127

end Lax109476Proofs.RamDecoder

end

section

namespace Lax109476Proofs.RamEncodedSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RamBitLength RamFrame RamRationalArrays RationalArithmeticBounds EncodingSize

theorem countWord_spec (B a t:ℕ) (x:String) (h2:2 < B) (ha:a < B)
    (ht:t + a.size + 1 < B):
    Spec B (fun σ => σ.vars x=a∧ σ.vars "size.total"=t) (countWord x)
      (fun _ τ => τ.vars "size.total"=t + a.size + 1) (12 * a.size + 14):=by
  have htB:t < B:=by omega
  have haddB:t + a.size < B:=by omega
  have hsizeB:a.size < B:=by omega
  have hbits:=spec_with_fields ["size.total"] (bitLength_spec B a h2 ha)
    (by intro y hy; simp at hy; subst y; decide) (by decide)
  rintro σ ⟨hσx,hσt⟩
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B bitLength (Env.setVar σ "bits.v" (Env.vars σ x)); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat:=c1 (Nat.mul ((12:Nat)) (Nat.size a)); let c3:Nat:=c2 ((6:Nat)); let c4:Env→ Prop:=FieldsAgree (@List.cons String "size.total" (@List.nil String)) (Env.setVar σ "bits.v" (Env.vars σ x)); let c5:String→ List Nat:=Env.arrs (Env.setVar σ "bits.v" (Env.vars σ x)); let c6:Env→ Prop:=fun (σ':Env) => And (c0 σ' c3) (And (And (@Eq Nat (Env.vars σ' "bits.v") ((0:Nat))) (@Eq Nat (Env.vars σ' "bits.k") (Nat.size a))) (And (c4 σ') (@Eq (String→ List Nat) (Env.arrs σ') c5))); let c7:Nat:=c2 ((14:Nat)); let c8:Nat:=c1 (c1 t (Nat.size a)) ((1:Nat)); let c9:Env→ Prop:=(fun (x_1 τ:Env) => @Eq Nat (Env.vars τ "size.total") c8) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B (countWord x) σ σ' c7) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Nat→ Nat:=c1 ((1:Nat)); let c13:Nat:=c12 (Expr.size (Expr.var x)); let c14:Expr:=Expr.add (Expr.add (Expr.var "size.total") (Expr.var "bits.k")) (Expr.lit ((1:Nat))); let c15:Nat:=c12 (Expr.size c14); let c16:Nat:=c1 c3 c15; let c17:Com:=Com.assign "size.total" c14; @Exists.casesOn Env c6 (fun (x_1:@Exists Env c6) => c11) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "bits.v") a) bitLength (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "bits.v") ((0:Nat))) (@Eq Nat (Env.vars τ "bits.k") (Nat.size a))) (And (FieldsAgree (@List.cons String "size.total" (@List.nil String)) σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c3 hbits (Env.setVar σ "bits.v" (Env.vars σ x)) ?_) fun (w:Env) (h:And (c0 w c3) (And (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size a))) (And (c4 w) (@Eq (String→ List Nat) (Env.arrs w) c5)))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "bits.v") ((0:Nat))) (@Eq Nat (Env.vars w "bits.k") (Nat.size a))) (And (c4 w) (@Eq (String→ List Nat) (Env.arrs w) c5)); let c1_1:Nat:=c1 (Env.vars w "size.total") (Env.vars w "bits.k"); let c2_1:Nat:=c1 c1_1 ((1:Nat)); let c3_1:Env:=Env.setVar w "size.total" c2_1; @And.casesOn (c0 w c3) c0_1 (fun (x_1:And (c0 w c3) c0_1) => c11) h fun (left:c0 w c3) (right:c0_1) => @Exists.intro Env c10 c3_1 (@And.intro (Run B (countWord x) σ c3_1 c7) (c9 c3_1) (RunStep.mono B (countWord x) σ c3_1 (c1 c13 c16) c7 (RunStep.seq B (Com.assign "bits.v" (Expr.var x)) (Com.seq bitLength c17) σ (Env.setVar σ "bits.v" (Env.vars σ x)) c3_1 c13 c16 (RunStep.assign B σ "bits.v" (Expr.var x) (Env.vars σ x) (RunStep.eval_var B σ x (?nAX_g4745_0_0_0))) (RunStep.seq B bitLength c17 (Env.setVar σ "bits.v" (Env.vars σ x)) w c3_1 c3 c15 left (RunStep.assign B w "size.total" c14 c2_1 (RunStep.eval_add B w (Expr.add (Expr.var "size.total") (Expr.var "bits.k")) (Expr.lit ((1:Nat))) c1_1 ((1:Nat)) (RunStep.eval_add B w (Expr.var "size.total") (Expr.var "bits.k") (Env.vars w "size.total") (Env.vars w "bits.k") (RunStep.eval_var B w "size.total" ?_) (RunStep.eval_var B w "bits.k" (?nAX_g4745_0_0_1)) ?_) (RunStep.eval_lit B ((1:Nat)) w (?nAX_g4745_0_0_2)) ?_)))) (?nAX_g4745_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4745_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4745_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4745_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4745_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hbits
  all_goals simp_all [FieldsAgree]
  all_goals omega

theorem rational_bits (q:ℚ):bitSize (encodeRational q) =
    (rationalSign q).size + q.num.natAbs.size + q.den.size + 3:=by
  simp only [encodeRational,rationalSign,bitSize_cons,bitSize_nil]
  omega

theorem countFraction_spec (B H t:ℕ) (q:ℚ) (h2:2 < B) (hH:1≤ H)
    (hHB:H < B) (hq:Height q H) (ht:t + bitSize (encodeRational q) < B):
    Spec B (fun σ => LeftOutput q σ∧ σ.vars "size.total"=t) countFraction
      (fun _ τ => LeftOutput q τ∧ τ.vars "size.total"=t + bitSize (encodeRational q))
      (36 * H.size + 42):=by
  have hsH:=(rationalSign_le_one q).trans hH
  have hsB:=hsH.trans_lt hHB
  have hnB:=hq.1.trans_lt hHB
  have hdB:=hq.2.trans_lt hHB
  have hbits:=rational_bits q
  rintro σ ⟨⟨hσs,hσn,hσd⟩,hσt⟩
  obtain ⟨τ,hr₁,hτt⟩:=countWord_spec B (rationalSign q) t "left.s" h2 hsB (by omega)
    σ ⟨hσs,hσt⟩
  have hτn:=(hr₁.frame_var "left.n" (by decide)).trans hσn
  have hτd:=(hr₁.frame_var "left.d" (by decide)).trans hσd
  obtain ⟨υ,hr₂,hυt⟩:=countWord_spec B q.num.natAbs (t + (rationalSign q).size + 1)
    "left.n" h2 hnB (by omega) τ ⟨hτn,hτt⟩
  have hυd:=(hr₂.frame_var "left.d" (by decide)).trans hτd
  obtain ⟨ξ,hr₃,hξt⟩:=countWord_spec B q.den
    (t + (rationalSign q).size + 1 + q.num.natAbs.size + 1) "left.d" h2 hdB (by omega)
      υ ⟨hυd,hυt⟩
  have hrun:=hr₁.seq (hr₂.seq hr₃)
  have hss:=Nat.size_le_size hsH
  have hns:=Nat.size_le_size hq.1
  have hds:=Nat.size_le_size hq.2
  refine ⟨ξ,hrun.mono (by omega), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (hrun.frame_var "left.s" (by decide)).trans hσs
  · exact (hrun.frame_var "left.n" (by decide)).trans hσn
  · exact (hrun.frame_var "left.d" (by decide)).trans hσd
  · omega

def prefixBits {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):ℕ:=
  bitSize ((List.ofFn v).take k |>.flatMap encodeRational)

theorem prefix_zero {n:ℕ} (v:Fin n→ ℚ):prefixBits v 0=0:=rfl

theorem prefix_done {n:ℕ} (v:Fin n→ ℚ):prefixBits v n=bitSize (encodeVector v):=by
  unfold prefixBits encodeVector
  rw [show (List.ofFn v).take n=List.ofFn v from
    by simpa only [List.length_ofFn] using List.take_length (l:=List.ofFn v)]

theorem prefix_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    prefixBits v (i.val + 1)=prefixBits v i.val + bitSize (encodeRational (v i)):=by
  have hi:i.val < (List.ofFn v).length:=by simp
  unfold prefixBits
  rw [← List.take_concat_get hi]
  simp [List.concat_eq_append,List.flatMap_append,bitSize_append,bitSize_nil]

theorem prefix_le {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):
    prefixBits v k≤ bitSize (encodeVector v):=by
  have he:prefixBits v k + bitSize ((List.ofFn v).drop k |>.flatMap encodeRational) =
      bitSize (encodeVector v):=by
    rw [prefixBits, ← bitSize_append, ← List.flatMap_append,List.take_append_drop]
    rfl
  omega

def Invariant (a:String) {n:ℕ} (v:Fin n→ ℚ) (t:ℕ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧ σ.vars "size.total"=t + prefixBits v (σ.vars "size.i")∧
    σ.vars "size.i" ≤ n∧ σ.vars "vec.n"=n

theorem countStep_warrs (a:String):(countStep a).warrs=[]:=by rfl

theorem countStep_spec (B H n t:ℕ) (a:String) (v:Fin n→ ℚ)
    (h2:2 < B) (hH:1≤ H) (hHB:H < B) (hnB:n < B)
    (hv:∀ i,Height (v i) H) (ht:t + bitSize (encodeVector v) < B):
    Spec B (fun σ => Invariant a v t σ∧ σ.vars "size.i" < n) (countStep a)
      (fun σ τ => Invariant a v t τ∧ τ.vars "size.i"=σ.vars "size.i" + 1)
      (36 * H.size + 57):=by
  rintro σ ⟨⟨hσa,hσt,hσiN,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "size.i",hσi⟩
  have hiB:i.val < B:=i.isLt.trans hnB
  have hr₁:Run B (.assign "vec.i" (.var "size.i")) σ (σ.setVar "vec.i" i.val) 2:=
    Run.assign (by simpa only [i] using evalB_var (B:=B) (σ:=σ) (x:= "size.i") hiB)
  obtain ⟨τ,hr₂,hτq⟩:=loadLeft_spec B a (List.ofFn v) i.val (by simp) (by omega) hiB
    (by simpa using (hv i).1.trans_lt hHB) (by simpa using (hv i).2.trans_lt hHB)
    (σ.setVar "vec.i" i.val) ⟨hσa,by simp⟩
  have hτq':LeftOutput (v i) τ:=by simpa only [List.getElem_ofFn,Fin.eta] using hτq
  have hτt:τ.vars "size.total"=t + prefixBits v i.val:=
    (hr₂.frame_var _ (by simp [loadLeft,Com.wvars])).trans hσt
  have htcoord:t + prefixBits v i.val + bitSize (encodeRational (v i)) < B:=by
    have hh:=prefix_le v (i.val + 1)
    rw [prefix_step] at hh
    omega
  obtain ⟨υ,hr₃,hυq,hυt⟩:=countFraction_spec B H (t + prefixBits v i.val) (v i)
    h2 hH hHB (hv i) htcoord τ ⟨hτq',hτt⟩
  have hpre:=hr₁.seq (hr₂.seq hr₃)
  have hυi:υ.vars "size.i"=i.val:=hpre.frame_var _ (by simp [loadLeft,
    countFraction,countWord,bitLength,bitLengthLoop,bitLengthStep,Com.wvars])
  have hυn:υ.vars "vec.n"=n:=(hpre.frame_var _ (by simp [loadLeft,
    countFraction,countWord,bitLength,bitLengthLoop,bitLengthStep,Com.wvars])).trans hσn
  have he:(Expr.add (.var "size.i") (.lit 1)).evalB B υ=some (i.val + 1):=by
    simpa only [hυi,Bop.apply_add] using evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "size.i") (by rw [hυi]; exact hiB))
      (evalB_lit (by omega:1 < B))
      (show Bop.add.apply (υ.vars "size.i") 1 < B by rw [hυi]; simp only [Bop.apply_add]; omega)
  have hr₄:=Run.assign (x:= "size.i") he
  have hrun:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have harrs:(υ.setVar "size.i" (i.val + 1)).arrs=σ.arrs:=by
    funext b
    exact hrun.frame_arr b (by change b∉ (countStep a).warrs; rw [countStep_warrs]; simp)
  refine ⟨_,hrun.mono (by simp only [Expr.size]; omega), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,harrs] using hσa
  · simp only [vars_setVar,ite_true,show "size.total" ≠ "size.i" by decide,ite_false]
    rw [prefix_step]
    omega
  · change i.val + 1≤ n; exact i.isLt
  · simpa [Env.setVar] using hυn
  · simp [i]

theorem countArray_spec (B H n t:ℕ) (a:String) (v:Fin n→ ℚ)
    (h2:2 < B) (hH:1≤ H) (hHB:H < B) (hnB:n < B)
    (hv:∀ i,Height (v i) H) (ht:t + bitSize (encodeVector v) < B):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "size.total"=t∧ σ.vars "vec.n"=n)
      (countArray a)
      (fun _ τ => Represents a (List.ofFn v) τ∧
        τ.vars "size.total"=t + bitSize (encodeVector v)∧ τ.vars "vec.n"=n)
      ((36 * H.size + 61) * n + 6):=by
  have hlo:=Spec.forRangeZero "size.i" "vec.n" (Invariant a v t) n (36 * H.size + 57) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (countStep_spec B H n t a v h2 hH hHB hnB hv ht)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa,hσt,hσn⟩
    clear hlo
    simp_all [Invariant,prefix_zero,Represents,Env.setVar]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨hτ.1,by simpa only [hcounter,prefix_done] using hτ.2.1,hτ.2.2.2⟩

end Lax109476Proofs.RamEncodedSize

end

section

namespace Lax109476Proofs.RamSizeBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamRationalArrays RamFrame RationalArithmeticBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding RamReadBlock

theorem countArray_wvars (a:String):(countArray a).wvars=(countArray "").wvars:=by rfl

theorem countBlock_spec (B H n t:ℕ) (a field:String) (v:Fin n→ ℚ)
    (h2:2 < B) (hH:1≤ H) (hHB:H < B) (hnB:n < B)
    (hv:∀ i,Height (v i) H) (ht:t + bitSize (encodeVector v) < B):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "size.total"=t∧ σ.vars field=n)
      (countBlock a field)
      (fun σ τ => τ.vars "size.total"=t + bitSize (encodeVector v)∧
        FieldsAgree fields σ τ∧ τ.arrs=σ.arrs)
      ((36 * H.size + 61) * n + 8):=by
  have harray:=spec_with_fields fields (countArray_spec B H n t a v h2 hH hHB hnB hv ht)
    (by intro x hx; rw [countArray_wvars]; simp [fields] at hx;
        rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
  rintro σ ⟨hσa,hσt,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ,hfields,harr⟩:=harray (σ.setVar "vec.n" n) ⟨hσa,hσt,by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.2.1, ?_,harr⟩
  intro x hx
  exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])

end Lax109476Proofs.RamSizeBlock

end

section

namespace Lax109476Proofs.RamProgramSize

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamSizeBlock RamRationalArrays RamFrame RamStoredProgram RamReadBlock
open RationalArithmeticBounds EncodingSize

theorem program_bits_flat {m n:ℕ} (P:Program ℚ m n):
    bitSize (encodeProgram P)=m.size + n.size + 2 +
      bitSize (encodeVector (fun k:Fin (m * n) => P.A k.divNat k.modNat)) +
      bitSize (encodeVector P.b) + bitSize (encodeVector P.c):=by
  rw [WordDecoding.encodeProgram_rows,RamReadMatrix.encodeRows_flat]
  simp only [bitSize_cons,bitSize_append]
  omega

theorem countWord_wvars (x:String):(countWord x).wvars=(countWord "").wvars:=by rfl

theorem countWord_frame_spec (B a t:ℕ) (x:String) (h2:2 < B) (ha:a < B)
    (ht:t + a.size + 1 < B):
    Spec B (fun σ => σ.vars x=a∧ σ.vars "size.total"=t) (countWord x)
      (fun σ τ => τ.vars "size.total"=t + a.size + 1∧
        FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) (12 * a.size + 14):=by
  exact spec_with_fields fields (countWord_spec B a t x h2 ha ht)
    (by
      intro y hy
      rw [countWord_wvars]
      simp [fields] at hy
      rcases hy with rfl | rfl | rfl <;> decide) (by rfl)

set_option maxHeartbeats 0 in
theorem prepareSize_spec (B H m n:ℕ) (P:Program ℚ m n)
    (h2:2 < B) (hH:1≤ H) (hHB:H < B) (hmB:m < B) (hnB:n < B)
    (hmnB:m * n < B) (hA:∀ i j,Height (P.A i j) H)
    (hb:∀ i,Height (P.b i) H) (hc:∀ j,Height (P.c j) H)
    (hL:bitSize (encodeProgram P) < B):
    Spec B (RepresentsProgram P) prepareSize
      (fun σ τ => τ.vars "input.bits"=bitSize (encodeProgram P)∧
        RepresentsProgram P τ∧ τ.arrs=σ.arrs)
      ((36 * H.size + 61) * (m * n + m + n) + 12 * m.size + 12 * n.size + 56):=by
  let Avec:Fin (m * n)→ ℚ:=fun k => P.A k.divNat k.modNat
  let aBits:=bitSize (encodeVector Avec)
  let bBits:=bitSize (encodeVector P.b)
  let cBits:=bitSize (encodeVector P.c)
  have hbits:bitSize (encodeProgram P)=m.size + n.size + 2 + aBits + bBits + cBits:=
    program_bits_flat P
  have hm:=countWord_frame_spec B m 0 "lp.m" h2 hmB (by omega)
  have hn:=countWord_frame_spec B n (m.size + 1) "lp.n" h2 hnB (by omega)
  have hmat:=countBlock_spec B H (m * n) (m.size + n.size + 2) "lp.A" "decode.count" Avec
    h2 hH hHB hmnB (fun k => hA k.divNat k.modNat) (by omega)
  have hbound:=countBlock_spec B H m (m.size + n.size + 2 + aBits) "lp.b" "lp.m" P.b
    h2 hH hHB hmB hb (by omega)
  have hobj:=countBlock_spec B H n (m.size + n.size + 2 + aBits + bBits) "lp.c" "lp.n" P.c
    h2 hH hHB hnB hc (by omega)
  rintro σ ⟨hσA,hσb,hσc,hσm,hσn,hσcount⟩
  let C:=36 * H.size + 61
  have hcost:C * (m * n + m + n)=C * (m * n) + C * m + C * n:=by simp only [Nat.mul_add]
  rw [hcost]
  dsimp only [C]
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "size.total" ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B (countWord "lp.m") c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c3 ((12:Nat)); let c5:Nat:=c4 (Nat.size m); let c6:Nat:=c2 c5 ((14:Nat)); let c7:Nat:=c2 (c2 ((0:Nat)) (Nat.size m)) ((1:Nat)); let c8:Env→ Prop:=FieldsAgree fields c0; let c9:String→ List Nat:=Env.arrs c0; let c10:Env→ Prop:=fun (σ':Env) => And (c1 σ' c6) (And (@Eq Nat (Env.vars σ' "size.total") c7) (And (c8 σ') (@Eq (String→ List Nat) (Env.arrs σ') c9))); let c11:Nat→ Nat:=c3 (c2 (c3 ((36:Nat)) (Nat.size H)) ((61:Nat))); let c12:Nat:=c3 m n; let c13:Nat→ Nat:=c2 (c11 c12); let c14:Nat:=c11 m; let c15:Nat:=c11 n; let c16:Nat:=c4 (Nat.size n); let c17:Nat:=c2 (c2 (c2 (c2 (c13 c14) c15) c5) c16) ((56:Nat)); let c18:Env→ Prop:=fun (σ':Env) => And (Run B prepareSize σ σ' c17) (And (@Eq Nat (Env.vars σ' "input.bits") (bitSize (@encodeProgram m n P))) (And (@RepresentsProgram m n P σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c19:String→ Nat:=Env.vars c0; let c20:Nat:=c2 c16 ((14:Nat)); let c21:Nat→ Nat:=c2 (Nat.size m); let c22:Nat:=c21 ((1:Nat)); let c23:Nat:=c2 (c2 c22 (Nat.size n)) ((1:Nat)); let c24:Nat:=c13 ((8:Nat)); let c25:Nat:=c2 (c21 (Nat.size n)) ((2:Nat)); let c26:Nat→ Nat:=c2 c25; let c27:Nat:=c26 (bitSize (@encodeVector c12 Avec)); let c28:Env→ Prop:=Represents "lp.A" (@List.ofFn Rat c12 Avec); let c29:Nat:=c2 c14 ((8:Nat)); let c30:Nat:=c26 aBits; let c31:Nat→ Nat:=c2 c30; let c32:Nat:=c31 (bitSize (@encodeVector m (@Program.b Rat m n P))); let c33:Env→ Prop:=Represents "lp.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c34:Nat:=c2 c15 ((8:Nat)); let c35:Nat:=c31 bBits; let c36:Nat:=c2 c35 (bitSize (@encodeVector n (@Program.c Rat m n P))); let c37:Env→ Prop:=Represents "lp.c" (@List.ofFn Rat n (@Program.c Rat m n P)); let c38:Nat→ Nat:=c2 ((1:Nat)); let c39:Nat:=c38 (Expr.size (Expr.lit ((0:Nat)))); let c40:Nat:=c38 (Expr.size (Expr.var "size.total")); let c41:Nat:=c2 c34 c40; let c42:Nat:=c2 c29 c41; let c43:Nat:=c2 c24 c42; let c44:Nat:=c2 c20 c43; let c45:Nat:=c2 c6 c44; let c46:Com:=Com.seq (countBlock "lp.c" "lp.n") (Com.assign "input.bits" (Expr.var "size.total")); let c47:Com:=Com.seq (countBlock "lp.b" "lp.m") c46; let c48:Com:=Com.seq (countBlock "lp.A" "decode.count") c47; let c49:Com:=Com.seq (countWord "lp.n") c48; @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "lp.m") m) (@Eq Nat (Env.vars σ_1 "size.total") ((0:Nat)))) (countWord "lp.m") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "size.total") c7) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c6 hm c0 ?_) fun (w:Env) (h:And (c1 w c6) (And (@Eq Nat (Env.vars w "size.total") c7) (And (c8 w) (@Eq (String→ List Nat) (Env.arrs w) c9)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "size.total") c7) (And (c8 w) (@Eq (String→ List Nat) (Env.arrs w) c9)); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B (countWord "lp.n") w σ' c20) (And (@Eq Nat (Env.vars σ' "size.total") c23) (And (FieldsAgree fields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn (c1 w c6) c0_1 (fun (x:And (c1 w c6) c0_1) => @Exists Env c18) h fun (left:c1 w c6) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "lp.n") n) (@Eq Nat (Env.vars σ_1 "size.total") c22)) (countWord "lp.n") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "size.total") c23) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c20 hn w ?_) fun (w_1:Env) (h_1:And (Run B (countWord "lp.n") w w_1 c20) (And (@Eq Nat (Env.vars w_1 "size.total") c23) (And (FieldsAgree fields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B (countWord "lp.n") w w_1 c20; let c1_2:Prop:=And (@Eq Nat (Env.vars w_1 "size.total") c23) (And (FieldsAgree fields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B (countBlock "lp.A" "decode.count") w_1 σ' c24) (And (@Eq Nat (Env.vars σ' "size.total") c27) (And (FieldsAgree fields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => @Exists Env c18) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (c28 σ_1) (And (@Eq Nat (Env.vars σ_1 "size.total") c25) (@Eq Nat (Env.vars σ_1 "decode.count") c12))) (countBlock "lp.A" "decode.count") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "size.total") c27) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c24 hmat w_1 ?_) fun (w_2:Env) (h_2:And (Run B (countBlock "lp.A" "decode.count") w_1 w_2 c24) (And (@Eq Nat (Env.vars w_2 "size.total") c27) (And (FieldsAgree fields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=Run B (countBlock "lp.A" "decode.count") w_1 w_2 c24; let c1_3:Prop:=And (@Eq Nat (Env.vars w_2 "size.total") c27) (And (FieldsAgree fields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); let c2_2:Env→ Prop:=fun (σ':Env) => And (Run B (countBlock "lp.b" "lp.m") w_2 σ' c29) (And (@Eq Nat (Env.vars σ' "size.total") c32) (And (FieldsAgree fields w_2 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_2)))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => @Exists Env c18) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (c33 σ_1) (And (@Eq Nat (Env.vars σ_1 "size.total") c30) (@Eq Nat (Env.vars σ_1 "lp.m") m))) (countBlock "lp.b" "lp.m") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "size.total") c32) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c29 hbound w_2 ?_) fun (w_3:Env) (h_3:And (Run B (countBlock "lp.b" "lp.m") w_2 w_3 c29) (And (@Eq Nat (Env.vars w_3 "size.total") c32) (And (FieldsAgree fields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))))) => let c0_4:Prop:=Run B (countBlock "lp.b" "lp.m") w_2 w_3 c29; let c1_4:Prop:=And (@Eq Nat (Env.vars w_3 "size.total") c32) (And (FieldsAgree fields w_2 w_3) (@Eq (String→ List Nat) (Env.arrs w_3) (Env.arrs w_2))); let c2_3:Env→ Prop:=fun (σ':Env) => And (Run B (countBlock "lp.c" "lp.n") w_3 σ' c34) (And (@Eq Nat (Env.vars σ' "size.total") c36) (And (FieldsAgree fields w_3 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_3)))); @And.casesOn c0_4 c1_4 (fun (x:And c0_4 c1_4) => @Exists Env c18) h_3 fun (left_3:c0_4) (right_3:c1_4) => @Exists.casesOn Env c2_3 (fun (x:@Exists Env c2_3) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (c37 σ_1) (And (@Eq Nat (Env.vars σ_1 "size.total") c35) (@Eq Nat (Env.vars σ_1 "lp.n") n))) (countBlock "lp.c" "lp.n") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "size.total") c36) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c34 hobj w_3 ?_) fun (w_4:Env) (h_4:And (Run B (countBlock "lp.c" "lp.n") w_3 w_4 c34) (And (@Eq Nat (Env.vars w_4 "size.total") c36) (And (FieldsAgree fields w_3 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) (Env.arrs w_3))))) => let c0_5:Prop:=Run B (countBlock "lp.c" "lp.n") w_3 w_4 c34; let c1_5:Prop:=And (@Eq Nat (Env.vars w_4 "size.total") c36) (And (FieldsAgree fields w_3 w_4) (@Eq (String→ List Nat) (Env.arrs w_4) (Env.arrs w_3))); let c2_4:Prop:=And (@Eq Nat (Env.vars (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) "input.bits") (bitSize (@encodeProgram m n P))) (And (@RepresentsProgram m n P (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total"))) (@Eq (String→ List Nat) (Env.arrs (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total"))) (Env.arrs σ))); @And.casesOn c0_5 c1_5 (fun (x:And c0_5 c1_5) => @Exists Env c18) h_4 fun (left_4:c0_5) (right_4:c1_5) => @Exists.intro Env c18 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) (@And.intro (Run B prepareSize σ (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c17) c2_4 (RunStep.mono B prepareSize σ (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) (c2 c39 c45) c17 (RunStep.seq B (Com.assign "size.total" (Expr.lit ((0:Nat)))) (Com.seq (countWord "lp.m") c49) σ c0 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c39 c45 (RunStep.assign B σ "size.total" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4767_0_0_0))) (RunStep.seq B (countWord "lp.m") c49 c0 w (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c6 c44 left (RunStep.seq B (countWord "lp.n") c48 w w_1 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c20 c43 left_1 (RunStep.seq B (countBlock "lp.A" "decode.count") c47 w_1 w_2 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c24 c42 left_2 (RunStep.seq B (countBlock "lp.b" "lp.m") c46 w_2 w_3 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c29 c41 left_3 (RunStep.seq B (countBlock "lp.c" "lp.n") (Com.assign "input.bits" (Expr.var "size.total")) w_3 w_4 (Env.setVar w_4 "input.bits" (Env.vars w_4 "size.total")) c34 c40 left_4 (RunStep.assign B w_4 "input.bits" (Expr.var "size.total") (Env.vars w_4 "size.total") (RunStep.eval_var B w_4 "size.total" (?nAX_g4767_0_0_1))))))))) (?nAX_g4767_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4767_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4767_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4767_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4))
  all_goals clear hm hn hmat hbound hobj
  all_goals simp_all [RepresentsProgram,Represents,FieldsAgree,fields,
    RamMatrixStorage.flatten,Avec,aBits,bBits,cBits,Nat.mul_add]
  all_goals omega

end Lax109476Proofs.RamProgramSize

end

section

namespace Lax109476Proofs.RamDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

def prefixProduct {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):ℕ:=
  ((List.ofFn fun j => (v j).den).take k).prod

def product {n:ℕ} (v:Fin n→ ℚ):ℕ:=(List.ofFn fun j => (v j).den).prod

theorem prefix_zero {n:ℕ} (v:Fin n→ ℚ):prefixProduct v 0=1:=rfl

theorem prefix_done {n:ℕ} (v:Fin n→ ℚ):prefixProduct v n=product v:=by
  unfold prefixProduct product
  rw [show (List.ofFn fun j => (v j).den).take n=List.ofFn (fun j => (v j).den) from
    by simpa only [List.length_ofFn] using List.take_length (l:=List.ofFn fun j => (v j).den)]

theorem prefix_step {n:ℕ} (v:Fin n→ ℚ) (i:Fin n):
    prefixProduct v (i.val + 1)=prefixProduct v i.val * (v i).den:=by
  have hi:i.val < (List.ofFn fun j => (v j).den).length:=by simp
  unfold prefixProduct
  rw [← List.take_concat_get hi]
  simp [List.concat_eq_append,List.prod_append]

theorem positive_list_product (xs:List ℕ) (hx:∀ a∈ xs,0 < a):0 < xs.prod:=by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.prod_cons]
    exact Nat.mul_pos (hx a (by simp)) (ih (fun b hb => hx b (by simp [hb])))

theorem prefix_pos {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):0 < prefixProduct v k:=by
  apply positive_list_product
  intro a ha
  have hh:=List.mem_of_mem_take ha
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp hh
  rw [← hi]
  exact (v i).den_pos

theorem prefix_le {n:ℕ} (v:Fin n→ ℚ) (k:ℕ):prefixProduct v k≤ product v:=by
  have hp:0 < ((List.ofFn fun j => (v j).den).drop k).prod:=by
    apply positive_list_product
    intro a ha
    obtain ⟨i,hi⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop ha)
    rw [← hi]
    exact (v i).den_pos
  have he:prefixProduct v k * ((List.ofFn fun j => (v j).den).drop k).prod=product v:=by
    rw [prefixProduct, ← List.prod_append,List.take_append_drop]
    rfl
  rw [← he]
  exact Nat.le_mul_of_pos_right _ hp

def Invariant (a:String) {n:ℕ} (v:Fin n→ ℚ) (D:ℕ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧ σ.vars "den.value"=D * prefixProduct v (σ.vars "den.i")∧
    σ.vars "den.i" ≤ n∧ σ.vars "vec.n"=n

theorem productStep_spec (B D n:ℕ) (a:String) (v:Fin n→ ℚ)
    (hD:0 < D) (hnB:n < B) (hprod:D * product v < B):
    Spec B (fun σ => Invariant a v D σ∧ σ.vars "den.i" < n) (productStep a)
      (fun σ τ => Invariant a v D τ∧ τ.vars "den.i"=σ.vars "den.i" + 1) 9:=by
  rintro σ ⟨⟨hσa,hσp,hσiN,hσn⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "den.i",hσi⟩
  have h1:1 < B:=by
    have hp:0 < product v:=by simpa only [prefix_done] using prefix_pos v n
    have hm:=Nat.mul_pos hD hp
    have hn:0 < n:=by omega
    omega
  have hiB:i.val < B:=i.isLt.trans hnB
  have hcurB:D * prefixProduct v i.val < B:=
    (Nat.mul_le_mul_left D (prefix_le v i.val)).trans_lt hprod
  have hnextB:D * prefixProduct v (i.val + 1) < B:=
    (Nat.mul_le_mul_left D (prefix_le v (i.val + 1))).trans_lt hprod
  have hqle:(v i).den≤ prefixProduct v (i.val + 1):=by
    rw [prefix_step]
    exact Nat.le_mul_of_pos_left _ (prefix_pos v i.val)
  have hqB:(v i).den < B:=(hqle.trans ((prefix_le v (i.val + 1)).trans
    (Nat.le_mul_of_pos_left _ hD))).trans_lt hprod
  have hlen:i.val < (σ.arrs (a ++ ".d")).length:=by rw [hσa.2.2]; simp
  have hget:(σ.arrs (a ++ ".d")).getD i.val 0=(v i).den:=by
    rw [hσa.2.2,map_getD _ _ _ (by simp)]
    simp
  have hvalB:σ.vars "den.value" < B:=hσp ▸ hcurB
  have hmulB:σ.vars "den.value" * (σ.arrs (a ++ ".d")).getD i.val 0 < B:=by
    rw [hσp,hget]
    change D * prefixProduct v i.val * (v i).den < B
    rw [Nat.mul_assoc, ← prefix_step v i]
    exact hnextB
  have hmul:σ.vars "den.value" * (σ.arrs (a ++ ".d")).getD i.val 0 =
      D * prefixProduct v (i.val + 1):=by
    rw [hσp,hget]
    change D * prefixProduct v i.val * (v i).den=D * prefixProduct v (i.val + 1)
    rw [Nat.mul_assoc, ← prefix_step v i]
  have hi1B:i.val + 1 < B:=lt_of_le_of_lt i.isLt hnB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Invariant a n v D τ) (@Eq Nat (Env.vars τ "den.i") (c0 (Env.vars σ_1 "den.i") ((1:Nat))))) σ; let c2:String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) a ".d"; let c3:Nat:= @List.getD Nat (Env.arrs σ c2) (Env.vars σ "den.i") ((0:Nat)); let c4:Nat:=Nat.mul (Env.vars σ "den.value") c3; let c5:Env:=Env.setVar σ "den.value" c4; let c6:Nat:=Env.vars c5 "den.i"; let c7:Nat:=c0 c6 ((1:Nat)); let c8:Env:=Env.setVar c5 "den.i" c7; let c9:Nat→ Nat:=c0 ((1:Nat)); let c10:Expr:=Expr.get c2 (Expr.var "den.i"); let c11:Expr:=Expr.mul (Expr.var "den.value") c10; let c12:Nat:=c9 (Expr.size c11); let c13:Expr:=Expr.add (Expr.var "den.i") (Expr.lit ((1:Nat))); let c14:Nat:=c9 (Expr.size c13); @Exists.intro Env (fun (σ':Env) => And (Run B (productStep a) σ σ' ((9:Nat))) (c1 σ')) c8 (@And.intro (Run B (productStep a) σ c8 ((9:Nat))) (c1 c8) (RunStep.mono B (productStep a) σ c8 (c0 c12 c14) ((9:Nat)) (RunStep.seq B (Com.assign "den.value" c11) (Com.assign "den.i" c13) σ c5 c8 c12 c14 (RunStep.assign B σ "den.value" c11 c4 (RunStep.eval_mul B σ (Expr.var "den.value") c10 (Env.vars σ "den.value") c3 (RunStep.eval_var B σ "den.value" hvalB) (RunStep.eval_get B σ c2 (Expr.var "den.i") (Env.vars σ "den.i") (RunStep.eval_var B σ "den.i" hiB) hlen ?_) hmulB)) (RunStep.assign B c5 "den.i" c13 c7 (RunStep.eval_add B c5 (Expr.var "den.i") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c5 "den.i" (?nAX_g4778_0_0_0)) (RunStep.eval_lit B ((1:Nat)) c5 h1) (?nAX_g4778_0_0_1)))) (?nAX_g4778_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4778_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4778_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4778_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Invariant,Represents,Env.setVar,i]

theorem productArray_spec (B D n:ℕ) (a:String) (v:Fin n→ ℚ)
    (hD:0 < D) (hnB:n < B) (hprod:D * product v < B):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "den.value"=D∧ σ.vars "vec.n"=n)
      (productArray a)
      (fun _ τ => Represents a (List.ofFn v) τ∧
        τ.vars "den.value"=D * product v∧ τ.vars "vec.n"=n) (13 * n + 6):=by
  have hlo:=Spec.forRangeZero "den.i" "vec.n" (Invariant a v D) n 9 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2) (productStep_spec B D n a v hD hnB hprod)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hσa,hσD,hσn⟩
    clear hlo
    simp_all [Invariant,prefix_zero,Represents,Env.setVar]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨hτ.1,by simpa only [hcounter,prefix_done] using hτ.2.1,hτ.2.2.2⟩

end Lax109476Proofs.RamDenominatorProduct

end

section

namespace Lax109476Proofs.RamDenominatorBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamRationalArrays RamFrame RamReadBlock

theorem productArray_wvars (a:String):(productArray a).wvars=(productArray "").wvars:=by rfl

theorem productBlock_spec (B D n:ℕ) (a field:String) (v:Fin n→ ℚ)
    (hD:0 < D) (hnB:n < B) (hprod:D * product v < B):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ σ.vars "den.value"=D∧ σ.vars field=n)
      (productBlock a field)
      (fun σ τ => τ.vars "den.value"=D * product v∧
        FieldsAgree fields σ τ∧ τ.arrs=σ.arrs) (13 * n + 8):=by
  have harray:=spec_with_fields fields (productArray_spec B D n a v hD hnB hprod)
    (by intro x hx; rw [productArray_wvars]; simp [fields] at hx;
        rcases hx with rfl | rfl | rfl <;> decide) (by rfl)
  rintro σ ⟨hσa,hσD,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ,hfields,harr⟩:=harray (σ.setVar "vec.n" n) ⟨hσa,hσD,by simp⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.2.1, ?_,harr⟩
  intro x hx
  exact (hfields x hx).trans (by simp [fields] at hx; rcases hx with rfl | rfl | rfl <;> simp [Env.setVar])

end Lax109476Proofs.RamDenominatorBlock

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamProgramDenominator

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamDenominatorBlock RamRationalArrays RamFrame RamStoredProgram RamReadBlock
open IntegerEncoding RationalSizeBounds EncodingSize

theorem product_pos {n:ℕ} (v:Fin n→ ℚ):0 < product v:=by
  simpa only [prefix_done] using prefix_pos v n

theorem denominator_flat {m n:ℕ} (P:Program ℚ m n):
    programDenominator P=product (fun k:Fin (m * n) => P.A k.divNat k.modNat) *
      product P.b * product P.c:=by
  have hflat:product (fun k:Fin (m * n) => P.A k.divNat k.modNat) =
      ∏ i, ∏ j, (P.A i j).den:=by
    unfold product
    have hm:(List.ofFn fun k:Fin (m * n) => (P.A k.divNat k.modNat).den) =
        (RamMatrixStorage.flatten P.A).map (fun q => q.den):=by
      simp only [RamMatrixStorage.flatten,List.map_ofFn]
      rfl
    rw [hm,RamReadMatrix.flatten_rows,List.map_flatten,List.map_ofFn]
    simp [List.prod_flatten,List.prod_ofFn,List.map_ofFn]
  unfold programDenominator commonDenominator programData
  simp only [Fintype.prod_sum_type,Fintype.prod_prod_type,Sum.elim_inl,Sum.elim_inr]
  rw [hflat]
  simp [product,List.prod_ofFn,Nat.mul_assoc]

set_option maxHeartbeats 0 in
theorem prepareDenominator_spec (B m n:ℕ) (P:Program ℚ m n)
    (h1:1 < B) (hmB:m < B) (hnB:n < B) (hmnB:m * n < B)
    (hD:programDenominator P < B):
    Spec B (RepresentsProgram P) prepareDenominator
      (fun σ τ => τ.vars "den.value"=programDenominator P∧
        RepresentsProgram P τ∧ τ.arrs=σ.arrs) (13 * (m * n + m + n) + 26):=by
  let Avec:Fin (m * n)→ ℚ:=fun k => P.A k.divNat k.modNat
  let DA:=product Avec
  let Db:=product P.b
  let Dc:=product P.c
  have hflat:programDenominator P=DA * Db * Dc:=denominator_flat P
  have hDA:0 < DA:=product_pos Avec
  have hDb:0 < Db:=product_pos P.b
  have hDc:0 < Dc:=product_pos P.c
  have hAB:DA < B:=(Nat.le_mul_of_pos_right DA hDb).trans_lt
    ((Nat.le_mul_of_pos_right (DA * Db) hDc).trans_lt (by simpa only [hflat] using hD))
  have hAbB:DA * Db < B:=(Nat.le_mul_of_pos_right (DA * Db) hDc).trans_lt
    (by simpa only [hflat] using hD)
  have hmat:=productBlock_spec B 1 (m * n) "lp.A" "decode.count" Avec (by decide) hmnB
    (by simpa using hAB)
  have hbound:=productBlock_spec B DA m "lp.b" "lp.m" P.b hDA hmB hAbB
  have hobj:=productBlock_spec B (DA * Db) n "lp.c" "lp.n" P.c (Nat.mul_pos hDA hDb) hnB
    (by simpa only [hflat] using hD)
  rintro σ ⟨hσA,hσb,hσc,hσm,hσn,hσcount⟩
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "den.value" ((1:Nat)); let c1:Env→ Nat→ Prop:=Run B (productBlock "lp.A" "decode.count") c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c3 ((13:Nat)); let c5:Nat:=c3 m n; let c6:Nat:=c2 (c4 c5) ((8:Nat)); let c7:Nat:=c3 ((1:Nat)) (@product c5 Avec); let c8:Env→ Prop:=FieldsAgree fields c0; let c9:String→ List Nat:=Env.arrs c0; let c10:Env→ Prop:=fun (σ':Env) => And (c1 σ' c6) (And (@Eq Nat (Env.vars σ' "den.value") c7) (And (c8 σ') (@Eq (String→ List Nat) (Env.arrs σ') c9))); let c11:Nat:=c2 (c4 (c2 (c2 c5 m) n)) ((26:Nat)); let c12:Env→ Prop:=(fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "den.value") (@programDenominator m n P)) (And (@RepresentsProgram m n P τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) σ; let c13:Env→ Prop:=fun (σ':Env) => And (Run B prepareDenominator σ σ' c11) (c12 σ'); let c14:Prop:= @Exists Env c13; let c15:Env→ Prop:=Represents "lp.A" (@List.ofFn Rat c5 Avec); let c16:String→ Nat:=Env.vars c0; let c17:Nat:=c2 (c4 m) ((8:Nat)); let c18:Nat→ Nat:=c3 DA; let c19:Nat:=c18 (@product m (@Program.b Rat m n P)); let c20:Env→ Prop:=Represents "lp.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c21:Nat:=c2 (c4 n) ((8:Nat)); let c22:Nat:=c18 Db; let c23:Nat:=c3 c22 (@product n (@Program.c Rat m n P)); let c24:Env→ Prop:=Represents "lp.c" (@List.ofFn Rat n (@Program.c Rat m n P)); let c25:Nat:=c2 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); let c26:Nat:=c2 c17 c21; let c27:Nat:=c2 c6 c26; let c28:Com:=Com.seq (productBlock "lp.b" "lp.m") (productBlock "lp.c" "lp.n"); @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c14) (RunStep.use B (fun (σ_1:Env) => And (c15 σ_1) (And (@Eq Nat (Env.vars σ_1 "den.value") ((1:Nat))) (@Eq Nat (Env.vars σ_1 "decode.count") c5))) (productBlock "lp.A" "decode.count") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "den.value") c7) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c6 hmat c0 ?_) fun (w:Env) (h:And (c1 w c6) (And (@Eq Nat (Env.vars w "den.value") c7) (And (c8 w) (@Eq (String→ List Nat) (Env.arrs w) c9)))) => let c0_1:Prop:=And (@Eq Nat (Env.vars w "den.value") c7) (And (c8 w) (@Eq (String→ List Nat) (Env.arrs w) c9)); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B (productBlock "lp.b" "lp.m") w σ' c17) (And (@Eq Nat (Env.vars σ' "den.value") c19) (And (FieldsAgree fields w σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w)))); @And.casesOn (c1 w c6) c0_1 (fun (x:And (c1 w c6) c0_1) => c14) h fun (left:c1 w c6) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c14) (RunStep.use B (fun (σ_1:Env) => And (c20 σ_1) (And (@Eq Nat (Env.vars σ_1 "den.value") DA) (@Eq Nat (Env.vars σ_1 "lp.m") m))) (productBlock "lp.b" "lp.m") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "den.value") c19) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c17 hbound w ?_) fun (w_1:Env) (h_1:And (Run B (productBlock "lp.b" "lp.m") w w_1 c17) (And (@Eq Nat (Env.vars w_1 "den.value") c19) (And (FieldsAgree fields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))))) => let c0_2:Prop:=Run B (productBlock "lp.b" "lp.m") w w_1 c17; let c1_2:Prop:=And (@Eq Nat (Env.vars w_1 "den.value") c19) (And (FieldsAgree fields w w_1) (@Eq (String→ List Nat) (Env.arrs w_1) (Env.arrs w))); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B (productBlock "lp.c" "lp.n") w_1 σ' c21) (And (@Eq Nat (Env.vars σ' "den.value") c23) (And (FieldsAgree fields w_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs w_1)))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c14) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c14) (RunStep.use B (fun (σ_1:Env) => And (c24 σ_1) (And (@Eq Nat (Env.vars σ_1 "den.value") c22) (@Eq Nat (Env.vars σ_1 "lp.n") n))) (productBlock "lp.c" "lp.n") (fun (σ_1 τ:Env) => And (@Eq Nat (Env.vars τ "den.value") c23) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c21 hobj w_1 ?_) fun (w_2:Env) (h_2:And (Run B (productBlock "lp.c" "lp.n") w_1 w_2 c21) (And (@Eq Nat (Env.vars w_2 "den.value") c23) (And (FieldsAgree fields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))))) => let c0_3:Prop:=Run B (productBlock "lp.c" "lp.n") w_1 w_2 c21; let c1_3:Prop:=And (@Eq Nat (Env.vars w_2 "den.value") c23) (And (FieldsAgree fields w_1 w_2) (@Eq (String→ List Nat) (Env.arrs w_2) (Env.arrs w_1))); @And.casesOn c0_3 c1_3 (fun (x:And c0_3 c1_3) => c14) h_2 fun (left_2:c0_3) (right_2:c1_3) => @Exists.intro Env c13 w_2 (@And.intro (Run B prepareDenominator σ w_2 c11) (c12 w_2) (RunStep.mono B prepareDenominator σ w_2 (c2 c25 c27) c11 (RunStep.seq B (Com.assign "den.value" (Expr.lit ((1:Nat)))) (Com.seq (productBlock "lp.A" "decode.count") c28) σ c0 w_2 c25 c27 (RunStep.assign B σ "den.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.seq B (productBlock "lp.A" "decode.count") c28 c0 w w_2 c6 c26 left (RunStep.seq B (productBlock "lp.b" "lp.m") (productBlock "lp.c" "lp.n") w w_1 w_2 c17 c21 left_1 left_2))) (?nAX_g4787_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4787_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals clear hmat hbound hobj
  all_goals simp_all [RepresentsProgram,Represents,FieldsAgree,fields,
    RamMatrixStorage.flatten,Avec,DA,Db,Dc,Nat.mul_add]
  all_goals omega

end Lax109476Proofs.RamProgramDenominator

end

section

open scoped BigOperators

namespace Lax109476Proofs.RamSolverInitialization

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds EncodingSize IntegerEncoding

theorem datum_height {m n:ℕ} (P:Program ℚ m n) (i):
    Height (programData P i) (2 ^ bitSize (encodeProgram P)):=by
  have hnum:=datum_numerator_size P i
  have hden:(programData P i).den.size≤ bitSize (encodeProgram P):=by
    have hs:=Finset.single_le_sum (fun j _ => Nat.zero_le (programData P j).den.size) (Finset.mem_univ i)
    have hh:=denominator_size_sum P
    omega
  exact ⟨((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hnum)).le,
    ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) hden)).le⟩

theorem cells_bound {m n:ℕ} (P:Program ℚ m n):m * n + m + n≤ bitSize (encodeProgram P):=by
  have hlen:(encodeProgram P).length=2 + 3 * (m * n + m + n):=by
    rw [WordDecoding.encodeProgram_rows]
    simp only [List.length_cons,List.length_append,WordDecoding.encodeRows_length,
      WordDecoding.encodeVector_length,Nat.mul_assoc]
    omega
  have hl:=WordSolverSize.length_le_bitSize (encodeProgram P)
  rw [hlen] at hl
  omega

end Lax109476Proofs.RamSolverInitialization

end

section

namespace Lax109476Proofs.RamScaleArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleCoordinate RamRationalArrays RamRational RamCenterUpdate RamCopy RationalArithmeticBounds

def scaled {n:ℕ} (v:Fin n→ ℚ) (D:ℕ):Fin n→ ℚ:=fun i => v i * (D:ℚ)

def Invariant {n:ℕ} (a b:String) (v:Fin n→ ℚ) (D:ℕ) (σ:Env):Prop:=
  Represents a (List.ofFn v) σ∧ Represents b (filled (scaled v D) (σ.vars "scale.i")) σ∧
    σ.vars "scale.i" ≤ n∧ σ.vars "vec.n"=n∧ σ.vars "scale.factor"=D

theorem coordinate_wvars (a b:String):
    (scaleCoordinate a b).wvars=(scaleCoordinate "" "").wvars:=by rfl

theorem scaleStep_spec (B M n D:ℕ) (a b:String) (v:Fin n→ ℚ)
    (hM:1≤ M) (hnB:n < B) (hB:2 * M ^ 2 + 3 < B)
    (hv:∀ i,Height (v i) M) (hD:D≤ M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Invariant a b v D σ∧ σ.vars "scale.i" < n) (scaleStep a b)
      (fun σ τ => Invariant a b v D τ∧ τ.vars "scale.i"=σ.vars "scale.i" + 1)
      (72 * M.size + 98):=by
  rintro σ ⟨⟨hσa,hσb,hσiN,hσn,hσD⟩,hσi⟩
  let i:Fin n:= ⟨σ.vars "scale.i",hσi⟩
  have hvi:Height (List.ofFn v)[i.val] M:=by simpa using hv i
  obtain ⟨τ,hr₁,hτb,hτa⟩:=scaleCoordinate_spec B M i.val D a b (List.ofFn v)
    (filled (scaled v D) i.val) (by simp) (by simp [filled]) (i.isLt.trans hnB) hM hB
      hvi hD hab σ ⟨hσa,hσb,rfl,hσD⟩
  have hτi:τ.vars "scale.i"=i.val:=hr₁.frame_var _ (by rw [coordinate_wvars]; decide)
  have hτn:τ.vars "vec.n"=n:=
    (hr₁.frame_var _ (by rw [coordinate_wvars]; decide)).trans hσn
  have hτD:τ.vars "scale.factor"=D:=
    (hr₁.frame_var _ (by rw [coordinate_wvars]; decide)).trans hσD
  have h1:1 < B:=by nlinarith
  have he:(Expr.add (.var "scale.i") (.lit 1)).evalB B τ=some (i.val + 1):=by
    simpa only [hτi,Bop.apply_add] using evalB_bin
      (evalB_var (B:=B) (σ:=τ) (x:= "scale.i") (by rw [hτi]; exact i.isLt.trans hnB))
      (evalB_lit h1)
      (show Bop.add.apply (τ.vars "scale.i") 1 < B by rw [hτi]; simp only [Bop.apply_add]; omega)
  have hr₂:=Run.assign (x:= "scale.i") he
  have hnext:Represents b (filled (scaled v D) (i.val + 1)) τ:=by
    rw [← filled_step]
    simpa only [List.getElem_ofFn,Fin.eta,scaled] using hτb
  refine ⟨_, (hr₁.seq hr₂).mono (by simp only [Expr.size]; omega), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτa
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hnext
  · change i.val + 1≤ n; exact i.isLt
  · simpa [Env.setVar] using hτn
  · simpa [Env.setVar] using hτD
  · simp [i]

theorem scaleLoop_spec (B M n D:ℕ) (a b:String) (v:Fin n→ ℚ)
    (hM:1≤ M) (hnB:n < B) (hB:2 * M ^ 2 + 3 < B)
    (hv:∀ i,Height (v i) M) (hD:D≤ M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧ Represents b (List.replicate n 0) σ∧
        σ.vars "vec.n"=n∧ σ.vars "scale.factor"=D)
      (scaleLoop a b)
      (fun _ τ => Represents b (List.ofFn (scaled v D)) τ∧ Represents a (List.ofFn v) τ∧
        τ.vars "vec.n"=n∧ τ.vars "scale.factor"=D)
      ((72 * M.size + 102) * n + 6):=by
  have hlo:=Spec.forRangeZero "scale.i" "vec.n" (Invariant a b v D) n (72 * M.size + 98) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1)
    (scaleStep_spec B M n D a b v hM hnB hB hv hD hab)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσa,hσb,hσn,hσD⟩
    clear hlo
    simp_all [Invariant,filled_zero,Represents,Env.setVar]
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨by simpa only [hcounter,filled_done] using hτ.2.1,
      hτ.1,hτ.2.2.2.1,hτ.2.2.2.2⟩

theorem scaleArray_spec (B M n D:ℕ) (a b:String) (v:Fin n→ ℚ)
    (hM:1≤ M) (hnB:n < B) (hB:2 * M ^ 2 + 3 < B)
    (hv:∀ i,Height (v i) M) (hD:D≤ M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧
        (σ.arrs (b ++ ".s")).length=n∧ (σ.arrs (b ++ ".n")).length=n∧
        (σ.arrs (b ++ ".d")).length=n∧ σ.vars "vec.n"=n∧ σ.vars "scale.factor"=D)
      (scaleArray a b)
      (fun _ τ => Represents b (List.ofFn (scaled v D)) τ∧ Represents a (List.ofFn v) τ∧
        τ.vars "vec.n"=n∧ τ.vars "scale.factor"=D)
      ((72 * M.size + 135) * n + 24):=by
  rintro σ ⟨hσa,hσs,hσnum,hσd,hσn,hσD⟩
  obtain ⟨τ,hr₁,hτb,hτn,harr⟩:=RamZeroArray.zeroRationalArray_spec B n b hnB (by nlinarith)
    σ ⟨hσs,hσnum,hσd,hσn⟩
  have hτa:Represents a (List.ofFn v) τ:=by
    simpa only [Represents,harr (a ++ ".s") (disjoint_not_mem a b ".s" hab (by simp [suffixes])),
      harr (a ++ ".n") (disjoint_not_mem a b ".n" hab (by simp [suffixes])),
      harr (a ++ ".d") (disjoint_not_mem a b ".d" hab (by simp [suffixes]))] using hσa
  have hτD:τ.vars "scale.factor"=D:=(hr₁.frame_var _ (by simp [RamZeroArray.zeroRationalArray,
    RamZeroArray.fillConstant,Lib.Fill.put,Com.wvars])).trans hσD
  obtain ⟨υ,hr₂,hυ⟩:=scaleLoop_spec B M n D a b v hM hnB hB hv hD hab τ ⟨hτa,hτb,hτn,hτD⟩
  exact ⟨υ, (hr₁.seq hr₂).mono (by simp only [Nat.add_mul]; omega),hυ⟩

end Lax109476Proofs.RamScaleArray

end

section

namespace Lax109476Proofs.RamScaleBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamRationalArrays RamFrame RationalArithmeticBounds RamReadBlock

def fields:List String:= ["lp.m", "lp.n", "decode.count", "den.value", "input.bits"]

theorem scaleArray_wvars (a b:String):(scaleArray a b).wvars=(scaleArray "" "").wvars:=by rfl

theorem scaleArray_warrs (a b:String):(scaleArray a b).warrs=(RamReadArray.readArray b).warrs:=by rfl

theorem scaleBlock_spec (B M n D:ℕ) (a b field:String) (v:Fin n→ ℚ)
    (hM:1≤ M) (hnB:n < B) (hB:2 * M ^ 2 + 3 < B)
    (hv:∀ i,Height (v i) M) (hD:D≤ M) (hab:RamCopy.Disjoint a b):
    Spec B (fun σ => Represents a (List.ofFn v) σ∧
        (σ.arrs (b ++ ".s")).length=n∧ (σ.arrs (b ++ ".n")).length=n∧
        (σ.arrs (b ++ ".d")).length=n∧ σ.vars field=n∧ σ.vars "scale.factor"=D)
      (scaleBlock a b field)
      (fun σ τ => Represents b (List.ofFn (scaled v D)) τ∧
        FieldsAgree fields σ τ∧ τ.vars "scale.factor"=D∧
        ∀ c∉ [b ++ ".s",b ++ ".n",b ++ ".d"],τ.arrs c=σ.arrs c)
      ((72 * M.size + 135) * n + 26):=by
  have harray:=spec_with_write_frame fields (scaleArray_spec B M n D a b v hM hnB hB hv hD hab)
    (by
      intro x hx
      rw [scaleArray_wvars]
      simp [fields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσa,hσs,hσnum,hσd,hσn,hσD⟩
  have hr₁:Run B (.assign "vec.n" (.var field)) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:=field) (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτ,hfields,harr⟩:=harray (σ.setVar "vec.n" n)
    ⟨hσa,hσs,hσnum,hσd,by simp,hσD⟩
  refine ⟨τ, (hr₁.seq hr₂).mono (by omega),hτ.1, ?_,hτ.2.2.2, ?_⟩
  · intro x hx
    exact (hfields x hx).trans (by
      simp [fields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [Env.setVar])
  · intro c hc
    apply harr c
    rw [scaleArray_warrs,RamReadBlock.readArray_warrs]
    simp at hc ⊢
    tauto

end Lax109476Proofs.RamScaleBlock

end

section

namespace Lax109476Proofs.RamClearProgram

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamScaleBlock RamRationalArrays RamFrame RamStoredProgram
open RationalArithmeticBounds IntegerEncoding RamEllipsoidStep

set_option maxHeartbeats 0 in
theorem clearProgram_spec (B M m n:ℕ) (P:Program ℚ m n)
    (hM:1≤ M) (hmB:m < B) (hnB:n < B) (hmnB:m * n < B)
    (hB:2 * M ^ 2 + 3 < B) (hA:∀ i j,Height (P.A i j) M)
    (hb:∀ i,Height (P.b i) M) (hc:∀ j,Height (P.c j) M)
    (hD:programDenominator P≤ M):
    Spec B (fun σ => RepresentsProgram P σ∧ Extents "int.A" (m * n) σ∧
        Extents "int.b" m σ∧ Extents "int.c" n σ∧ σ.vars "den.value"=programDenominator P)
      clearProgram
      (fun σ τ => IntegerRep P τ∧ RepresentsProgram P τ∧
        τ.vars "den.value"=programDenominator P∧ τ.vars "input.bits"=σ.vars "input.bits")
      ((72 * M.size + 135) * (m * n + m + n) + 80):=by
  let D:=programDenominator P
  let Avec:Fin (m * n)→ ℚ:=fun k => P.A k.divNat k.modNat
  have hmat:=scaleBlock_spec B M (m * n) D "lp.A" "int.A" "decode.count" Avec
    hM hmnB hB (fun k => hA k.divNat k.modNat) hD (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hbound:=scaleBlock_spec B M m D "lp.b" "int.b" "lp.m" P.b
    hM hmB hB hb hD (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hobj:=scaleBlock_spec B M n D "lp.c" "int.c" "lp.n" P.c
    hM hnB hB hc hD (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have h1:1 < B:=by nlinarith
  have hMB:M < B:=by nlinarith
  have hDB:D < B:=hD.trans_lt hMB
  have hint:=integerProgram_eq_scaled P
  rintro σ ⟨⟨hσA,hσb,hσc,hσm,hσn,hσcount⟩,hσintA,hσintb,hσintc,hσD⟩
  have hAs:=hσintA ".s" (by simp)
  have hAn:=hσintA ".n" (by simp)
  have hAd:=hσintA ".d" (by simp)
  have hbs:=hσintb ".s" (by simp)
  have hbn:=hσintb ".n" (by simp)
  have hbd:=hσintb ".d" (by simp)
  have hcs:=hσintc ".s" (by simp)
  have hcn:=hσintc ".n" (by simp)
  have hcd:=hσintc ".d" (by simp)
  simp only [Nat.mul_add]
  (expose_names;
    (refine let c0:Env→ Nat→ Prop:=Run B (scaleBlock "lp.A" "int.A" "decode.count") (Env.setVar σ "scale.factor" (Env.vars σ "den.value")); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat→ Nat:=c2 (c1 (c2 ((72:Nat)) (Nat.size M)) ((135:Nat))); let c4:Nat:=c2 m n; let c5:Nat→ Nat:=c1 (c3 c4); let c6:Nat:=c5 ((26:Nat)); let c7:(Fin c4→ Rat)→ List Rat:= @List.ofFn Rat c4; let c8:Env→ Prop:=Represents "int.A" (c7 (@scaled c4 Avec D)); let c9:Env→ Prop:=FieldsAgree fields (Env.setVar σ "scale.factor" (Env.vars σ "den.value")); let c10:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c11:String→ String:=c10 "int.A"; let c12:String:=c11 ".s"; let c13:String:=c11 ".n"; let c14:String:=c11 ".d"; let c15:String→ List Nat:=Env.arrs (Env.setVar σ "scale.factor" (Env.vars σ "den.value")); let c16:Env→ Prop:=fun (σ':Env) => And (c0 σ' c6) (And (c8 σ') (And (c9 σ') (And (@Eq Nat (Env.vars σ' "scale.factor") D) (∀ c∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' c) (c15 c))))); let c17:Nat:=c3 m; let c18:Nat:=c3 n; let c19:Nat:=c1 (c1 (c5 c17) c18) ((80:Nat)); let c20:Env→ Prop:=fun (σ':Env) => And (Run B clearProgram σ σ' c19) (And (@IntegerRep m n P σ') (And (@RepresentsProgram m n P σ') (And (@Eq Nat (Env.vars σ' "den.value") (@programDenominator m n P)) (@Eq Nat (Env.vars σ' "input.bits") (Env.vars σ "input.bits"))))); let c21:Env→ Prop:=Represents "lp.A" (c7 Avec); let c22:String→ Nat:=Env.vars (Env.setVar σ "scale.factor" (Env.vars σ "den.value")); let c23:Nat:=c1 c17 ((26:Nat)); let c24:Env→ Prop:=Represents "int.b" (@List.ofFn Rat m (@scaled m (@Program.b Rat m n P) D)); let c25:String→ String:=c10 "int.b"; let c26:String:=c25 ".s"; let c27:String:=c25 ".n"; let c28:String:=c25 ".d"; let c29:Env→ Prop:=Represents "lp.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c30:Nat:=c1 c18 ((26:Nat)); let c31:Env→ Prop:=Represents "int.c" (@List.ofFn Rat n (@scaled n (@Program.c Rat m n P) D)); let c32:String→ String:=c10 "int.c"; let c33:String:=c32 ".s"; let c34:String:=c32 ".n"; let c35:String:=c32 ".d"; let c36:Env→ Prop:=Represents "lp.c" (@List.ofFn Rat n (@Program.c Rat m n P)); let c37:Nat:=c1 ((1:Nat)) (Expr.size (Expr.var "den.value")); let c38:Nat:=c1 c23 c30; let c39:Nat:=c1 c6 c38; let c40:Com:=Com.seq (scaleBlock "lp.b" "int.b" "lp.m") (scaleBlock "lp.c" "int.c" "lp.n"); @Exists.casesOn Env c16 (fun (x:@Exists Env c16) => @Exists Env c20) (RunStep.use B (fun (σ_1:Env) => And (c21 σ_1) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c12)) c4) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c13)) c4) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c14)) c4) (And (@Eq Nat (Env.vars σ_1 "decode.count") c4) (@Eq Nat (Env.vars σ_1 "scale.factor") D)))))) (scaleBlock "lp.A" "int.A" "decode.count") (fun (σ_1 τ:Env) => And (c8 τ) (And (FieldsAgree fields σ_1 τ) (And (@Eq Nat (Env.vars τ "scale.factor") D) (∀ c∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs τ c) (Env.arrs σ_1 c))))) c6 hmat (Env.setVar σ "scale.factor" (Env.vars σ "den.value")) ?_) fun (w:Env) (h:And (c0 w c6) (And (c8 w) (And (c9 w) (And (@Eq Nat (Env.vars w "scale.factor") D) (∀ c∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs w c) (c15 c)))))) => let c0_1:Prop:=And (c8 w) (And (c9 w) (And (@Eq Nat (Env.vars w "scale.factor") D) (∀ c∉ @List.cons String c12 (@List.cons String c13 (@List.cons String c14 (@List.nil String))), @Eq (List Nat) (Env.arrs w c) (c15 c)))); let c1_1:Env→ Nat→ Prop:=Run B (scaleBlock "lp.b" "int.b" "lp.m") w; let c2_1:Env→ Prop:=fun (σ':Env) => And (c1_1 σ' c23) (And (c24 σ') (And (FieldsAgree fields w σ') (And (@Eq Nat (Env.vars σ' "scale.factor") D) (∀ c∉ @List.cons String c26 (@List.cons String c27 (@List.cons String c28 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' c) (Env.arrs w c))))); @And.casesOn (c0 w c6) c0_1 (fun (x:And (c0 w c6) c0_1) => @Exists Env c20) h fun (left:c0 w c6) (right:c0_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c20) (RunStep.use B (fun (σ_1:Env) => And (c29 σ_1) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c26)) m) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c27)) m) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c28)) m) (And (@Eq Nat (Env.vars σ_1 "lp.m") m) (@Eq Nat (Env.vars σ_1 "scale.factor") D)))))) (scaleBlock "lp.b" "int.b" "lp.m") (fun (σ_1 τ:Env) => And (c24 τ) (And (FieldsAgree fields σ_1 τ) (And (@Eq Nat (Env.vars τ "scale.factor") D) (∀ c∉ @List.cons String c26 (@List.cons String c27 (@List.cons String c28 (@List.nil String))), @Eq (List Nat) (Env.arrs τ c) (Env.arrs σ_1 c))))) c23 hbound w ?_) fun (w_1:Env) (h_1:And (c1_1 w_1 c23) (And (c24 w_1) (And (FieldsAgree fields w w_1) (And (@Eq Nat (Env.vars w_1 "scale.factor") D) (∀ c∉ @List.cons String c26 (@List.cons String c27 (@List.cons String c28 (@List.nil String))), @Eq (List Nat) (Env.arrs w_1 c) (Env.arrs w c)))))) => let c0_2:Prop:=And (c24 w_1) (And (FieldsAgree fields w w_1) (And (@Eq Nat (Env.vars w_1 "scale.factor") D) (∀ c∉ @List.cons String c26 (@List.cons String c27 (@List.cons String c28 (@List.nil String))), @Eq (List Nat) (Env.arrs w_1 c) (Env.arrs w c)))); let c1_2:Env→ Nat→ Prop:=Run B (scaleBlock "lp.c" "int.c" "lp.n") w_1; let c2_2:Env→ Prop:=fun (σ':Env) => And (c1_2 σ' c30) (And (c31 σ') (And (FieldsAgree fields w_1 σ') (And (@Eq Nat (Env.vars σ' "scale.factor") D) (∀ c∉ @List.cons String c33 (@List.cons String c34 (@List.cons String c35 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' c) (Env.arrs w_1 c))))); @And.casesOn (c1_1 w_1 c23) c0_2 (fun (x:And (c1_1 w_1 c23) c0_2) => @Exists Env c20) h_1 fun (left_1:c1_1 w_1 c23) (right_1:c0_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => @Exists Env c20) (RunStep.use B (fun (σ_1:Env) => And (c36 σ_1) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c33)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c34)) n) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c35)) n) (And (@Eq Nat (Env.vars σ_1 "lp.n") n) (@Eq Nat (Env.vars σ_1 "scale.factor") D)))))) (scaleBlock "lp.c" "int.c" "lp.n") (fun (σ_1 τ:Env) => And (c31 τ) (And (FieldsAgree fields σ_1 τ) (And (@Eq Nat (Env.vars τ "scale.factor") D) (∀ c∉ @List.cons String c33 (@List.cons String c34 (@List.cons String c35 (@List.nil String))), @Eq (List Nat) (Env.arrs τ c) (Env.arrs σ_1 c))))) c30 hobj w_1 ?_) fun (w_2:Env) (h_2:And (c1_2 w_2 c30) (And (c31 w_2) (And (FieldsAgree fields w_1 w_2) (And (@Eq Nat (Env.vars w_2 "scale.factor") D) (∀ c∉ @List.cons String c33 (@List.cons String c34 (@List.cons String c35 (@List.nil String))), @Eq (List Nat) (Env.arrs w_2 c) (Env.arrs w_1 c)))))) => let c0_3:Prop:=And (c31 w_2) (And (FieldsAgree fields w_1 w_2) (And (@Eq Nat (Env.vars w_2 "scale.factor") D) (∀ c∉ @List.cons String c33 (@List.cons String c34 (@List.cons String c35 (@List.nil String))), @Eq (List Nat) (Env.arrs w_2 c) (Env.arrs w_1 c)))); let c1_3:Prop:=And (@IntegerRep m n P w_2) (And (@RepresentsProgram m n P w_2) (And (@Eq Nat (Env.vars w_2 "den.value") (@programDenominator m n P)) (@Eq Nat (Env.vars w_2 "input.bits") (Env.vars σ "input.bits")))); @And.casesOn (c1_2 w_2 c30) c0_3 (fun (x:And (c1_2 w_2 c30) c0_3) => @Exists Env c20) h_2 fun (left_2:c1_2 w_2 c30) (right_2:c0_3) => @Exists.intro Env c20 w_2 (@And.intro (Run B clearProgram σ w_2 c19) c1_3 (RunStep.mono B clearProgram σ w_2 (c1 c37 c39) c19 (RunStep.seq B (Com.assign "scale.factor" (Expr.var "den.value")) (Com.seq (scaleBlock "lp.A" "int.A" "decode.count") c40) σ (Env.setVar σ "scale.factor" (Env.vars σ "den.value")) w_2 c37 c39 (RunStep.assign B σ "scale.factor" (Expr.var "den.value") (Env.vars σ "den.value") (RunStep.eval_var B σ "den.value" (?nAX_g4809_0_0_0))) (RunStep.seq B (scaleBlock "lp.A" "int.A" "decode.count") c40 (Env.setVar σ "scale.factor" (Env.vars σ "den.value")) w w_2 c6 c38 left (RunStep.seq B (scaleBlock "lp.b" "int.b" "lp.m") (scaleBlock "lp.c" "int.c" "lp.n") w w_1 w_2 c23 c30 left_1 left_2))) (?nAX_g4809_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4809_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4809_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2))
  all_goals clear hmat hbound hobj
  all_goals simp_all [IntegerRep,RepresentsProgram,Represents,FieldsAgree,fields,
    RamMatrixStorage.flatten,scaledProgram,Avec,D,Extents,mul_comm]
  all_goals aesop
  all_goals funext i
  all_goals change _=_
  all_goals simp only [Function.comp_def,RamScaleArray.scaled]
  all_goals simp only [mul_comm]

end Lax109476Proofs.RamClearProgram

end

section

namespace Lax109476Proofs.RamSolverFrontEnd

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem clearing_word_guard (L w:ℕ) (hw:RamDecoder.wordWidth L≤ w):
    2 * (2 ^ L) ^ 2 + 3 < 2 ^ w:=by
  have he:2 * L + 3≤ w:=by unfold RamDecoder.wordWidth at hw; omega
  have hp:1≤ 2 ^ (2 * L):=Nat.one_le_pow _ _ (by decide)
  have hlarge:2 * (2 ^ L) ^ 2 + 3 < 2 ^ (2 * L + 3):=by
    rw [← pow_mul,Nat.mul_comm L 2,pow_add]
    norm_num
    omega
  exact hlarge.trans_le (Nat.pow_le_pow_right (by decide) he)

end Lax109476Proofs.RamSolverFrontEnd

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

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

@[simp] theorem view_setVar (f:String→ String) (σ:Env) (x:String) (v:ℕ):
    view f (σ.setVar x v)=(view f σ).setVar x v:=rfl

end Lax109476Proofs.RamArrayRelabel

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

end Lax109476Proofs.RamSolverWorkspace

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

namespace Lax109476Proofs.RamDecodedProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBody RamRationalArrays RationalArithmeticBounds

theorem flatten_body (xs:List ℕ) (m n:ℕ):
    RamMatrixStorage.flatten (bodyProgram xs m n).A=List.ofFn (values xs 1 (m * n)):=by
  unfold RamMatrixStorage.flatten
  congr 1
  funext i
  change values xs 1 (m * n) ⟨(i.val / n) * n + i.val % n,_⟩=values xs 1 (m * n) i
  congr 1
  apply Fin.ext
  simpa only [Nat.mul_comm] using Nat.div_add_mod i.val n

theorem result_program (B m n:ℕ) (xs:List ℕ) (σ:Env) (hσ:Result B xs 1 m n σ):
    RamStoredProgram.RepresentsProgram (bodyProgram xs m n) σ∧ σ.vars "input.valid" ≤ 1:=by
  rcases hσ with ⟨hA,hb,hc,hinp,hrem,hvalid,hbounded,hm,hn,hcount⟩
  refine ⟨⟨?_,hb,hc,hm,hn,hcount⟩, ?_⟩
  · simpa only [flatten_body] using hA
  · have hfa:flagA xs 1 m n≤ 1:=flag_le_one xs 1 (m * n) (by decide)
    have hfb:flagB xs 1 m n≤ 1:=flag_le_one (afterA xs m n) _ m hfa
    have hfc:flagC xs 1 m n≤ 1:=flag_le_one (afterB xs m n) _ n hfb
    rw [hvalid]
    split_ifs <;> omega

theorem values_height (xs:List ℕ) (v n M:ℕ) (hM:1≤ M)
    (hwords:∀ z∈ xs,z≤ M):∀ i,Height (values xs v n i) M:=by
  intro i
  exact safeValue_height _ _ M hM (fun z hz => hwords z (List.mem_of_mem_drop hz))

theorem body_height (xs:List ℕ) (m n M:ℕ) (hM:1≤ M) (hwords:∀ z∈ xs,z≤ M):
    (∀ i j,Height ((bodyProgram xs m n).A i j) M)∧
      (∀ i,Height ((bodyProgram xs m n).b i) M)∧ ∀ j,Height ((bodyProgram xs m n).c j) M:=by
  refine ⟨fun i j => values_height xs 1 (m * n) M hM hwords _, ?_, ?_⟩
  · exact values_height _ _ _ _ hM (fun z hz => hwords z (List.mem_of_mem_drop hz))
  · exact values_height _ _ _ _ hM (fun z hz => hwords z (List.mem_of_mem_drop (List.mem_of_mem_drop hz)))

theorem decoded_size (xs:List ℕ) (hheader:RamDecoder.AcceptedHeader xs):
    bitSize (encodeProgram (decodedProgram xs))≤ canonicalBound (bitSize xs):=by
  let L:=bitSize xs
  have hlen:xs.length≤ L:=WordSolverSize.length_le_bitSize xs
  have hm:xs.headD 0≤ L + 1:=by
    have hh:=hheader.2.1
    simp only [List.length_drop] at hh
    omega
  have hn:xs.tail.headD 0≤ L + 1:=by
    have hh:=hheader.2.2
    simp only [List.length_drop] at hh
    omega
  have hprod:xs.headD 0 * xs.tail.headD 0≤ (L + 1) ^ 2:=by
    simpa only [pow_two] using Nat.mul_le_mul hm hn
  have hM:1≤ 2 ^ L:=Nat.one_le_pow _ _ (by decide)
  have hwords:∀ z∈ xs.drop 2,z≤ 2 ^ L:=by
    intro z hz
    exact ((Nat.lt_size_self z).trans_le
      (Nat.pow_le_pow_right (by decide) (WordSolverSize.member_size_le (List.mem_of_mem_drop hz)))).le
  obtain ⟨hA,hb,hc⟩:=body_height (xs.drop 2) (xs.headD 0) (xs.tail.headD 0) (2 ^ L) hM hwords
  have hs:=RecoveryArithmeticBounds.program_height_size (decodedProgram xs) (2 ^ L) hA hb hc
  rw [Nat.size_pow] at hs
  have hrows:xs.headD 0 + xs.tail.headD 0 + 2≤ 2 * L + 4:=by omega
  have hcells:xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0≤ (L + 1) ^ 2 + 2 * L + 2:=by omega
  exact hs.trans (Nat.add_le_add hrows (Nat.mul_le_mul_right (4 + 2 * (L + 1)) hcells))

theorem canonicalBound_ge (L:ℕ):L≤ canonicalBound L:=by
  unfold canonicalBound
  omega

theorem output_empty_of_valid (B:ℕ) (xs:List ℕ) (σ:Env)
    (hheader:RamDecoder.AcceptedHeader xs) (hσ:RamDecoder.Output B xs σ)
    (hvalid:σ.vars "input.valid"=1):σ.inp=[]:=by
  simp only [RamDecoder.Output,if_pos hheader] at hσ
  rcases hσ with ⟨hA,hb,hc,hinp,hrem,hflag,hbound,hm,hn,hcount⟩
  have hz:(afterC (xs.drop 2) (xs.headD 0) (xs.tail.headD 0)).length=0:=by
    by_contra h
    simp only [if_neg h] at hflag
    omega
  exact hinp.trans (List.eq_nil_of_length_eq_zero hz)

theorem output_program (B:ℕ) (xs:List ℕ) (σ:Env) (hheader:RamDecoder.AcceptedHeader xs)
    (hσ:RamDecoder.Output B xs σ):
    RamStoredProgram.RepresentsProgram (decodedProgram xs) σ∧ σ.vars "input.valid" ≤ 1:=by
  simp only [RamDecoder.Output,if_pos hheader] at hσ
  exact result_program B _ _ _ σ hσ

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

namespace Lax109476Proofs.RamPrepareStoredProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds IntegerEncoding

def prepare:Com:=.seq RamProgramSize.prepareSize RamProgramDenominator.prepareDenominator
def instructionBound (L:ℕ):ℕ:=(36 * (L + 1) + 61) * L + 37 * L + 82

theorem instructionBound_monotone {L S:ℕ} (h:L≤ S):instructionBound L≤ instructionBound S:=by
  unfold instructionBound
  gcongr

theorem prepare_spec (m n:ℕ) (P:Program ℚ m n) (w:ℕ)
    (hw:RamDecoder.wordWidth (bitSize (encodeProgram P))≤ w):
    Spec (2 ^ w) (fun σ => RepresentsProgram P σ∧ σ.vars "input.valid"=1) prepare
      (fun _ τ => RepresentsProgram P τ∧ τ.vars "input.valid"=1∧
        τ.vars "input.bits"=bitSize (encodeProgram P)∧ τ.vars "den.value"=programDenominator P)
      (instructionBound (bitSize (encodeProgram P))):=by
  let L:=bitSize (encodeProgram P)
  let H:=2 ^ L
  have hHL:H < 2 ^ w:=Nat.pow_lt_pow_right (by decide)
    (by dsimp only [RamDecoder.wordWidth] at hw; omega)
  have hH:1≤ H:=Nat.one_le_pow L 2 (by decide)
  have h8:8≤ w:=by dsimp only [RamDecoder.wordWidth] at hw; omega
  have h256:256≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) h8
  have h2:2 < 2 ^ w:=by omega
  have hLB:L < 2 ^ w:=(Nat.lt_two_pow_self (n:=L)).trans hHL
  have hcells:=RamSolverInitialization.cells_bound P
  have hmB:m < 2 ^ w:=(by omega:m≤ L).trans_lt hLB
  have hnB:n < 2 ^ w:=(by omega:n≤ L).trans_lt hLB
  have hmnB:m * n < 2 ^ w:=(by omega:m * n≤ L).trans_lt hLB
  have hA:∀ i j,Height (P.A i j) H:=fun i j => RamSolverInitialization.datum_height P (.inl (i,j))
  have hb:∀ i,Height (P.b i) H:=fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
  have hc:∀ j,Height (P.c j) H:=fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
  have hDB:programDenominator P < 2 ^ w:=(programDenominator_bound P).trans_lt hHL
  rintro σ ⟨hσP,hσvalid⟩
  obtain ⟨τ,hr₁,hτbits,hτP,_⟩:=RamProgramSize.prepareSize_spec (2 ^ w) H m n P
    h2 hH hHL hmB hnB hmnB hA hb hc hLB σ hσP
  obtain ⟨υ,hr₂,hυden,hυP,_⟩:=RamProgramDenominator.prepareDenominator_spec (2 ^ w) m n P
    (by omega) hmB hnB hmnB hDB τ hτP
  have hυbits:=(hr₂.frame_var "input.bits" (by decide)).trans hτbits
  have hυvalid:=((hr₁.seq hr₂).frame_var "input.valid" (by decide)).trans hσvalid
  have hms:m.size≤ L:=(RationalSizeBounds.size_le_self m).trans (by omega)
  have hns:n.size≤ L:=(RationalSizeBounds.size_le_self n).trans (by omega)
  have hmul:=Nat.mul_le_mul_left (36 * (L + 1) + 61) hcells
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυP,hυvalid,hυbits,hυden⟩
  simp only [instructionBound,H,Nat.size_pow,L]
  dsimp only [L] at hmul hms hns
  omega

end Lax109476Proofs.RamPrepareStoredProgram

end

section

namespace Lax109476Proofs.RamInitializationTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram IntegerEncoding RamDecodedProgram

def instructionBound (L:ℕ):ℕ:=RamSolverInitialization.instructionBound (canonicalBound L)

def Output (xs:List ℕ) (σ:Env):Prop:=σ.vars "input.valid"=0∨
  (RamDecoder.AcceptedHeader xs∧ σ.vars "input.valid"=1∧ RepresentsProgram (decodedProgram xs) σ∧
    σ.vars "input.bits"=bitSize (encodeProgram (decodedProgram xs))∧
    σ.vars "den.value"=programDenominator (decodedProgram xs)∧ σ.inp=[])

theorem decoder_bound_monotone {L S:ℕ} (h:L≤ S):
    RamDecoder.instructionBound L (L + 1)≤ RamDecoder.instructionBound S (S + 1):=by
  unfold RamDecoder.instructionBound
  gcongr

theorem initialize_spec (xs:List ℕ) (w:ℕ) (hw:wordWidth (bitSize xs)≤ w):
    Spec (2 ^ w) (RamDecoder.Input (2 ^ w) xs) RamSolverInitialization.initializeSolver
      (fun _ τ => Output xs τ∧ τ.InpBounded (2 ^ w)) (instructionBound (bitSize xs)):=by
  let L:=bitSize xs
  let C:=canonicalBound L
  have hLC:L≤ C:=canonicalBound_ge L
  have hwDecode:RamDecoder.wordWidth L≤ w:=by
    dsimp only [wordWidth] at hw
    unfold RamDecoder.wordWidth at hw ⊢
    dsimp only [C,L] at hLC
    omega
  have h1:1 < 2 ^ w:=by
    have h2w:2≤ w:=by unfold RamDecoder.wordWidth at hwDecode; omega
    have hp:4≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) h2w
    omega
  have hDecodeCost:=decoder_bound_monotone hLC
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=RamDecoder.decode_bounded_spec xs w hwDecode σ hσ
  by_cases hh:RamDecoder.AcceptedHeader xs
  · obtain ⟨hτP,hτflag⟩:=output_program (2 ^ w) xs τ hh hτ
    by_cases hv:τ.vars "input.valid"=1
    · let P:=decodedProgram xs
      have hsize:bitSize (encodeProgram P)≤ C:=decoded_size xs hh
      have hwPrepare:RamDecoder.wordWidth (bitSize (encodeProgram P))≤ w:=by
        unfold RamDecoder.wordWidth
        have hwC:RamDecoder.wordWidth C≤ w:=hw
        unfold RamDecoder.wordWidth at hwC
        omega
      obtain ⟨υ,hr₂,hυP,hυvalid,hυbits,hυden⟩:=RamPrepareStoredProgram.prepare_spec _ _ P w hwPrepare τ ⟨hτP,hv⟩
      have hτinp:=output_empty_of_valid (2 ^ w) xs τ hh hτ hv
      have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
      have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some true:=by
        simpa [hv] using evalB_condEq
          (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hv]; exact h1)) (evalB_lit h1)
      have hr:=hr₁.seq (Run.ite_true (d:=.skip) hb hr₂)
      have hPrepareCost:=RamPrepareStoredProgram.instructionBound_monotone hsize
      refine ⟨υ,hr.mono ?_,Or.inr ⟨hh,hυvalid,hυP,hυbits,hυden,hυinp⟩,
        hr.inpBounded hσ.2.1⟩
      dsimp only [instructionBound,RamSolverInitialization.instructionBound,
        RamPrepareStoredProgram.instructionBound,Cond.size,Expr.size] at *
      dsimp only [C,L] at hDecodeCost hPrepareCost
      omega
    · have hz:τ.vars "input.valid"=0:=by omega
      have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some false:=by
        simpa [hz] using evalB_condEq
          (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
      have hr:=hr₁.seq (Run.ite_false (c:=RamPrepareStoredProgram.prepare) hb Run.skip)
      refine ⟨τ,hr.mono ?_,Or.inl hz,hr.inpBounded hσ.2.1⟩
      dsimp only [instructionBound,RamSolverInitialization.instructionBound,Cond.size,Expr.size] at *
      dsimp only [C,L] at hDecodeCost
      omega
  · have hz:τ.vars "input.valid"=0:=by
      have hbad:=hτ
      simp only [RamDecoder.Output,if_neg hh] at hbad
      exact hbad.1
    have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some false:=by
      simpa [hz] using evalB_condEq
        (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
    have hr:=hr₁.seq (Run.ite_false (c:=RamPrepareStoredProgram.prepare) hb Run.skip)
    refine ⟨τ,hr.mono ?_,Or.inl hz,hr.inpBounded hσ.2.1⟩
    dsimp only [instructionBound,RamSolverInitialization.instructionBound,Cond.size,Expr.size] at *
    dsimp only [C,L] at hDecodeCost
    omega

end Lax109476Proofs.RamInitializationTotal

end

section

namespace Lax109476Proofs.RamFrontEndTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding RamDecodedProgram

def Output (xs:List ℕ) (σ:Env):Prop:=σ.vars "input.valid"=0∨
  (RamDecoder.AcceptedHeader xs∧ RamSolverFrontEnd.Output (decodedProgram xs) σ)

theorem frontEnd_spec (xs:List ℕ) (w:ℕ) (hw:wordWidth (bitSize xs)≤ w):
    Spec (2 ^ w) (Input (2 ^ w) xs) RamSolverFrontEnd.frontEnd
      (fun _ τ => Output xs τ∧ τ.InpBounded (2 ^ w)) (instructionBound (bitSize xs)):=by
  let C:=canonicalBound (bitSize xs)
  have hwC:RamDecoder.wordWidth C≤ w:=hw
  have h1:1 < 2 ^ w:=by
    have h2w:2≤ w:=by unfold RamDecoder.wordWidth at hwC; omega
    have hp:4≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) h2w
    omega
  rintro σ ⟨hσInput,hσA,hσb,hσc⟩
  obtain ⟨τ,hr₁,hτOutput,hτBounded⟩:=RamInitializationTotal.initialize_spec xs w hw σ hσInput
  rcases hτOutput with hz | ⟨hheader,hτvalid,hτP,hτbits,hτD,hτinp⟩
  · have hb:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some false:=by
      simpa [hz] using evalB_condEq
        (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hz]; omega)) (evalB_lit h1)
    have hr:=hr₁.seq (Run.ite_false (c:=clearProgram) hb Run.skip)
    refine ⟨τ,hr.mono ?_,Or.inl hz,hr.inpBounded hσInput.2.1⟩
    dsimp only [instructionBound,RamSolverFrontEnd.instructionBound,RamInitializationTotal.instructionBound,
      Cond.size,Expr.size]
    omega
  · let P:=decodedProgram xs
    let K:=bitSize (encodeProgram P)
    let H:=2 ^ K
    have hsize:K≤ C:=decoded_size xs hheader
    have hwP:RamDecoder.wordWidth K≤ w:=by
      unfold RamDecoder.wordWidth at hwC ⊢
      omega
    have hHL:H < 2 ^ w:=Nat.pow_lt_pow_right (by decide)
      (by unfold RamDecoder.wordWidth at hwP; omega)
    have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
    have hKB:K < 2 ^ w:=(Nat.lt_two_pow_self (n:=K)).trans hHL
    have hcells:=RamSolverInitialization.cells_bound P
    have hmB:xs.headD 0 < 2 ^ w:=(by omega:xs.headD 0≤ K).trans_lt hKB
    have hnB:xs.tail.headD 0 < 2 ^ w:=(by omega:xs.tail.headD 0≤ K).trans_lt hKB
    have hmnB:xs.headD 0 * xs.tail.headD 0 < 2 ^ w:=
      (by omega:xs.headD 0 * xs.tail.headD 0≤ K).trans_lt hKB
    have hA:∀ i j,Height (P.A i j) H:=fun i j => RamSolverInitialization.datum_height P (.inl (i,j))
    have hb:∀ i,Height (P.b i) H:=fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
    have hc:∀ j,Height (P.c j) H:=fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
    have hD:programDenominator P≤ H:=programDenominator_bound P
    have hguard:=RamSolverFrontEnd.clearing_word_guard K w hwP
    have hτA:=RamAdvanceState.extents_of_run hr₁ "int.A" _ hσA
    have hτb:=RamAdvanceState.extents_of_run hr₁ "int.b" _ hσb
    have hτc:=RamAdvanceState.extents_of_run hr₁ "int.c" _ hσc
    simp only [if_pos hheader.2] at hτA hτb hτc
    obtain ⟨υ,hr₂,hυI,hυP,hυD,hυbits⟩:=clearProgram_spec (2 ^ w) H _ _ P
      hH hmB hnB hmnB hguard hA hb hc hD τ ⟨hτP,hτA,hτb,hτc,hτD⟩
    have hυvalid:=(hr₂.frame_var "input.valid" (by decide)).trans hτvalid
    have hυinp:=(hr₂.frame_inp (by decide)).trans hτinp
    have hbcond:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some true:=by
      simpa [hτvalid] using evalB_condEq
        (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hτvalid]; exact h1)) (evalB_lit h1)
    have hr:=hr₁.seq (Run.ite_true (d:=.skip) hbcond hr₂)
    have hmul:(72 * (K + 1) + 135) * (xs.headD 0 * xs.tail.headD 0 + xs.headD 0 + xs.tail.headD 0)≤
        (72 * (C + 1) + 135) * C:=
      Nat.mul_le_mul (by omega) (hcells.trans hsize)
    refine ⟨υ,hr.mono ?_,Or.inr ⟨hheader,hυP,hυI,hυvalid,hυbits.trans hτbits,hυD,hυinp⟩,
      hr₂.inpBounded hτBounded⟩
    dsimp only [instructionBound,RamSolverFrontEnd.instructionBound,RamInitializationTotal.instructionBound,
      Cond.size,Expr.size,H] at *
    rw [Nat.size_pow]
    dsimp only [C,K,P] at hmul ⊢
    omega

end Lax109476Proofs.RamFrontEndTotal

end

section

namespace Lax109476Proofs.RamUniformSolverBounds

open RamResourcePolynomial

@[gcongr] theorem decision_size_monotone {r s S t u T:ℕ} (hr:r≤ t) (hs:s≤ u) (hS:S≤ T):
    RamCertificateDecision.sizeBound r s S≤ RamCertificateDecision.sizeBound t u T:=by
  unfold RamCertificateDecision.sizeBound
  gcongr

@[gcongr] theorem decision_cost_monotone {r s S t u T:ℕ} (hr:r≤ t) (hs:s≤ u) (hS:S≤ T):
    RamCertificateDecision.instructionBound r s S≤ RamCertificateDecision.instructionBound t u T:=by
  unfold RamCertificateDecision.instructionBound
  gcongr

@[gcongr] theorem branch_width_monotone {S T:ℕ} (h:S≤ T):
    RamSolverBranchBounds.wordWidth S≤ RamSolverBranchBounds.wordWidth T:=by
  unfold RamSolverBranchBounds.wordWidth
  gcongr

@[gcongr] theorem branch_cost_monotone {S T:ℕ} (h:S≤ T):
    RamSolverBranchBounds.instructionBound S≤ RamSolverBranchBounds.instructionBound T:=by
  unfold RamSolverBranchBounds.instructionBound RamSolverBranchBounds.buildCost
    RamSolverBranchBounds.decisionCost RamSolverBranchBounds.recoveryCost
  gcongr

@[gcongr] theorem parameter_monotone {L K:ℕ} (h:L≤ K):
    RamCertificateSetup.parameter L≤ RamCertificateSetup.parameter K:=by
  unfold RamCertificateSetup.parameter
  omega

theorem front_width (L w:ℕ) (hw:wordWidth L≤ w):RamFrontEndTotal.wordWidth L≤ w:=by
  unfold wordWidth at hw
  omega

theorem branch_width (L K w:ℕ) (hK:K≤ canonicalSize L) (hw:wordWidth L≤ w):
    RamSolverBranchBounds.wordWidth (RamCertificateSetup.parameter K)≤ w:=by
  have hp:=parameter_monotone hK
  have hb:=branch_width_monotone hp
  unfold wordWidth parameter at hw
  omega

theorem stack_depth (L K:ℕ) (hK:K≤ canonicalSize L):
    RamRationalReconstruction.depthBound (RamRecoverFeasibleSystem.recoveryBits (RamCertificateSetup.parameter K)) + 1≤
      stackLength L:=by
  unfold stackLength parameter RamRationalReconstruction.depthBound
  have h:=RamRecoveryResourceMonotonicity.recovery_bits (parameter_monotone hK)
  omega

end Lax109476Proofs.RamUniformSolverBounds

end

section

namespace Lax109476Proofs.RamSolverTotalExecution

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamSolverWorkspace RamDecodedProgram RamUniformSolverBounds

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem front_noWrite:RamSolverFrontEnd.frontEnd.NoWrite:=by decide

theorem solve_spec (xs:List ℕ) (w:ℕ) (hw:wordWidth (bitSize xs)≤ w):
    Spec (2 ^ w) (Input (2 ^ w) xs) RamExactSolverProgram.solve (Result xs)
      (instructionBound (bitSize xs)):=by
  let L:=bitSize xs
  have h1:1 < 2 ^ w:=by
    have hwF:=front_width L w hw
    have hh:RamDecoder.wordWidth (canonicalBound L)≤ w:=hwF
    have hw2:2≤ w:=by unfold RamDecoder.wordWidth at hh; omega
    have hp:4≤ 2 ^ w:=by simpa using Nat.pow_le_pow_right (by decide:1≤ 2) hw2
    omega
  rintro σ ⟨hσFront,hσA,hσb,hσc,hσAll⟩
  obtain ⟨τ,hrFront,hτResult,hτBound⟩:=RamFrontEndTotal.frontEnd_spec xs w (front_width L w hw) σ hσFront
  rcases hτResult with hτzero | ⟨hheader,hτFront⟩
  · have hcond:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some false:=by
      simpa [hτzero] using evalB_condEq
        (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid") (by rw [hτzero]; omega)) (evalB_lit h1)
    have hr:=hrFront.seq (Run.ite_false
      (c:=.seq RamCertificateSetup.save RamExactSolverProgram.chooseCertificate) hcond Run.skip)
    exact ⟨τ,hr.mono (by
      dsimp only [instructionBound,Cond.size,Expr.size]
      omega),Or.inl ⟨hτzero,hrFront.out_eq front_noWrite⟩⟩
  · let P:=decodedProgram xs
    let K:=bitSize (encodeProgram P)
    have hK:K≤ canonicalSize L:=decoded_size xs hheader
    have hτA:=RamAdvanceState.extents_of_run hrFront _ _ hσA
    have hτb:=RamAdvanceState.extents_of_run hrFront _ _ hσb
    have hτc:=RamAdvanceState.extents_of_run hrFront _ _ hσc
    have hτAll:=all_of_run hrFront _ _ _ hσAll
    obtain ⟨υ,hrFinish,cert,hυout,hvalid⟩:=RamSolverFinish.finish_spec _ _ (stackLength L) w P
      (branch_width L K w hK hw) (stack_depth L K hK) τ ⟨hτFront,hτA,hτb,hτc,hτAll⟩
    have hcond:(Cond.eq (.var "input.valid") (.lit 1)).evalB (2 ^ w) τ=some true:=by
      simpa [hτFront.2.2.1] using evalB_condEq
        (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "input.valid")
          (by rw [hτFront.2.2.1]; exact h1)) (evalB_lit h1)
    have hr:=hrFront.seq (Run.ite_true (d:=.skip) hcond hrFinish)
    have hcost:=branch_cost_monotone (parameter_monotone hK)
    refine ⟨υ,hr.mono ?_,Or.inr ⟨cert, ?_,hvalid⟩⟩
    · dsimp only [instructionBound,RamSolverFinish.instructionBound,Cond.size,Expr.size,
        parameter,K,P,L] at *
      omega
    · simpa only [hrFront.out_eq front_noWrite] using hυout

end Lax109476Proofs.RamSolverTotalExecution

end

theorem solution:∀ (xs:List Nat) (w:Nat),
  Nat.le (Lax109476Proofs.RamUniformSolverBounds.wordWidth (Lax759944.BinaryWordEncoding.bitSize xs)) w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (Lax109476Proofs.RamSolverTotalExecution.Input
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) w)
        xs)
      Lax109476Proofs.RamExactSolverProgram.solve (Lax109476Proofs.RamSolverTotalExecution.Result xs)
      (Lax109476Proofs.RamUniformSolverBounds.instructionBound (Lax759944.BinaryWordEncoding.bitSize xs)):= @Lax109476Proofs.RamSolverTotalExecution.solve_spec
