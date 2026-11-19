-- Prove2me | solution 1 for Lax109476Proofs.RamStoredFeasibility.decideFeasible_condition_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:47.213248+00:00
-- url     : https://prove2.me/submissions/52c785a1-2425-49fc-8710-69cfd35bb7bb

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRationalFeasibility_decideFeasible_with_flag_spec_native

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
namespace Lax109476Proofs.RamRationalFeasibility
end Lax109476Proofs.RamRationalFeasibility
theorem Lax109476Proofs.RamRationalFeasibility.decideFeasible_with_flag_spec:∀ (m n:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (w:Nat),
  LE.le
      (Lax109476Proofs.RamRationalFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamRationalFeasibility.decideFeasible
      (fun (x τ:Lax808846Proofs.Imp.Env) =>
        And (LE.le (τ.vars "search.found") ((1:Nat)))
          (@Eq Bool
            (@Decidable.decide
              (@Eq Nat (τ.vars "search.found") ((1:Nat)))
              (instDecidableEqNat (τ.vars "search.found") ((1:Nat))))
            (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P)))
      (Lax109476Proofs.RamRationalFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))):= @Lax109476Proofs.RamRationalFeasibility.decideFeasible_with_flag_spec_native

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

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

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

end Lax109476Proofs.WordDecoding

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

theorem readArray_warrs (a:String):(readArray a).warrs =
    [a ++ ".s",a ++ ".n",a ++ ".d",a ++ ".s",a ++ ".s",a ++ ".n",a ++ ".d"]:=by rfl

end Lax109476Proofs.RamReadBlock

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

namespace Lax109476Proofs.WordSolverSize

open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax109476.RationalEncoding EncodingSize

theorem length_le_bitSize (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.length_cons,bitSize_cons]; omega

end Lax109476Proofs.WordSolverSize

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

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

end Lax109476Proofs.RamIntegerFeasibility

namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds

end Lax109476Proofs.RamPaddedFeasibility

namespace Lax109476Proofs.RamRationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

end Lax109476Proofs.RamRationalFeasibility

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep RationalArithmeticBounds IntegerEncoding

theorem decideFeasible_with_flag_spec (m n:ℕ) (P:Program ℚ m n) (w:ℕ)
    (hw:wordWidth (bitSize (encodeProgram P))≤ w):
    Spec (2 ^ w) (Input P) decideFeasible
      (fun _ τ => τ.vars "search.found" ≤ 1∧ decide (τ.vars "search.found"=1)=RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))):=by
  let L:=bitSize (encodeProgram P)
  let H:=2 ^ L
  have hwFront:RamDecoder.wordWidth L≤ w:=by dsimp only [L]; unfold wordWidth at hw; omega
  have hwFeas:RamRationalFeasibility.wordWidth L≤ w:=by dsimp only [L]; unfold wordWidth at hw; omega
  have hH:1≤ H:=Nat.one_le_pow L 2 (by decide)
  have hHB:H < 2 ^ w:=Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwFront; omega)
  have hLB:L < 2 ^ w:=(Nat.lt_two_pow_self (n:=L)).trans hHB
  have hcells:=RamSolverInitialization.cells_bound P
  have hmB:m < 2 ^ w:=(by omega:m≤ L).trans_lt hLB
  have hnB:n < 2 ^ w:=(by omega:n≤ L).trans_lt hLB
  have hmnB:m * n < 2 ^ w:=(by omega:m * n≤ L).trans_lt hLB
  have hms:m.size≤ L:=(RationalSizeBounds.size_le_self m).trans (by omega)
  have hns:n.size≤ L:=(RationalSizeBounds.size_le_self n).trans (by omega)
  have h2:2 < 2 ^ w:=by
    have:=Nat.pow_le_pow_right (n:=2) (by decide) (show 2≤ w by unfold RamDecoder.wordWidth at hwFront; omega)
    norm_num at this; omega
  have hA:∀ i j,Height (P.A i j) H:=fun i j => RamSolverInitialization.datum_height P (.inl (i,j))
  have hb:∀ i,Height (P.b i) H:=fun i => RamSolverInitialization.datum_height P (.inr (.inl i))
  have hc:∀ j,Height (P.c j) H:=fun j => RamSolverInitialization.datum_height P (.inr (.inr j))
  have hD:programDenominator P≤ H:=programDenominator_bound P
  have hB:=RamSolverFrontEnd.clearing_word_guard L w hwFront
  rintro σ ⟨hσP,hσA,hσb,hσc,hσW⟩
  obtain ⟨τ,hr₁,hτbits,hτP,hτarrs⟩:=RamProgramSize.prepareSize_spec (2 ^ w) H m n P
    h2 hH hHB hmB hnB hmnB hA hb hc hLB σ hσP
  obtain ⟨υ,hr₂,hυD,hυP,hυarrs⟩:=RamProgramDenominator.prepareDenominator_spec (2 ^ w) m n P
    (by omega) hmB hnB hmnB (hD.trans_lt hHB) τ hτP
  have hrPre:=hr₁.seq hr₂
  have hυA:=RamAdvanceState.extents_of_run hrPre "int.A" (m * n) hσA
  have hυb:=RamAdvanceState.extents_of_run hrPre "int.b" m hσb
  have hυc:=RamAdvanceState.extents_of_run hrPre "int.c" n hσc
  obtain ⟨ρ,hr₃,hρI,hρP,hρD,hρbits⟩:=clearProgram_spec (2 ^ w) H m n P
    hH hmB hnB hmnB hB hA hb hc hD υ ⟨hυP,hυA,hυb,hυc,hυD⟩
  have hυbits:υ.vars "input.bits"=L:=(hr₂.frame_var _ (by decide)).trans hτbits
  have hρW:=workspace_of_run (hrPre.seq hr₃) m n hσW
  obtain ⟨ξ,hr₄,hξ⟩:=RamRationalFeasibility.decideFeasible_with_flag_spec m n P w hwFeas ρ
    ⟨hρI,hρW,hρP.2.2.2.1,hρP.2.2.2.2.1,hρP.2.2.2.2.2,hρbits.trans hυbits⟩
  have hcount:=Nat.mul_le_mul_left (36 * (L + 1) + 61) hcells
  have hden:=Nat.mul_le_mul_left 13 hcells
  have hclear:=Nat.mul_le_mul_left (72 * (L + 1) + 135) hcells
  refine ⟨ξ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono ?_,hξ⟩
  dsimp only [instructionBound,H]
  rw [Nat.size_pow]
  dsimp only [L] at hcount hden hclear hms hns ⊢
  omega

end Lax109476Proofs.RamStoredFeasibility

namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem decideFeasible_condition_spec (m n:ℕ) (P:Program ℚ m n) (w:ℕ)
    (hw:wordWidth (bitSize (encodeProgram P))≤ w):
    Spec (2 ^ w) (Input P) decideFeasible
      (fun _ τ => (Cond.eq (.var "search.found") (.lit 1)).evalB (2 ^ w) τ =
        some (RationalFeasibilityDecision.feasible P))
      (instructionBound (bitSize (encodeProgram P))):=by
  have h1:1 < 2 ^ w:=by
    have hwD:RamDecoder.wordWidth (bitSize (encodeProgram P))≤ w:=by unfold wordWidth at hw; omega
    have hp:=Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤ w by unfold RamDecoder.wordWidth at hwD; omega)
    norm_num at hp; omega
  refine (decideFeasible_with_flag_spec m n P w hw).post ?_
  rintro σ τ _ ⟨hflag,hvalue⟩
  have he:=evalB_condEq (evalB_var (B:=2 ^ w) (σ:=τ) (x:= "search.found")
    (hflag.trans_lt h1)) (evalB_lit h1)
  simpa only [Bool.beq_eq_decide_eq,hvalue] using he

end Lax109476Proofs.RamStoredFeasibility

end

theorem solution:∀ (m n:ℕ) (P:Lax109476.LinearProgram.Program ℚ m n) (w:ℕ),
  Lax109476Proofs.RamStoredFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))≤
      w→
    Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamStoredFeasibility.Input P)
      Lax109476Proofs.RamStoredFeasibility.decideFeasible
      (fun (x τ:Lax808846Proofs.Imp.Env) =>
        Lax808846Proofs.Imp.Cond.evalB (2 ^ w)
            (Lax808846Proofs.Imp.Cond.eq (Lax808846Proofs.Imp.Expr.var "search.found") (Lax808846Proofs.Imp.Expr.lit 1))
            τ =
          Option.some (Lax109476Proofs.RationalFeasibilityDecision.feasible P))
      (Lax109476Proofs.RamStoredFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (Lax109476.RationalEncoding.encodeProgram P))):= @Lax109476Proofs.RamStoredFeasibility.decideFeasible_condition_spec
