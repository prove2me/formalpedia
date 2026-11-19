-- Prove2me | solution 1 for Lax109476Proofs.RamRecoverFeasibleSystem.recover_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:46.00219+00:00
-- url     : https://prove2.me/submissions/c9cd597f-8b36-4b11-87a1-5f9440a9c609

import Mathlib.Tactic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamStandardPointRecovery_recover_with_cap_spec_native

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

namespace Lax109476Proofs.RamStandardPointRecovery
end Lax109476Proofs.RamStandardPointRecovery
theorem Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec:∀ (m n H S K N w D:Nat) (C:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Int),
  (∀ (i:Fin m) (j:Fin n),Nat.le (C i j).natAbs H)→
    (∀ (i:Fin m),Nat.le (b i).natAbs H)→
      Nat.le H
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) S)→
        Nat.le (Lax109476Proofs.LexicographicBounds.coordinateCap m n H) D→
          Nat.le D.size K→
            Nat.le
                (HAdd.hAdd
                  (HMul.hMul
                    ((4:Nat)) K)
                  ((2:Nat)))
                S→
              Nat.le
                  (HAdd.hAdd
                    (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                    ((1:Nat)))
                  N→
                Nat.le
                    (Lax109476Proofs.RamPointRecoveryBounds.wordWidth
                      (HAdd.hAdd m m) n S)
                    w→
                  (∃ (x:Fin n→ Rat),
                      @Lax109476Proofs.LexicographicSupport.Feasible m n
                        (@Matrix.map (Fin m) (Fin n) Int Rat C fun (z:Int) => @Int.cast Rat Rat.instIntCast z)
                        (fun (i:Fin m) => @Int.cast Rat Rat.instIntCast (b i)) x)→
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) w)
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And
                          (@Lax109476Proofs.RamPointInitialization.Base
                            (HAdd.hAdd m m) n
                            (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) σ)
                          (And
                            (Lax109476Proofs.RamRecoveryThreshold.Workspace
                              (HAdd.hAdd m m) n σ)
                            (And (Lax109476Proofs.RamEllipsoidStep.Extents "point.x" n σ)
                              (And (@Eq Nat (σ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))))
                      Lax109476Proofs.RamPointInitialization.recover
                      (fun (x τ:Lax808846Proofs.Imp.Env) =>
                        ∃ (x:Fin n→ Rat),
                          And
                            (@Lax109476Proofs.RamRecoveryThreshold.Persistent
                              (HAdd.hAdd m m) n
                              (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) x n τ)
                            (And
                              (@Lax109476Proofs.LexicographicSupport.Feasible m n
                                (@Matrix.map (Fin m) (Fin n) Int Rat C fun (z:Int) => @Int.cast Rat Rat.instIntCast z)
                                (fun (i:Fin m) => @Int.cast Rat Rat.instIntCast (b i)) x)
                              (∀ (j:Fin n),
                                Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                                  (Lax109476Proofs.LexicographicBounds.coordinateCap m n H))))
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (HMul.hMul
                            ((33:Nat)) n)
                          ((22:Nat)))
                        (Lax109476Proofs.RamPointRecoveryBounds.instructionBound
                          (HAdd.hAdd m m) n S K)):= @Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec_native

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

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

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

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding PointRecovery

def withSlacks {m n:ℕ} (P:Program ℤ m n) (x:Fin n→ ℚ):Fin (n + m)→ ℚ:=
  Fin.addCases x (fun i => (P.b i:ℚ) - rowValue (rationalProgram P) x i)

theorem slack_rows {m n:ℕ} (P:Program ℤ m n) (z:Fin (n + m)→ ℚ) (i:Fin m):
    (((slackMatrix P).map (fun a => (a:ℚ))) *ᵥ z) i =
      rowValue (rationalProgram P) (fun j => z (Fin.castAdd m j)) i + z (Fin.natAdd n i):=by
  simp [slackMatrix,Matrix.mulVec,Matrix.map,dotProduct,Fin.sum_univ_add,
    rowValue,rationalProgram,apply_ite]

theorem withSlacks_feasible {m n:ℕ} (P:Program ℤ m n) (x:Fin n→ ℚ)
    (hx:PrimalFeasible (rationalProgram P) x):
    LexicographicSupport.Feasible (slackMatrix P |>.map (fun a => (a:ℚ)))
      (fun i => (P.b i:ℚ)) (withSlacks P x):=by
  constructor
  · intro j
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j
    · simpa [withSlacks] using hx.1 j
    · simpa [withSlacks,rationalProgram] using sub_nonneg.mpr (hx.2 i)
  · funext i
    rw [slack_rows]
    simp [withSlacks]

theorem slack_point_feasible {m n:ℕ} (P:Program ℤ m n) (z:Fin (n + m)→ ℚ)
    (hz:LexicographicSupport.Feasible (slackMatrix P |>.map (fun a => (a:ℚ)))
      (fun i => (P.b i:ℚ)) z):
    PrimalFeasible (rationalProgram P) (fun j => z (Fin.castAdd m j)):=by
  refine ⟨fun j => hz.1 _,fun i => ?_⟩
  have h:=congrFun hz.2 i
  rw [slack_rows] at h
  have hpos:=hz.1 (Fin.natAdd n i)
  change 0≤ z (Fin.natAdd n i) at hpos
  change rowValue _ _ _≤ (P.b i:ℚ)
  linarith

end Lax109476Proofs.IntegerPointRecovery

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

theorem height_neg (q:ℚ) (B:ℕ) (hq:Height q B):Height (-q) B:=by
  simpa only [Height,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

theorem height_nat (v B:ℕ) (hv:v≤ B) (hB:1≤ B):Height (v:ℚ) B:=by
  simpa [Height] using And.intro hv hB

end Lax109476Proofs.RationalArithmeticBounds

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

namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars
open BinaryOptimization RamBisectionCommit

def preserves (B:ℕ) (Q:Env→ Prop) (c:Com):Prop:=
  ∀ {σ τ k},Run B c σ τ k→ Q σ→ Q τ

end Lax109476Proofs.RamBisectionLoop

end

section

namespace Lax109476Proofs.RamBuildVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamCenterUpdate RamEllipsoidStep RationalArithmeticBounds

def Invariant {n:ℕ} (a:String) (v:Fin n→ ℚ) (Q:Env→ Prop) (σ:Env):Prop:=
  Q σ∧ Represents a (filled v (σ.vars "build.i")) σ∧
    σ.vars "build.i" ≤ n∧ σ.vars "build.count"=n

set_option maxHeartbeats 0 in
theorem step_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Invariant a v Q σ∧ σ.vars "build.i" < n) (step a selector)
      (fun σ τ => Invariant a v Q τ∧ τ.vars "build.i"=σ.vars "build.i" + 1)
      (selectorCost + 19):=by
  rintro σ ⟨⟨hσQ,hσa,hσi,hσn⟩,hi⟩
  let i:Fin n:= ⟨σ.vars "build.i",hi⟩
  obtain ⟨τ,hr₁,hτQ,hτv⟩:=hselector i σ ⟨hσQ,rfl,hσn⟩
  have hτi:τ.vars "build.i"=i.val:=hr₁.frame_var _ hiFrame
  have hτa:Represents a (filled v i.val) τ:=RamReadBody.represents_frame _ _ hσa hr₁ haFrame
  have hiB:i.val < B:=i.isLt.trans hnB
  have hr₂:Run B (.assign "vec.i" (.var "build.i")) τ (τ.setVar "vec.i" i.val) 2:=
    Run.assign (by simpa only [hτi] using evalB_var (B:=B) (σ:=τ) (x:= "build.i") (hτi ▸ hiB))
  have hstore:=storeReduced_spec B a (filled v i.val) (v i) i.val
    (by simpa only [filled,List.length_ofFn] using i.isLt) h1 hiB
    ((hv i).1.trans_lt hMB) ((hv i).2.trans_lt hMB)
  obtain ⟨υ,hr₃,hυa⟩:=hstore (τ.setVar "vec.i" i.val)
    ⟨hτa,by simp,by simpa [FractionOutput,vars_setVar] using hτv⟩
  have hυQ:Q υ:=hQstore hr₃ (hQvec τ i.val hτQ)
  have hυi:υ.vars "build.i"=i.val:=
    (hr₃.frame_var _ (by simp [storeReduced,Com.wvars])).trans (by simpa using hτi)
  have hsumB:Bop.add.apply (υ.vars "build.i") 1 < B:=by simpa [hυi] using lt_of_le_of_lt i.isLt hnB
  have hr₄:Run B (.assign "build.i" (.add (.var "build.i") (.lit 1))) υ (υ.setVar "build.i" (i.val + 1)) 4:=
    Run.assign (by simpa only [hυi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=υ) (x:= "build.i") (hυi ▸ hiB)) (evalB_lit h1) hsumB))
  have hr:=(hr₁.seq (hr₂.seq hr₃)).seq hr₄
  have hfilled:Represents a (filled v (i.val + 1)) υ:=by rw [← filled_step]; exact hυa
  refine ⟨_,hr.mono (by omega), ⟨hQset υ (i.val + 1) hυQ, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change i.val + 1≤ n; exact i.isLt
  · exact (hr.frame_var _ (by simp [Com.wvars,storeReduced,hnFrame])).trans hσn
  · simp [i]

theorem loop_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t)):
    Spec B (fun σ => Q σ∧ Represents a (List.replicate n 0) σ∧ σ.vars "build.count"=n)
      (loop a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 23) * n + 6):=by
  have hlo:=Spec.forRangeZero "build.i" "build.count" (Invariant a v Q) n (selectorCost + 19) hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2)
    (step_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector hiFrame hnFrame haFrame hQstore hQset hQvec)
  refine ((hlo.pre ?_).post ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega)
  · rintro σ ⟨hσQ,hσa,hσn⟩
    exact ⟨hQset σ 0 hσQ,by simpa only [Represents,arrs_setVar,vars_setVar,ite_true,filled_zero] using hσa,by simp,by simpa using hσn⟩
  · rintro σ τ _ ⟨hτ,hcounter⟩
    exact ⟨hτ.1,by simpa only [hcounter,filled_done] using hτ.2.1,hτ.2.2.2⟩

theorem build_spec (B M n selectorCost:ℕ) (a:String) (v:Fin n→ ℚ)
    (selector:Com) (Q:Env→ Prop) (h1:1 < B) (hnB:n < B) (hMB:M < B)
    (hv:∀ i,Height (v i) M)
    (hselector:∀ i:Fin n,Spec B (fun σ => Q σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=n)
      selector (fun _ τ => Q τ∧ FractionOutput (v i) τ) selectorCost)
    (hiFrame:"build.i" ∉ selector.wvars) (hnFrame:"build.count" ∉ selector.wvars)
    (haFrame:∀ s∈ RamCopy.suffixes,a ++ s∉ selector.warrs)
    (hQstore:RamBisectionLoop.preserves B Q (storeReduced a))
    (hQzero:RamBisectionLoop.preserves B Q (RamZeroArray.zeroRationalArray a))
    (hQset:∀ σ t,Q σ→ Q (σ.setVar "build.i" t))
    (hQvec:∀ σ t,Q σ→ Q (σ.setVar "vec.i" t))
    (hQlength:∀ σ t,Q σ→ Q (σ.setVar "vec.n" t)):
    Spec B (fun σ => Q σ∧ Extents a n σ∧ σ.vars "build.count"=n)
      (build a selector) (fun _ τ => Q τ∧ Represents a (List.ofFn v) τ∧ τ.vars "build.count"=n)
      ((selectorCost + 56) * n + 26):=by
  rintro σ ⟨hσQ,hσa,hσn⟩
  have hr₁:Run B (.assign "vec.n" (.var "build.count")) σ (σ.setVar "vec.n" n) 2:=
    Run.assign (by simpa only [hσn] using evalB_var (B:=B) (σ:=σ) (x:= "build.count") (hσn ▸ hnB))
  obtain ⟨τ,hr₂,hτa,hτn,hτframe⟩:=RamZeroArray.zeroRationalArray_spec B n a hnB h1
    (σ.setVar "vec.n" n) ⟨hσa ".s" (by simp),hσa ".n" (by simp),hσa ".d" (by simp),by simp⟩
  have hτQ:=hQzero hr₂ (hQlength σ n hσQ)
  have hτcount:τ.vars "build.count"=n:=
    (hr₂.frame_var _ (by simp [RamZeroArray.zeroRationalArray,RamZeroArray.fillConstant,Com.wvars,Lib.Fill.put])).trans
      (by simpa using hσn)
  obtain ⟨υ,hr₃,hυ⟩:=loop_spec B M n selectorCost a v selector Q h1 hnB hMB hv hselector
    hiFrame hnFrame haFrame hQstore hQset hQvec τ ⟨hτQ,hτa,hτcount⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq hr₃)).mono ?_,hυ⟩
  simp only [Nat.add_mul]
  omega

end Lax109476Proofs.RamBuildVector

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

namespace Lax109476Proofs.RamRecoveryQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds RamStoredProgram

theorem extent_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    (m n:ℕ) (hσ:Extent m n σ):Extent m n τ:=
  ⟨RamAdvanceState.extents_of_run hr _ _ hσ.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.1,
    RamAdvanceState.extents_of_run hr _ _ hσ.2.2⟩

end Lax109476Proofs.RamRecoveryQuery

end

section

namespace Lax109476Proofs.RamNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def powerInvariant (a n:ℕ) (σ:Env):Prop:=
  σ.vars "power.base"=a∧ σ.vars "power.exponent"=n∧
    σ.vars "power.i" ≤ n∧ σ.vars "power.value"=a ^ σ.vars "power.i"

theorem powerStep_spec (B a n:ℕ) (ha:1≤ a) (haB:a < B)
    (hnB:n < B) (hpB:a ^ n < B):
    Spec B (fun σ => powerInvariant a n σ∧ σ.vars "power.i" < n) powerStep
      (fun σ τ => powerInvariant a n τ∧ τ.vars "power.i"=σ.vars "power.i" + 1) 8:=by
  rintro σ ⟨⟨hσa,hσn,hσiN,hσp⟩,hσi⟩
  have hiB:σ.vars "power.i" < B:=hσi.trans hnB
  have hnextB:a ^ (σ.vars "power.i" + 1) < B:=
    (Nat.pow_le_pow_right ha hσi).trans_lt hpB
  have hcurB:a ^ σ.vars "power.i" < B:=
    (Nat.pow_le_pow_right ha hσiN).trans_lt hpB
  have hmulB:σ.vars "power.value" * σ.vars "power.base" < B:=by
    rw [hσp,hσa, ← pow_succ]
    exact hnextB
  have h1:1 < B:=ha.trans_lt haB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (powerInvariant a n τ) (@Eq Nat (Env.vars τ "power.i") (c0 (Env.vars σ_1 "power.i") ((1:Nat))))) σ; let c2:Nat:=Nat.mul (Env.vars σ "power.value") (Env.vars σ "power.base"); let c3:Env:=Env.setVar σ "power.value" c2; let c4:Nat:=Env.vars c3 "power.i"; let c5:Nat:=c0 c4 ((1:Nat)); let c6:Env:=Env.setVar c3 "power.i" c5; let c7:Nat→ Nat:=c0 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))); let c9:Expr:=Expr.add (Expr.var "power.i") (Expr.lit ((1:Nat))); let c10:Nat:=c7 (Expr.size c9); @Exists.intro Env (fun (σ':Env) => And (Run B powerStep σ σ' ((8:Nat))) (c1 σ')) c6 (@And.intro (Run B powerStep σ c6 ((8:Nat))) (c1 c6) (RunStep.mono B powerStep σ c6 (c0 c8 c10) ((8:Nat)) (RunStep.seq B (Com.assign "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base"))) (Com.assign "power.i" c9) σ c3 c6 c8 c10 (RunStep.assign B σ "power.value" (Expr.mul (Expr.var "power.value") (Expr.var "power.base")) c2 (RunStep.eval_mul B σ (Expr.var "power.value") (Expr.var "power.base") (Env.vars σ "power.value") (Env.vars σ "power.base") (RunStep.eval_var B σ "power.value" (?nAX_g4671_0_0_0)) (RunStep.eval_var B σ "power.base" (?nAX_g4671_0_0_1)) hmulB)) (RunStep.assign B c3 "power.i" c9 c5 (RunStep.eval_add B c3 (Expr.var "power.i") (Expr.lit ((1:Nat))) c4 ((1:Nat)) (RunStep.eval_var B c3 "power.i" (?nAX_g4671_0_0_2)) (RunStep.eval_lit B ((1:Nat)) c3 h1) (?nAX_g4671_0_0_3)))) (?nAX_g4671_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4671_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4671_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [powerInvariant,pow_succ]

theorem power_spec (B a n:ℕ) (ha:1≤ a) (haB:a < B)
    (hnB:n < B) (hpB:a ^ n < B):
    Spec B (fun σ => σ.vars "power.base"=a∧ σ.vars "power.exponent"=n) power
      (fun _ τ => τ.vars "power.value"=a ^ n∧
        τ.vars "power.base"=a∧ τ.vars "power.exponent"=n) (12 * n + 8):=by
  have hlo:=Spec.forRangeZero "power.i" "power.exponent" (powerInvariant a n) n 8 hnB
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (powerStep_spec B a n ha haB hnB hpB)
  have h1:1 < B:=ha.trans_lt haB
  rintro σ ⟨hσa,hσn⟩
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "power.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "power.i") (Expr.var "power.exponent")) powerStep); let c1:Env:=Env.setVar σ "power.value" ((1:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c3 (c4 (c3 ((8:Nat)) ((4:Nat))) n) ((6:Nat)); let c6:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (powerInvariant a n σ') (@Eq Nat (Env.vars σ' "power.i") n)); let c7:Nat:=c3 (c4 ((12:Nat)) n) ((8:Nat)); let c8:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a n; let c9:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "power.value") c8) (And (@Eq Nat (Env.vars τ "power.base") a) (@Eq Nat (Env.vars τ "power.exponent") n))) σ; let c10:Env→ Prop:=fun (σ':Env) => And (Run B power σ σ' c7) (c9 σ'); let c11:Prop:= @Exists Env c10; let c12:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c11) (RunStep.use B (fun (σ_1:Env) => powerInvariant a n (Env.setVar σ_1 "power.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (powerInvariant a n σ') (@Eq Nat (Env.vars σ' "power.i") n)) c5 hlo c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (powerInvariant a n w) (@Eq Nat (Env.vars w "power.i") n))) => let c0_1:Prop:=And (powerInvariant a n w) (@Eq Nat (Env.vars w "power.i") n); @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c11) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c10 w (@And.intro (Run B power σ w c7) (c9 w) (RunStep.mono B power σ w (c3 c12 c5) c7 (RunStep.seq B (Com.assign "power.value" (Expr.lit ((1:Nat)))) c0 σ c1 w c12 c5 (RunStep.assign B σ "power.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) left) (?nAX_g4673_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4673_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [powerInvariant]

def factorialInvariant (n:ℕ) (σ:Env):Prop:=
  σ.vars "factorial.n"=n∧ σ.vars "factorial.i" ≤ n∧
    σ.vars "factorial.value"=(σ.vars "factorial.i").factorial

theorem factorialStep_spec (B n:ℕ) (hnB:n < B) (hfB:n.factorial < B):
    Spec B (fun σ => factorialInvariant n σ∧ σ.vars "factorial.i" < n) factorialStep
      (fun σ τ => factorialInvariant n τ∧ τ.vars "factorial.i"=σ.vars "factorial.i" + 1) 8:=by
  rintro σ ⟨⟨hσn,hσiN,hσf⟩,hσi⟩
  have h1:1 < B:=lt_of_le_of_lt (Nat.factorial_pos n) hfB
  have hiB:σ.vars "factorial.i" < B:=hσi.trans hnB
  have hi1B:σ.vars "factorial.i" + 1 < B:=lt_of_le_of_lt hσi hnB
  have hcurB:(σ.vars "factorial.i").factorial < B:=(Nat.factorial_le hσiN).trans_lt hfB
  have hnextB:(σ.vars "factorial.i" + 1).factorial < B:=(Nat.factorial_le hσi).trans_lt hfB
  have hmulB:σ.vars "factorial.value" * (σ.vars "factorial.i" + 1) < B:=by
    rw [hσf,Nat.mul_comm, ← Nat.factorial_succ]
    exact hnextB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Env→ Prop:=(fun (σ_1 τ:Env) => And (factorialInvariant n τ) (@Eq Nat (Env.vars τ "factorial.i") (c0 (Env.vars σ_1 "factorial.i") ((1:Nat))))) σ; let c2:Nat:=c0 (Env.vars σ "factorial.i") ((1:Nat)); let c3:Env:=Env.setVar σ "factorial.i" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "factorial.value"; let c6:Nat:=c4 "factorial.i"; let c7:Nat:=Nat.mul c5 c6; let c8:Env:=Env.setVar c3 "factorial.value" c7; let c9:Nat→ Nat:=c0 ((1:Nat)); let c10:Expr:=Expr.add (Expr.var "factorial.i") (Expr.lit ((1:Nat))); let c11:Nat:=c9 (Expr.size c10); let c12:Nat:=c9 (Expr.size (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i"))); @Exists.intro Env (fun (σ':Env) => And (Run B factorialStep σ σ' ((8:Nat))) (c1 σ')) c8 (@And.intro (Run B factorialStep σ c8 ((8:Nat))) (c1 c8) (RunStep.mono B factorialStep σ c8 (c0 c11 c12) ((8:Nat)) (RunStep.seq B (Com.assign "factorial.i" c10) (Com.assign "factorial.value" (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i"))) σ c3 c8 c11 c12 (RunStep.assign B σ "factorial.i" c10 c2 (RunStep.eval_add B σ (Expr.var "factorial.i") (Expr.lit ((1:Nat))) (Env.vars σ "factorial.i") ((1:Nat)) (RunStep.eval_var B σ "factorial.i" hiB) (RunStep.eval_lit B ((1:Nat)) σ h1) hi1B)) (RunStep.assign B c3 "factorial.value" (Expr.mul (Expr.var "factorial.value") (Expr.var "factorial.i")) c7 (RunStep.eval_mul B c3 (Expr.var "factorial.value") (Expr.var "factorial.i") c5 c6 (RunStep.eval_var B c3 "factorial.value" (?nAX_g4676_0_0_0)) (RunStep.eval_var B c3 "factorial.i" (?nAX_g4676_0_0_1)) (?nAX_g4676_0_0_2)))) (?nAX_g4676_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4676_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4676_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [factorialInvariant,Nat.factorial_succ,Nat.mul_comm]

theorem factorial_spec (B n:ℕ) (hnB:n < B) (hfB:n.factorial < B):
    Spec B (fun σ => σ.vars "factorial.n"=n) factorial
      (fun _ τ => τ.vars "factorial.value"=n.factorial∧ τ.vars "factorial.n"=n)
      (12 * n + 8):=by
  have hlo:=Spec.forRangeZero "factorial.i" "factorial.n" (factorialInvariant n) n 8 hnB
    (fun _ h => h.2.1) (fun _ h => h.1) (factorialStep_spec B n hnB hfB)
  have h1:1 < B:=lt_of_le_of_lt (Nat.factorial_pos n) hfB
  intro σ hσ
  (expose_names;
    (refine let c0:Com:=Com.seq (Com.assign "factorial.i" (Expr.lit ((0:Nat)))) (Com.while (Cond.lt (Expr.var "factorial.i") (Expr.var "factorial.n")) factorialStep); let c1:Env:=Env.setVar σ "factorial.value" ((1:Nat)); let c2:Env→ Nat→ Prop:=Run B c0 c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=c3 (c4 (c3 ((8:Nat)) ((4:Nat))) n) ((6:Nat)); let c6:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (factorialInvariant n σ') (@Eq Nat (Env.vars σ' "factorial.i") n)); let c7:Nat:=c3 (c4 ((12:Nat)) n) ((8:Nat)); let c8:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "factorial.value") (Nat.factorial n)) (@Eq Nat (Env.vars τ "factorial.n") n)) σ; let c9:Env→ Prop:=fun (σ':Env) => And (Run B factorial σ σ' c7) (c8 σ'); let c10:Prop:= @Exists Env c9; let c11:Nat:=c3 ((1:Nat)) (Expr.size (Expr.lit ((1:Nat)))); @Exists.casesOn Env c6 (fun (x:@Exists Env c6) => c10) (RunStep.use B (fun (σ_1:Env) => factorialInvariant n (Env.setVar σ_1 "factorial.i" ((0:Nat)))) c0 (fun (x σ':Env) => And (factorialInvariant n σ') (@Eq Nat (Env.vars σ' "factorial.i") n)) c5 hlo c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (factorialInvariant n w) (@Eq Nat (Env.vars w "factorial.i") n))) => let c0_1:Prop:=And (factorialInvariant n w) (@Eq Nat (Env.vars w "factorial.i") n); @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c10) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c9 w (@And.intro (Run B factorial σ w c7) (c8 w) (RunStep.mono B factorial σ w (c3 c11 c5) c7 (RunStep.seq B (Com.assign "factorial.value" (Expr.lit ((1:Nat)))) c0 σ c1 w c11 c5 (RunStep.assign B σ "factorial.value" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) left) (?nAX_g4678_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4678_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hlo
  all_goals simp_all [factorialInvariant]

end Lax109476Proofs.RamNaturalPower

end

section

namespace Lax109476Proofs.RamCoordinateCap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNaturalPower RamFrame IntegerCertificates

def magnitude (m n H:ℕ):ℕ:=
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  m + n + H + K + K * H * H + a + K.factorial + a ^ K + coordinateCap m n H + 10

set_option maxHeartbeats 0 in
theorem prepareCap_spec (B m n H:ℕ) (hB:magnitude m n H < B):
    Spec B (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧ σ.vars "cap.H"=H)
      prepareCap
      (fun _ τ => τ.vars "cap.value"=coordinateCap m n H∧ τ.vars "cap.H"=H∧
        τ.vars "query.m"=m∧ τ.vars "query.n"=n)
      (24 * (2 * (m + n) + 2) + 42):=by
  let K:=2 * (m + n) + 2
  let a:=K * H * H + 1
  have hmB:m < B:=by dsimp [magnitude] at hB; omega
  have hnB:n < B:=by dsimp [magnitude] at hB; omega
  have hHB:H < B:=by dsimp [magnitude] at hB; omega
  have hKB:K < B:=by dsimp [magnitude,K] at hB ⊢; omega
  have haB:a < B:=by dsimp [magnitude,K,a] at hB ⊢; omega
  have hfB:K.factorial < B:=by dsimp [magnitude,K] at hB ⊢; omega
  have hpB:a ^ K < B:=by dsimp [magnitude,K,a] at hB ⊢; omega
  have hcB:coordinateCap m n H < B:=by dsimp [magnitude] at hB; omega
  have h1:1 < B:=by dsimp [magnitude] at hB; omega
  have h2:2 < B:=by dsimp [magnitude] at hB; omega
  have hsum:m + n < B:=by dsimp [K] at hKB; omega
  have hdouble:2 * (m + n) < B:=by dsimp [K] at hKB; omega
  have hkhh:K * H * H < B:=by dsimp [a] at haB; omega
  have hkh:K * H < B:=by
    by_cases hH:H=0
    · simp [hH]; omega
    · have hm:=Nat.le_mul_of_pos_right (K * H) (by omega:0 < H)
      exact hm.trans_lt hkhh
  have hfactorial:=spec_with_fields ["cap.k", "cap.H", "query.m", "query.n"]
    (factorial_spec B K hKB hfB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hpower:=spec_with_fields ["cap.k", "cap.H", "cap.factorial", "query.m", "query.n"]
    (power_spec B a K (by dsimp [a]; omega) haB hKB hpB)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hc:coordinateCap m n H=K.factorial * a ^ K:=by
    simp only [coordinateCap,K,a,pow_two,Nat.mul_assoc]
  rintro σ ⟨hσm,hσn,hσH⟩
  dsimp only [K] at hfactorial hpower hfB hpB
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((2:Nat)); let c3:Nat:=c0 (Env.vars σ "query.m") (Env.vars σ "query.n"); let c4:Nat:=c2 c3; let c5:Nat:=c0 c4 ((2:Nat)); let c6:Env:=Env.setVar σ "cap.k" c5; let c7:Nat:=Env.vars c6 "cap.k"; let c8:Env:=Env.setVar c6 "factorial.n" c7; let c9:Env→ Nat→ Prop:=Run B factorial c8; let c10:Nat:=c0 (c2 (c0 m n)) ((2:Nat)); let c11:Nat:=c0 (c1 ((12:Nat)) c10) ((8:Nat)); let c12:Nat:=Nat.factorial c10; let c13:List String:= @List.cons String "query.m" (@List.cons String "query.n" (@List.nil String)); let c14:Env→ Env→ Prop:=FieldsAgree (@List.cons String "cap.k" (@List.cons String "cap.H" c13)); let c15:Env→ Prop:=c14 c8; let c16:String→ List Nat:=Env.arrs c8; let c17:Env→ Prop:=fun (σ':Env) => And (c9 σ' c11) (And (And (@Eq Nat (Env.vars σ' "factorial.value") c12) (@Eq Nat (Env.vars σ' "factorial.n") c10)) (And (c15 σ') (@Eq (String→ List Nat) (Env.arrs σ') c16))); let c18:Nat:=c0 (c1 ((24:Nat)) c10) ((42:Nat)); let c19:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "cap.value") (coordinateCap m n H)) (And (@Eq Nat (Env.vars τ "cap.H") H) (And (@Eq Nat (Env.vars τ "query.m") m) (@Eq Nat (Env.vars τ "query.n") n)))) σ; let c20:Env→ Prop:=fun (σ':Env) => And (Run B prepareCap σ σ' c18) (c19 σ'); let c21:Prop:= @Exists Env c20; let c22:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a c10; let c23:Env→ Env→ Prop:=FieldsAgree (@List.cons String "cap.k" (@List.cons String "cap.H" (@List.cons String "cap.factorial" c13))); let c24:Nat→ Nat:=c0 ((1:Nat)); let c25:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.add (Expr.var "query.m") (Expr.var "query.n")); let c26:Expr:=Expr.add c25 (Expr.lit ((2:Nat))); let c27:Nat:=c24 (Expr.size c26); let c28:Nat:=c24 (Expr.size (Expr.var "cap.k")); let c29:Nat→ Nat:=c0 c28; let c30:Nat→ Nat:=c0 c11; let c31:Nat:=c24 (Expr.size (Expr.var "factorial.value")); let c32:Expr:=Expr.mul (Expr.mul (Expr.var "cap.k") (Expr.var "cap.H")) (Expr.var "cap.H"); let c33:Expr:=Expr.add c32 (Expr.lit ((1:Nat))); let c34:Nat:=c24 (Expr.size c33); let c35:Nat:=c24 (Expr.size (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value"))); let c36:Nat:=c30 c35; let c37:Nat:=c29 c36; let c38:Nat:=c0 c34 c37; let c39:Nat:=c0 c31 c38; let c40:Nat:=c30 c39; let c41:Nat:=c29 c40; let c42:Com:=Com.assign "power.base" c33; let c43:Com:=Com.assign "cap.value" (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value")); let c44:Com:=Com.seq power c43; let c45:Com:=Com.seq (Com.assign "power.exponent" (Expr.var "cap.k")) c44; let c46:Com:=Com.seq c42 c45; let c47:Com:=Com.seq (Com.assign "cap.factorial" (Expr.var "factorial.value")) c46; let c48:Com:=Com.seq factorial c47; @Exists.casesOn Env c17 (fun (x:@Exists Env c17) => c21) (RunStep.use B (fun (σ_1:Env) => @Eq Nat (Env.vars σ_1 "factorial.n") c10) factorial (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "factorial.value") c12) (@Eq Nat (Env.vars τ "factorial.n") c10)) (And (c14 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c11 hfactorial c8 ?_) fun (w:Env) (h:And (c9 w c11) (And (And (@Eq Nat (Env.vars w "factorial.value") c12) (@Eq Nat (Env.vars w "factorial.n") c10)) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "factorial.value") c12) (@Eq Nat (Env.vars w "factorial.n") c10)) (And (c15 w) (@Eq (String→ List Nat) (Env.arrs w) c16)); let c1_1:String→ Nat:=Env.vars (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")); let c2_1:Nat:=c1_1 "cap.k"; let c3_1:Nat:=c1_1 "cap.H"; let c4_1:Nat:=c1 c2_1 c3_1; let c5_1:Nat:=c1 c4_1 c3_1; let c6_1:Nat:=c0 c5_1 ((1:Nat)); let c7_1:Env:=Env.setVar (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "power.base" c6_1; let c8_1:Nat:=Env.vars c7_1 "cap.k"; let c9_1:Env:=Env.setVar c7_1 "power.exponent" c8_1; let c10_1:Env→ Nat→ Prop:=Run B power c9_1; let c11_1:Env→ Prop:=c23 c9_1; let c12_1:String→ List Nat:=Env.arrs c9_1; let c13_1:Env→ Prop:=fun (σ':Env) => And (c10_1 σ' c11) (And (And (@Eq Nat (Env.vars σ' "power.value") c22) (And (@Eq Nat (Env.vars σ' "power.base") a) (@Eq Nat (Env.vars σ' "power.exponent") c10))) (And (c11_1 σ') (@Eq (String→ List Nat) (Env.arrs σ') c12_1))); let c14_1:String→ Nat:=Env.vars c9_1; @And.casesOn (c9 w c11) c0_1 (fun (x:And (c9 w c11) c0_1) => c21) h fun (left:c9 w c11) (right:c0_1) => @Exists.casesOn Env c13_1 (fun (x:@Exists Env c13_1) => c21) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "power.base") a) (@Eq Nat (Env.vars σ_1 "power.exponent") c10)) power (fun (σ_1 τ:Env) => And (And (@Eq Nat (Env.vars τ "power.value") c22) (And (@Eq Nat (Env.vars τ "power.base") a) (@Eq Nat (Env.vars τ "power.exponent") c10))) (And (c23 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c11 hpower c9_1 ?_) fun (w_1:Env) (h_1:And (c10_1 w_1 c11) (And (And (@Eq Nat (Env.vars w_1 "power.value") c22) (And (@Eq Nat (Env.vars w_1 "power.base") a) (@Eq Nat (Env.vars w_1 "power.exponent") c10))) (And (c11_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c12_1)))) => let c0_2:Prop:=And (And (@Eq Nat (Env.vars w_1 "power.value") c22) (And (@Eq Nat (Env.vars w_1 "power.base") a) (@Eq Nat (Env.vars w_1 "power.exponent") c10))) (And (c11_1 w_1) (@Eq (String→ List Nat) (Env.arrs w_1) c12_1)); let c1_2:Nat:=c1 (Env.vars w_1 "cap.factorial") (Env.vars w_1 "power.value"); let c2_2:Env:=Env.setVar w_1 "cap.value" c1_2; let c3_2:String→ Nat:=Env.vars c2_2; @And.casesOn (c10_1 w_1 c11) c0_2 (fun (x:And (c10_1 w_1 c11) c0_2) => c21) h_1 fun (left_1:c10_1 w_1 c11) (right_1:c0_2) => @Exists.intro Env c20 c2_2 (@And.intro (Run B prepareCap σ c2_2 c18) (c19 c2_2) (RunStep.mono B prepareCap σ c2_2 (c0 c27 c41) c18 (RunStep.seq B (Com.assign "cap.k" c26) (Com.seq (Com.assign "factorial.n" (Expr.var "cap.k")) c48) σ c6 c2_2 c27 c41 (RunStep.assign B σ "cap.k" c26 c5 (RunStep.eval_add B σ c25 (Expr.lit ((2:Nat))) c4 ((2:Nat)) (RunStep.eval_mul B σ (Expr.lit ((2:Nat))) (Expr.add (Expr.var "query.m") (Expr.var "query.n")) ((2:Nat)) c3 (RunStep.eval_lit B ((2:Nat)) σ h2) (RunStep.eval_add B σ (Expr.var "query.m") (Expr.var "query.n") (Env.vars σ "query.m") (Env.vars σ "query.n") (RunStep.eval_var B σ "query.m" (?nAX_g4681_0_0_0)) (RunStep.eval_var B σ "query.n" (?nAX_g4681_0_0_1)) (?nAX_g4681_0_0_2)) (?nAX_g4681_0_0_3)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4681_0_0_4))) (RunStep.seq B (Com.assign "factorial.n" (Expr.var "cap.k")) c48 c6 c8 c2_2 c28 c40 (RunStep.assign B c6 "factorial.n" (Expr.var "cap.k") c7 (RunStep.eval_var B c6 "cap.k" (?nAX_g4681_0_0_5))) (RunStep.seq B factorial c47 c8 w c2_2 c11 c39 left (RunStep.seq B (Com.assign "cap.factorial" (Expr.var "factorial.value")) c46 w (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c2_2 c31 c38 (RunStep.assign B w "cap.factorial" (Expr.var "factorial.value") (Env.vars w "factorial.value") (RunStep.eval_var B w "factorial.value" (?nAX_g4681_0_0_6))) (RunStep.seq B c42 c45 (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c7_1 c2_2 c34 c37 (RunStep.assign B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "power.base" c33 c6_1 (RunStep.eval_add B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) c32 (Expr.lit ((1:Nat))) c5_1 ((1:Nat)) (RunStep.eval_mul B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) (Expr.mul (Expr.var "cap.k") (Expr.var "cap.H")) (Expr.var "cap.H") c4_1 c3_1 (RunStep.eval_mul B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) (Expr.var "cap.k") (Expr.var "cap.H") c2_1 c3_1 (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.k" ?_) (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.H" ?_) ?_) (RunStep.eval_var B (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) "cap.H" ?_) ?_) (RunStep.eval_lit B ((1:Nat)) (Env.setVar w "cap.factorial" (Env.vars w "factorial.value")) h1) ?_)) (RunStep.seq B (Com.assign "power.exponent" (Expr.var "cap.k")) c44 c7_1 c9_1 c2_2 c28 c36 (RunStep.assign B c7_1 "power.exponent" (Expr.var "cap.k") c8_1 (RunStep.eval_var B c7_1 "cap.k" ?_)) (RunStep.seq B power c43 c9_1 w_1 c2_2 c11 c35 left_1 (RunStep.assign B w_1 "cap.value" (Expr.mul (Expr.var "cap.factorial") (Expr.var "power.value")) c1_2 (RunStep.eval_mul B w_1 (Expr.var "cap.factorial") (Expr.var "power.value") (Env.vars w_1 "cap.factorial") (Env.vars w_1 "power.value") (RunStep.eval_var B w_1 "cap.factorial" ?_) (RunStep.eval_var B w_1 "power.value" (?nAX_g4681_0_0_7)) ?_))))))))) (?nAX_g4681_0_0_8)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4681_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4681_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hfactorial hpower
  all_goals simp_all [FieldsAgree,K,a,hc,Nat.mul_assoc]

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

theorem prepareCap_bounded_spec (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (fun σ => σ.vars "query.m"=m∧ σ.vars "query.n"=n∧
        σ.vars "cap.H"=2 ^ (2 * S)) prepareCap
      (fun _ τ => τ.vars "cap.value"=coordinateCap m n (2 ^ (2 * S))∧
        τ.vars "cap.H"=2 ^ (2 * S)∧ τ.vars "query.m"=m∧ τ.vars "query.n"=n)
      (48 * S + 90):=by
  exact (prepareCap_spec (2 ^ w) m n (2 ^ (2 * S)) (magnitude_fits m n S w hdim hw)).mono (by omega)

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

def sizeBound (m n M:ℕ):ℕ:=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * M.size)

def instructionBound (m n M:ℕ):ℕ:=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (sizeBound m n M)

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

namespace Lax109476Proofs.RamEquationData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def fields:List String:= ["system.m", "system.n"]
def arrays:List String:= ["system.A", "system.b"]

theorem data_frame {B z:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ z)
    {m n:ℕ} (P:Program ℤ m n) (hσ:Data P σ)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):Data P τ:=by
  rcases hσ with ⟨hA,hb,hm,hn⟩
  exact ⟨RamReadBody.represents_frame _ _ hA hr (ha _ (by simp [arrays])),
    RamReadBody.represents_frame _ _ hb hr (ha _ (by simp [arrays])),
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hm,
    (hr.frame_var _ (hf _ (by simp [fields]))).trans hn⟩

theorem data_setVar {m n:ℕ} (P:Program ℤ m n) (σ:Env) (v:String) (z:ℕ)
    (hv:v∉ fields) (hσ:Data P σ):Data P (σ.setVar v z):=by
  have hm:v ≠ "system.m" :=by intro h; subst v; simp [fields] at hv
  have hn:v ≠ "system.n" :=by intro h; subst v; simp [fields] at hv
  simpa [Data,Represents,arrs_setVar,vars_setVar,Ne.symm hm,Ne.symm hn] using hσ

theorem preserves_data (B:ℕ) {m n:ℕ} (P:Program ℤ m n) (c:Com)
    (hf:∀ a∈ fields,a∉ c.wvars)
    (ha:∀ a∈ arrays, ∀ s∈ RamCopy.suffixes,a ++ s∉ c.warrs):
    RamBisectionLoop.preserves B (Data P) c:=fun hr hσ => data_frame hr P hσ hf ha

end Lax109476Proofs.RamEquationData

end

section

namespace Lax109476Proofs.EquationQueryEntries

open Lax109476.LinearProgram
open IntegerPointRecovery RamStandardPointRecovery RationalArithmeticBounds

def slackEntry {m n:ℕ} (P:Program ℤ m n) (i:Fin m) (j:Fin (n + m)):ℚ:=
  if hj:j.val < n then (P.A i ⟨j.val,hj⟩:ℚ)
  else if j.val - n=i.val then 1 else 0

def entry {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + m)) (j:Fin (n + m)):ℚ:=
  if hi:i.val < m then slackEntry P ⟨i.val,hi⟩ j
  else -slackEntry P ⟨i.val - m,by omega⟩ j

def bound {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + m)):ℚ:=
  if hi:i.val < m then (P.b ⟨i.val,hi⟩:ℚ)
  else -(P.b ⟨i.val - m,by omega⟩:ℚ)

theorem slackEntry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin m) (j:Fin (n + m)):
    slackEntry P i j=(slackMatrix P i j:ℚ):=by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [slackEntry,slackMatrix,Fin.addCases_left,j.isLt]
  · have hj:¬n + j.val < n:=by omega
    have he:j.val=i.val↔ j=i:=Fin.ext_iff.symm
    simp [-Fin.natAdd_eq_addNat,slackEntry,slackMatrix,hj,he]

theorem entry_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + m)) (j:Fin (n + m)):
    entry P i j=(program (slackMatrix P) P.b).A i j:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have he:entry P (Fin.castAdd m i) j=(slackMatrix P i j:ℚ):=by
      simpa [entry,i.isLt] using slackEntry_eq P i j
    rw [he]
    change _=Fin.addCases (motive:=fun _:Fin (m + m) => Fin (n + m)→ ℚ)
      (fun i j => (slackMatrix P i j:ℚ)) (fun i j => -(slackMatrix P i j:ℚ)) (Fin.castAdd m i) j
    rw [Fin.addCases_left (motive:=fun _:Fin (m + m) => Fin (n + m)→ ℚ)]
  · have hi:¬m + i.val < m:=by omega
    have he:entry P (Fin.natAdd m i) j=-(slackMatrix P i j:ℚ):=by
      simpa [-Fin.natAdd_eq_addNat,entry,hi] using congrArg Neg.neg (slackEntry_eq P i j)
    rw [he]
    change _=Fin.addCases (motive:=fun _:Fin (m + m) => Fin (n + m)→ ℚ)
      (fun i j => (slackMatrix P i j:ℚ)) (fun i j => -(slackMatrix P i j:ℚ)) (Fin.natAdd m i) j
    rw [Fin.addCases_right (motive:=fun _:Fin (m + m) => Fin (n + m)→ ℚ)]

theorem bound_eq {m n:ℕ} (P:Program ℤ m n) (i:Fin (m + m)):
    bound P i=(program (slackMatrix P) P.b).b i:=by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [bound,program,LexicographicMinima.equationProgram,i.isLt]
  · have hi:¬m + i.val < m:=by omega
    simp [-Fin.natAdd_eq_addNat,bound,program,LexicographicMinima.equationProgram,hi]

theorem entry_height {m n:ℕ} (P:Program ℤ m n) (M:ℕ) (hM:1≤ M)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (i:Fin (m + m)) (j:Fin (n + m)):Height (entry P i j) M:=by
  have hs:∀ r:Fin m,Height (slackEntry P r j) M:=by
    intro r
    unfold slackEntry
    split_ifs with hj he
    · exact ⟨by simpa using hA r ⟨j.val,hj⟩,by simpa using hM⟩
    · exact height_nat 1 M hM hM
    · exact height_mono 0 height_zero (by omega)
  unfold entry
  split_ifs
  · exact hs _
  · exact height_neg _ _ (hs _)

theorem bound_height {m n:ℕ} (P:Program ℤ m n) (M:ℕ) (hM:1≤ M)
    (hb:∀ i, (P.b i).natAbs≤ M) (i:Fin (m + m)):Height (bound P i) M:=by
  have hs:∀ r:Fin m,Height (P.b r:ℚ) M:=fun r =>
    ⟨by simpa using hb r,by simpa using hM⟩
  unfold bound
  split_ifs
  · exact hs _
  · exact height_neg _ _ (hs _)

end Lax109476Proofs.EquationQueryEntries

end

section

namespace Lax109476Proofs.RamEquationSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries IntegerEncoding

def slackFields:List String:= ["system.m", "system.n", "query.row", "query.baseRow", "query.col"]

set_option maxHeartbeats 0 in
theorem selectSlack_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin m) (j:Fin (n + m))
    (hM:1≤ M) (hMB:M < B) (hB:m * n + m + n + 4 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.baseRow"=i.val∧ σ.vars "query.col"=j.val)
      selectSlack (fun _ τ => FractionOutput (slackEntry P i j) τ) 32:=by
  have h1:1 < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hnB:n < B:=by omega
  have hmB:m < B:=by omega
  have hzero:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  have hone:=RamPadSelector.constantFraction_spec B 1 h1 h1
  rintro σ ⟨⟨hσA,hσb,hσm,hσn⟩,hσi,hσj⟩
  by_cases hj:j.val < n
  · let jj:Fin n:= ⟨j.val,hj⟩
    let index:=i.val * n + j.val
    have hindex:index < (RamMatrixStorage.flatten (rationalProgram P).A).length:=by
      simpa [RamMatrixStorage.flatten,index,jj] using RamMatrixStorage.row_index_lt i jj
    have hindexB:index < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hindex:index < m * n).trans
      (by omega)
    have hmulB:i.val * n < B:=by dsimp only [index] at hindexB; omega
    have he:(RamMatrixStorage.flatten (rationalProgram P).A)[index]=(P.A i jj:ℚ):=
      RamMatrixStorage.flatten_entry (rationalProgram P).A i jj
    have hq:Height (P.A i jj:ℚ) M:= ⟨by simpa using hA i jj,by simpa using hM⟩
    have hload:=spec_with_fields slackFields
      (RamArrayResult.load_spec B "system.A" (RamMatrixStorage.flatten (rationalProgram P).A) index
        hindex h1 hindexB (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB))
      (by intro a ha; simp [slackFields] at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide) (by rfl)
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "system.n"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@slackEntry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectSlack σ σ' ((32:Nat))) (c3 σ'); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=Nat.mul (Env.vars σ "query.baseRow") (Env.vars σ "system.n"); let c7:Nat:=c5 c6 (Env.vars σ "query.col"); let c8:Env:=Env.setVar σ "vec.i" c7; let c9:Env→ Nat→ Prop:=Run B (RamArrayResult.load "system.A") c8; let c10:List Rat:= @RamMatrixStorage.flatten m n (@Program.A Rat m n (@rationalProgram m n P)); let c11:Env→ Prop:=FractionOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c10 index hindex); let c12:Env→ Prop:=FieldsAgree slackFields c8; let c13:String→ List Nat:=Env.arrs c8; let c14:Env→ Prop:=fun (σ':Env) => And (c9 σ' ((15:Nat))) (And (c11 σ') (And (c12 σ') (@Eq (String→ List Nat) (Env.arrs σ') c13))); let c15:Env→ Prop:=Represents "system.A" c10; let c16:Nat→ Nat:=c5 ((1:Nat)); let c17:Nat→ Nat:=c5 (c16 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "system.n")))); let c18:Expr:=Expr.add (Expr.mul (Expr.var "query.baseRow") (Expr.var "system.n")) (Expr.var "query.col"); let c19:Nat:=c16 (Expr.size c18); let c20:Nat:=c5 c19 ((15:Nat)); let c21:Com:=Com.assign "vec.i" c18; let c22:Com:=Com.seq c21 (RamArrayResult.load "system.A"); let c23:Cond:=Cond.eq (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow"); let c24:Com:=Com.ite c23 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c25:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "query.col") (Env.vars σ "system.n"); let c26:Prop:= @Eq Nat c25 (Env.vars σ "query.baseRow"); let c27:Prop:=Not c26; let c28:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c29:Nat→ Env:=Env.setVar c28 "rat.n"; let c30:Env:=c29 ((1:Nat)); let c31:Env:=Env.setVar c30 "rat.d" ((1:Nat)); let c32:Nat→ Nat:=c5 (c16 (Cond.size c23)); let c33:Nat:=c16 (Expr.size (Expr.lit ((0:Nat)))); let c34:Nat→ Nat:=c5 c33; let c35:Nat:=c16 (Expr.size (Expr.lit ((1:Nat)))); let c36:Nat:=c5 c35 c35; let c37:Nat:=c34 c36; let c38:Nat:=c32 c37; let c39:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c40:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c41:Env:=c29 ((0:Nat)); let c42:Env:=Env.setVar c41 "rat.d" ((1:Nat)); let c43:Nat:=c34 c35; let c44:Nat:=c34 c43; let c45:Nat:=c32 c44; let c46:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c14 (fun (x:@Exists Env c14) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (c15 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") index)) (RamArrayResult.load "system.A") (fun (σ_1 τ:Env) => And (c11 τ) (And (FieldsAgree slackFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((15:Nat)) hload c8 ?_) fun (w:Env) (h:And (c9 w ((15:Nat))) (And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)))) => let c0_1:Prop:=c9 w ((15:Nat)); let c1_1:Prop:=And (c11 w) (And (c12 w) (@Eq (String→ List Nat) (Env.arrs w) c13)); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c4 w (@And.intro (Run B selectSlack σ w ((32:Nat))) (c3 w) (RunStep.mono B selectSlack σ w (c17 c20) ((32:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c22 c24 σ w c20 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_1)) hcase) (RunStep.seq B c21 (RamArrayResult.load "system.A") σ c8 w c19 ((15:Nat)) (RunStep.assign B σ "vec.i" c18 c7 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.baseRow") (Expr.var "system.n")) (Expr.var "query.col") c6 (Env.vars σ "query.col") (RunStep.eval_mul B σ (Expr.var "query.baseRow") (Expr.var "system.n") (Env.vars σ "query.baseRow") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_0_0_2)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_3)) ?_) (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_4)) ?_)) left)) (?nAX_g5131_0_0_5)) ?_)) fun (hcase:c1) => @Or.casesOn c26 c27 (fun (x:Or c26 c27) => @Exists Env c4) (Classical.em c26) (fun (hcase_1:c26) => @Exists.intro Env c4 c31 (@And.intro (Run B selectSlack σ c31 ((32:Nat))) (c3 c31) (RunStep.mono B selectSlack σ c31 (c17 c38) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c22 c24 σ c31 c38 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_6)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_7)) hcase) (RunStep.ite_true B c23 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c31 c37 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow") c25 (Env.vars σ "query.baseRow") (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_8)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_9)) (?nAX_g5131_0_0_10)) (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_0_0_11)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c39 c40) σ c28 c31 c33 c36 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5131_0_0_12))) (RunStep.seq B c39 c40 c28 c30 c31 c35 c35 (RunStep.assign B c28 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c28 h1)) (RunStep.assign B c30 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c30 h1)))))) (?nAX_g5131_0_0_13)) ?_)) fun (hcase_1:c27) => @Exists.intro Env c4 c42 (@And.intro (Run B selectSlack σ c42 ((32:Nat))) (c3 c42) (RunStep.mono B selectSlack σ c42 (c17 c45) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c22 c24 σ c42 c45 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_14)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_15)) hcase) (RunStep.ite_false B c23 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ c42 c44 (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow") c25 (Env.vars σ "query.baseRow") (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_0_0_16)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_0_0_17)) (?nAX_g5131_0_0_18)) (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_0_0_19)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c46 c40) σ c28 c42 c33 c43 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5131_0_0_20))) (RunStep.seq B c46 c40 c28 c41 c42 c33 c35 (RunStep.assign B c28 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c28 (?nAX_g5131_0_0_21))) (RunStep.assign B c41 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c41 h1)))))) (?nAX_g5131_0_0_22)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5131_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hload
    all_goals simp_all [slackFields,FieldsAgree,slackEntry,index,jj,Represents]
    all_goals omega
  · have hsub:j.val - n < B:=(Nat.sub_le _ _).trans_lt hjB
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.col") (Env.vars σ "system.n"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@slackEntry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectSlack σ σ' ((32:Nat))) (c3 σ'); let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:=Nat.mul (Env.vars σ "query.baseRow") (Env.vars σ "system.n"); let c7:Nat:=c5 c6 (Env.vars σ "query.col"); let c8:Env:=Env.setVar σ "vec.i" c7; let c9:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "system.A"; let c10:String:=c9 ".s"; let c11:Nat:=Env.vars c8 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c8 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c8 "left.s" c12; let c14:String:=c9 ".n"; let c15:Nat:=Env.vars c13 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c13 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c13 "left.n" c16; let c18:String:=c9 ".d"; let c19:Nat:=Env.vars c17 "vec.i"; let c20:Nat:= @List.getD Nat (Env.arrs c17 c18) c19 ((0:Nat)); let c21:Env:=Env.setVar c17 "left.d" c20; let c22:Nat:=Env.vars c21 "left.s"; let c23:Env:=Env.setVar c21 "rat.s" c22; let c24:Nat:=Env.vars c23 "left.n"; let c25:Env:=Env.setVar c23 "rat.n" c24; let c26:Nat:=Env.vars c25 "left.d"; let c27:Env:=Env.setVar c25 "rat.d" c26; let c28:Nat→ Nat:=c5 ((1:Nat)); let c29:Nat→ Nat:=c5 (c28 (Cond.size (Cond.lt (Expr.var "query.col") (Expr.var "system.n")))); let c30:Expr:=Expr.add (Expr.mul (Expr.var "query.baseRow") (Expr.var "system.n")) (Expr.var "query.col"); let c31:Nat:=c28 (Expr.size c30); let c32:Expr:=Expr.get c10 (Expr.var "vec.i"); let c33:Nat:=c28 (Expr.size c32); let c34:Expr:=Expr.get c14 (Expr.var "vec.i"); let c35:Nat:=c28 (Expr.size c34); let c36:Expr:=Expr.get c18 (Expr.var "vec.i"); let c37:Nat:=c28 (Expr.size c36); let c38:Nat:=c5 c35 c37; let c39:Nat:=c5 c33 c38; let c40:Nat:=c28 (Expr.size (Expr.var "left.s")); let c41:Nat:=c28 (Expr.size (Expr.var "left.n")); let c42:Nat:=c28 (Expr.size (Expr.var "left.d")); let c43:Nat:=c5 c41 c42; let c44:Nat:=c5 c40 c43; let c45:Nat:=c5 c39 c44; let c46:Nat:=c5 c31 c45; let c47:Com:=Com.assign "vec.i" c30; let c48:Com:=Com.seq c47 (RamArrayResult.load "system.A"); let c49:Cond:=Cond.eq (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow"); let c50:Com:=Com.ite c49 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))); let c51:Com:=Com.assign "left.n" c34; let c52:Com:=Com.assign "left.d" c36; let c53:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "query.col") (Env.vars σ "system.n"); let c54:Prop:= @Eq Nat c53 (Env.vars σ "query.baseRow"); let c55:Prop:=Not c54; let c56:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((1:Nat))) σ; let c57:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat))); let c58:Env→ Prop:=fun (σ':Env) => And (c56 σ' ((6:Nat))) (c57 σ'); let c59:Nat:=c5 (c28 (Cond.size c49)) ((6:Nat)); let c60:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c61:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c62:Env→ Prop:=fun (σ':Env) => And (c60 σ' ((6:Nat))) (c61 σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 c27 (@And.intro (Run B selectSlack σ c27 ((32:Nat))) (c3 c27) (RunStep.mono B selectSlack σ c27 (c29 c46) ((32:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c48 c50 σ c27 c46 (RunStep.cond_lt_true B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_0)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_1)) hcase) (RunStep.seq B c47 (RamArrayResult.load "system.A") σ c8 c27 c31 c45 (RunStep.assign B σ "vec.i" c30 c7 (RunStep.eval_add B σ (Expr.mul (Expr.var "query.baseRow") (Expr.var "system.n")) (Expr.var "query.col") c6 (Env.vars σ "query.col") (RunStep.eval_mul B σ (Expr.var "query.baseRow") (Expr.var "system.n") (Env.vars σ "query.baseRow") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_1_0_2)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_3)) (?nAX_g5131_1_0_4)) (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_5)) (?nAX_g5131_1_0_6))) (RunStep.seq B (loadLeft "system.A") RamCopy.leftToResult c8 c21 c27 c39 c44 (RunStep.seq B (Com.assign "left.s" c32) (Com.seq c51 c52) c8 c13 c21 c33 c38 (RunStep.assign B c8 "left.s" c32 c12 (RunStep.eval_get B c8 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c8 "vec.i" (?nAX_g5131_1_0_7)) (?nAX_g5131_1_0_8) (?nAX_g5131_1_0_9))) (RunStep.seq B c51 c52 c13 c17 c21 c35 c37 (RunStep.assign B c13 "left.n" c34 c16 (RunStep.eval_get B c13 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c13 "vec.i" (?nAX_g5131_1_0_10)) (?nAX_g5131_1_0_11) (?nAX_g5131_1_0_12))) (RunStep.assign B c17 "left.d" c36 c20 (RunStep.eval_get B c17 c18 (Expr.var "vec.i") c19 (RunStep.eval_var B c17 "vec.i" (?nAX_g5131_1_0_13)) (?nAX_g5131_1_0_14) (?nAX_g5131_1_0_15))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c21 c23 c27 c40 c43 (RunStep.assign B c21 "rat.s" (Expr.var "left.s") c22 (RunStep.eval_var B c21 "left.s" (?nAX_g5131_1_0_16))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c23 c25 c27 c41 c42 (RunStep.assign B c23 "rat.n" (Expr.var "left.n") c24 (RunStep.eval_var B c23 "left.n" (?nAX_g5131_1_0_17))) (RunStep.assign B c25 "rat.d" (Expr.var "left.d") c26 (RunStep.eval_var B c25 "left.d" (?nAX_g5131_1_0_18)))))))) (?nAX_g5131_1_0_19)) ?_)) fun (hcase:c1) => @Or.casesOn c54 c55 (fun (x:Or c54 c55) => @Exists Env c4) (Classical.em c54) (fun (hcase_1:c54) => @Exists.casesOn Env c58 (fun (x:@Exists Env c58) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((1:Nat))) (fun (x τ:Env) => c57 τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (c56 w ((6:Nat))) (c57 w)) => let c0_1:Prop:=c56 w ((6:Nat)); @And.casesOn c0_1 (c57 w) (fun (x:And c0_1 (c57 w)) => @Exists Env c4) h fun (left:c0_1) (right:c57 w) => @Exists.intro Env c4 w (@And.intro (Run B selectSlack σ w ((32:Nat))) (c3 w) (RunStep.mono B selectSlack σ w (c29 c59) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c48 c50 σ w c59 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_20)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_21)) hcase) (RunStep.ite_true B c49 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow") c53 (Env.vars σ "query.baseRow") (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_22)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_23)) (?nAX_g5131_1_0_24)) (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_1_0_25)) hcase_1) left)) (?nAX_g5131_1_0_26)) ?_)) fun (hcase_1:c55) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => @Exists Env c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => @Exists Env c4) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectSlack σ w ((32:Nat))) (c3 w) (RunStep.mono B selectSlack σ w (c29 c59) ((32:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.col") (Expr.var "system.n")) c48 c50 σ w c59 (RunStep.cond_lt_false B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_27)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_28)) hcase) (RunStep.ite_false B c49 (RamPadSelector.constantFraction ((1:Nat))) (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "query.col") (Expr.var "system.n")) (Expr.var "query.baseRow") c53 (Env.vars σ "query.baseRow") (RunStep.eval_sub B σ (Expr.var "query.col") (Expr.var "system.n") (Env.vars σ "query.col") (Env.vars σ "system.n") (RunStep.eval_var B σ "query.col" (?nAX_g5131_1_0_29)) (RunStep.eval_var B σ "system.n" (?nAX_g5131_1_0_30)) (?nAX_g5131_1_0_31)) (RunStep.eval_var B σ "query.baseRow" (?nAX_g5131_1_0_32)) hcase_1) left)) (?nAX_g5131_1_0_33)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5131_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5131_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hzero hone
    all_goals simp_all [slackEntry,Represents]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

theorem applyRowSign_spec (B m row:ℕ) (q:ℚ) (h1:1 < B) (hm:m < B) (hr:row < B):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "system.m"=m∧ σ.vars "query.row"=row)
      applyRowSign (fun _ τ => FractionOutput (if row < m then q else -q) τ) 8:=by
  have hn:=RamResultNegation.negateResult_spec B q h1
  rintro σ ⟨hσq,hσm,hσrow⟩
  by_cases hrow:row < m
  · (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "system.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@ite Rat (Nat.lt row m) (Nat.decLt row m) q (@Neg.neg Rat Rat.instNeg q)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B applyRowSign σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (c6 ((1:Nat)) (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "system.m")))); let c8:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult σ σ' ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 σ (@And.intro (Run B applyRowSign σ σ ((8:Nat))) (c3 σ) (RunStep.mono B applyRowSign σ σ (c7 ((1:Nat))) ((8:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) Com.skip RamResultNegation.negateResult σ σ ((1:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5135_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5135_0_0_1)) hcase) (RunStep.skip B σ)) (?nAX_g5135_0_0_2)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c5) (RunStep.use B (FractionOutput q) RamResultNegation.negateResult (fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) ((4:Nat)) hn σ ?_) fun (w:Env) (h:And (Run B RamResultNegation.negateResult σ w ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => let c0_1:Prop:=Run B RamResultNegation.negateResult σ w ((4:Nat)); @And.casesOn c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w) (fun (x:And c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => c5) h fun (left:c0_1) (right:FractionOutput (@Neg.neg Rat Rat.instNeg q) w) => @Exists.intro Env c4 w (@And.intro (Run B applyRowSign σ w ((8:Nat))) (c3 w) (RunStep.mono B applyRowSign σ w (c7 ((4:Nat))) ((8:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) Com.skip RamResultNegation.negateResult σ w ((4:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5135_0_0_3)) (RunStep.eval_var B σ "system.m" (?nAX_g5135_0_0_4)) hcase) left) (?nAX_g5135_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5135_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hn
    all_goals simp_all
  · (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "system.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@ite Rat (Nat.lt row m) (Nat.decLt row m) q (@Neg.neg Rat Rat.instNeg q)); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B applyRowSign σ σ' ((8:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (c6 ((1:Nat)) (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "system.m")))); let c8:Env→ Prop:=fun (σ':Env) => And (Run B RamResultNegation.negateResult σ σ' ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c4 σ (@And.intro (Run B applyRowSign σ σ ((8:Nat))) (c3 σ) (RunStep.mono B applyRowSign σ σ (c7 ((1:Nat))) ((8:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) Com.skip RamResultNegation.negateResult σ σ ((1:Nat)) (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5135_1_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5135_1_0_1)) hcase) (RunStep.skip B σ)) (?nAX_g5135_1_0_2)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c8 (fun (x:@Exists Env c8) => c5) (RunStep.use B (FractionOutput q) RamResultNegation.negateResult (fun (x τ:Env) => FractionOutput (@Neg.neg Rat Rat.instNeg q) τ) ((4:Nat)) hn σ ?_) fun (w:Env) (h:And (Run B RamResultNegation.negateResult σ w ((4:Nat))) (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => let c0_1:Prop:=Run B RamResultNegation.negateResult σ w ((4:Nat)); @And.casesOn c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w) (fun (x:And c0_1 (FractionOutput (@Neg.neg Rat Rat.instNeg q) w)) => c5) h fun (left:c0_1) (right:FractionOutput (@Neg.neg Rat Rat.instNeg q) w) => @Exists.intro Env c4 w (@And.intro (Run B applyRowSign σ w ((8:Nat))) (c3 w) (RunStep.mono B applyRowSign σ w (c7 ((4:Nat))) ((8:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) Com.skip RamResultNegation.negateResult σ w ((4:Nat)) (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5135_1_0_3)) (RunStep.eval_var B σ "system.m" (?nAX_g5135_1_0_4)) hcase) left) (?nAX_g5135_1_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5135_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5135_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hn
    all_goals simp_all
    all_goals split_ifs <;> (try simp_all) <;> omega

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + m)) (j:Fin (n + m))
    (hM:1≤ M) (hMB:M < B) (hB:(m + m) * (n + m) + m + n + 4 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val∧ σ.vars "query.col"=j.val)
      selectEntry (fun _ τ => Data P τ∧ FractionOutput (entry P i j) τ) 48:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hmpos:0 < m:=by have hi:=i.isLt; omega
  have hrows:m + m≤ (m + m) * (n + m):=Nat.le_mul_of_pos_right _ (by omega)
  have hiB:i.val < B:=(i.isLt.trans_le hrows).trans (by omega)
  have hjB:j.val < B:=j.isLt.trans (by omega)
  have hmn:m * n≤ (m + m) * (n + m):=Nat.mul_le_mul (by omega) (by omega)
  let r:Fin m:=if hi:i.val < m then ⟨i.val,hi⟩ else ⟨i.val - m,by omega⟩
  have hrB:r.val < B:=r.isLt.trans hm
  have hprepare:Spec B (fun σ => σ.vars "system.m"=m∧ σ.vars "query.row"=i.val)
      prepareRow (fun _ τ => τ.vars "query.baseRow"=r.val) 8:=by
    rintro σ ⟨hσm,hσrow⟩
    have hsub:i.val - m < B:=(Nat.sub_le _ _).trans_lt hiB
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "system.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "query.baseRow") (@Fin.val m r)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B prepareRow σ σ' ((8:Nat))) (c2 σ'); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat→ Nat:=c4 (c5 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "system.m")))); let c7:Nat:=c5 (Expr.size (Expr.var "query.row")); let c8:Com:=Com.assign "query.baseRow" (Expr.sub (Expr.var "query.row") (Expr.var "system.m")); let c9:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "query.row") (Env.vars σ "system.m"); let c10:Env:=Env.setVar σ "query.baseRow" c9; let c11:Nat:=c5 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "system.m"))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) (@And.intro (Run B prepareRow σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) ((8:Nat))) (c2 (Env.setVar σ "query.baseRow" (Env.vars σ "query.row"))) (RunStep.mono B prepareRow σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) (c6 c7) ((8:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) (Com.assign "query.baseRow" (Expr.var "query.row")) c8 σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) c7 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5136_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5136_0_0_1)) hcase) (RunStep.assign B σ "query.baseRow" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5136_0_0_2)))) (?nAX_g5136_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c3 c10 (@And.intro (Run B prepareRow σ c10 ((8:Nat))) (c2 c10) (RunStep.mono B prepareRow σ c10 (c6 c11) ((8:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) (Com.assign "query.baseRow" (Expr.var "query.row")) c8 σ c10 c11 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5136_0_0_4)) (RunStep.eval_var B σ "system.m" (?nAX_g5136_0_0_5)) hcase) (RunStep.assign B σ "query.baseRow" (Expr.sub (Expr.var "query.row") (Expr.var "system.m")) c9 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5136_0_0_6)) (RunStep.eval_var B σ "system.m" (?nAX_g5136_0_0_7)) (?nAX_g5136_0_0_8)))) (?nAX_g5136_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5136_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5136_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [r]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  rintro σ ⟨hσData,hσrow,hσcol⟩
  obtain ⟨τ,hr₁,hτr⟩:=hprepare σ ⟨hσData.2.2.1,hσrow⟩
  have hτData:=data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; change a ++ s∉ ([]:List String); simp)
  have hτcol:=(hr₁.frame_var "query.col" (by decide)).trans hσcol
  obtain ⟨υ,hr₂,hυq⟩:=selectSlack_spec B M m n P r j hM hMB (by omega) hA τ ⟨hτData,hτr,hτcol⟩
  have hυm:=(hr₂.frame_var "system.m" (by decide)).trans hτData.2.2.1
  have hυrow:=(hr₂.frame_var "query.row" (by decide)).trans ((hr₁.frame_var _ (by decide)).trans hσrow)
  obtain ⟨ρ,hr₃,hρq⟩:=applyRowSign_spec B m i.val (slackEntry P r j) h1 hm hiB υ ⟨hυq,hυm,hυrow⟩
  have hr:=hr₁.seq (hr₂.seq hr₃)
  refine ⟨ρ,hr,data_frame hr P hσData ?_ ?_, ?_⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp
  · by_cases hi:i.val < m <;> simpa [entry,r,hi] using hρq

end Lax109476Proofs.RamEquationSelector

end

section

namespace Lax109476Proofs.RamEquationMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries RamEllipsoidStep

def values {m n:ℕ} (P:Program ℤ m n):Fin ((m + m) * (n + m))→ ℚ:=
  fun i => entry P i.divNat i.modNat

set_option maxHeartbeats 0 in
theorem selectCoordinate_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin ((m + m) * (n + m)))
    (hM:1≤ M) (hMB:M < B) (hB:(m + m) * (n + m) + m + n + 4 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=(m + m) * (n + m))
      selectCoordinate (fun _ τ => Data P τ∧ FractionOutput (values P i) τ) 62:=by
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hsum:n + m < B:=by omega
  have hdiv:i.val / (n + m) < B:=(Nat.div_le_self _ _).trans_lt hiB
  have hmul:(i.val / (n + m)) * (n + m) < B:=(Nat.div_mul_le_self _ _).trans_lt hiB
  have hsub:i.val - (i.val / (n + m)) * (n + m) < B:=(Nat.sub_le _ _).trans_lt hiB
  have hmod:i.val - (i.val / (n + m)) * (n + m)=i.val % (n + m):=by
    simpa [Nat.mul_comm] using (Nat.mod_eq_sub_mul_div (x:=i.val) (k:=n + m)).symm
  have hselector:=RamEquationSelector.selectEntry_spec B M m n P i.divNat i.modNat hM hMB hB hA
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=(m + m) * (n + m))
      selectCoordinate (fun _ τ => FractionOutput (values P i) τ) 62:=by
    rintro σ ⟨⟨hσA,hσb,hσm,hσn⟩,hσi,hσcount⟩
    (expose_names;
      (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "system.n") (Env.vars σ "system.m"); let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "build.i") c1; let c3:Env:=Env.setVar σ "query.row" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "build.i"; let c6:Nat:=c4 "query.row"; let c7:Nat:=c4 "system.n"; let c8:Nat:=c4 "system.m"; let c9:Nat:=c0 c7 c8; let c10:Nat:=Nat.mul c6 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c5 c10; let c12:Env:=Env.setVar c3 "query.col" c11; let c13:Env→ Nat→ Prop:=Run B RamEquationSelector.selectEntry c12; let c14:Nat:=c0 m m; let c15:Nat:=c0 n m; let c16:Fin c14:= @Fin.divNat c14 c15 i; let c17:Fin c15:= @Fin.modNat c14 c15 i; let c18:Env→ Prop:=FractionOutput (@entry m n P c16 c17); let c19:Env→ Prop:=fun (σ':Env) => And (c13 σ' ((48:Nat))) (And (@Data m n P σ') (c18 σ')); let c20:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@values m n P i) τ) σ; let c21:Env→ Prop:=fun (σ':Env) => And (Run B selectCoordinate σ σ' ((62:Nat))) (c20 σ'); let c22:Prop:= @Exists Env c21; let c23:Nat:= @Fin.val c14 c16; let c24:Nat:= @Fin.val c15 c17; let c25:String→ Nat:=Env.vars c12; let c26:Nat→ Nat:=c0 ((1:Nat)); let c27:Expr:=Expr.div (Expr.var "build.i") (Expr.add (Expr.var "system.n") (Expr.var "system.m")); let c28:Nat:=c26 (Expr.size c27); let c29:Expr:=Expr.mul (Expr.var "query.row") (Expr.add (Expr.var "system.n") (Expr.var "system.m")); let c30:Expr:=Expr.sub (Expr.var "build.i") c29; let c31:Nat:=c26 (Expr.size c30); let c32:Nat:=c0 c31 ((48:Nat)); let c33:Com:=Com.assign "query.col" c30; @Exists.casesOn Env c19 (fun (x:@Exists Env c19) => c22) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (And (@Eq Nat (Env.vars σ_1 "query.row") c23) (@Eq Nat (Env.vars σ_1 "query.col") c24))) RamEquationSelector.selectEntry (fun (x τ:Env) => And (@Data m n P τ) (c18 τ)) ((48:Nat)) hselector c12 ?_) fun (w:Env) (h:And (c13 w ((48:Nat))) (And (@Data m n P w) (c18 w))) => let c0_1:Prop:=c13 w ((48:Nat)); let c1_1:Prop:=And (@Data m n P w) (c18 w); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c22) h fun (left:c0_1) (right:c1_1) => @Exists.intro Env c21 w (@And.intro (Run B selectCoordinate σ w ((62:Nat))) (c20 w) (RunStep.mono B selectCoordinate σ w (c0 c28 c32) ((62:Nat)) (RunStep.seq B (Com.assign "query.row" c27) (Com.seq c33 RamEquationSelector.selectEntry) σ c3 w c28 c32 (RunStep.assign B σ "query.row" c27 c2 (RunStep.eval_div B σ (Expr.var "build.i") (Expr.add (Expr.var "system.n") (Expr.var "system.m")) (Env.vars σ "build.i") c1 (RunStep.eval_var B σ "build.i" (?nAX_g5139_0_0_0)) (RunStep.eval_add B σ (Expr.var "system.n") (Expr.var "system.m") (Env.vars σ "system.n") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.n" (?nAX_g5139_0_0_1)) (RunStep.eval_var B σ "system.m" (?nAX_g5139_0_0_2)) (?nAX_g5139_0_0_3)) ?_)) (RunStep.seq B c33 RamEquationSelector.selectEntry c3 c12 w c31 ((48:Nat)) (RunStep.assign B c3 "query.col" c30 c11 (RunStep.eval_sub B c3 (Expr.var "build.i") c29 c5 c10 (RunStep.eval_var B c3 "build.i" (?nAX_g5139_0_0_4)) (RunStep.eval_mul B c3 (Expr.var "query.row") (Expr.add (Expr.var "system.n") (Expr.var "system.m")) c6 c9 (RunStep.eval_var B c3 "query.row" ?_) (RunStep.eval_add B c3 (Expr.var "system.n") (Expr.var "system.m") c7 c8 (RunStep.eval_var B c3 "system.n" (?nAX_g5139_0_0_5)) (RunStep.eval_var B c3 "system.m" (?nAX_g5139_0_0_6)) (?nAX_g5139_0_0_7)) ?_) (?nAX_g5139_0_0_8))) left)) (?nAX_g5139_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5139_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5139_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hselector
    all_goals simp_all [values,Fin.divNat,Fin.modNat,Data,Represents,arrs_setVar]
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

set_option maxHeartbeats 0 in
theorem matrix_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hB:(m + m) * (n + m) + m + n + 4 < B)
    (hA:∀ r s, (P.A r s).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ Extents "point.A" ((m + m) * (n + m)) σ) matrix
      (fun _ τ => Data P τ∧ Represents "point.A"
        (RamMatrixStorage.flatten (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).A) τ)
      (118 * ((m + m) * (n + m)) + 34):=by
  let N:=(m + m) * (n + m)
  have h1:1 < B:=by omega
  have hNB:N < B:=by dsimp only [N]; omega
  have hrowsB:m + m < B:=by
    by_cases hm:m=0
    · simp [hm]; omega
    · exact (Nat.le_mul_of_pos_right (m + m) (by omega:0 < n + m)).trans_lt hNB
  have hbuild:=RamBuildVector.build_spec B M N 62 "point.A" (values P) selectCoordinate (Data P)
    h1 hNB hMB (fun i => entry_height P M hM hA i.divNat i.modNat)
    (selectCoordinate_spec B M m n P · hM hMB hB hA) (by decide) (by decide)
    (by intro s hs; change "point.A" ++ s∉ ([]:List String); simp)
    (preserves_data B P (storeReduced "point.A")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P (RamZeroArray.zeroRationalArray "point.A")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.n" z (by decide) h)
  have hvalues:List.ofFn (values P)=RamMatrixStorage.flatten
      (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).A:=by
    congr 1
    funext i
    exact entry_eq P i.divNat i.modNat
  have hmeta:Spec B (fun σ => σ.vars "system.m"=m∧ σ.vars "system.n"=n) prepare
      (fun _ τ => τ.vars "build.count"=N) 8:=by
    rintro σ ⟨hm,hn⟩
    (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "build.count") N) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 (Env.vars σ "system.m") (Env.vars σ "system.m"); let c3:Nat:=c1 (Env.vars σ "system.n") (Env.vars σ "system.m"); let c4:Nat:=Nat.mul c2 c3; let c5:Env:=Env.setVar σ "build.count" c4; let c6:Expr:=Expr.mul (Expr.add (Expr.var "system.m") (Expr.var "system.m")) (Expr.add (Expr.var "system.n") (Expr.var "system.m")); @Exists.intro Env (fun (σ':Env) => And (Run B prepare σ σ' ((8:Nat))) (c0 σ')) c5 (@And.intro (Run B prepare σ c5 ((8:Nat))) (c0 c5) (RunStep.mono B prepare σ c5 (c1 ((1:Nat)) (Expr.size c6)) ((8:Nat)) (RunStep.assign B σ "build.count" c6 c4 (RunStep.eval_mul B σ (Expr.add (Expr.var "system.m") (Expr.var "system.m")) (Expr.add (Expr.var "system.n") (Expr.var "system.m")) c2 c3 (RunStep.eval_add B σ (Expr.var "system.m") (Expr.var "system.m") (Env.vars σ "system.m") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.m" (?nAX_g5142_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5142_0_0_1)) (?nAX_g5142_0_0_2)) (RunStep.eval_add B σ (Expr.var "system.n") (Expr.var "system.m") (Env.vars σ "system.n") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.n" (?nAX_g5142_0_0_3)) (RunStep.eval_var B σ "system.m" (?nAX_g5142_0_0_4)) (?nAX_g5142_0_0_5)) ?_)) (?nAX_g5142_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5142_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5142_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ ⟨hσData.2.2.1,hσData.2.2.2⟩
  have hτData:=data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs,prepare])
  obtain ⟨υ,hr₂,hυData,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτData,RamAdvanceState.extents_of_run hr₁ "point.A" N hσtarget,hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυData, ?_⟩
  · dsimp only [N]; omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamEquationMatrix

end

section

namespace Lax109476Proofs.RamEquationBoundSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries IntegerEncoding

set_option maxHeartbeats 0 in
theorem selectBound_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + m))
    (hM:1≤ M) (hMB:M < B) (hB:m + m + n + 4 < B)
    (hb:∀ r, (P.b r).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "query.row"=i.val)
      selectBound (fun _ τ => Data P τ∧ FractionOutput (bound P i) τ) 33:=by
  have h1:1 < B:=by omega
  have hm:m < B:=by omega
  have hiB:i.val < B:=i.isLt.trans (by omega)
  let r:Fin m:=if hi:i.val < m then ⟨i.val,hi⟩ else ⟨i.val - m,by omega⟩
  have hrB:r.val < B:=r.isLt.trans hm
  have hq:Height (P.b r:ℚ) M:= ⟨by simpa using hb r,by simpa using hM⟩
  have hprepare:Spec B (fun σ => σ.vars "system.m"=m∧ σ.vars "query.row"=i.val)
      RamEquationSelector.prepareRow (fun _ τ => τ.vars "query.baseRow"=r.val) 8:=by
    rintro σ ⟨hσm,hσrow⟩
    have hsub:i.val - m < B:=(Nat.sub_le _ _).trans_lt hiB
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "query.row") (Env.vars σ "system.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "query.baseRow") (@Fin.val m r)) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B RamEquationSelector.prepareRow σ σ' ((8:Nat))) (c2 σ'); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat→ Nat:=c4 (c5 (Cond.size (Cond.lt (Expr.var "query.row") (Expr.var "system.m")))); let c7:Nat:=c5 (Expr.size (Expr.var "query.row")); let c8:Com:=Com.assign "query.baseRow" (Expr.sub (Expr.var "query.row") (Expr.var "system.m")); let c9:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "query.row") (Env.vars σ "system.m"); let c10:Env:=Env.setVar σ "query.baseRow" c9; let c11:Nat:=c5 (Expr.size (Expr.sub (Expr.var "query.row") (Expr.var "system.m"))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) (@And.intro (Run B RamEquationSelector.prepareRow σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) ((8:Nat))) (c2 (Env.setVar σ "query.baseRow" (Env.vars σ "query.row"))) (RunStep.mono B RamEquationSelector.prepareRow σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) (c6 c7) ((8:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) (Com.assign "query.baseRow" (Expr.var "query.row")) c8 σ (Env.setVar σ "query.baseRow" (Env.vars σ "query.row")) c7 (RunStep.cond_lt_true B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5144_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5144_0_0_1)) hcase) (RunStep.assign B σ "query.baseRow" (Expr.var "query.row") (Env.vars σ "query.row") (RunStep.eval_var B σ "query.row" (?nAX_g5144_0_0_2)))) (?nAX_g5144_0_0_3)) ?_)) fun (hcase:c1) => @Exists.intro Env c3 c10 (@And.intro (Run B RamEquationSelector.prepareRow σ c10 ((8:Nat))) (c2 c10) (RunStep.mono B RamEquationSelector.prepareRow σ c10 (c6 c11) ((8:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "query.row") (Expr.var "system.m")) (Com.assign "query.baseRow" (Expr.var "query.row")) c8 σ c10 c11 (RunStep.cond_lt_false B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5144_0_0_4)) (RunStep.eval_var B σ "system.m" (?nAX_g5144_0_0_5)) hcase) (RunStep.assign B σ "query.baseRow" (Expr.sub (Expr.var "query.row") (Expr.var "system.m")) c9 (RunStep.eval_sub B σ (Expr.var "query.row") (Expr.var "system.m") (Env.vars σ "query.row") (Env.vars σ "system.m") (RunStep.eval_var B σ "query.row" (?nAX_g5144_0_0_6)) (RunStep.eval_var B σ "system.m" (?nAX_g5144_0_0_7)) (?nAX_g5144_0_0_8)))) (?nAX_g5144_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5144_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5144_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [r]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega
  rintro σ ⟨hσData,hσrow⟩
  obtain ⟨τ,hr₁,hτr⟩:=hprepare σ ⟨hσData.2.2.1,hσrow⟩
  have hτData:=data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; change a ++ s∉ ([]:List String); simp)
  have hr₂:Run B (.assign "vec.i" (.var "query.baseRow")) τ (τ.setVar "vec.i" r.val) 2:=
    Run.assign (by simpa only [hτr] using (evalB_var (B:=B) (σ:=τ) (x:= "query.baseRow") (hτr ▸ hrB)))
  have he:(List.ofFn (rationalProgram P).b)[r.val]=(P.b r:ℚ):=by simp [rationalProgram]
  obtain ⟨υ,hr₃,hυq⟩:=RamArrayResult.load_spec B "system.b" (List.ofFn (rationalProgram P).b) r.val
    (by simpa using r.isLt) h1 hrB (by rw [he]; exact hq.1.trans_lt hMB) (by rw [he]; exact hq.2.trans_lt hMB)
    (τ.setVar "vec.i" r.val) ⟨hτData.2.1,by simp⟩
  rw [he] at hυq
  have hυm:=((hr₂.seq hr₃).frame_var "system.m" (by decide)).trans hτData.2.2.1
  have hυrow:=((hr₁.seq (hr₂.seq hr₃)).frame_var "query.row" (by decide)).trans hσrow
  obtain ⟨ρ,hr₄,hρq⟩:=RamEquationSelector.applyRowSign_spec B m i.val (P.b r:ℚ) h1 hm hiB υ ⟨hυq,hυm,hυrow⟩
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  refine ⟨ρ,hr,data_frame hr P hσData ?_ ?_, ?_⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp
  · by_cases hi:i.val < m <;> simpa [bound,r,hi] using hρq

end Lax109476Proofs.RamEquationBoundSelector

end

section

namespace Lax109476Proofs.RamEquationBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamEquationData EquationQueryEntries RamEllipsoidStep

set_option maxHeartbeats 0 in
theorem selectCoordinate_spec (B M m n:ℕ) (P:Program ℤ m n) (i:Fin (m + m))
    (hM:1≤ M) (hMB:M < B) (hB:m + m + n + 4 < B)
    (hb:∀ r, (P.b r).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=m + m)
      selectCoordinate (fun _ τ => Data P τ∧ FractionOutput (bound P i) τ) 35:=by
  have hiB:i.val < B:=i.isLt.trans (by omega)
  have hselector:=RamEquationBoundSelector.selectBound_spec B M m n P i hM hMB hB hb
  have hbase:Spec B (fun σ => Data P σ∧ σ.vars "build.i"=i.val∧ σ.vars "build.count"=m + m)
      selectCoordinate (fun _ τ => FractionOutput (bound P i) τ) 35:=by
    rintro σ ⟨⟨hσA,hσb,hσm,hσn⟩,hσi,hσcount⟩
    (expose_names;
      (refine let c0:Env→ Nat→ Prop:=Run B RamEquationBoundSelector.selectBound (Env.setVar σ "query.row" (Env.vars σ "build.i")); let c1:Env→ Prop:=fun (σ':Env) => And (c0 σ' ((33:Nat))) (And (@Data m n P σ') (FractionOutput (@bound m n P i) σ')); let c2:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@bound m n P i) τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B selectCoordinate σ σ' ((35:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat:= @Fin.val (c5 m m) i; let c7:Nat:=c5 ((1:Nat)) (Expr.size (Expr.var "build.i")); @Exists.casesOn Env c1 (fun (x:@Exists Env c1) => c4) (RunStep.use B (fun (σ_1:Env) => And (@Data m n P σ_1) (@Eq Nat (Env.vars σ_1 "query.row") c6)) RamEquationBoundSelector.selectBound (fun (x τ:Env) => And (@Data m n P τ) (FractionOutput (@bound m n P i) τ)) ((33:Nat)) hselector (Env.setVar σ "query.row" (Env.vars σ "build.i")) ?_) fun (w:Env) (h:And (c0 w ((33:Nat))) (And (@Data m n P w) (FractionOutput (@bound m n P i) w))) => let c0_1:Prop:=c0 w ((33:Nat)); let c1_1:Prop:=FractionOutput (@bound m n P i) w; let c2_1:Prop:=And (@Data m n P w) c1_1; @And.casesOn c0_1 c2_1 (fun (x:And c0_1 c2_1) => c4) h fun (left:c0_1) (right:c2_1) => @Exists.intro Env c3 w (@And.intro (Run B selectCoordinate σ w ((35:Nat))) (c2 w) (RunStep.mono B selectCoordinate σ w (c5 c7 ((33:Nat))) ((35:Nat)) (RunStep.seq B (Com.assign "query.row" (Expr.var "build.i")) RamEquationBoundSelector.selectBound σ (Env.setVar σ "query.row" (Env.vars σ "build.i")) w c7 ((33:Nat)) (RunStep.assign B σ "query.row" (Expr.var "build.i") (Env.vars σ "build.i") (RunStep.eval_var B σ "build.i" (?nAX_g5146_0_0_0))) left) (?nAX_g5146_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5146_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5146_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals clear hselector
    all_goals simp_all [Data,Represents,arrs_setVar]
    all_goals aesop
  intro σ hσ
  obtain ⟨τ,hr,hτ⟩:=hbase σ hσ
  refine ⟨τ,hr,data_frame hr P hσ.1 ?_ ?_,hτ⟩
  · intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide
  · intro a ha s hs; change a ++ s∉ ([]:List String); simp

set_option maxHeartbeats 0 in
theorem buildBound_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hB:m + m + n + 4 < B)
    (hb:∀ r, (P.b r).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ Extents "point.b" (m + m) σ) buildBound
      (fun _ τ => Data P τ∧ Represents "point.b"
        (List.ofFn (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).b) τ)
      (91 * (m + m) + 30):=by
  let N:=m + m
  have h1:1 < B:=by omega
  have hNB:N < B:=by dsimp only [N]; omega
  have hbuild:=RamBuildVector.build_spec B M N 35 "point.b" (bound P) selectCoordinate (Data P)
    h1 hNB hMB (bound_height P M hM hb)
    (selectCoordinate_spec B M m n P · hM hMB hB hb) (by decide) (by decide)
    (by intro s hs; change "point.b" ++ s∉ ([]:List String); simp)
    (preserves_data B P (storeReduced "point.b")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (preserves_data B P (RamZeroArray.zeroRationalArray "point.b")
      (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
      (by
        intro a ha s hs
        simp [RamEquationData.arrays] at ha
        simp [RamCopy.suffixes] at hs
        rcases ha with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> decide))
    (fun σ z h => data_setVar P σ "build.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.i" z (by decide) h)
    (fun σ z h => data_setVar P σ "vec.n" z (by decide) h)
  have hvalues:List.ofFn (bound P)=List.ofFn
      (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b).b:=by
    congr 1; funext i; exact bound_eq P i
  have hmeta:Spec B (fun σ => σ.vars "system.m"=m) prepare (fun _ τ => τ.vars "build.count"=N) 4:=by
    intro σ hm
    (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "build.count") N) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 (Env.vars σ "system.m") (Env.vars σ "system.m"); let c3:Env:=Env.setVar σ "build.count" c2; @Exists.intro Env (fun (σ':Env) => And (Run B prepare σ σ' ((4:Nat))) (c0 σ')) c3 (@And.intro (Run B prepare σ c3 ((4:Nat))) (c0 c3) (RunStep.mono B prepare σ c3 (c1 ((1:Nat)) (Expr.size (Expr.add (Expr.var "system.m") (Expr.var "system.m")))) ((4:Nat)) (RunStep.assign B σ "build.count" (Expr.add (Expr.var "system.m") (Expr.var "system.m")) c2 (RunStep.eval_add B σ (Expr.var "system.m") (Expr.var "system.m") (Env.vars σ "system.m") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.m" (?nAX_g5149_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5149_0_0_1)) (?nAX_g5149_0_0_2))) (?nAX_g5149_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5149_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5149_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5149_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5149_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [N]
    all_goals omega
  rintro σ ⟨hσData,hσtarget⟩
  obtain ⟨τ,hr₁,hτcount⟩:=hmeta σ hσData.2.2.1
  have hτData:=data_frame hr₁ P hσData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [Com.warrs,prepare])
  obtain ⟨υ,hr₂,hυData,hυtarget,hυcount⟩:=hbuild τ
    ⟨hτData,RamAdvanceState.extents_of_run hr₁ "point.b" N hσtarget,hτcount⟩
  refine ⟨υ, (hr₁.seq hr₂).mono ?_,hυData, ?_⟩
  · dsimp only [N]; omega
  · simpa only [hvalues] using hυtarget

end Lax109476Proofs.RamEquationBound

end

section

namespace Lax109476Proofs.RamEquationBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEquationData RamEllipsoidStep RationalArithmeticBounds

theorem metadata_spec (B m n:ℕ) (hB:m + m + n + 4 < B):
    Spec B (fun σ => σ.vars "system.m"=m∧ σ.vars "system.n"=n) metadata
      (fun _ τ => τ.vars "point.m"=m + m∧ τ.vars "point.n"=n + m) 8:=by
  rintro σ ⟨hm,hn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 m m; let c2:Nat:=c0 n m; let c3:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "point.m") c1) (@Eq Nat (Env.vars τ "point.n") c2)) σ; let c4:Nat:=c0 (Env.vars σ "system.m") (Env.vars σ "system.m"); let c5:Env:=Env.setVar σ "point.m" c4; let c6:String→ Nat:=Env.vars c5; let c7:Nat:=c6 "system.n"; let c8:Nat:=c6 "system.m"; let c9:Nat:=c0 c7 c8; let c10:Env:=Env.setVar c5 "point.n" c9; let c11:Nat→ Nat:=c0 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.add (Expr.var "system.m") (Expr.var "system.m"))); let c13:Nat:=c11 (Expr.size (Expr.add (Expr.var "system.n") (Expr.var "system.m"))); let c14:String→ Nat:=Env.vars c10; @Exists.intro Env (fun (σ':Env) => And (Run B metadata σ σ' ((8:Nat))) (c3 σ')) c10 (@And.intro (Run B metadata σ c10 ((8:Nat))) (c3 c10) (RunStep.mono B metadata σ c10 (c0 c12 c13) ((8:Nat)) (RunStep.seq B (Com.assign "point.m" (Expr.add (Expr.var "system.m") (Expr.var "system.m"))) (Com.assign "point.n" (Expr.add (Expr.var "system.n") (Expr.var "system.m"))) σ c5 c10 c12 c13 (RunStep.assign B σ "point.m" (Expr.add (Expr.var "system.m") (Expr.var "system.m")) c4 (RunStep.eval_add B σ (Expr.var "system.m") (Expr.var "system.m") (Env.vars σ "system.m") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.m" (?nAX_g5152_0_0_0)) (RunStep.eval_var B σ "system.m" (?nAX_g5152_0_0_1)) (?nAX_g5152_0_0_2))) (RunStep.assign B c5 "point.n" (Expr.add (Expr.var "system.n") (Expr.var "system.m")) c9 (RunStep.eval_add B c5 (Expr.var "system.n") (Expr.var "system.m") c7 c8 (RunStep.eval_var B c5 "system.n" (?nAX_g5152_0_0_3)) (RunStep.eval_var B c5 "system.m" (?nAX_g5152_0_0_4)) (?nAX_g5152_0_0_5)))) (?nAX_g5152_0_0_6)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5152_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5152_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all
  all_goals omega

set_option maxHeartbeats 0 in
theorem buildSystem_spec (B M m n:ℕ) (P:Program ℤ m n)
    (hM:1≤ M) (hMB:M < B) (hB:(m + m) * (n + m) + m + m + n + 4 < B)
    (hA:∀ i j, (P.A i j).natAbs≤ M) (hb:∀ i, (P.b i).natAbs≤ M):
    Spec B (fun σ => Data P σ∧ Extents "point.A" ((m + m) * (n + m)) σ∧ Extents "point.b" (m + m) σ)
      buildSystem (fun _ τ => Data P τ∧ RamPointInitialization.Base
        (RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b) τ)
      (118 * ((m + m) * (n + m)) + 91 * (m + m) + 72):=by
  let C:=RamStandardPointRecovery.program (IntegerPointRecovery.slackMatrix P) P.b
  rintro σ ⟨hσData,hσA,hσb⟩
  obtain ⟨τ,hr₁,hτData,hτA⟩:=RamEquationMatrix.matrix_spec B M m n P hM hMB (by omega) hA σ ⟨hσData,hσA⟩
  obtain ⟨υ,hr₂,hυData,hυb⟩:=RamEquationBound.buildBound_spec B M m n P hM hMB (by omega) hb τ
    ⟨hτData,RamAdvanceState.extents_of_run hr₁ _ _ hσb⟩
  have hυA:=RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten C.A) hτA hr₂
    (by intro s hs; simp at hs; rcases hs with rfl | rfl | rfl <;> decide)
  obtain ⟨ρ,hr₃,hρm,hρn⟩:=metadata_spec B m n (by omega) υ ⟨hυData.2.2.1,hυData.2.2.2⟩
  have hρData:=data_frame hr₃ P hυData
    (by intro a ha; simp [RamEquationData.fields] at ha; rcases ha with rfl | rfl <;> decide)
    (by intro a ha s hs; simp [metadata,Com.warrs])
  have hρA:=RamReadBody.represents_frame "point.A" (RamMatrixStorage.flatten C.A) hυA hr₃
    (by intro s hs; simp [metadata,Com.warrs])
  have hρb:=RamReadBody.represents_frame "point.b" (List.ofFn C.b) hυb hr₃
    (by intro s hs; simp [metadata,Com.warrs])
  exact ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega),hρData,hρA,hρb,hρm,hρn⟩

end Lax109476Proofs.RamEquationBuilder

end

section

namespace Lax109476Proofs.StandardPointCapComparison

theorem slack_cap_le (m n H:ℕ):
    LexicographicBounds.coordinateCap m (n + m) H≤ IntegerCertificates.coordinateCap m n H:=by
  let K:=2 * (m + n) + 2
  have hnm:n + m≤ K:=by dsimp only [K]; omega
  have hm:m≤ K:=by dsimp only [K]; omega
  unfold LexicographicBounds.coordinateCap IntegerCertificates.coordinateCap
  change (n + m).factorial * (m * H ^ 2 + 1) ^ (n + m)≤ K.factorial * (K * H ^ 2 + 1) ^ K
  apply Nat.mul_le_mul (Nat.factorial_le hnm)
  exact (Nat.pow_le_pow_left (by gcongr) _).trans (Nat.pow_le_pow_right (by omega) hnm)

end Lax109476Proofs.StandardPointCapComparison

end

section

namespace Lax109476Proofs.RamRecoverFeasibleSystem

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEquationData RamEllipsoidStep RationalArithmeticBounds
open IntegerEncoding IntegerPointRecovery

theorem prepareCap_spec (B m n H:ℕ) (hm:m < B) (hn:n < B) (hH:H < B):
    Spec B (fun σ => σ.vars "system.m"=m∧ σ.vars "system.n"=n∧ σ.vars "system.H"=H)
      prepareCap (fun _ τ => τ.vars "query.m"=m∧ τ.vars "query.n"=n∧ τ.vars "cap.H"=H) 6:=by
  rintro σ ⟨hσm,hσn,hσH⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "query.m") m) (And (@Eq Nat (Env.vars τ "query.n") n) (@Eq Nat (Env.vars τ "cap.H") H))) σ; let c1:Nat:=Env.vars (Env.setVar σ "query.m" (Env.vars σ "system.m")) "system.n"; let c2:Env:=Env.setVar (Env.setVar σ "query.m" (Env.vars σ "system.m")) "query.n" c1; let c3:Nat:=Env.vars c2 "system.H"; let c4:Env:=Env.setVar c2 "cap.H" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "system.m")); let c8:Nat:=c6 (Expr.size (Expr.var "system.n")); let c9:Nat:=c6 (Expr.size (Expr.var "system.H")); let c10:Nat:=c5 c8 c9; let c11:String→ Nat:=Env.vars c4; @Exists.intro Env (fun (σ':Env) => And (Run B prepareCap σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B prepareCap σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B prepareCap σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "query.m" (Expr.var "system.m")) (Com.seq (Com.assign "query.n" (Expr.var "system.n")) (Com.assign "cap.H" (Expr.var "system.H"))) σ (Env.setVar σ "query.m" (Env.vars σ "system.m")) c4 c7 c10 (RunStep.assign B σ "query.m" (Expr.var "system.m") (Env.vars σ "system.m") (RunStep.eval_var B σ "system.m" (?nAX_g5162_0_0_0))) (RunStep.seq B (Com.assign "query.n" (Expr.var "system.n")) (Com.assign "cap.H" (Expr.var "system.H")) (Env.setVar σ "query.m" (Env.vars σ "system.m")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "query.m" (Env.vars σ "system.m")) "query.n" (Expr.var "system.n") c1 (RunStep.eval_var B (Env.setVar σ "query.m" (Env.vars σ "system.m")) "system.n" (?nAX_g5162_0_0_1))) (RunStep.assign B c2 "cap.H" (Expr.var "system.H") c3 (RunStep.eval_var B c2 "system.H" (?nAX_g5162_0_0_2))))) (?nAX_g5162_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5162_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5162_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5162_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5162_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_spec (m n S N w:ℕ) (P:Program ℤ m n)
    (hdim:m + n≤ S) (hw:wordWidth m n S≤ w)
    (hN:RamRationalReconstruction.depthBound (recoveryBits S) + 1≤ N)
    (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S)) (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S))
    (hf:∃ x,PrimalFeasible (rationalProgram P) x):
    Spec (2 ^ w) (Input P S N) recover
      (fun _ τ => ∃ z:Fin (n + m)→ ℚ,
        RamRecoveryThreshold.Persistent (RamStandardPointRecovery.program (slackMatrix P) P.b) z (n + m) τ∧
          PrimalFeasible (rationalProgram P) (fun j => z (Fin.castAdd m j))∧
            ∀ j,Height (z j) (IntegerCertificates.coordinateCap m n (2 ^ (2 * S))))
      (instructionBound m n S):=by
  let H:=2 ^ (2 * S)
  let D:=IntegerCertificates.coordinateCap m n H
  let R:=recoveryBits S
  let E:=RamStandardPointRecovery.program (slackMatrix P) P.b
  have hH1:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have hwCap:RamCoordinateCapBounds.wordWidth S≤ w:=by unfold wordWidth at hw; omega
  have hwPoint:RamPointRecoveryBounds.wordWidth (m + m) (n + m) R≤ w:=by
    dsimp only [R]; unfold wordWidth at hw; omega
  have hguard:(m + m) * (n + m) + m + m + n + 4 < 2 ^ w:=
    (by unfold wordWidth at hw; omega:(m + m) * (n + m) + m + m + n + 4≤ w).trans_lt
      (Nat.lt_two_pow_self (n:=w))
  have hmag:=RamCoordinateCapBounds.magnitude_fits m n S w hdim hwCap
  have hHB:H < 2 ^ w:=by dsimp only [RamCoordinateCap.magnitude] at hmag; dsimp only [H]; omega
  have hmB:m < 2 ^ w:=by omega
  have hnB:n < 2 ^ w:=by omega
  have hDbits:D.size≤ capBits S:=RationalSizeBounds.certificate_cap_size
    (2 * (m + n) + 2) S (by omega)
  have hR:4 * capBits S + 2≤ R:=by dsimp only [R,recoveryBits]; omega
  have hHR:H≤ 2 ^ R:=Nat.pow_le_pow_right (by decide) (by dsimp only [R,recoveryBits]; omega)
  have hslack:∀ i j, (slackMatrix P i j).natAbs≤ H:=by
    intro i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa [slackMatrix] using hA i j
    · simp only [slackMatrix,Fin.addCases_right]
      split_ifs <;> norm_num <;> omega
  obtain ⟨x₀,hx₀⟩:=hf
  have hfeas:∃ x,LexicographicSupport.Feasible ((slackMatrix P).map (fun z => (z:ℚ)))
      (fun i => (P.b i:ℚ)) x:= ⟨withSlacks P x₀,withSlacks_feasible P x₀ hx₀⟩
  rintro σ ⟨hσData,hσH,hσA,hσb,hσx,hσW,hσN⟩
  obtain ⟨τ,hr₁,hτData,hτE⟩:=RamEquationBuilder.buildSystem_spec (2 ^ w) H m n P hH1 hHB hguard hA hb σ
    ⟨hσData,hσA,hσb⟩
  have hτH:=(hr₁.frame_var "system.H" (by decide)).trans hσH
  obtain ⟨υ,hr₂,hυm,hυn,hυH⟩:=prepareCap_spec (2 ^ w) m n H hmB hnB hHB τ ⟨hτData.2.2.1,hτData.2.2.2,hτH⟩
  obtain ⟨ρ,hr₃,hρD,_,_,_⟩:=RamCoordinateCapBounds.prepareCap_bounded_spec m n S w hdim hwCap υ ⟨hυm,hυn,hυH⟩
  have hDB:D < 2 ^ w:=by dsimp only [RamCoordinateCap.magnitude] at hmag; dsimp only [D,H]; omega
  have hr₄:Run (2 ^ w) (.assign "minimum.bound" (.var "cap.value")) ρ (ρ.setVar "minimum.bound" D) 2:=
    Run.assign (by simpa only [hρD] using (evalB_var (B:=2 ^ w) (σ:=ρ) (x:= "cap.value") (hρD ▸ hDB)))
  let ξ:=ρ.setVar "minimum.bound" D
  have hrPrepare:=hr₂.seq (hr₃.seq hr₄)
  have hξE:RamPointInitialization.Base E ξ:=by
    rcases hτE with ⟨hEA,hEb,hEm,hEn⟩
    exact ⟨RamReadBody.represents_frame _ _ hEA hrPrepare (by intro s hs; change _∉ ([]:List String); simp),
      RamReadBody.represents_frame _ _ hEb hrPrepare (by intro s hs; change _∉ ([]:List String); simp),
      (hrPrepare.frame_var "point.m" (by decide)).trans hEm, (hrPrepare.frame_var "point.n" (by decide)).trans hEn⟩
  have hrPre:=hr₁.seq hrPrepare
  have hξW:=RamRecoveryThreshold.workspace_frame hrPre _ _ hσW
  have hξx:=RamAdvanceState.extents_of_run hrPre "point.x" (n + m) hσx
  have hξN:(ξ.arrs "cf.stack").length=N:=by rw [hrPre.frame_arr _ (by decide)]; exact hσN
  obtain ⟨ζ,hr₅,z,hζ,hz,hzHeight⟩:=RamStandardPointRecovery.recover_with_cap_spec m (n + m) H R (capBits S) N w D
    (slackMatrix P) P.b hslack hb hHR (StandardPointCapComparison.slack_cap_le m n H)
    hDbits hR hN hwPoint hfeas ξ ⟨hξE,hξW,hξx,by simp [ξ],hξN⟩
  refine ⟨ζ, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))).mono ?_,z,hζ,
    slack_point_feasible P z hz,fun j => height_mono _ (hzHeight j) (StandardPointCapComparison.slack_cap_le m n H)⟩
  dsimp only [instructionBound,R]
  omega

end Lax109476Proofs.RamRecoverFeasibleSystem

end

theorem solution:∀ (m n S N w:ℕ) (P:Lax109476.LinearProgram.Program ℤ m n),
  m + n≤ S→
    Lax109476Proofs.RamRecoverFeasibleSystem.wordWidth m n S≤ w→
      Lax109476Proofs.RamRationalReconstruction.depthBound (Lax109476Proofs.RamRecoverFeasibleSystem.recoveryBits S) +
            1≤
          N→
        (∀ (i:Fin m) (j:Fin n), (P.A i j).natAbs≤ 2 ^ (2 * S))→
          (∀ (i:Fin m), (P.b i).natAbs≤ 2 ^ (2 * S))→
            (∃ (x:Fin n→ ℚ),
                Lax109476.LinearProgram.PrimalFeasible (Lax109476Proofs.IntegerEncoding.rationalProgram P) x)→
              Lax808846Proofs.Reasoning.Spec (2 ^ w) (Lax109476Proofs.RamRecoverFeasibleSystem.Input P S N)
                Lax109476Proofs.RamRecoverFeasibleSystem.recover
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  ∃ (z:Fin (n + m)→ ℚ),
                    Lax109476Proofs.RamRecoveryThreshold.Persistent
                        (Lax109476Proofs.RamStandardPointRecovery.program
                          (Lax109476Proofs.IntegerPointRecovery.slackMatrix P) P.b)
                        z (n + m) τ∧
                      (Lax109476.LinearProgram.PrimalFeasible (Lax109476Proofs.IntegerEncoding.rationalProgram P)
                          fun (j:Fin n) => z (Fin.castAdd m j))∧
                        ∀ (j:Fin (n + m)),
                          Lax109476Proofs.RationalArithmeticBounds.Height (z j)
                            (Lax109476Proofs.IntegerCertificates.coordinateCap m n (2 ^ (2 * S))))
                (Lax109476Proofs.RamRecoverFeasibleSystem.instructionBound m n S):= @Lax109476Proofs.RamRecoverFeasibleSystem.recover_spec
