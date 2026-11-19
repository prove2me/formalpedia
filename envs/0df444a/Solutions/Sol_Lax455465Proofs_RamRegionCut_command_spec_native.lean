-- Prove2me | solution 1 for Lax455465Proofs.RamRegionCut.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:51.375663+00:00
-- url     : https://prove2.me/submissions/aaac1683-61c0-4fd9-a5b6-c9e82e2dd900

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.BigOperators
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native

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
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational
theorem Lax109476Proofs.RamRational.addFraction_spec:∀ (B M s₁ n₁ d₁ s₂ n₂ d₂:Nat),
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
                      Lax109476Proofs.RamRational.addFraction
                      (fun (x σ':Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (HAdd.hAdd
                        (HMul.hMul
                          ((36:Nat))
                          (HMul.hMul d₁ d₂).size)
                        ((96:Nat))):= @Lax109476Proofs.RamRational.addFraction_spec_native

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

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

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

theorem fractionValue_inv (s n d:ℕ):fractionValue s d n=(fractionValue s n d)⁻¹:=by
  unfold fractionValue
  split_ifs <;> simp [inv_div,neg_div]

theorem invertFraction_spec (B s n d:ℕ) (h1:1 < B) (hs:s≤ 1)
    (hn:n < B) (hd:d < B):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧ σ.vars "left.d"=d)
      invertFraction (fun _ σ' => FractionOutput (fractionValue s n d)⁻¹ σ')
      (36 * n.size + 40):=by
  have hsB:=hs.trans_lt h1
  by_cases hz:n=0
  · subst n
    have hzero:Spec B (fun _ => True)
        (.seq (.assign "rat.n" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
        (fun _ σ' => FractionOutput 0 σ') 6:=by
      (expose_names;
        (refine fun (σ:Env) (a:True) => let c0:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c1:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c2:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c3:Com:=Com.seq c1 c2; let c4:Com:=Com.seq c0 c3; let c5:Env→ Nat→ Prop:=Run B c4 σ; let c6:Env→ Prop:=(fun (x σ':Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) σ') σ; let c7:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat)); let c9:Env:=Env.setVar c8 "rat.s" ((0:Nat)); let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.lit ((1:Nat)))); let c14:Nat:=c10 c13 c12; @Exists.intro Env (fun (σ':Env) => And (c5 σ' ((6:Nat))) (c6 σ')) c9 (@And.intro (c5 c9 ((6:Nat))) (c6 c9) (RunStep.mono B c4 σ c9 (c10 c12 c14) ((6:Nat)) (RunStep.seq B c0 c3 σ c7 c9 c12 c14 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ hn)) (RunStep.seq B c1 c2 c7 c8 c9 c13 c12 (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)) (RunStep.assign B c8 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c8 hn)))) (?nAX_g5425_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5425_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
      all_goals simp [FractionOutput,fractionValue]
    rintro σ ⟨hσs,hσn,hσd⟩
    have hc:(Cond.eq (.var "left.n") (.lit 0)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hσn ▸ hn)) (evalB_lit (by omega)),hσn]
      rfl
    obtain ⟨τ,hr,hτ⟩:=hzero σ True.intro
    exact ⟨τ, (Run.ite_true hc hr).mono (by simp [Nat.size]),
      by simpa [fractionValue] using hτ⟩
  · have hnorm:=normalizeFraction_output_spec B s d n hs hd hn (Nat.pos_of_ne_zero hz)
    have hv:=fractionValue_inv s n d
    (expose_names;
      (refine fun (σ:Env) (a:And (@Eq Nat (Env.vars σ "left.s") s) (And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d))) => let c0:Prop:=And (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d); let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat→ Nat:=c1 (Nat.mul ((36:Nat)) (Nat.size n)); let c3:Nat:=c2 ((40:Nat)); let c4:Env→ Prop:=FractionOutput (@Inv.inv Rat Rat.instInv (fractionValue s n d)); let c5:Env→ Prop:=(fun (x σ':Env) => c4 σ') σ; let c6:Env→ Prop:=fun (σ':Env) => And (Run B invertFraction σ σ' c3) (c5 σ'); let c7:Prop:= @Exists Env c6; let c8:Prop:= @Eq Nat (Env.vars σ "left.n") ((0:Nat)); let c9:Prop:=Not c8; let c10:Env:=Env.setVar σ "rat.n" ((0:Nat)); let c11:Env:=Env.setVar c10 "rat.d" ((1:Nat)); let c12:Env:=Env.setVar c11 "rat.s" ((0:Nat)); let c13:Nat→ Nat:=c1 ((1:Nat)); let c14:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c15:Nat→ Nat:=c1 (c13 (Cond.size c14)); let c16:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c17:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c18:Nat:=c1 c17 c16; let c19:Nat:=c1 c16 c18; let c20:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c22:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c23:Com:=Com.seq c21 c22; let c24:Com:=Com.seq c20 c23; let c25:Com:=Com.seq (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction); let c26:Com:=Com.seq (Com.assign "rat.n" (Expr.var "left.d")) c25; let c27:Nat:=Env.vars (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n"; let c28:Env:=Env.setVar (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" c27; let c29:Nat:=Env.vars c28 "left.s"; let c30:Env:=Env.setVar c28 "rat.s" c29; let c31:Env→ Nat→ Prop:=Run B normalizeFraction c30; let c32:Nat:=c2 ((16:Nat)); let c33:Env→ Prop:=fun (σ':Env) => And (c31 σ' c32) (FractionOutput (fractionValue s d n) σ'); let c34:String→ Nat:=Env.vars c30; let c35:Nat:=c13 (Expr.size (Expr.var "left.d")); let c36:Nat:=c13 (Expr.size (Expr.var "left.n")); let c37:Nat:=c13 (Expr.size (Expr.var "left.s")); let c38:Nat:=c1 c37 c32; let c39:Nat:=c1 c36 c38; let c40:Nat:=c1 c35 c39; @And.casesOn (@Eq Nat (Env.vars σ "left.s") s) c0 (fun (x:And (@Eq Nat (Env.vars σ "left.s") s) c0) => c7) a fun (left:@Eq Nat (Env.vars σ "left.s") s) (right:c0) => @And.casesOn (@Eq Nat (Env.vars σ "left.n") n) (@Eq Nat (Env.vars σ "left.d") d) (fun (x:c0) => c7) right fun (left_1:@Eq Nat (Env.vars σ "left.n") n) (right_1:@Eq Nat (Env.vars σ "left.d") d) => @Or.casesOn c8 c9 (fun (x:Or c8 c9) => c7) (Classical.em c8) (fun (hcase:c8) => @Exists.intro Env c6 c12 (@And.intro (Run B invertFraction σ c12 c3) (c5 c12) (RunStep.mono B invertFraction σ c12 (c15 c19) c3 (RunStep.ite_true B c14 c24 c26 σ c12 c19 (RunStep.cond_eq_true B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g5425_1_0_0)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_1)) hcase) (RunStep.seq B c20 c23 σ c10 c12 c16 c18 (RunStep.assign B σ "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_2))) (RunStep.seq B c21 c22 c10 c11 c12 c17 c16 (RunStep.assign B c10 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c10 h1)) (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g5425_1_0_3)))))) (?nAX_g5425_1_0_4)) ?_)) fun (hcase:c9) => @Exists.casesOn Env c33 (fun (x:@Exists Env c33) => c7) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") d) (And (@Eq Nat (Env.vars σ_1 "rat.d") n) (@Eq Nat (Env.vars σ_1 "rat.s") s))) normalizeFraction (fun (x σ':Env) => FractionOutput (fractionValue s d n) σ') c32 hnorm c30 ?_) fun (w:Env) (h:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => @And.casesOn (c31 w c32) (FractionOutput (fractionValue s d n) w) (fun (x:And (c31 w c32) (FractionOutput (fractionValue s d n) w)) => c7) h fun (left_2:c31 w c32) (right_2:FractionOutput (fractionValue s d n) w) => @Exists.intro Env c6 w (@And.intro (Run B invertFraction σ w c3) (c5 w) (RunStep.mono B invertFraction σ w (c15 c40) c3 (RunStep.ite_false B c14 c24 c26 σ w c40 (RunStep.cond_eq_false B σ (Expr.var "left.n") (Expr.lit ((0:Nat))) (Env.vars σ "left.n") ((0:Nat)) (RunStep.eval_var B σ "left.n" (?nAX_g5425_1_0_5)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5425_1_0_6)) hcase) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.d")) c25 σ (Env.setVar σ "rat.n" (Env.vars σ "left.d")) w c35 c39 (RunStep.assign B σ "rat.n" (Expr.var "left.d") (Env.vars σ "left.d") (RunStep.eval_var B σ "left.d" (?nAX_g5425_1_0_7))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "left.n")) (Com.seq (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction) (Env.setVar σ "rat.n" (Env.vars σ "left.d")) c28 w c36 c38 (RunStep.assign B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "rat.d" (Expr.var "left.n") c27 (RunStep.eval_var B (Env.setVar σ "rat.n" (Env.vars σ "left.d")) "left.n" (?nAX_g5425_1_0_8))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) normalizeFraction c28 c30 w c37 c32 (RunStep.assign B c28 "rat.s" (Expr.var "left.s") c29 (RunStep.eval_var B c28 "left.s" (?nAX_g5425_1_0_9))) left_2)))) (?nAX_g5425_1_0_10)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5425_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5425_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left_2))
    all_goals simp_all

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

set_option maxHeartbeats 0 in
theorem addFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ σ' => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) σ')
      (36 * (d₁ * d₂).size + 96)  :=by
  exact Lax109476Proofs.RamRational.addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂ hd₁pos hd₂pos

end Lax455465Proofs.RamRational

end

section

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def leFlag (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):ℕ:=
  if s₁=s₂ then
    if s₁=1 then (if n₁ * d₂ < n₂ * d₁ then 0 else 1)
    else (if n₂ * d₁ < n₁ * d₂ then 0 else 1)
  else if s₁=1 then 1
  else if n₁=0 then (if n₂=0 then 1 else 0) else 0

theorem leFlag_le_one (s₁ n₁ d₁ s₂ n₂ d₂:ℕ):leFlag s₁ n₁ d₁ s₂ n₂ d₂≤ 1:=by
  unfold leFlag
  split_ifs <;> omega

theorem leFlag_correct (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hd₁:0 < d₁) (hd₂:0 < d₂):
    leFlag s₁ n₁ d₁ s₂ n₂ d₂=1↔
      fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂:=by
  have hd₁q:(0:ℚ) < d₁:=by exact_mod_cast hd₁
  have hd₂q:(0:ℚ) < d₂:=by exact_mod_cast hd₂
  have hpos₁:(0:ℚ)≤ (n₁:ℚ) / d₁:=by positivity
  have hpos₂:(0:ℚ)≤ (n₂:ℚ) / d₂:=by positivity
  have hcross:(n₁:ℚ) / d₁≤ (n₂:ℚ) / d₂↔ n₁ * d₂≤ n₂ * d₁:=by
    rw [div_le_div_iff₀ hd₁q hd₂q]
    exact_mod_cast Iff.rfl
  have hcrossRev:(n₂:ℚ) / d₂≤ (n₁:ℚ) / d₁↔ n₂ * d₁≤ n₁ * d₂:=by
    rw [div_le_div_iff₀ hd₂q hd₁q]
    exact_mod_cast Iff.rfl
  have hzero:(n₁:ℚ) / d₁≤ -((n₂:ℚ) / d₂)↔ n₁=0∧ n₂=0:=by
    constructor
    · intro h
      have hz₁:(n₁:ℚ) / d₁=0:=by linarith
      have hz₂:(n₂:ℚ) / d₂=0:=by linarith
      simpa [div_eq_zero_iff,ne_of_gt hd₁q,ne_of_gt hd₂q] using And.intro hz₁ hz₂
    · rintro ⟨rfl,rfl⟩; simp
  have hs₁cases:s₁=0∨ s₁=1:=by omega
  have hs₂cases:s₂=0∨ s₂=1:=by omega
  rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl
  · simp [leFlag,fractionValue,hcross]
  · simp [leFlag,fractionValue,neg_div,hzero]
    split_ifs <;> simp_all
  · simp [leFlag,fractionValue,neg_div]
    linarith
  · simp [leFlag,fractionValue,neg_div,hcrossRev]

set_option maxHeartbeats 0 in
theorem compareFraction_flag_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le"=leFlag s₁ n₁ d₁ s₂ n₂ d₂) 40:=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have huB:n₁ * d₂ < B:=(Nat.mul_le_mul hn₁ hd₂).trans_lt (by nlinarith)
  have hvB:n₂ * d₁ < B:=(Nat.mul_le_mul hn₂ hd₁).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:=hs₁.trans_lt h1
  have hs₂B:=hs₂.trans_lt h1
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.d"); let c2:Env:=Env.setVar σ "cmp.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "right.n"; let c5:Nat:=c3 "left.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "cmp.v" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat→ Prop:= @Eq Nat c9; let c11:Nat:=c8 "right.s"; let c12:Prop:=c10 c11; let c13:Prop:=Not c12; let c14:Nat:=leFlag s₁ n₁ d₁ s₂ n₂ d₂; let c15:Env→ Prop:=(fun (x σ':Env) => @Eq Nat (Env.vars σ' "cmp.le") c14) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B compareFraction σ σ' ((40:Nat))) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Prop:=c10 ((1:Nat)); let c19:Prop:=Not c18; let c20:Nat:=c8 "cmp.u"; let c21:Nat→ Prop:=Nat.lt c20; let c22:Nat:=c8 "cmp.v"; let c23:Prop:=c21 c22; let c24:Prop:=Not c23; let c25:Nat→ Env:=Env.setVar c7 "cmp.le"; let c26:Env:=c25 ((0:Nat)); let c27:Nat→ Nat→ Nat:=Nat.add; let c28:Nat→ Nat:=c27 ((1:Nat)); let c29:Nat:=c28 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))); let c30:Nat→ Nat:=c27 c29; let c31:Nat:=c28 (Expr.size (Expr.mul (Expr.var "right.n") (Expr.var "left.d"))); let c32:Nat→ Nat:=c27 c31; let c33:Nat→ Nat:=c27 (c28 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c34:Cond:=Cond.eq (Expr.var "left.s") (Expr.lit ((1:Nat))); let c35:Nat→ Nat:=c27 (c28 (Cond.size c34)); let c36:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")))); let c37:Nat:=c28 (Expr.size (Expr.lit ((0:Nat)))); let c38:Nat:=c36 c37; let c39:Nat:=c35 c38; let c40:Nat:=c33 c39; let c41:Nat:=c32 c40; let c42:Com:=Com.assign "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")); let c43:Com→ Com→ Com:=Com.ite c34; let c44:Com:=Com.assign "cmp.le" (Expr.lit ((0:Nat))); let c45:Com:=Com.assign "cmp.le" (Expr.lit ((1:Nat))); let c46:Com:=Com.ite (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45; let c47:Com:=Com.ite (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45; let c48:Com:=c43 c46 c47; let c49:Cond:=Cond.eq (Expr.var "left.n") (Expr.lit ((0:Nat))); let c50:Cond:=Cond.eq (Expr.var "right.n") (Expr.lit ((0:Nat))); let c51:Com:=Com.ite c50 c45 c44; let c52:Com:=Com.ite c49 c51 c44; let c53:Com:=c43 c45 c52; let c54:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53; let c55:Nat→ Prop:=Nat.lt c22; let c56:Env:=c25 ((1:Nat)); let c57:Nat:=c28 (Expr.size (Expr.lit ((1:Nat)))); let c58:Nat:=c36 c57; let c59:Nat:=c35 c58; let c60:Nat:=c33 c59; let c61:Nat:=c32 c60; let c62:Prop:=c55 c20; let c63:Prop:=Not c62; let c64:Nat→ Nat:=c27 (c28 (Cond.size (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")))); let c65:Nat:=c64 c37; let c66:Nat:=c35 c65; let c67:Nat:=c33 c66; let c68:Nat:=c32 c67; let c69:Nat:=c64 c57; let c70:Nat:=c35 c69; let c71:Nat:=c33 c70; let c72:Nat:=c32 c71; let c73:Nat:=c35 c57; let c74:Nat:=c33 c73; let c75:Nat:=c32 c74; let c76:Nat:=c8 "left.n"; let c77:Prop:= @Eq Nat c76 ((0:Nat)); let c78:Prop:=Not c77; let c79:Nat:=c8 "right.n"; let c80:Prop:= @Eq Nat c79 ((0:Nat)); let c81:Prop:=Not c80; let c82:Nat→ Nat:=c27 (c28 (Cond.size c49)); let c83:Nat→ Nat:=c27 (c28 (Cond.size c50)); let c84:Nat:=c83 c57; let c85:Nat:=c82 c84; let c86:Nat:=c35 c85; let c87:Nat:=c33 c86; let c88:Nat:=c32 c87; let c89:Nat:=c83 c37; let c90:Nat:=c82 c89; let c91:Nat:=c35 c90; let c92:Nat:=c33 c91; let c93:Nat:=c32 c92; let c94:Nat:=c82 c37; let c95:Nat:=c35 c94; let c96:Nat:=c33 c95; let c97:Nat:=c32 c96; @Or.casesOn c12 c13 (fun (x:Or c12 c13) => c17) (Classical.em c12) (fun (hcase:c12) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Or.casesOn c23 c24 (fun (x:Or c23 c24) => c17) (Classical.em c23) (fun (hcase_2:c23) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c41) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c41 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_0)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_1)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c40 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_2)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_3)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c39 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_5)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c26 c38 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_6)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_7)))))))) (?nAX_g5438_0_0_8)) ?_)) fun (hcase_2:c24) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c61) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c61 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_9)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_10)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c60 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_11)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_12)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c59 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_13)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_14)) hcase) (RunStep.ite_true B c34 c46 c47 c7 c56 c58 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_15)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.u") (Expr.var "cmp.v")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.u") (Expr.var "cmp.v") c20 c22 (RunStep.eval_var B c7 "cmp.u" ?_) (RunStep.eval_var B c7 "cmp.v" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_16)) ?_)) fun (hcase_1:c19) => @Or.casesOn c62 c63 (fun (x:Or c62 c63) => c17) (Classical.em c62) (fun (hcase_2:c62) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c68) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c68 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_17)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_18)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c67 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_19)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_20)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c66 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_21)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_22)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c26 c65 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_23)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c26 c37 (RunStep.cond_lt_true B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_24)))))))) (?nAX_g5438_0_0_25)) ?_)) fun (hcase_2:c63) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c72) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c72 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_26)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_27)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c71 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_28)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_29)) ?_)) (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c70 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_30)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_31)) hcase) (RunStep.ite_false B c34 c46 c47 c7 c56 c69 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_32)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B (Cond.lt (Expr.var "cmp.v") (Expr.var "cmp.u")) c44 c45 c7 c56 c57 (RunStep.cond_lt_false B c7 (Expr.var "cmp.v") (Expr.var "cmp.u") c22 c20 (RunStep.eval_var B c7 "cmp.v" ?_) (RunStep.eval_var B c7 "cmp.u" ?_) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))))))) (?nAX_g5438_0_0_33)) ?_)) fun (hcase:c13) => @Or.casesOn c18 c19 (fun (x:Or c18 c19) => c17) (Classical.em c18) (fun (hcase_1:c18) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c75) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c75 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_34)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_35)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c74 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_36)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_37)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c73 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_38)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_39)) hcase) (RunStep.ite_true B c34 c45 c52 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_40)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))) (?nAX_g5438_0_0_41)) ?_)) fun (hcase_1:c19) => @Or.casesOn c77 c78 (fun (x:Or c77 c78) => c17) (Classical.em c77) (fun (hcase_2:c77) => @Or.casesOn c80 c81 (fun (x:Or c80 c81) => c17) (Classical.em c80) (fun (hcase_3:c80) => @Exists.intro Env c16 c56 (@And.intro (Run B compareFraction σ c56 ((40:Nat))) (c15 c56) (RunStep.mono B compareFraction σ c56 (c30 c88) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c56 c29 c88 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_42)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_43)) ?_)) (RunStep.seq B c42 c54 c2 c7 c56 c31 c87 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_44)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_45)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c56 c86 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_46)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_47)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c56 c85 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_48)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c56 c84 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_49)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_50)) hcase_2) (RunStep.ite_true B c50 c45 c44 c7 c56 c57 (RunStep.cond_eq_true B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_51)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_52)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1)))))))) (?nAX_g5438_0_0_53)) ?_)) fun (hcase_3:c81) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c93) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c93 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_54)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_55)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c92 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_56)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_57)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c91 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_58)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_59)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c90 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_60)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_true B c49 c51 c44 c7 c26 c89 (RunStep.cond_eq_true B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_61)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_62)) hcase_2) (RunStep.ite_false B c50 c45 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "right.n") (Expr.lit ((0:Nat))) c79 ((0:Nat)) (RunStep.eval_var B c7 "right.n" (?nAX_g5438_0_0_63)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_64)) hcase_3) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_65))))))))) (?nAX_g5438_0_0_66)) ?_)) fun (hcase_2:c78) => @Exists.intro Env c16 c26 (@And.intro (Run B compareFraction σ c26 ((40:Nat))) (c15 c26) (RunStep.mono B compareFraction σ c26 (c30 c97) ((40:Nat)) (RunStep.seq B (Com.assign "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d"))) (Com.seq c42 c54) σ c2 c26 c29 c97 (RunStep.assign B σ "cmp.u" (Expr.mul (Expr.var "left.n") (Expr.var "right.d")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.d") (Env.vars σ "left.n") (Env.vars σ "right.d") (RunStep.eval_var B σ "left.n" (?nAX_g5438_0_0_67)) (RunStep.eval_var B σ "right.d" (?nAX_g5438_0_0_68)) ?_)) (RunStep.seq B c42 c54 c2 c7 c26 c31 c96 (RunStep.assign B c2 "cmp.v" (Expr.mul (Expr.var "right.n") (Expr.var "left.d")) c6 (RunStep.eval_mul B c2 (Expr.var "right.n") (Expr.var "left.d") c4 c5 (RunStep.eval_var B c2 "right.n" (?nAX_g5438_0_0_69)) (RunStep.eval_var B c2 "left.d" (?nAX_g5438_0_0_70)) ?_)) (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c48 c53 c7 c26 c95 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c11 (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_71)) (RunStep.eval_var B c7 "right.s" (?nAX_g5438_0_0_72)) hcase) (RunStep.ite_false B c34 c45 c52 c7 c26 c94 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.lit ((1:Nat))) c9 ((1:Nat)) (RunStep.eval_var B c7 "left.s" (?nAX_g5438_0_0_73)) (RunStep.eval_lit B ((1:Nat)) c7 h1) hcase_1) (RunStep.ite_false B c49 c51 c44 c7 c26 c37 (RunStep.cond_eq_false B c7 (Expr.var "left.n") (Expr.lit ((0:Nat))) c76 ((0:Nat)) (RunStep.eval_var B c7 "left.n" (?nAX_g5438_0_0_74)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_75)) hcase_2) (RunStep.assign B c7 "cmp.le" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5438_0_0_76)))))))) (?nAX_g5438_0_0_77)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5438_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_60 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_61 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_62 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_63 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_64 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_65 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_66 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_67 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_68 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_69 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_70 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_71 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_72 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_73 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_74 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_75 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_76 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5438_0_0_77 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [leFlag]

theorem compareFraction_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) compareFraction
      (fun _ σ' => σ'.vars "cmp.le" ≤ 1∧
        (σ'.vars "cmp.le"=1↔ fractionValue s₁ n₁ d₁≤ fractionValue s₂ n₂ d₂)) 40:=by
  apply (compareFraction_flag_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂).post
  intro σ τ _ ht
  rw [ht]
  exact ⟨leFlag_le_one _ _ _ _ _ _,leFlag_correct _ _ _ _ _ _ hs₁ hs₂ hd₁pos hd₂pos⟩

end Lax455465Proofs.RamComparison

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

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowLP

open Lax455465.RationalEncoding Lax109476.LinearProgram

def vector {n:ℕ} (f:ℚ) (x:CommodityArc n→ ℚ):
    Fin (1 + (n * n) * (n * n))→ ℚ:=
  fun j => match (variableIndex n).symm j with
    | .inl _ => f
    | .inr a => x a

end Lax455465Proofs.DirectedFlowLP

end

section

namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

theorem zero_spec (B:ℕ) (h1:1 < B):
    Spec B (fun _ => True) zero (fun _ τ => FractionOutput 0 τ) 6:=by
  (expose_names;
    (refine fun (σ:Env) (a:True) => let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" ((0:Nat)); let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat→ Nat:=c4 c6; let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c7 c8; let c10:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B zero σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B zero σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B zero σ c3 (c7 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c10 c11) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g5825_0_0_0))) (RunStep.seq B c10 c11 c1 c2 c3 c6 c8 (RunStep.assign B c1 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g5825_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g5825_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5825_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5825_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

end Lax455465Proofs.RamFractionPrimitives

end

section

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val=s.val * n + t.val:=by
  simp [edgeIndex,finProdFinEquiv]
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

end Lax455465Proofs.FlowLpIndices

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

namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

theorem height_mul {M N:ℕ} {q r:ℚ} (hq:Height M q) (hr:Height N r):
    Height (M * N) (q * r):=by
  constructor
  · rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1)
  · rw [Rat.mul_den]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul hq.2 hr.2)

end Lax455465Proofs.LpInputSize

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

namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (words:List ℕ) (array cursor:String) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧
    Prefix (words ++ RamUnsignedBuffer.encode (qs.take (σ.vars index))) array σ∧
    σ.vars cursor=words.length+2*σ.vars index∧
    words.length+2*qs.length < (σ.arrs array).length

theorem command_spec (B K:ℕ) (R:Env→ Prop) (index limit array cursor:String)
    (qs:List ℚ≥0) (words:List ℕ) (body:Com) (h1:1 < B)
    (hlen:words.length+2*qs.length+2 < B)
    (hnum:∀ i, ∀ hi:i < qs.length,qs[i].num < B)
    (hden:∀ i, ∀ hi:i < qs.length,qs[i].den < B)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k,R σ→ R (σ.setVar index k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ RamRational.FractionOutput (qs[i]:ℚ) τ) K)
    (hbodyIndex:index∉ body.wvars) (hbodyPosition:cursor∉ body.wvars)
    (hbodyArray:array∉ body.warrs)
    (hemitIndex:index∉ (RamUnsignedEncoding.command array cursor).wvars)
    (hemitFrame:∀ {σ τ:Env} {k:ℕ},Run B (RamUnsignedEncoding.command array cursor) σ τ k→ R σ→ R τ)
    (hpositionIndex:index ≠ cursor) (hcursorDen:cursor ≠ "rat.d"):
    Spec B (fun σ => R σ∧ Prefix words array σ∧ σ.vars cursor=words.length∧
      words.length+2*qs.length < (σ.arrs array).length) (command index limit array cursor body)
      (fun _ τ => R τ∧ Prefix (words ++ RamUnsignedBuffer.encode qs) array τ∧
        τ.vars cursor=words.length+2*qs.length) ((K+22)*qs.length+6):=by
  have hcount:qs.length < B:=by omega
  have hstep:Spec B (fun σ => Invariant R index qs words array cursor σ∧ σ.vars index < qs.length)
      (step index array cursor body) (fun σ τ => Invariant R index qs words array cursor τ∧ τ.vars index=σ.vars index+1)
      (K+18):=by
    rintro σ ⟨⟨hR,hi,hp,hpos,hroom⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    have hi0:i≤ qs.length:=hi
    have hpLen:(words ++ RamUnsignedBuffer.encode (qs.take i)).length=words.length+2*i:=by
      simp only [List.length_append,RamUnsignedBuffer.length_encode,List.length_take,Nat.min_eq_left hi0]
    obtain ⟨ν,hproduce,hproduced⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(hproduce.frame_var index hbodyIndex).trans rfl
    have hposν:ν.vars cursor=words.length+2*i:=
      (hproduce.frame_var cursor hbodyPosition).trans hpos
    have hpν:Prefix (words ++ RamUnsignedBuffer.encode (qs.take i)) array ν:=by
      simpa only [Prefix,hproduce.frame_arr array hbodyArray] using hp
    have hroomν:words.length+2*qs.length < (ν.arrs array).length:=by
      rwa [RamFrames.run_array_length hproduce array]
    obtain ⟨μ,hemit,hemitted⟩:=RamUnsignedEncoding.command_spec B array cursor qs[i] (words ++ RamUnsignedBuffer.encode (qs.take i)) h1
      (hnum i hi') (hden i hi') (by rw [hpLen]; omega) hcursorDen ν
        ⟨hproduced.2,hpν,by rwa [hpLen],by rw [hpLen]; omega⟩
    have hiμ:μ.vars index=i:=(hemit.frame_var index hemitIndex).trans hiν
    have hRμ:=hemitFrame hemit hproduced.1
    have hroomμ:words.length+2*qs.length < (μ.arrs array).length:=by
      rwa [RamFrames.run_array_length hemit array]
    have hpμ:Prefix (words ++ RamUnsignedBuffer.encode (qs.take (i+1))) array μ:=by
      rw [List.take_succ_eq_append_getElem hi']
      simpa only [RamUnsignedBuffer.encode,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.append_assoc] using hemitted.1
    have hposμ:μ.vars cursor=words.length+2*(i+1):=by rw [hpLen] at hemitted; omega
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
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs words array cursor) qs.length (K+18)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ ⟨hR,hp,hpos,hroom⟩
  have hinit:Invariant R index qs words array cursor (σ.setVar index 0):=by
    refine ⟨hset σ 0 hR,by simp,?_,?_,?_⟩
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true,List.take_zero,RamUnsignedBuffer.encode,List.flatMap_nil,
        List.append_nil] using hp
    · simpa only [vars_setVar,if_neg (Ne.symm hpositionIndex),if_true,Nat.mul_zero,Nat.add_zero] using hpos
    · simpa only [arrs_setVar] using hroom
  obtain ⟨τ,hr,hpost⟩:=hscan σ hinit
  refine ⟨τ,by simpa [command,Nat.add_assoc] using hr,hpost.1.1,?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.1
  · simpa only [hpost.2] using hpost.1.2.2.2.1

end Lax455465Proofs.RamUnsignedVector

end

section

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

def Nonnegative {n:ℕ} (d:Distance n):Prop:= ∀ u v,0≤ d u v

end Lax455465Proofs.RationalDistances

end

section

namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

@[simp] theorem length_values {n:ℕ} (d:Matrix n):(values d).length=n*n:=List.length_ofFn

theorem value_at {n:ℕ} (d:Matrix n) (u v:Fin n):
    (values d)[(edgeIndex n (u,v)).val]'(by simpa only [length_values] using (edgeIndex n (u,v)).isLt)=d u v:=by
  simp only [values,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

end Lax455465Proofs.MetricMatrix

end

section

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

theorem indices_spec (B:ℕ) {n:ℕ} (u v:Fin n) (hn:n < B) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val) indices
      (fun _ τ => τ.vars "metric.u"=u.val∧ τ.vars "metric.v"=v.val) 10:=by
  have he:(edgeIndex n (u,v)).val < B:=(edgeIndex n (u,v)).isLt.trans hn2
  have hu:u.val < B:=u.isLt.trans hn
  have hv:v.val < B:=v.isLt.trans hn
  have hmul:u.val*n < B:=by rw [FlowLpIndices.edge_value] at he; omega
  have hdiv:=FlowLpIndices.edge_div u v
  have hmod:=FlowLpIndices.edge_mod u v
  rw [Nat.mod_def] at hmod
  rintro σ ⟨hnσ,heσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "metric.u") (@Fin.val n u)) (@Eq Nat (Env.vars τ "metric.v") (@Fin.val n v))) σ; let c1:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "metric.entry") (Env.vars σ "metric.n"); let c2:Env:=Env.setVar σ "metric.u" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "metric.entry"; let c5:Nat:=c3 "metric.u"; let c6:Nat:=c3 "metric.n"; let c7:Nat:=Nat.mul c5 c6; let c8:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c4 c7; let c9:Env:=Env.setVar c2 "metric.v" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))); let c13:Expr:=Expr.sub (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")); let c14:Nat:=c11 (Expr.size c13); let c15:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B indices σ σ' ((10:Nat))) (c0 σ')) c9 (@And.intro (Run B indices σ c9 ((10:Nat))) (c0 c9) (RunStep.mono B indices σ c9 (c10 c12 c14) ((10:Nat)) (RunStep.seq B (Com.assign "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))) (Com.assign "metric.v" c13) σ c2 c9 c12 c14 (RunStep.assign B σ "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n")) c1 (RunStep.eval_div B σ (Expr.var "metric.entry") (Expr.var "metric.n") (Env.vars σ "metric.entry") (Env.vars σ "metric.n") (RunStep.eval_var B σ "metric.entry" (?nAX_g6217_0_0_0)) (RunStep.eval_var B σ "metric.n" (?nAX_g6217_0_0_1)) ?_)) (RunStep.assign B c2 "metric.v" c13 c8 (RunStep.eval_sub B c2 (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) c4 c7 (RunStep.eval_var B c2 "metric.entry" (?nAX_g6217_0_0_2)) (RunStep.eval_mul B c2 (Expr.var "metric.u") (Expr.var "metric.n") c5 c6 (RunStep.eval_var B c2 "metric.u" ?_) (RunStep.eval_var B c2 "metric.n" (?nAX_g6217_0_0_3)) ?_) (?nAX_g6217_0_0_4)))) (?nAX_g6217_0_0_5)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6217_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6217_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FlowLpIndices.edge_value]

end Lax455465Proofs.RamDualDistancesInit

end

section

namespace Lax455465Proofs.RamUnsignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem copy_spec (B:ℕ) (q:ℚ≥0) (side:String) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:side ++ ".s" ≠ "rat.n" ∧ side ++ ".s" ≠ "rat.d" ∧ side ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (copy side)
      (fun _ τ => τ.vars (side ++ ".s")=0∧ τ.vars (side ++ ".n")=q.num∧
        τ.vars (side ++ ".d")=q.den) 6:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hsN:=Ne.symm hfresh.1
  have hsD:=Ne.symm hfresh.2.1
  have hnD:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) side; let c1:String:=c0 ".s"; let c2:String:=c0 ".n"; let c3:String:=c0 ".d"; let c4:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ c1) ((0:Nat))) (And (@Eq Nat (Env.vars τ c2) (NNRat.num q)) (@Eq Nat (Env.vars τ c3) (NNRat.den q)))) σ; let c5:Env:=Env.setVar σ c1 ((0:Nat)); let c6:Nat:=Env.vars c5 "rat.n"; let c7:Env:=Env.setVar c5 c2 c6; let c8:Nat:=Env.vars c7 "rat.d"; let c9:Env:=Env.setVar c7 c3 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.lit ((0:Nat)))); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c2 (Expr.var "rat.n"); let c17:Com:=Com.assign c3 (Expr.var "rat.d"); let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B (copy side) σ σ' ((6:Nat))) (c4 σ')) c9 (@And.intro (Run B (copy side) σ c9 ((6:Nat))) (c4 c9) (RunStep.mono B (copy side) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c1 (Expr.lit ((0:Nat)))) (Com.seq c16 c17) σ c5 c9 c12 c15 (RunStep.assign B σ c1 (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6226_0_0_0))) (RunStep.seq B c16 c17 c5 c7 c9 c13 c14 (RunStep.assign B c5 c2 (Expr.var "rat.n") c6 (RunStep.eval_var B c5 "rat.n" ?_)) (RunStep.assign B c7 c3 (Expr.var "rat.d") c8 (RunStep.eval_var B c7 "rat.d" ?_)))) (?nAX_g6226_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6226_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6226_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem value (q:ℚ≥0):fractionValue 0 q.num q.den=(q:ℚ):=by
  simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
  exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)

theorem add_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) addFraction
      (fun _ τ => FractionOutput ((a+b:ℚ≥0):ℚ) τ) (36*(a.den*b.den).size+96):=by
  simpa only [value,NNRat.coe_add] using addFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos

end Lax455465Proofs.RamUnsignedArithmetic

end

section

namespace Lax455465Proofs.RamArrayCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def Invariant (xs:List ℕ) (source target count:String) (σ:Env):Prop:=
  Prefix xs source σ∧ σ.vars count=xs.length∧ σ.vars "copy.i" ≤ xs.length∧
    xs.length≤ (σ.arrs target).length∧ Prefix (xs.take (σ.vars "copy.i")) target σ

theorem step_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Invariant xs source target count σ∧ σ.vars "copy.i" < xs.length)
      (step source target) (fun σ τ => Invariant xs source target count τ∧
        τ.vars "copy.i"=σ.vars "copy.i"+1) 8:=by
  rintro σ ⟨⟨hp,hc,hi,hroom,ht⟩,hlt⟩
  let i:=σ.vars "copy.i"
  have hi':i < xs.length:=hlt
  have hget:(σ.arrs source)[i]?=some xs[i]:=hp i hi'
  have hiB:i < B:=hi'.trans hlen
  have hvB:xs[i] < B:=hwords _ (List.getElem_mem hi')
  have rstore:Run B (.store target (.var "copy.i") (.get source (.var "copy.i"))) σ
      (σ.setArr target i xs[i]) 4:=Run.store (evalB_var hiB)
        (evalB_get (evalB_var hiB) hget hvB) (by omega)
  let ν:=σ.setArr target i xs[i]
  have rinc:Run B (.assign "copy.i" (.add (.var "copy.i") (.lit 1))) ν
      (ν.setVar "copy.i" (i+1)) 4:=Run.assign
    (evalB_bin (op:=.add) (evalB_var (by simpa [ν] using hiB)) (evalB_lit h1) (by dsimp [Bop.apply]; omega))
  have hprefix:Prefix (xs.take (i+1)) target ν:=by
    intro j hj
    have hj':j < i+1:=by simp only [List.length_take] at hj; omega
    have hxj:j < xs.length:=by omega
    have htake:(xs.take (i+1))[j]=xs[j]:=List.getElem_take
    simp only [ν,arrs_setArr,if_true]
    by_cases he:i=j
    · subst j
      rw [List.getElem?_set_self (by omega)]
      exact congrArg some htake.symm
    · rw [List.getElem?_set_ne he]
      have hji:j < i:=by omega
      have hjtake:j < (xs.take i).length:=by simp only [List.length_take]; omega
      exact (ht j hjtake).trans (congrArg some (by simp only [List.getElem_take,htake]))
  refine ⟨ν.setVar "copy.i" (i+1),rstore.seq rinc,?_,?_⟩
  · refine ⟨?_,?_,by simp; omega,?_,?_⟩
    · simpa only [Prefix,ν,arrs_setVar,arrs_setArr,if_neg harray] using hp
    · simpa only [ν,vars_setVar,vars_setArr,if_neg hcount] using hc
    · simpa only [ν,length_arrs_setArr,arrs_setVar] using hroom
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_pos rfl,if_true] using hprefix
  · simp [i]

theorem command_spec (B:ℕ) (xs:List ℕ) (source target count:String)
    (h1:1 < B) (hlen:xs.length < B) (hwords:∀ x∈ xs,x < B)
    (harray:source ≠ target) (hcount:count ≠ "copy.i"):
    Spec B (fun σ => Prefix xs source σ∧ σ.vars count=xs.length∧
      xs.length≤ (σ.arrs target).length) (command source target count)
      (fun _ τ => Prefix xs source τ∧ Prefix xs target τ) (12*xs.length+6):=by
  have hloop:=Spec.forRangeZero "copy.i" count (Invariant xs source target count) xs.length 8 hlen
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B xs source target count h1 hlen hwords harray hcount)
  rintro σ ⟨hp,hc,hroom⟩
  have hinit:Invariant xs source target count (σ.setVar "copy.i" 0):=by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [Prefix,arrs_setVar] using hp
    · simpa only [vars_setVar,if_neg hcount] using hc
    · simpa only [arrs_setVar] using hroom
    · intro i hi
      simp only [vars_setVar,if_true,List.take_zero,List.length_nil] at hi
      omega
  obtain ⟨τ,hr,hpost⟩:=hloop σ hinit
  exact ⟨τ,by simpa only [command] using hr,hpost.1.1,
    by simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2⟩

end Lax455465Proofs.RamArrayCopy

end

section

namespace Lax455465Proofs.RamArrayProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B M:ℕ) (leftArray rightArray:String) (xs ys:List ℚ≥0) (i:ℕ)
    (hxi:i < xs.length) (hyi:i < ys.length) (hB:2*M^2+3 < B) (hindex:2*i+1 < B)
    (hxn:xs[i].num≤ M) (hxd:xs[i].den≤ M) (hyn:ys[i].num≤ M) (hyd:ys[i].den≤ M):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode xs) leftArray σ∧
      Prefix (RamUnsignedBuffer.encode ys) rightArray σ∧ σ.vars "sum.i"=i)
      (command leftArray rightArray)
      (fun _ τ => FractionOutput ((xs[i]*ys[i]:ℚ≥0):ℚ) τ)
      (36*(xs[i].den*ys[i].den).size+104):=by
  have hM:M < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  rintro σ ⟨hxp,hyp,hi⟩
  obtain ⟨ν,rx,px⟩:=RamUnsignedBuffer.read_spec B leftArray "sum.i" xs i hxi h2 hindex
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) σ ⟨hxp,hi⟩
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B xs[i] "left" (by omega)
    (hxn.trans_lt hM) (hxd.trans_lt hM) (by decide) ν px.1
  have hypμ:Prefix (RamUnsignedBuffer.encode ys) rightArray μ:=by
    have rr:=rx.seq rl
    simpa only [Prefix,rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using hyp
  have hiμ:μ.vars "sum.i"=i:=by
    have rr:=rx.seq rl
    exact (rr.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars])).trans hi
  obtain ⟨ξ,ry,py⟩:=RamUnsignedBuffer.read_spec B rightArray "sum.i" ys i hyi h2 hindex
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) μ ⟨hypμ,hiμ⟩
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B ys[i] "right" (by omega)
    (hyn.trans_lt hM) (hyd.trans_lt hM) (by decide) ξ py.1
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=xs[i].num∧ η.vars "left.d"=xs[i].den:=by
    have run:=ry.seq rr
    simpa only [run.frame_var "left.s" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.n" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),
      run.frame_var "left.d" (by simp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rm,pm⟩:=multiplyFraction_spec B M 0 xs[i].num xs[i].den 0 ys[i].num ys[i].den
    hB (by omega) (by omega) hxn hxd hyn hyd xs[i].den_pos ys[i].den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,(rx.seq (rl.seq (ry.seq (rr.seq rm)))).mono (by omega),?_⟩
  simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using pm

end Lax455465Proofs.RamArrayProduct

end

section

namespace Lax455465Proofs.RamUnsignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def Stored (q:ℚ≥0) (σ:Env):Prop:=σ.vars "fold.n"=q.num∧ σ.vars "fold.d"=q.den

theorem load_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) load (fun _ τ => τ.vars "right.s"=0∧ τ.vars "right.n"=q.num∧ τ.vars "right.d"=q.den) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "right.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "right.n") (NNRat.num q)) (@Eq Nat (Env.vars τ "right.d") (NNRat.den q)))) σ; let c1:Env:=Env.setVar σ "right.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "right.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "right.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; let c12:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B load σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B load σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B load σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "right.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6296_0_0_0))) (RunStep.seq B (Com.assign "right.n" (Expr.var "fold.n")) (Com.assign "right.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "right.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6296_0_0_1))) (RunStep.assign B c3 "right.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6296_0_0_2))))) (?nAX_g6296_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6296_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6296_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem save_spec (B:ℕ) (q:ℚ≥0) (hn:q.num < B) (hd:q.den < B):
    Spec B (FractionOutput (q:ℚ)) save (fun _ τ => Stored q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" c0; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat:=c2 ((1:Nat)); let c4:Nat:=c3 (Expr.size (Expr.var "rat.n")); let c5:Nat:=c3 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B save σ σ' ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ σ')) c1 (@And.intro (Run B save σ c1 ((4:Nat))) ((fun (x τ:Env) => Stored q τ) σ c1) (RunStep.mono B save σ c1 (c2 c4 c5) ((4:Nat)) (RunStep.seq B (Com.assign "fold.n" (Expr.var "rat.n")) (Com.assign "fold.d" (Expr.var "rat.d")) σ (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) c1 c4 c5 (RunStep.assign B σ "fold.n" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6297_0_0_0))) (RunStep.assign B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "fold.d" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "fold.n" (Env.vars σ "rat.n")) "rat.d" (?nAX_g6297_0_0_1)))) (?nAX_g6297_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6297_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6297_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

theorem finish_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (Stored q) finish (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "fold.n"; let c3:Env:=Env.setVar c1 "rat.n" c2; let c4:Nat:=Env.vars c3 "fold.d"; let c5:Env:=Env.setVar c3 "rat.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "fold.n")); let c10:Nat:=c7 (Expr.size (Expr.var "fold.d")); let c11:Nat:=c6 c9 c10; @Exists.intro Env (fun (σ':Env) => And (Run B finish σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B finish σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B finish σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6298_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "fold.n")) (Com.assign "rat.d" (Expr.var "fold.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "rat.n" (Expr.var "fold.n") c2 (RunStep.eval_var B c1 "fold.n" (?nAX_g6298_0_0_1))) (RunStep.assign B c3 "rat.d" (Expr.var "fold.d") c4 (RunStep.eval_var B c3 "fold.d" (?nAX_g6298_0_0_2))))) (?nAX_g6298_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6298_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6298_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored,FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem combine_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hsn:(a+b).num < B) (hsd:(a+b).den < B):
    Spec B (fun σ => FractionOutput (a:ℚ) σ∧ Stored b σ) combine
      (fun _ τ => Stored (a+b) τ) (36*(M^2).size+112):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) σ ha
  have hbν:Stored b ν:=by
    simpa only [Stored,rleft.frame_var "fold.n" (by decide),rleft.frame_var "fold.d" (by decide)] using hb
  obtain ⟨μ,rright,pright⟩:=load_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hbν
  have paμ:μ.vars "left.s"=0∧ μ.vars "left.n"=a.num∧ μ.vars "left.d"=a.den:=by
    simpa only [rright.frame_var "left.s" (by decide),rright.frame_var "left.n" (by decide),rright.frame_var "left.d" (by decide),String.reduceAppend] using pleft
  obtain ⟨ξ,radd,padd⟩:=RamUnsignedArithmetic.add_spec B M a b hB han had hbn hbd μ
    ⟨paμ.1,paμ.2.1,paμ.2.2,pright⟩
  obtain ⟨τ,rsave,psave⟩:=save_spec B (a+b) hsn hsd ξ padd
  refine ⟨τ,(rleft.seq (rright.seq (radd.seq rsave))).mono ?_,psave⟩
  have hprod:a.den*b.den≤ M^2:=by nlinarith [Nat.mul_le_mul had hbd]
  have hsize:=Nat.size_le_size hprod
  omega

def Invariant (R:Env→ Prop) (index:String) (qs:List ℚ≥0) (σ:Env):Prop:=
  R σ∧ σ.vars index≤ qs.length∧ Stored (qs.take (σ.vars index)).sum σ

set_option maxHeartbeats 0 in

theorem command_spec (B M K:ℕ) (R:Env→ Prop) (index limit:String)
    (qs:List ℚ≥0) (body:Com) (hB:2*M^2+3 < B) (hlen:qs.length < B)
    (hnum:∀ q∈ qs,q.num≤ M) (hden:∀ q∈ qs,q.den≤ M)
    (hprefixNum:∀ i, (qs.take i).sum.num≤ M) (hprefixDen:∀ i, (qs.take i).sum.den≤ M)
    (hlimit:∀ σ,R σ→ σ.vars limit=qs.length)
    (hset:∀ σ k name,R σ→ name=index∨ name="fold.n" ∨ name="fold.d" → R (σ.setVar name k))
    (hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => R σ∧ σ.vars index=i) body
        (fun _ τ => R τ∧ FractionOutput (qs[i]:ℚ) τ) K)
    (hfresh:index ≠ "fold.n" ∧ index ≠ "fold.d" ∧ index∉ combine.wvars)
    (hbodyIndex:index∉ body.wvars) (hbodySum:"fold.n" ∉ body.wvars∧ "fold.d" ∉ body.wvars)
    (hcombineFrame:∀ {σ τ:Env} {k:ℕ},Run B combine σ τ k→ R σ→ R τ)
    (hfinishFrame:∀ {σ τ:Env} {k:ℕ},Run B finish σ τ k→ R σ→ R τ):
    Spec B R (command index limit body)
      (fun _ τ => R τ∧ FractionOutput ((qs.sum:ℚ≥0):ℚ) τ)
      ((K+36*(M^2).size+120)*qs.length+16):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hstep:Spec B (fun σ => Invariant R index qs σ∧ σ.vars index < qs.length)
      (step index body) (fun σ τ => Invariant R index qs τ∧ τ.vars index=σ.vars index+1)
      (K+36*(M^2).size+116):=by
    rintro σ ⟨⟨hR,hi,hstored⟩,hlt⟩
    let i:=σ.vars index
    have hi':i < qs.length:=hlt
    obtain ⟨ν,rbody,pbody⟩:=hbody i hi' σ ⟨hR,rfl⟩
    have hiν:ν.vars index=i:=(rbody.frame_var index hbodyIndex).trans rfl
    have hstoredν:Stored (qs.take i).sum ν:=by
      simpa only [Stored,rbody.frame_var "fold.n" hbodySum.1,rbody.frame_var "fold.d" hbodySum.2] using hstored
    have hq:qs[i]∈ qs:=List.getElem_mem hi'
    have hsum:qs[i]+(qs.take i).sum=(qs.take (i+1)).sum:=by
      rw [List.take_succ_eq_append_getElem hi',List.sum_append,List.sum_singleton,add_comm]
    obtain ⟨μ,rcombine,pcombine⟩:=combine_spec B M qs[i] (qs.take i).sum hB
      (hnum _ hq) (hden _ hq) (hprefixNum i) (hprefixDen i)
      (by rw [hsum]; exact (hprefixNum (i+1)).trans_lt hM)
      (by rw [hsum]; exact (hprefixDen (i+1)).trans_lt hM) ν ⟨pbody.2,hstoredν⟩
    have hiμ:μ.vars index=i:=(rcombine.frame_var index hfresh.2.2).trans hiν
    have hRμ:=hcombineFrame rcombine pbody.1
    have hinc:Run B (.assign index (.add (.var index) (.lit 1))) μ (μ.setVar index (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨μ.setVar index (i+1),(rbody.seq (rcombine.seq hinc)).mono (by omega),?_,?_⟩
    · refine ⟨hset μ (i+1) index hRμ (Or.inl rfl),by simp; omega,?_⟩
      simpa only [Stored,vars_setVar,if_neg (Ne.symm hfresh.1),if_neg (Ne.symm hfresh.2.1),if_pos rfl,if_true,hsum] using pcombine
    · simp [i]
  have hscan:=Spec.forRangeZero index limit (Invariant R index qs) qs.length
    (K+36*(M^2).size+116) hlen (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "fold.n" 0).setVar "fold.d" 1
  have rinit:Run B init σ ν 4:=by
    exact (Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit h1))
  have hRν:R ν:=hset _ 1 "fold.d" (hset σ 0 "fold.n" hR (Or.inr (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have hinvariant:Invariant R index qs (ν.setVar index 0):=by
    refine ⟨hset ν 0 index hRν (Or.inl rfl),by simp,?_⟩
    simp [Stored,ν,Ne.symm hfresh.1,Ne.symm hfresh.2.1]
  obtain ⟨μ,rscan,pscan⟩:=hscan ν hinvariant
  have hstoredμ:Stored qs.sum μ:=by simpa only [pscan.2,List.take_length] using pscan.1.2.2
  have hfinalNum:qs.sum.num≤ M:=by simpa only [List.take_length] using hprefixNum qs.length
  have hfinalDen:qs.sum.den≤ M:=by simpa only [List.take_length] using hprefixDen qs.length
  obtain ⟨τ,rfinish,pfinish⟩:=finish_spec B qs.sum h1 (hfinalNum.trans_lt hM) (hfinalDen.trans_lt hM) μ hstoredμ
  refine ⟨τ,(rinit.seq (rscan.seq rfinish)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),hfinishFrame rfinish pscan.1.1,pfinish⟩

end Lax455465Proofs.RamUnsignedSum

end

section

namespace Lax455465Proofs.RamProductSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (leftArray rightArray:String) (xs ys:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=xs.length∧ Prefix (RamUnsignedBuffer.encode xs) leftArray σ∧
    Prefix (RamUnsignedBuffer.encode ys) rightArray σ

theorem value_at (xs ys:List ℚ≥0) (hlen:ys.length=xs.length) (i:ℕ) (hi:i < xs.length):
    (products xs ys)[i]'(by simpa only [products,List.length_ofFn] using hi) =
      xs[i]*ys[i]'(by omega):=by
  simp only [products,List.getElem_ofFn,List.getD_eq_get ys 0 (⟨i,by omega⟩:Fin ys.length)]
  rfl

theorem command_spec (B M:ℕ) (leftArray rightArray:String) (xs ys:List ℚ≥0)
    (hlen:ys.length=xs.length) (hB:2*M^2+3 < B) (hindex:2*xs.length+2 < B)
    (hxn:∀ q∈ xs,q.num≤ M) (hxd:∀ q∈ xs,q.den≤ M)
    (hyn:∀ q∈ ys,q.num≤ M) (hyd:∀ q∈ ys,q.den≤ M)
    (hpn:∀ q∈ products xs ys,q.num≤ M) (hpd:∀ q∈ products xs ys,q.den≤ M)
    (hprefixNum:∀ i, ((products xs ys).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((products xs ys).take i).sum.den≤ M):
    Spec B (Context leftArray rightArray xs ys) (command leftArray rightArray)
      (fun _ τ => Context leftArray rightArray xs ys τ∧ FractionOutput (((products xs ys).sum:ℚ≥0):ℚ) τ)
      ((72*(M^2).size+224)*xs.length+16):=by
  have hlength:(products xs ys).length=xs.length:=List.length_ofFn
  have hbody:∀ i, ∀ hi:i < (products xs ys).length,
      Spec B (fun σ => Context leftArray rightArray xs ys σ∧ σ.vars "sum.i"=i)
        (RamArrayProduct.command leftArray rightArray)
        (fun _ τ => Context leftArray rightArray xs ys τ∧ FractionOutput ((products xs ys)[i]:ℚ) τ)
        (36*(M^2).size+104):=by
    intro i hi σ hσ
    have hx:i < xs.length:=by rwa [hlength] at hi
    have hy:i < ys.length:=by omega
    have hxm:xs[i]∈ xs:=List.getElem_mem hx
    have hym:ys[i]∈ ys:=List.getElem_mem hy
    obtain ⟨τ,rr,pr⟩:=RamArrayProduct.command_spec B M leftArray rightArray xs ys i hx hy hB
      (by omega) (hxn _ hxm) (hxd _ hxm) (hyn _ hym) (hyd _ hym) σ ⟨hσ.1.2.1,hσ.1.2.2,hσ.2⟩
    have hcost:(xs[i].den*ys[i].den).size≤ (M^2).size:=
      Nat.size_le_size (by nlinarith [Nat.mul_le_mul (hxd _ hxm) (hyd _ hym)])
    refine ⟨τ,rr.mono (by omega),?_,?_⟩
    · simpa only [Context,Prefix,rr.frame_var "sum.count" (by
        dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using hσ.1
    · simpa only [value_at xs ys hlen i hx] using pr
  have hf:=RamUnsignedSum.command_spec B M (36*(M^2).size+104)
    (Context leftArray rightArray xs ys) "sum.i" "sum.count" (products xs ys)
    (RamArrayProduct.command leftArray rightArray) hB (by rw [hlength]; omega) hpn hpd hprefixNum hprefixDen
    (fun σ h => by simpa only [hlength] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using h)
  unfold command
  rw [hlength] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamProductSum

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionVolume

theorem edgePortion_le (length base radius:ℚ):edgePortion length base radius≤ length:=
  min_le_left _ _

end Lax455465Proofs.RegionVolume

end

section

namespace Lax455465Proofs.RegionBudget

theorem steps_pos (p:ℕ):0 < steps p:=by unfold steps; omega

end Lax455465Proofs.RegionBudget

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionCharging

open RegionVolume

def erase {n:ℕ} (capacity:Matrix n) (S:Finset (Fin n)):Matrix n:=
  fun u v => if u∈ S∨ v∈ S then 0 else capacity u v

def chosenBall {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (direction:ℚ→ Bool) (r:ℚ):Finset (Fin n):=
  if direction r then ball outDistance r else ball inDistance r

theorem weight_nonnegative {n:ℕ} (capacity length:Matrix n)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    0≤ weight capacity length:=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hc u v) (hl u v)

theorem weight_drop {n:ℕ} (capacity length:Matrix n) (S:Finset (Fin n)):
    weight capacity length - weight (erase capacity S) length =
      ∑ u, ∑ v,if u∈ S∨ v∈ S then capacity u v * length u v else 0:=by
  unfold weight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  unfold erase
  split_ifs <;> ring

private theorem portion_outside (length base radius:ℚ)
    (hl:0≤ length) (h:radius≤ base):edgePortion length base radius=0:=by
  unfold edgePortion
  rw [max_eq_right (sub_nonpos.mpr h),min_eq_right hl]

theorem volume_bound {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed r:ℚ) (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    volume capacity length distance seed r≤
      seed + (weight capacity length - weight (erase capacity (ball distance r)) length):=by
  rw [weight_drop]
  unfold volume
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  by_cases hu:u∈ ball distance r
  · rw [if_pos (Or.inl hu)]
    exact mul_le_mul_of_nonneg_left (edgePortion_le _ _ _) (hc u v)
  · have hout:r≤ distance u:=by simpa [ball,not_lt] using hu
    rw [portion_outside _ _ _ (hl u v) hout,mul_zero]
    split_ifs
    · exact mul_nonneg (hc u v) (hl u v)
    · exact le_rfl

theorem weight_transpose {n:ℕ} (capacity length:Matrix n):
    weight (fun u v => capacity v u) (fun u v => length v u)=weight capacity length:=by
  unfold weight
  rw [Finset.sum_comm]

private theorem erase_transpose {n:ℕ} (capacity:Matrix n) (S:Finset (Fin n)):
    erase (fun u v => capacity v u) S=fun u v => erase capacity S v u:=by
  funext u v
  simp only [erase,or_comm]

theorem selected_volume_bound {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed r:ℚ) (direction:ℚ→ Bool)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    RegionSearch.selectedVolume capacity length outDistance inDistance seed direction r≤
      seed + (weight capacity length -
        weight (erase capacity (chosenBall outDistance inDistance direction r)) length):=by
  cases hdir:direction r with
  | true =>
    simpa only [RegionSearch.selectedVolume,chosenBall,hdir,Bool.true_eq, ↓reduceIte] using
      volume_bound capacity length outDistance seed r hc hl
  | false =>
    have h:=volume_bound (fun u v => capacity v u) (fun u v => length v u)
      inDistance seed r (fun u v => hc v u) (fun u v => hl v u)
    rw [erase_transpose,weight_transpose capacity length,
      weight_transpose (erase capacity (ball inDistance r)) length] at h
    simpa only [RegionSearch.selectedVolume,chosenBall,hdir,Bool.false_eq_true, ↓reduceIte] using h

theorem total_boundary_bound (cost boundary volume:ℕ→ ℚ) (k:ℕ) (seed beta:ℚ)
    (hbeta:0≤ beta) (hfinal:0≤ cost k)
    (hvolume:∀ j < k,volume j≤ seed + (cost j - cost (j + 1)))
    (hboundary:∀ j < k,boundary j≤ beta * volume j):
    (∑ j∈ Finset.range k,boundary j)≤ beta * ((k:ℚ) * seed + cost 0):=by
  have hsum:(∑ j∈ Finset.range k,boundary j)≤
      ∑ j∈ Finset.range k,beta * (seed + (cost j - cost (j + 1))):=by
    apply Finset.sum_le_sum
    intro j hj
    exact (hboundary j (Finset.mem_range.mp hj)).trans
      (mul_le_mul_of_nonneg_left (hvolume j (Finset.mem_range.mp hj)) hbeta)
  have htel:(∑ j∈ Finset.range k, (cost j - cost (j + 1)))=cost 0 - cost k:=by
    calc
      (∑ j∈ Finset.range k, (cost j - cost (j + 1))) =
          -(∑ j∈ Finset.range k, (cost (j + 1) - cost j)):=by
        rw [← Finset.sum_neg_distrib]
        simp only [neg_sub]
      _=cost 0 - cost k:=by rw [Finset.sum_range_sub]; ring
  simp_rw [mul_add] at hsum
  rw [Finset.sum_add_distrib] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  rw [htel] at hsum
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  nlinarith

theorem total_boundary_normalized (cost boundary volume:ℕ→ ℚ) (k p:ℕ) (beta:ℚ)
    (hp:0 < p) (hk:k≤ p) (hbeta:0≤ beta)
    (hstart:0≤ cost 0) (hfinal:0≤ cost k)
    (hvolume:∀ j < k,volume j≤ cost 0 / p + (cost j - cost (j + 1)))
    (hboundary:∀ j < k,boundary j≤ beta * volume j):
    (∑ j∈ Finset.range k,boundary j)≤ 2 * beta * cost 0:=by
  have h:=total_boundary_bound cost boundary volume k (cost 0 / p) beta hbeta hfinal hvolume hboundary
  have hpq:(0:ℚ) < p:=by exact_mod_cast hp
  have hkq:(k:ℚ)≤ p:=by exact_mod_cast hk
  have hseed:0≤ cost 0 / p:=div_nonneg hstart hpq.le
  have hks:=mul_le_mul_of_nonneg_right hkq hseed
  have hid:(p:ℚ) * (cost 0 / p)=cost 0:=by field_simp [ne_of_gt hpq]
  rw [hid] at hks
  have hmul:=mul_le_mul_of_nonneg_left hks hbeta
  nlinarith

end Lax455465Proofs.RegionCharging

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionOrdering

open RegionVolume

def position (k:ℕ) (orientation:ℕ→ Bool) (j:ℕ):ℕ:=
  if j=k then k else if orientation j then 2 * k - j else j

def lateCut {n k:ℕ} (index:Fin n→ Fin (k + 1)) (orientation:ℕ→ Bool)
    (threshold:ℕ):Finset (Fin n):=
  Finset.univ.filter fun v => threshold < position k orientation (index v).val

def edgeCharge {n k:ℕ} (capacity:Matrix n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (j:Fin k) (u v:Fin n):ℚ:=
  if orientation j.val then
    if (index u).val=j.val∧ j.val < (index v).val then capacity u v else 0
  else if (index v).val=j.val∧ j.val < (index u).val then capacity u v else 0

def chargedBoundary {n k:ℕ} (capacity:Matrix n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (j:Fin k):ℚ:= ∑ u, ∑ v,edgeCharge capacity index orientation j u v

def cutCapacity {n:ℕ} (capacity:Matrix n) (S:Finset (Fin n)):ℚ:=
  ∑ u, ∑ v,if u∈ S∧ v∉ S then capacity u v else 0

private theorem earlier_outward (k:ℕ) (orientation:ℕ→ Bool) (i j:ℕ)
    (hij:i < j) (hj:j≤ k) (hi:orientation i=true):
    position k orientation j < position k orientation i:=by
  unfold position
  split_ifs <;> (try simp_all) <;> omega

private theorem earlier_inward (k:ℕ) (orientation:ℕ→ Bool) (i j:ℕ)
    (hij:i < j) (hj:j≤ k) (hi:orientation i=false):
    position k orientation i < position k orientation j:=by
  unfold position
  split_ifs <;> (try simp_all) <;> omega

theorem backward_arc_charged {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (orientation:ℕ→ Bool) (u v:Fin n)
    (hback:position k orientation (index v).val < position k orientation (index u).val):
    ∃ j:Fin k,edgeCharge capacity index orientation j u v=capacity u v:=by
  have hneq:(index u).val ≠ (index v).val:=by
    intro heq
    rw [heq] at hback
    exact (lt_irrefl _) hback
  rcases Nat.lt_or_gt_of_ne hneq with huv | hvu
  · have hik:(index u).val < k:=by have h:=(index v).isLt; omega
    have hout:orientation (index u).val=true:=by
      cases heq:orientation (index u).val with
      | true => rfl
      | false =>
        have hforward:=earlier_inward k orientation _ _ huv (by have h:=(index v).isLt; omega) heq
        omega
    refine ⟨⟨(index u).val,hik⟩, ?_⟩
    simp only [edgeCharge,hout, ↓reduceIte,huv,and_self]
  · have hik:(index v).val < k:=by have h:=(index u).isLt; omega
    have hin:orientation (index v).val=false:=by
      cases heq:orientation (index v).val with
      | false => rfl
      | true =>
        have hforward:=earlier_outward k orientation _ _ hvu (by have h:=(index u).isLt; omega) heq
        omega
    refine ⟨⟨(index v).val,hik⟩, ?_⟩
    simp only [edgeCharge,hin,Bool.false_eq_true, ↓reduceIte,hvu,and_self]

theorem edgeCharge_nonnegative {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (orientation:ℕ→ Bool) (j:Fin k) (u v:Fin n)
    (hc:∀ u v,0≤ capacity u v):0≤ edgeCharge capacity index orientation j u v:=by
  unfold edgeCharge
  split_ifs <;> first | exact hc u v | exact le_rfl

theorem late_cut_bound {n k:ℕ} (capacity:Matrix n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (threshold:ℕ) (hc:∀ u v,0≤ capacity u v):
    cutCapacity capacity (lateCut index orientation threshold)≤
      ∑ j:Fin k,chargedBoundary capacity index orientation j:=by
  have hpoint:∀ u v:Fin n,
      (if u∈ lateCut index orientation threshold∧ v∉ lateCut index orientation threshold
        then capacity u v else 0)≤ ∑ j:Fin k,edgeCharge capacity index orientation j u v:=by
    intro u v
    split_ifs with hcross
    · have hu:threshold < position k orientation (index u).val:=(Finset.mem_filter.mp hcross.1).2
      have hv:position k orientation (index v).val≤ threshold:=by
        simpa only [lateCut,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hcross.2
      obtain ⟨j,hj⟩:=backward_arc_charged capacity index orientation u v (lt_of_le_of_lt hv hu)
      rw [← hj]
      exact Finset.single_le_sum (fun i _ => edgeCharge_nonnegative capacity index orientation i u v hc)
        (Finset.mem_univ j)
    · exact Finset.sum_nonneg fun j _ => edgeCharge_nonnegative capacity index orientation j u v hc
  unfold cutCapacity chargedBoundary
  have hsum:(∑ u, ∑ v,if u∈ lateCut index orientation threshold∧ v∉ lateCut index orientation threshold
      then capacity u v else 0)≤ ∑ u, ∑ v, ∑ j:Fin k,edgeCharge capacity index orientation j u v:=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpoint u v
  conv_rhs at hsum =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  conv_rhs at hsum => rw [Finset.sum_comm]
  exact hsum

end Lax455465Proofs.RegionOrdering

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionFrontier

open RegionVolume RegionOrdering

def residual {n k:ℕ} (capacity:Matrix n) (index:Fin n→ Fin (k + 1))
    (j:ℕ):Matrix n:=
  fun u v => if j≤ (index u).val∧ j≤ (index v).val then capacity u v else 0

private theorem outgoing_term {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (j:ℕ) (S:Finset (Fin n))
    (hS:∀ v,j≤ (index v).val→ (v∈ S↔ (index v).val=j)) (u v:Fin n):
    (if u∈ S∧ v∉ S then residual capacity index j u v else 0) =
      if (index u).val=j∧ j < (index v).val then capacity u v else 0:=by
  by_cases hu:j≤ (index u).val
  · by_cases hv:j≤ (index v).val
    · have hcond:((index u).val=j∧ ¬ (index v).val=j)↔
          ((index u).val=j∧ j < (index v).val):=by omega
      simp only [residual,hu,hv,and_self, ↓reduceIte,hS u hu,hS v hv,hcond]
    · have hnot:¬ j < (index v).val:=by omega
      simp [residual,hv,hnot]
  · have hnot:(index u).val ≠ j:=by omega
    simp [residual,hu,hnot]

theorem outgoing_boundary {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (j:ℕ) (S:Finset (Fin n))
    (hS:∀ v,j≤ (index v).val→ (v∈ S↔ (index v).val=j)):
    cutCapacity (residual capacity index j) S =
      ∑ u, ∑ v,if (index u).val=j∧ j < (index v).val then capacity u v else 0:=by
  unfold cutCapacity
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  exact outgoing_term capacity index j S hS u v

theorem incoming_boundary {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (j:ℕ) (S:Finset (Fin n))
    (hS:∀ v,j≤ (index v).val→ (v∈ S↔ (index v).val=j)):
    cutCapacity (fun u v => residual capacity index j v u) S =
      ∑ u, ∑ v,if (index v).val=j∧ j < (index u).val then capacity u v else 0:=by
  have ht:(fun u v => residual capacity index j v u) =
      residual (fun u v => capacity v u) index j:=by
    funext u v
    simp only [residual,and_comm]
  rw [ht,outgoing_boundary (fun u v => capacity v u) index j S hS,Finset.sum_comm]

def orientedBoundary {n:ℕ} (capacity:Matrix n) (S:Finset (Fin n)) (outward:Bool):ℚ:=
  if outward then cutCapacity capacity S else cutCapacity (fun u v => capacity v u) S

theorem charged_eq_boundary {n k:ℕ} (capacity:Matrix n)
    (index:Fin n→ Fin (k + 1)) (orientation:ℕ→ Bool) (j:Fin k)
    (S:Finset (Fin n))
    (hS:∀ v,j.val≤ (index v).val→ (v∈ S↔ (index v).val=j.val)):
    chargedBoundary capacity index orientation j =
      orientedBoundary (residual capacity index j.val) S (orientation j.val):=by
  cases hd:orientation j.val with
  | true =>
    simp only [chargedBoundary,edgeCharge,orientedBoundary,hd, ↓reduceIte]
    exact (outgoing_boundary capacity index j.val S hS).symm
  | false =>
    simp only [chargedBoundary,edgeCharge,orientedBoundary,hd,Bool.false_eq_true, ↓reduceIte]
    exact (incoming_boundary capacity index j.val S hS).symm

theorem ball_boundary {n:ℕ} (capacity:Matrix n) (distance:Fin n→ ℚ) (r:ℚ):
    boundary capacity distance r=cutCapacity capacity (RegionCharging.ball distance r):=by
  unfold boundary cutCapacity RegionCharging.ball
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_lt]

theorem selected_boundary {n:ℕ} (capacity:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (direction:ℚ→ Bool) (r:ℚ):
    RegionSearch.selectedBoundary capacity outDistance inDistance direction r =
      orientedBoundary capacity (RegionCharging.chosenBall outDistance inDistance direction r) (direction r):=by
  cases hd:direction r <;>
    simp only [RegionSearch.selectedBoundary,RegionCharging.chosenBall,orientedBoundary,
      hd,Bool.false_eq_true, ↓reduceIte,ball_boundary]

end Lax455465Proofs.RegionFrontier

end

section

open scoped BigOperators NNRat NNReal

namespace Lax455465Proofs.CutSweeps

open Lax455465.ProductNetwork Lax455465.RationalEncoding

instance {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    Decidable (admissibleQ I S):=inferInstanceAs (Decidable (_∧ _))

theorem massQ_nonneg {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    0≤ massQ I S:=by
  exact Finset.sum_nonneg (fun v _ => NNRat.coe_nonneg (I.weight v))

theorem capacityQ_nonneg {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    0≤ capacityQ I S:=by
  exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg
    (fun v _ => NNRat.coe_nonneg (I.capacity u v)))

theorem admissibleQ_iff_product_pos {n:ℕ} (I:RationalInstance n)
    (S:Finset (Fin n)):
    admissibleQ I S↔ 0 < massQ I S * massQ I Sᶜ:=by
  constructor
  · rintro ⟨hS,hSc⟩
    exact mul_pos hS hSc
  · intro h
    have hS:=massQ_nonneg I S
    have hSc:=massQ_nonneg I Sᶜ
    constructor <;> nlinarith

theorem demand_zero_of_not_admissible {n:ℕ} (I:RationalInstance n)
    (S:Finset (Fin n)) (h:¬ admissibleQ I S):
    massQ I S * massQ I Sᶜ=0:=by
  have hnonneg:=mul_nonneg (massQ_nonneg I S) (massQ_nonneg I Sᶜ)
  have hnot:¬ 0 < massQ I S * massQ I Sᶜ:=by
    simpa only [admissibleQ_iff_product_pos] using h
  exact le_antisymm (le_of_not_gt hnot) hnonneg

def choose {n:ℕ} (I:RationalInstance n):List (Finset (Fin n))→ Option (Finset (Fin n))
  | [] => none
  | S::rest =>
    match choose I rest with
    | none => if admissibleQ I S then some S else none
    | some T =>
      if admissibleQ I S∧ ratioQ I S≤ ratioQ I T then some S else some T

theorem choose_sound {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n))) (S:Finset (Fin n))
    (h:choose I candidates=some S):S∈ candidates∧ admissibleQ I S:=by
  induction candidates with
  | nil => simp [choose] at h
  | cons T rest ih =>
    simp only [choose] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self,by assumption⟩
      · simp at h
    · rename_i U hU
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        exact ⟨List.mem_cons_self, (by assumption:admissibleQ I T∧ _).1⟩
      · simp only [Option.some.injEq] at h
        subst S
        obtain ⟨hmem,hadm⟩:=ih hU
        exact ⟨List.mem_cons_of_mem _ hmem,hadm⟩

theorem choose_exists {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n)))
    (hex:∃ S∈ candidates,admissibleQ I S):∃ S,choose I candidates=some S:=by
  induction candidates with
  | nil => simp at hex
  | cons T rest ih =>
    by_cases hrest:∃ S∈ rest,admissibleQ I S
    · obtain ⟨U,hU⟩:=ih hrest
      simp only [choose,hU]
      split <;> exact ⟨_,rfl⟩
    · have hnone:choose I rest=none:=by
        cases h:choose I rest with
        | none => rfl
        | some U =>
          obtain ⟨hmem,hadm⟩:=choose_sound I rest U h
          exact False.elim (hrest ⟨U,hmem,hadm⟩)
      obtain ⟨S,hmem,hadm⟩:=hex
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨S,by simp [choose,hnone,hadm]⟩
      · exact False.elim (hrest ⟨S,hmem,hadm⟩)

theorem choose_minimal {n:ℕ} (I:RationalInstance n)
    (candidates:List (Finset (Fin n))) (S T:Finset (Fin n))
    (h:choose I candidates=some S) (hT:T∈ candidates)
    (hvalid:admissibleQ I T):ratioQ I S≤ ratioQ I T:=by
  induction candidates generalizing S with
  | nil => simp at hT
  | cons U rest ih =>
    simp only [choose] at h
    split at h
    · rename_i hnone
      split at h
      · simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · obtain ⟨V,hV⟩:=choose_exists I rest ⟨T,hT,hvalid⟩
          rw [hnone] at hV
          cases hV
      · simp at h
    · rename_i V hV
      split at h
      · rename_i hbetter
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_rfl
        · exact hbetter.2.trans (ih V hV hT)
      · rename_i hnot
        simp only [Option.some.injEq] at h
        subst S
        rcases List.mem_cons.mp hT with rfl | hT
        · exact le_of_not_ge (fun hle => hnot ⟨hvalid,hle⟩)
        · exact ih V hV hT

def candidates {n:ℕ} (potential:Fin n→ ℚ):List (Finset (Fin n)):=
  (List.finRange n).map fun v => Finset.univ.filter fun u => potential u≤ potential v

end Lax455465Proofs.CutSweeps

end

section

open scoped BigOperators

namespace Lax455465Proofs.CutLayers

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps

structure Layers (n k:ℕ) where
  rank:Fin n→ Fin (k + 1)
  gap:Fin k→ ℚ
  gap_nonneg:∀ i,0≤ gap i

def potential {n k:ℕ} (L:Layers n k) (v:Fin n):ℚ:=
  ∑ i:Fin k,if i.val < (L.rank v).val then L.gap i else 0

def shore {n k:ℕ} (L:Layers n k) (i:Fin k):Finset (Fin n):=
  Finset.univ.filter fun v => (L.rank v).val≤ i.val

theorem difference {n k:ℕ} (L:Layers n k) (u v:Fin n)
    (h:(L.rank u).val≤ (L.rank v).val):
    potential L v - potential L u =
      ∑ i:Fin k,if (L.rank u).val≤ i.val∧ i.val < (L.rank v).val
        then L.gap i else 0:=by
  rw [potential,potential, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all <;> omega

theorem monotone {n k:ℕ} (L:Layers n k) (u v:Fin n)
    (h:(L.rank u).val≤ (L.rank v).val):potential L u≤ potential L v:=by
  have hd:=difference L u v h
  have hnonneg:0≤ ∑ i:Fin k,
      if (L.rank u).val≤ i.val∧ i.val < (L.rank v).val then L.gap i else 0:=
    Finset.sum_nonneg (fun i _ => by split_ifs; exact L.gap_nonneg i; exact le_rfl)
  linarith

theorem positive_difference {n k:ℕ} (L:Layers n k) (u v:Fin n):
    max (potential L v - potential L u) 0 =
      ∑ i:Fin k,if u∈ shore L i∧ v∉ shore L i then L.gap i else 0:=by
  simp only [shore,Finset.mem_filter,Finset.mem_univ,true_and,not_le]
  by_cases h:(L.rank u).val≤ (L.rank v).val
  · rw [max_eq_left (sub_nonneg.mpr (monotone L u v h)),difference L u v h]
  · have hrev:(L.rank v).val≤ (L.rank u).val:=by omega
    rw [max_eq_right (sub_nonpos.mpr (monotone L v u hrev))]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

private theorem complement_filter {n:ℕ} (S:Finset (Fin n)):
    (Finset.univ.filter fun v => v∉ S)=Sᶜ:=by
  ext v
  simp

theorem mass_product {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    massQ I S * massQ I Sᶜ =
      ∑ u:Fin n, ∑ v:Fin n,
        if u∈ S∧ v∉ S then (I.weight u:ℚ) * I.weight v else 0:=by
  simp only [massQ]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  symm
  simp_rw [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

theorem capacity_expansion {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    capacityQ I S =
      ∑ u:Fin n, ∑ v:Fin n,
        if u∈ S∧ v∉ S then (I.capacity u v:ℚ) else 0:=by
  simp only [capacityQ]
  symm
  simp_rw [ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [← Finset.sum_filter]
  simp [complement_filter]

theorem demand_identity {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    (∑ u:Fin n, ∑ v:Fin n,
      (I.weight u:ℚ) * I.weight v * max (potential L v - potential L u) 0) =
      ∑ i:Fin k,L.gap i * (massQ I (shore L i) * massQ I (shore L i)ᶜ):=by
  simp_rw [positive_difference,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [mass_product,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

theorem capacity_identity {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    (∑ u:Fin n, ∑ v:Fin n,
      (I.capacity u v:ℚ) * max (potential L v - potential L u) 0) =
      ∑ i:Fin k,L.gap i * capacityQ I (shore L i):=by
  simp_rw [positive_difference,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [capacity_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> ring

end Lax455465Proofs.CutLayers

end

section

open scoped BigOperators

namespace Lax455465Proofs.ThresholdRounding

open Lax455465.RationalEncoding Lax455465Proofs.CutSweeps Lax455465Proofs.CutLayers

def separation {n k:ℕ} (I:RationalInstance n) (L:Layers n k):ℚ:=
  ∑ u:Fin n, ∑ v:Fin n,
    (I.weight u:ℚ) * I.weight v * max (potential L v - potential L u) 0

def edgeCost {n k:ℕ} (I:RationalInstance n) (L:Layers n k):ℚ:=
  ∑ u:Fin n, ∑ v:Fin n,
    (I.capacity u v:ℚ) * max (potential L v - potential L u) 0

def layerCandidates {n k:ℕ} (L:Layers n k):List (Finset (Fin n)):=
  List.ofFn (shore L)

def round {n k:ℕ} (I:RationalInstance n) (L:Layers n k):
    Option (Finset (Fin n)):=choose I (layerCandidates L)

private theorem admissible_layer {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (hsep:0 < separation I L):∃ i:Fin k,admissibleQ I (shore L i):=by
  by_contra h
  have hzero:∀ i:Fin k,massQ I (shore L i) * massQ I (shore L i)ᶜ=0:=by
    intro i
    apply demand_zero_of_not_admissible
    exact fun hi => h ⟨i,hi⟩
  have hid:=demand_identity I L
  change separation I L=_ at hid
  simp only [hzero,mul_zero,Finset.sum_const_zero] at hid
  exact (ne_of_gt hsep) hid

theorem round_spec {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (hsep:0 < separation I L):
    ∃ S,round I L=some S∧ admissibleQ I S∧
      ratioQ I S≤ edgeCost I L / separation I L:=by
  obtain ⟨i,hi⟩:=admissible_layer I L hsep
  have himem:shore L i∈ layerCandidates L:=List.mem_ofFn.mpr ⟨i,rfl⟩
  obtain ⟨S,hS⟩:=choose_exists I (layerCandidates L) ⟨_,himem,hi⟩
  have hvalid:=(choose_sound I _ _ hS).2
  refine ⟨S,hS,hvalid, (le_div_iff₀ hsep).mpr ?_⟩
  have hcut:∀ j:Fin k,
      ratioQ I S * (massQ I (shore L j) * massQ I (shore L j)ᶜ)≤
        capacityQ I (shore L j):=by
    intro j
    by_cases hj:admissibleQ I (shore L j)
    · have hjmem:shore L j∈ layerCandidates L:=List.mem_ofFn.mpr ⟨j,rfl⟩
      have hmin:=choose_minimal I _ S (shore L j) hS hjmem hj
      unfold ratioQ at hmin
      exact (le_div_iff₀ ((admissibleQ_iff_product_pos I _).mp hj)).mp hmin
    · rw [demand_zero_of_not_admissible I _ hj,mul_zero]
      exact capacityQ_nonneg I _
  change ratioQ I S * (∑ u, ∑ v,_)≤ ∑ u, ∑ v,_
  rw [demand_identity,capacity_identity,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hbound:=mul_le_mul_of_nonneg_left (hcut j) (L.gap_nonneg j)
  nlinarith

theorem edgeCost_le {n k:ℕ} (I:RationalInstance n) (L:Layers n k)
    (length:Fin n→ Fin n→ ℚ)
    (hnonneg:∀ u v,0≤ length u v)
    (hlip:∀ u v,potential L v - potential L u≤ length u v):
    edgeCost I L≤ ∑ u, ∑ v, (I.capacity u v:ℚ) * length u v:=by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (max_le (hlip u v) (hnonneg u v))
    (NNRat.coe_nonneg (I.capacity u v))

end Lax455465Proofs.ThresholdRounding

end

section

open scoped BigOperators

namespace Lax455465Proofs.PotentialLayers

open CutLayers

def values {n:ℕ} (a:Fin n→ ℚ):List ℚ:=
  (List.ofFn a).mergeSort (·≤ ·)

theorem values_length {n:ℕ} (a:Fin n→ ℚ):(values a).length=n:=by
  simp [values]

theorem value_mem {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):a v∈ values a:=by
  exact List.mem_mergeSort.mpr (List.mem_ofFn.mpr ⟨v,rfl⟩)

def level (xs:List ℚ) (i:ℕ):ℚ:=xs.getD (min i (xs.length - 1)) 0

theorem level_monotone (xs:List ℚ) (hs:xs.SortedLE):Monotone (level xs):=by
  intro i j hij
  cases xs with
  | nil => simp [level]
  | cons x xs =>
    have hi:min i ((x::xs).length - 1) < (x::xs).length:=by
      simp only [List.length_cons]
      omega
    have hj:min j ((x::xs).length - 1) < (x::xs).length:=by
      simp only [List.length_cons]
      omega
    unfold level
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
    exact hs.monotone_get (min_le_min_right _ hij)

def rank {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):Fin (n + 1):=
  ⟨(values a).idxOf (a v),by
    have h:=List.idxOf_lt_length_of_mem (value_mem a v)
    rw [values_length] at h
    omega⟩

theorem level_rank {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):
    level (values a) (rank a v).val=a v:=by
  have h:=List.idxOf_lt_length_of_mem (value_mem a v)
  have hle:(values a).idxOf (a v)≤ (values a).length - 1:=by omega
  unfold level rank
  rw [min_eq_left hle,List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

def build {n:ℕ} (a:Fin n→ ℚ):Layers n n where
  rank:=rank a
  gap i:=level (values a) i.succ.val - level (values a) i.castSucc.val
  gap_nonneg i:=sub_nonneg.mpr
    (level_monotone _ List.sortedLE_mergeSort (by simp))

private theorem prefix_step {k:ℕ} (f:Fin k→ ℚ) (r:Fin k):
    (∑ i:Fin k,if i.val < r.succ.val then f i else 0) =
      (∑ i:Fin k,if i.val < r.castSucc.val then f i else 0) + f r:=by
  have hterm:∀ i:Fin k,
      (if i.val < r.succ.val then f i else 0) =
        (if i.val < r.castSucc.val then f i else 0) + (if i=r then f i else 0):=by
    intro i
    by_cases hir:i=r
    · subst i
      simp
    · have hval:i.val ≠ r.val:=fun h => hir (Fin.ext h)
      simp only [Fin.val_succ,Fin.val_castSucc,if_neg hir,add_zero]
      have hpred:i.val < r.val + 1↔ i.val < r.val:=by omega
      simp only [hpred]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

theorem telescope {k:ℕ} (a:Fin (k + 1)→ ℚ) (r:Fin (k + 1)):
    (∑ i:Fin k,if i.val < r.val then a i.succ - a i.castSucc else 0)=a r - a 0:=by
  refine Fin.induction ?_ ?_ r
  · simp
  · intro i ih
    rw [prefix_step,ih]
    ring

theorem potential_eq {n:ℕ} (a:Fin n→ ℚ) (v:Fin n):
    potential (build a) v=a v - level (values a) 0:=by
  change (∑ i:Fin n,if i.val < (rank a v).val then
    level (values a) i.succ.val - level (values a) i.castSucc.val else 0)=_
  rw [telescope (fun i:Fin (n + 1) => level (values a) i.val) (rank a v),level_rank]
  rfl

theorem difference_eq {n:ℕ} (a:Fin n→ ℚ) (u v:Fin n):
    potential (build a) v - potential (build a) u=a v - a u:=by
  rw [potential_eq,potential_eq]
  ring

open Lax455465.RationalEncoding CutSweeps

def separation {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):ℚ:=
  ∑ u, ∑ v, (I.weight u:ℚ) * I.weight v * max (a v - a u) 0

def edgeCost {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):ℚ:=
  ∑ u, ∑ v, (I.capacity u v:ℚ) * max (a v - a u) 0

private theorem separation_build {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):
    ThresholdRounding.separation I (build a)=separation I a:=by
  simp only [ThresholdRounding.separation,separation,difference_eq]

private theorem edgeCost_build {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):
    ThresholdRounding.edgeCost I (build a)=edgeCost I a:=by
  simp only [ThresholdRounding.edgeCost,edgeCost,difference_eq]

def round {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):Option (Finset (Fin n)):=
  ThresholdRounding.round I (build a)

theorem round_spec {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ)
    (hsep:0 < separation I a):
    ∃ S,round I a=some S∧ admissibleQ I S∧ ratioQ I S≤ edgeCost I a / separation I a:=by
  simpa only [round,separation_build,edgeCost_build] using
    ThresholdRounding.round_spec I (build a) (by simpa only [separation_build] using hsep)

theorem edgeCost_le {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ)
    (length:Fin n→ Fin n→ ℚ) (hnonneg:∀ u v,0≤ length u v)
    (hlip:∀ u v,a v - a u≤ length u v):
    edgeCost I a≤ ∑ u, ∑ v, (I.capacity u v:ℚ) * length u v:=by
  rw [← edgeCost_build]
  exact ThresholdRounding.edgeCost_le I (build a) length hnonneg
    (by simpa only [difference_eq] using hlip)

end Lax455465Proofs.PotentialLayers

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.SetDistances

open RationalDistances

def fromSet {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty) (v:Fin n):ℚ:=
  S.inf' hS fun u => d u v

def toSet {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty) (v:Fin n):ℚ:=
  S.inf' hS fun u => d v u

theorem from_nonnegative {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (hd:Nonnegative d) (v:Fin n):0≤ fromSet d S hS v:=
  Finset.le_inf' hS _ fun u _ => hd u v

theorem to_nonnegative {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (hd:Nonnegative d) (v:Fin n):0≤ toSet d S hS v:=
  Finset.le_inf' hS _ fun u _ => hd v u

theorem from_zero {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (hd:Nonnegative d) (hdiag:∀ v,d v v=0) (v:Fin n) (hv:v∈ S):
    fromSet d S hS v=0:=by
  apply le_antisymm _ (from_nonnegative d S hS hd v)
  have h:=Finset.inf'_le (fun u => d u v) hv
  simpa only [hdiag,fromSet] using h

theorem to_zero {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (hd:Nonnegative d) (hdiag:∀ v,d v v=0) (v:Fin n) (hv:v∈ S):
    toSet d S hS v=0:=by
  apply le_antisymm _ (to_nonnegative d S hS hd v)
  have h:=Finset.inf'_le (fun u => d v u) hv
  simpa only [hdiag,toSet] using h

theorem from_lipschitz {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (htri:∀ u v w,d u w≤ d u v + d v w) (u v:Fin n):
    fromSet d S hS v - fromSet d S hS u≤ d u v:=by
  obtain ⟨s,hs,hmin⟩:=Finset.exists_mem_eq_inf' hS (fun t => d t u)
  change fromSet d S hS u=d s u at hmin
  have hbound:=Finset.inf'_le (fun t => d t v) hs
  change fromSet d S hS v≤ d s v at hbound
  linarith [htri s u v]

theorem negative_to_lipschitz {n:ℕ} (d:Distance n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (htri:∀ u v w,d u w≤ d u v + d v w) (u v:Fin n):
    -toSet d S hS v - -toSet d S hS u≤ d u v:=by
  obtain ⟨s,hs,hmin⟩:=Finset.exists_mem_eq_inf' hS (fun t => d v t)
  change toSet d S hS v=d v s at hmin
  have hbound:=Finset.inf'_le (fun t => d u t) hs
  change toSet d S hS u≤ d u s at hbound
  linarith [htri u v s]

theorem root_balls_bound {n:ℕ} (d:Distance n) (Tin Tout:Finset (Fin n))
    (hin:Tin.Nonempty) (hout:Tout.Nonempty) (root:Fin n) (radius:ℚ)
    (htri:∀ u v w,d u w≤ d u v + d v w)
    (hinRadius:∀ s∈ Tin,d s root≤ radius)
    (houtRadius:∀ t∈ Tout,d root t≤ radius) (u v:Fin n):
    d u v≤ toSet d Tin hin u + 2 * radius + fromSet d Tout hout v:=by
  obtain ⟨s,hs,hminIn⟩:=Finset.exists_mem_eq_inf' hin (fun t => d u t)
  obtain ⟨t,ht,hminOut⟩:=Finset.exists_mem_eq_inf' hout (fun t => d t v)
  change toSet d Tin hin u=d u s at hminIn
  change fromSet d Tout hout v=d t v at hminOut
  linarith [htri u s v,htri s root v,htri root t v,
    hinRadius s hs,houtRadius t ht]

end Lax455465Proofs.SetDistances

end

section

open scoped BigOperators

namespace Lax455465Proofs.LargeBallRounding

open Lax455465.RationalEncoding CutSweeps SetDistances RationalDistances

def fromAverage {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (S:Finset (Fin n)) (hS:S.Nonempty):ℚ:=
  ∑ v, (I.weight v:ℚ) * fromSet d S hS v

def toAverage {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (S:Finset (Fin n)) (hS:S.Nonempty):ℚ:=
  ∑ v, (I.weight v:ℚ) * toSet d S hS v

def potential {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty):Fin n→ ℚ:=
  if toAverage I d Tin hin≤ fromAverage I d Tout hout then fromSet d Tout hout
  else fun v => -toSet d Tin hin v

private theorem separation_neg {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ):
    PotentialLayers.separation I (fun v => -a v)=PotentialLayers.separation I a:=by
  unfold PotentialLayers.separation
  have ht:∀ u v:Fin n,
      (I.weight u:ℚ) * I.weight v * max (-a v - -a u) 0 =
      (I.weight v:ℚ) * I.weight u * max (a u - a v) 0:=by
    intro u v
    rw [neg_sub_neg]
    ring
  simp_rw [ht]
  rw [Finset.sum_comm]

theorem separation_lower {n:ℕ} (I:RationalInstance n) (a:Fin n→ ℚ)
    (S:Finset (Fin n)) (ha:∀ v,0≤ a v) (hzero:∀ v∈ S,a v=0):
    mass I S * (∑ v, (I.weight v:ℚ) * a v)≤ PotentialLayers.separation I a:=by
  calc
    mass I S * (∑ v, (I.weight v:ℚ) * a v) =
        ∑ u∈ S, ∑ v, (I.weight u:ℚ) * I.weight v * max (a v - a u) 0:=by
      unfold mass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [hzero u hu,sub_zero,max_eq_left (ha v)]
      ring
    _≤ PotentialLayers.separation I a:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro u _ _
      exact Finset.sum_nonneg fun v _ =>
        mul_nonneg (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _)) (le_max_right _ _)

private theorem pair_linear_identity {n:ℕ} (w a b:Fin n→ ℚ) (r:ℚ):
    (∑ u, ∑ v,w u * w v * (a u + 2 * r + b v)) =
      (∑ v,w v) * (∑ u,w u * a u) + 2 * r * (∑ v,w v) ^ 2 +
        (∑ u,w u) * (∑ v,w v * b v):=by
  have ht:∀ u v:Fin n,w u * w v * (a u + 2 * r + b v) =
      (w u * a u) * w v + (2 * r * w u) * w v + w u * (w v * b v):=by
    intro u v
    ring
  simp_rw [ht,Finset.sum_add_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem average_bound {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (root:Fin n)
    (hM:0 < total I) (hsep:1≤ distanceSeparation I d)
    (htri:∀ u v w,d u w≤ d u v + d v w)
    (hinRadius:∀ s∈ Tin,d s root≤ 1 / (4 * total I ^ 2))
    (houtRadius:∀ t∈ Tout,d root t≤ 1 / (4 * total I ^ 2)):
    (1 / 2:ℚ)≤ total I * toAverage I d Tin hin + total I * fromAverage I d Tout hout:=by
  have hpair:distanceSeparation I d≤
      ∑ u, ∑ v, (I.weight u:ℚ) * I.weight v *
        (toSet d Tin hin u + 2 * (1 / (4 * total I ^ 2)) + fromSet d Tout hout v):=by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left
      (root_balls_bound d Tin Tout hin hout root _ htri hinRadius houtRadius u v)
      (mul_nonneg (NNRat.coe_nonneg _) (NNRat.coe_nonneg _))
  rw [pair_linear_identity] at hpair
  change distanceSeparation I d≤ total I * toAverage I d Tin hin +
    2 * (1 / (4 * total I ^ 2)) * total I ^ 2 + total I * fromAverage I d Tout hout at hpair
  have hr:2 * (1 / (4 * total I ^ 2)) * total I ^ 2=(1 / 2:ℚ):=by
    field_simp [ne_of_gt hM]
    norm_num
  linarith

theorem potential_separation {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (root:Fin n)
    (hM:0 < total I) (hd:Nonnegative d) (hdiag:∀ v,d v v=0)
    (hsep:1≤ distanceSeparation I d) (htri:∀ u v w,d u w≤ d u v + d v w)
    (hinRadius:∀ s∈ Tin,d s root≤ 1 / (4 * total I ^ 2))
    (houtRadius:∀ t∈ Tout,d root t≤ 1 / (4 * total I ^ 2))
    (hinMass:(2 / 3:ℚ) * total I≤ mass I Tin)
    (houtMass:(2 / 3:ℚ) * total I≤ mass I Tout):
    (1 / 6:ℚ)≤ PotentialLayers.separation I (potential I d Tin Tout hin hout):=by
  have hab:=average_bound I d Tin Tout hin hout root hM hsep htri hinRadius houtRadius
  have hfromNN:0≤ fromAverage I d Tout hout:=
    Finset.sum_nonneg fun v _ => mul_nonneg (NNRat.coe_nonneg _) (from_nonnegative d Tout hout hd v)
  have htoNN:0≤ toAverage I d Tin hin:=
    Finset.sum_nonneg fun v _ => mul_nonneg (NNRat.coe_nonneg _) (to_nonnegative d Tin hin hd v)
  unfold potential
  by_cases hcompare:toAverage I d Tin hin≤ fromAverage I d Tout hout
  · rw [if_pos hcompare]
    have havg:(1 / 4:ℚ)≤ total I * fromAverage I d Tout hout:=by
      have hle:=mul_le_mul_of_nonneg_left hcompare hM.le
      linarith
    have hmass:=mul_le_mul_of_nonneg_right houtMass hfromNN
    have hbound:=separation_lower I (fromSet d Tout hout) Tout
      (from_nonnegative d Tout hout hd) (from_zero d Tout hout hd hdiag)
    change mass I Tout * fromAverage I d Tout hout≤ _ at hbound
    nlinarith
  · rw [if_neg hcompare,separation_neg]
    have havg:(1 / 4:ℚ)≤ total I * toAverage I d Tin hin:=by
      have hle:=mul_le_mul_of_nonneg_left (le_of_not_ge hcompare) hM.le
      linarith
    have hmass:=mul_le_mul_of_nonneg_right hinMass htoNN
    have hbound:=separation_lower I (toSet d Tin hin) Tin
      (to_nonnegative d Tin hin hd) (to_zero d Tin hin hd hdiag)
    change mass I Tin * toAverage I d Tin hin≤ _ at hbound
    nlinarith

theorem potential_lipschitz {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty)
    (htri:∀ u v w,d u w≤ d u v + d v w) (u v:Fin n):
    potential I d Tin Tout hin hout v - potential I d Tin Tout hin hout u≤ d u v:=by
  unfold potential
  split_ifs
  · exact from_lipschitz d Tout hout htri u v
  · exact negative_to_lipschitz d Tin hin htri u v

def round {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty):Option (Finset (Fin n)):=
  PotentialLayers.round I (potential I d Tin Tout hin hout)

theorem round_correct {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (root:Fin n)
    (hM:0 < total I) (hd:Nonnegative d) (hdiag:∀ v,d v v=0)
    (hsep:1≤ distanceSeparation I d) (htri:∀ u v w,d u w≤ d u v + d v w)
    (hinRadius:∀ s∈ Tin,d s root≤ 1 / (4 * total I ^ 2))
    (houtRadius:∀ t∈ Tout,d root t≤ 1 / (4 * total I ^ 2))
    (hinMass:(2 / 3:ℚ) * total I≤ mass I Tin)
    (houtMass:(2 / 3:ℚ) * total I≤ mass I Tout):
    ∃ S,round I d Tin Tout hin hout=some S∧ admissibleQ I S∧
      ratioQ I S≤ 6 * (∑ u, ∑ v, (I.capacity u v:ℚ) * d u v):=by
  have hsepBound:=potential_separation I d Tin Tout hin hout root hM hd hdiag hsep htri
    hinRadius houtRadius hinMass houtMass
  have hsepPos:0 < PotentialLayers.separation I (potential I d Tin Tout hin hout):=by linarith
  obtain ⟨S,hS,hvalid,hratio⟩:=PotentialLayers.round_spec I _ hsepPos
  refine ⟨S,hS,hvalid,hratio.trans ?_⟩
  have hcost:=PotentialLayers.edgeCost_le I (potential I d Tin Tout hin hout) d hd
    (potential_lipschitz I d Tin Tout hin hout htri)
  have hW:0≤ ∑ u, ∑ v, (I.capacity u v:ℚ) * d u v:=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (NNRat.coe_nonneg _) (hd u v)
  apply (div_le_iff₀ hsepPos).mpr
  nlinarith

end Lax455465Proofs.LargeBallRounding

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

theorem weights_nonnegative {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (v:Fin n):
    0≤ weights I active v:=by unfold weights; split_ifs <;> positivity

theorem capacity_nonnegative {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    ∀ u v,0≤ capacity I active u v:=by
  intro u v
  unfold capacity
  split_ifs <;> positivity

theorem capacity_remove {n:ℕ} (I:RationalInstance n) (active S:Finset (Fin n)):
    capacity I (active \ S)=erase (capacity I active) S:=by
  funext u v
  simp only [capacity,erase,Finset.mem_sdiff]
  split_ifs <;> (try simp_all)

end Lax455465Proofs.RegionLoop

end

section

open scoped BigOperators

namespace Lax455465Proofs.BalancedPrefix

def prefixMass (weights:ℕ→ ℚ) (t:ℕ):ℚ:= ∑ j∈ Finset.range (t + 1),weights j

def choose (weights:ℕ→ ℚ) (limit:ℕ) (total:ℚ):Option ℕ:=
  (List.range limit).find? fun t => decide (total / 6≤ prefixMass weights t)

theorem choose_correct (weights:ℕ→ ℚ) (limit:ℕ) (total:ℚ)
    (hpos:0 < total) (hsum:(∑ j∈ Finset.range limit,weights j)=total)
    (hsmall:∀ j < limit,weights j < (2 / 3:ℚ) * total):
    ∃ t,choose weights limit total=some t∧ t < limit∧
      total / 6≤ prefixMass weights t∧ prefixMass weights t < (5 / 6:ℚ) * total:=by
  have hlimit:0 < limit:=by
    by_contra h
    have hzero:limit=0:=by omega
    simp only [hzero,Finset.range_zero,Finset.sum_empty] at hsum
    linarith
  have hlast:prefixMass weights (limit - 1)=total:=by
    unfold prefixMass
    rw [Nat.sub_add_cancel (by omega),hsum]
  cases hs:choose weights limit total with
  | none =>
    unfold choose at hs
    have hfail:=List.find?_eq_none.mp hs (limit - 1) (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at hfail
    exact False.elim (hfail (by rw [hlast]; linarith))
  | some t =>
    have ht:t < limit:=List.mem_range.mp (List.mem_of_find?_eq_some hs)
    have hfound:total / 6≤ prefixMass weights t:=by
      simpa only [decide_eq_true_eq] using List.find?_some hs
    refine ⟨t,rfl,ht,hfound, ?_⟩
    obtain ⟨_,i,hi,hit,hprevious⟩:=List.find?_eq_some_iff_getElem.mp hs
    have hindex:i=t:=by simpa only [List.getElem_range] using hit
    have hprev:∀ j < t,prefixMass weights j < total / 6:=by
      intro j hj
      have hb:=hprevious j (by omega)
      have hn:¬ total / 6≤ prefixMass weights j:=by simpa using hb
      exact lt_of_not_ge hn
    by_cases ht0:t=0
    · have hsmall0:=hsmall t ht
      rw [ht0] at hsmall0 ⊢
      simp only [prefixMass,Nat.zero_add,Finset.sum_range_one]
      linarith
    · have hstep:prefixMass weights t=prefixMass weights (t - 1) + weights t:=by
        unfold prefixMass
        rw [Finset.sum_range_succ,Nat.sub_add_cancel (by omega)]
      rw [hstep]
      have hp:=hprev (t - 1) (by omega)
      have hb:=hsmall t ht
      linarith

theorem demand_bound (total retained:ℚ) (hpos:0 < total)
    (hlow:total / 6≤ retained) (hhigh:retained≤ (5 / 6:ℚ) * total):
    0 < retained∧ 0 < total - retained∧ (5 / 36:ℚ) * total ^ 2≤ retained * (total - retained):=by
  refine ⟨by linarith,by linarith, ?_⟩
  have hprod:=mul_nonneg (show 0≤ retained - total / 6 by linarith)
    (show 0≤ (5 / 6:ℚ) * total - retained by linarith)
  nlinarith

end Lax455465Proofs.BalancedPrefix

end

section

open scoped BigOperators

namespace Lax455465Proofs.BalancedRegionCut

open Lax455465.RationalEncoding CutSweeps RegionOrdering

def total {n:ℕ} (I:RationalInstance n):ℚ:= ∑ v, (I.weight v:ℚ)

def slotMass {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (t:ℕ):ℚ:=
  ∑ v,if position k orientation (index v).val=t then (I.weight v:ℚ) else 0

theorem position_injective (k:ℕ) (orientation:ℕ→ Bool) (i j:ℕ)
    (hi:i≤ k) (hj:j≤ k) (heq:position k orientation i=position k orientation j):
    i=j:=by
  unfold position at heq
  split_ifs at heq <;> omega

def regionMass {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (j:Fin (k + 1)):ℚ:= ∑ v,if index v=j then (I.weight v:ℚ) else 0

theorem slots_small {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (hM:0 < total I)
    (hsmall:∀ j,regionMass I index j < (2 / 3:ℚ) * total I):
    ∀ t,slotMass I index orientation t < (2 / 3:ℚ) * total I:=by
  intro t
  by_cases hex:∃ v,position k orientation (index v).val=t
  · obtain ⟨v,hv⟩:=hex
    have heq:slotMass I index orientation t=regionMass I index (index v):=by
      unfold slotMass regionMass
      apply Finset.sum_congr rfl
      intro u _
      have hiff:position k orientation (index u).val=t↔ index u=index v:=by
        constructor
        · intro hu
          apply Fin.ext
          exact position_injective k orientation _ _ (by have h:=(index u).isLt; omega)
            (by have h:=(index v).isLt; omega) (hu.trans hv.symm)
        · intro hu
          simpa only [hu] using hv
      simp only [hiff]
    rw [heq]
    exact hsmall (index v)
  · have hz:slotMass I index orientation t=0:=by
      unfold slotMass
      apply Finset.sum_eq_zero
      intro v _
      exact if_neg (fun hv => hex ⟨v,hv⟩)
    rw [hz]
    linarith

private theorem position_bound (k:ℕ) (orientation:ℕ→ Bool) (j:ℕ) (hj:j≤ k):
    position k orientation j < 2 * k + 1:=by
  unfold position
  split_ifs <;> omega

theorem slot_total {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool):
    (∑ t∈ Finset.range (2 * k + 1),slotMass I index orientation t)=total I:=by
  unfold slotMass total
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_ite_eq]
  rw [if_pos (Finset.mem_range.mpr (position_bound k orientation _ (by have h:=(index v).isLt; omega)))]

theorem prefix_mass {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (t:ℕ):
    BalancedPrefix.prefixMass (slotMass I index orientation) t=massQ I (lateCut index orientation t)ᶜ:=by
  unfold BalancedPrefix.prefixMass slotMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_range,Nat.lt_succ_iff]
  have hc:(lateCut index orientation t)ᶜ =
      Finset.univ.filter fun v => position k orientation (index v).val≤ t:=by
    ext v
    simp [lateCut,not_lt]
  rw [hc]
  unfold massQ
  rw [Finset.sum_filter]

theorem mass_complement {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    massQ I S + massQ I Sᶜ=total I:=by
  exact Finset.sum_add_sum_compl S (fun v => (I.weight v:ℚ))

def round {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool):Option (Finset (Fin n)):=
  (BalancedPrefix.choose (slotMass I index orientation) (2 * k + 1) (total I)).map
    (lateCut index orientation)

theorem round_correct {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (hM:0 < total I)
    (hsmall:∀ t < 2 * k + 1,slotMass I index orientation t < (2 / 3:ℚ) * total I):
    ∃ S,round I index orientation=some S∧ admissibleQ I S∧
      (5 / 36:ℚ) * total I ^ 2≤ massQ I S * massQ I Sᶜ∧
      capacityQ I S≤ ∑ j:Fin k,chargedBoundary (fun u v => (I.capacity u v:ℚ)) index orientation j:=by
  obtain ⟨t,ht,_,hlow,hhigh⟩:=BalancedPrefix.choose_correct
    (slotMass I index orientation) (2 * k + 1) (total I) hM (slot_total I index orientation) hsmall
  let S:=lateCut index orientation t
  have hpref:BalancedPrefix.prefixMass (slotMass I index orientation) t=massQ I Sᶜ:=
    prefix_mass I index orientation t
  obtain ⟨hleft,hright,hdemand⟩:=BalancedPrefix.demand_bound (total I) _ hM hlow hhigh.le
  rw [hpref] at hleft hright hdemand
  have hcomplement:=mass_complement I S
  have hS:total I - massQ I Sᶜ=massQ I S:=by linarith
  rw [hS] at hright hdemand
  refine ⟨S,by simp only [round,ht,Option.map_some,S], ⟨hright,hleft⟩, ?_, ?_⟩
  · nlinarith [hdemand]
  · have hbound:=late_cut_bound (fun u v => (I.capacity u v:ℚ)) index orientation t
      (fun u v => NNRat.coe_nonneg _)
    rw [CutLayers.capacity_expansion]
    exact hbound

theorem round_ratio {n k:ℕ} (I:RationalInstance n) (index:Fin n→ Fin (k + 1))
    (orientation:ℕ→ Bool) (K W:ℚ) (hM:0 < total I) (hK:0≤ K) (hW:0≤ W)
    (hsmall:∀ j,regionMass I index j < (2 / 3:ℚ) * total I)
    (hcharge:(∑ j:Fin k,chargedBoundary (fun u v => (I.capacity u v:ℚ)) index orientation j)≤
      8 * K * total I ^ 2 * W):
    ∃ S,round I index orientation=some S∧ admissibleQ I S∧
      ratioQ I S≤ (288 / 5:ℚ) * K * W:=by
  obtain ⟨S,hs,hadm,hdemand,hcap⟩:=round_correct I index orientation hM
    (fun t _ => slots_small I index orientation hM hsmall t)
  refine ⟨S,hs,hadm, ?_⟩
  unfold ratioQ
  apply (div_le_iff₀ (mul_pos hadm.1 hadm.2)).mpr
  calc
    capacityQ I S≤ 8 * K * total I ^ 2 * W:=hcap.trans hcharge
    _=((288 / 5:ℚ) * K * W) * ((5 / 36:ℚ) * total I ^ 2):=by ring
    _≤ ((288 / 5:ℚ) * K * W) * (massQ I S * massQ I Sᶜ):=
      mul_le_mul_of_nonneg_left hdemand (by positivity)

end Lax455465Proofs.BalancedRegionCut

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionHistory

open Lax455465.RationalEncoding RegionLoop RegionSelection RegionFrontier RegionOrdering

def index {n:ℕ} (d:RationalDistances.Distance n):
    (history:List (Region n))→ Fin n→ Fin (history.length + 1)
  | [],_ => 0
  | R::rest,v => if v∈ R.ball d then 0 else (index d rest v).succ

def orientation {n:ℕ} (history:List (Region n)) (j:ℕ):Bool:=
  ((history[j]?).map Region.outward).getD true

def activeAt {n:ℕ} (d:RationalDistances.Distance n):
    Finset (Fin n)→ List (Region n)→ ℕ→ Finset (Fin n)
  | active, [],_ => active
  | active,_::_,0 => active
  | active,R::rest,j + 1 => activeAt d (active \ R.ball d) rest j

theorem activeAt_zero {n:ℕ} (d:RationalDistances.Distance n)
    (active:Finset (Fin n)) (history:List (Region n)):activeAt d active history 0=active:=by
  cases history <;> rfl

theorem activeAt_mem {n:ℕ} (d:RationalDistances.Distance n)
    (history:List (Region n)) (active:Finset (Fin n)) (j:ℕ) (hj:j≤ history.length) (v:Fin n):
    v∈ activeAt d active history j↔ v∈ active∧ j≤ (index d history v).val:=by
  induction history generalizing active j with
  | nil =>
    have hj0:j=0:=by simpa using hj
    simp [hj0,activeAt,index]
  | cons R rest ih =>
    cases j with
    | zero => simp [activeAt]
    | succ j =>
      rw [activeAt,ih (active \ R.ball d) j (by simpa using hj)]
      by_cases hv:v∈ R.ball d
      · simp [index,hv]
      · simp [index,hv]

theorem frontier {n:ℕ} (d:RationalDistances.Distance n) (history:List (Region n))
    (j:ℕ) (hj:j < history.length) (v:Fin n) (ha:j≤ (index d history v).val):
    v∈ history[j].ball d↔ (index d history v).val=j:=by
  induction history generalizing j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero =>
      by_cases hv:v∈ R.ball d <;> simp [index,hv]
    | succ j =>
      have hnot:v∉ R.ball d:=by
        intro hv
        simp [index,hv] at ha
      have har:j≤ (index d rest v).val:=by
        simpa only [index,if_neg hnot,Fin.val_succ,Nat.succ_le_succ_iff] using ha
      simpa only [List.getElem_cons_succ,index,if_neg hnot,Fin.val_succ,
        Nat.add_right_cancel_iff] using ih j (by simpa using hj) har

theorem step_valid {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n)) (active:Finset (Fin n))
    (hvalid:ValidHistory I d seed delta p active history) (j:ℕ) (hj:j < history.length):
    StepGood I d seed delta p (activeAt d active history j) history[j]:=by
  induction history generalizing active j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero => exact hvalid.1
    | succ j => exact ih (active \ R.ball d) hvalid.2 j (by simpa using hj)

theorem final_support {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n)) (active:Finset (Fin n))
    (hvalid:ValidHistory I d seed delta p active history):
    (support (weights I (activeAt d active history history.length))).card=0:=by
  induction history generalizing active with
  | nil => exact hvalid
  | cons R rest ih => exact ih (active \ R.ball d) hvalid.2

theorem capacity_eq_residual {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)) (j:ℕ) (hj:j≤ history.length):
    capacity I (activeAt d Finset.univ history j) =
      residual (fun u v => (I.capacity u v:ℚ)) (index d history) j:=by
  funext u v
  simp only [capacity,RegionFrontier.residual,activeAt_mem d history Finset.univ j hj,
    Finset.mem_univ,true_and]

theorem activeAt_step {n:ℕ} (d:RationalDistances.Distance n)
    (history:List (Region n)) (active:Finset (Fin n)) (j:ℕ) (hj:j < history.length):
    activeAt d active history (j + 1)=activeAt d active history j \ history[j].ball d:=by
  induction history generalizing active j with
  | nil => simp at hj
  | cons R rest ih =>
    cases j with
    | zero => simp only [activeAt,List.getElem_cons_zero,activeAt_zero]
    | succ j => exact ih (active \ R.ball d) j (by simpa using hj)

theorem orientation_eq {n:ℕ} (history:List (Region n)) (j:ℕ) (hj:j < history.length):
    orientation history j=history[j].outward:=by
  simp only [orientation,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some]

theorem block_mass {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)) (j:Fin history.length):
    BalancedRegionCut.regionMass I (index d history) j.castSucc =
      ∑ v∈ history[j.val].ball d,weights I (activeAt d Finset.univ history j.val) v:=by
  let A:=activeAt d Finset.univ history j.val
  let S:=history[j.val].ball d
  have hfull:(∑ v∈ S,weights I A v)=∑ v,if v∈ S then weights I A v else 0:=by
    have hf:Finset.univ.filter (fun v => v∈ S)=S:=by ext v; simp
    rw [← hf,Finset.sum_filter]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change (∑ v,if index d history v=j.castSucc then (I.weight v:ℚ) else 0)=∑ v∈ S,weights I A v
  rw [hfull]
  apply Finset.sum_congr rfl
  intro v _
  have hm:v∈ A↔ j.val≤ (index d history v).val:=by
    simpa only [A,Finset.mem_univ,true_and] using
      activeAt_mem d history Finset.univ j.val j.isLt.le v
  have hi:index d history v=j.castSucc↔ v∈ A∧ v∈ S:=by
    constructor
    · intro h
      have hv:(index d history v).val=j.val:=congrArg Fin.val h
      have ha:v∈ A:=hm.mpr hv.ge
      exact ⟨ha, (frontier d history j.val j.isLt v hv.ge).mpr hv⟩
    · rintro ⟨ha,hs⟩
      apply Fin.ext
      exact (frontier d history j.val j.isLt v (hm.mp ha)).mp hs
  simp only [hi,weights]
  by_cases ha:v∈ A <;> by_cases hs:v∈ S <;> simp [ha,hs]

theorem final_block_zero {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n))
    (hvalid:ValidHistory I d seed delta p Finset.univ history):
    BalancedRegionCut.regionMass I (index d history) (Fin.last history.length)=0:=by
  have hs:=final_support I d seed delta p history Finset.univ hvalid
  have hz:∀ v,weights I (activeAt d Finset.univ history history.length) v=0:=by
    intro v
    have hnot:¬ 0 < weights I (activeAt d Finset.univ history history.length) v:=by
      intro hv
      have hm:v∈ support (weights I (activeAt d Finset.univ history history.length)):=by
        simp [support,hv]
      have hpos:=Finset.card_pos.mpr ⟨v,hm⟩
      omega
    exact le_antisymm (le_of_not_gt hnot) (weights_nonnegative I _ v)
  unfold BalancedRegionCut.regionMass
  apply Finset.sum_eq_zero
  intro v _
  split_ifs with hv
  · have hidx:(index d history v).val=history.length:=congrArg Fin.val hv
    have ha:v∈ activeAt d Finset.univ history history.length:=
      (activeAt_mem d history Finset.univ history.length le_rfl v).mpr ⟨Finset.mem_univ _,hidx.ge⟩
    simpa only [weights,if_pos ha] using hz v
  · rfl

theorem blocks_small {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n))
    (hvalid:ValidHistory I d seed delta p Finset.univ history)
    (hM:0 < LargeBallRounding.total I):
    ∀ j,BalancedRegionCut.regionMass I (index d history) j <
      (2 / 3:ℚ) * BalancedRegionCut.total I:=by
  intro j
  by_cases hj:j.val < history.length
  · have hstep:=step_valid I d seed delta p history Finset.univ hvalid j.val hj
    let i:Fin history.length:= ⟨j.val,hj⟩
    have hji:j=i.castSucc:=Fin.ext rfl
    rw [hji,block_mass]
    exact hstep.2.2.2.2.2
  · have hlast:j=Fin.last history.length:=by apply Fin.ext; have h:=j.isLt; simp; omega
    rw [hlast,final_block_zero I d seed delta p history hvalid]
    change 0 < (2 / 3:ℚ) * LargeBallRounding.total I
    positivity

end Lax455465Proofs.RegionHistory

end

section

open scoped BigOperators

namespace Lax455465Proofs.HistoryCharging

open Lax455465.RationalEncoding RegionLoop RegionHistory RegionFrontier RegionOrdering RegionVolume

def cost {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)) (j:ℕ):ℚ:=
  weight (RegionLoop.capacity I (activeAt d Finset.univ history j)) d

def volume {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed:ℚ) (history:List (Region n)) (j:ℕ):ℚ:=
  if hj:j < history.length then
    let R:=history[j]
    let A:=activeAt d Finset.univ history j
    RegionSearch.selectedVolume (RegionLoop.capacity I A) d (d R.root) (fun v => d v R.root)
      seed (chooseDirection I d A R.root) R.radius
  else 0

def boundary {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)) (j:ℕ):ℚ:=
  if hj:j < history.length then
    let R:=history[j]
    orientedBoundary (RegionLoop.capacity I (activeAt d Finset.univ history j)) (R.ball d) R.outward
  else 0

theorem chosen_ball_eq {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (A:Finset (Fin n)) (R:Region n)
    (hstep:StepGood I d seed delta p A R):
    RegionCharging.chosenBall (d R.root) (fun v => d v R.root) (chooseDirection I d A R.root) R.radius =
      R.ball d:=by
  unfold RegionCharging.chosenBall Region.ball
  rw [← hstep.2.2.2.1]

theorem volume_bound {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n))
    (hvalid:ValidHistory I d seed delta p Finset.univ history)
    (hd:RationalDistances.Nonnegative d) (j:ℕ) (hj:j < history.length):
    volume I d seed history j≤ seed + (cost I d history j - cost I d history (j + 1)):=by
  have hstep:=step_valid I d seed delta p history Finset.univ hvalid j hj
  have hb:=RegionCharging.selected_volume_bound
    (RegionLoop.capacity I (activeAt d Finset.univ history j)) d
    (d history[j].root) (fun v => d v history[j].root) seed history[j].radius
    (chooseDirection I d (activeAt d Finset.univ history j) history[j].root)
    (capacity_nonnegative I _) hd
  rw [chosen_ball_eq I d seed delta p _ _ hstep, ← capacity_remove,
    ← activeAt_step d history Finset.univ j hj] at hb
  simpa only [volume,dif_pos hj,cost] using hb

theorem boundary_bound {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (seed delta:ℚ) (p:ℕ) (history:List (Region n))
    (hvalid:ValidHistory I d seed delta p Finset.univ history) (j:ℕ) (hj:j < history.length):
    boundary I d history j≤ RegionSearch.slope (RegionBudget.steps p) delta * volume I d seed history j:=by
  have hstep:=step_valid I d seed delta p history Finset.univ hvalid j hj
  have hb:=hstep.2.2.2.2.1
  unfold RegionSearch.Good at hb
  rw [selected_boundary,chosen_ball_eq I d seed delta p _ _ hstep, ← hstep.2.2.2.1] at hb
  simpa only [boundary,volume,dif_pos hj] using hb

theorem charge_eq {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)) (j:Fin history.length):
    chargedBoundary (fun u v => (I.capacity u v:ℚ)) (index d history) (orientation history) j =
      boundary I d history j.val:=by
  rw [charged_eq_boundary _ _ _ j (history[j.val].ball d)
    (fun v ha => frontier d history j.val j.isLt v ha)]
  rw [← capacity_eq_residual I d history j.val j.isLt.le,orientation_eq history j.val j.isLt]
  simp only [boundary,dif_pos j.isLt]

theorem initial_cost {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (history:List (Region n)):
    cost I d history 0=weight (fun u v => (I.capacity u v:ℚ)) d:=by
  have hc:RegionLoop.capacity I Finset.univ=(fun u v => (I.capacity u v:ℚ)):=by
    funext u v
    simp only [RegionLoop.capacity,Finset.mem_univ,and_self, ↓reduceIte]
  rw [cost,activeAt_zero,hc]

theorem total_charge {n:ℕ} (I:RationalInstance n) (d:RationalDistances.Distance n)
    (delta:ℚ) (p:ℕ) (history:List (Region n))
    (hp:0 < p) (hlen:history.length≤ p) (hdelta:0 < delta)
    (hd:RationalDistances.Nonnegative d)
    (hvalid:ValidHistory I d (weight (fun u v => (I.capacity u v:ℚ)) d / p) delta p Finset.univ history):
    (∑ j:Fin history.length,chargedBoundary (fun u v => (I.capacity u v:ℚ))
      (index d history) (orientation history) j)≤
      2 * RegionSearch.slope (RegionBudget.steps p) delta * weight (fun u v => (I.capacity u v:ℚ)) d:=by
  simp_rw [charge_eq]
  rw [Fin.sum_univ_eq_sum_range]
  have h:=RegionCharging.total_boundary_normalized (cost I d history) (boundary I d history)
    (volume I d (weight (fun u v => (I.capacity u v:ℚ)) d / p) history) history.length p
    (RegionSearch.slope (RegionBudget.steps p) delta) hp hlen (by unfold RegionSearch.slope; positivity)
    (by rw [initial_cost]; exact RegionCharging.weight_nonnegative _ d (fun u v => NNRat.coe_nonneg _) hd)
    (RegionCharging.weight_nonnegative _ d (capacity_nonnegative I _) hd)
    (fun j hj => by rw [initial_cost]; exact volume_bound I d _ delta p history hvalid hd j hj)
    (boundary_bound I d _ delta p history hvalid)
  rw [initial_cost] at h
  exact h

end Lax455465Proofs.HistoryCharging

end

section

namespace Lax455465Proofs.RamUnsignedScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem load_spec (B:ℕ) (name:String) (q:ℚ≥0) (h1:1 < B)
    (hn:q.num < B) (hd:q.den < B)
    (hfresh:name ++ ".n" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.s" ∧ name ++ ".d" ≠ "rat.n"):
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  have hv:=RamUnsignedArithmetic.value q
  have hns:=Ne.symm hfresh.1
  have hds:=Ne.symm hfresh.2.1
  have hdn:=Ne.symm hfresh.2.2
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c3:String:=c2 ".n"; let c4:Nat:=Env.vars c1 c3; let c5:Env:=Env.setVar c1 "rat.n" c4; let c6:String:=c2 ".d"; let c7:Nat:=Env.vars c5 c6; let c8:Env:=Env.setVar c5 "rat.d" c7; let c9:Nat→ Nat→ Nat:=Nat.add; let c10:Nat→ Nat:=c9 ((1:Nat)); let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat)))); let c12:Expr:=Expr.var c3; let c13:Nat:=c10 (Expr.size c12); let c14:Expr:=Expr.var c6; let c15:Nat:=c10 (Expr.size c14); let c16:Nat:=c9 c13 c15; let c17:Com:=Com.assign "rat.n" c12; let c18:Com:=Com.assign "rat.d" c14; @Exists.intro Env (fun (σ':Env) => And (Run B (load name) σ σ' ((6:Nat))) (c0 σ')) c8 (@And.intro (Run B (load name) σ c8 ((6:Nat))) (c0 c8) (RunStep.mono B (load name) σ c8 (c9 c11 c16) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c17 c18) σ c1 c8 c11 c16 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6578_0_0_0))) (RunStep.seq B c17 c18 c1 c5 c8 c13 c15 (RunStep.assign B c1 "rat.n" c12 c4 (RunStep.eval_var B c1 c3 ?_)) (RunStep.assign B c5 "rat.d" c14 c7 (RunStep.eval_var B c5 c6 ?_)))) (?nAX_g6578_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6578_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6578_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem save_spec (B:ℕ) (name:String) (q:ℚ≥0)
    (hn:q.num < B) (hd:q.den < B) (hfresh:name ++ ".n" ≠ "rat.d"):
    Spec B (FractionOutput (q:ℚ)) (save name) (fun _ τ => Stored name q τ) 4:=by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hn':σ.vars "rat.n"=q.num:=by simpa only [NNRat.natAbs_num_coe] using hnσ
  have hd':σ.vars "rat.d"=q.den:=by simpa only [NNRat.den_coe] using hdσ
  have hdn:=Ne.symm hfresh
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Stored name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".n"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.n"); let c4:String:=c1 ".d"; let c5:Nat:=Env.vars c3 "rat.d"; let c6:Env:=Env.setVar c3 c4 c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c7 ((1:Nat)); let c9:Nat:=c8 (Expr.size (Expr.var "rat.n")); let c10:Nat:=c8 (Expr.size (Expr.var "rat.d")); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((4:Nat))) (c0 σ')) c6 (@And.intro (Run B (save name) σ c6 ((4:Nat))) (c0 c6) (RunStep.mono B (save name) σ c6 (c7 c9 c10) ((4:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.n")) (Com.assign c4 (Expr.var "rat.d")) σ c3 c6 c9 c10 (RunStep.assign B σ c2 (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g6579_0_0_0))) (RunStep.assign B c3 c4 (Expr.var "rat.d") c5 (RunStep.eval_var B c3 "rat.d" ?_))) (?nAX_g6579_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6579_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6579_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

end Lax455465Proofs.RamUnsignedScalar

end

section

namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B:ℕ) (mode:Option Bool) (a b:Bool) (h1:1 < B):
    Spec B (fractionInputs 0 (bit a).num 1 0 (bit b).num 1) (command mode)
      (fun _ τ => FractionOutput (bit (flag mode a b):ℚ) τ) 10:=by
  cases mode with
  | none =>
    cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) false true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true false)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                 | (expose_names;
                                                                     (refine
                                                                         let c0:Env→ Prop:=FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@none Bool) true true)));
                                                                         let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ;
                                                                         let c2:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                         let c3:String→ Nat:=Env.vars c2;
                                                                         let c4:Nat:=c3 "left.n";
                                                                         let c5:Nat:=c3 "right.n";
                                                                         let c6:Nat:=Nat.mul c4 c5;
                                                                         let c7:Env:=Env.setVar c2 "rat.n" c6;
                                                                         let c8:Env:=Env.setVar c7 "rat.d" ((1:Nat));
                                                                         let c9:Nat→ Nat→ Nat:=Nat.add;
                                                                         let c10:Nat→ Nat:=c9 ((1:Nat));
                                                                         let c11:Nat:=c10 (Expr.size (Expr.lit ((0:Nat))));
                                                                         let c12:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                         let c13:Expr:=
                                                                           flag.match_1 (fun (mode:Option Bool) => Expr) (@none Bool)
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                             (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c12 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                             Expr.mul (c12 (Expr.var "left.n")) (Expr.var "right.n");
                                                                         let c14:Nat:=c10 (Expr.size c13);
                                                                         let c15:Nat:=c10 (Expr.size (Expr.lit ((1:Nat))));
                                                                         let c16:Nat:=c9 c14 c15;
                                                                         let c17:Com:=Com.assign "rat.n" c13;
                                                                         let c18:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                         @Exists.intro Env
                                                                           (fun (σ':Env) =>
                                                                             And (Run B (command (@none Bool)) σ σ' ((10:Nat))) (c1 σ'))
                                                                           c8
                                                                           (@And.intro (Run B (command (@none Bool)) σ c8 ((10:Nat)))
                                                                             (c1 c8)
                                                                             (RunStep.mono B (command (@none Bool)) σ c8 (c9 c11 c16)
                                                                               ((10:Nat))
                                                                               (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                 (Com.seq c17 c18) σ c2 c8 c11 c16
                                                                                 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                   ((0:Nat))
                                                                                   (RunStep.eval_lit B ((0:Nat)) σ
                                                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                 (RunStep.seq B c17 c18 c2 c7 c8 c14 c15
                                                                                   (RunStep.assign B c2 "rat.n" c13 c6
                                                                                     (RunStep.eval_mul B c2 (Expr.var "left.n") (Expr.var "right.n") c4 c5
                                                                                       (RunStep.eval_var B c2 "left.n" ?_) (RunStep.eval_var B c2 "right.n" ?_)
                                                                                       ?_))
                                                                                   (RunStep.assign B c7 "rat.d" (Expr.lit ((1:Nat)))
                                                                                     ((1:Nat))
                                                                                     (RunStep.eval_lit B ((1:Nat)) c7 h1))))
                                                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                             ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega
  | some mode =>
    cases mode <;> cases a <;> cases b <;> rintro σ ⟨hs,hn,hd,hts,htn,htd⟩ <;> (first
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool false)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool false) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c5;
                                                                                        let c7:Nat:=c4 "right.n";
                                                                                        let c8:Nat:=Nat.mul c6 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "left.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool false)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (c14 (Expr.var "right.n"))) fun (_:Unit) =>
                                                                                            Expr.mul c15 (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool false)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 c15 (Expr.var "right.n") c6 c7
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "left.n") ((1:Nat)) c5
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      (RunStep.eval_var B c3 "right.n" ?_) ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) false true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true false)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                                | (expose_names;
                                                                                    (refine
                                                                                        let c0:Env→ Nat→ Prop:=Run B (command (@some Bool true)) σ;
                                                                                        let c1:Env→ Prop:=
                                                                                          FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit (flag (@some Bool true) true true)));
                                                                                        let c2:Env→ Prop:=(fun (x τ:Env) => c1 τ) σ;
                                                                                        let c3:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                                                                        let c4:String→ Nat:=Env.vars c3;
                                                                                        let c5:Nat:=c4 "left.n";
                                                                                        let c6:Nat:=c4 "right.n";
                                                                                        let c7:Nat:=
                                                                                          @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) ((1:Nat)) c6;
                                                                                        let c8:Nat:=Nat.mul c5 c7;
                                                                                        let c9:Env:=Env.setVar c3 "rat.n" c8;
                                                                                        let c10:Env:=Env.setVar c9 "rat.d" ((1:Nat));
                                                                                        let c11:Nat→ Nat→ Nat:=Nat.add;
                                                                                        let c12:Nat→ Nat:=c11 ((1:Nat));
                                                                                        let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat))));
                                                                                        let c14:Expr→ Expr:=Expr.sub (Expr.lit ((1:Nat)));
                                                                                        let c15:Expr:=c14 (Expr.var "right.n");
                                                                                        let c16:Expr:=
                                                                                          flag.match_1 (fun (mode:Option Bool) => Expr) (@some Bool true)
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") (Expr.var "right.n"))
                                                                                            (fun (_:Unit) => Expr.mul (Expr.var "left.n") c15) fun (_:Unit) =>
                                                                                            Expr.mul (c14 (Expr.var "left.n")) (Expr.var "right.n");
                                                                                        let c17:Nat:=c12 (Expr.size c16);
                                                                                        let c18:Nat:=c12 (Expr.size (Expr.lit ((1:Nat))));
                                                                                        let c19:Nat:=c11 c17 c18;
                                                                                        let c20:Com:=Com.assign "rat.n" c16;
                                                                                        let c21:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                                                                        @Exists.intro Env
                                                                                          (fun (σ':Env) => And (c0 σ' ((10:Nat))) (c2 σ')) c10
                                                                                          (@And.intro (c0 c10 ((10:Nat))) (c2 c10)
                                                                                            (RunStep.mono B (command (@some Bool true)) σ c10 (c11 c13 c19)
                                                                                              ((10:Nat))
                                                                                              (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                                                                                (Com.seq c20 c21) σ c3 c10 c13 c19
                                                                                                (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                                                                  ((0:Nat))
                                                                                                  (RunStep.eval_lit B ((0:Nat)) σ
                                                                                                    ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                                                                                (RunStep.seq B c20 c21 c3 c9 c10 c17 c18
                                                                                                  (RunStep.assign B c3 "rat.n" c16 c8
                                                                                                    (RunStep.eval_mul B c3 (Expr.var "left.n") c15 c5 c7 (RunStep.eval_var B c3 "left.n" ?_)
                                                                                                      (RunStep.eval_sub B c3 (Expr.lit ((1:Nat)))
                                                                                                        (Expr.var "right.n") ((1:Nat)) c6
                                                                                                        (RunStep.eval_lit B ((1:Nat)) c3 h1)
                                                                                                        (RunStep.eval_var B c3 "right.n" ?_)
                                                                                                        ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                                      ?_))
                                                                                                  (RunStep.assign B c9 "rat.d" (Expr.lit ((1:Nat)))
                                                                                                    ((1:Nat))
                                                                                                    (RunStep.eval_lit B ((1:Nat)) c9 h1))))
                                                                                              ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                                                            ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                                                                               )
    all_goals simp_all [bit,flag,FractionOutput,fractionValue] <;> omega

end Lax455465Proofs.RamBooleanArithmetic

end

section

namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

@[simp] theorem length_coefficients (qs ms:List ℚ≥0):(coefficients qs ms).length=qs.length:=List.length_ofFn

def Context (source mask:String) (qs ms:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "sum.count"=qs.length∧ Prefix (RamUnsignedBuffer.encode qs) source σ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem coefficient_at (qs ms:List ℚ≥0) (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length):
    (coefficients qs ms)[i]'(by simpa only [coefficients,List.length_ofFn] using hi) =
      if (ms[i]'(by omega)).num=1 then qs[i] else 0:=by
  simp only [coefficients,List.getElem_ofFn,List.getD_eq_get ms 0 (⟨i,by omega⟩:Fin ms.length)]
  rfl

theorem entry_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (i:ℕ) (hi:i < qs.length) (hB:2*M^2+3 < B)
    (hindex:2*i+1 < B) (hqn:qs[i].num≤ M) (hqd:qs[i].den≤ M)
    (hmn:(ms[i]'(by omega)).num≤ M) (hmd:(ms[i]'(by omega)).den≤ M):
    Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]'(by simpa only [length_coefficients] using hi):ℚ) τ) 32:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hmi:i < ms.length:=by omega
  rintro σ ⟨hctx,hidx⟩
  obtain ⟨ν,rm,pm⟩:=RamUnsignedBuffer.read_spec B mask "sum.i" ms i hmi (by nlinarith) hindex
    (hmn.trans_lt hM) (hmd.trans_lt hM) (by decide) σ ⟨hctx.2.2,hidx⟩
  have hnum:ν.vars "rat.n"=ms[i].num:=by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  have hctxν:Context source mask qs ms ν:=by
    simpa only [Context,Prefix,rm.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
      rm.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
      rm.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctx
  have hidxν:ν.vars "sum.i"=i:=(rm.frame_var "sum.i" (by simp [RamUnsignedBuffer.read,Com.wvars])).trans hidx
  have hc:(Cond.eq (.var "rat.n") (.lit 1)).evalB B ν=some (decide (ms[i].num=1)):=by
    rw [evalB_condEq (evalB_var (hnum ▸ hmn.trans_lt hM)) (evalB_lit h1),hnum]
    congr 1
  by_cases hm:ms[i].num=1
  · obtain ⟨τ,rq,pq⟩:=RamUnsignedBuffer.read_spec B source "sum.i" qs i hi (by nlinarith) hindex
      (hqn.trans_lt hM) (hqd.trans_lt hM) (by decide) ν ⟨hctxν.2.1,hidxν⟩
    have rr:=rm.seq (Run.ite_true (d:=RamFractionPrimitives.zero) (by simpa only [hm,decide_true] using hc) rq)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rq.frame_var "sum.count" (by simp [RamUnsignedBuffer.read,Com.wvars]),
        rq.frame_arr source (by simp [RamUnsignedBuffer.read,Com.warrs]),
        rq.frame_arr mask (by simp [RamUnsignedBuffer.read,Com.warrs])] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_pos hm] using pq.1
  · obtain ⟨τ,rz,pz⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    have rr:=rm.seq (Run.ite_false (c:=RamUnsignedBuffer.read source "sum.i") (by simpa only [hm,decide_false] using hc) rz)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,Prefix,rz.frame_var "sum.count" (by decide),rz.frame_arr source (by change source∉ ([]:List String); simp),
        rz.frame_arr mask (by change mask∉ ([]:List String); simp)] using hctxν
    · simpa only [coefficient_at qs ms hlen i hi,if_neg hm,NNRat.coe_zero] using pz

theorem command_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (hB:2*M^2+3 < B) (hindex:2*qs.length+2 < B)
    (hqn:∀ q∈ qs,q.num≤ M) (hqd:∀ q∈ qs,q.den≤ M)
    (hmn:∀ q∈ ms,q.num≤ M) (hmd:∀ q∈ ms,q.den≤ M)
    (hprefixNum:∀ i, ((coefficients qs ms).take i).sum.num≤ M)
    (hprefixDen:∀ i, ((coefficients qs ms).take i).sum.den≤ M):
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ∧ FractionOutput (((coefficients qs ms).sum:ℚ≥0):ℚ) τ)
      ((36*(M^2).size+152)*qs.length+16):=by
  have hM1:1≤ M:=by simpa only [List.take_zero,List.sum_nil,NNRat.den_zero] using hprefixDen 0
  have hnum:∀ q∈ coefficients qs ms,q.num≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqn _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.num_zero] using Nat.zero_le M
  have hden:∀ q∈ coefficients qs ms,q.den≤ M:=by
    intro q hq
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    split_ifs
    · exact hqd _ (List.getElem_mem i.isLt)
    · simpa only [NNRat.den_zero] using hM1
  have hbody:∀ i, ∀ hi:i < (coefficients qs ms).length,
      Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "sum.i"=i) (entry source mask)
        (fun _ τ => Context source mask qs ms τ∧ FractionOutput ((coefficients qs ms)[i]:ℚ) τ) 32:=by
    intro i hi
    have hq:i < qs.length:=by simpa only [length_coefficients] using hi
    have hm:i < ms.length:=by omega
    exact entry_spec B M source mask qs ms hlen i hq hB (by omega)
      (hqn _ (List.getElem_mem hq)) (hqd _ (List.getElem_mem hq))
      (hmn _ (List.getElem_mem hm)) (hmd _ (List.getElem_mem hm))
  have hf:=RamUnsignedSum.command_spec B M 32 (Context source mask qs ms)
    "sum.i" "sum.count" (coefficients qs ms) (entry source mask) hB
    (by rw [length_coefficients]; omega) hnum hden hprefixNum hprefixDen
    (fun _ h => by simpa only [length_coefficients] using h.1)
    (fun σ k name h hn => by
      rcases hn with rfl | rfl | rfl <;>
        simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (by decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (by dsimp [entry,RamUnsignedBuffer.read,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
    (fun rr h => by
      simpa only [Context,Prefix,rr.frame_var "sum.count" (by decide),
        rr.frame_arr source (by change source∉ ([]:List String); simp),
        rr.frame_arr mask (by change mask∉ ([]:List String); simp)] using h)
  unfold command
  rw [length_coefficients] at hf
  convert hf using 1 <;> ring

end Lax455465Proofs.RamMaskedSum

end

section

namespace Lax455465Proofs.MaskedMassData

open LpInputSize
open scoped BigOperators NNRat

theorem coefficients_ofFn {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    RamMaskedSum.coefficients (List.ofFn weights) (flags mask) =
      List.ofFn (fun v => if mask v then weights v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,List.length_ofFn]
  · intro i hi hj
    have hn:i < n:=by simpa only [RamMaskedSum.length_coefficients,List.length_ofFn] using hi
    rw [RamMaskedSum.coefficient_at (List.ofFn weights) (flags mask) (by simp [flags]) i (by simpa using hn)]
    simp only [flags,List.getElem_ofFn]
    cases h:mask ⟨i,hn⟩ <;> simp [h]

theorem coe_sum {n:ℕ} (weights:Fin n→ ℚ≥0) (mask:Fin n→ Bool):
    (((RamMaskedSum.coefficients (List.ofFn weights) (flags mask)).sum:ℚ≥0):ℚ) =
      ∑ v,if mask v then (weights v:ℚ) else 0:=by
  rw [coefficients_ofFn,List.sum_ofFn,NNRat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  cases mask v <;> rfl

end Lax455465Proofs.MaskedMassData

end

section

namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def Context {n:ℕ} (source:String) (mask:Fin n→ Bool) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags mask)) source σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {source:String} {mask:Fin n→ Bool} (h:Context source mask σ)
    (ha:source∉ cmd.warrs) (hx:∀ x∈ ["metric.n","metric.n2"],x∉ cmd.wvars):
    Context source mask τ:=by
  simpa only [Context,Prefix,hr.frame_arr source ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

theorem coefficient_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source:String)
    (mask:Fin n→ Bool) (u v:Fin n) (h2:2 < B) (hn:n < B) (hn2:n*n < B)
    (hindex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val)
      (coefficient mode source)
      (fun _ τ => Context source mask τ∧ FractionOutput ((matrix mode mask u v:ℚ≥0):ℚ) τ) 60:=by
  let qs:=MaskedMassData.flags mask
  have hlen:qs.length=n:=List.length_ofFn
  have hvalue (t:Fin n):qs[t.val]=RamBooleanArithmetic.bit (mask t):=by
    simp only [qs,MaskedMassData.flags,List.getElem_ofFn,RamBooleanArithmetic.bit]
  have hnum (t:Fin n):qs[t.val].num < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hden (t:Fin n):qs[t.val].den < B:=by
    rw [hvalue]; cases mask t <;> simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨σ₁,r₁,p₁⟩:=RamDualDistancesInit.indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctx₁:=frame r₁ hctx (by simp [RamDualDistancesInit.indices,Com.warrs]) (by decide)
  obtain ⟨σ₂,r₂,p₂⟩:=RamUnsignedBuffer.read_spec B source "metric.u" qs u.val
    (by simpa only [hlen] using u.isLt) h2 (by omega) (hnum u) (hden u) (by decide) σ₁ ⟨hctx₁.2.2,p₁.1⟩
  obtain ⟨σ₃,r₃,p₃⟩:=RamUnsignedArithmetic.copy_spec B qs[u.val] "left" (by omega)
    (hnum u) (hden u) (by decide) σ₂ p₂.1
  have hctx₃:=frame r₃ (frame r₂ hctx₁ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hv₃:σ₃.vars "metric.v"=v.val:=
    (r₃.frame_var _ (by decide)).trans ((r₂.frame_var _ (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)).trans p₁.2)
  obtain ⟨σ₄,r₄,p₄⟩:=RamUnsignedBuffer.read_spec B source "metric.v" qs v.val
    (by simpa only [hlen] using v.isLt) h2 (by omega) (hnum v) (hden v) (by decide) σ₃ ⟨hctx₃.2.2,hv₃⟩
  obtain ⟨σ₅,r₅,p₅⟩:=RamUnsignedArithmetic.copy_spec B qs[v.val] "right" (by omega)
    (hnum v) (hden v) (by decide) σ₄ p₄.1
  have hctx₅:=frame r₅ (frame r₄ hctx₃ (by simp [RamUnsignedBuffer.read,Com.warrs]) (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide))
    (by simp [RamUnsignedArithmetic.copy,Com.warrs]) (by decide)
  have hleft:σ₅.vars "left.s"=0∧ σ₅.vars "left.n"=(RamBooleanArithmetic.bit (mask u)).num∧ σ₅.vars "left.d"=1:=by
    rw [r₅.frame_var "left.s" (by decide),r₅.frame_var "left.n" (by decide),r₅.frame_var "left.d" (by decide),
      r₄.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide),r₄.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,Com.wvars]; decide)]
    have hp:=p₃
    rw [hvalue u] at hp
    cases hu:mask u <;> simpa [RamBooleanArithmetic.bit,hu] using hp
  have hright:σ₅.vars "right.s"=0∧ σ₅.vars "right.n"=(RamBooleanArithmetic.bit (mask v)).num∧ σ₅.vars "right.d"=1:=by
    have hp:=p₅
    rw [hvalue v] at hp
    cases hv:mask v <;> simpa [RamBooleanArithmetic.bit,hv] using hp
  obtain ⟨τ,r₆,p₆⟩:=RamBooleanArithmetic.command_spec B mode (mask u) (mask v) (by omega) σ₅
    ⟨hleft.1,hleft.2.1,hleft.2.2,hright.1,hright.2.1,hright.2.2⟩
  refine ⟨τ,r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆)))),
    frame r₆ hctx₅ (by cases mode with | none => simp [RamBooleanArithmetic.command,Com.warrs] | some b => cases b <;> simp [RamBooleanArithmetic.command,Com.warrs])
      (by cases mode with | none => decide | some b => cases b <;> decide),p₆⟩

theorem command_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (source target:String)
    (mask:Fin n→ Bool) (hneq:source ≠ target) (h2:2 < B) (hn:n < B)
    (hn2:n*n < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B):
    Spec B (fun σ => Context source mask σ∧ 2*(n*n) < (σ.arrs target).length)
      (command mode source target)
      (fun _ τ => Context source mask τ∧ Prefix (RamUnsignedBuffer.encode (values (matrix mode mask))) target τ)
      (82*(n*n)+8):=by
  let qs:=values (matrix mode mask)
  have hlen:qs.length=n*n:=length_values _
  have hwords:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    simp only [qs,values,matrix,List.getElem_ofFn]
    cases RamBooleanArithmetic.flag mode (mask _) (mask _) <;> simp [RamBooleanArithmetic.bit] <;> omega
  have hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => Context source mask σ∧ σ.vars "metric.entry"=i)
        (coefficient mode source) (fun _ τ => Context source mask τ∧ FractionOutput (qs[i]:ℚ) τ) 60:=by
    intro i hi
    have he:i < n*n:=by rwa [hlen] at hi
    let uv:=(edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
    have hidx:edgeIndex n uv=(⟨i,he⟩:Fin (n*n)):=(edgeIndex n).apply_symm_apply _
    simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
      coefficient_spec B mode source mask uv.1 uv.2 h2 hn hn2 hvertex
  have hfresh (x:String) (h:x∈ ["metric.entry","mask.position"]):
      x∉ (coefficient mode source).wvars:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
    · subst x; cases mode with
      | none => dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; decide
      | some b => cases b <;> dsimp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars] <;> decide
  have hloop:=RamUnsignedVector.command_spec B 60 (Context source mask)
    "metric.entry" "metric.n2" target "mask.position" qs [] (coefficient mode source) (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody (hfresh _ (by simp)) (hfresh _ (by simp))
    (by cases mode with
      | none => simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs]
      | some b => cases b <;> simp [coefficient,RamDualDistancesInit.indices,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.warrs])
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => frame rr h (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq])
      (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "mask.position" 0
  have rzero:Run B (.assign "mask.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:=frame rzero hctx (by simp [Com.warrs]) (by decide)
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamArcMask

end

section

namespace Lax455465Proofs.BallMassData

open scoped BigOperators NNRat

theorem mask_eq {n:ℕ} (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    mask distance radius=MaskedMassData.flags (fun v => decide ((distance v:ℚ) < (radius:ℚ))):=by
  simp only [mask,List.map_ofFn,MaskedMassData.flags]
  congr 1
  funext v
  simp [RamBallMask.flag]

end Lax455465Proofs.BallMassData

end

section

namespace Lax455465Proofs.BoundaryData

open MetricMatrix
open scoped BigOperators NNRat

theorem masked_matrix {n:ℕ} (capacity flags:Matrix n):
    RamMaskedSum.coefficients (values capacity) (values flags) =
      values (fun u v => if (flags u v).num=1 then capacity u v else 0):=by
  apply List.ext_getElem
  · simp only [RamMaskedSum.length_coefficients,length_values]
  · intro i hi hj
    have he:i < n*n:=by simpa only [RamMaskedSum.length_coefficients,length_values] using hi
    rw [RamMaskedSum.coefficient_at (values capacity) (values flags) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

end Lax455465Proofs.BoundaryData

end

section

namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (value a b:ℚ) τ) (36*(a.den*b.den).size+142):=by
  have h1:1 < B:=by nlinarith
  have ha:=RamUnsignedArithmetic.value a
  have hb:=RamUnsignedArithmetic.value b
  rintro σ hinputs
  obtain ⟨ν,hcompare,hpost⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den
    hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos σ hinputs
  have hinputsν:fractionInputs 0 a.num a.den 0 b.num b.den ν:=by
    simpa only [fractionInputs,hcompare.frame_var "left.s" (by decide),hcompare.frame_var "left.n" (by decide),
      hcompare.frame_var "left.d" (by decide),hcompare.frame_var "right.s" (by decide),
      hcompare.frame_var "right.n" (by decide),hcompare.frame_var "right.d" (by decide)] using hinputs
  have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some (decide (ν.vars "cmp.le"=1)):=by
    rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1)]
    congr 1
  by_cases hab:(a:ℚ)≤ (b:ℚ)
  · have hflag:ν.vars "cmp.le"=1:=hpost.2.mpr (by rwa [ha,hb])
    obtain ⟨τ,hr,ht⟩:=RamFractionPrimitives.zero_spec B h1 ν trivial
    refine ⟨τ,(hcompare.seq (Run.ite_true (d:=difference) (by simpa only [hflag,decide_true] using hc) hr)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simpa only [value,NNRat.coe_mk,max_eq_right (sub_nonpos.mpr hab)] using ht
  · have hflag:¬ν.vars "cmp.le"=1:=fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    let μ:=ν.setVar "right.s" 1
    have hr:Run B (.assign "right.s" (.lit 1)) ν μ 2:=Run.assign (evalB_lit h1)
    have hμ:fractionInputs 0 a.num a.den 1 b.num b.den μ:=by
      simpa [μ,fractionInputs,vars_setVar] using
        And.intro hinputsν.1 (And.intro hinputsν.2.1 (And.intro hinputsν.2.2.1 (And.intro (rfl:(1:ℕ)=1) hinputsν.2.2.2.2)))
    obtain ⟨τ,haRun,haPost⟩:=addFraction_spec B M 0 a.num a.den 1 b.num b.den hB
      (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos μ hμ
    have hdifference:Run B difference ν τ (36*(a.den*b.den).size+98):=by
      have hh:=hr.seq haRun
      unfold difference
      convert hh using 1 <;> omega
    refine ⟨τ,(hcompare.seq (Run.ite_false (c:=RamFractionPrimitives.zero) (by simpa only [hflag,decide_false] using hc) hdifference)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    have hnegative:fractionValue 1 b.num b.den=-(b:ℚ):=by
      simpa [fractionValue,neg_div] using congrArg Neg.neg hb
    change FractionOutput (max ((a:ℚ)-(b:ℚ)) 0) τ
    rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hab)),sub_eq_add_neg]
    simpa only [ha,hnegative] using haPost

end Lax455465Proofs.RamTruncatedSubtract

end

section

namespace Lax455465Proofs.RoundingConstants
open scoped NNRat

theorem inverse_height {M:ℕ} {q:ℚ≥0} (hM:1≤ M) (hq:LpInputSize.Height M (q:ℚ)):
    LpInputSize.Height M ((q⁻¹:ℚ≥0):ℚ):=by
  simp only [LpInputSize.Height,NNRat.coe_inv,Rat.num_inv,Rat.den_inv]
  have habs:(q:ℚ).num.sign.natAbs≤1:=by
    rw [Int.natAbs_sign]; split_ifs <;> omega
  constructor
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast,Nat.one_mul] using
      (Nat.mul_le_mul habs hq.2)
  · split_ifs
    · exact hM
    · exact hq.1

end Lax455465Proofs.RoundingConstants

end

section

namespace Lax455465Proofs.RamScalarInverse
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B:ℕ) (name:String) (q:ℚ≥0) (h1:1< B)
    (hn:q.num< B) (hd:q.den< B)
    (hfresh:name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n"):
    Spec B (Stored name q) (command name)
      (fun _ τ => FractionOutput ((q⁻¹:ℚ≥0):ℚ) τ) (36*q.num.size+52):=by
  rintro σ hσ
  obtain ⟨ν,rl,pl⟩:=load_spec B name q h1 hn hd hfresh σ hσ
  obtain ⟨μ,rc,pc⟩:=RamUnsignedArithmetic.copy_spec B q "left" h1 hn hd (by decide) ν pl
  obtain ⟨τ,ri,pi⟩:=invertFraction_spec B 0 q.num q.den h1 (by omega) hn hd μ pc
  exact ⟨τ,(rl.seq (rc.seq ri)).mono (by omega),by simpa only [RamUnsignedArithmetic.value,NNRat.coe_inv] using pi⟩

end Lax455465Proofs.RamScalarInverse

end

section

namespace Lax455465Proofs.RamScalarBinary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M K:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (operation:Com) (q:ℚ) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (hop:Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) operation
      (fun _ τ => FractionOutput q τ) K):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName operation) (fun _ τ => FractionOutput q τ) (K+24):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rleft,pleft⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1
    (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rleft
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,
      rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rright,pright⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1
    (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have pleftη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have rr:=rb.seq rright
    simpa only [rr.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),rr.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      rr.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pleft
  obtain ⟨τ,rop,pop⟩:=hop η ⟨pleftη.1,pleftη.2.1,pleftη.2.2,by simpa only [String.reduceAppend] using pright⟩
  refine ⟨τ,(ra.seq (rleft.seq (rb.seq (rright.seq rop)))).mono (by omega),pop⟩

end Lax455465Proofs.RamScalarBinary

end

section

namespace Lax455465Proofs.RamArrayScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

theorem command_spec (B:ℕ) (array index name:String) (qs:List ℚ≥0) (i:ℕ)
    (hi:i < qs.length) (h2:2 < B) (hindex:2*i+1 < B)
    (hn:qs[i].num < B) (hd:qs[i].den < B)
    (hfresh:index ≠ "rat.n" ∧ index ≠ "rat.d" ∧ index ≠ "rat.s")
    (hname:name ++ ".n" ≠ "rat.d"):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) array σ∧ σ.vars index=i)
      (command array index name) (fun _ τ => Stored name qs[i] τ) 18:=by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamUnsignedBuffer.read_spec B array index qs i hi h2 hindex hn hd hfresh σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B name qs[i] hn hd hname ν pr.1
  exact ⟨τ,rr.seq rs,ps⟩

end Lax455465Proofs.RamArrayScalar

end

section

namespace Lax455465Proofs.RamRootDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat

def vector {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n):List ℚ≥0:=
  List.ofFn fun v => if outward then d root v else d v root

@[simp] theorem length_vector {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n):
    (vector outward root d).length=n:=List.length_ofFn

def Context {n:ℕ} (root:Fin n) (d:Matrix n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "region.root"=root.val∧
    Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {root:Fin n} {d:Matrix n} (h:Context root d σ)
    (ha:"metric.old" ∉ cmd.warrs) (hn:"metric.n" ∉ cmd.wvars)
    (hroot:"region.root" ∉ cmd.wvars):Context root d τ:=by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.n" hn,hr.frame_var "region.root" hroot] using h

theorem entry_spec (B H:ℕ) {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n) (v:Fin n)
    (hH:H < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H):
    Spec B (fun σ => Context root d σ∧ σ.vars "region.i"=v.val) (entry outward)
      (fun _ τ => Context root d τ∧ FractionOutput ((vector outward root d)[v.val]:ℚ) τ) 20:=by
  let u:=if outward then root else v
  let t:=if outward then v else root
  let address:=(edgeIndex n (u,t)).val
  have ha:address < n*n:=(edgeIndex n (u,t)).isLt
  have hval:(values d)[address]=d u t:=value_at d u t
  have hvector:(vector outward root d)[v.val]=d u t:=by
    simp only [vector,List.getElem_ofFn,u,t]
    cases outward <;> rfl
  rintro σ ⟨hctx,hi⟩
  let ν:=σ.setVar "region.address" address
  have haddr:Run B (.assign "region.address" (if outward then .add (.mul (.var "region.root") (.var "metric.n")) (.var "region.i")
      else .add (.mul (.var "region.i") (.var "metric.n")) (.var "region.root"))) σ ν 6:=by
    have hroot:root.val < B:=root.isLt.trans hn
    have hv:v.val < B:=v.isLt.trans hn
    have hprodR:root.val*n < B:=(by nlinarith [root.isLt]:root.val*n < n*n).trans hn2
    have hprodV:v.val*n < B:=(by nlinarith [v.isLt]:v.val*n < n*n).trans hn2
    cases outward with
    | false =>
      have heq:address=v.val*n+root.val:=by simp [address,u,t,FlowLpIndices.edge_value]
      have hm:=evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodV
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op:=.add) hm
        (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩) (by change v.val*n+root.val < B; rw [←heq]; exact ha.trans hn2)):Run B _ _ _ 6)
    | true =>
      have heq:address=root.val*n+v.val:=by simp [address,u,t,FlowLpIndices.edge_value]
      have hm:=evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hctx.2.1.symm,hctx.2.1 ▸ hroot⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.1.symm,hctx.1 ▸ hn⟩) hprodR
      simpa only [Bool.false_eq_true,if_false,if_pos rfl,ν,heq,Expr.size,Bop.apply,Nat.reduceAdd,if_true] using (Run.assign (evalB_bin (op:=.add) hm
        (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hv⟩) (by change root.val*n+v.val < B; rw [←heq]; exact ha.trans hn2)):Run B _ _ _ 6)
  have hctxν:=frame haddr hctx (by simp [Com.warrs]) (by simp [Com.wvars]) (by simp [Com.wvars])
  obtain ⟨τ,rr,pr⟩:=RamUnsignedBuffer.read_spec B "metric.old" "region.address" (values d) address
    (by simpa only [length_values] using ha) (by omega) (by omega)
    (by rw [hval]; exact (hnum u t).trans_lt hH) (by rw [hval]; exact (hden u t).trans_lt hH)
    (by decide) ν ⟨hctxν.2.2,by simp [ν]⟩
  refine ⟨τ,haddr.seq rr,frame rr hctxν (by decide) (by decide) (by decide),?_⟩
  simpa only [hval,hvector] using pr.1

theorem command_spec (B H:ℕ) {n:ℕ} (outward:Bool) (root:Fin n) (d:Matrix n)
    (hH:H < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H):
    Spec B (fun σ => Context root d σ∧ 2*n < (σ.arrs (array outward)).length) (command outward)
      (fun _ τ => Context root d τ∧ Prefix (RamUnsignedBuffer.encode (vector outward root d)) (array outward) τ)
      (42*n+8):=by
  let qs:=vector outward root d
  have hlen:qs.length=n:=List.length_ofFn
  have hwords:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    have hv:i < n:=by rwa [hlen] at hi
    have heq:qs[i]=if outward then d root ⟨i,hv⟩ else d ⟨i,hv⟩ root:=by
      dsimp only [qs,vector]
      erw [List.getElem_ofFn]
    rw [heq]
    cases outward <;> exact ⟨(hnum _ _).trans_lt hH,(hden _ _).trans_lt hH⟩
  have hloop:=RamUnsignedVector.command_spec B 20 (Context root d)
    "region.i" "metric.n" (array outward) "region.pos" qs [] (entry outward) (by omega)
    (by have hnpositive:=root.isLt; simp only [List.length_nil,hlen]; nlinarith)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun σ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have hv:i < n:=by rwa [hlen] at hi
      exact entry_spec B H outward root d ⟨i,hv⟩ hH hn hn2 hindex hnum hden)
    (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide)
    (by cases outward <;> decide)
    (fun rr h => frame rr h (by cases outward <;> decide) (by cases outward <;> decide) (by cases outward <;> decide))
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "region.pos" 0
  have rzero:Run B (.assign "region.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:=frame rzero hctx (by decide) (by decide) (by decide)
  obtain ⟨τ,rr,pr⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlen,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamRootDistances

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

theorem num_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.num≤ M:=by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.den≤ M:=by
  simpa only [NNRat.den_coe] using h.2

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamScalarReciprocal
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem command_spec (B M:ℕ) (q:ℚ≥0) (source target:String) (hM:1≤ M) (hB:M< B)
    (hq:LpInputSize.Height M (q:ℚ))
    (hsource:source++".n"≠"rat.s" ∧ source++".d"≠"rat.s" ∧ source++".d"≠"rat.n")
    (htarget:target++".n"≠"rat.d"):
    Spec B (Stored source q) (command source target) (fun _ τ => Stored target q⁻¹ τ)
      (36*q.num.size+56):=by
  have hi:=RoundingConstants.inverse_height hM hq
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarInverse.command_spec B source q (by omega)
    ((num_bound hq).trans_lt hB) ((den_bound hq).trans_lt hB) hsource σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target q⁻¹ ((num_bound hi).trans_lt hB) ((den_bound hi).trans_lt hB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarReciprocal

end

section

namespace Lax455465Proofs.RamScalarProduct
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName target:String)
    (hB:2*M^2+3< B) (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh:rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain:rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget:target++".n"≠"rat.d"):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a*b) τ) (36*(a.den*b.den).size+92):=by
  have ha:LpInputSize.Height M (a:ℚ):= ⟨by simpa only [NNRat.natAbs_num_coe] using han,by simpa only [NNRat.den_coe] using had⟩
  have hb:LpInputSize.Height M (b:ℚ):= ⟨by simpa only [NNRat.natAbs_num_coe] using hbn,by simpa only [NNRat.den_coe] using hbd⟩
  have hp:=LpInputSize.height_mul ha hb
  have hpnum:(a*b).num< B:=(show (a*b).num≤ M*M by simpa only [←NNRat.coe_mul,NNRat.natAbs_num_coe] using hp.1).trans_lt (by nlinarith)
  have hpden:(a*b).den< B:=(show (a*b).den≤ M*M by simpa only [←NNRat.coe_mul,NNRat.den_coe] using hp.2).trans_lt (by nlinarith)
  have hop:=multiplyFraction_spec B M 0 a.num a.den 0 b.num b.den hB (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarBinary.command_spec B M (36*(a.den*b.den).size+64) a b leftName rightName multiplyFraction ((a*b:ℚ≥0):ℚ)
    hB han had hbn hbd hlfresh hrfresh hrretain (by simpa only [RamUnsignedArithmetic.value,NNRat.coe_mul] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target (a*b) hpnum hpden htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarProduct

end

section

namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext RoundingConstants
open scoped NNRat

theorem storedFrame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {name:String} {q:ℚ≥0} (h:Stored name q σ)
    (hn:name++".n"∉cmd.wvars) (hd:name++".d"∉cmd.wvars):Stored name q τ:=by
  simpa only [Stored,rr.frame_var (name++".n") hn,rr.frame_var (name++".d") hd] using h

end Lax455465Proofs.RamRoundingConstants

end

section

namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem first_succ (predicate:ℕ→ Bool) (i:ℕ):
    first predicate (i+1)=match first predicate i with
      | some j => some j
      | none => if predicate i then some i else none:=by
  simp only [first,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  cases h:(List.range i).find? predicate <;> cases predicate i <;> rfl

def Invariant (R:Env→ Prop) (predicate:ℕ→ Bool) (count:ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars "find.i" ≤ count∧ Matches (first predicate (σ.vars "find.i")) σ

set_option maxHeartbeats 0 in

theorem command_spec (B count K:ℕ) (R:Env→ Prop) (predicate:ℕ→ Bool) (body:Com)
    (h1:1 < B) (hcount:count < B)
    (hlimit:∀ σ,R σ→ σ.vars "find.count"=count)
    (hset:∀ σ k name,R σ→ name∈ ["find.i","find.found","find.result"]→ R (σ.setVar name k))
    (hbody:∀ i,i < count→ Spec B (fun σ => R σ∧ σ.vars "find.i"=i) body
      (fun _ τ => R τ∧ τ.vars "find.ok"=if predicate i then 1 else 0) K)
    (hfresh:"find.i" ∉ body.wvars∧ "find.found" ∉ body.wvars∧ "find.result" ∉ body.wvars):
    Spec B R (command body) (fun _ τ => R τ∧ Matches (first predicate count) τ)
      ((K+20)*count+10):=by
  have hprocess:∀ i,i < count→
      Spec B (fun σ => R σ∧ σ.vars "find.i"=i∧ Matches (first predicate i) σ)
        (process body) (fun _ τ => R τ∧ τ.vars "find.i"=i∧ Matches (first predicate (i+1)) τ) (K+12):=by
    intro i hi σ ⟨hR,hindex,hmatch⟩
    have hiB:i < B:=hi.trans hcount
    cases hs:first predicate i with
    | some j =>
      have hm:σ.vars "find.found"=1∧ σ.vars "find.result"=j:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some false:=by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit (by omega)),hm.1]
        rfl
      refine ⟨σ,(Run.ite_false (c:=.seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hR,hindex,?_⟩
      rw [first_succ,hs]
      exact hm
    | none =>
      have hm:σ.vars "find.found"=0:=by simpa only [hs,Matches] using hmatch
      have hc:(Cond.eq (.var "find.found") (.lit 0)).evalB B σ=some true:=by
        rw [evalB_condEq (evalB_var (hm ▸ (by omega:0 < B))) (evalB_lit (by omega)),hm]
        rfl
      obtain ⟨ν,rb,pb⟩:=hbody i hi σ ⟨hR,hindex⟩
      have hiν:ν.vars "find.i"=i:=(rb.frame_var "find.i" hfresh.1).trans hindex
      have hmν:ν.vars "find.found"=0:=(rb.frame_var "find.found" hfresh.2.1).trans hm
      cases hp:predicate i with
      | false =>
        have hok:ν.vars "find.ok"=0:=by simpa only [hp,Bool.false_eq_true,if_false] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some false:=by
          rw [evalB_condEq (evalB_var (hok ▸ (by omega:0 < B))) (evalB_lit h1),hok]
          rfl
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_false (c:=record) hcok Run.skip))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pb.1,hiν,?_⟩
        rw [first_succ,hs,hp]
        exact hmν
      | true =>
        have hok:ν.vars "find.ok"=1:=by simpa only [hp,if_true] using pb.2
        have hcok:(Cond.eq (.var "find.ok") (.lit 1)).evalB B ν=some true:=by
          rw [evalB_condEq (evalB_var (hok ▸ h1)) (evalB_lit h1),hok]
          rfl
        let τ:=(ν.setVar "find.found" 1).setVar "find.result" i
        have rrecord:Run B record ν τ 4:=(Run.assign (evalB_lit h1)).seq
          (Run.assign (by rw [evalB_var_iff]; exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hiν.symm,
            by simpa only [vars_setVar,String.reduceEq,if_false] using hiν ▸ hiB⟩))
        have rr:=Run.ite_true (d:=Com.skip) hc (rb.seq (Run.ite_true (d:=Com.skip) hcok rrecord))
        refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_,?_⟩
        · exact hset _ i "find.result" (hset ν 1 "find.found" pb.1 (by simp)) (by simp)
        · simpa only [τ,vars_setVar,String.reduceEq,if_false] using hiν
        · rw [first_succ,hs,hp]
          simp [Matches,τ]
  have hstep:Spec B (fun σ => Invariant R predicate count σ∧ σ.vars "find.i" < count)
      (step body) (fun σ τ => Invariant R predicate count τ∧ τ.vars "find.i"=σ.vars "find.i"+1) (K+16):=by
    rintro σ ⟨⟨hR,hi,hmatch⟩,hlt⟩
    let i:=σ.vars "find.i"
    obtain ⟨ν,rr,pr⟩:=hprocess i hlt σ ⟨hR,rfl,hmatch⟩
    have hiν:ν.vars "find.i"=i:=pr.2.1
    have rinc:Run B (.assign "find.i" (.add (.var "find.i") (.lit 1))) ν (ν.setVar "find.i" (i+1)) 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega:i < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega))
    refine ⟨ν.setVar "find.i" (i+1),(rr.seq rinc).mono (by omega),?_,by simp [i]⟩
    refine ⟨hset ν (i+1) "find.i" pr.1 (by simp),by simp; omega,?_⟩
    change Matches (first predicate (i+1)) (ν.setVar "find.i" (i+1))
    cases h:first predicate (i+1) <;>
      simpa only [h,Matches,vars_setVar,String.reduceEq,if_false] using pr.2.2
  have hscan:=Spec.forRangeZero "find.i" "find.count" (Invariant R predicate count) count (K+16)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hR
  let ν:=(σ.setVar "find.found" 0).setVar "find.result" 0
  have rinit:Run B init σ ν 4:=(Run.assign (evalB_lit (by omega:0 < B))).seq (Run.assign (evalB_lit (by omega)))
  have hRν:R ν:=hset _ 0 "find.result" (hset σ 0 "find.found" hR (by simp)) (by simp)
  have hinvariant:Invariant R predicate count (ν.setVar "find.i" 0):=by
    refine ⟨hset ν 0 "find.i" hRν (by simp),by simp,?_⟩
    simp [first,Matches,ν]
  obtain ⟨τ,rr,pr⟩:=hscan ν hinvariant
  refine ⟨τ,(rinit.seq rr).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,?_⟩
  simpa only [pr.2] using pr.1.2.2

theorem first_some (predicate:ℕ→ Bool) (count i:ℕ) (h:first predicate count=some i):
    i < count∧ predicate i=true:=by
  exact ⟨List.mem_range.mp (List.mem_of_find?_eq_some h),List.find?_some h⟩

theorem first_none (predicate:ℕ→ Bool) (count:ℕ) (h:first predicate count=none):
    ∀ i < count,predicate i=false:=by
  intro i hi
  exact Bool.eq_false_iff.mpr (List.find?_eq_none.mp h i (List.mem_range.mpr hi))

end Lax455465Proofs.RamFind

end

section

namespace Lax455465Proofs.RamScalarComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName:String)
    (hB:2*M^2+3 < B) (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M)
    (hlfresh:leftName ++ ".n" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.s" ∧ leftName ++ ".d" ≠ "rat.n")
    (hrfresh:rightName ++ ".n" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.s" ∧ rightName ++ ".d" ≠ "rat.n")
    (hrretain:rightName ++ ".n" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName ++ ".d" ∉ (Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ)
      (command leftName rightName) (fun _ τ => τ.vars "cmp.le"=if (a:ℚ)≤ (b:ℚ) then 1 else 0) 64:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  rintro σ ⟨ha,hb⟩
  obtain ⟨ν,ra,pa⟩:=load_spec B leftName a h1 (han.trans_lt hM) (had.trans_lt hM) hlfresh σ ha
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B a "left" h1 (han.trans_lt hM) (had.trans_lt hM) (by decide) ν pa
  have hbμ:Stored rightName b μ:=by
    have rr:=ra.seq rl
    simpa only [Stored,rr.frame_var (rightName ++ ".n") hrretain.1,rr.frame_var (rightName ++ ".d") hrretain.2] using hb
  obtain ⟨ξ,rb,pb⟩:=load_spec B rightName b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) hrfresh μ hbμ
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B b "right" h1 (hbn.trans_lt hM) (hbd.trans_lt hM) (by decide) ξ pb
  have plη:η.vars "left.s"=0∧ η.vars "left.n"=a.num∧ η.vars "left.d"=a.den:=by
    have r:=rb.seq rr
    simpa only [r.frame_var "left.s" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),
      r.frame_var "left.n" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),r.frame_var "left.d" (by simp [load,RamUnsignedArithmetic.copy,Com.wvars]),String.reduceAppend] using pl
  obtain ⟨τ,rc,pc⟩:=RamComparison.compareFraction_spec B M 0 a.num a.den 0 b.num b.den hB
    (by omega) (by omega) han had hbn hbd a.den_pos b.den_pos η
    ⟨plη.1,plη.2.1,plη.2.2,by simpa only [String.reduceAppend] using pr⟩
  refine ⟨τ,ra.seq (rl.seq (rb.seq (rr.seq rc))),?_⟩
  have hp:τ.vars "cmp.le"=1↔ (a:ℚ)≤(b:ℚ):=by simpa only [RamUnsignedArithmetic.value] using pc.2
  by_cases h:(a:ℚ)≤(b:ℚ)
  · simpa only [if_pos h] using hp.mpr h
  · have hz:τ.vars "cmp.le"=0:=by have hn:=mt hp.mp h; omega
    simpa only [if_neg h] using hz

end Lax455465Proofs.RamScalarComparison

end

section

namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

@[simp] theorem length_words {n:ℕ} (history:List (Entry n)):(words history).length=4*history.length:=by
  induction history with
  | nil => rfl
  | cons e history ih => simp [words,Entry.words] at *; omega

structure Input {n:ℕ} (history:List (Entry n)) (e:Entry n) (σ:Env):Prop where
  data:Prefix (words history) "region.history" σ
  position:σ.vars "history.pos"=(words history).length
  root:σ.vars "region.root"=e.root.val
  radius:Stored "region.radius" e.radius σ
  outward:σ.vars "region.outward"=(if e.outward then 1 else 0)

theorem command_spec (B:ℕ) {n:ℕ} (history:List (Entry n)) (e:Entry n)
    (hlen:4*history.length+4< B) (hroot:n< B) (hnum:e.radius.num< B) (hden:e.radius.den< B):
    Spec B (fun σ => Input history e σ∧ 4*history.length+4≤(σ.arrs "region.history").length)
      command (fun _ τ => Prefix (words (history++[e])) "region.history" τ∧
        τ.vars "history.pos"=4*(history.length+1)) 28:=by
  have h1:1< B:=by omega
  let ws:=words history
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamWordBuffer.append_spec B "region.history" "history.pos" ws e.root.val (.var "region.root")
    h1 (by simp only [ws,length_words]; omega) σ
    ⟨hσ.data,hσ.position,by simp only [ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨hσ.root.symm,hσ.root ▸ e.root.isLt.trans hroot⟩⟩
  obtain ⟨σ2,r2,p2⟩:=RamWordBuffer.append_spec B "region.history" "history.pos" (ws++[e.root.val]) e.radius.num (.var "region.radius.n")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ1
    ⟨p1.1,by simpa only [List.length_append,List.length_singleton] using p1.2,
      by rw [RamFrames.run_array_length r1 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨((r1.frame_var _ (by decide)).trans hσ.radius.1).symm,
        ((r1.frame_var _ (by decide)).trans hσ.radius.1) ▸ hnum⟩⟩
  have r12:=r1.seq r2
  obtain ⟨σ3,r3,p3⟩:=RamWordBuffer.append_spec B "region.history" "history.pos" ((ws++[e.root.val])++[e.radius.num]) e.radius.den (.var "region.radius.d")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ2
    ⟨p2.1,by simpa only [List.length_append,List.length_singleton] using p2.2,
      by rw [RamFrames.run_array_length r12 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨((r12.frame_var _ (by decide)).trans hσ.radius.2).symm,
        ((r12.frame_var _ (by decide)).trans hσ.radius.2) ▸ hden⟩⟩
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨τ,r4,p4⟩:=RamWordBuffer.append_spec B "region.history" "history.pos" (((ws++[e.root.val])++[e.radius.num])++[e.radius.den]) (if e.outward then 1 else 0) (.var "region.outward")
    h1 (by simp only [List.length_append,List.length_singleton,ws,length_words]; omega) σ3
    ⟨p3.1,by simpa only [List.length_append,List.length_singleton] using p3.2,
      by rw [RamFrames.run_array_length r123 "region.history"]; simp only [List.length_append,List.length_singleton,ws,length_words]; omega,
      by rw [evalB_var_iff]; refine ⟨((r123.frame_var _ (by decide)).trans hσ.outward).symm,?_⟩
         rw [(r123.frame_var _ (by decide)).trans hσ.outward]; split_ifs <;> omega⟩
  refine ⟨τ,r1.seq (r2.seq (r3.seq r4)),?_,?_⟩
  · simpa only [words,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,Entry.words,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,ws] using p4.1
  · simp only [List.length_append,List.length_singleton,ws,length_words] at p4
    omega

end Lax455465Proofs.RamRegionRecord

end

section

namespace Lax455465Proofs.RamSmallRegion
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionRecord RamRegionContext
open scoped NNRat

def ball {n:ℕ} (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):Finset (Fin n):=
  RegionCharging.ball (fun v => (distance v:ℚ)) radius

theorem mask_eq {n:ℕ} (distance:Fin n→ ℚ≥0) (radius:ℚ≥0):
    BallMassData.mask distance radius=MaskedMassData.flags (ResidualData.mask (ball distance radius)):=by
  rw [BallMassData.mask_eq]
  congr 1
  funext v
  simp [ResidualData.mask,ball,RegionCharging.ball]

end Lax455465Proofs.RamSmallRegion

end

section

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionRuntimeCorrespondence
open Lax455465.RationalEncoding RegionRuntimeState RamRegionRecord RegionLoop

theorem coe_total {n:ℕ} (I:RationalInstance n):
    (RamRoundingInit.total I.weight:ℚ)=LargeBallRounding.total I:=by
  simp [RamRoundingInit.total,LargeBallRounding.total,List.sum_ofFn,NNRat.cast_sum]

end Lax455465Proofs.RegionRuntimeCorrespondence

end

section

namespace Lax455465Proofs.CutScoreData
open Lax455465.RationalEncoding MetricMatrix
open scoped BigOperators NNRat

theorem coe_mass {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(mass I S:ℚ)=CutSweeps.massQ I S:=by
  unfold mass vertexFlags
  rw [MaskedMassData.coe_sum]
  simp only [ResidualData.mask,decide_eq_true_eq,CutSweeps.massQ,←Finset.sum_filter]
  simp

theorem mass_add_complement {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    mass I S+mass I Sᶜ=RamRoundingInit.total I.weight:=by
  apply NNRat.coe_injective
  rw [NNRat.coe_add,coe_mass,coe_mass,RegionRuntimeCorrespondence.coe_total]
  unfold CutSweeps.massQ LargeBallRounding.total
  exact Finset.sum_add_sum_compl S _

theorem otherMass_eq {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):otherMass I S=mass I Sᶜ:=by
  rw [otherMass,←mass_add_complement I S,add_tsub_cancel_left]

theorem arc_condition {n:ℕ} (S:Finset (Fin n)) (u v:Fin n):(arcFlags S u v).num=1↔ u∈S∧ v∉S:=by
  by_cases hu:u∈S <;> by_cases hv:v∈S <;>
    simp [arcFlags,RamArcMask.matrix,RamBooleanArithmetic.bit,RamBooleanArithmetic.flag,ResidualData.mask,hu,hv]

theorem coe_capacity {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(capacity I S:ℚ)=CutSweeps.capacityQ I S:=by
  unfold capacity
  rw [BoundaryData.masked_matrix]
  simp only [values,List.sum_ofFn]
  rw [←Equiv.sum_comp (DirectedFlowLP.edgeIndex n)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,NNRat.cast_sum]
  have hsum (T:Finset (Fin n)) (g:Fin n→ ℚ):(∑ v∈T,g v)=∑ v,if v∈T then g v else 0:=by
    have ht:Finset.univ.filter (fun v => v∈T)=T:=by ext v; simp
    have h:=Finset.sum_filter (s:=Finset.univ) (p:=fun v => v∈T) (f:=g)
    rwa [ht] at h
  rw [CutSweeps.capacityQ,hsum S]
  simp_rw [hsum Sᶜ]
  simp only [Finset.mem_compl]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hus:u∈S
  · simp only [hus,if_true]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvs:v∈S <;> simp [arc_condition,hus,hvs]
  · simp [arc_condition,hus]

theorem coe_demand {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    (demand I S:ℚ)=CutSweeps.massQ I S*CutSweeps.massQ I Sᶜ:=by
  rw [demand,NNRat.coe_mul,otherMass_eq,coe_mass,coe_mass]

theorem coe_ratio {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):(ratio I S:ℚ)=CutSweeps.ratioQ I S:=by
  rw [ratio,NNRat.coe_div,coe_capacity,coe_demand]
  rfl

theorem admissible_iff {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)):
    CutSweeps.admissibleQ I S↔ 0<(demand I S).num:=by
  rw [CutSweeps.admissibleQ_iff_product_pos,←coe_demand]
  exact ⟨fun h => NNRat.num_pos.mpr (by exact_mod_cast h),fun h => by exact_mod_cast NNRat.num_pos.mp h⟩

end Lax455465Proofs.CutScoreData

end

section

namespace Lax455465Proofs.BestCutIndex
open scoped NNRat

def next (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ):Option ℕ→ Option ℕ
  | none => if valid i then some i else none
  | some j => if valid i∧ value i< value j then some i else some j

def best (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0):ℕ→ Option ℕ
  | 0 => none
  | i+1 => next valid value i (best valid value i)

theorem best_none (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ):
    best valid value i=none↔ ∀ j < i, ¬valid j:=by
  induction i with
  | zero => simp [best]
  | succ i ih =>
    cases hb:best valid value i with
    | none =>
      have hn:=ih.mp hb
      simp only [best,hb,next]
      by_cases hv:valid i
      · simp only [if_pos hv,Option.some_ne_none,false_iff]
        intro h
        exact h i (by omega) hv
      · simp only [if_neg hv,true_iff]
        intro j hj
        by_cases he:j=i
        · simpa only [he] using hv
        · exact hn j (by omega)
    | some j =>
      have hex:∃ k < i,valid k:=by
        by_contra hn
        have hall:∀ k < i, ¬valid k:=by
          intro k hk hv
          exact hn ⟨k,hk,hv⟩
        have hnone:=ih.mpr hall
        rw [hb] at hnone
        cases hnone
      simp only [best,hb,next]
      constructor
      · split_ifs <;> intro h <;> cases h
      · intro h
        obtain ⟨k,hk,hv⟩:=hex
        exact False.elim (h k (by omega) hv)

theorem best_sound (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i j:ℕ)
    (h:best valid value i=some j):j < i∧ valid j:=by
  induction i generalizing j with
  | zero => simp [best] at h
  | succ i ih =>
    simp only [best] at h
    cases hb:best valid value i with
    | none =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he:i=j:=Option.some.inj h
        subst j
        exact ⟨by omega,hv⟩
    | some k =>
      simp only [hb,next] at h
      split_ifs at h with hv
      · have he:i=j:=Option.some.inj h
        subst j
        exact ⟨by omega,hv.1⟩
      · have he:k=j:=Option.some.inj h
        subst j
        have hs:=ih k hb
        exact ⟨by omega,hs.2⟩

theorem best_minimal (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i j k:ℕ)
    (h:best valid value i=some j) (hk:k < i) (hvalid:valid k):value j≤ value k:=by
  induction i generalizing j with
  | zero => omega
  | succ i ih =>
    simp only [best] at h
    cases hb:best valid value i with
    | none =>
      have hn:=(best_none valid value i).mp hb
      have he:k=i:=by
        by_contra he
        exact hn k (by omega) hvalid
      subst k
      simp only [hb,next,if_pos hvalid,Option.some.injEq] at h
      subst j
      exact le_rfl
    | some old =>
      simp only [hb,next] at h
      by_cases hv:valid i∧ value i< value old
      · rw [if_pos hv] at h
        have he:i=j:=Option.some.inj h
        subst j
        by_cases he:k=i
        · subst k; exact le_rfl
        · exact hv.2.le.trans (ih old hb (by omega))
      · rw [if_neg hv] at h
        have he:old=j:=Option.some.inj h
        subst j
        by_cases he:k=i
        · subst k
          exact le_of_not_gt (fun hlt => hv ⟨hvalid,hlt⟩)
        · exact ih old hb (by omega)

end Lax455465Proofs.BestCutIndex

end

section

namespace Lax455465Proofs.RamBestUpdate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open scoped NNRat

def Matches (value:ℕ→ ℚ≥0):Option ℕ→ Env→ Prop
  | none,σ => σ.vars "best.found"=0
  | some j,σ => σ.vars "best.found"=1∧ σ.vars "best.index"=j∧ Stored "best.value" (value j) σ

def Current (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (i:ℕ) (σ:Env):Prop:=
  σ.vars "cut.candidate"=i∧ σ.vars "cut.valid"=(if valid i then 1 else 0)∧ Stored "cut.ratio" (value i) σ

theorem update_spec (B:ℕ) (i:ℕ) (q:ℚ≥0) (hi:i< B) (hn:q.num< B) (hd:q.den< B) (h1:1< B):
    Spec B (fun σ => σ.vars "cut.candidate"=i∧ Stored "cut.ratio" q σ) update
      (fun _ τ => τ.vars "best.found"=1∧ τ.vars "best.index"=i∧ Stored "best.value" q τ) 8:=by
  rintro σ ⟨hidx,hq⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "best.found") ((1:Nat))) (And (@Eq Nat (Env.vars τ "best.index") i) (Stored "best.value" q τ))) σ; let c1:Nat:=Env.vars (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "cut.ratio.n"; let c2:Env:=Env.setVar (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "best.value.n" c1; let c3:Nat:=Env.vars c2 "cut.ratio.d"; let c4:Env:=Env.setVar c2 "best.value.d" c3; let c5:Env:=Env.setVar c4 "best.found" ((1:Nat)); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.var "cut.candidate")); let c9:Nat:=c7 (Expr.size (Expr.var "cut.ratio.n")); let c10:Nat:=c7 (Expr.size (Expr.var "cut.ratio.d")); let c11:Nat:=c7 (Expr.size (Expr.lit ((1:Nat)))); let c12:Nat:=c6 c10 c11; let c13:Nat:=c6 c9 c12; let c14:Com:=Com.assign "best.found" (Expr.lit ((1:Nat))); let c15:Com:=Com.seq (Com.assign "best.value.d" (Expr.var "cut.ratio.d")) c14; let c16:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B update σ σ' ((8:Nat))) (c0 σ')) c5 (@And.intro (Run B update σ c5 ((8:Nat))) (c0 c5) (RunStep.mono B update σ c5 (c6 c8 c13) ((8:Nat)) (RunStep.seq B (Com.assign "best.index" (Expr.var "cut.candidate")) (Com.seq (Com.assign "best.value.n" (Expr.var "cut.ratio.n")) c15) σ (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) c5 c8 c13 (RunStep.assign B σ "best.index" (Expr.var "cut.candidate") (Env.vars σ "cut.candidate") (RunStep.eval_var B σ "cut.candidate" (?nAX_g7010_0_0_0))) (RunStep.seq B (Com.assign "best.value.n" (Expr.var "cut.ratio.n")) c15 (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) c2 c5 c9 c12 (RunStep.assign B (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "best.value.n" (Expr.var "cut.ratio.n") c1 (RunStep.eval_var B (Env.setVar σ "best.index" (Env.vars σ "cut.candidate")) "cut.ratio.n" ?_)) (RunStep.seq B (Com.assign "best.value.d" (Expr.var "cut.ratio.d")) c14 c2 c4 c5 c10 c11 (RunStep.assign B c2 "best.value.d" (Expr.var "cut.ratio.d") c3 (RunStep.eval_var B c2 "cut.ratio.d" ?_)) (RunStep.assign B c4 "best.found" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c4 h1))))) (?nAX_g7010_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7010_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7010_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Stored]

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0)
    (i:ℕ) (old:Option ℕ) (hB:2*M^2+3< B) (hi:i< B)
    (hcur:LpInputSize.Height M (value i:ℚ))
    (hold:∀ j,old=some j→ LpInputSize.Height M (value j:ℚ)):
    Spec B (fun σ => Current valid value i σ∧ Matches value old σ) command
      (fun _ τ => Current valid value i τ∧ Matches value (BestCutIndex.next valid value i old) τ) 84:=by
  have hMB:M< B:=by nlinarith
  have h1:1< B:=by nlinarith
  have currentFrame {cmd:Com} {σ τ:Env} {K:ℕ} (rr:Run B cmd σ τ K) (h:Current valid value i σ)
      (hx:∀ x∈["cut.candidate","cut.valid","cut.ratio.n","cut.ratio.d"],x∉cmd.wvars):Current valid value i τ:=by
    exact ⟨(rr.frame_var _ (hx _ (by simp))).trans h.1,(rr.frame_var _ (hx _ (by simp))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp)) (hx _ (by simp))⟩
  rintro σ ⟨hσ,holdσ⟩
  by_cases hv:valid i
  · have hvalid:σ.vars "cut.valid"=1:=by simpa only [if_pos hv] using hσ.2.1
    have hc:(Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hvalid ▸ h1)) (evalB_lit h1),hvalid]
      rfl
    cases old with
    | none =>
      have hf:σ.vars "best.found"=0:=holdσ
      have hfound:(Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some true:=by
        rw [evalB_condEq (evalB_var (hf ▸ (by omega:0< B))) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨τ,ru,pu⟩:=update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 σ ⟨hσ.1,hσ.2.2⟩
      have rr:=Run.ite_true (d:=.skip) hc (Run.ite_true (d:=compare) hfound ru)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
        by simpa only [BestCutIndex.next,if_pos hv,Matches] using pu⟩
    | some j =>
      have hj:LpInputSize.Height M (value j:ℚ):=hold j rfl
      have hf:σ.vars "best.found"=1:=holdσ.1
      have hfound:(Cond.eq (.var "best.found") (.lit 0)).evalB B σ=some false:=by
        rw [evalB_condEq (evalB_var (hf ▸ h1)) (evalB_lit (by omega)),hf]
        rfl
      obtain ⟨ν,rc,pc⟩:=RamScalarComparison.command_spec B M (value j) (value i) "best.value" "cut.ratio" hB
        (num_bound hj) (den_bound hj) (num_bound hcur) (den_bound hcur) (by decide) (by decide) (by decide) σ ⟨holdσ.2.2,hσ.2.2⟩
      have hν:=currentFrame rc hσ (by decide)
      by_cases hbetter:value i< value j
      · have hcmp:ν.vars "cmp.le"=0:=by
          simpa only [NNRat.coe_le_coe,if_neg (not_le.mpr hbetter)] using pc
        have htest:(Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some true:=by
          rw [evalB_condEq (evalB_var (hcmp ▸ (by omega:0< B))) (evalB_lit (by omega)),hcmp]
          rfl
        obtain ⟨τ,ru,pu⟩:=update_spec B i (value i) hi ((num_bound hcur).trans_lt hMB) ((den_bound hcur).trans_lt hMB) h1 ν ⟨hν.1,hν.2.2⟩
        have rr:=Run.ite_true (d:=.skip) hc (Run.ite_false (c:=update) hfound
          (rc.seq (Run.ite_true (d:=.skip) htest ru)))
        exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),
          by simpa only [BestCutIndex.next,if_pos (And.intro hv hbetter),Matches] using pu⟩
      · have hcmp:ν.vars "cmp.le"=1:=by
          simpa only [NNRat.coe_le_coe,if_pos (le_of_not_gt hbetter)] using pc
        have htest:(Cond.eq (.var "cmp.le") (.lit 0)).evalB B ν=some false:=by
          rw [evalB_condEq (evalB_var (hcmp ▸ h1)) (evalB_lit (by omega)),hcmp]
          rfl
        have rr:=Run.ite_true (d:=.skip) hc (Run.ite_false (c:=update) hfound
          (rc.seq (Run.ite_false (c:=update) htest Run.skip)))
        refine ⟨ν,rr.mono (by dsimp [Cond.size,Expr.size]; omega),currentFrame rr hσ (by decide),?_⟩
        simp only [BestCutIndex.next,if_neg (show ¬(valid i∧ value i< value j) from fun h => hbetter h.2),Matches]
        exact ⟨(rc.frame_var _ (by decide)).trans holdσ.1,(rc.frame_var _ (by decide)).trans holdσ.2.1,
          RamRoundingConstants.storedFrame rc holdσ.2.2 (by decide) (by decide)⟩
  · have hvalid:σ.vars "cut.valid"=0:=by simpa only [if_neg hv] using hσ.2.1
    have hc:(Cond.eq (.var "cut.valid") (.lit 1)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hvalid ▸ (by omega:0< B))) (evalB_lit h1),hvalid]
      rfl
    refine ⟨σ,(Run.ite_false (c:=choose) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),hσ,?_⟩
    cases old <;> simpa only [BestCutIndex.next,hv,if_false,false_and] using holdσ

end Lax455465Proofs.RamBestUpdate

end

section

namespace Lax455465Proofs.RamBestFold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamBestUpdate
open scoped NNRat

def bestNames:List String:= ["best.found","best.index","best.value.n","best.value.d"]

theorem Matches.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {value:ℕ→ ℚ≥0} {old:Option ℕ} (h:Matches value old σ)
    (hx:∀ x∈bestNames,x∉cmd.wvars):Matches value old τ:=by
  cases old with
  | none => exact (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h
  | some j =>
    exact ⟨(rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.1,
      (rr.frame_var _ (hx _ (by simp [bestNames]))).trans h.2.1,
      RamRoundingConstants.storedFrame rr h.2.2 (hx _ (by simp [bestNames])) (hx _ (by simp [bestNames]))⟩

def Invariant (R:Env→ Prop) (valid:ℕ→ Prop) [DecidablePred valid] (value:ℕ→ ℚ≥0) (count:ℕ) (σ:Env):Prop:=
  R σ∧ σ.vars "cut.candidate"≤ count∧ Matches value (BestCutIndex.best valid value (σ.vars "cut.candidate")) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M K:ℕ) (R:Env→ Prop) (valid:ℕ→ Prop) [DecidablePred valid]
    (value:ℕ→ ℚ≥0) (count:ℕ) (producer:Com) (hB:2*M^2+3< B) (hcount:count< B)
    (hvalue:∀ i< count,LpInputSize.Height M (value i:ℚ))
    (hlimit:∀ σ,R σ→σ.vars "cut.count"=count)
    (hset:∀ σ k name,name∈["cut.candidate","best.found","best.index"]→ R σ→R (σ.setVar name k))
    (hproducer:∀ i< count,Spec B (fun σ => R σ∧ σ.vars "cut.candidate"=i) producer
      (fun _ τ => R τ∧ Current valid value i τ) K)
    (hproducerFrame:∀ x∈bestNames,x∉producer.wvars)
    (hupdateFrame:∀ {σ τ:Env} {k:ℕ},Run B RamBestUpdate.command σ τ k→R σ→R τ):
    Spec B R (command producer) (fun _ τ => R τ∧ Matches value (BestCutIndex.best valid value count) τ)
      ((K+92)*count+10):=by
  have h1:1< B:=by nlinarith
  have hstep:Spec B (fun σ => Invariant R valid value count σ∧ σ.vars "cut.candidate"< count)
      (step producer) (fun σ τ => Invariant R valid value count τ∧ τ.vars "cut.candidate"=σ.vars "cut.candidate"+1)
      (K+88):=by
    rintro σ ⟨⟨hR,hle,hmatch⟩,hlt⟩
    let i:=σ.vars "cut.candidate"
    obtain ⟨ν,rp,pp⟩:=hproducer i hlt σ ⟨hR,rfl⟩
    have hm:=Matches.frame rp hmatch hproducerFrame
    obtain ⟨μ,ru,pu⟩:=RamBestUpdate.command_spec B M valid value i (BestCutIndex.best valid value i) hB (hlt.trans hcount)
      (hvalue i hlt) (fun j hj => hvalue j ((BestCutIndex.best_sound valid value i j hj).1.trans hlt)) ν ⟨pp.2,hm⟩
    have hμ:μ.vars "cut.candidate"=i:=pu.1.1
    have hnext:i+1< B:=by dsimp [i]; omega
    let τ:=μ.setVar "cut.candidate" (i+1)
    have ri:Run B (.assign "cut.candidate" (.add (.var "cut.candidate") (.lit 1))) μ τ 4:=
      Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega:i< B)⟩)
        (evalB_lit h1) hnext)
    have hmatchτ:=Matches.frame ri pu.2 (by dsimp [bestNames,Com.wvars]; decide)
    refine ⟨τ,rp.seq (ru.seq ri),?_,by simp [τ,i]⟩
    refine ⟨hset μ (i+1) "cut.candidate" (by simp) (hupdateFrame ru pp.1),by simp [τ]; dsimp [i]; omega,?_⟩
    simpa only [τ,vars_setVar,if_true,BestCutIndex.best] using hmatchτ
  have hs:=Spec.forRangeZero "cut.candidate" "cut.count" (Invariant R valid value count) count (K+88)
    hcount (fun _ h => h.2.1) (fun σ h => hlimit σ h.1) hstep
  rintro σ hσ
  let ν:=σ.setVar "best.found" 0
  let μ:=ν.setVar "best.index" 0
  have rf:Run B (.assign "best.found" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have rix:Run B (.assign "best.index" (.lit 0)) ν μ 2:=Run.assign (evalB_lit (by omega))
  have hRμ:=hset ν 0 "best.index" (by simp) (hset σ 0 "best.found" (by simp) hσ)
  have hinit:Invariant R valid value count (μ.setVar "cut.candidate" 0):=by
    refine ⟨hset μ 0 "cut.candidate" (by simp) hRμ,by simp,?_⟩
    simp [BestCutIndex.best,Matches,μ,ν,vars_setVar]
  obtain ⟨τ,rr,pr⟩:=hs μ hinit
  exact ⟨τ,(rf.seq (rix.seq rr)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),pr.1.1,by simpa only [pr.2] using pr.1.2.2⟩

end Lax455465Proofs.RamBestFold

end

section

namespace Lax455465Proofs.RamMaskedMinimum
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open scoped NNRat

def valid (mask:List ℚ≥0) (i:ℕ):Prop:=(mask.getD i 0).num=1
instance (mask:List ℚ≥0):DecidablePred (valid mask):=fun i => inferInstanceAs (Decidable ((_:ℕ)=1))
def value (qs:List ℚ≥0) (i:ℕ):ℚ≥0:=qs.getD i 0
def minimum (qs mask:List ℚ≥0):ℚ≥0:=
  match BestCutIndex.best (valid mask) (value qs) qs.length with
  | none => 0
  | some j => value qs j

def Context (source mask:String) (qs ms:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "cut.count"=qs.length∧ Prefix (RamUnsignedBuffer.encode qs) source σ∧
    Prefix (RamUnsignedBuffer.encode ms) mask σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {source mask:String} {qs ms:List ℚ≥0} (h:Context source mask qs ms σ)
    (hx:"cut.count"∉cmd.wvars) (hs:source∉cmd.warrs) (hm:mask∉cmd.warrs):Context source mask qs ms τ:=by
  simpa only [Context,Prefix,rr.frame_var "cut.count" hx,rr.frame_arr source hs,rr.frame_arr mask hm] using h

theorem entry_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0) (i:ℕ)
    (hi:i< qs.length) (hlen:ms.length=qs.length) (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*i+1< B)
    (hq:LpInputSize.Height M (qs[i]:ℚ)) (hmn:(ms[i]'(by omega)).num≤1) (hmd:(ms[i]'(by omega)).den≤1):
    Spec B (fun σ => Context source mask qs ms σ∧ σ.vars "cut.candidate"=i) (entry source mask)
      (fun _ τ => Context source mask qs ms τ∧ RamBestUpdate.Current (valid ms) (value qs) i τ) 34:=by
  have hMB:M< B:=by nlinarith
  have h1:1< B:=by nlinarith
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨ν,rq,pq⟩:=RamArrayScalar.command_spec B source "cut.candidate" "cut.ratio" qs i hi
    (by nlinarith) hindex ((num_bound hq).trans_lt hMB) ((den_bound hq).trans_lt hMB) (by decide) (by decide) σ ⟨hσ.2.1,hidx⟩
  have hν:=frame rq hσ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
  have hiν:ν.vars "cut.candidate"=i:=(rq.frame_var _ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])).trans hidx
  obtain ⟨μ,rm,pm⟩:=RamUnsignedBuffer.read_spec B mask "cut.candidate" ms i (by omega)
    (by nlinarith) hindex (hmn.trans_lt h1) (hmd.trans_lt h1) (by decide) ν ⟨hν.2.2,hiν⟩
  have hm:μ.vars "rat.n"=ms[i].num:=by simpa only [NNRat.natAbs_num_coe] using pm.1.2.1
  let τ:=μ.setVar "cut.valid" ms[i].num
  have ra:Run B (.assign "cut.valid" (.var "rat.n")) μ τ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ hmn.trans_lt h1⟩)
  have rr:=rq.seq (rm.seq ra)
  refine ⟨τ,rr,frame rr hσ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs])
    (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.warrs]),
    (rr.frame_var _ (by simp [RamArrayScalar.command,RamUnsignedBuffer.read,save,Com.wvars])).trans hidx,?_,?_⟩
  · simp only [τ,vars_setVar,if_true,valid,List.getD_eq_get ms 0 ⟨i,by omega⟩]
    change ms[i].num=(if ms[i].num=1 then 1 else 0)
    split_ifs <;> omega
  · have hp:=RamRoundingConstants.storedFrame (rm.seq ra) pq
      (by simp [RamUnsignedBuffer.read,Com.wvars]) (by simp [RamUnsignedBuffer.read,Com.wvars])
    simpa only [value,List.getD_eq_get qs 0 ⟨i,hi⟩,List.get_eq_getElem] using hp

theorem command_spec (B M:ℕ) (source mask:String) (qs ms:List ℚ≥0)
    (hlen:ms.length=qs.length) (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*qs.length+2< B)
    (hq:∀ i,∀ hi:i< qs.length,LpInputSize.Height M (qs[i]:ℚ))
    (hmn:∀ q∈ms,q.num≤1) (hmd:∀ q∈ms,q.den≤1)
    (hex:∃ i< qs.length,valid ms i):
    Spec B (Context source mask qs ms) (command source mask)
      (fun _ τ => Context source mask qs ms τ∧ RamRational.FractionOutput (minimum qs ms:ℚ) τ)
      (126*qs.length+16):=by
  have hvalue (i:ℕ) (hi:i< qs.length):LpInputSize.Height M (value qs i:ℚ):=by
    simpa only [value,List.getD_eq_get qs 0 ⟨i,hi⟩,List.get_eq_getElem] using hq i hi
  have hscan:=RamBestFold.command_spec B M 34 (Context source mask qs ms) (valid ms) (value qs) qs.length
    (entry source mask) hB (by omega) hvalue (fun _ h => h.1)
    (fun σ k name hn h => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => entry_spec B M source mask qs ms i hi hlen hM hB (by omega) (hq i hi)
      (hmn _ (List.getElem_mem (by omega))) (hmd _ (List.getElem_mem (by omega))))
    (by dsimp [RamBestFold.bestNames,entry,RamArrayScalar.command,RamUnsignedBuffer.read,Com.wvars,save]; decide)
    (fun rr h => frame rr h (by decide) (by simp [RamBestUpdate.command,RamBestUpdate.choose,RamBestUpdate.compare,
      RamBestUpdate.update,RamScalarComparison.command,RamScalarBinary.command,RamComparison.compareFraction,Com.warrs,load,RamUnsignedArithmetic.copy])
      (by simp [RamBestUpdate.command,RamBestUpdate.choose,RamBestUpdate.compare,
      RamBestUpdate.update,RamScalarComparison.command,RamScalarBinary.command,RamComparison.compareFraction,Com.warrs,load,RamUnsignedArithmetic.copy]))
  have hexBest:∃ j,BestCutIndex.best (valid ms) (value qs) qs.length=some j:=by
    cases he:BestCutIndex.best (valid ms) (value qs) qs.length with
    | none => obtain ⟨i,hi,hv⟩:=hex; exact False.elim ((BestCutIndex.best_none _ _ _).mp he i hi hv)
    | some j => exact ⟨j,rfl⟩
  obtain ⟨j,hj⟩:=hexBest
  have hjlt:=(BestCutIndex.best_sound _ _ _ j hj).1
  have hheight:=hvalue j hjlt
  have hMB:M< B:=by nlinarith
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩:=hscan σ hσ
  have hm:RamBestUpdate.Matches (value qs) (some j) ν:=by simpa only [hj] using ps.2
  obtain ⟨τ,rl,pl⟩:=load_spec B "best.value" (value qs j) (by nlinarith)
    ((num_bound hheight).trans_lt hMB) ((den_bound hheight).trans_lt hMB) (by decide) ν hm.2.2
  exact ⟨τ,(rs.seq rl).mono (by omega),frame rl ps.1 (by decide) (by simp [load,Com.warrs]) (by simp [load,Com.warrs]),
    by simpa only [minimum,hj] using pl⟩

end Lax455465Proofs.RamMaskedMinimum

end

section

namespace Lax455465Proofs.SetDistanceData
open scoped NNRat

theorem valid_flags {n:ℕ} (S:Finset (Fin n)) (i:ℕ) (hi:i< n):
    RamMaskedMinimum.valid (CutScoreData.vertexFlags S) i↔ (⟨i,hi⟩:Fin n)∈S:=by
  by_cases hv:(⟨i,hi⟩:Fin n)∈S <;>
    simp [RamMaskedMinimum.valid,CutScoreData.vertexFlags,MaskedMassData.flags,ResidualData.mask,hi,hv]

theorem mask_nonempty {n:ℕ} (S:Finset (Fin n)) (hS:S.Nonempty):
    ∃ i< n,RamMaskedMinimum.valid (CutScoreData.vertexFlags S) i:=by
  obtain ⟨v,hv⟩:=hS
  exact ⟨v.val,v.isLt,(valid_flags S v.val v.isLt).mpr hv⟩

theorem minimum_eq_inf {n:ℕ} (f:Fin n→ ℚ≥0) (S:Finset (Fin n)) (hS:S.Nonempty):
    RamMaskedMinimum.minimum (List.ofFn f) (CutScoreData.vertexFlags S)=S.inf' hS f:=by
  let valid:=RamMaskedMinimum.valid (CutScoreData.vertexFlags S)
  let value:=RamMaskedMinimum.value (List.ofFn f)
  have hvalue (v:Fin n):value v.val=f v:=by
    simp [value,RamMaskedMinimum.value]
  cases he:BestCutIndex.best valid value n with
  | none =>
    obtain ⟨i,hi,hv⟩:=mask_nonempty S hS
    exact False.elim ((BestCutIndex.best_none valid value n).mp he i hi hv)
  | some j =>
    have hs:=BestCutIndex.best_sound valid value n j he
    have hjS:(⟨j,hs.1⟩:Fin n)∈S:=(valid_flags S j hs.1).mp hs.2
    simp only [RamMaskedMinimum.minimum,List.length_ofFn,show
      BestCutIndex.best (RamMaskedMinimum.valid (CutScoreData.vertexFlags S))
        (RamMaskedMinimum.value (List.ofFn f)) n=some j from he]
    change value j=S.inf' hS f
    apply le_antisymm
    · apply Finset.le_inf'
      intro v hv
      have h:=BestCutIndex.best_minimal valid value n j v.val he v.isLt ((valid_flags S v.val v.isLt).mpr hv)
      rwa [hvalue v] at h
    · rw [hvalue ⟨j,hs.1⟩]
      exact Finset.inf'_le f hjS

theorem minimum_vector {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n) (S:Finset (Fin n))
    (hS:S.Nonempty) (v:Fin n):
    RamMaskedMinimum.minimum (RamRootDistances.vector toSet v d) (CutScoreData.vertexFlags S)=distance toSet d S hS v:=
  minimum_eq_inf _ S hS

theorem coe_distance {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n) (S:Finset (Fin n))
    (hS:S.Nonempty) (v:Fin n):(distance toSet d S hS v:ℚ)=
      if toSet then SetDistances.toSet (MetricMatrix.rational d) S hS v
      else SetDistances.fromSet (MetricMatrix.rational d) S hS v:=by
  let f:Fin n→ ℚ≥0:=fun u => if toSet then d v u else d u v
  have hcoe:((S.inf' hS f:ℚ≥0):ℚ)=S.inf' hS (fun u => (f u:ℚ)):=by
    obtain ⟨j,hj,hmin⟩:=Finset.exists_mem_eq_inf' hS f
    rw [hmin]
    apply le_antisymm
    · apply Finset.le_inf'
      intro u hu
      exact NNRat.coe_le_coe.mpr (hmin ▸ Finset.inf'_le f hu)
    · exact Finset.inf'_le _ hj
  cases toSet <;> exact hcoe

theorem height {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n) (S:Finset (Fin n))
    (hS:S.Nonempty) (M:ℕ) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)) (v:Fin n):
    LpInputSize.Height M (distance toSet d S hS v:ℚ):=by
  obtain ⟨j,hj,hmin⟩:=Finset.exists_mem_eq_inf' hS (fun u => if toSet then d v u else d u v)
  unfold distance
  rw [hmin]
  cases toSet <;> exact hd _ _

end Lax455465Proofs.SetDistanceData

end

section

namespace Lax455465Proofs.RamThresholdMask
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRational RamBooleanArithmetic
open scoped NNRat

def chosen (reversed:Bool) (a threshold:ℚ≥0):Bool:=
  decide (if reversed then (threshold:ℚ)≤ a else (a:ℚ)≤ threshold)
def Context {n:ℕ} (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Stored "cut.threshold" threshold σ∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ

theorem emit_spec (B:ℕ) (b:Bool) (h1:1< B):
    Spec B (fun σ => σ.vars "cmp.le"=if b then 1 else 0) emit
      (fun _ τ => FractionOutput (bit b:ℚ) τ) 6:=by
  cases b <;> intro σ hσ <;> (first
                              | (expose_names;
                                  (refine
                                      let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit false)) τ) σ;
                                      let c1:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                      let c2:Nat:=Env.vars c1 "cmp.le";
                                      let c3:Env:=Env.setVar c1 "rat.n" c2;
                                      let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat));
                                      let c5:Nat→ Nat→ Nat:=Nat.add;
                                      let c6:Nat→ Nat:=c5 ((1:Nat));
                                      let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat))));
                                      let c8:Nat:=c6 (Expr.size (Expr.var "cmp.le"));
                                      let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat))));
                                      let c10:Nat:=c5 c8 c9;
                                      let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                      @Exists.intro Env
                                        (fun (σ':Env) => And (Run B emit σ σ' ((6:Nat))) (c0 σ')) c4
                                        (@And.intro (Run B emit σ c4 ((6:Nat))) (c0 c4)
                                          (RunStep.mono B emit σ c4 (c5 c7 c10) ((6:Nat))
                                            (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                              (Com.seq (Com.assign "rat.n" (Expr.var "cmp.le")) c11) σ c1 c4 c7 c10
                                              (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                ((0:Nat))
                                                (RunStep.eval_lit B ((0:Nat)) σ
                                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                              (RunStep.seq B (Com.assign "rat.n" (Expr.var "cmp.le")) c11 c1 c3 c4 c8 c9
                                                (RunStep.assign B c1 "rat.n" (Expr.var "cmp.le") c2 (RunStep.eval_var B c1 "cmp.le" ?_))
                                                (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat)))
                                                  ((1:Nat))
                                                  (RunStep.eval_lit B ((1:Nat)) c3 h1))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                              | (expose_names;
                                  (refine
                                      let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast (bit true)) τ) σ;
                                      let c1:Env:=Env.setVar σ "rat.s" ((0:Nat));
                                      let c2:Nat:=Env.vars c1 "cmp.le";
                                      let c3:Env:=Env.setVar c1 "rat.n" c2;
                                      let c4:Env:=Env.setVar c3 "rat.d" ((1:Nat));
                                      let c5:Nat→ Nat→ Nat:=Nat.add;
                                      let c6:Nat→ Nat:=c5 ((1:Nat));
                                      let c7:Nat:=c6 (Expr.size (Expr.lit ((0:Nat))));
                                      let c8:Nat:=c6 (Expr.size (Expr.var "cmp.le"));
                                      let c9:Nat:=c6 (Expr.size (Expr.lit ((1:Nat))));
                                      let c10:Nat:=c5 c8 c9;
                                      let c11:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat)));
                                      @Exists.intro Env
                                        (fun (σ':Env) => And (Run B emit σ σ' ((6:Nat))) (c0 σ')) c4
                                        (@And.intro (Run B emit σ c4 ((6:Nat))) (c0 c4)
                                          (RunStep.mono B emit σ c4 (c5 c7 c10) ((6:Nat))
                                            (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat))))
                                              (Com.seq (Com.assign "rat.n" (Expr.var "cmp.le")) c11) σ c1 c4 c7 c10
                                              (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat)))
                                                ((0:Nat))
                                                (RunStep.eval_lit B ((0:Nat)) σ
                                                  ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega)))))
                                              (RunStep.seq B (Com.assign "rat.n" (Expr.var "cmp.le")) c11 c1 c3 c4 c8 c9
                                                (RunStep.assign B c1 "rat.n" (Expr.var "cmp.le") c2 (RunStep.eval_var B c1 "cmp.le" ?_))
                                                (RunStep.assign B c3 "rat.d" (Expr.lit ((1:Nat)))
                                                  ((1:Nat))
                                                  (RunStep.eval_lit B ((1:Nat)) c3 h1))))
                                            ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                          ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                             )
  all_goals simp_all [FractionOutput,fractionValue,bit] <;> omega

theorem compare_spec (B M:ℕ) (reversed:Bool) (a threshold:ℚ≥0) (hB:2*M^2+3< B)
    (han:a.num≤ M) (had:a.den≤ M) (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Stored "cut.value" a σ∧ Stored "cut.threshold" threshold σ) (compare reversed)
      (fun _ τ => τ.vars "cmp.le"=if chosen reversed a threshold then 1 else 0) 64:=by
  cases reversed
  · simpa only [compare,Bool.false_eq_true,if_false,chosen,decide_eq_true_eq] using
      RamScalarComparison.command_spec B M a threshold "cut.value" "cut.threshold" hB han had htn htd (by decide) (by decide) (by decide)
  · intro σ hσ
    obtain ⟨τ,rr,pr⟩:=RamScalarComparison.command_spec B M threshold a "cut.threshold" "cut.value" hB htn htd han had
      (by decide) (by decide) (by decide) σ ⟨hσ.2,hσ.1⟩
    exact ⟨τ,rr,by simpa only [chosen,if_true,decide_eq_true_eq] using pr⟩

theorem entry_spec (B M:ℕ) {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0)
    (v:Fin n) (hB:2*M^2+3< B) (hindex:2*n+2< B)
    (hpn:∀ v, (potential v).num≤ M) (hpd:∀ v, (potential v).den≤ M)
    (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Context potential threshold σ∧ σ.vars "cut.i"=v.val) (entry reversed)
      (fun _ τ => Context potential threshold τ∧ FractionOutput (bit (chosen reversed (potential v) threshold):ℚ) τ) 88:=by
  have hMB:M< B:=by nlinarith
  rintro σ ⟨hσ,hidx⟩
  have hi:v.val<(List.ofFn potential).length:=by simpa only [List.length_ofFn] using v.isLt
  have he:(List.ofFn potential)[v.val]=potential v:=by simp
  obtain ⟨ν,rr,pr⟩:=RamArrayScalar.command_spec B "cut.potential" "cut.i" "cut.value" (List.ofFn potential) v.val hi
    (by nlinarith) (by omega) (by rw [he]; exact (hpn v).trans_lt hMB) (by rw [he]; exact (hpd v).trans_lt hMB)
    (by decide) (by decide) σ ⟨hσ.2.2,hidx⟩
  obtain ⟨μ,rc,pc⟩:=compare_spec B M reversed (potential v) threshold hB (hpn v) (hpd v) htn htd ν
    ⟨by simpa only [he] using pr,
      RamRoundingConstants.storedFrame rr hσ.2.1 (by decide) (by decide)⟩
  obtain ⟨τ,re,pe⟩:=emit_spec B (chosen reversed (potential v) threshold) (by nlinarith) μ pc
  have run:=rr.seq (rc.seq re)
  refine ⟨τ,run,?_,pe⟩
  exact ⟨(run.frame_var _ (by cases reversed <;> decide)).trans hσ.1,
    RamRoundingConstants.storedFrame run hσ.2.1 (by cases reversed <;> decide) (by cases reversed <;> decide),
    by simpa only [Prefix,run.frame_arr "cut.potential" (by cases reversed <;> decide)] using hσ.2.2⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0) (threshold:ℚ≥0)
    (hB:2*M^2+3< B) (hindex:2*n+2< B)
    (hpn:∀ v, (potential v).num≤ M) (hpd:∀ v, (potential v).den≤ M)
    (htn:threshold.num≤ M) (htd:threshold.den≤ M):
    Spec B (fun σ => Context potential threshold σ∧ 2*n<(σ.arrs "cut.flags").length) (command reversed)
      (fun _ τ => Context potential threshold τ∧ Prefix (RamUnsignedBuffer.encode
        (MaskedMassData.flags (fun v => chosen reversed (potential v) threshold))) "cut.flags" τ) (110*n+8):=by
  let qs:=MaskedMassData.flags (fun v => chosen reversed (potential v) threshold)
  have hlen:qs.length=n:=List.length_ofFn
  have hv:∀ i, ∀ hi:i< qs.length,qs[i]=bit (chosen reversed (potential ⟨i,by simpa only [hlen] using hi⟩) threshold):=by
    intro i hi; simp [qs,MaskedMassData.flags,bit]
  have hwords:∀ i, ∀ hi:i< qs.length,qs[i].num< B∧ qs[i].den< B:=by
    intro i hi; rw [hv i hi]
    cases chosen reversed (potential _) threshold <;> simp [bit] <;> omega
  have body:∀ i, ∀ hi:i< qs.length,
      Spec B (fun σ => Context potential threshold σ∧ σ.vars "cut.i"=i) (entry reversed)
        (fun _ τ => Context potential threshold τ∧ FractionOutput (qs[i]:ℚ) τ) 88:=by
    intro i hi
    simpa only [hv i hi] using entry_spec B M reversed potential threshold ⟨i,by simpa only [hlen] using hi⟩ hB hindex hpn hpd htn htd
  have hf:=RamUnsignedVector.command_spec B 88 (Context potential threshold) "cut.i" "metric.n" "cut.flags" "cut.pos" qs []
    (entry reversed) (by nlinarith) (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2) (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using h)
    body (by cases reversed <;> decide) (by cases reversed <;> decide) (by cases reversed <;> decide)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Stored,Prefix,String.reduceAppend,
        rr.frame_var "metric.n" (by decide),rr.frame_var "cut.threshold.n" (by decide),rr.frame_var "cut.threshold.d" (by decide),
        rr.frame_arr "cut.potential" (by decide)] using h)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν:=σ.setVar "cut.pos" 0
  have rz:Run B (.assign "cut.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by nlinarith))
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨by simpa only [Context,Stored,Prefix,ν,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using hσ,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rz.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamThresholdMask

end

section

namespace Lax455465Proofs.ThresholdCutData
open Lax455465.RationalEncoding
open scoped NNRat

def potential {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):Fin n→ ℚ:=
  fun v => if reversed then -(values v:ℚ) else (values v:ℚ)
def shore {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (threshold:ℚ≥0):Finset (Fin n):=
  Finset.univ.filter fun v => RamThresholdMask.chosen reversed (values v) threshold

def candidates {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):List (Finset (Fin n)):=
  (List.finRange n).map fun v => shore reversed values (values v)

theorem mask_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (threshold:ℚ≥0):
    MaskedMassData.flags (fun v => RamThresholdMask.chosen reversed (values v) threshold)=
      CutScoreData.vertexFlags (shore reversed values threshold):=by
  unfold CutScoreData.vertexFlags
  congr 1
  funext v
  simp [shore,ResidualData.mask]

theorem candidates_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):
    candidates reversed values=CutSweeps.candidates (potential reversed values):=by
  apply List.map_congr_left
  intro v hv
  ext u
  cases reversed <;> simp [shore,potential,RamThresholdMask.chosen]

@[simp] theorem length_candidates {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0):
    (candidates reversed values).length=n:=by simp [candidates]

def candidate {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):Finset (Fin n):=
  (candidates reversed values).getD i ∅

theorem at_eq {n:ℕ} (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ) (hi:i< n):
    candidate reversed values i=shore reversed values (values ⟨i,hi⟩):=by
  rw [candidate,List.getD_eq_get (candidates reversed values) ∅ (⟨i,by simpa only [length_candidates] using hi⟩:Fin (candidates reversed values).length)]
  simp [candidates]

def valid {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):Prop:=
  CutSweeps.admissibleQ I (candidate reversed values i)
instance {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0):DecidablePred (valid I reversed values):=
  fun i => inferInstanceAs (Decidable (CutSweeps.admissibleQ I (candidate reversed values i)))
def score {n:ℕ} (I:RationalInstance n) (reversed:Bool) (values:Fin n→ ℚ≥0) (i:ℕ):ℚ≥0:=
  CutScoreData.ratio I (candidate reversed values i)

end Lax455465Proofs.ThresholdCutData

end

section

namespace Lax455465Proofs.LargePotentialData
open Lax455465.RationalEncoding LpInputSize
open scoped NNRat

def average {n:ℕ} (I:RationalInstance n) (toSet:Bool) (d:MetricMatrix.Matrix n)
    (S:Finset (Fin n)) (hS:S.Nonempty):ℚ≥0:=(products I toSet d S hS).sum

theorem coe_average {n:ℕ} (I:RationalInstance n) (toSet:Bool) (d:MetricMatrix.Matrix n)
    (S:Finset (Fin n)) (hS:S.Nonempty):(average I toSet d S hS:ℚ)=
      if toSet then LargeBallRounding.toAverage I (MetricMatrix.rational d) S hS
      else LargeBallRounding.fromAverage I (MetricMatrix.rational d) S hS:=by
  have he:products I toSet d S hS=List.ofFn (fun v => I.weight v*SetDistanceData.distance toSet d S hS v):=by
    apply List.ext_getElem
    · simp [products,RamProductSum.products]
    · intro i hi hj
      change (RamProductSum.products (List.ofFn I.weight) (vector toSet d S hS))[i]=_
      erw [RamProductSum.value_at (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) i (by simpa using hj)]
      simp only [vector,List.getElem_ofFn]
  simp only [average,he,List.sum_ofFn,NNRat.cast_sum,NNRat.coe_mul,SetDistanceData.coe_distance]
  cases toSet <;> rfl

def reversed {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty):Bool:=
  if average I true d Tin hin≤ average I false d Tout hout then false else true
def values {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty):Fin n→ ℚ≥0:=
  if reversed I d Tin Tout hin hout then SetDistanceData.distance true d Tin hin
    else SetDistanceData.distance false d Tout hout

theorem potential_eq {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty):
    ThresholdCutData.potential (reversed I d Tin Tout hin hout) (values I d Tin Tout hin hout)=
      LargeBallRounding.potential I (MetricMatrix.rational d) Tin Tout hin hout:=by
  have hc:average I true d Tin hin≤ average I false d Tout hout↔
      LargeBallRounding.toAverage I (MetricMatrix.rational d) Tin hin≤
        LargeBallRounding.fromAverage I (MetricMatrix.rational d) Tout hout:=by
    rw [←NNRat.coe_le_coe,coe_average,coe_average]
    rfl
  funext v
  by_cases h:average I true d Tin hin≤ average I false d Tout hout
  · simp [ThresholdCutData.potential,values,reversed,h,LargeBallRounding.potential,hc.mp h,SetDistanceData.coe_distance]
  · simp [ThresholdCutData.potential,values,reversed,h,LargeBallRounding.potential,not_congr hc |>.mp h,SetDistanceData.coe_distance]

end Lax455465Proofs.LargePotentialData

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamSetDistances
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat

def Context {n:ℕ} (d:MetricMatrix.Matrix n) (S:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "cut.count"=n∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "potential.set" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {d:MetricMatrix.Matrix n} {S:Finset (Fin n)} (h:Context d S σ)
    (hx:∀ x∈["metric.n","cut.count"],x∉cmd.wvars)
    (ha:∀ a∈["metric.old","potential.set"],a∉cmd.warrs):Context d S τ:=by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "cut.count" (hx _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp)),rr.frame_arr "potential.set" (ha _ (by simp))] using h

theorem entry_spec (B M:ℕ) {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n)
    (S:Finset (Fin n)) (hS:S.Nonempty) (v:Fin n) (hM:1≤ M) (hB:2*M^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)):
    Spec B (fun σ => Context d S σ∧ σ.vars "region.root"=v.val∧
        2*n<(σ.arrs (RamRootDistances.array toSet)).length) (entry toSet)
      (fun _ τ => Context d S τ∧ RamRational.FractionOutput (SetDistanceData.distance toSet d S hS v:ℚ) τ)
      (168*n+24):=by
  have hMB:M< B:=by nlinarith
  rintro σ ⟨hσ,hroot,hroom⟩
  obtain ⟨ν,rr,pr⟩:=RamRootDistances.command_spec B M toSet v d hMB (by omega) (by omega) hindex
    (fun u v => num_bound (hd u v)) (fun u v => den_bound (hd u v)) σ
      ⟨⟨hσ.1,hroot,hσ.2.2.1⟩,hroom⟩
  have hν:=frame rr hσ (by cases toSet <;> decide) (by cases toSet <;> decide)
  have hqs:∀ i,∀ hi:i<(RamRootDistances.vector toSet v d).length,
      LpInputSize.Height M ((RamRootDistances.vector toSet v d)[i]:ℚ):=by
    intro i hi
    have hi':i< n:=by simpa only [RamRootDistances.length_vector] using hi
    simp only [RamRootDistances.vector,List.getElem_ofFn]
    cases toSet <;> exact hd _ _
  have hflags:∀ q∈CutScoreData.vertexFlags S,q.num≤1∧ q.den≤1:=by
    intro q hq
    obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hq
    change (if ResidualData.mask S u then (1:ℚ≥0) else 0).num≤1∧
      (if ResidualData.mask S u then (1:ℚ≥0) else 0).den≤1
    split_ifs <;> norm_num
  obtain ⟨τ,rm,pm⟩:=RamMaskedMinimum.command_spec B M (RamRootDistances.array toSet) "potential.set"
    (RamRootDistances.vector toSet v d) (CutScoreData.vertexFlags S)
    (by simp [CutScoreData.vertexFlags,MaskedMassData.flags]) hM hB (by simpa using hvertex) hqs
    (fun q hq => (hflags q hq).1) (fun q hq => (hflags q hq).2)
    (by simpa only [RamRootDistances.length_vector] using SetDistanceData.mask_nonempty S hS) ν
    ⟨by simpa only [RamRootDistances.length_vector] using hν.2.1,pr.2,hν.2.2.2⟩
  exact ⟨τ,(rr.seq rm).mono (by simp only [RamRootDistances.length_vector]; omega),
    frame rm hν (by cases toSet <;> decide) (by cases toSet <;> decide),
    by simpa only [SetDistanceData.minimum_vector toSet d S hS v] using pm.2⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n)
    (S:Finset (Fin n)) (hS:S.Nonempty) (hM:1≤ M) (hB:2*M^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)):
    Spec B (fun σ => Context d S σ∧ 2*n<(σ.arrs (RamRootDistances.array toSet)).length∧
        2*n<(σ.arrs "potential.values").length) (command toSet)
      (fun _ τ => Context d S τ∧ Prefix (RamUnsignedBuffer.encode
        (List.ofFn (SetDistanceData.distance toSet d S hS))) "potential.values" τ) (cost n):=by
  let qs:=List.ofFn (SetDistanceData.distance toSet d S hS)
  let R:=fun σ => Context d S σ∧ 2*n<(σ.arrs (RamRootDistances.array toSet)).length
  have hMB:M< B:=by nlinarith
  have hheight (i:ℕ) (hi:i< qs.length):LpInputSize.Height M (qs[i]:ℚ):=by
    simp only [qs,List.getElem_ofFn]
    exact SetDistanceData.height toSet d S hS M hd _
  have hloop:=RamUnsignedVector.command_spec B (168*n+24) R "region.root" "metric.n"
    "potential.values" "potential.pos" qs [] (entry toSet) (by nlinarith)
    (by simpa only [qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hvertex)
    (fun i hi => (num_bound (hheight i hi)).trans_lt hMB)
    (fun i hi => (den_bound (hheight i hi)).trans_lt hMB)
    (fun σ h => by simpa only [qs,List.length_ofFn] using h.1.1)
    (fun σ k h => by simpa only [R,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ h => by
      have hi':i< n:=by simpa only [qs,List.length_ofFn] using hi
      obtain ⟨τ,rr,pr⟩:=entry_spec B M toSet d S hS ⟨i,hi'⟩ hM hB hindex hvertex hd σ ⟨h.1.1,h.2,h.1.2⟩
      exact ⟨τ,rr,⟨pr.1,by rw [RamFrames.run_array_length rr]; exact h.1.2⟩,
        by simpa only [qs,List.getElem_ofFn] using pr.2⟩)
    (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide) (by decide)
    (fun rr h => ⟨frame rr h.1 (by decide) (by decide),by rw [RamFrames.run_array_length rr]; exact h.2⟩)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom,hout⟩
  let ν:=σ.setVar "potential.pos" 0
  have rz:Run B (.assign "potential.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hν:=frame rz hσ (by decide) (by decide)
  obtain ⟨τ,rl,pl⟩:=hloop ν ⟨⟨hν,hroom⟩,by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hout⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [qs,List.length_ofFn,cost,Nat.add_assoc,Nat.reduceAdd]; omega),pl.1.1,
    by simpa only [List.nil_append,qs] using pl.2.1⟩

end Lax455465Proofs.RamSetDistances

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamSetPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionContext
open scoped NNRat

def Context {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n) (S:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ∧
    Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) (maskArray toSet) σ
def Room (n:ℕ) (toSet:Bool) (σ:Env):Prop:=
  ∀ a∈["potential.set","potential.values",RamRootDistances.array toSet,targetArray toSet],2*n<(σ.arrs a).length

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {toSet:Bool} {d:MetricMatrix.Matrix n} {S:Finset (Fin n)} (h:Context toSet d S σ)
    (hx:"metric.n"∉cmd.wvars) (hd:"metric.old"∉cmd.warrs) (hs:maskArray toSet∉cmd.warrs):Context toSet d S τ:=by
  simpa only [Context,Prefix,rr.frame_var "metric.n" hx,rr.frame_arr "metric.old" hd,rr.frame_arr (maskArray toSet) hs] using h

theorem encoded_bound (B M:ℕ) (qs:List ℚ≥0) (hMB:M< B)
    (hq:∀ q∈qs,LpInputSize.Height M (q:ℚ)):∀ x∈RamUnsignedBuffer.encode qs,x< B:=by
  intro x hx
  simp only [RamUnsignedBuffer.encode,List.mem_flatMap] at hx
  obtain ⟨q,hq',hx⟩:=hx
  simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact (num_bound (hq q hq')).trans_lt hMB
  · exact (den_bound (hq q hq')).trans_lt hMB

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (toSet:Bool) (d:MetricMatrix.Matrix n)
    (S:Finset (Fin n)) (hS:S.Nonempty) (hM:1≤ M) (hB:2*M^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ)):
    Spec B (fun σ => Context toSet d S σ∧ Room n toSet σ) (command toSet)
      (fun _ τ => Context toSet d S τ∧ Prefix (RamUnsignedBuffer.encode
        (List.ofFn (SetDistanceData.distance toSet d S hS))) (targetArray toSet) τ) (cost n):=by
  have h1:1< B:=by nlinarith
  have hMB:M< B:=by nlinarith
  let mask:=CutScoreData.vertexFlags S
  let qs:=List.ofFn (SetDistanceData.distance toSet d S hS)
  have hmasklen:(RamUnsignedBuffer.encode mask).length=2*n:=by simp [mask,CutScoreData.vertexFlags,MaskedMassData.flags]
  have hqslen:(RamUnsignedBuffer.encode qs).length=2*n:=by simp [qs]
  have hmaskwords:∀ x∈RamUnsignedBuffer.encode mask,x< B:=by
    apply encoded_bound B 1 mask h1
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    change LpInputSize.Height 1 (((if ResidualData.mask S v then 1 else 0):ℚ≥0):ℚ)
    split_ifs <;> norm_num [LpInputSize.Height]
  have hqswords:∀ x∈RamUnsignedBuffer.encode qs,x< B:=by
    apply encoded_bound B M qs hMB
    intro q hq
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact SetDistanceData.height toSet d S hS M hd v
  rintro σ ⟨hσ,hroom⟩
  let ν:=(σ.setVar "cut.count" n).setVar "copy.count" (2*n)
  have rsetup:Run B setup σ ν 6:=by
    have r1:Run B (.assign "cut.count" (.var "metric.n")) σ (σ.setVar "cut.count" n) 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ (by omega:n< B)⟩)
    have hn:(σ.setVar "cut.count" n).vars "metric.n"=n:=by simpa using hσ.1
    have r2:Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) (σ.setVar "cut.count" n) ν 4:=
      Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega))
        (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩) (by dsimp [Bop.apply]; omega))
    exact r1.seq r2
  have hν:=frame rsetup hσ (by decide) (by decide) (by cases toSet <;> decide)
  obtain ⟨μ,rc,pc⟩:=RamArrayCopy.command_spec B (RamUnsignedBuffer.encode mask) (maskArray toSet)
    "potential.set" "copy.count" h1 (by rw [hmasklen]; omega) hmaskwords (by cases toSet <;> decide) (by decide) ν
    ⟨hν.2.2,by simp [ν,hmasklen],by rw [hmasklen]; exact (hroom _ (by simp [Room])).le⟩
  have hμ:=frame rc hν (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide)
  have hcount:μ.vars "cut.count"=n:=by rw [rc.frame_var _ (by cases toSet <;> decide)]; simp [ν]
  have rpre:=rsetup.seq rc
  obtain ⟨ξ,rd,pd⟩:=RamSetDistances.command_spec B M toSet d S hS hM hB hindex hvertex hd μ
    ⟨⟨hμ.1,hcount,hμ.2.1,pc.2⟩,
      by rw [RamFrames.run_array_length rpre]; exact hroom _ (by simp [Room]),
      by rw [RamFrames.run_array_length rpre]; exact hroom _ (by simp [Room])⟩
  have rbefore:=rpre.seq rd
  obtain ⟨τ,rs,ps⟩:=RamArrayCopy.command_spec B (RamUnsignedBuffer.encode qs) "potential.values"
    (targetArray toSet) "copy.count" h1 (by rw [hqslen]; omega) hqswords (by cases toSet <;> decide) (by decide) ξ
    ⟨pd.2,by rw [rd.frame_var _ (by cases toSet <;> decide),rc.frame_var _ (by cases toSet <;> decide)]; simp [ν,hqslen],
      by rw [hqslen,RamFrames.run_array_length rbefore]; exact (hroom _ (by simp [Room])).le⟩
  have rr:=rsetup.seq (rc.seq (rd.seq rs))
  exact ⟨τ,rr.mono (by rw [hmasklen,hqslen]; dsimp [cost]; omega),
    frame rr hσ (by cases toSet <;> decide) (by cases toSet <;> decide) (by cases toSet <;> decide),ps.2⟩

end Lax455465Proofs.RamSetPotential

end

section

namespace Lax455465Proofs.RamPotentialAverage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (toSet:Bool)
    (d:MetricMatrix.Matrix n) (S:Finset (Fin n)) (hS:S.Nonempty)
    (hB:2*M^2+3< B) (hvertex:2*n+2< B)
    (hw:∀ v,LpInputSize.Height M (I.weight v:ℚ)) (hd:∀ u v,LpInputSize.Height M (d u v:ℚ))
    (hp:∀ q∈products I toSet d S hS,LpInputSize.Height M (q:ℚ))
    (hprefix:∀ i,LpInputSize.Height M ((((products I toSet d S hS).take i).sum:ℚ≥0):ℚ)):
    Spec B (fun σ => σ.vars "metric.n"=n∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ∧
      Prefix (RamUnsignedBuffer.encode (vector toSet d S hS)) (RamSetPotential.targetArray toSet) σ)
      (command toSet) (fun _ τ => Stored (name toSet) (average I toSet d S hS) τ) (cost n M):=by
  have hMB:M< B:=by nlinarith
  have hweights:∀ q∈List.ofFn I.weight,LpInputSize.Height M (q:ℚ):=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hw v
  have hvalues:∀ q∈vector toSet d S hS,LpInputSize.Height M (q:ℚ):=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact SetDistanceData.height toSet d S hS M hd v
  have havg:LpInputSize.Height M (average I toSet d S hS:ℚ):=by
    simpa only [List.take_length,average] using hprefix (products I toSet d S hS).length
  rintro σ ⟨hn,hweightsσ,hvaluesσ⟩
  let ν:=σ.setVar "sum.count" n
  have rc:Run B (.assign "sum.count" (.var "metric.n")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩)
  obtain ⟨μ,rs,ps⟩:=RamProductSum.command_spec B M "flow.weights" (RamSetPotential.targetArray toSet)
    (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) hB (by simpa using hvertex)
    (fun q hq => num_bound (hweights q hq)) (fun q hq => den_bound (hweights q hq))
    (fun q hq => num_bound (hvalues q hq)) (fun q hq => den_bound (hvalues q hq))
    (fun q hq => num_bound (hp q hq)) (fun q hq => den_bound (hp q hq))
    (fun i => num_bound (hprefix i)) (fun i => den_bound (hprefix i)) ν
    ⟨by simp [ν],hweightsσ,hvaluesσ⟩
  obtain ⟨τ,rv,pv⟩:=save_spec B (name toSet) (average I toSet d S hS)
    ((num_bound havg).trans_lt hMB) ((den_bound havg).trans_lt hMB) (by cases toSet <;> decide) μ ps.2
  exact ⟨τ,(rc.seq (rs.seq rv)).mono (by simp only [List.length_ofFn,cost]; omega),pv⟩

end Lax455465Proofs.RamPotentialAverage

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamPotentialChoice
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

theorem select_spec (B M:ℕ) {n:ℕ} (toSet:Bool) (f:Fin n→ ℚ≥0)
    (hMB:M< B) (h1:1< B) (hindex:2*n+2< B) (hf:∀ v,LpInputSize.Height M (f v:ℚ)):
    Spec B (fun σ => σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (List.ofFn f))
        (RamSetPotential.targetArray toSet) σ∧ 2*n<(σ.arrs "cut.potential").length) (select toSet)
      (fun _ τ => τ.vars "cut.reversed"=(if toSet then 1 else 0)∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn f)) "cut.potential" τ) (24*n+12):=by
  let xs:=RamUnsignedBuffer.encode (List.ofFn f)
  have hlen:xs.length=2*n:=by simp [xs]
  have hwords:∀ x∈xs,x< B:=RamSetPotential.encoded_bound B M (List.ofFn f) hMB
    (by intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hf v)
  rintro σ ⟨hn,hp,hroom⟩
  let ν:=σ.setVar "copy.count" (2*n)
  have rc:Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) σ ν 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩) (by dsimp [Bop.apply]; omega))
  obtain ⟨μ,rr,pr⟩:=RamArrayCopy.command_spec B xs (RamSetPotential.targetArray toSet) "cut.potential" "copy.count"
    h1 (by rw [hlen]; omega) hwords (by cases toSet <;> decide) (by decide) ν
    ⟨hp,by simp [ν,hlen],by rw [hlen]; exact hroom.le⟩
  let τ:=μ.setVar "cut.reversed" (if toSet then 1 else 0)
  have rflag:Run B (.assign "cut.reversed" (.lit (if toSet then 1 else 0))) μ τ 2:=
    Run.assign (evalB_lit (by split_ifs <;> omega))
  exact ⟨τ,(rc.seq (rr.seq rflag)).mono (by rw [hlen]; omega),by simp [τ],pr.2⟩

structure Input {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  fromAverage:Stored "potential.fromAvg" (average I false d Tout hout) σ
  toAverage:Stored "potential.toAvg" (average I true d Tin hin) σ
  fromData:Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ
  toData:Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ
  room:2*n<(σ.arrs "cut.potential").length

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty)
    (hb:Bounds I d Tin Tout hin hout M) (hB:2*M^2+3< B) (hindex:2*n+2< B):
    Spec B (Input I d Tin Tout hin hout) command
      (fun _ τ => τ.vars "cut.reversed"=(if reversed I d Tin Tout hin hout then 1 else 0)∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values I d Tin Tout hin hout))) "cut.potential" τ)
      (24*n+80):=by
  have hMB:M< B:=by nlinarith
  have h1:1< B:=by nlinarith
  have hfrom:LpInputSize.Height M (average I false d Tout hout:ℚ):=by
    simpa only [average,List.take_length] using hb.fromPrefix (products I false d Tout hout).length
  have hto:LpInputSize.Height M (average I true d Tin hin:ℚ):=by
    simpa only [average,List.take_length] using hb.toPrefix (products I true d Tin hin).length
  rintro σ hσ
  obtain ⟨ν,rc,pc⟩:=RamScalarComparison.command_spec B M (average I true d Tin hin) (average I false d Tout hout)
    "potential.toAvg" "potential.fromAvg" hB (num_bound hto) (den_bound hto) (num_bound hfrom) (den_bound hfrom)
    (by decide) (by decide) (by decide) σ ⟨hσ.toAverage,hσ.fromAverage⟩
  have hn:ν.vars "metric.n"=n:=(rc.frame_var _ (by decide)).trans hσ.nValue
  have hroom:2*n<(ν.arrs "cut.potential").length:=by rw [RamFrames.run_array_length rc]; exact hσ.room
  by_cases h:average I true d Tin hin≤ average I false d Tout hout
  · have hcmp:ν.vars "cmp.le"=1:=by simpa only [NNRat.coe_le_coe,if_pos h] using pc
    have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some true:=by
      rw [evalB_condEq (evalB_var (hcmp ▸ h1)) (evalB_lit h1),hcmp]; rfl
    have hp:Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" ν:=by
      simpa only [Prefix,rc.frame_arr "potential.from" (by decide)] using hσ.fromData
    obtain ⟨τ,rs,ps⟩:=select_spec B M false (SetDistanceData.distance false d Tout hout) hMB h1 hindex
      (SetDistanceData.height false d Tout hout M hb.distances) ν ⟨hn,hp,hroom⟩
    exact ⟨τ,(rc.seq (Run.ite_true (d:=select true) hc rs)).mono (by dsimp [Cond.size,Expr.size]; omega),
      by simpa only [reversed,values,if_pos h,Bool.false_eq_true,if_false] using ps⟩
  · have hcmp:ν.vars "cmp.le"=0:=by simpa only [NNRat.coe_le_coe,if_neg h] using pc
    have hc:(Cond.eq (.var "cmp.le") (.lit 1)).evalB B ν=some false:=by
      rw [evalB_condEq (evalB_var (hcmp ▸ (by omega:0< B))) (evalB_lit h1),hcmp]; rfl
    have hp:Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" ν:=by
      simpa only [Prefix,rc.frame_arr "potential.to" (by decide)] using hσ.toData
    obtain ⟨τ,rs,ps⟩:=select_spec B M true (SetDistanceData.distance true d Tin hin) hMB h1 hindex
      (SetDistanceData.height true d Tin hin M hb.distances) ν ⟨hn,hp,hroom⟩
    exact ⟨τ,(rc.seq (Run.ite_false (c:=select false) hc rs)).mono (by dsimp [Cond.size,Expr.size]; omega),
      by simpa only [reversed,values,if_neg h,if_true] using ps⟩

end Lax455465Proofs.RamPotentialChoice

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  weights:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  distances:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  inMask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tin)) "region.inMask" σ
  outMask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tout)) "region.outMask" σ

def sourceArrays:List String:= ["flow.weights","metric.old","region.inMask","region.outMask"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {d:MetricMatrix.Matrix n} {Tin Tout:Finset (Fin n)}
    (h:Input I d Tin Tout σ) (hn:"metric.n"∉cmd.wvars)
    (ha:∀ a∈sourceArrays,a∉cmd.warrs):Input I d Tin Tout τ:=by
  exact ⟨(rr.frame_var _ hn).trans h.nValue,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [sourceArrays]))] using h.weights,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [sourceArrays]))] using h.distances,
    by simpa only [Prefix,rr.frame_arr "region.inMask" (ha _ (by simp [sourceArrays]))] using h.inMask,
    by simpa only [Prefix,rr.frame_arr "region.outMask" (ha _ (by simp [sourceArrays]))] using h.outMask⟩

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} (h:Room n σ):Room n τ:=by
  intro a ha
  rw [RamFrames.run_array_length rr]
  exact h a ha

theorem Room.stage {n:ℕ} {σ:Env} (h:Room n σ) (toSet:Bool):RamSetPotential.Room n toSet σ:=by
  intro a ha
  apply h a
  cases toSet <;> simp_all [scratchArrays,RamRootDistances.array,RamSetPotential.targetArray] <;> tauto

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty)
    (hb:Bounds I d Tin Tout hin hout M) (hM:1≤ M) (hB:2*M^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B):
    Spec B (fun σ => Input I d Tin Tout σ∧ Room n σ) command
      (fun _ τ => Input I d Tin Tout τ∧
        τ.vars "cut.reversed"=(if reversed I d Tin Tout hin hout then 1 else 0)∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values I d Tin Tout hin hout))) "cut.potential" τ)
      (cost n M):=by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamSetPotential.command_spec B M false d Tout hout hM hB hindex hvertex hb.distances σ
    ⟨⟨hσ.nValue,hσ.distances,hσ.outMask⟩,hroom.stage false⟩
  have h1:=Input.frame r1 hσ (by decide) (by dsimp [sourceArrays]; decide)
  obtain ⟨σ2,r2,p2⟩:=RamSetPotential.command_spec B M true d Tin hin hM hB hindex hvertex hb.distances σ1
    ⟨⟨h1.nValue,h1.distances,h1.inMask⟩,(hroom.frame r1).stage true⟩
  have h2:=Input.frame r2 h1 (by decide) (by dsimp [sourceArrays]; decide)
  have hfrom2:Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ2:=by
    simpa only [vector,Prefix,RamSetPotential.targetArray,Bool.false_eq_true,if_false,r2.frame_arr "potential.from" (by decide)] using p1.2
  obtain ⟨σ3,r3,p3⟩:=RamPotentialAverage.command_spec B M I false d Tout hout hB hvertex
    hb.weights hb.distances hb.fromProducts hb.fromPrefix σ2 ⟨h2.nValue,h2.weights,hfrom2⟩
  have h3:=Input.frame r3 h2 (by decide) (by dsimp [sourceArrays]; decide)
  have hto3:Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ3:=by
    simpa only [vector,Prefix,RamSetPotential.targetArray,if_true,r3.frame_arr "potential.to" (by decide)] using p2.2
  obtain ⟨σ4,r4,p4⟩:=RamPotentialAverage.command_spec B M I true d Tin hin hB hvertex
    hb.weights hb.distances hb.toProducts hb.toPrefix σ3 ⟨h3.nValue,h3.weights,hto3⟩
  have h4:=Input.frame r4 h3 (by decide) (by dsimp [sourceArrays]; decide)
  have hfromAvg:Stored "potential.fromAvg" (average I false d Tout hout) σ4:=
    RamRoundingConstants.storedFrame r4 p3 (by decide) (by decide)
  have hfrom4:Prefix (RamUnsignedBuffer.encode (vector false d Tout hout)) "potential.from" σ4:=by
    simpa only [Prefix,(r3.seq r4).frame_arr "potential.from" (by decide)] using hfrom2
  have hto4:Prefix (RamUnsignedBuffer.encode (vector true d Tin hin)) "potential.to" σ4:=by
    simpa only [Prefix,r4.frame_arr "potential.to" (by decide)] using hto3
  have rr4:=r1.seq (r2.seq (r3.seq r4))
  obtain ⟨τ,r5,p5⟩:=RamPotentialChoice.command_spec B M I d Tin Tout hin hout hb hB hvertex σ4
    ⟨h4.nValue,hfromAvg,p4,hfrom4,hto4,(hroom.frame rr4) _ (by simp [scratchArrays])⟩
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),Input.frame r5 h4 (by decide) (by dsimp [sourceArrays]; decide),p5⟩

end Lax455465Proofs.RamLargePotential

end

section

namespace Lax455465Proofs.RamScalarDifference
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem value_eq (a b:ℚ≥0):RamTruncatedSubtract.value a b=a-b:=by
  apply NNRat.coe_injective
  by_cases h:b≤ a
  · rw [NNRat.coe_sub h]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,max_eq_left (sub_nonneg.mpr (NNRat.coe_le_coe.mpr h))]
  · rw [tsub_eq_zero_of_le (le_of_not_ge h)]
    simp only [RamTruncatedSubtract.value,NNRat.coe_mk,NNRat.coe_zero,max_eq_right (sub_nonpos.mpr (NNRat.coe_le_coe.mpr (le_of_not_ge h)))]

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (leftName rightName target:String)
    (hB:2*M^2+3< B) (ha:LpInputSize.Height M (a:ℚ)) (hb:LpInputSize.Height M (b:ℚ))
    (hout:LpInputSize.Height M ((a-b:ℚ≥0):ℚ))
    (hlfresh:leftName++".n"≠"rat.s" ∧ leftName++".d"≠"rat.s" ∧ leftName++".d"≠"rat.n")
    (hrfresh:rightName++".n"≠"rat.s" ∧ rightName++".d"≠"rat.s" ∧ rightName++".d"≠"rat.n")
    (hrretain:rightName++".n"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars∧
      rightName++".d"∉(Com.seq (load leftName) (RamUnsignedArithmetic.copy "left")).wvars)
    (htarget:target++".n"≠"rat.d"):
    Spec B (fun σ => Stored leftName a σ∧ Stored rightName b σ) (command leftName rightName target)
      (fun _ τ => Stored target (a-b) τ) (36*(a.den*b.den).size+170):=by
  have hMB:M< B:=by nlinarith
  have hop:=RamTruncatedSubtract.command_spec B M a b hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
  rintro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamScalarBinary.command_spec B M (36*(a.den*b.den).size+142) a b leftName rightName
    RamTruncatedSubtract.command ((a-b:ℚ≥0):ℚ) hB (num_bound ha) (den_bound ha) (num_bound hb) (den_bound hb)
    hlfresh hrfresh hrretain (by simpa only [value_eq] using hop) σ hσ
  obtain ⟨τ,rs,ps⟩:=save_spec B target (a-b) ((num_bound hout).trans_lt hMB) ((den_bound hout).trans_lt hMB) htarget ν pr
  exact ⟨τ,(rr.seq rs).mono (by omega),ps⟩

end Lax455465Proofs.RamScalarDifference

end

section

namespace Lax455465Proofs.RamCutMeasures
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData MetricMatrix
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData:Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ
  maskData:Prefix (RamUnsignedBuffer.encode (vertexFlags S)) "cut.flags" σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B):
    Spec B (fun σ => Input I S σ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => Input I S τ∧ Stored "cut.capacity" (capacity I S) τ∧ Stored "cut.mass" (mass I S) τ)
      ((36*(M^2).size+234)*(n*n)+(36*(M^2).size+152)*n+52):=by
  have hMB:M< B:=by nlinarith
  let ws:=List.ofFn I.weight
  let vs:=vertexFlags S
  let cs:=values I.capacity
  let es:=values (arcFlags S)
  have hws:ws.length=n:=List.length_ofFn
  have hvs:vs.length=n:=List.length_ofFn
  have hcs:cs.length=n*n:=length_values _
  have hes:es.length=n*n:=length_values _
  have hwn:∀ q∈ws,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact num_bound (hb.weightsBound v)
  have hwd:∀ q∈ws,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact den_bound (hb.weightsBound v)
  have hcn:∀ q∈cs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact num_bound (hb.capacityBound _ _)
  have hcd:∀ q∈cs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact den_bound (hb.capacityBound _ _)
  have hvn:∀ q∈vs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hvd:∀ q∈vs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈S <;> simp [vertexFlags,MaskedMassData.flags,ResidualData.mask,hv] <;> omega
  have hen:∀ q∈es,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have hed:∀ q∈es,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [arcFlags,RamArcMask.matrix]
    cases RamBooleanArithmetic.flag (some true) (ResidualData.mask S _) (ResidualData.mask S _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamArcMask.command_spec B (some true) "cut.flags" "cut.crossing" (ResidualData.mask S)
    (by decide) (by nlinarith) (by omega) (by omega) hindex hvertex σ
    ⟨⟨hσ.nValue,hσ.n2Value,hσ.maskData⟩,hroom⟩
  let σ2:=σ1.setVar "sum.count" (n*n)
  have r2:Run B (.assign "sum.count" (.var "metric.n2")) σ1 σ2 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨p1.1.2.1.symm,p1.1.2.1 ▸ (by omega:n*n< B)⟩)
  have r12:=r1.seq r2
  obtain ⟨σ3,r3,p3⟩:=RamMaskedSum.command_spec B M "flow.capacities" "cut.crossing" cs es
    (by rw [hes,hcs]) hB (by rwa [hcs]) hcn hcd hen hed
    (fun i => num_bound (hb.capacityPrefix i)) (fun i => den_bound (hb.capacityPrefix i)) σ2
    ⟨by simp [σ2,hcs],by simpa only [cs,Prefix,r12.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [es,arcFlags,Prefix,σ2,arrs_setVar] using p1.2⟩
  obtain ⟨σ4,r4,p4⟩:=save_spec B "cut.capacity" (capacity I S)
    ((num_bound hb.cutCapacityBound).trans_lt hMB) ((den_bound hb.cutCapacityBound).trans_lt hMB) (by decide) σ3 p3.2
  have rbefore:=r1.seq (r2.seq (r3.seq r4))
  have hn:σ4.vars "metric.n"=n:=(rbefore.frame_var _ (by decide)).trans hσ.nValue
  let σ5:=σ4.setVar "sum.count" n
  have r5:Run B (.assign "sum.count" (.var "metric.n")) σ4 σ5 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩)
  have rprior:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  obtain ⟨σ6,r6,p6⟩:=RamMaskedSum.command_spec B M "flow.weights" "cut.flags" ws vs
    (by rw [hvs,hws]) hB (by rwa [hws]) hwn hwd hvn hvd
    (fun i => num_bound (hb.massPrefix i)) (fun i => den_bound (hb.massPrefix i)) σ5
    ⟨by simp [σ5,hws],by simpa only [ws,Prefix,rprior.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [vs,Prefix,rprior.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  obtain ⟨τ,r7,p7⟩:=save_spec B "cut.mass" (mass I S)
    ((num_bound hb.massBound).trans_lt hMB) ((den_bound hb.massBound).trans_lt hMB) (by decide) σ6 p6.2
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))
  refine ⟨τ,rr.mono (by simp only [hws,hcs]; nlinarith),?_,?_,p7⟩
  · exact ⟨(rr.frame_var _ (by decide)).trans hσ.nValue,(rr.frame_var _ (by decide)).trans hσ.n2Value,
      RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using hσ.weightsData,
      by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using hσ.capacityData,
      by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using hσ.maskData⟩
  · exact RamRoundingConstants.storedFrame (r5.seq (r6.seq r7)) p4 (by decide) (by decide)

end Lax455465Proofs.RamCutMeasures

end

section

namespace Lax455465Proofs.RamCutRatio
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (σ:Env):Prop where
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacityData:Stored "cut.capacity" (capacity I S) σ
  massData:Stored "cut.mass" (mass I S) σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B):
    Spec B (Input I S) command (fun _ τ => Input I S τ∧ Stored "cut.other" (otherMass I S) τ∧
      Stored "cut.demand" (demand I S) τ∧ Stored "cut.ratio" (ratio I S) τ∧
      τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (144*(M^2).size+416):=by
  have hsize {a b:ℚ≥0} (ha:LpInputSize.Height M (a:ℚ)) (hb:LpInputSize.Height M (b:ℚ)):
      (a.den*b.den).size≤(M^2).size:=Nat.size_le_size (by nlinarith [Nat.mul_le_mul (den_bound ha) (den_bound hb)])
  have hnumsize:(demand I S).num.size≤(M^2).size:=Nat.size_le_size (by nlinarith [num_bound hb.demandBound])
  have h2:2< B:=by nlinarith
  rintro σ hσ
  obtain ⟨σ1,r1,p1⟩:=RamScalarDifference.command_spec B M (RamRoundingInit.total I.weight) (mass I S)
    "round.total" "cut.mass" "cut.other" hB hb.totalBound hb.massBound hb.otherBound
    (by decide) (by decide) (by decide) (by decide) σ ⟨hσ.totalData,hσ.massData⟩
  obtain ⟨σ2,r2,p2⟩:=RamScalarProduct.command_spec B M (mass I S) (otherMass I S)
    "cut.mass" "cut.other" "cut.demand" hB (num_bound hb.massBound) (den_bound hb.massBound)
    (num_bound hb.otherBound) (den_bound hb.otherBound) (by decide) (by decide) (by decide) (by decide) σ1
    ⟨RamRoundingConstants.storedFrame r1 hσ.massData (by decide) (by decide),p1⟩
  obtain ⟨σ3,r3,p3⟩:=RamScalarReciprocal.command_spec B M (demand I S) "cut.demand" "cut.inverseDemand" hM (by nlinarith) hb.demandBound
    (by decide) (by decide) σ2 p2
  have r123:=r1.seq (r2.seq r3)
  obtain ⟨σ4,r4,p4⟩:=RamScalarProduct.command_spec B M (capacity I S) (demand I S)⁻¹
    "cut.capacity" "cut.inverseDemand" "cut.ratio" hB (num_bound hb.cutCapacityBound) (den_bound hb.cutCapacityBound)
    (num_bound hb.inverseBound) (den_bound hb.inverseBound) (by decide) (by decide) (by decide) (by decide) σ3
    ⟨RamRoundingConstants.storedFrame r123 hσ.capacityData (by decide) (by decide),p3⟩
  have hd:σ4.vars "cut.demand.n"=(demand I S).num:=
    ((r3.seq r4).frame_var _ (by decide)).trans p2.1
  have hdB:σ4.vars "cut.demand.n"< B:=by rw [hd]; exact (num_bound hb.demandBound).trans_lt (by nlinarith)
  have hv:∃ τ,Run B valid σ4 τ 6∧ τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0:=by
    by_cases hz:(demand I S).num=0
    · have hc:(Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some true:=by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd,hz]
        rfl
      have rr:Run B (.assign "cut.valid" (.lit 0)) σ4 (σ4.setVar "cut.valid" 0) 2:=Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 0,Run.ite_true (d:=.assign "cut.valid" (.lit 1)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,hz,lt_self_iff_false,if_false]
    · have hc:(Cond.eq (.var "cut.demand.n") (.lit 0)).evalB B σ4=some false:=by
        rw [evalB_condEq (evalB_var hdB) (evalB_lit (by omega)),hd]
        simp [hz]
      have rr:Run B (.assign "cut.valid" (.lit 1)) σ4 (σ4.setVar "cut.valid" 1) 2:=Run.assign (evalB_lit (by omega))
      refine ⟨σ4.setVar "cut.valid" 1,Run.ite_false (c:=.assign "cut.valid" (.lit 0)) hc rr,?_⟩
      simp only [vars_setVar,if_true,admissible_iff,Nat.pos_of_ne_zero hz,if_true]
  obtain ⟨τ,r5,p5⟩:=hv
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono ?_,?_,?_,?_,?_,p5⟩
  · have hs1:=hsize hb.totalBound hb.massBound
    have hs2:=hsize hb.massBound hb.otherBound
    have hs4:=hsize hb.cutCapacityBound hb.inverseBound
    nlinarith
  · exact ⟨RamRoundingConstants.storedFrame rr hσ.totalData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.capacityData (by decide) (by decide),
      RamRoundingConstants.storedFrame rr hσ.massData (by decide) (by decide)⟩
  · exact RamRoundingConstants.storedFrame (r2.seq (r3.seq (r4.seq r5))) p1 (by decide) (by decide)
  · exact RamRoundingConstants.storedFrame (r3.seq (r4.seq r5)) p2 (by decide) (by decide)
  · have hp:=RamRoundingConstants.storedFrame r5 p4 (by decide) (by decide)
    simpa only [ratio,div_eq_mul_inv] using hp

end Lax455465Proofs.RamCutRatio

end

section

namespace Lax455465Proofs.RamCutScore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding CutScoreData
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (S:Finset (Fin n)) (hM:1≤ M)
    (hb:CutScoreHeight.Bounds I S M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B):
    Spec B (fun σ => RamCutMeasures.Input I S σ∧ 2*(n*n)<(σ.arrs "cut.crossing").length) command
      (fun _ τ => RamCutMeasures.Input I S τ∧ Stored "cut.ratio" (ratio I S) τ∧
        τ.vars "cut.valid"=if CutSweeps.admissibleQ I S then 1 else 0) (cost n M):=by
  rintro σ hσ
  obtain ⟨ν,rm,pm⟩:=RamCutMeasures.command_spec B M I S hM hb hB hindex hvertex σ hσ
  obtain ⟨τ,rr,pr⟩:=RamCutRatio.command_spec B M I S hM hb hB ν
    ⟨pm.1.totalData,pm.2.1,pm.2.2⟩
  refine ⟨τ,(rm.seq rr).mono (by dsimp [cost]; omega),?_,pr.2.2.2.1,pr.2.2.2.2⟩
  exact ⟨(rr.frame_var _ (by decide)).trans pm.1.nValue,(rr.frame_var _ (by decide)).trans pm.1.n2Value,
    pr.1.totalData,
    by simpa only [Prefix,rr.frame_arr "flow.weights" (by decide)] using pm.1.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (by decide)] using pm.1.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.flags" (by decide)] using pm.1.maskData⟩

end Lax455465Proofs.RamCutScore

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamThresholdCandidate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding
open scoped NNRat

structure Input {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  count:σ.vars "cut.count"=n
  reversedValue:σ.vars "cut.reversed"=(if reversed then 1 else 0)
  totalData:Stored "round.total" (RamRoundingInit.total I.weight) σ
  weightsData:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacityData:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialData:Prefix (RamUnsignedBuffer.encode (List.ofFn potential)) "cut.potential" σ
  maskRoom:2*n<(σ.arrs "cut.flags").length
  crossingRoom:2*(n*n)<(σ.arrs "cut.crossing").length

def names:List String:= ["metric.n","metric.n2","cut.count","cut.reversed","round.total.n","round.total.d"]
def arrays:List String:= ["flow.weights","flow.capacities","cut.potential"]

theorem Input.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {potential:Fin n→ ℚ≥0} {reversed:Bool} (h:Input I potential reversed σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈arrays,a∉cmd.warrs):Input I potential reversed τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.count,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.reversedValue,
    RamRoundingConstants.storedFrame rr h.totalData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "cut.potential" (ha _ (by simp [arrays]))] using h.potentialData,
    by rw [RamFrames.run_array_length rr "cut.flags"]; exact h.maskRoom,
    by rw [RamFrames.run_array_length rr "cut.crossing"]; exact h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (i:ℕ) (hi:i< n) (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hp:∀ v,LpInputSize.Height M (potential v:ℚ))
    (hb:CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M):
    Spec B (fun σ => Input I potential reversed σ∧ σ.vars "cut.candidate"=i) command
      (fun _ τ => Input I potential reversed τ∧
        RamBestUpdate.Current (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) i τ∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential i))) "cut.flags" τ)
      (cost n M):=by
  have hMB:M< B:=by nlinarith
  let v:Fin n:= ⟨i,hi⟩
  let S:=ThresholdCutData.candidate reversed potential i
  have hS:S=ThresholdCutData.shore reversed potential (potential v):=ThresholdCutData.at_eq reversed potential i hi
  have hmask:MaskedMassData.flags (fun u => RamThresholdMask.chosen reversed (potential u) (potential v))=CutScoreData.vertexFlags S:=by
    rw [hS]
    exact ThresholdCutData.mask_eq reversed potential (potential v)
  rintro σ ⟨hσ,hidx⟩
  have hi':i<(List.ofFn potential).length:=by simpa only [List.length_ofFn] using hi
  have he:(List.ofFn potential)[i]=potential v:=by simp [v]
  obtain ⟨σ1,r1,p1⟩:=RamArrayScalar.command_spec B "cut.potential" "cut.candidate" "cut.threshold" (List.ofFn potential) i hi'
    (by nlinarith) (by omega) (by rw [he]; exact (num_bound (hp v)).trans_lt hMB)
    (by rw [he]; exact (den_bound (hp v)).trans_lt hMB) (by decide) (by decide) σ ⟨hσ.potentialData,hidx⟩
  have h1:=Input.frame r1 hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have maskSpec:∃ σ2,Run B mask σ1 σ2 (110*n+12)∧ Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" σ2:=by
    have applyMask (b:Bool):∃ σ2,Run B (RamThresholdMask.command b) σ1 σ2 (110*n+8)∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun u => RamThresholdMask.chosen b (potential u) (potential v)))) "cut.flags" σ2:=by
      obtain ⟨σ2,rr,pr⟩:=RamThresholdMask.command_spec B M b potential (potential v) hB hvertex
        (fun u => num_bound (hp u)) (fun u => den_bound (hp u)) (num_bound (hp v)) (den_bound (hp v)) σ1
        ⟨⟨h1.nValue,by simpa only [he] using p1,h1.potentialData⟩,h1.maskRoom⟩
      exact ⟨σ2,rr,pr.2⟩
    cases hr:reversed
    · have hv:σ1.vars "cut.reversed"=0:=by simpa only [hr,Bool.false_eq_true,if_false] using h1.reversedValue
      have hc:(Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some false:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega:0< B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩:=applyMask false
      exact ⟨σ2,(Run.ite_false (c:=RamThresholdMask.command true) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
    · have hv:σ1.vars "cut.reversed"=1:=by simpa only [hr,if_true] using h1.reversedValue
      have hc:(Cond.eq (.var "cut.reversed") (.lit 1)).evalB B σ1=some true:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by nlinarith:1< B))) (evalB_lit (by nlinarith)),hv]
        rfl
      obtain ⟨σ2,rr,pr⟩:=applyMask true
      exact ⟨σ2,(Run.ite_true (d:=RamThresholdMask.command false) hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),
        by rw [←hmask,hr]; exact pr⟩
  obtain ⟨σ2,r2,p2⟩:=maskSpec
  have h2:=Input.frame r2 h1 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  obtain ⟨τ,r3,p3⟩:=RamCutScore.command_spec B M I S hM hb hB hindex hvertex σ2
    ⟨⟨h2.nValue,h2.n2Value,h2.totalData,h2.weightsData,h2.capacityData,p2⟩,h2.crossingRoom⟩
  have rr:=r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),Input.frame rr hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide),
    ⟨(rr.frame_var _ (by decide)).trans hidx,p3.2.2,p3.2.1⟩,p3.1.maskData⟩

end Lax455465Proofs.RamThresholdCandidate

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamPotentialSweep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding RamThresholdCandidate
open scoped NNRat

def Selected {n:ℕ} (reversed:Bool) (potential:Fin n→ ℚ≥0):Option ℕ→ Env→ Prop
  | none,_ => True
  | some j,σ => Prefix (RamUnsignedBuffer.encode
      (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed potential j))) "cut.flags" σ

theorem input_set {n:ℕ} {I:RationalInstance n} {potential:Fin n→ ℚ≥0} {reversed:Bool}
    (σ:Env) (k:ℕ) (name:String) (hn:name∈["cut.candidate","best.found","best.index"])
    (h:Input I potential reversed σ):Input I potential reversed (σ.setVar name k):=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl
  all_goals
    exact ⟨by simpa using h.nValue,by simpa using h.n2Value,by simpa using h.count,
      by simpa using h.reversedValue,by simpa [Stored] using h.totalData,
      h.weightsData,h.capacityData,h.potentialData,h.maskRoom,h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hp:∀ v,LpInputSize.Height M (potential v:ℚ))
    (hb:∀ i< n,CutScoreHeight.Bounds I (ThresholdCutData.candidate reversed potential i) M):
    Spec B (Input I potential reversed) command
      (fun _ τ => Input I potential reversed τ∧
        RamBestUpdate.Matches (ThresholdCutData.score I reversed potential)
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ∧
        Selected reversed potential
          (BestCutIndex.best (ThresholdCutData.valid I reversed potential) (ThresholdCutData.score I reversed potential) n) τ)
      (cost n M):=by
  let valid:=ThresholdCutData.valid I reversed potential
  let value:=ThresholdCutData.score I reversed potential
  let best:=BestCutIndex.best valid value n
  have producer (i:ℕ) (hi:i< n):=RamThresholdCandidate.command_spec B M I potential reversed i hi hM hB hindex hvertex hp (hb i hi)
  have scan:=RamBestFold.command_spec B M (RamThresholdCandidate.cost n M) (Input I potential reversed)
    valid value n RamThresholdCandidate.command hB (by omega)
    (fun i hi => (hb i hi).ratioBound) (fun _ h => h.count) input_set
    (fun i hi σ h => by obtain ⟨τ,rr,pr⟩:=producer i hi σ h; exact ⟨τ,rr,pr.1,pr.2.1⟩)
    (by dsimp [RamBestFold.bestNames]; decide)
    (fun rr h => Input.frame rr h (by dsimp [RamThresholdCandidate.names]; decide) (by dsimp [RamThresholdCandidate.arrays]; decide))
  rintro σ hσ
  obtain ⟨ν,rs,ps⟩:=scan σ hσ
  change Input I potential reversed ν∧ RamBestUpdate.Matches value best ν at ps
  have h1:1< B:=by nlinarith
  have hf:∃ τ,Run B finish ν τ (RamThresholdCandidate.cost n M+6)∧
      Input I potential reversed τ∧ RamBestUpdate.Matches value best τ∧ Selected reversed potential best τ:=by
    cases he:best with
    | none =>
      have hv:ν.vars "best.found"=0:=by simpa only [he,RamBestUpdate.Matches] using ps.2
      have hc:(Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some false:=by
        rw [evalB_condEq (evalB_var (hv ▸ (by omega:0< B))) (evalB_lit h1),hv]
        rfl
      exact ⟨ν,(Run.ite_false (c:=restore) hc Run.skip).mono (by dsimp [Cond.size,Expr.size]; omega),
        ps.1,hv,trivial⟩
    | some j =>
      have hj:j< n:=(BestCutIndex.best_sound valid value n j he).1
      have hm:RamBestUpdate.Matches value (some j) ν:=by simpa only [he] using ps.2
      have hc:(Cond.eq (.var "best.found") (.lit 1)).evalB B ν=some true:=by
        rw [evalB_condEq (evalB_var (hm.1 ▸ h1)) (evalB_lit h1),hm.1]
        rfl
      let μ:=ν.setVar "cut.candidate" j
      have ri:Run B (.assign "cut.candidate" (.var "best.index")) ν μ 2:=
        Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.1.symm,by rw [hm.2.1]; omega⟩)
      obtain ⟨τ,rp,pp⟩:=producer j hj μ ⟨input_set ν j "cut.candidate" (by simp) ps.1,by simp [μ]⟩
      have rr:=Run.ite_true (d:=.skip) hc (ri.seq rp)
      exact ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),pp.1,
        RamBestFold.Matches.frame rr hm (by dsimp [RamBestFold.bestNames]; decide),pp.2.2⟩
  obtain ⟨τ,rf,pf⟩:=hf
  exact ⟨τ,(rs.seq rf).mono (by dsimp [cost]; omega),pf⟩

theorem selected_le {n:ℕ} (I:RationalInstance n) (potential:Fin n→ ℚ≥0) (reversed:Bool)
    (S:Finset (Fin n)) (hS:S∈CutSweeps.candidates (ThresholdCutData.potential reversed potential))
    (hvalid:CutSweeps.admissibleQ I S):
    ∃ j,BestCutIndex.best (ThresholdCutData.valid I reversed potential)
        (ThresholdCutData.score I reversed potential) n=some j∧ j< n∧
      CutSweeps.admissibleQ I (ThresholdCutData.candidate reversed potential j)∧
      CutSweeps.ratioQ I (ThresholdCutData.candidate reversed potential j)≤ CutSweeps.ratioQ I S:=by
  rw [←ThresholdCutData.candidates_eq] at hS
  obtain ⟨k,hk,hget⟩:=List.mem_iff_getElem.mp hS
  have hkn:k< n:=by simpa only [ThresholdCutData.length_candidates] using hk
  have hcan:ThresholdCutData.candidate reversed potential k=S:=by
    rw [ThresholdCutData.candidate,List.getD_eq_get _ ∅ ⟨k,hk⟩]
    exact hget
  have hv:ThresholdCutData.valid I reversed potential k:=by
    simpa only [ThresholdCutData.valid,hcan] using hvalid
  cases he:BestCutIndex.best (ThresholdCutData.valid I reversed potential)
      (ThresholdCutData.score I reversed potential) n with
  | none => exact False.elim ((BestCutIndex.best_none _ _ _).mp he k hkn hv)
  | some j =>
    have hs:=BestCutIndex.best_sound _ _ n j he
    refine ⟨j,rfl,hs.1,hs.2,?_⟩
    have hm:=BestCutIndex.best_minimal _ _ n j k he hkn hv
    have hq:=NNRat.coe_le_coe.mpr hm
    simpa only [ThresholdCutData.score,CutScoreData.coe_ratio,hcan] using hq

end Lax455465Proofs.RamPotentialSweep

end

section

namespace Lax455465Proofs.PotentialCandidates
open PotentialLayers

theorem layer_shore {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    CutLayers.shore (build a) i=Finset.univ.filter (fun v => a v≤(values a)[i.val]'(by simpa [values_length] using i.isLt)):=by
  let xs:=values a
  have hi:i.val< xs.length:=by simpa only [xs,values_length] using i.isLt
  ext v
  simp only [CutLayers.shore,Finset.mem_filter,Finset.mem_univ,true_and]
  have hv:xs.idxOf (a v)< xs.length:=List.idxOf_lt_length_of_mem (value_mem a v)
  have sorted:xs.SortedLE:=List.sortedLE_mergeSort
  change xs.idxOf (a v)≤ i.val↔ a v≤ xs[i.val]
  constructor
  · intro h
    have hm:=sorted.monotone_get (show (⟨xs.idxOf (a v),hv⟩:Fin xs.length)≤⟨i.val,hi⟩ from h)
    simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
  · intro h
    by_contra hn
    have hlt:i.val< xs.idxOf (a v):=by omega
    have hm:=sorted.monotone_get (show (⟨i.val,hi⟩:Fin xs.length)≤⟨xs.idxOf (a v),hv⟩ from hlt.le)
    have hrev:xs[i.val]≤ a v:=by simpa only [List.get_eq_getElem,List.getElem_idxOf] using hm
    have he:xs[i.val]=a v:=le_antisymm hrev h
    have hnot:=List.not_of_lt_findIdx (p:=fun q:ℚ => q==a v) (xs:=xs) hlt
    simp [he] at hnot

theorem layer_mem {n:ℕ} (a:Fin n→ ℚ) (i:Fin n):
    CutLayers.shore (build a) i∈CutSweeps.candidates a:=by
  have hi:i.val<(values a).length:=by simpa only [values_length] using i.isLt
  have hm:(values a)[i.val]∈values a:=List.getElem_mem hi
  obtain ⟨v,hv⟩:=List.mem_ofFn.mp (List.mem_mergeSort.mp hm)
  rw [layer_shore,←hv]
  exact List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩

theorem round_mem {n:ℕ} (I:Lax455465.RationalEncoding.RationalInstance n) (a:Fin n→ ℚ)
    (S:Finset (Fin n)) (hS:PotentialLayers.round I a=some S):S∈CutSweeps.candidates a:=by
  have hm:=(CutSweeps.choose_sound I (ThresholdRounding.layerCandidates (build a)) S hS).1
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hm
  exact layer_mem a i

end Lax455465Proofs.PotentialCandidates

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamLargeCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped BigOperators NNRat

structure Input {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (σ:Env):Prop where
  potential:RamLargePotential.Input I d Tin Tout σ
  n2Value:σ.vars "metric.n2"=n*n
  total:Stored "round.total" (RamRoundingInit.total I.weight) σ
  capacities:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  potentialRoom:RamLargePotential.Room n σ
  maskRoom:2*n<(σ.arrs "cut.flags").length
  crossingRoom:2*(n*n)<(σ.arrs "cut.crossing").length

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty)
    (hb:Bounds I d Tin Tout hin hout M) (hcuts:∀ S,CutScoreHeight.Bounds I S M)
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (U:ℚ) (hgood:∃ S∈CutSweeps.candidates (LargeBallRounding.potential I (MetricMatrix.rational d) Tin Tout hin hout),
      CutSweeps.admissibleQ I S∧ CutSweeps.ratioQ I S≤ U):
    Spec B (Input I d Tin Tout) command
      (fun _ τ => ∃ S:Finset (Fin n),CutSweeps.admissibleQ I S∧ CutSweeps.ratioQ I S≤ U∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M):=by
  let f:=values I d Tin Tout hin hout
  let reversed:=LargePotentialData.reversed I d Tin Tout hin hout
  have hf:∀ v,LpInputSize.Height M (f v:ℚ):=by
    intro v
    dsimp only [f,values]
    split_ifs <;> exact SetDistanceData.height _ d _ _ M hb.distances v
  obtain ⟨S,hS,hvalid,hratio⟩:=hgood
  have hSmem:S∈CutSweeps.candidates (ThresholdCutData.potential reversed f):=by
    simpa only [f,reversed,LargePotentialData.potential_eq] using hS
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩:=RamPotentialSweep.selected_le I f reversed S hSmem hvalid
  rintro σ hσ
  obtain ⟨ν,rp,pp⟩:=RamLargePotential.command_spec B M I d Tin Tout hin hout hb hM hB hindex hvertex σ
    ⟨hσ.potential,hσ.potentialRoom⟩
  let μ:=ν.setVar "cut.count" n
  have rc:Run B (.assign "cut.count" (.var "metric.n")) ν μ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pp.1.nValue.symm,pp.1.nValue ▸ (by omega:n< B)⟩)
  have htotal:=RamRoundingConstants.storedFrame rp hσ.total (by decide) (by decide)
  have hcap:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" ν:=by
    simpa only [Prefix,rp.frame_arr "flow.capacities" (by decide)] using hσ.capacities
  have hinput:RamThresholdCandidate.Input I f reversed μ:=by
    exact ⟨by simpa [μ] using pp.1.nValue,
      by simpa [μ,rp.frame_var "metric.n2" (by decide)] using hσ.n2Value,
      by simp [μ],by simpa [μ] using pp.2.1,htotal,pp.1.weights,hcap,pp.2.2,
      by rw [show μ.arrs "cut.flags"=ν.arrs "cut.flags" from rfl,RamFrames.run_array_length rp]; exact hσ.maskRoom,
      by rw [show μ.arrs "cut.crossing"=ν.arrs "cut.crossing" from rfl,RamFrames.run_array_length rp]; exact hσ.crossingRoom⟩
  obtain ⟨τ,rs,ps⟩:=RamPotentialSweep.command_spec B M I f reversed hM hB hindex hvertex hf (fun i hi => hcuts _) μ hinput
  have hmask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate reversed f j))) "cut.flags" τ:=by
    simpa only [hj,RamPotentialSweep.Selected] using ps.2.2
  exact ⟨τ,(rp.seq (rc.seq rs)).mono (by dsimp [cost]; omega),
    ThresholdCutData.candidate reversed f j,hjvalid,hjratio.trans hratio,hmask⟩

theorem large_ball_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (Tin Tout:Finset (Fin n)) (hin:Tin.Nonempty) (hout:Tout.Nonempty) (root:Fin n)
    (hb:Bounds I d Tin Tout hin hout M) (hcuts:∀ S,CutScoreHeight.Bounds I S M)
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (htotal:0< LargeBallRounding.total I) (hdiag:∀ v,d v v=0)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (htri:∀ u v w,(d u w:ℚ)≤(d u v:ℚ)+(d v w:ℚ))
    (hinRadius:∀ s∈Tin,(d s root:ℚ)≤1/(4*LargeBallRounding.total I^2))
    (houtRadius:∀ t∈Tout,(d root t:ℚ)≤1/(4*LargeBallRounding.total I^2))
    (hinMass:(2/3:ℚ)*LargeBallRounding.total I≤ LargeBallRounding.mass I Tin)
    (houtMass:(2/3:ℚ)*LargeBallRounding.total I≤ LargeBallRounding.mass I Tout):
    Spec B (Input I d Tin Tout) command
      (fun _ τ => ∃ S:Finset (Fin n),CutSweeps.admissibleQ I S∧
        CutSweeps.ratioQ I S≤6*(∑ u,∑ v,(I.capacity u v:ℚ)*(d u v:ℚ))∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n M):=by
  obtain ⟨S,hS,hvalid,hratio⟩:=LargeBallRounding.round_correct I (MetricMatrix.rational d) Tin Tout hin hout root htotal
    (fun _ _ => NNRat.coe_nonneg _) (by intro v; simp [MetricMatrix.rational,hdiag]) hsep htri hinRadius houtRadius hinMass houtMass
  exact command_spec B M I d Tin Tout hin hout hb hcuts hM hB hindex hvertex _
    ⟨S,PotentialCandidates.round_mem I _ S hS,hvalid,hratio⟩

end Lax455465Proofs.RamLargeCut

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.HistoryPotentialData
open Lax455465.RationalEncoding RamRegionRecord RegionHistory RegionOrdering
open scoped BigOperators NNRat

def contains {n:ℕ} (d:MetricMatrix.Matrix n) (e:Entry n) (v:Fin n):Bool:=
  if e.outward then decide (d e.root v< e.radius) else decide (d v e.root< e.radius)
def predicate {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n) (i:ℕ):Bool:=
  ((history[i]?).map (fun e => contains d e v)).getD false

theorem contains_eq {n:ℕ} (d:MetricMatrix.Matrix n) (e:Entry n) (v:Fin n):
    contains d e v=decide (v∈e.region.ball (MetricMatrix.rational d)):=by
  cases he:e.outward <;> simp [contains,Entry.region,RegionLoop.Region.ball,RegionCharging.ball,MetricMatrix.rational,he]

theorem predicate_at {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (i:ℕ) (hi:i< history.length):predicate d history v i=contains d history[i] v:=by
  simp only [predicate,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

theorem index_findIdx_regions {n:ℕ} (d:RationalDistances.Distance n) (history:List (RegionLoop.Region n)) (v:Fin n):
    (index d history v).val=history.findIdx (fun e => decide (v∈ e.ball d)):=by
  induction history with
  | nil => rfl
  | cons e rest ih =>
    by_cases hv:v∈ e.ball d <;> simp [RegionHistory.index,List.findIdx_cons,hv,ih]

theorem index_findIdx {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n):
    (index (MetricMatrix.rational d) (history.map Entry.region) v).val=history.findIdx (fun e => contains d e v):=by
  rw [index_findIdx_regions,List.findIdx_map]
  simp only [Function.comp_def,contains_eq]

theorem first_index {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n):
    (RamFind.first (predicate d history v) history.length).getD history.length=
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val:=by
  rw [index_findIdx]
  cases he:RamFind.first (predicate d history v) history.length with
  | none =>
    simp only [Option.getD_none]
    symm
    apply List.findIdx_eq_length_of_false
    intro e he
    obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp he
    have hf:=RamFind.first_none (predicate d history v) history.length (by assumption) i hi
    simpa only [predicate_at d history v i hi] using hf
  | some j =>
    simp only [Option.getD_some]
    have hs:=List.find?_range_eq_some.mp he
    have hj:=List.mem_range.mp hs.2.1
    symm
    apply (List.findIdx_eq hj).mpr
    exact ⟨by simpa only [predicate_at d history v j hj] using hs.1,
      fun i hi => by simpa [predicate_at d history v i (hi.trans hj)] using hs.2.2 i hi⟩

def values {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n):ℚ≥0:=
  (position history.length (orientation (history.map Entry.region))
    (index (MetricMatrix.rational d) (history.map Entry.region) v).val:ℕ)

theorem value_none {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (h:RamFind.first (predicate d history v) history.length=none):
    values d history v=(history.length:ℚ≥0):=by
  have hi:=first_index d history v
  rw [h,Option.getD_none] at hi
  unfold values
  rw [←hi]
  simp [position]

theorem value_some {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (j:ℕ) (h:RamFind.first (predicate d history v) history.length=some j)
    (hj:j < history.length):
    values d history v=((if history[j].outward then 2*history.length-j else j:ℕ):ℚ≥0):=by
  have hi:=first_index d history v
  rw [h,Option.getD_some] at hi
  unfold values
  rw [←hi]
  have ho:orientation (history.map Entry.region) j=history[j].outward:=by
    simp only [orientation,List.getElem?_map,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some,Entry.region]
  simp only [position,if_neg (Nat.ne_of_lt hj),ho]

theorem value_height {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (M:ℕ)
    (h1:1≤ M) (hm:2*history.length≤ M) (v:Fin n):LpInputSize.Height M (values d history v:ℚ):=by
  have hj:(index (MetricMatrix.rational d) (history.map Entry.region) v).val≤ history.length:=by
    have h:=(index (MetricMatrix.rational d) (history.map Entry.region) v).isLt
    simp only [List.length_map] at h
    omega
  have hp:position history.length (orientation (history.map Entry.region))
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val≤ M:=by
    unfold position
    split_ifs <;> omega
  exact ⟨by simpa [values] using hp,by simpa [values] using h1⟩

theorem late_mem {n k:ℕ} (labels:Fin n→ Fin (k+1)) (orientation:ℕ→ Bool) (t:ℕ)
    (hnonempty:(lateCut labels orientation t).Nonempty):
    lateCut labels orientation t∈ThresholdCutData.candidates true
      (fun v => (position k orientation (labels v).val:ℕ)):=by
  let S:=lateCut labels orientation t
  let pos:=fun v => position k orientation (labels v).val
  obtain ⟨v,hv,hmin⟩:=Finset.exists_mem_eq_inf' hnonempty pos
  have hvt:t< pos v:=(Finset.mem_filter.mp hv).2
  have he:S=ThresholdCutData.shore true (fun u => (pos u:ℚ≥0)) (pos v):=by
    ext u
    simp only [S,lateCut,ThresholdCutData.shore,Finset.mem_filter,Finset.mem_univ,true_and,
      RamThresholdMask.chosen,if_true,decide_eq_true_eq]
    constructor
    · intro hu
      have hm:=Finset.inf'_le pos (show u∈lateCut labels orientation t by simpa [lateCut] using hu)
      rw [hmin] at hm
      exact_mod_cast hm
    · intro hu
      have hpos:pos v≤ pos u:=by exact_mod_cast hu
      exact hvt.trans_le hpos
  rw [show lateCut labels orientation t=S from rfl,he]
  exact List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩

theorem round_mem {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (history:List (Entry n))
    (S:Finset (Fin n))
    (hs:BalancedRegionCut.round I (index (MetricMatrix.rational d) (history.map Entry.region))
      (orientation (history.map Entry.region))=some S) (hv:CutSweeps.admissibleQ I S):
    S∈CutSweeps.candidates (ThresholdCutData.potential true (values d history)):=by
  unfold BalancedRegionCut.round at hs
  obtain ⟨t,ht,he⟩:=Option.map_eq_some_iff.mp hs
  have hnonempty:S.Nonempty:=by
    by_contra hn
    have he:=Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [he,CutSweeps.massQ,Finset.sum_empty,lt_self_iff_false] using hv.1
  subst S
  rw [←ThresholdCutData.candidates_eq]
  change _∈ ThresholdCutData.candidates true (fun v =>
    (position history.length (orientation (history.map Entry.region))
      (index (MetricMatrix.rational d) (history.map Entry.region) v).val:ℚ≥0))
  simpa only [List.length_map] using late_mem
    (index (MetricMatrix.rational d) (history.map Entry.region)) (orientation (history.map Entry.region)) t hnonempty

end Lax455465Proofs.HistoryPotentialData

end

section

namespace Lax455465Proofs.RamHistoryEntry
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open scoped NNRat

theorem word_at {n:ℕ} (history:List (Entry n)) (i:ℕ) (hi:i < history.length) (j:Fin 4):
    (words history)[4*i+j.val]?=some (history[i].words[j.val]'(by simp [Entry.words])):=by
  induction history generalizing i with
  | nil => simp at hi
  | cons e rest ih =>
    cases i with
    | zero => fin_cases j <;> simp [words,Entry.words]
    | succ i =>
      have hr:i < rest.length:=by simpa using hi
      simpa only [words,List.flatMap_cons,Entry.words,List.cons_append,List.nil_append,
        show 4*(i+1)+j.val=Nat.succ (Nat.succ (Nat.succ (Nat.succ (4*i+j.val)))) by omega,
        List.getElem?_cons_succ,List.getElem_cons_succ] using ih i hr

def Output {n:ℕ} (e:Entry n) (σ:Env):Prop:=
  σ.vars "history.root"=e.root.val∧ Stored "history.radius" e.radius σ∧
    σ.vars "history.outward"=(if e.outward then 1 else 0)

theorem command_spec (B:ℕ) {n:ℕ} (history:List (Entry n)) (i:ℕ) (hi:i < history.length)
    (h4:4 < B) (hlen:4*history.length < B) (hn:n < B)
    (hnum:history[i].radius.num < B) (hden:history[i].radius.den < B):
    Spec B (fun σ => Prefix (words history) "region.history" σ∧ σ.vars "find.i"=i) command
      (fun _ τ => Output history[i] τ) 22:=by
  rintro σ ⟨hp,hiσ⟩
  have hg:∀ j:Fin 4, (σ.arrs "region.history")[4*i+j.val]?=some (history[i].words[j.val]'(by simp [Entry.words])):=by
    intro j
    have hj:4*i+j.val < (words history).length:=by simp only [length_words]; omega
    exact (hp _ hj).trans ((List.getElem?_eq_getElem hj).symm.trans (word_at history i hi j))
  have hg0:=hg 0
  have hg1:=hg 1
  have hg2:=hg 2
  have hg3:=hg 3
  simp only [Entry.words,Fin.val_zero,Fin.val_one,Fin.val_two,Nat.add_zero,
    List.getElem_cons_zero,List.getElem_cons_succ] at hg0 hg1 hg2 hg3
  have hroom:4*i+3 < (σ.arrs "region.history").length:=List.getElem?_eq_some_iff.mp hg3 |>.1
  have hr:history[i].root.val < B:=history[i].root.isLt.trans hn
  have ho:(if history[i].outward then 1 else 0) < B:=by split_ifs <;> omega
  have hiB:i < B:=by omega
  have hbase:4*i < B:=by omega
  have ha1:4*i+1 < B:=by omega
  have ha2:4*i+2 < B:=by omega
  have ha3:4*i+3 < B:=by omega
  (expose_names;
    (refine let c0:Env→ Prop:= @Output n (@getElem (List (Entry n)) Nat (Entry n) (fun (as:List (Entry n)) (i_1:Nat) => Nat.lt i_1 (@List.length (Entry n) as)) (@List.instGetElemNatLtLength (Entry n)) history i hi); let c1:Env→ Prop:=(fun (x τ:Env) => c0 τ) σ; let c2:Nat:=Nat.mul ((4:Nat)) (Env.vars σ "find.i"); let c3:Env:=Env.setVar σ "history.address" c2; let c4:Nat:=Env.vars c3 "history.address"; let c5:Nat:= @List.getD Nat (Env.arrs c3 "region.history") c4 ((0:Nat)); let c6:Env:=Env.setVar c3 "history.root" c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Env.vars c6 "history.address"; let c9:Nat:=c7 c8 ((1:Nat)); let c10:Nat:= @List.getD Nat (Env.arrs c6 "region.history") c9 ((0:Nat)); let c11:Env:=Env.setVar c6 "history.radius.n" c10; let c12:Nat:=Env.vars c11 "history.address"; let c13:Nat:=c7 c12 ((2:Nat)); let c14:Nat:= @List.getD Nat (Env.arrs c11 "region.history") c13 ((0:Nat)); let c15:Env:=Env.setVar c11 "history.radius.d" c14; let c16:Nat:=Env.vars c15 "history.address"; let c17:Nat:=c7 c16 ((3:Nat)); let c18:Nat:= @List.getD Nat (Env.arrs c15 "region.history") c17 ((0:Nat)); let c19:Env:=Env.setVar c15 "history.outward" c18; let c20:Nat→ Nat:=c7 ((1:Nat)); let c21:Expr:=Expr.mul (Expr.lit ((4:Nat))) (Expr.var "find.i"); let c22:Nat:=c20 (Expr.size c21); let c23:Nat:=c20 (Expr.size (Expr.get "region.history" (Expr.var "history.address"))); let c24:Expr:=Expr.add (Expr.var "history.address") (Expr.lit ((1:Nat))); let c25:Expr:=Expr.get "region.history" c24; let c26:Nat:=c20 (Expr.size c25); let c27:Expr:=Expr.add (Expr.var "history.address") (Expr.lit ((2:Nat))); let c28:Expr:=Expr.get "region.history" c27; let c29:Nat:=c20 (Expr.size c28); let c30:Expr:=Expr.add (Expr.var "history.address") (Expr.lit ((3:Nat))); let c31:Expr:=Expr.get "region.history" c30; let c32:Nat:=c20 (Expr.size c31); let c33:Nat:=c7 c29 c32; let c34:Nat:=c7 c26 c33; let c35:Nat:=c7 c23 c34; let c36:Com:=Com.assign "history.radius.n" c25; let c37:Com:=Com.assign "history.radius.d" c28; let c38:Com:=Com.assign "history.outward" c31; let c39:Com:=Com.seq c37 c38; let c40:Com:=Com.seq c36 c39; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((22:Nat))) (c1 σ')) c19 (@And.intro (Run B command σ c19 ((22:Nat))) (c1 c19) (RunStep.mono B command σ c19 (c7 c22 c35) ((22:Nat)) (RunStep.seq B (Com.assign "history.address" c21) (Com.seq (Com.assign "history.root" (Expr.get "region.history" (Expr.var "history.address"))) c40) σ c3 c19 c22 c35 (RunStep.assign B σ "history.address" c21 c2 (RunStep.eval_mul B σ (Expr.lit ((4:Nat))) (Expr.var "find.i") ((4:Nat)) (Env.vars σ "find.i") (RunStep.eval_lit B ((4:Nat)) σ h4) (RunStep.eval_var B σ "find.i" (?nAX_g7168_0_0_0)) (?nAX_g7168_0_0_1))) (RunStep.seq B (Com.assign "history.root" (Expr.get "region.history" (Expr.var "history.address"))) c40 c3 c6 c19 c23 c34 (RunStep.assign B c3 "history.root" (Expr.get "region.history" (Expr.var "history.address")) c5 (RunStep.eval_get B c3 "region.history" (Expr.var "history.address") c4 (RunStep.eval_var B c3 "history.address" (?nAX_g7168_0_0_2)) (?nAX_g7168_0_0_3) ?_)) (RunStep.seq B c36 c39 c6 c11 c19 c26 c33 (RunStep.assign B c6 "history.radius.n" c25 c10 (RunStep.eval_get B c6 "region.history" c24 c9 (RunStep.eval_add B c6 (Expr.var "history.address") (Expr.lit ((1:Nat))) c8 ((1:Nat)) (RunStep.eval_var B c6 "history.address" (?nAX_g7168_0_0_4)) (RunStep.eval_lit B ((1:Nat)) c6 (?nAX_g7168_0_0_5)) (?nAX_g7168_0_0_6)) (?nAX_g7168_0_0_7) ?_)) (RunStep.seq B c37 c38 c11 c15 c19 c29 c32 (RunStep.assign B c11 "history.radius.d" c28 c14 (RunStep.eval_get B c11 "region.history" c27 c13 (RunStep.eval_add B c11 (Expr.var "history.address") (Expr.lit ((2:Nat))) c12 ((2:Nat)) (RunStep.eval_var B c11 "history.address" (?nAX_g7168_0_0_8)) (RunStep.eval_lit B ((2:Nat)) c11 (?nAX_g7168_0_0_9)) (?nAX_g7168_0_0_10)) (?nAX_g7168_0_0_11) ?_)) (RunStep.assign B c15 "history.outward" c31 c18 (RunStep.eval_get B c15 "region.history" c30 c17 (RunStep.eval_add B c15 (Expr.var "history.address") (Expr.lit ((3:Nat))) c16 ((3:Nat)) (RunStep.eval_var B c15 "history.address" (?nAX_g7168_0_0_12)) (RunStep.eval_lit B ((3:Nat)) c15 (?nAX_g7168_0_0_13)) (?nAX_g7168_0_0_14)) (?nAX_g7168_0_0_15) ?_)))))) (?nAX_g7168_0_0_16)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7168_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7168_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Output,Stored]

end Lax455465Proofs.RamHistoryEntry

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamHistoryTest
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP FlowLpIndices
open scoped NNRat

def pair {n:ℕ} (e:Entry n) (v:Fin n):Fin n × Fin n:=
  if e.outward then (e.root,v) else (v,e.root)

def Context {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "find.count"=history.length∧ σ.vars "history.vertex"=v.val∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ∧
    Prefix (words history) "region.history" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {d:MetricMatrix.Matrix n} {history:List (Entry n)} {v:Fin n} (h:Context d history v σ)
    (hx:∀ x∈["metric.n","find.count","history.vertex"],x∉cmd.wvars)
    (ha:∀ a∈["metric.old","region.history"],a∉cmd.warrs):Context d history v τ:=by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "find.count" (hx _ (by simp)),
    rr.frame_var "history.vertex" (hx _ (by simp)),rr.frame_arr "metric.old" (ha _ (by simp)),
    rr.frame_arr "region.history" (ha _ (by simp))] using h

theorem address_spec (B:ℕ) {n:ℕ} (e:Entry n) (v:Fin n) (h1:1 < B) (hn:n < B) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "history.vertex"=v.val∧ RamHistoryEntry.Output e σ) address
      (fun _ τ => τ.vars "history.edge"=(edgeIndex n (pair e v)).val) 10:=by
  have hrv:(edgeIndex n (e.root,v)).val < B:=(edgeIndex n (e.root,v)).isLt.trans hn2
  have hvr:(edgeIndex n (v,e.root)).val < B:=(edgeIndex n (v,e.root)).isLt.trans hn2
  rw [edge_value] at hrv hvr
  have hr:e.root.val < B:=e.root.isLt.trans hn
  have hv:v.val < B:=v.isLt.trans hn
  have hrn:e.root.val*n < B:=by omega
  have hvn:v.val*n < B:=by omega
  rintro σ ⟨hnσ,hvσ,hrσ,hqσ,hoσ⟩
  cases he:e.outward <;> (expose_names;
                             (refine
                                 let c0:Prop:= @Eq Nat (Env.vars σ "history.outward") ((1:Nat));
                                 let c1:Prop:=Not c0;
                                 let c2:Nat→ Nat→ Nat:=Nat.mul;
                                 let c3:Nat:=c2 n n;
                                 let c4:Type:=Fin c3;
                                 let c5:Type:=Equiv (Edge n) c4;
                                 let c6:Nat:=
                                   @Fin.val c3
                                     (@DFunLike.coe c5 (Edge n) (fun (x:Edge n) => c4)
                                       (@EquivLike.toFunLike c5 (Edge n) c4 (@Equiv.instEquivLike (Edge n) c4)) (edgeIndex n) (@pair n e v));
                                 let c7:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "history.edge") c6) σ;
                                 let c8:Env→ Prop:=fun (σ':Env) =>
                                   And (Run B address σ σ' ((10:Nat))) (c7 σ');
                                 let c9:Nat→ Nat→ Nat:=Nat.add;
                                 let c10:Nat:=c2 (Env.vars σ "history.root") (Env.vars σ "metric.n");
                                 let c11:Nat:=c9 c10 (Env.vars σ "history.vertex");
                                 let c12:Env:=Env.setVar σ "history.edge" c11;
                                 let c13:Nat→ Nat:=c9 ((1:Nat));
                                 let c14:Cond:=
                                   Cond.eq (Expr.var "history.outward") (Expr.lit ((1:Nat)));
                                 let c15:Nat→ Nat:=c9 (c13 (Cond.size c14));
                                 let c16:Expr:=Expr.add (Expr.mul (Expr.var "history.root") (Expr.var "metric.n")) (Expr.var "history.vertex");
                                 let c17:Nat:=c13 (Expr.size c16);
                                 let c18:Com:=Com.assign "history.edge" c16;
                                 let c19:Expr:=Expr.add (Expr.mul (Expr.var "history.vertex") (Expr.var "metric.n")) (Expr.var "history.root");
                                 let c20:Com:=Com.assign "history.edge" c19;
                                 let c21:Nat:=c2 (Env.vars σ "history.vertex") (Env.vars σ "metric.n");
                                 let c22:Nat:=c9 c21 (Env.vars σ "history.root");
                                 let c23:Env:=Env.setVar σ "history.edge" c22;
                                 let c24:Nat:=c13 (Expr.size c19);
                                 @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c8) (Classical.em c0)
                                   (fun (hcase:c0) =>
                                     @Exists.intro Env c8 c12
                                       (@And.intro (Run B address σ c12 ((10:Nat))) (c7 c12)
                                         (RunStep.mono B address σ c12 (c15 c17) ((10:Nat))
                                           (RunStep.ite_true B c14 c18 c20 σ c12 c17
                                             (RunStep.cond_eq_true B σ (Expr.var "history.outward")
                                               (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                               ((1:Nat))
                                               (RunStep.eval_var B σ "history.outward" ?_)
                                               (RunStep.eval_lit B ((1:Nat)) σ h1) hcase)
                                             (RunStep.assign B σ "history.edge" c16 c11
                                               (RunStep.eval_add B σ (Expr.mul (Expr.var "history.root") (Expr.var "metric.n"))
                                                 (Expr.var "history.vertex") c10 (Env.vars σ "history.vertex")
                                                 (RunStep.eval_mul B σ (Expr.var "history.root") (Expr.var "metric.n") (Env.vars σ "history.root")
                                                   (Env.vars σ "metric.n")
                                                   (RunStep.eval_var B σ "history.root"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   (RunStep.eval_var B σ "metric.n"
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   ?_)
                                                 (RunStep.eval_var B σ "history.vertex"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ?_)))
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         ?_))
                                   fun (hcase:c1) =>
                                   @Exists.intro Env c8 c23
                                     (@And.intro (Run B address σ c23 ((10:Nat))) (c7 c23)
                                       (RunStep.mono B address σ c23 (c15 c24) ((10:Nat))
                                         (RunStep.ite_false B c14 c18 c20 σ c23 c24
                                           (RunStep.cond_eq_false B σ (Expr.var "history.outward")
                                             (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                             ((1:Nat))
                                             (RunStep.eval_var B σ "history.outward" ?_)
                                             (RunStep.eval_lit B ((1:Nat)) σ h1) hcase)
                                           (RunStep.assign B σ "history.edge" c19 c22
                                             (RunStep.eval_add B σ (Expr.mul (Expr.var "history.vertex") (Expr.var "metric.n"))
                                               (Expr.var "history.root") c21 (Env.vars σ "history.root")
                                               (RunStep.eval_mul B σ (Expr.var "history.vertex") (Expr.var "metric.n")
                                                 (Env.vars σ "history.vertex") (Env.vars σ "metric.n")
                                                 (RunStep.eval_var B σ "history.vertex"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 (RunStep.eval_var B σ "metric.n"
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ?_)
                                               (RunStep.eval_var B σ "history.root"
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ?_)))
                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                       ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *)) <;> simp_all [pair,edge_value] <;> omega

theorem flag_spec (B:ℕ) (a b:ℚ≥0) (h1:1 < B):
    Spec B (fun σ => σ.vars "cmp.le"=(if (a:ℚ)≤ (b:ℚ) then 1 else 0)) flag
      (fun _ τ => τ.vars "find.ok"=(if b < a then 1 else 0)) 6:=by
  intro σ hσ
  by_cases h:(a:ℚ)≤ (b:ℚ) <;> (expose_names;
                                       (refine
                                           let c0:Prop:= @Eq Nat (Env.vars σ "cmp.le") ((0:Nat));
                                           let c1:Prop:=Not c0;
                                           let c2:Nat:=
                                             @ite Nat
                                               (@LT.lt NNRat
                                                 (@Preorder.toLT NNRat
                                                   (@PartialOrder.toPreorder NNRat
                                                     (@SemilatticeInf.toPartialOrder NNRat
                                                       (@Lattice.toSemilatticeInf NNRat
                                                         (@DistribLattice.toLattice NNRat (@instDistribLatticeOfLinearOrder NNRat instLinearOrderNNRat))))))
                                                 b a)
                                               (@LinearOrder.toDecidableLT NNRat instLinearOrderNNRat b a)
                                               ((1:Nat))
                                               ((0:Nat));
                                           let c3:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "find.ok") c2) σ;
                                           let c4:Env→ Prop:=fun (σ':Env) =>
                                             And (Run B flag σ σ' ((6:Nat))) (c3 σ');
                                           let c5:Env:=Env.setVar σ "find.ok" ((1:Nat));
                                           let c6:Nat→ Nat→ Nat:=Nat.add;
                                           let c7:Nat→ Nat:=c6 ((1:Nat));
                                           let c8:Cond:=Cond.eq (Expr.var "cmp.le") (Expr.lit ((0:Nat)));
                                           let c9:Nat→ Nat:=c6 (c7 (Cond.size c8));
                                           let c10:Nat:=c7 (Expr.size (Expr.lit ((1:Nat))));
                                           let c11:Com:=Com.assign "find.ok" (Expr.lit ((1:Nat)));
                                           let c12:Com:=Com.assign "find.ok" (Expr.lit ((0:Nat)));
                                           let c13:Env:=Env.setVar σ "find.ok" ((0:Nat));
                                           let c14:Nat:=c7 (Expr.size (Expr.lit ((0:Nat))));
                                           @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0)
                                             (fun (hcase:c0) =>
                                               @Exists.intro Env c4 c5
                                                 (@And.intro (Run B flag σ c5 ((6:Nat))) (c3 c5)
                                                   (RunStep.mono B flag σ c5 (c9 c10) ((6:Nat))
                                                     (RunStep.ite_true B c8 c11 c12 σ c5 c10
                                                       (RunStep.cond_eq_true B σ (Expr.var "cmp.le")
                                                         (Expr.lit ((0:Nat))) (Env.vars σ "cmp.le")
                                                         ((0:Nat))
                                                         (RunStep.eval_var B σ "cmp.le" ?_)
                                                         (RunStep.eval_lit B ((0:Nat)) σ
                                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                         hcase)
                                                       (RunStep.assign B σ "find.ok" (Expr.lit ((1:Nat)))
                                                         ((1:Nat))
                                                         (RunStep.eval_lit B ((1:Nat)) σ h1)))
                                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                   ?_))
                                             fun (hcase:c1) =>
                                             @Exists.intro Env c4 c13
                                               (@And.intro (Run B flag σ c13 ((6:Nat))) (c3 c13)
                                                 (RunStep.mono B flag σ c13 (c9 c14) ((6:Nat))
                                                   (RunStep.ite_false B c8 c11 c12 σ c13 c14
                                                     (RunStep.cond_eq_false B σ (Expr.var "cmp.le")
                                                       (Expr.lit ((0:Nat))) (Env.vars σ "cmp.le")
                                                       ((0:Nat))
                                                       (RunStep.eval_var B σ "cmp.le" ?_)
                                                       (RunStep.eval_lit B ((0:Nat)) σ
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                       hcase)
                                                     (RunStep.assign B σ "find.ok" (Expr.lit ((0:Nat)))
                                                       ((0:Nat))
                                                       (RunStep.eval_lit B ((0:Nat)) σ
                                                         ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                                   ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                                 ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *)) <;> simp_all <;> omega

theorem command_spec (B M:ℕ) {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (i:ℕ) (hi:i < history.length) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hn:n < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ))
    (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ)):
    Spec B (fun σ => Context d history v σ∧ σ.vars "find.i"=i) command
      (fun _ τ => Context d history v τ∧
        τ.vars "find.ok"=(if d (pair history[i] v).1 (pair history[i] v).2 < history[i].radius then 1 else 0)) 120:=by
  have hMB:M < B:=by nlinarith
  let e:=history[i]
  let uv:=pair e v
  have her:=hr e (List.getElem_mem hi)
  have hed:=hd uv.1 uv.2
  have hdist:(MetricMatrix.values d)[(edgeIndex n uv).val]'(by simpa using (edgeIndex n uv).isLt)=d uv.1 uv.2:=MetricMatrix.value_at d uv.1 uv.2
  rintro σ ⟨hσ,hiσ⟩
  obtain ⟨σ1,r1,p1⟩:=RamHistoryEntry.command_spec B history i hi h4 hlen hn
    ((num_bound her).trans_lt hMB) ((den_bound her).trans_lt hMB) σ ⟨hσ.2.2.2.2,hiσ⟩
  have h1:=frame r1 hσ (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩:=address_spec B e v (by omega) hn (by omega) σ1 ⟨h1.1,h1.2.2.1,p1⟩
  have h2:=frame r2 h1 (by decide) (by decide)
  obtain ⟨σ3,r3,p3⟩:=RamArrayScalar.command_spec B "metric.old" "history.edge" "history.distance"
    (MetricMatrix.values d) (edgeIndex n uv).val (by simpa using (edgeIndex n uv).isLt) (by omega)
    (by have:=(edgeIndex n uv).isLt; omega)
    (by rw [hdist]; exact (num_bound hed).trans_lt hMB)
    (by rw [hdist]; exact (den_bound hed).trans_lt hMB) (by decide) (by decide) σ2 ⟨h2.2.2.2.1,p2⟩
  have hrad:=RamRoundingConstants.storedFrame (r2.seq r3) p1.2.1 (by decide) (by decide)
  obtain ⟨σ4,r4,p4⟩:=RamScalarComparison.command_spec B M e.radius (d uv.1 uv.2) "history.radius" "history.distance"
    hB (num_bound her) (den_bound her) (num_bound hed) (den_bound hed) (by decide) (by decide) (by decide) σ3
    ⟨hrad,by simpa only [hdist] using p3⟩
  obtain ⟨τ,r5,p5⟩:=flag_spec B e.radius (d uv.1 uv.2) (by omega) σ4 p4
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr,frame rr hσ (by decide) (by decide),p5⟩

end Lax455465Proofs.RamHistoryTest

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamHistoryLabel
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding HistoryPotentialData RamHistoryTest
open scoped NNRat

def cost (m:ℕ):ℕ:=140*m+52

theorem position_spec (B m j:ℕ) (outward:Bool) (h2:2 < B) (hj:j < m) (hm:2*m < B):
    Spec B (fun σ => σ.vars "find.count"=m∧ σ.vars "find.result"=j∧
      σ.vars "history.outward"=(if outward then 1 else 0)) position
      (fun _ τ => τ.vars "rat.n"=(if outward then 2*m-j else j)) 10:=by
  rintro σ ⟨hmσ,hjσ,hoσ⟩
  have hmB:m < B:=by omega
  have hjB:j < B:=by omega
  have hout:2*m-j < B:=by omega
  cases outward <;> (first
                     | (expose_names;
                         (refine
                             let c0:Prop:= @Eq Nat (Env.vars σ "history.outward") ((1:Nat));
                             let c1:Prop:=Not c0;
                             let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat);
                             let c3:Nat→ Nat:=
                               Nat.mul ((2:Nat));
                             let c4:Nat:= @ite Nat (@Eq Bool false true) (instDecidableEqBool false true) (c2 (c3 m) j) j;
                             let c5:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "rat.n") c4) σ;
                             let c6:Env→ Prop:=fun (σ':Env) =>
                               And (Run B position σ σ' ((10:Nat))) (c5 σ');
                             let c7:Nat:=c3 (Env.vars σ "find.count");
                             let c8:Nat:=c2 c7 (Env.vars σ "find.result");
                             let c9:Env:=Env.setVar σ "rat.n" c8;
                             let c10:Nat→ Nat→ Nat:=Nat.add;
                             let c11:Nat→ Nat:=c10 ((1:Nat));
                             let c12:Cond:=
                               Cond.eq (Expr.var "history.outward") (Expr.lit ((1:Nat)));
                             let c13:Nat→ Nat:=c10 (c11 (Cond.size c12));
                             let c14:Expr:=
                               Expr.mul (Expr.lit ((2:Nat))) (Expr.var "find.count");
                             let c15:Expr:=Expr.sub c14 (Expr.var "find.result");
                             let c16:Nat:=c11 (Expr.size c15);
                             let c17:Com:=Com.assign "rat.n" c15;
                             let c18:Nat:=c11 (Expr.size (Expr.var "find.result"));
                             @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c6) (Classical.em c0)
                               (fun (hcase:c0) =>
                                 @Exists.intro Env c6 c9
                                   (@And.intro (Run B position σ c9 ((10:Nat))) (c5 c9)
                                     (RunStep.mono B position σ c9 (c13 c16) ((10:Nat))
                                       (RunStep.ite_true B c12 c17 (Com.assign "rat.n" (Expr.var "find.result")) σ c9 c16
                                         (RunStep.cond_eq_true B σ (Expr.var "history.outward")
                                           (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                           ((1:Nat))
                                           (RunStep.eval_var B σ "history.outward" ?_)
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           hcase)
                                         (RunStep.assign B σ "rat.n" c15 c8
                                           (RunStep.eval_sub B σ c14 (Expr.var "find.result") c7 (Env.vars σ "find.result")
                                             (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                               (Expr.var "find.count") ((2:Nat))
                                               (Env.vars σ "find.count")
                                               (RunStep.eval_lit B ((2:Nat)) σ h2)
                                               (RunStep.eval_var B σ "find.count"
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                             (RunStep.eval_var B σ "find.result"
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ?_))
                               fun (hcase:c1) =>
                               @Exists.intro Env c6 (Env.setVar σ "rat.n" (Env.vars σ "find.result"))
                                 (@And.intro
                                   (Run B position σ (Env.setVar σ "rat.n" (Env.vars σ "find.result"))
                                     ((10:Nat)))
                                   (c5 (Env.setVar σ "rat.n" (Env.vars σ "find.result")))
                                   (RunStep.mono B position σ (Env.setVar σ "rat.n" (Env.vars σ "find.result")) (c13 c18)
                                     ((10:Nat))
                                     (RunStep.ite_false B c12 c17 (Com.assign "rat.n" (Expr.var "find.result")) σ
                                       (Env.setVar σ "rat.n" (Env.vars σ "find.result")) c18
                                       (RunStep.cond_eq_false B σ (Expr.var "history.outward")
                                         (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                         ((1:Nat))
                                         (RunStep.eval_var B σ "history.outward" ?_)
                                         (RunStep.eval_lit B ((1:Nat)) σ
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         hcase)
                                       (RunStep.assign B σ "rat.n" (Expr.var "find.result") (Env.vars σ "find.result")
                                         (RunStep.eval_var B σ "find.result"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                     | (expose_names;
                         (refine
                             let c0:Prop:= @Eq Nat (Env.vars σ "history.outward") ((1:Nat));
                             let c1:Prop:=Not c0;
                             let c2:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat);
                             let c3:Nat→ Nat:=
                               Nat.mul ((2:Nat));
                             let c4:Nat:= @ite Nat (@Eq Bool true true) (instDecidableEqBool true true) (c2 (c3 m) j) j;
                             let c5:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "rat.n") c4) σ;
                             let c6:Env→ Prop:=fun (σ':Env) =>
                               And (Run B position σ σ' ((10:Nat))) (c5 σ');
                             let c7:Nat:=c3 (Env.vars σ "find.count");
                             let c8:Nat:=c2 c7 (Env.vars σ "find.result");
                             let c9:Env:=Env.setVar σ "rat.n" c8;
                             let c10:Nat→ Nat→ Nat:=Nat.add;
                             let c11:Nat→ Nat:=c10 ((1:Nat));
                             let c12:Cond:=
                               Cond.eq (Expr.var "history.outward") (Expr.lit ((1:Nat)));
                             let c13:Nat→ Nat:=c10 (c11 (Cond.size c12));
                             let c14:Expr:=
                               Expr.mul (Expr.lit ((2:Nat))) (Expr.var "find.count");
                             let c15:Expr:=Expr.sub c14 (Expr.var "find.result");
                             let c16:Nat:=c11 (Expr.size c15);
                             let c17:Com:=Com.assign "rat.n" c15;
                             let c18:Nat:=c11 (Expr.size (Expr.var "find.result"));
                             @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c6) (Classical.em c0)
                               (fun (hcase:c0) =>
                                 @Exists.intro Env c6 c9
                                   (@And.intro (Run B position σ c9 ((10:Nat))) (c5 c9)
                                     (RunStep.mono B position σ c9 (c13 c16) ((10:Nat))
                                       (RunStep.ite_true B c12 c17 (Com.assign "rat.n" (Expr.var "find.result")) σ c9 c16
                                         (RunStep.cond_eq_true B σ (Expr.var "history.outward")
                                           (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                           ((1:Nat))
                                           (RunStep.eval_var B σ "history.outward" ?_)
                                           (RunStep.eval_lit B ((1:Nat)) σ
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                           hcase)
                                         (RunStep.assign B σ "rat.n" c15 c8
                                           (RunStep.eval_sub B σ c14 (Expr.var "find.result") c7 (Env.vars σ "find.result")
                                             (RunStep.eval_mul B σ (Expr.lit ((2:Nat)))
                                               (Expr.var "find.count") ((2:Nat))
                                               (Env.vars σ "find.count")
                                               (RunStep.eval_lit B ((2:Nat)) σ h2)
                                               (RunStep.eval_var B σ "find.count"
                                                 ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                             (RunStep.eval_var B σ "find.result"
                                               ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                             ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                       ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                     ?_))
                               fun (hcase:c1) =>
                               @Exists.intro Env c6 (Env.setVar σ "rat.n" (Env.vars σ "find.result"))
                                 (@And.intro
                                   (Run B position σ (Env.setVar σ "rat.n" (Env.vars σ "find.result"))
                                     ((10:Nat)))
                                   (c5 (Env.setVar σ "rat.n" (Env.vars σ "find.result")))
                                   (RunStep.mono B position σ (Env.setVar σ "rat.n" (Env.vars σ "find.result")) (c13 c18)
                                     ((10:Nat))
                                     (RunStep.ite_false B c12 c17 (Com.assign "rat.n" (Expr.var "find.result")) σ
                                       (Env.setVar σ "rat.n" (Env.vars σ "find.result")) c18
                                       (RunStep.cond_eq_false B σ (Expr.var "history.outward")
                                         (Expr.lit ((1:Nat))) (Env.vars σ "history.outward")
                                         ((1:Nat))
                                         (RunStep.eval_var B σ "history.outward" ?_)
                                         (RunStep.eval_lit B ((1:Nat)) σ
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                         hcase)
                                       (RunStep.assign B σ "rat.n" (Expr.var "find.result") (Env.vars σ "find.result")
                                         (RunStep.eval_var B σ "find.result"
                                           ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))))
                                     ((by (try dsimp +zetaDelta at *); first | omega | (simp <;> omega) | assumption | (simp_all <;> omega))))
                                   ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *))
                    ) <;> simp_all <;> omega

theorem finish_spec (B a:ℕ) (h1:1 < B):
    Spec B (fun σ => σ.vars "rat.n"=a) finish (fun _ τ => RamRational.FractionOutput (a:ℚ) τ) 4:=by
  intro σ hσ
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => RamRational.FractionOutput (@Nat.cast Rat Rat.instNatCast a) τ) σ; let c1:Env:=Env.setVar σ "rat.d" ((1:Nat)); let c2:Env:=Env.setVar c1 "rat.s" ((0:Nat)); let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 ((1:Nat)); let c5:Nat:=c4 (Expr.size (Expr.lit ((1:Nat)))); let c6:Nat:=c4 (Expr.size (Expr.lit ((0:Nat)))); @Exists.intro Env (fun (σ':Env) => And (Run B finish σ σ' ((4:Nat))) (c0 σ')) c2 (@And.intro (Run B finish σ c2 ((4:Nat))) (c0 c2) (RunStep.mono B finish σ c2 (c3 c5 c6) ((4:Nat)) (RunStep.seq B (Com.assign "rat.d" (Expr.lit ((1:Nat)))) (Com.assign "rat.s" (Expr.lit ((0:Nat)))) σ c1 c2 c5 c6 (RunStep.assign B σ "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) σ h1)) (RunStep.assign B c1 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c1 (?nAX_g7184_0_0_0)))) (?nAX_g7184_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g7184_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g7184_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [RamRational.FractionOutput,RamRational.fractionValue]

theorem choose_spec (B M:ℕ) {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (hMB:M < B) (h4:4 < B) (hlen:4*history.length < B) (hn:n < B)
    (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ)):
    Spec B (fun σ => Context d history v σ∧ RamFind.Matches (RamFind.first (predicate d history v) history.length) σ)
      choose (fun _ τ => Context d history v τ∧ τ.vars "rat.n"=(values d history v).num) 38:=by
  rintro σ ⟨hσ,hmatch⟩
  cases he:RamFind.first (predicate d history v) history.length with
  | none =>
    have hf:σ.vars "find.found"=0:=by simpa only [he,RamFind.Matches] using hmatch
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hf ▸ (by omega:0 < B))) (evalB_lit (by omega)),hf]
      rfl
    have ra:Run B (.assign "rat.n" (.var "find.count")) σ (σ.setVar "rat.n" history.length) 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hσ.2.1.symm,hσ.2.1 ▸ (by omega:history.length < B)⟩)
    have rr:=Run.ite_false (c:=.seq (.assign "find.i" (.var "find.result")) (.seq RamHistoryEntry.command position)) hc ra
    refine ⟨_,rr.mono (by decide),frame rr hσ (by decide) (by decide),?_⟩
    simp [value_none d history v he]
  | some j =>
    have hj:=(RamFind.first_some _ _ _ he).1
    have hm:σ.vars "find.found"=1∧ σ.vars "find.result"=j:=by simpa only [he,RamFind.Matches] using hmatch
    have hjB:j < B:=by omega
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hm.1 ▸ (by omega:1 < B))) (evalB_lit (by omega)),hm.1]
      rfl
    let σ1:=σ.setVar "find.i" j
    have r1:Run B (.assign "find.i" (.var "find.result")) σ σ1 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hm.2.symm,hm.2 ▸ hjB⟩)
    have h1:=frame r1 hσ (by decide) (by decide)
    have hrj:=hr history[j] (List.getElem_mem hj)
    obtain ⟨σ2,r2,p2⟩:=RamHistoryEntry.command_spec B history j hj h4 hlen hn
      ((num_bound hrj).trans_lt hMB) ((den_bound hrj).trans_lt hMB) σ1 ⟨h1.2.2.2.2,by simp [σ1]⟩
    have h2:=frame r2 h1 (by decide) (by decide)
    have hj2:σ2.vars "find.result"=j:=((r1.seq r2).frame_var _ (by decide)).trans hm.2
    obtain ⟨τ,r3,p3⟩:=position_spec B history.length j history[j].outward (by omega) hj (by omega) σ2 ⟨h2.2.1,hj2,p2.2.2⟩
    have rr:=Run.ite_true (d:=.assign "rat.n" (.var "find.count")) hc (r1.seq (r2.seq r3))
    refine ⟨τ,rr,frame rr hσ (by decide) (by decide),?_⟩
    rw [value_some d history v j he hj]
    change τ.vars "rat.n"=(if history[j].outward then 2*history.length-j else j)
    exact p3

theorem command_spec (B M:ℕ) {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (v:Fin n)
    (hB:2*M^2+3 < B) (h4:4 < B) (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hn:n < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ)) (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ)):
    Spec B (Context d history v) command
      (fun _ τ => Context d history v τ∧ RamRational.FractionOutput (values d history v:ℚ) τ)
      (cost history.length):=by
  have hMB:M < B:=by nlinarith
  have hscan:=RamFind.command_spec B history.length 120 (Context d history v) (predicate d history v)
    RamHistoryTest.command (by omega) (by omega) (fun _ h => h.2.1)
    (fun σ k name h hname => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl | rfl | rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      obtain ⟨τ,rr,pr⟩:=RamHistoryTest.command_spec B M d history v i hi hB h4 hlen hindex hn hd hr σ hσ
      refine ⟨τ,rr,pr.1,?_⟩
      cases he:history[i].outward <;>
        simpa only [predicate_at d history v i hi,contains,pair,he,Bool.false_eq_true,if_false,if_true,
          decide_eq_true_eq] using pr.2) (by decide)
  intro σ hσ
  obtain ⟨σ1,r1,p1⟩:=hscan σ hσ
  obtain ⟨σ2,r2,p2⟩:=choose_spec B M d history v hMB h4 hlen hn hr σ1 p1
  obtain ⟨τ,r3,p3⟩:=finish_spec B (values d history v).num (by omega) σ2 p2.2
  have rr:=r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [cost]),frame rr hσ (by decide) (by decide),?_⟩
  simpa [values] using p3

end Lax455465Proofs.RamHistoryLabel

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamHistoryPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding HistoryPotentialData
open scoped NNRat

def Context {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n)) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "find.count"=history.length∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ∧ Prefix (words history) "region.history" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {d:MetricMatrix.Matrix n} {history:List (Entry n)} (h:Context d history σ)
    (hx:∀ x∈["metric.n","find.count"],x∉cmd.wvars)
    (ha:∀ a∈["metric.old","region.history"],a∉cmd.warrs):Context d history τ:=by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "find.count" (hx _ (by simp)),
    rr.frame_arr "metric.old" (ha _ (by simp)),rr.frame_arr "region.history" (ha _ (by simp))] using h

theorem vector_spec (B M:ℕ) {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n))
    (hM:1≤ M) (hm:2*history.length≤ M) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ)) (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ)):
    Spec B (fun σ => Context d history σ∧ 2*n < (σ.arrs "cut.potential").length) vector
      (fun _ τ => Context d history τ∧ Prefix (RamUnsignedBuffer.encode (List.ofFn (values d history))) "cut.potential" τ)
      ((140*history.length+74)*n+8):=by
  let qs:=List.ofFn (values d history)
  have hMB:M < B:=by nlinarith
  have hheight (i:ℕ) (hi:i < qs.length):LpInputSize.Height M (qs[i]:ℚ):=by
    simp only [qs,List.getElem_ofFn]
    exact value_height d history M hM hm _
  have hloop:=RamUnsignedVector.command_spec B (RamHistoryLabel.cost history.length) (Context d history)
    "history.vertex" "metric.n" "cut.potential" "history.potentialPos" qs [] RamHistoryLabel.command (by omega)
    (by simpa only [qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hvertex)
    (fun i hi => (num_bound (hheight i hi)).trans_lt hMB)
    (fun i hi => (den_bound (hheight i hi)).trans_lt hMB)
    (fun σ h => by simpa only [qs,List.length_ofFn] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi σ hσ => by
      have hi':i < n:=by simpa only [qs,List.length_ofFn] using hi
      obtain ⟨τ,rr,pr⟩:=RamHistoryLabel.command_spec B M d history ⟨i,hi'⟩ hB h4 hlen hindex (by omega) hd hr σ
        ⟨hσ.1.1,hσ.1.2.1,hσ.2,hσ.1.2.2⟩
      exact ⟨τ,rr,⟨pr.1.1,pr.1.2.1,pr.1.2.2.2⟩,by simpa only [qs,List.getElem_ofFn] using pr.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν:=σ.setVar "history.potentialPos" 0
  have rz:Run B (.assign "history.potentialPos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  have hν:=frame rz hσ (by decide) (by decide)
  obtain ⟨τ,rl,pl⟩:=hloop ν ⟨hν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,qs,List.length_nil,List.length_ofFn,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rz.seq rl).mono (by simp only [qs,List.length_ofFn,RamHistoryLabel.cost,Nat.add_assoc,Nat.reduceAdd]; omega),
    pl.1,by simpa only [List.nil_append,qs] using pl.2.1⟩

theorem command_spec (B M:ℕ) {n:ℕ} (d:MetricMatrix.Matrix n) (history:List (Entry n))
    (hM:1≤ M) (hm:2*history.length≤ M) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ)) (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ)):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "history.pos"=4*history.length∧
      Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ∧ Prefix (words history) "region.history" σ∧
      2*n < (σ.arrs "cut.potential").length) command
      (fun _ τ => Context d history τ∧ τ.vars "cut.reversed"=1∧ τ.vars "cut.count"=n∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (values d history))) "cut.potential" τ) (cost n history.length):=by
  rintro σ ⟨hn,hpos,hdσ,hhσ,hroom⟩
  let ν:=σ.setVar "find.count" history.length
  have r1:Run B (.assign "find.count" (.div (.var "history.pos") (.lit 4))) σ ν 4:=by
    have he:(Expr.div (.var "history.pos") (.lit 4)).evalB B σ=some history.length:=by
      simpa [Bop.apply] using evalB_bin (op:=.div)
        (show (Expr.var "history.pos").evalB B σ=some (4*history.length) from by
          rw [evalB_var_iff]; exact ⟨hpos.symm,hpos ▸ hlen⟩) (evalB_lit h4) (by dsimp [Bop.apply]; omega)
    exact Run.assign he
  have hν:Context d history ν:= ⟨by simpa [ν] using hn,by simp [ν],hdσ,hhσ⟩
  obtain ⟨μ,r2,p2⟩:=vector_spec B M d history hM hm hB h4 hlen hindex hvertex hd hr ν ⟨hν,hroom⟩
  let ξ:=μ.setVar "cut.reversed" 1
  let τ:=ξ.setVar "cut.count" n
  have r3:Run B (.assign "cut.reversed" (.lit 1)) μ ξ 2:=Run.assign (evalB_lit (by omega))
  have r4:Run B (.assign "cut.count" (.var "metric.n")) ξ τ 2:=Run.assign (by
    rw [evalB_var_iff]
    exact ⟨by simpa only [ξ,vars_setVar,String.reduceEq,if_false] using p2.1.1.symm,
      by simp only [ξ,vars_setVar,String.reduceEq,if_false,p2.1.1]; omega⟩)
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp [cost]; omega),
    frame (r3.seq r4) p2.1 (by decide) (by decide),by simp [τ,ξ],by simp [τ],p2.2⟩

end Lax455465Proofs.RamHistoryPotential

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamHistoryCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext RamRegionRecord
open Lax455465.RationalEncoding HistoryPotentialData
open scoped BigOperators NNRat

structure Input {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (history:List (Entry n)) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  n2Value:σ.vars "metric.n2"=n*n
  historyPosition:σ.vars "history.pos"=4*history.length
  metric:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ
  records:Prefix (words history) "region.history" σ
  weights:Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities:Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  total:Stored "round.total" (RamRoundingInit.total I.weight) σ
  potentialRoom:2*n < (σ.arrs "cut.potential").length
  maskRoom:2*n < (σ.arrs "cut.flags").length
  crossingRoom:2*(n*n) < (σ.arrs "cut.crossing").length

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (history:List (Entry n))
    (hM:1≤ M) (hm:2*history.length≤ M) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ)) (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ))
    (hcuts:∀ S,CutScoreHeight.Bounds I S M) (U:ℚ)
    (hgood:∃ S∈CutSweeps.candidates (ThresholdCutData.potential true (values d history)),
      CutSweeps.admissibleQ I S∧ CutSweeps.ratioQ I S≤ U):
    Spec B (Input I d history) command
      (fun _ τ => ∃ S:Finset (Fin n),CutSweeps.admissibleQ I S∧ CutSweeps.ratioQ I S≤ U∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n history.length M):=by
  obtain ⟨S,hS,hvalid,hratio⟩:=hgood
  obtain ⟨j,hj,hjn,hjvalid,hjratio⟩:=RamPotentialSweep.selected_le I (values d history) true S hS hvalid
  rintro σ hσ
  obtain ⟨ν,rp,pp⟩:=RamHistoryPotential.command_spec B M d history hM hm hB h4 hlen hindex hvertex hd hr σ
    ⟨hσ.nValue,hσ.historyPosition,hσ.metric,hσ.records,hσ.potentialRoom⟩
  have hinput:RamThresholdCandidate.Input I (values d history) true ν:=by
    exact ⟨pp.1.1,(rp.frame_var _ (by decide)).trans hσ.n2Value,pp.2.2.1,pp.2.1,
      RamRoundingConstants.storedFrame rp hσ.total (by decide) (by decide),
      by simpa only [Prefix,rp.frame_arr "flow.weights" (by decide)] using hσ.weights,
      by simpa only [Prefix,rp.frame_arr "flow.capacities" (by decide)] using hσ.capacities,
      pp.2.2.2,
      by rw [RamFrames.run_array_length rp]; exact hσ.maskRoom,
      by rw [RamFrames.run_array_length rp]; exact hσ.crossingRoom⟩
  obtain ⟨τ,rs,ps⟩:=RamPotentialSweep.command_spec B M I (values d history) true hM hB hindex hvertex
    (value_height d history M hM hm) (fun i hi => hcuts _) ν hinput
  have hmask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags (ThresholdCutData.candidate true (values d history) j))) "cut.flags" τ:=by
    simpa only [hj,RamPotentialSweep.Selected] using ps.2.2
  exact ⟨τ,rp.seq rs,ThresholdCutData.candidate true (values d history) j,hjvalid,hjratio.trans hratio,hmask⟩

theorem history_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n) (history:List (Entry n))
    (p:ℕ) (hM:1≤ M) (hm:2*history.length≤ M) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*history.length < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ)) (hr:∀ e∈history,LpInputSize.Height M (e.radius:ℚ))
    (hcuts:∀ S,CutScoreHeight.Bounds I S M) (htotal:0 < LargeBallRounding.total I)
    (hp:0 < p) (hcount:history.length≤ p)
    (hvalid:RegionLoop.ValidHistory I (MetricMatrix.rational d)
      (RegionRounding.metricCost I (MetricMatrix.rational d)/p) (RegionRounding.radiusBudget I) p Finset.univ
      (history.map Entry.region)):
    Spec B (Input I d history) command
      (fun _ τ => ∃ S:Finset (Fin n),CutSweeps.admissibleQ I S∧
        CutSweeps.ratioQ I S≤ (288/5:ℚ)*(RegionBudget.steps p:ℚ)*RegionRounding.metricCost I (MetricMatrix.rational d)∧
        Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags S)) "cut.flags" τ) (cost n history.length M):=by
  let history':=history.map Entry.region
  let W:=RegionRounding.metricCost I (MetricMatrix.rational d)
  have hdelta:0 < RegionRounding.radiusBudget I:=by unfold RegionRounding.radiusBudget; positivity
  have hW:0≤ W:=RegionCharging.weight_nonnegative _ _ (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
  have hc:=HistoryCharging.total_charge I (MetricMatrix.rational d) (RegionRounding.radiusBudget I) p history' hp
    (by simpa only [history',List.length_map] using hcount) hdelta (fun _ _ => NNRat.coe_nonneg _) hvalid
  have heq:2*RegionSearch.slope (RegionBudget.steps p) (RegionRounding.radiusBudget I)*W =
      8*(RegionBudget.steps p:ℚ)*BalancedRegionCut.total I^2*W:=by
    unfold RegionSearch.slope RegionRounding.radiusBudget
    change 2*((RegionBudget.steps p:ℚ)/(1/(4*LargeBallRounding.total I^2)))*W =
      8*(RegionBudget.steps p:ℚ)*LargeBallRounding.total I^2*W
    field_simp [ne_of_gt htotal]
    ring
  change (∑ j:Fin history'.length,RegionOrdering.chargedBoundary (fun u v => (I.capacity u v:ℚ))
    (RegionHistory.index (MetricMatrix.rational d) history') (RegionHistory.orientation history') j)≤
      2*RegionSearch.slope (RegionBudget.steps p) (RegionRounding.radiusBudget I)*W at hc
  rw [heq] at hc
  obtain ⟨S,hS,hadm,hbound⟩:=BalancedRegionCut.round_ratio I (RegionHistory.index (MetricMatrix.rational d) history')
    (RegionHistory.orientation history') (RegionBudget.steps p) W htotal (Nat.cast_nonneg _) hW
    (RegionHistory.blocks_small I (MetricMatrix.rational d) _ _ _ history' hvalid htotal) hc
  exact command_spec B M I d history hM hm hB h4 hlen hindex hvertex hd hr hcuts _
    ⟨S,HistoryPotentialData.round_mem I d history S hS hadm,hadm,hbound⟩

end Lax455465Proofs.RamHistoryCut

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding RegionRuntimeState
open scoped BigOperators NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (d:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (s:State n)
    (hM:1≤ M) (hm:2*p≤ M) (hB:2*M^2+3 < B) (h4:4 < B)
    (hlen:4*p+4 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hd:∀ u w,LpInputSize.Height M (d u w:ℚ))
    (hr:∀ e∈s.history,LpInputSize.Height M (e.radius:ℚ))
    (hlargeBounds:∀ Tin Tout:Finset (Fin n),∀ hin:Tin.Nonempty,∀ hout:Tout.Nonempty,
      LargePotentialData.Bounds I d Tin Tout hin hout M)
    (hcuts:∀ S,CutScoreHeight.Bounds I S M) (htotal:0 < LargeBallRounding.total I)
    (hp:0 < p) (hdiag:∀ v,d v v=0)
    (hsep:1≤ LargeBallRounding.distanceSeparation I (MetricMatrix.rational d))
    (htri:∀ u v w,(d u w:ℚ)≤ (d u v:ℚ)+(d v w:ℚ))
    (hseed:(seed:ℚ)=RegionRounding.metricCost I (MetricMatrix.rational d)/p)
    (hdelta:(delta:ℚ)=RegionRounding.radiusBudget I)
    (hvalid:RegionRuntimeCorrespondence.ValidFinal I d seed delta p s):
    Spec B (fun σ => RamRegionInvariant.Fixed I d seed beta delta threshold p σ∧
      RamRegionState.View I d seed beta s σ∧ Stored "round.total" (RamRoundingInit.total I.weight) σ∧ Room n σ)
      command (fun _ τ => Output I d p τ) (cost n p M):=by
  rintro σ ⟨hσ,hview,htσ,hroom⟩
  cases hs:s.status with
  | running => simp only [RegionRuntimeCorrespondence.ValidFinal,hs] at hvalid
  | failed => simp only [RegionRuntimeCorrespondence.ValidFinal,hs] at hvalid
  | exhausted =>
    have hv:RegionLoop.ValidHistory I (MetricMatrix.rational d) seed delta p Finset.univ (s.history.map Entry.region)∧ s.history.length≤ p:=by
      simpa only [RegionRuntimeCorrespondence.ValidFinal,hs] using hvalid
    have hvw:σ.vars "region.phase"=2∧ Prefix (words s.history) "region.history" σ∧
      σ.vars "history.pos"=4*s.history.length∧
      Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask s.active))) "region.active" σ:=by
      simpa only [RamRegionState.View,hs] using hview
    have hc:(Cond.eq (.var "region.phase") (.lit 1)).evalB B σ=some false:=by
      rw [evalB_condEq (evalB_var (hvw.1 ▸ (by omega:2 < B))) (evalB_lit (by omega)),hvw.1]
      rfl
    obtain ⟨τ,rr,pr⟩:=RamHistoryCut.history_spec B M I d s.history p hM (by omega) hB h4 (by omega) hindex hvertex hd hr
      hcuts htotal hp hv.2 (by simpa only [hseed,hdelta] using hv.1) σ
      ⟨hσ.nValue,hσ.n2Value,hvw.2.2.1,hσ.lengthData,hvw.2.1,hσ.weightsData,hσ.capacityData,htσ,
        hroom.potential _ (by simp [RamLargePotential.scratchArrays]),hroom.mask,hroom.crossing⟩
    have hcost:RamHistoryCut.cost n s.history.length M≤ RamHistoryCut.cost n p M:=by
      dsimp [RamHistoryCut.cost,RamHistoryPotential.cost]
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right n (by omega)) 16) _
    exact ⟨τ,(Run.ite_false (c:=RamLargeCut.command) hc rr).mono (by dsimp [cost,Cond.size,Expr.size]; omega),pr⟩
  | large e =>
    have hv:RegionLoop.LargeGood I (MetricMatrix.rational d) delta e.region:=by
      simpa only [RegionRuntimeCorrespondence.ValidFinal,hs] using hvalid
    have hvw:σ.vars "region.phase"=1∧
      RamSmallRegion.Input (RadiusSearchData.atRadius (RegionExecutionData.query I d s.active e.root seed beta) e.radius)
        s.active s.history e.root σ:=by simpa only [RamRegionState.View,hs] using hview
    let Tin:=RamSmallRegion.ball (fun v => d v e.root) e.radius
    let Tout:=RamSmallRegion.ball (d e.root) e.radius
    have hin:Tin.Nonempty:= ⟨e.root,by simpa [Tin,RamSmallRegion.ball,RegionCharging.ball,hdiag,Entry.region] using hv.1⟩
    have hout:Tout.Nonempty:= ⟨e.root,by simpa [Tout,RamSmallRegion.ball,RegionCharging.ball,hdiag,Entry.region] using hv.1⟩
    have hiMask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tin)) "region.inMask" σ:=by
      simpa only [CutScoreData.vertexFlags,←RamSmallRegion.mask_eq,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,Tin] using hvw.2.masks.inMask
    have hoMask:Prefix (RamUnsignedBuffer.encode (CutScoreData.vertexFlags Tout)) "region.outMask" σ:=by
      simpa only [CutScoreData.vertexFlags,←RamSmallRegion.mask_eq,RadiusSearchData.atRadius,RegionExecutionData.query,RamRegionSetup.query,Tout] using hvw.2.masks.outMask
    have hrad:(e.radius:ℚ)≤ 1/(4*LargeBallRounding.total I^2):=by
      simpa only [Entry.region,hdelta,RegionRounding.radiusBudget] using hv.2.1
    have hc:(Cond.eq (.var "region.phase") (.lit 1)).evalB B σ=some true:=by
      rw [evalB_condEq (evalB_var (hvw.1 ▸ (by omega:1 < B))) (evalB_lit (by omega)),hvw.1]
      rfl
    obtain ⟨τ,rr,S,hadm,hratio,hmask⟩:=RamLargeCut.large_ball_spec B M I d Tin Tout hin hout e.root
      (hlargeBounds Tin Tout hin hout) hcuts hM hB hindex hvertex htotal hdiag hsep htri
      (fun v hv => ((Finset.mem_filter.mp hv).2.le).trans hrad)
      (fun v hv => ((Finset.mem_filter.mp hv).2.le).trans hrad)
      hv.2.2.2 hv.2.2.1 σ
      ⟨⟨hσ.nValue,hσ.weightsData,hσ.lengthData,hiMask,hoMask⟩,hσ.n2Value,htσ,hσ.capacityData,hroom.potential,hroom.mask,hroom.crossing⟩
    have hW:0≤ RegionRounding.metricCost I (MetricMatrix.rational d):=
      RegionCharging.weight_nonnegative _ _ (fun _ _ => NNRat.coe_nonneg _) (fun _ _ => NNRat.coe_nonneg _)
    have hk:(1:ℚ)≤ RegionBudget.steps p:=by exact_mod_cast RegionBudget.steps_pos p
    have hmul:=mul_le_mul_of_nonneg_right hk hW
    have hrat:CutSweeps.ratioQ I S≤ 6*RegionRounding.metricCost I (MetricMatrix.rational d):=hratio
    refine ⟨τ,(Run.ite_true (d:=RamHistoryCut.command) hc rr).mono (by dsimp [cost,Cond.size,Expr.size]; omega),S,hadm,?_,hmask⟩
    nlinarith

end Lax455465Proofs.RamRegionCut

end

theorem solution:∀ (B M:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n) (d:Lax455465Proofs.MetricMatrix.Matrix n)
  (seed beta delta threshold:NNRat) (p:Nat) (s:Lax455465Proofs.RegionRuntimeState.State n),
  Nat.le ((1:Nat)) M→
    Nat.le
        (Nat.mul ((2:Nat)) p)
        M→
      Nat.lt
          (Nat.add
            (Nat.mul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        Nat.lt ((4:Nat)) B→
          Nat.lt
              (Nat.add
                (Nat.mul
                  ((4:Nat)) p)
                ((4:Nat)))
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
                (∀ (u w:Fin n),Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (d u w)))→
                  (∀ (e:Lax455465Proofs.RamRegionRecord.Entry n),
                      @Membership.mem (Lax455465Proofs.RamRegionRecord.Entry n)
                          (List (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@List.instMembership (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@Lax455465Proofs.RegionRuntimeState.State.history n s) e→
                        Lax455465Proofs.LpInputSize.Height M
                          (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465Proofs.RamRegionRecord.Entry.radius n e)))→
                    (∀ (Tin Tout:Finset (Fin n)) (hin:@Finset.Nonempty (Fin n) Tin)
                        (hout:@Finset.Nonempty (Fin n) Tout),
                        @Lax455465Proofs.LargePotentialData.Bounds n I d Tin Tout hin hout M)→
                      (∀ (S:Finset (Fin n)), @Lax455465Proofs.CutScoreHeight.Bounds n I S M)→
                        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                            (@Lax455465Proofs.LargeBallRounding.total n I)→
                          Nat.lt ((0:Nat)) p→
                            (∀ (v:Fin n),
                                @Eq NNRat (d v v)
                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                    (@Zero.toOfNat0 NNRat
                                      (@MulZeroClass.toZero NNRat
                                        (@instMulZeroClassOfSemiring NNRat
                                          (@DivisionSemiring.toSemiring NNRat
                                            (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield)))))))→
                              @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                                    (@Lax455465Proofs.MetricMatrix.rational n d))→
                                (∀ (u v w:Fin n),
                                    @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u w))
                                      (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                        (@NNRat.cast Rat Rat.instNNRatCast (d u v))
                                        (@NNRat.cast Rat Rat.instNNRatCast (d v w))))→
                                  @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast seed)
                                      (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                        (@Lax455465Proofs.RegionRounding.metricCost n I
                                          (@Lax455465Proofs.MetricMatrix.rational n d))
                                        (@Nat.cast Rat Rat.instNatCast p))→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast delta)
                                        (@Lax455465Proofs.RegionRounding.radiusBudget n I)→
                                      @Lax455465Proofs.RegionRuntimeCorrespondence.ValidFinal n I d seed delta p s→
                                        Lax808846Proofs.Reasoning.Spec B
                                          (fun (σ:Lax808846Proofs.Imp.Env) =>
                                            And
                                              (@Lax455465Proofs.RamRegionInvariant.Fixed n I d seed beta delta threshold
                                                p σ)
                                              (And (@Lax455465Proofs.RamRegionState.View n I d seed beta s σ)
                                                (And
                                                  (Lax455465Proofs.RamUnsignedScalar.Stored "round.total"
                                                    (@Lax455465Proofs.RamRoundingInit.total n
                                                      (@Lax455465.RationalEncoding.RationalInstance.weight n I))
                                                    σ)
                                                  (Lax455465Proofs.RamRegionCut.Room n σ))))
                                          Lax455465Proofs.RamRegionCut.command
                                          (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                            @Lax455465Proofs.RamRegionCut.Output n I d p τ)
                                          (Lax455465Proofs.RamRegionCut.cost n p M):= @Lax455465Proofs.RamRegionCut.command_spec
