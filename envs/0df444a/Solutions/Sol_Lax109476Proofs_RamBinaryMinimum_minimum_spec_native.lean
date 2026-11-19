-- Prove2me | solution 1 for Lax109476Proofs.RamBinaryMinimum.minimum_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:54.904194+00:00
-- url     : https://prove2.me/submissions/a5dd831c-9950-48fe-b21c-af54ee8e748f

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRational_addFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRationalReconstruction_reconstruct_spec_native

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
namespace Lax109476Proofs.RamRationalReconstruction
end Lax109476Proofs.RamRationalReconstruction
theorem Lax109476Proofs.RamRationalReconstruction.reconstruct_spec:∀ (S N w D:Nat) (l u:Rat),
  @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) u→
    Lax109476Proofs.RationalArithmeticBounds.Height l
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          ((2:Nat)) S)→
      Lax109476Proofs.RationalArithmeticBounds.Height u
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) S)→
        LE.le
            (HAdd.hAdd (Lax109476Proofs.RamRationalReconstruction.depthBound S)
              ((1:Nat)))
            N→
          LE.le (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w→
            LT.lt D
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w)→
              Lax808846Proofs.Reasoning.Spec
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w)
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (Lax109476Proofs.RamRationalScalars.Value "recon.lo" l σ)
                    (And (Lax109476Proofs.RamRationalScalars.Value "recon.hi" u σ)
                      (And (@Eq Nat (σ.vars "recon.bound") D) (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N))))
                Lax109476Proofs.RamRationalReconstruction.reconstruct
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamReconstructionRecord.Output
                    (Lax109476Proofs.RationalReconstruction.reconstruct l u D) τ)
                (Lax109476Proofs.RamRationalReconstruction.instructionBound S):= @Lax109476Proofs.RamRationalReconstruction.reconstruct_spec_native

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

namespace Lax109476Proofs.RationalRounding

theorem grid_num_den_bound (k:ℤ) (D:ℕ) (hD:0 < D):
    ((k:ℚ) / D).num.natAbs≤ k.natAbs∧ ((k:ℚ) / D).den≤ D:=by
  obtain ⟨c,hnum,hden⟩:=Rat.exists_eq_mul_div_num_and_eq_mul_div_den k
    (d:=(D:ℤ)) (by exact_mod_cast ne_of_gt hD)
  have hc:c ≠ 0:=by
    intro h
    rw [h,zero_mul] at hden
    have hDn:(D:ℤ) ≠ 0:=by exact_mod_cast ne_of_gt hD
    exact hDn hden
  have hcpos:0 < c.natAbs:=Int.natAbs_pos.mpr hc
  have hnumAbs:k.natAbs=c.natAbs * ((k:ℚ) / D).num.natAbs:=by
    simpa only [Int.natAbs_mul,Int.cast_natCast] using congrArg Int.natAbs hnum
  have hdenAbs:D=c.natAbs * ((k:ℚ) / D).den:=by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,Int.cast_natCast] using
      congrArg Int.natAbs hden
  constructor
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).num.natAbs:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hnumAbs.symm
  · calc
      _≤ c.natAbs * ((k:ℚ) / D).den:=Nat.le_mul_of_pos_left _ hcpos
      _=_:=hdenAbs.symm

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

end Lax109476Proofs.DeterminantBounds

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

theorem size_le_self (a:ℕ):Nat.size a≤ a:=
  Nat.size_le.mpr (Nat.lt_two_pow_self (n:=a))

end Lax109476Proofs.RationalSizeBounds

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

theorem eval_add (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m + n < B):
    (Expr.bin .add e f).evalB B σ=some (m + n):=evalB_bin he hf h

theorem eval_mul (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m * n < B):
    (Expr.bin .mul e f).evalB B σ=some (m * n):=evalB_bin he hf h

theorem eval_div (B:ℕ) (σ:Env) (e f:Expr) (m n:ℕ)
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:m / n < B):
    (Expr.bin .div e f).evalB B σ=some (m / n):=evalB_bin he hf h

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

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

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

theorem height_add (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q + r) (2 * B * C):=by
  have hd:(q.den:ℤ) * r.den ≠ 0:=by positivity
  have he:q + r=((q.num * r.den + r.num * q.den:ℤ):ℚ) /
      ((q.den:ℤ) * r.den):=by
    conv_lhs => rw [← q.num_div_den, ← r.num_div_den]
    push_cast
    field_simp
  rw [he]
  obtain ⟨hn,hd'⟩:=integer_ratio_num_den_bound (q.num * r.den + r.num * q.den) _ hd
  simp only [Int.cast_mul,Int.cast_natCast] at hn hd'
  have hb:(q.num * r.den + r.num * q.den:ℤ).natAbs≤ 2 * B * C:=by
    calc
      _≤ (q.num * r.den:ℤ).natAbs + (r.num * q.den:ℤ).natAbs:=Int.natAbs_add_le _ _
      _=q.num.natAbs * r.den + r.num.natAbs * q.den:=by simp [Int.natAbs_mul]
      _≤ B * C + C * B:=Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _=_:=by ring
  refine ⟨hn.trans hb, ?_⟩
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at hd'
  exact hd'.trans ((Nat.mul_le_mul hq.2 hr.2).trans (by nlinarith))

theorem height_inv (q:ℚ) (B:ℕ) (hq:Height q B):Height q⁻¹ B:=by
  have hB:1≤ B:=le_trans q.den_pos hq.2
  by_cases hz:q=0
  · subst q
    simpa using height_mono 0 height_zero hB
  · have hnum:(q⁻¹).num.natAbs≤ q.den:=by
      rw [Rat.num_inv,Int.natAbs_mul]
      have hs:q.num.sign.natAbs≤ 1:=by
        have hsign:=Int.sign_trichotomy q.num
        rcases hsign with h | h | h <;> rw [h] <;> norm_num
      simpa using Nat.mul_le_mul_right q.den hs
    exact ⟨hnum.trans hq.2,by rw [Rat.den_inv_of_ne_zero hz]; exact hq.1⟩

theorem height_div (q r:ℚ) (B C:ℕ) (hq:Height q B) (hr:Height r C):
    Height (q / r) (B * C):=by
  simpa only [div_eq_mul_inv] using height_mul q r⁻¹ B C hq (height_inv r C hr)

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem addFraction_uniform_spec (B M s₁ n₁ d₁ s₂ n₂ d₂:ℕ)
    (hB:2 * M ^ 2 + 3 < B) (hs₁:s₁≤ 1) (hs₂:s₂≤ 1)
    (hn₁:n₁≤ M) (hd₁:d₁≤ M) (hn₂:n₂≤ M) (hd₂:d₂≤ M)
    (hd₁pos:0 < d₁) (hd₂pos:0 < d₂):
    Spec B (fractionInputs s₁ n₁ d₁ s₂ n₂ d₂) addFraction
      (fun _ τ => FractionOutput (fractionValue s₁ n₁ d₁ + fractionValue s₂ n₂ d₂) τ)
      (72 * M.size + 96):=by
  apply (addFraction_spec B M s₁ n₁ d₁ s₂ n₂ d₂ hB hs₁ hs₂ hn₁ hd₁ hn₂ hd₂
    hd₁pos hd₂pos).mono
  have hs:=size_mul_le d₁ d₂
  have h₁:=Nat.size_le_size hd₁
  have h₂:=Nat.size_le_size hd₂
  change 36 * (d₁ * d₂).size + _ ≤ _
  omega

end Lax109476Proofs.RamPrimitiveBounds

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

theorem add_spec (B M:ℕ) (q r:ℚ) (hB:2 * M ^ 2 + 3 < B)
    (hq:Height q M) (hr:Height r M):
    Spec B (fun σ => LeftValue q σ∧ RightValue r σ) addFraction
      (fun _ τ => FractionOutput (q + r) τ) (72 * M.size + 96):=by
  rintro σ ⟨⟨hqval,hqn,hqd,hqs⟩, ⟨hrval,hrn,hrd,hrs⟩⟩
  rw [hqn,hqd] at hqval
  rw [hrn,hrd] at hrval
  obtain ⟨τ,hrun,hτ⟩:=addFraction_uniform_spec B M (σ.vars "left.s") q.num.natAbs q.den
    (σ.vars "right.s") r.num.natAbs r.den hB hqs hrs hq.1 hq.2 hr.1 hr.2 q.den_pos r.den_pos
    σ ⟨rfl,hqn,hqd,rfl,hrn,hrd⟩
  exact ⟨τ,hrun,by simpa only [hqval,hrval] using hτ⟩

theorem resultToLeft_spec (B:ℕ) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (FractionOutput q) resultToLeft (fun _ τ => LeftValue q τ) 6:=by
  rintro σ ⟨hqval,hqn,hqd,hqs⟩
  have hsB:=hqs.trans_lt h1
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n"; let c1:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" c0; let c2:Nat:=Env.vars c1 "rat.d"; let c3:Env:=Env.setVar c1 "left.d" c2; let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.var "rat.s")); let c7:Nat:=c5 (Expr.size (Expr.var "rat.n")); let c8:Nat:=c5 (Expr.size (Expr.var "rat.d")); let c9:Nat:=c4 c7 c8; @Exists.intro Env (fun (σ':Env) => And (Run B resultToLeft σ σ' ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ σ')) c3 (@And.intro (Run B resultToLeft σ c3 ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ c3) (RunStep.mono B resultToLeft σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.var "rat.s")) (Com.seq (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d"))) σ (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c3 c6 c9 (RunStep.assign B σ "left.s" (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hsB)) (RunStep.seq B (Com.assign "left.n" (Expr.var "rat.n")) (Com.assign "left.d" (Expr.var "rat.d")) (Env.setVar σ "left.s" (Env.vars σ "rat.s")) c1 c3 c7 c8 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "left.n" (Expr.var "rat.n") c0 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "rat.s")) "rat.n" (?nAX_g3972_0_0_0))) (RunStep.assign B c1 "left.d" (Expr.var "rat.d") c2 (RunStep.eval_var B c1 "rat.d" (?nAX_g3972_0_0_1))))) (?nAX_g3972_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g3972_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g3972_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [LeftValue]

end Lax109476Proofs.RamFractionInterface

end

section

namespace Lax109476Proofs.RamRationalScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalArrays

theorem readLeft_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hname:RamCopy.Disjoint name "left"):
    Spec B (Value name q) (readLeft name) (fun _ τ => LeftValue q τ) 6:=by
  have hsn:name ++ ".n" ≠ "left.s" :=hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:name ++ ".d" ≠ "left.s" :=hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:name ++ ".d" ≠ "left.n" :=hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "left.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "left.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "left.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "left.n" c14; let c20:Com:=Com.assign "left.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (readLeft name) σ σ' ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ σ')) c9 (@And.intro (Run B (readLeft name) σ c9 ((6:Nat))) ((fun (x τ:Env) => LeftValue q τ) σ c9) (RunStep.mono B (readLeft name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "left.s" c12 c2 (RunStep.eval_var B σ c1 hs)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "left.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "left.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g4095_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4095_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,LeftValue]

theorem readRight_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hname:RamCopy.Disjoint name "right"):
    Spec B (Value name q) (readRight name) (fun _ τ => RightValue q τ) 6:=by
  have hsn:name ++ ".n" ≠ "right.s" :=hname ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:name ++ ".d" ≠ "right.s" :=hname ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:name ++ ".d" ≠ "right.n" :=hname ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c1:String:=c0 ".s"; let c2:Nat:=Env.vars σ c1; let c3:Env:=Env.setVar σ "right.s" c2; let c4:String:=c0 ".n"; let c5:Nat:=Env.vars c3 c4; let c6:Env:=Env.setVar c3 "right.n" c5; let c7:String:=c0 ".d"; let c8:Nat:=Env.vars c6 c7; let c9:Env:=Env.setVar c6 "right.d" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.var c1; let c13:Nat:=c11 (Expr.size c12); let c14:Expr:=Expr.var c4; let c15:Nat:=c11 (Expr.size c14); let c16:Expr:=Expr.var c7; let c17:Nat:=c11 (Expr.size c16); let c18:Nat:=c10 c15 c17; let c19:Com:=Com.assign "right.n" c14; let c20:Com:=Com.assign "right.d" c16; @Exists.intro Env (fun (σ':Env) => And (Run B (readRight name) σ σ' ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ σ')) c9 (@And.intro (Run B (readRight name) σ c9 ((6:Nat))) ((fun (x τ:Env) => RightValue q τ) σ c9) (RunStep.mono B (readRight name) σ c9 (c10 c13 c18) ((6:Nat)) (RunStep.seq B (Com.assign "right.s" c12) (Com.seq c19 c20) σ c3 c9 c13 c18 (RunStep.assign B σ "right.s" c12 c2 (RunStep.eval_var B σ c1 hs)) (RunStep.seq B c19 c20 c3 c6 c9 c15 c17 (RunStep.assign B c3 "right.n" c14 c5 (RunStep.eval_var B c3 c4 ?_)) (RunStep.assign B c6 "right.d" c16 c8 (RunStep.eval_var B c6 c7 ?_)))) (?nAX_g4096_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4096_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,RightValue]

theorem save_spec (B:ℕ) (name:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B)
    (hname:∀ s∈ [".s", ".n", ".d"], ∀ t∈ [".s", ".n", ".d"],name ++ s ≠ "rat" ++ t):
    Spec B (FractionOutput q) (save name) (fun _ τ => Value name q τ) 6:=by
  have hsn:name ++ ".s" ≠ "rat.n" :=hname ".s" (by simp) ".n" (by simp)
  have hsd:name ++ ".s" ≠ "rat.d" :=hname ".s" (by simp) ".d" (by simp)
  have hnd:name ++ ".n" ≠ "rat.d" :=hname ".n" (by simp) ".d" (by simp)
  have hsn':name ++ ".s" ≠ name ++ ".n" :=by simp
  have hsd':name ++ ".s" ≠ name ++ ".d" :=by simp
  have hnd':name ++ ".n" ≠ name ++ ".d" :=by simp
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Value name q τ) σ; let c1:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) name; let c2:String:=c1 ".s"; let c3:Env:=Env.setVar σ c2 (Env.vars σ "rat.s"); let c4:String:=c1 ".n"; let c5:Nat:=Env.vars c3 "rat.n"; let c6:Env:=Env.setVar c3 c4 c5; let c7:String:=c1 ".d"; let c8:Nat:=Env.vars c6 "rat.d"; let c9:Env:=Env.setVar c6 c7 c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Nat:=c11 (Expr.size (Expr.var "rat.s")); let c13:Nat:=c11 (Expr.size (Expr.var "rat.n")); let c14:Nat:=c11 (Expr.size (Expr.var "rat.d")); let c15:Nat:=c10 c13 c14; let c16:Com:=Com.assign c4 (Expr.var "rat.n"); let c17:Com:=Com.assign c7 (Expr.var "rat.d"); @Exists.intro Env (fun (σ':Env) => And (Run B (save name) σ σ' ((6:Nat))) (c0 σ')) c9 (@And.intro (Run B (save name) σ c9 ((6:Nat))) (c0 c9) (RunStep.mono B (save name) σ c9 (c10 c12 c15) ((6:Nat)) (RunStep.seq B (Com.assign c2 (Expr.var "rat.s")) (Com.seq c16 c17) σ c3 c9 c12 c15 (RunStep.assign B σ c2 (Expr.var "rat.s") (Env.vars σ "rat.s") (RunStep.eval_var B σ "rat.s" hs)) (RunStep.seq B c16 c17 c3 c6 c9 c13 c14 (RunStep.assign B c3 c4 (Expr.var "rat.n") c5 (RunStep.eval_var B c3 "rat.n" ?_)) (RunStep.assign B c6 c7 (Expr.var "rat.d") c8 (RunStep.eval_var B c6 "rat.d" ?_)))) (?nAX_g4097_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4097_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,FractionOutput,Ne.symm hsn,Ne.symm hsd,Ne.symm hnd,
    Ne.symm hsn',Ne.symm hsd',Ne.symm hnd']

end Lax109476Proofs.RamRationalScalars

end

section

namespace Lax109476Proofs.RamScalarFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem value_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (name:String) (q:ℚ) (h:Value name q σ)
    (hs:name ++ ".s" ∉ c.wvars) (hn:name ++ ".n" ∉ c.wvars)
    (hd:name ++ ".d" ∉ c.wvars):Value name q τ:=by
  simpa only [Value,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

theorem left_frame {B k:ℕ} {c:Com} {σ τ:Env} (hr:Run B c σ τ k)
    (q:ℚ) (h:LeftValue q σ)
    (hs:"left.s" ∉ c.wvars) (hn:"left.n" ∉ c.wvars)
    (hd:"left.d" ∉ c.wvars):LeftValue q τ:=by
  simpa only [LeftValue,hr.frame_var _ hs,hr.frame_var _ hn,hr.frame_var _ hd] using h

end Lax109476Proofs.RamScalarFrame

end

section

namespace Lax109476Proofs.RamScalarCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

theorem copy_spec (B:ℕ) (a b:String) (q:ℚ) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B) (hab:RamCopy.Disjoint a b):
    Spec B (Value a q) (copy a b) (fun _ τ => Value b q τ) 6:=by
  have hsn:a ++ ".n" ≠ b ++ ".s" :=hab ".n" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hsd:a ++ ".d" ≠ b ++ ".s" :=hab ".d" (by simp [RamCopy.suffixes]) ".s" (by simp [RamCopy.suffixes])
  have hnd:a ++ ".d" ≠ b ++ ".n" :=hab ".d" (by simp [RamCopy.suffixes]) ".n" (by simp [RamCopy.suffixes])
  have hbSN:b ++ ".s" ≠ b ++ ".n" :=by simp
  have hbSD:b ++ ".s" ≠ b ++ ".d" :=by simp
  have hbND:b ++ ".n" ≠ b ++ ".d" :=by simp
  rintro σ ⟨hval,hσn,hσd,hσs⟩
  have hs:=hσs.trans_lt h1
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => Value b q τ) σ; let c1:String→ String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString); let c2:String→ String:=c1 b; let c3:String:=c2 ".s"; let c4:String→ String:=c1 a; let c5:String:=c4 ".s"; let c6:Nat:=Env.vars σ c5; let c7:Env:=Env.setVar σ c3 c6; let c8:String:=c2 ".n"; let c9:String:=c4 ".n"; let c10:Nat:=Env.vars c7 c9; let c11:Env:=Env.setVar c7 c8 c10; let c12:String:=c2 ".d"; let c13:String:=c4 ".d"; let c14:Nat:=Env.vars c11 c13; let c15:Env:=Env.setVar c11 c12 c14; let c16:Nat→ Nat→ Nat:=Nat.add; let c17:Nat→ Nat:=c16 ((1:Nat)); let c18:Expr:=Expr.var c5; let c19:Nat:=c17 (Expr.size c18); let c20:Expr:=Expr.var c9; let c21:Nat:=c17 (Expr.size c20); let c22:Expr:=Expr.var c13; let c23:Nat:=c17 (Expr.size c22); let c24:Nat:=c16 c21 c23; let c25:Com:=Com.assign c8 c20; let c26:Com:=Com.assign c12 c22; @Exists.intro Env (fun (σ':Env) => And (Run B (copy a b) σ σ' ((6:Nat))) (c0 σ')) c15 (@And.intro (Run B (copy a b) σ c15 ((6:Nat))) (c0 c15) (RunStep.mono B (copy a b) σ c15 (c16 c19 c24) ((6:Nat)) (RunStep.seq B (Com.assign c3 c18) (Com.seq c25 c26) σ c7 c15 c19 c24 (RunStep.assign B σ c3 c18 c6 (RunStep.eval_var B σ c5 hs)) (RunStep.seq B c25 c26 c7 c11 c15 c21 c23 (RunStep.assign B c7 c8 c20 c10 (RunStep.eval_var B c7 c9 ?_)) (RunStep.assign B c11 c12 c22 c14 (RunStep.eval_var B c11 c13 ?_)))) (?nAX_g4103_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4103_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Value,Ne.symm hbSN,Ne.symm hbSD,Ne.symm hbND]

end Lax109476Proofs.RamScalarCopy

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

end Lax109476Proofs.RamAdvanceState

end

section

namespace Lax109476Proofs.RamRationalHalf

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamArithmetic

theorem fractionValue_half (s n d:ℕ):fractionValue s n (2 * d)=fractionValue s n d / 2:=by
  unfold fractionValue
  split_ifs <;> push_cast <;> ring

theorem half_spec (B M:ℕ) (q:ℚ) (hB:2 * M + 3 < B) (hq:Height q M):
    Spec B (LeftValue q) half (fun _ τ => FractionOutput (q / 2) τ) (36 * M.size + 60):=by
  have h2:2 < B:=by omega
  have hnB:=hq.1.trans_lt (by omega:M < B)
  have hdB:2 * q.den < B:=(Nat.mul_le_mul_left 2 hq.2).trans_lt (by omega)
  have hds:=RationalSizeBounds.size_mul_le 2 q.den
  have h2size:(2:ℕ).size=2:=by decide

  have hds':(2 * q.den).size=q.den.size + 1:=by
    simpa [Nat.bit] using Nat.size_bit (show Nat.bit false q.den ≠ 0 by have:=q.den_pos; simp [Nat.bit])
  rintro σ ⟨hval,hn,hd,hs⟩
  have hsB:σ.vars "left.s" < B:=by omega
  have hnorm:=normalizeFraction_output_spec B (σ.vars "left.s") q.num.natAbs (2 * q.den) hs hnB hdB (by positivity)
  have hsize:=Nat.size_le_size hq.2
  have hcost:8 + (36 * (2 * q.den).size + 16)≤ 36 * M.size + 60:=by rw [hds']; omega
  have he:fractionValue (σ.vars "left.s") q.num.natAbs (2 * q.den)=q / 2:=by
    rw [fractionValue_half]
    simpa only [hn,hd] using congrArg (fun r:ℚ => r / 2) hval
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c1:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c0; let c2:Nat→ Nat→ Nat:=Nat.mul; let c3:Nat:=Env.vars c1 "left.d"; let c4:Nat:=c2 c3 ((2:Nat)); let c5:Env:=Env.setVar c1 "rat.d" c4; let c6:Env→ Nat→ Prop:=Run B normalizeFraction c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat→ Nat:=c2 ((36:Nat)); let c9:Nat:=c2 ((2:Nat)) (Rat.den q); let c10:Nat:=c7 (c8 (Nat.size c9)) ((16:Nat)); let c11:Env→ Prop:=FractionOutput (fractionValue (Env.vars σ "left.s") (Int.natAbs (Rat.num q)) c9); let c12:Env→ Prop:=fun (σ':Env) => And (c6 σ' c10) (c11 σ'); let c13:Nat:=c7 (c8 (Nat.size M)) ((60:Nat)); let c14:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) q (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))); let c15:Env→ Prop:=(fun (x τ:Env) => c14 τ) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B half σ σ' c13) (c15 σ'); let c17:String→ Nat:=Env.vars c5; let c18:Nat→ Nat:=c7 ((1:Nat)); let c19:Nat:=c18 (Expr.size (Expr.var "left.s")); let c20:Nat:=c18 (Expr.size (Expr.var "left.n")); let c21:Expr:=Expr.mul (Expr.var "left.d") (Expr.lit ((2:Nat))); let c22:Nat:=c18 (Expr.size c21); let c23:Nat:=c7 c22 c10; let c24:Nat:=c7 c20 c23; let c25:Com:=Com.assign "rat.d" c21; let c26:Com:=Com.seq c25 normalizeFraction; @Exists.casesOn Env c12 (fun (x:@Exists Env c12) => @Exists Env c16) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (Int.natAbs (Rat.num q))) (And (@Eq Nat (Env.vars σ_1 "rat.d") c9) (@Eq Nat (Env.vars σ_1 "rat.s") (Env.vars σ "left.s")))) normalizeFraction (fun (x σ':Env) => c11 σ') c10 hnorm c5 ?_) fun (w:Env) (h:And (c6 w c10) (c11 w)) => @And.casesOn (c6 w c10) (c11 w) (fun (x:And (c6 w c10) (c11 w)) => @Exists Env c16) h fun (left:c6 w c10) (right:c11 w) => @Exists.intro Env c16 w (@And.intro (Run B half σ w c13) (c15 w) (RunStep.mono B half σ w (c7 c19 c24) c13 (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) c26) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) w c19 c24 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" hsB)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) c26 (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c1 w c20 c23 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c0 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g4382_0_0_0))) (RunStep.seq B c25 normalizeFraction c1 c5 w c22 c10 (RunStep.assign B c1 "rat.d" c21 c4 (RunStep.eval_mul B c1 (Expr.var "left.d") (Expr.lit ((2:Nat))) c3 ((2:Nat)) (RunStep.eval_var B c1 "left.d" (?nAX_g4382_0_0_1)) (RunStep.eval_lit B ((2:Nat)) c1 h2) (?nAX_g4382_0_0_2))) left))) (?nAX_g4382_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4382_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4382_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4382_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4382_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [mul_comm]

end Lax109476Proofs.RamRationalHalf

end

section

namespace Lax109476Proofs.RamRationalMidpoint

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem midpoint_spec (B M:ℕ) (l u:ℚ) (hB:4 * M ^ 2 + 3 < B)
    (hl:Height l M) (hu:Height u M):
    Spec B (fun σ => Value "bisect.lo" l σ∧ Value "bisect.hi" u σ) midpoint
      (fun _ τ => Value "bisect.mid" ((l + u) / 2) τ) (144 * M.size + 324):=by
  have hM:1≤ M:=le_trans l.den_pos hl.2
  have hMB:M < B:=by nlinarith
  have h1:1 < B:=by omega
  have hsum:Height (l + u) (2 * M ^ 2):=by
    simpa only [pow_two,Nat.mul_assoc] using height_add l u M M hl hu
  have hsumB:2 * M ^ 2 < B:=by omega
  have hhalf:Height ((l + u) / 2) (4 * M ^ 2):=by
    have h:=height_div (l + u) 2 (2 * M ^ 2) 2 hsum (by norm_num [Height])
    convert h using 1 <;> ring
  have hhalfB:4 * M ^ 2 < B:=by omega
  rintro σ ⟨hσl,hσu⟩
  obtain ⟨τ,hr₁,hτl⟩:=readLeft_spec B "bisect.lo" l h1 (hl.1.trans_lt hMB) (hl.2.trans_lt hMB)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ hσl
  have hτu:=value_frame hr₁ "bisect.hi" u hσu (by decide) (by decide) (by decide)
  obtain ⟨υ,hr₂,hυu⟩:=readRight_spec B "bisect.hi" u h1 (hu.1.trans_lt hMB) (hu.2.trans_lt hMB)
    (by simp [RamCopy.Disjoint,RamCopy.suffixes]) τ hτu
  have hυl:=left_frame hr₂ l hτl (by decide) (by decide) (by decide)
  obtain ⟨ρ,hr₃,hρsum⟩:=add_spec B M l u (by omega) hl hu υ ⟨hυl,hυu⟩
  obtain ⟨ξ,hr₄,hξsum⟩:=resultToLeft_spec B (l + u) h1 (hsum.1.trans_lt hsumB)
    (hsum.2.trans_lt hsumB) ρ hρsum
  obtain ⟨ζ,hr₅,hζhalf⟩:=RamRationalHalf.half_spec B (2 * M ^ 2) (l + u) (by omega) hsum ξ hξsum
  obtain ⟨η,hr₆,hη⟩:=save_spec B "bisect.mid" ((l + u) / 2) h1 (hhalf.1.trans_lt hhalfB)
    (hhalf.2.trans_lt hhalfB) (by simp) ζ hζhalf
  have hp:=RationalSizeBounds.size_pow_le M 2
  have hm:=RationalSizeBounds.size_mul_le 2 (M ^ 2)
  have h2size:(2:ℕ).size=2:=by decide
  rw [h2size] at hm
  exact ⟨η, (hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq (hr₅.seq hr₆))))).mono (by omega),hη⟩

end Lax109476Proofs.RamRationalMidpoint

end

section

namespace Lax109476Proofs.RamBisectionCommit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame

theorem commit_spec (B:ℕ) (l u t:ℚ) (answer:Bool) (h1:1 < B)
    (hn:t.num.natAbs < B) (hd:t.den < B):
    Spec B (fun σ => Value "bisect.lo" l σ∧ Value "bisect.hi" u σ∧ Value "bisect.mid" t σ∧
      condition.evalB B σ=some answer) commit
      (fun _ τ => Value "bisect.lo" (if answer then l else t) τ∧
        Value "bisect.hi" (if answer then t else u) τ) 10:=by
  rintro σ ⟨hσl,hσu,hσt,hσanswer⟩
  cases answer with
  | true =>
    obtain ⟨τ,hr,hτ⟩:=RamScalarCopy.copy_spec B "bisect.mid" "bisect.hi" t h1 hn hd
      (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ hσt
    exact ⟨τ,Run.ite_true hσanswer hr,
      value_frame hr "bisect.lo" l hσl (by decide) (by decide) (by decide),hτ⟩
  | false =>
    obtain ⟨τ,hr,hτ⟩:=RamScalarCopy.copy_spec B "bisect.mid" "bisect.lo" t h1 hn hd
      (by simp [RamCopy.Disjoint,RamCopy.suffixes]) σ hσt
    exact ⟨τ,Run.ite_false hσanswer hr,hτ,
      value_frame hr "bisect.hi" u hσu (by decide) (by decide) (by decide)⟩

end Lax109476Proofs.RamBisectionCommit

end

section

namespace Lax109476Proofs.BinaryOptimizationBounds

open BinaryOptimization RationalArithmeticBounds RationalRounding

theorem bisect_grid (query:ℚ→ Bool) (B k:ℕ):
    ∃ a b:ℕ,a≤ b∧ b≤ B * 2 ^ k∧
      (bisect query 0 B k).1=(a:ℚ) / 2 ^ k∧
      (bisect query 0 B k).2=(b:ℚ) / 2 ^ k:=by
  induction k with
  | zero => exact ⟨0,B,Nat.zero_le _,by simp,by simp [bisect],by simp [bisect]⟩
  | succ k ih =>
    obtain ⟨a,b,hab,hb,ha',hb'⟩:=ih
    let mid:=((bisect query 0 B k).1 + (bisect query 0 B k).2) / 2
    have hm:mid=((a + b:ℕ):ℚ) / 2 ^ (k + 1):=by
      dsimp only [mid]
      rw [ha',hb',pow_succ]
      push_cast
      ring
    have hdouble (v:ℕ):(v:ℚ) / 2 ^ k=((2 * v:ℕ):ℚ) / 2 ^ (k + 1):=by
      rw [pow_succ]
      push_cast
      field_simp
    change ∃ a' b':ℕ,a'≤ b'∧ b'≤ B * 2 ^ (k + 1)∧
      (if query mid then ((bisect query 0 B k).1,mid)
        else (mid, (bisect query 0 B k).2)).1=_∧
      (if query mid then ((bisect query 0 B k).1,mid)
        else (mid, (bisect query 0 B k).2)).2=_
    by_cases h:query mid=true
    · rw [if_pos h]
      refine ⟨2 * a,a + b,by omega, ?_,ha'.trans (hdouble a),hm⟩
      rw [pow_succ]
      nlinarith
    · rw [if_neg h]
      refine ⟨a + b,2 * b,by omega, ?_,hm,hb'.trans (hdouble b)⟩
      rw [pow_succ]
      nlinarith

theorem bisect_range (query:ℚ→ Bool) (B k:ℕ):
    0≤ (bisect query 0 B k).1∧
      (bisect query 0 B k).1≤ (bisect query 0 B k).2∧
      (bisect query 0 B k).2≤ B:=by
  obtain ⟨a,b,hab,hb,ha',hb'⟩:=bisect_grid query B k
  rw [ha',hb']
  have hp:(0:ℚ) < 2 ^ k:=by positivity
  refine ⟨by positivity, (div_le_div_iff_of_pos_right hp).mpr (by exact_mod_cast hab), ?_⟩
  apply (div_le_iff₀ hp).mpr
  exact_mod_cast hb

theorem bisect_height (query:ℚ→ Bool) (B k:ℕ):
    Height (bisect query 0 B k).1 ((B + 1) * 2 ^ k)∧
      Height (bisect query 0 B k).2 ((B + 1) * 2 ^ k):=by
  obtain ⟨a,b,hab,hb,ha',hb'⟩:=bisect_grid query B k
  have hg (v:ℕ) (hv:v≤ B * 2 ^ k):
      Height ((v:ℚ) / 2 ^ k) ((B + 1) * 2 ^ k):=by
    have h:=grid_num_den_bound (v:ℤ) (2 ^ k) (by positivity)
    simp only [Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat,Int.natAbs_natCast] at h
    exact ⟨h.1.trans (by nlinarith),h.2.trans (by nlinarith)⟩
  rw [ha',hb']
  exact ⟨hg a (hab.trans hb),hg b hb⟩

end Lax109476Proofs.BinaryOptimizationBounds

end

section

namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars RamScalarFrame
open BinaryOptimization RamBisectionCommit

def Invariant (query:ℚ→ Bool) (D K:ℕ) (Q:Env→ Prop) (σ:Env):Prop:=
  Q σ∧ Value "bisect.lo" (bisect query 0 D (σ.vars "bisect.i")).1 σ∧
    Value "bisect.hi" (bisect query 0 D (σ.vars "bisect.i")).2 σ∧
    σ.vars "bisect.i" ≤ K∧ σ.vars "bisect.limit"=K

set_option maxHeartbeats 0 in

theorem body_spec (B M D K queryCost:ℕ) (query:ℚ→ Bool) (queryCom:Com) (Q:Env→ Prop)
    (hB:4 * M ^ 2 + 3 < B) (hKB:K < B) (hM:(D + 1) * 2 ^ K≤ M)
    (hquery:∀ t,Height t (4 * M ^ 2)→ Spec B (fun σ => Q σ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ∧ condition.evalB B τ=some (query t)) queryCost)
    (hfields:∀ x∈ fields,x∉ queryCom.wvars)
    (hQmid:preserves B Q RamRationalMidpoint.midpoint)
    (hQend:preserves B Q (.seq commit increment)):
    Spec B (fun σ => Invariant query D K Q σ∧ σ.vars "bisect.i" < K) (body queryCom)
      (fun σ τ => Invariant query D K Q τ∧ τ.vars "bisect.i"=σ.vars "bisect.i" + 1)
      (144 * M.size + 338 + queryCost):=by
  have hMB:M < B:=by nlinarith
  have h1:1 < B:=by omega
  rintro σ ⟨⟨hσQ,hσl,hσu,hσi,hσK⟩,hi⟩
  let j:=σ.vars "bisect.i"
  let old:=bisect query 0 D j
  let mid:=(old.1 + old.2) / 2
  have hbound:(D + 1) * 2 ^ j≤ M:=(Nat.mul_le_mul_left (D + 1)
    (Nat.pow_le_pow_right (by decide) hσi)).trans hM
  obtain ⟨hl,hu⟩:=BinaryOptimizationBounds.bisect_height query D j
  have hlM:=height_mono _ hl hbound
  have huM:=height_mono _ hu hbound
  have hmid:Height mid (4 * M ^ 2):=by
    have h:=height_div (old.1 + old.2) 2 (2 * M * M) 2
      (height_add old.1 old.2 M M hlM huM) (by norm_num [Height])
    convert h using 1 <;> ring
  obtain ⟨τ,hr₁,hτmid⟩:=RamRationalMidpoint.midpoint_spec B M old.1 old.2 hB hlM huM σ ⟨hσl,hσu⟩
  have hτQ:=hQmid hr₁ hσQ
  obtain ⟨υ,hr₂,hυQ,hυanswer⟩:=hquery mid hmid τ ⟨hτQ,hτmid⟩
  have hτl:=value_frame hr₁ "bisect.lo" old.1 hσl (by decide) (by decide) (by decide)
  have hτu:=value_frame hr₁ "bisect.hi" old.2 hσu (by decide) (by decide) (by decide)
  have hυl:=value_frame hr₂ "bisect.lo" old.1 hτl
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  have hυu:=value_frame hr₂ "bisect.hi" old.2 hτu
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  have hυmid:=value_frame hr₂ "bisect.mid" mid hτmid
    (hfields _ (by simp [fields])) (hfields _ (by simp [fields])) (hfields _ (by simp [fields]))
  obtain ⟨ρ,hr₃,hρl,hρu⟩:=commit_spec B old.1 old.2 mid (query mid) h1
    (hmid.1.trans_lt (by omega)) (hmid.2.trans_lt (by omega)) υ ⟨hυl,hυu,hυmid,hυanswer⟩
  have hρi:ρ.vars "bisect.i"=j:=
    (hr₃.frame_var _ (by decide)).trans ((hr₂.frame_var _ (hfields _ (by simp [fields]))).trans
      (hr₁.frame_var _ (by decide)))
  have hjB:j < B:=hi.trans hKB
  have hsumB:Bop.add.apply (ρ.vars "bisect.i") 1 < B:=by
    simpa [hρi] using (show j + 1 < B by dsimp only [j]; omega)
  have hr₄:Run B increment ρ (ρ.setVar "bisect.i" (j + 1)) 4:=Run.assign (by
    simpa only [hρi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=ρ) (x:= "bisect.i") (hρi ▸ hjB)) (evalB_lit h1) hsumB))
  have hresultl:=value_frame hr₄ "bisect.lo" (if query mid then old.1 else mid) hρl (by decide) (by decide) (by decide)
  have hresultu:=value_frame hr₄ "bisect.hi" (if query mid then mid else old.2) hρu (by decide) (by decide) (by decide)
  have hr:=hr₁.seq (hr₂.seq (hr₃.seq hr₄))
  have hlimit:(ρ.setVar "bisect.i" (j + 1)).vars "bisect.limit"=K:=
    (hr₄.frame_var _ (by decide)).trans ((hr₃.frame_var _ (by decide)).trans
      ((hr₂.frame_var _ (hfields _ (by simp [fields]))).trans ((hr₁.frame_var _ (by decide)).trans hσK)))
  refine ⟨_,hr.mono (by omega), ⟨hQend (hr₃.seq hr₄) hυQ, ?_, ?_, ?_,hlimit⟩, ?_⟩
  · change Value "bisect.lo" (bisect query 0 D (j + 1)).1 _
    simpa only [bisect,apply_ite Prod.fst,Prod.fst] using hresultl
  · change Value "bisect.hi" (bisect query 0 D (j + 1)).2 _
    simpa only [bisect,apply_ite Prod.snd,Prod.snd] using hresultu
  · change j + 1≤ K; omega
  · simp [j]

theorem loop_spec (B M D K queryCost:ℕ) (query:ℚ→ Bool) (queryCom:Com) (Q:Env→ Prop)
    (hB:4 * M ^ 2 + 3 < B) (hKB:K < B) (hM:(D + 1) * 2 ^ K≤ M)
    (hquery:∀ t,Height t (4 * M ^ 2)→ Spec B (fun σ => Q σ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ∧ condition.evalB B τ=some (query t)) queryCost)
    (hfields:∀ x∈ fields,x∉ queryCom.wvars)
    (hQmid:preserves B Q RamRationalMidpoint.midpoint)
    (hQend:preserves B Q (.seq commit increment))
    (hQinit:∀ σ,Q σ→ Q (σ.setVar "bisect.i" 0)):
    Spec B (fun σ => Q σ∧ Value "bisect.lo" 0 σ∧ Value "bisect.hi" D σ∧ σ.vars "bisect.limit"=K)
      (loop queryCom) (fun _ τ => Q τ∧ Value "bisect.lo" (bisect query 0 D K).1 τ∧
        Value "bisect.hi" (bisect query 0 D K).2 τ)
      ((144 * M.size + 342 + queryCost) * K + 6):=by
  have hlo:=Spec.forRangeZero "bisect.i" "bisect.limit" (Invariant query D K Q) K
    (144 * M.size + 338 + queryCost) hKB (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.2.2)
    (body_spec B M D K queryCost query queryCom Q hB hKB hM hquery hfields hQmid hQend)
  refine ((hlo.pre ?_).post ?_).mono ?_
  · rintro σ ⟨hQ,hl,hu,hK⟩
    refine ⟨?_, ?_, ?_,by simp, ?_⟩
    · exact hQinit σ hQ
    · simpa [Value,vars_setVar,bisect] using hl
    · simpa [Value,vars_setVar,bisect] using hu
    · simpa using hK
  · rintro σ τ _ ⟨hτ,hcounter⟩
    dsimp only [Invariant] at hτ
    rw [hcounter] at hτ
    exact ⟨hτ.1,hτ.2.1,hτ.2.2.1⟩
  · exact le_of_eq (by ring)

end Lax109476Proofs.RamBisectionLoop

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

namespace Lax109476Proofs.RamBinaryMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalScalars RamScalarFrame RationalArithmeticBounds BinaryOptimization

theorem prepare_spec (B D:ℕ) (h3:3 < B) (hDB:D < B) (hKB:steps D < B):
    Spec B (fun σ => σ.vars "minimum.bound"=D) prepare
      (fun _ τ => Value "bisect.lo" 0 τ∧ Value "bisect.hi" D τ∧
        τ.vars "bisect.limit"=steps D) (12 * D.size + 28):=by
  have hstart:Spec B (fun σ => σ.vars "minimum.bound"=D) endpoints
      (fun _ τ => Value "bisect.lo" 0 τ∧ Value "bisect.hi" D τ∧ τ.vars "bits.v"=D) 14:=by
    intro σ hσ
    (expose_names;
      (refine let c0:Env→ Prop:=Value "bisect.lo" (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c1:Env→ Prop:=(fun (x τ:Env) => And (c0 τ) (And (Value "bisect.hi" (@Nat.cast Rat Rat.instNatCast D) τ) (@Eq Nat (Env.vars τ "bits.v") D))) σ; let c2:Env:=Env.setVar σ "bisect.lo.s" ((0:Nat)); let c3:Env:=Env.setVar c2 "bisect.lo.n" ((0:Nat)); let c4:Env:=Env.setVar c3 "bisect.lo.d" ((1:Nat)); let c5:Env:=Env.setVar c4 "bisect.hi.s" ((0:Nat)); let c6:Nat:=Env.vars c5 "minimum.bound"; let c7:Env:=Env.setVar c5 "bisect.hi.n" c6; let c8:Env:=Env.setVar c7 "bisect.hi.d" ((1:Nat)); let c9:Nat:=Env.vars c8 "minimum.bound"; let c10:Env:=Env.setVar c8 "bits.v" c9; let c11:Nat→ Nat→ Nat:=Nat.add; let c12:Nat→ Nat:=c11 ((1:Nat)); let c13:Nat:=c12 (Expr.size (Expr.lit ((0:Nat)))); let c14:Nat→ Nat:=c11 c13; let c15:Nat:=c12 (Expr.size (Expr.lit ((1:Nat)))); let c16:Nat→ Nat:=c11 c15; let c17:Nat:=c12 (Expr.size (Expr.var "minimum.bound")); let c18:Nat:=c16 c17; let c19:Nat:=c11 c17 c18; let c20:Nat:=c14 c19; let c21:Nat:=c16 c20; let c22:Nat:=c14 c21; let c23:Com:=Com.assign "bisect.lo.n" (Expr.lit ((0:Nat))); let c24:Com:=Com.assign "bisect.lo.d" (Expr.lit ((1:Nat))); let c25:Com:=Com.assign "bisect.hi.s" (Expr.lit ((0:Nat))); let c26:Com:=Com.assign "bisect.hi.d" (Expr.lit ((1:Nat))); let c27:Com:=Com.seq c26 (Com.assign "bits.v" (Expr.var "minimum.bound")); let c28:Com:=Com.seq (Com.assign "bisect.hi.n" (Expr.var "minimum.bound")) c27; let c29:Com:=Com.seq c25 c28; let c30:Com:=Com.seq c24 c29; @Exists.intro Env (fun (σ':Env) => And (Run B endpoints σ σ' ((14:Nat))) (c1 σ')) c10 (@And.intro (Run B endpoints σ c10 ((14:Nat))) (c1 c10) (RunStep.mono B endpoints σ c10 (c14 c22) ((14:Nat)) (RunStep.seq B (Com.assign "bisect.lo.s" (Expr.lit ((0:Nat)))) (Com.seq c23 c30) σ c2 c10 c13 c22 (RunStep.assign B σ "bisect.lo.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4973_0_0_0))) (RunStep.seq B c23 c30 c2 c3 c10 c13 c21 (RunStep.assign B c2 "bisect.lo.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g4973_0_0_1))) (RunStep.seq B c24 c29 c3 c4 c10 c15 c20 (RunStep.assign B c3 "bisect.lo.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c3 (?nAX_g4973_0_0_2))) (RunStep.seq B c25 c28 c4 c5 c10 c13 c19 (RunStep.assign B c4 "bisect.hi.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c4 (?nAX_g4973_0_0_3))) (RunStep.seq B (Com.assign "bisect.hi.n" (Expr.var "minimum.bound")) c27 c5 c7 c10 c17 c18 (RunStep.assign B c5 "bisect.hi.n" (Expr.var "minimum.bound") c6 (RunStep.eval_var B c5 "minimum.bound" (?nAX_g4973_0_0_4))) (RunStep.seq B c26 (Com.assign "bits.v" (Expr.var "minimum.bound")) c7 c8 c10 c15 c17 (RunStep.assign B c7 "bisect.hi.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 (?nAX_g4973_0_0_5))) (RunStep.assign B c8 "bits.v" (Expr.var "minimum.bound") c9 (RunStep.eval_var B c8 "minimum.bound" (?nAX_g4973_0_0_6))))))))) (?nAX_g4973_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4973_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [Value,fractionValue]
  have hlimit:Spec B (fun σ => σ.vars "bits.k"=D.size) setLimit
      (fun _ τ => τ.vars "bisect.limit"=steps D) 6:=by
    intro σ hσ
    have hsize:=RationalSizeBounds.size_le_self D
    (expose_names;
      (refine let c0:Env→ Prop:=(fun (x τ:Env) => @Eq Nat (Env.vars τ "bisect.limit") (steps D)) σ; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=Nat.mul ((3:Nat)) (Env.vars σ "bits.k"); let c3:Nat:=c1 c2 ((2:Nat)); let c4:Env:=Env.setVar σ "bisect.limit" c3; let c5:Expr:=Expr.mul (Expr.lit ((3:Nat))) (Expr.var "bits.k"); let c6:Expr:=Expr.add c5 (Expr.lit ((2:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B setLimit σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B setLimit σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B setLimit σ c4 (c1 ((1:Nat)) (Expr.size c6)) ((6:Nat)) (RunStep.assign B σ "bisect.limit" c6 c3 (RunStep.eval_add B σ c5 (Expr.lit ((2:Nat))) c2 ((2:Nat)) (RunStep.eval_mul B σ (Expr.lit ((3:Nat))) (Expr.var "bits.k") ((3:Nat)) (Env.vars σ "bits.k") (RunStep.eval_lit B ((3:Nat)) σ h3) (RunStep.eval_var B σ "bits.k" (?nAX_g4973_1_0_0)) ?_) (RunStep.eval_lit B ((2:Nat)) σ (?nAX_g4973_1_0_1)) ?_)) (?nAX_g4973_1_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4973_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4973_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all))
    all_goals simp_all [steps]
    all_goals omega
  intro σ hσ
  obtain ⟨τ,hr₁,hτl,hτu,hτv⟩:=hstart σ hσ
  obtain ⟨υ,hr₂,_,hυk⟩:=RamBitLength.bitLength_spec B D (by omega) hDB τ hτv
  obtain ⟨ρ,hr₃,hρlimit⟩:=hlimit υ hυk
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega), ?_, ?_,hρlimit⟩
  · exact value_frame (hr₂.seq hr₃) "bisect.lo" 0 hτl (by decide) (by decide) (by decide)
  · exact value_frame (hr₂.seq hr₃) "bisect.hi" D hτu (by decide) (by decide) (by decide)

theorem finish_spec (S N w D:ℕ) (l u:ℚ) (hu0:0≤ u)
    (hl:Height l (2 ^ S)) (hu:Height u (2 ^ S)) (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamRationalReconstruction.wordWidth S≤ w) (hDB:D < 2 ^ w):
    Spec (2 ^ w) (fun σ => Value "bisect.lo" l σ∧ Value "bisect.hi" u σ∧
      σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N) finish
      (fun _ τ => RamReconstructionRecord.Output (RationalReconstruction.reconstruct l u D) τ)
      (RamRationalReconstruction.instructionBound S + 14):=by
  have h1:1 < 2 ^ w:=by
    have hp:=Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤ w by
      unfold RamRationalReconstruction.wordWidth RamConvergentBounds.wordWidth at hw; omega)
    norm_num at hp; omega
  have hHB:2 ^ S < 2 ^ w:=Nat.pow_lt_pow_right (by decide) (by
    unfold RamRationalReconstruction.wordWidth RamConvergentBounds.wordWidth
      RamConvergentBounds.exponent RamDecoder.wordWidth RamRationalReconstruction.depthBound at hw
    nlinarith)
  have hcopyl:=RamScalarCopy.copy_spec (2 ^ w) "bisect.lo" "recon.lo" l h1
    (hl.1.trans_lt hHB) (hl.2.trans_lt hHB) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hcopyu:=RamScalarCopy.copy_spec (2 ^ w) "bisect.hi" "recon.hi" u h1
    (hu.1.trans_lt hHB) (hu.2.trans_lt hHB) (by simp [RamCopy.Disjoint,RamCopy.suffixes])
  have hreconstruct:=RamRationalReconstruction.reconstruct_spec S N w D l u hu0 hl hu hN hw hDB
  rintro σ ⟨hσl,hσu,hσD,hσN⟩
  obtain ⟨τ,hr₁,hτl⟩:=hcopyl σ hσl
  have hτu:=value_frame hr₁ "bisect.hi" u hσu (by decide) (by decide) (by decide)
  obtain ⟨υ,hr₂,hυu⟩:=hcopyu τ hτu
  have hυl:=value_frame hr₂ "recon.lo" l hτl (by decide) (by decide) (by decide)
  have hυD:=((hr₁.seq hr₂).frame_var "minimum.bound" (by decide)).trans hσD
  have hυN:(υ.arrs "cf.stack").length=N:=by
    rw [(hr₁.seq hr₂).frame_arr _ (by decide)]; exact hσN
  have hr₃:Run (2 ^ w) (.assign "recon.bound" (.var "minimum.bound")) υ (υ.setVar "recon.bound" D) 2:=
    Run.assign (by simpa only [hυD] using (evalB_var (B:=2 ^ w) (σ:=υ) (x:= "minimum.bound")
      (hυD ▸ hDB)))
  obtain ⟨ρ,hr₄,hρ⟩:=hreconstruct (υ.setVar "recon.bound" D)
    ⟨value_frame hr₃ "recon.lo" l hυl (by decide) (by decide) (by decide),
      value_frame hr₃ "recon.hi" u hυu (by decide) (by decide) (by decide),by simp,
      by simpa only [arrs_setVar] using hυN⟩
  exact ⟨ρ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega),hρ⟩

set_option maxHeartbeats 0 in
theorem minimum_spec (S N w D M queryCost:ℕ) (query:ℚ→ Bool) (queryCom:Com) (Q:Env→ Prop)
    (hB:4 * M ^ 2 + 3 < 2 ^ w) (hKB:steps D < 2 ^ w)
    (hM:(D + 1) * 2 ^ steps D≤ M) (hMS:M≤ 2 ^ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamRationalReconstruction.wordWidth S≤ w) (hDB:D < 2 ^ w)
    (hquery:∀ t,Height t (4 * M ^ 2)→ Spec (2 ^ w) (fun σ => Q σ∧ Value "bisect.mid" t σ) queryCom
      (fun _ τ => Q τ∧ RamBisectionCommit.condition.evalB (2 ^ w) τ=some (query t)) queryCost)
    (hfields:∀ x∈ RamBisectionLoop.fields,x∉ queryCom.wvars)
    (hbound:"minimum.bound" ∉ queryCom.wvars)
    (hQmid:RamBisectionLoop.preserves (2 ^ w) Q RamRationalMidpoint.midpoint)
    (hQend:RamBisectionLoop.preserves (2 ^ w) Q (.seq RamBisectionCommit.commit RamBisectionLoop.increment))
    (hQinit:∀ σ,Q σ→ Q (σ.setVar "bisect.i" 0))
    (hQprepare:RamBisectionLoop.preserves (2 ^ w) Q prepare)
    (hQfinish:RamBisectionLoop.preserves (2 ^ w) Q finish):
    Spec (2 ^ w) (fun σ => Q σ∧ σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N)
      (minimum queryCom) (fun _ τ => Q τ∧ RamReconstructionRecord.Output (BinaryOptimization.minimum query D) τ)
      ((144 * M.size + 342 + queryCost) * steps D + 12 * D.size +
        RamRationalReconstruction.instructionBound S + 48):=by
  rintro σ ⟨hσQ,hσD,hσN⟩
  obtain ⟨τ,hr₁,hτl,hτu,hτlimit⟩:=prepare_spec (2 ^ w) D (by omega) hDB hKB σ hσD
  have hτQ:=hQprepare hr₁ hσQ
  obtain ⟨υ,hr₂,hυQ,hυl,hυu⟩:=RamBisectionLoop.loop_spec (2 ^ w) M D (steps D) queryCost query queryCom Q
    hB hKB hM hquery hfields hQmid hQend hQinit τ ⟨hτQ,hτl,hτu,hτlimit⟩
  have hloopbound:"minimum.bound" ∉ (RamBisectionLoop.loop queryCom).wvars:=by
    simp only [RamBisectionLoop.loop,RamBisectionLoop.body,Com.wvars,List.mem_append,not_or,
      List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨by decide,by decide,hbound,by decide,by decide⟩
  have hυD:=(hr₂.frame_var _ hloopbound).trans ((hr₁.frame_var _ (by decide)).trans hσD)
  have hυN:(υ.arrs "cf.stack").length=N:=by
    obtain ⟨_,_,hs⟩:=(hr₁.seq hr₂).bigStep
    exact (RamAdvanceState.array_length_of_bigStep hs "cf.stack").trans hσN
  obtain ⟨hl,hu⟩:=BinaryOptimizationBounds.bisect_height query D (steps D)
  have he:=hM.trans hMS
  have hu0:=(BinaryOptimizationBounds.bisect_range query D (steps D)).1.trans
    (BinaryOptimizationBounds.bisect_range query D (steps D)).2.1
  obtain ⟨ρ,hr₃,hρ⟩:=finish_spec S N w D _ _ hu0
    (height_mono _ hl he) (height_mono _ hu he) hN hw hDB υ ⟨hυl,hυu,hυD,hυN⟩
  refine ⟨ρ, (hr₁.seq (hr₂.seq hr₃)).mono (by omega),hQfinish hr₃ hυQ, ?_⟩
  exact hρ

end Lax109476Proofs.RamBinaryMinimum

end

theorem solution:∀ (S N w D M queryCost:Nat) (query:Rat→ Bool) (queryCom:Lax808846Proofs.Imp.Com)
  (Q:Lax808846Proofs.Imp.Env→ Prop),
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
                (∀ (t:Rat),
                    Lax109476Proofs.RationalArithmeticBounds.Height t
                        (Nat.mul
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
                                  (Nat.add
                                    (Nat.add
                                      (Nat.add
                                        (Nat.mul
                                          (Nat.add
                                            (Nat.add
                                              (Nat.mul
                                                ((144:Nat)) M.size)
                                              ((342:Nat)))
                                            queryCost)
                                          (Lax109476Proofs.BinaryOptimization.steps D))
                                        (Nat.mul
                                          ((12:Nat)) D.size))
                                      (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                    ((48:Nat))):= @Lax109476Proofs.RamBinaryMinimum.minimum_spec
