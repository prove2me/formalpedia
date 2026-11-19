-- Prove2me | solution 1 for Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:57:46.414206+00:00
-- url     : https://prove2.me/submissions/5712ce45-50d4-47d8-9fcc-15227442dceb

import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax109476Proofs_RamArithmetic_normalizeFraction_spec_native
import Theorems.Thm_Lax109476Proofs_RamRounding_upperRootFraction_spec_native

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
namespace Lax109476Proofs.RamRounding
end Lax109476Proofs.RamRounding
theorem Lax109476Proofs.RamRounding.upperRootFraction_spec:∀ (B M s n d D:Nat),
  Nat.lt
      (HAdd.hAdd
        (HAdd.hAdd
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat))
                (HAdd.hAdd
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                    ((3:Nat)))
                  ((2:Nat))))
              ((1:Nat)))
            ((2:Nat)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            ((3:Nat))))
        ((3:Nat)))
      B→
    Nat.le s ((1:Nat))→
      Nat.le n M→
        Nat.le d M→
          Nat.le D M→
            Nat.lt ((0:Nat)) d→
              Nat.lt ((0:Nat)) D→
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ:Lax808846Proofs.Imp.Env) =>
                    And (@Eq Nat (σ.vars "left.s") s)
                      (And (@Eq Nat (σ.vars "left.n") n)
                        (And (@Eq Nat (σ.vars "left.d") d) (@Eq Nat (σ.vars "grid.D") D))))
                  Lax109476Proofs.RamRounding.upperRootFraction
                  (fun (x σ':Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamRational.FractionOutput
                      (Lax109476Proofs.RationalRounding.sqrtUpper (Lax109476Proofs.RamRational.fractionValue s n d) D)
                      σ')
                  (HAdd.hAdd
                    (HAdd.hAdd
                      (HMul.hMul
                        ((26:Nat))
                        (Lax109476Proofs.RamRounding.upperMagnitude s n d D).size)
                      (HMul.hMul
                        ((36:Nat)) D.size))
                    ((128:Nat))):= @Lax109476Proofs.RamRounding.upperRootFraction_spec_native

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

theorem size_add_one_le (a:ℕ):Nat.size (a + 1)≤ Nat.size a + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h:=Nat.lt_size_self a
  have hp:0 < 2 ^ Nat.size a:=by positivity
  omega

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

open RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

end Lax109476Proofs.RationalArithmeticBounds

end

section

namespace Lax109476Proofs.RamPrimitiveBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRounding RationalSizeBounds RationalArithmeticBounds

theorem upperMagnitude_le (s n d D M:ℕ) (hn:n≤ M) (hD:D≤ M):
    upperMagnitude s n d D≤ M ^ 3 + 1:=by
  have ha:n * D ^ 2≤ M ^ 3:=by
    calc
      _≤ M * M ^ 2:=Nat.mul_le_mul hn (Nat.pow_le_pow_left hD 2)
      _=_:=by ring
  have hq:=Nat.div_le_self (n * D ^ 2) d
  unfold upperMagnitude ceilQuotient
  split_ifs <;> omega

theorem upperMagnitude_size (s n d D M:ℕ) (hn:n≤ M) (hD:D≤ M):
    (upperMagnitude s n d D).size≤ 3 * M.size + 2:=by
  have hs:=Nat.size_le_size (upperMagnitude_le s n d D M hn hD)
  have hp:=size_pow_le M 3
  have ha:=size_add_one_le (M ^ 3)
  omega

theorem upperRootFraction_uniform_spec (B M s n d D:ℕ)
    (hB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hs:s≤ 1) (hn:n≤ M) (hd:d≤ M) (hD:D≤ M)
    (hdpos:0 < d) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "left.s"=s∧ σ.vars "left.n"=n∧
      σ.vars "left.d"=d∧ σ.vars "grid.D"=D) upperRootFraction
      (fun _ τ => FractionOutput (RationalRounding.sqrtUpper (fractionValue s n d) D) τ)
      (114 * M.size + 180):=by
  apply (upperRootFraction_spec B M s n d D hB hs hn hd hD hdpos hDpos).mono
  have hs:=upperMagnitude_size s n d D M hn hD
  have hds:=Nat.size_le_size hD
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

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidArithmeticBounds

open RationalArithmeticBounds RationalRounding Matrix
open EllipsoidBounds EllipsoidCenter

theorem height_sqrtUpper (q:ℚ) (B D:ℕ) (hq:Height q B) (hD:0 < D):
    Height (sqrtUpper q D) (B * D ^ 2 + 1):=by
  have hb:1≤ B:=q.den_pos.trans_le hq.2
  have hqB:q≤ (B:ℚ):=by
    have hden:(0:ℚ) < q.den:=by positivity
    have hden1:(1:ℚ)≤ q.den:=by exact_mod_cast q.den_pos
    have hn:(q.num:ℚ)≤ B:=by
      have hnabs:q.num≤ (q.num.natAbs:ℤ):=Int.le_natAbs
      have hc':(q.num:ℚ)≤ ((q.num.natAbs:ℤ):ℚ):=Int.cast_le.mpr hnabs
      have hc:(q.num:ℚ)≤ (q.num.natAbs:ℚ):=by simpa only [Int.cast_natCast] using hc'
      exact hc.trans (by exact_mod_cast hq.1)
    rw [← q.num_div_den]
    apply (div_le_iff₀ hden).mpr
    exact hn.trans (by nlinarith)
  have hc:Nat.ceil (q * (D:ℚ) ^ 2)≤ B * D ^ 2:=by
    apply Nat.ceil_le.mpr
    exact_mod_cast mul_le_mul_of_nonneg_right hqB (sq_nonneg (D:ℚ))
  have hs:Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2))≤ B * D ^ 2:=
    (Nat.sqrt_le_self _).trans hc
  have hg:=grid_num_den_bound
    ((Nat.sqrt (Nat.ceil (q * (D:ℚ) ^ 2)) + 1:ℕ):ℤ) D hD
  simp only [Int.cast_natCast,Int.natAbs_natCast] at hg
  exact ⟨hg.1.trans (Nat.add_le_add_right hs 1),hg.2.trans (by nlinarith)⟩

end Lax109476Proofs.EllipsoidArithmeticBounds

end

section

namespace Lax109476Proofs.RamEllipsoidScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamEllipsoidForm RationalSizeBounds RationalArithmeticBounds
open RamRounding RamPrimitiveBounds RamFrame

theorem alphaFraction_spec (B n:ℕ) (hn:2≤ n) (hnB:n ^ 2 < B):
    Spec B (fun σ => σ.vars "vec.n"=n) alphaFraction
      (fun _ τ => FractionOutput ((n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1)) τ)
      (36 * (n ^ 2 - 1).size + 26):=by
  have hnn:n < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hd:n ^ 2 - 1 < B:=(Nat.sub_le _ _).trans_lt hnB
  have hdpos:0 < n ^ 2 - 1:=by
    have hsq:1 < n ^ 2:=by nlinarith
    omega
  have hone:1≤ n ^ 2:=by nlinarith
  have hnorm:=normalizeFraction_output_spec B 0 (n ^ 2) (n ^ 2 - 1) (by omega) hnB hd hdpos
  have hval:fractionValue 0 (n ^ 2) (n ^ 2 - 1)=(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1):=by
    simp [fractionValue,Nat.cast_sub hone]
  intro σ hσ
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=Env.vars c0 "vec.n"; let c3:Nat:=c1 c2 c2; let c4:Env:=Env.setVar c0 "rat.n" c3; let c5:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c6:Nat:=Env.vars c4 "rat.n"; let c7:Nat:=c5 c6 ((1:Nat)); let c8:Env:=Env.setVar c4 "rat.d" c7; let c9:Env→ Nat→ Prop:=Run B normalizeFraction c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n ((2:Nat)); let c12:Nat:=c5 c11 ((1:Nat)); let c13:Nat→ Nat:=c10 (c1 ((36:Nat)) (Nat.size c12)); let c14:Nat:=c13 ((16:Nat)); let c15:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) c11 c12); let c16:Env→ Prop:=fun (σ':Env) => And (c9 σ' c14) (c15 σ'); let c17:Nat:=c13 ((26:Nat)); let c18:Rat:= @HPow.hPow Rat Nat Rat (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid))) (@Nat.cast Rat Rat.instNatCast n) ((2:Nat)); let c19:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) c18 (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) c18 (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))); let c20:Env→ Prop:=(fun (x τ:Env) => c19 τ) σ; let c21:Env→ Prop:=fun (σ':Env) => And (Run B alphaFraction σ σ' c17) (c20 σ'); let c22:Prop:= @Exists Env c21; let c23:String→ Nat:=Env.vars c8; let c24:Nat→ Nat:=c10 ((1:Nat)); let c25:Nat:=c24 (Expr.size (Expr.lit ((0:Nat)))); let c26:Nat:=c24 (Expr.size (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n"))); let c27:Expr:=Expr.sub (Expr.var "rat.n") (Expr.lit ((1:Nat))); let c28:Nat:=c24 (Expr.size c27); let c29:Nat:=c10 c28 c14; let c30:Nat:=c10 c26 c29; let c31:Com:=Com.assign "rat.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")); let c32:Com:=Com.assign "rat.d" c27; let c33:Com:=Com.seq c32 normalizeFraction; @Exists.casesOn Env c16 (fun (x:@Exists Env c16) => c22) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c11) (And (@Eq Nat (Env.vars σ_1 "rat.d") c12) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c15 σ') c14 hnorm c8 ?_) fun (w:Env) (h:And (c9 w c14) (c15 w)) => @And.casesOn (c9 w c14) (c15 w) (fun (x:And (c9 w c14) (c15 w)) => c22) h fun (left:c9 w c14) (right:c15 w) => @Exists.intro Env c21 w (@And.intro (Run B alphaFraction σ w c17) (c20 w) (RunStep.mono B alphaFraction σ w (c10 c25 c30) c17 (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c31 c33) σ c0 w c25 c30 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4277_0_0_0))) (RunStep.seq B c31 c33 c0 c4 w c26 c29 (RunStep.assign B c0 "rat.n" (Expr.mul (Expr.var "vec.n") (Expr.var "vec.n")) c3 (RunStep.eval_mul B c0 (Expr.var "vec.n") (Expr.var "vec.n") c2 c2 (RunStep.eval_var B c0 "vec.n" (?nAX_g4277_0_0_1)) (RunStep.eval_var B c0 "vec.n" (?nAX_g4277_0_0_2)) ?_)) (RunStep.seq B c32 normalizeFraction c4 c8 w c28 c14 (RunStep.assign B c4 "rat.d" c27 c7 (RunStep.eval_sub B c4 (Expr.var "rat.n") (Expr.lit ((1:Nat))) c6 ((1:Nat)) (RunStep.eval_var B c4 "rat.n" ?_) (RunStep.eval_lit B ((1:Nat)) c4 h1) ?_)) left))) (?nAX_g4277_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4277_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4277_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4277_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4277_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnorm
  all_goals simp_all [pow_two]

theorem alphaFraction_cost (n:ℕ):
    36 * (n ^ 2 - 1).size + 26≤ 72 * n.size + 62:=by
  have hd:=Nat.size_le_size (Nat.sub_le (n ^ 2) 1)
  have hp:=size_pow_le n 2
  omega

theorem inflationFraction_spec (B E:ℕ) (hE:0 < E) (hB:(E + 1) ^ 2 < B):
    Spec B (fun σ => σ.vars "ell.epsden"=E) inflationFraction
      (fun _ τ => FractionOutput ((1 + 1 / (E:ℚ)) ^ 2) τ)
      (36 * (E ^ 2).size + 30):=by
  have hEB:E < B:=by nlinarith
  have hEaB:E + 1 < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hdB:E ^ 2 < B:=by nlinarith
  have hnorm:=normalizeFraction_output_spec B 0 ((E + 1) ^ 2) (E ^ 2)
    (by omega) hB hdB (by positivity)
  have hval:fractionValue 0 ((E + 1) ^ 2) (E ^ 2)=(1 + 1 / (E:ℚ)) ^ 2:=by
    have hEq:(E:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt hE
    simp only [fractionValue,show (0:ℕ) ≠ 1 by decide,ite_false,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    field_simp
  intro σ hσ
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "ell.epsden") ((1:Nat)); let c2:Env:=Env.setVar σ "infl.a" c1; let c3:Env:=Env.setVar c2 "rat.s" ((0:Nat)); let c4:Nat→ Nat→ Nat:=Nat.mul; let c5:Nat:=Env.vars c3 "infl.a"; let c6:Nat:=c4 c5 c5; let c7:Env:=Env.setVar c3 "rat.n" c6; let c8:Nat:=Env.vars c7 "ell.epsden"; let c9:Nat:=c4 c8 c8; let c10:Env:=Env.setVar c7 "rat.d" c9; let c11:Env→ Nat→ Prop:=Run B normalizeFraction c10; let c12:Nat→ Nat→ Nat:= @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))); let c13:Nat:=c12 E ((2:Nat)); let c14:Nat→ Nat:=c0 (c4 ((36:Nat)) (Nat.size c13)); let c15:Nat:=c14 ((16:Nat)); let c16:Nat:=c12 (c0 E ((1:Nat))) ((2:Nat)); let c17:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) c16 c13); let c18:Env→ Prop:=fun (σ':Env) => And (c11 σ' c15) (c17 σ'); let c19:Nat:=c14 ((30:Nat)); let c20:Env→ Prop:=FractionOutput (@HPow.hPow Rat Nat Rat (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid))) (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@Nat.cast Rat Rat.instNatCast E))) ((2:Nat))); let c21:Env→ Prop:=(fun (x τ:Env) => c20 τ) σ; let c22:Env→ Prop:=fun (σ':Env) => And (Run B inflationFraction σ σ' c19) (c21 σ'); let c23:Prop:= @Exists Env c22; let c24:String→ Nat:=Env.vars c10; let c25:Nat→ Nat:=c0 ((1:Nat)); let c26:Expr:=Expr.add (Expr.var "ell.epsden") (Expr.lit ((1:Nat))); let c27:Nat:=c25 (Expr.size c26); let c28:Nat:=c25 (Expr.size (Expr.lit ((0:Nat)))); let c29:Nat:=c25 (Expr.size (Expr.mul (Expr.var "infl.a") (Expr.var "infl.a"))); let c30:Nat:=c25 (Expr.size (Expr.mul (Expr.var "ell.epsden") (Expr.var "ell.epsden"))); let c31:Nat:=c0 c30 c15; let c32:Nat:=c0 c29 c31; let c33:Nat:=c0 c28 c32; let c34:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c35:Com:=Com.assign "rat.n" (Expr.mul (Expr.var "infl.a") (Expr.var "infl.a")); let c36:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "ell.epsden") (Expr.var "ell.epsden")); let c37:Com:=Com.seq c36 normalizeFraction; let c38:Com:=Com.seq c35 c37; @Exists.casesOn Env c18 (fun (x:@Exists Env c18) => c23) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c16) (And (@Eq Nat (Env.vars σ_1 "rat.d") c13) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c17 σ') c15 hnorm c10 ?_) fun (w:Env) (h:And (c11 w c15) (c17 w)) => @And.casesOn (c11 w c15) (c17 w) (fun (x:And (c11 w c15) (c17 w)) => c23) h fun (left:c11 w c15) (right:c17 w) => @Exists.intro Env c22 w (@And.intro (Run B inflationFraction σ w c19) (c21 w) (RunStep.mono B inflationFraction σ w (c0 c27 c33) c19 (RunStep.seq B (Com.assign "infl.a" c26) (Com.seq c34 c38) σ c2 w c27 c33 (RunStep.assign B σ "infl.a" c26 c1 (RunStep.eval_add B σ (Expr.var "ell.epsden") (Expr.lit ((1:Nat))) (Env.vars σ "ell.epsden") ((1:Nat)) (RunStep.eval_var B σ "ell.epsden" (?nAX_g4282_0_0_0)) (RunStep.eval_lit B ((1:Nat)) σ h1) (?nAX_g4282_0_0_1))) (RunStep.seq B c34 c38 c2 c3 w c28 c32 (RunStep.assign B c2 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c2 (?nAX_g4282_0_0_2))) (RunStep.seq B c35 c37 c3 c7 w c29 c31 (RunStep.assign B c3 "rat.n" (Expr.mul (Expr.var "infl.a") (Expr.var "infl.a")) c6 (RunStep.eval_mul B c3 (Expr.var "infl.a") (Expr.var "infl.a") c5 c5 (RunStep.eval_var B c3 "infl.a" (?nAX_g4282_0_0_3)) (RunStep.eval_var B c3 "infl.a" (?nAX_g4282_0_0_4)) ?_)) (RunStep.seq B c36 normalizeFraction c7 c10 w c30 c15 (RunStep.assign B c7 "rat.d" (Expr.mul (Expr.var "ell.epsden") (Expr.var "ell.epsden")) c9 (RunStep.eval_mul B c7 (Expr.var "ell.epsden") (Expr.var "ell.epsden") c8 c8 (RunStep.eval_var B c7 "ell.epsden" (?nAX_g4282_0_0_5)) (RunStep.eval_var B c7 "ell.epsden" (?nAX_g4282_0_0_6)) ?_)) left)))) (?nAX_g4282_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4282_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4282_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnorm
  all_goals simp_all [pow_two]

theorem inflationFraction_cost (E:ℕ):
    36 * (E ^ 2).size + 30≤ 72 * E.size + 66:=by
  have hp:=size_pow_le E 2
  omega

theorem positive_num_ratio (q:ℚ) (hq:0 < q):(q.num.natAbs:ℚ) / q.den=q:=by
  have hnum:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hcast:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) hnum
  rw [hcast,q.num_div_den]

theorem betaFraction_spec (B n M:ℕ) (q:ℚ) (hqpos:0 < q) (hq:Height q M)
    (hn:n≤ M) (hB:2 * M ^ 2 + 3 < B):
    Spec B (fun σ => FormOutput q σ∧ σ.vars "vec.n"=n) betaFraction
      (fun _ τ => FractionOutput (2 / (((n:ℚ) + 1) * q)) τ)
      (36 * ((n + 1) * q.num.natAbs).size + 30):=by
  have hM:1≤ M:=le_trans q.den_pos hq.2
  have hMB:M < B:=by nlinarith
  have hnB:=hn.trans_lt hMB
  have h1:1 < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  have hqnB:=hq.1.trans_lt hMB
  have hqdB:=hq.2.trans_lt hMB
  have hnpB:n + 1 < B:=by nlinarith
  have hqnumpos:0 < q.num.natAbs:=Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqpos))
  have hbetaN:2 * q.den < B:=by nlinarith [hq.2]
  have hmul:=Nat.mul_le_mul (by omega:n + 1≤ M + 1) hq.1
  have hbetaD:(n + 1) * q.num.natAbs < B:=by nlinarith
  have hnorm:=normalizeFraction_output_spec B 0 (2 * q.den) ((n + 1) * q.num.natAbs)
    (by omega) hbetaN hbetaD (Nat.mul_pos (by omega) hqnumpos)
  have hval:fractionValue 0 (2 * q.den) ((n + 1) * q.num.natAbs) =
      2 / (((n:ℚ) + 1) * q):=by
    conv_rhs => rw [← positive_num_ratio q hqpos]
    simp only [fractionValue,show (0:ℕ) ≠ 1 by decide,ite_false,Nat.cast_mul,
      Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    field_simp
  rintro σ ⟨hσq,hσn⟩
  have hnum:=hσq.2.1
  have hden:=hσq.2.2.1
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat→ Nat:=c1 ((2:Nat)); let c3:Nat:=Env.vars c0 "ell.form.d"; let c4:Nat:=c2 c3; let c5:Env:=Env.setVar c0 "rat.n" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:=Env.vars c5 "vec.n"; let c8:Nat:=c6 c7 ((1:Nat)); let c9:Env:=Env.setVar c5 "beta.nplus" c8; let c10:String→ Nat:=Env.vars c9; let c11:Nat:=c10 "beta.nplus"; let c12:Nat:=c10 "ell.form.n"; let c13:Nat:=c1 c11 c12; let c14:Env:=Env.setVar c9 "rat.d" c13; let c15:Env→ Nat→ Prop:=Run B normalizeFraction c14; let c16:Nat:=c1 (c6 n ((1:Nat))) (Int.natAbs (Rat.num q)); let c17:Nat→ Nat:=c6 (c1 ((36:Nat)) (Nat.size c16)); let c18:Nat:=c17 ((16:Nat)); let c19:Nat:=c2 (Rat.den q); let c20:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) c19 c16); let c21:Env→ Prop:=fun (σ':Env) => And (c15 σ' c18) (c20 σ'); let c22:Nat:=c17 ((30:Nat)); let c23:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@Nat.cast Rat Rat.instNatCast n) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) q)); let c24:Env→ Prop:=(fun (x τ:Env) => c23 τ) σ; let c25:Env→ Prop:=fun (σ':Env) => And (Run B betaFraction σ σ' c22) (c24 σ'); let c26:String→ Nat:=Env.vars c14; let c27:Nat→ Nat:=c6 ((1:Nat)); let c28:Nat:=c27 (Expr.size (Expr.lit ((0:Nat)))); let c29:Expr:=Expr.mul (Expr.lit ((2:Nat))) (Expr.var "ell.form.d"); let c30:Nat:=c27 (Expr.size c29); let c31:Expr:=Expr.add (Expr.var "vec.n") (Expr.lit ((1:Nat))); let c32:Nat:=c27 (Expr.size c31); let c33:Nat:=c27 (Expr.size (Expr.mul (Expr.var "beta.nplus") (Expr.var "ell.form.n"))); let c34:Nat:=c6 c33 c18; let c35:Nat:=c6 c32 c34; let c36:Nat:=c6 c30 c35; let c37:Com:=Com.assign "rat.n" c29; let c38:Com:=Com.assign "beta.nplus" c31; let c39:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "beta.nplus") (Expr.var "ell.form.n")); let c40:Com:=Com.seq c39 normalizeFraction; let c41:Com:=Com.seq c38 c40; @Exists.casesOn Env c21 (fun (x:@Exists Env c21) => @Exists Env c25) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c19) (And (@Eq Nat (Env.vars σ_1 "rat.d") c16) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c20 σ') c18 hnorm c14 ?_) fun (w:Env) (h:And (c15 w c18) (c20 w)) => @And.casesOn (c15 w c18) (c20 w) (fun (x:And (c15 w c18) (c20 w)) => @Exists Env c25) h fun (left:c15 w c18) (right:c20 w) => @Exists.intro Env c25 w (@And.intro (Run B betaFraction σ w c22) (c24 w) (RunStep.mono B betaFraction σ w (c6 c28 c36) c22 (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c37 c41) σ c0 w c28 c36 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4289_0_0_0))) (RunStep.seq B c37 c41 c0 c5 w c30 c35 (RunStep.assign B c0 "rat.n" c29 c4 (RunStep.eval_mul B c0 (Expr.lit ((2:Nat))) (Expr.var "ell.form.d") ((2:Nat)) c3 (RunStep.eval_lit B ((2:Nat)) c0 h2) (RunStep.eval_var B c0 "ell.form.d" (?nAX_g4289_0_0_1)) (?nAX_g4289_0_0_2))) (RunStep.seq B c38 c40 c5 c9 w c32 c34 (RunStep.assign B c5 "beta.nplus" c31 c8 (RunStep.eval_add B c5 (Expr.var "vec.n") (Expr.lit ((1:Nat))) c7 ((1:Nat)) (RunStep.eval_var B c5 "vec.n" (?nAX_g4289_0_0_3)) (RunStep.eval_lit B ((1:Nat)) c5 h1) (?nAX_g4289_0_0_4))) (RunStep.seq B c39 normalizeFraction c9 c14 w c33 c18 (RunStep.assign B c9 "rat.d" (Expr.mul (Expr.var "beta.nplus") (Expr.var "ell.form.n")) c13 (RunStep.eval_mul B c9 (Expr.var "beta.nplus") (Expr.var "ell.form.n") c11 c12 (RunStep.eval_var B c9 "beta.nplus" (?nAX_g4289_0_0_5)) (RunStep.eval_var B c9 "ell.form.n" (?nAX_g4289_0_0_6)) ?_)) left)))) (?nAX_g4289_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4289_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4289_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnorm
  all_goals simp_all

theorem betaFraction_cost (n M:ℕ) (q:ℚ) (hn:n≤ M) (hq:Height q M):
    36 * ((n + 1) * q.num.natAbs).size + 30≤ 72 * M.size + 66:=by
  have hm:=size_mul_le (n + 1) q.num.natAbs
  have hp:=size_add_one_le n
  have hnsize:=Nat.size_le_size hn
  have hqsize:=Nat.size_le_size hq.1
  omega

theorem scaledInverseFraction_spec (B n M:ℕ) (q:ℚ) (hqpos:0 < q) (hq:Height q M)
    (hn:n≤ M) (hB:2 * M ^ 2 + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "vec.n"=n) scaledInverseFraction
      (fun _ τ => FractionOutput (1 / (((n:ℚ) + 1) * q)) τ)
      (36 * ((n + 1) * q.num.natAbs).size + 30):=by
  have hM:1≤ M:=le_trans q.den_pos hq.2
  have hMB:M < B:=by nlinarith
  have hnB:=hn.trans_lt hMB
  have h1:1 < B:=by nlinarith
  have hqnB:=hq.1.trans_lt hMB
  have hqdB:=hq.2.trans_lt hMB
  have hnpB:n + 1 < B:=by nlinarith
  have hqnumpos:0 < q.num.natAbs:=Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hqpos))
  have hmul:=Nat.mul_le_mul (by omega:n + 1≤ M + 1) hq.1
  have hgammaD:(n + 1) * q.num.natAbs < B:=by nlinarith
  have hnorm:=normalizeFraction_output_spec B 0 q.den ((n + 1) * q.num.natAbs)
    (by omega) hqdB hgammaD (Nat.mul_pos (by omega) hqnumpos)
  have hval:fractionValue 0 q.den ((n + 1) * q.num.natAbs) =
      1 / (((n:ℚ) + 1) * q):=by
    conv_rhs => rw [← positive_num_ratio q hqpos]
    simp only [fractionValue,show (0:ℕ) ≠ 1 by decide,ite_false,Nat.cast_mul,
      Nat.cast_add,Nat.cast_one]
    field_simp
  rintro σ ⟨hσq,hσn⟩
  have hnum:=hσq.2.1
  have hden:=hσq.2.2.1
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=Env.vars (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) "vec.n"; let c2:Nat:=c0 c1 ((1:Nat)); let c3:Env:=Env.setVar (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) "gamma.nplus" c2; let c4:Nat:=Env.vars c3 "rat.d"; let c5:Env:=Env.setVar c3 "rat.n" c4; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:String→ Nat:=Env.vars c5; let c8:Nat:=c7 "gamma.nplus"; let c9:Nat:=c7 "gamma.rootn"; let c10:Nat:=c6 c8 c9; let c11:Env:=Env.setVar c5 "rat.d" c10; let c12:Env:=Env.setVar c11 "rat.s" ((0:Nat)); let c13:Env→ Nat→ Prop:=Run B normalizeFraction c12; let c14:Nat:=c6 (c0 n ((1:Nat))) (Int.natAbs (Rat.num q)); let c15:Nat→ Nat:=c0 (c6 ((36:Nat)) (Nat.size c14)); let c16:Nat:=c15 ((16:Nat)); let c17:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) (Rat.den q) c14); let c18:Env→ Prop:=fun (σ':Env) => And (c13 σ' c16) (c17 σ'); let c19:Nat:=c15 ((30:Nat)); let c20:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@Nat.cast Rat Rat.instNatCast n) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) q)); let c21:Env→ Prop:=(fun (x τ:Env) => c20 τ) σ; let c22:Env→ Prop:=fun (σ':Env) => And (Run B scaledInverseFraction σ σ' c19) (c21 σ'); let c23:String→ Nat:=Env.vars c12; let c24:Nat→ Nat:=c0 ((1:Nat)); let c25:Nat:=c24 (Expr.size (Expr.var "rat.n")); let c26:Expr:=Expr.add (Expr.var "vec.n") (Expr.lit ((1:Nat))); let c27:Nat:=c24 (Expr.size c26); let c28:Nat:=c24 (Expr.size (Expr.var "rat.d")); let c29:Nat:=c24 (Expr.size (Expr.mul (Expr.var "gamma.nplus") (Expr.var "gamma.rootn"))); let c30:Nat:=c24 (Expr.size (Expr.lit ((0:Nat)))); let c31:Nat:=c0 c30 c16; let c32:Nat:=c0 c29 c31; let c33:Nat:=c0 c28 c32; let c34:Nat:=c0 c27 c33; let c35:Com:=Com.assign "gamma.nplus" c26; let c36:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "gamma.nplus") (Expr.var "gamma.rootn")); let c37:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c38:Com:=Com.seq c37 normalizeFraction; let c39:Com:=Com.seq c36 c38; let c40:Com:=Com.seq (Com.assign "rat.n" (Expr.var "rat.d")) c39; @Exists.casesOn Env c18 (fun (x:@Exists Env c18) => @Exists Env c22) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") (Rat.den q)) (And (@Eq Nat (Env.vars σ_1 "rat.d") c14) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c17 σ') c16 hnorm c12 ?_) fun (w:Env) (h:And (c13 w c16) (c17 w)) => @And.casesOn (c13 w c16) (c17 w) (fun (x:And (c13 w c16) (c17 w)) => @Exists Env c22) h fun (left:c13 w c16) (right:c17 w) => @Exists.intro Env c22 w (@And.intro (Run B scaledInverseFraction σ w c19) (c21 w) (RunStep.mono B scaledInverseFraction σ w (c0 c25 c34) c19 (RunStep.seq B (Com.assign "gamma.rootn" (Expr.var "rat.n")) (Com.seq c35 c40) σ (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) w c25 c34 (RunStep.assign B σ "gamma.rootn" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g4292_0_0_0))) (RunStep.seq B c35 c40 (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) c3 w c27 c33 (RunStep.assign B (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) "gamma.nplus" c26 c2 (RunStep.eval_add B (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) (Expr.var "vec.n") (Expr.lit ((1:Nat))) c1 ((1:Nat)) (RunStep.eval_var B (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) "vec.n" (?nAX_g4292_0_0_1)) (RunStep.eval_lit B ((1:Nat)) (Env.setVar σ "gamma.rootn" (Env.vars σ "rat.n")) h1) (?nAX_g4292_0_0_2))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "rat.d")) c39 c3 c5 w c28 c32 (RunStep.assign B c3 "rat.n" (Expr.var "rat.d") c4 (RunStep.eval_var B c3 "rat.d" (?nAX_g4292_0_0_3))) (RunStep.seq B c36 c38 c5 c11 w c29 c31 (RunStep.assign B c5 "rat.d" (Expr.mul (Expr.var "gamma.nplus") (Expr.var "gamma.rootn")) c10 (RunStep.eval_mul B c5 (Expr.var "gamma.nplus") (Expr.var "gamma.rootn") c8 c9 (RunStep.eval_var B c5 "gamma.nplus" (?nAX_g4292_0_0_4)) (RunStep.eval_var B c5 "gamma.rootn" (?nAX_g4292_0_0_5)) ?_)) (RunStep.seq B c37 normalizeFraction c11 c12 w c30 c16 (RunStep.assign B c11 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c11 (?nAX_g4292_0_0_6))) left))))) (?nAX_g4292_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4292_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4292_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnorm
  all_goals simp_all

theorem scaledInverseFraction_uniform_spec (B n M:ℕ) (q:ℚ)
    (hqpos:0 < q) (hq:Height q M) (hn:n≤ M) (hB:2 * M ^ 2 + 3 < B):
    Spec B (fun σ => FractionOutput q σ∧ σ.vars "vec.n"=n) scaledInverseFraction
      (fun _ τ => FractionOutput (1 / (((n:ℚ) + 1) * q)) τ) (72 * M.size + 66):=
  (scaledInverseFraction_spec B n M q hqpos hq hn hB).mono (betaFraction_cost n M q hn hq)

theorem sqrtUpper_pos (q:ℚ) (D:ℕ) (hD:0 < D):0 < RationalRounding.sqrtUpper q D:=by
  unfold RationalRounding.sqrtUpper
  positivity

set_option maxHeartbeats 0 in
theorem gammaFraction_spec (B n M D:ℕ) (q:ℚ) (hq:Height q M)
    (hn:n≤ M) (hD:D≤ M) (hDpos:0 < D)
    (hB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B):
    Spec B (fun σ => FormOutput q σ∧ σ.vars "vec.n"=n∧ σ.vars "grid.D"=D)
      gammaFraction
      (fun _ τ => FractionOutput (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper q D)) τ)
      (6 + (114 * M.size + 180 + (72 * (M ^ 3 + 1).size + 66))):=by
  have hM:1≤ M:=le_trans q.den_pos hq.2
  have hMpow:M≤ M ^ 3 + 1:=by
    have hp:=le_self_pow hM (by decide:(3:ℕ) ≠ 0)
    omega
  have hMB:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hqnB:=hq.1.trans_lt hMB
  have hqdB:=hq.2.trans_lt hMB
  have hnM:=hn.trans hMpow
  have hB₂:2 * (M ^ 3 + 1) ^ 2 + 3 < B:=by nlinarith
  have hsqrt:Height (RationalRounding.sqrtUpper q D) (M ^ 3 + 1):=by
    have ht:=EllipsoidArithmeticBounds.height_sqrtUpper q M D hq hDpos
    have hm:=Nat.mul_le_mul_left M (Nat.pow_le_pow_left hD 2)
    exact height_mono _ ht (by nlinarith)
  have hinv:=scaledInverseFraction_uniform_spec B n (M ^ 3 + 1)
    (RationalRounding.sqrtUpper q D) (sqrtUpper_pos q D hDpos) hsqrt hnM hB₂
  rintro σ ⟨hσq,hσn,hσD⟩
  have hqval:=hσq.1
  have hqnum:=hσq.2.1
  have hqden:=hσq.2.2.1
  have hqs:=hσq.2.2.2.trans_lt h1
  have hroot:=upperRootFraction_uniform_spec B M (σ.vars "ell.form.s") q.num.natAbs q.den D
    hB hσq.2.2.2 hq.1 hq.2 hD q.den_pos hDpos
  have hframe:=spec_with_fields ["vec.n"] hroot
    (by
      intro x hx
      simp at hx
      subst x
      simp [upperRootFraction,RamSquareRoot.squareRoot,RamSquareRoot.sqrtLoop,
        RamSquareRoot.sqrtStep,normalizeFraction,gcdLoop,gcdDoubleStep,gcdStep,Com.wvars])
    (by simp [upperRootFraction,RamSquareRoot.squareRoot,RamSquareRoot.sqrtLoop,
        RamSquareRoot.sqrtStep,normalizeFraction,gcdLoop,gcdDoubleStep,gcdStep,Com.warrs])
  clear hroot
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) "ell.form.n"; let c1:Env:=Env.setVar (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) "left.n" c0; let c2:Nat:=Env.vars c1 "ell.form.d"; let c3:Env:=Env.setVar c1 "left.d" c2; let c4:Env→ Nat→ Prop:=Run B upperRootFraction c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c5 (c6 ((114:Nat)) (Nat.size M)) ((180:Nat)); let c8:Env→ Prop:=FractionOutput (RationalRounding.sqrtUpper (fractionValue (Env.vars σ "ell.form.s") (Int.natAbs (Rat.num q)) (Rat.den q)) D); let c9:Env→ Prop:=FieldsAgree (@List.cons String "vec.n" (@List.nil String)) c3; let c10:String→ List Nat:=Env.arrs c3; let c11:Env→ Prop:=fun (σ':Env) => And (c4 σ' c7) (And (c8 σ') (And (c9 σ') (@Eq (String→ List Nat) (Env.arrs σ') c10))); let c12:Nat:=c5 (c6 ((72:Nat)) (Nat.size (c5 (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M ((3:Nat))) ((1:Nat))))) ((66:Nat)); let c13:Nat:=c5 c7 c12; let c14:Nat:=c5 ((6:Nat)) c13; let c15:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd) (@Nat.cast Rat Rat.instNatCast n) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))) (RationalRounding.sqrtUpper q D))); let c16:Env→ Env→ Prop:=fun (x τ:Env) => c15 τ; let c17:Env→ Prop:=c16 σ; let c18:Env→ Prop:=fun (σ':Env) => And (Run B gammaFraction σ σ' c14) (c17 σ'); let c19:String→ Nat:=Env.vars c3; let c20:Nat→ Nat:=c5 ((1:Nat)); let c21:Nat:=c20 (Expr.size (Expr.var "ell.form.s")); let c22:Nat:=c20 (Expr.size (Expr.var "ell.form.n")); let c23:Nat:=c20 (Expr.size (Expr.var "ell.form.d")); let c24:Nat:=c5 c23 c13; let c25:Nat:=c5 c22 c24; let c26:Com:=Com.seq (Com.assign "left.d" (Expr.var "ell.form.d")) (Com.seq upperRootFraction scaledInverseFraction); @Exists.casesOn Env c11 (fun (x:@Exists Env c11) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "left.s") (Env.vars σ "ell.form.s")) (And (@Eq Nat (Env.vars σ_1 "left.n") (Int.natAbs (Rat.num q))) (And (@Eq Nat (Env.vars σ_1 "left.d") (Rat.den q)) (@Eq Nat (Env.vars σ_1 "grid.D") D)))) upperRootFraction (fun (σ_1 τ:Env) => And (c8 τ) (And (FieldsAgree (@List.cons String "vec.n" (@List.nil String)) σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) c7 hframe c3 ?_) fun (w:Env) (h:And (c4 w c7) (And (c8 w) (And (c9 w) (@Eq (String→ List Nat) (Env.arrs w) c10)))) => let c0_1:Prop:=And (c8 w) (And (c9 w) (@Eq (String→ List Nat) (Env.arrs w) c10)); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B scaledInverseFraction w σ' c12) (c15 σ'); @And.casesOn (c4 w c7) c0_1 (fun (x:And (c4 w c7) c0_1) => @Exists Env c18) h fun (left:c4 w c7) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c18) (RunStep.use B (fun (σ_1:Env) => And (FractionOutput (RationalRounding.sqrtUpper q D) σ_1) (@Eq Nat (Env.vars σ_1 "vec.n") n)) scaledInverseFraction c16 c12 hinv w ?_) fun (w_1:Env) (h_1:And (Run B scaledInverseFraction w w_1 c12) (c15 w_1)) => @And.casesOn (Run B scaledInverseFraction w w_1 c12) (c15 w_1) (fun (x:And (Run B scaledInverseFraction w w_1 c12) (c15 w_1)) => @Exists Env c18) h_1 fun (left_1:Run B scaledInverseFraction w w_1 c12) (right_1:c15 w_1) => @Exists.intro Env c18 w_1 (@And.intro (Run B gammaFraction σ w_1 c14) (c17 w_1) (RunStep.mono B gammaFraction σ w_1 (c5 c21 c25) c14 (RunStep.seq B (Com.assign "left.s" (Expr.var "ell.form.s")) (Com.seq (Com.assign "left.n" (Expr.var "ell.form.n")) c26) σ (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) w_1 c21 c25 (RunStep.assign B σ "left.s" (Expr.var "ell.form.s") (Env.vars σ "ell.form.s") (RunStep.eval_var B σ "ell.form.s" hqs)) (RunStep.seq B (Com.assign "left.n" (Expr.var "ell.form.n")) c26 (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) c1 w_1 c22 c24 (RunStep.assign B (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) "left.n" (Expr.var "ell.form.n") c0 (RunStep.eval_var B (Env.setVar σ "left.s" (Env.vars σ "ell.form.s")) "ell.form.n" (?nAX_g4296_0_0_0))) (RunStep.seq B (Com.assign "left.d" (Expr.var "ell.form.d")) (Com.seq upperRootFraction scaledInverseFraction) c1 c3 w_1 c23 c13 (RunStep.assign B c1 "left.d" (Expr.var "ell.form.d") c2 (RunStep.eval_var B c1 "ell.form.d" (?nAX_g4296_0_0_1))) (RunStep.seq B upperRootFraction scaledInverseFraction c3 w w_1 c7 c12 left left_1)))) (?nAX_g4296_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4296_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4296_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4296_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hframe hinv
  all_goals simp_all [FormOutput,FractionOutput,FieldsAgree]
  all_goals aesop

theorem gammaFraction_cost (M:ℕ):
    6 + (114 * M.size + 180 + (72 * (M ^ 3 + 1).size + 66))≤ 330 * M.size + 396:=by
  have hp:=size_pow_le M 3
  have ha:=size_add_one_le (M ^ 3)
  omega

theorem diagonalFraction_spec (B n D:ℕ) (hn:n < B) (hD:D < B) (hDpos:0 < D):
    Spec B (fun σ => σ.vars "vec.n"=n∧ σ.vars "grid.D"=D) diagonalFraction
      (fun _ τ => FractionOutput ((n:ℚ) / D) τ) (36 * D.size + 22):=by
  have hnorm:=normalizeFraction_output_spec B 0 n D (by omega) hn hD hDpos
  have h0:0 < B:=hDpos.trans hD
  have hval:fractionValue 0 n D=(n:ℚ) / D:=by simp [fractionValue]
  rintro σ ⟨hσn,hσD⟩
  (expose_names;
    (refine let c0:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c1:Nat:=Env.vars c0 "vec.n"; let c2:Env:=Env.setVar c0 "rat.n" c1; let c3:Nat:=Env.vars c2 "grid.D"; let c4:Env:=Env.setVar c2 "rat.d" c3; let c5:Env→ Nat→ Prop:=Run B normalizeFraction c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 (Nat.mul ((36:Nat)) (Nat.size D)); let c8:Nat:=c7 ((16:Nat)); let c9:Env→ Prop:=FractionOutput (fractionValue ((0:Nat)) n D); let c10:Env→ Prop:=fun (σ':Env) => And (c5 σ' c8) (c9 σ'); let c11:Nat:=c7 ((22:Nat)); let c12:Env→ Prop:=FractionOutput (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv) (@Nat.cast Rat Rat.instNatCast n) (@Nat.cast Rat Rat.instNatCast D)); let c13:Env→ Prop:=(fun (x τ:Env) => c12 τ) σ; let c14:Env→ Prop:=fun (σ':Env) => And (Run B diagonalFraction σ σ' c11) (c13 σ'); let c15:Prop:= @Exists Env c14; let c16:String→ Nat:=Env.vars c4; let c17:Nat→ Nat:=c6 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.lit ((0:Nat)))); let c19:Nat:=c17 (Expr.size (Expr.var "vec.n")); let c20:Nat:=c17 (Expr.size (Expr.var "grid.D")); let c21:Nat:=c6 c20 c8; let c22:Nat:=c6 c19 c21; @Exists.casesOn Env c10 (fun (x:@Exists Env c10) => c15) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") n) (And (@Eq Nat (Env.vars σ_1 "rat.d") D) (@Eq Nat (Env.vars σ_1 "rat.s") ((0:Nat))))) normalizeFraction (fun (x σ':Env) => c9 σ') c8 hnorm c4 ?_) fun (w:Env) (h:And (c5 w c8) (c9 w)) => @And.casesOn (c5 w c8) (c9 w) (fun (x:And (c5 w c8) (c9 w)) => c15) h fun (left:c5 w c8) (right:c9 w) => @Exists.intro Env c14 w (@And.intro (Run B diagonalFraction σ w c11) (c13 w) (RunStep.mono B diagonalFraction σ w (c6 c18 c22) c11 (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.var "vec.n")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction)) σ c0 w c18 c22 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ h0)) (RunStep.seq B (Com.assign "rat.n" (Expr.var "vec.n")) (Com.seq (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction) c0 c2 w c19 c21 (RunStep.assign B c0 "rat.n" (Expr.var "vec.n") c1 (RunStep.eval_var B c0 "vec.n" (?nAX_g4299_0_0_0))) (RunStep.seq B (Com.assign "rat.d" (Expr.var "grid.D")) normalizeFraction c2 c4 w c20 c8 (RunStep.assign B c2 "rat.d" (Expr.var "grid.D") c3 (RunStep.eval_var B c2 "grid.D" (?nAX_g4299_0_0_1))) left))) (?nAX_g4299_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4299_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4299_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4299_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals clear hnorm
  all_goals simp_all

end Lax109476Proofs.RamEllipsoidScalars

end

section

namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds

def scalarFields:List String:=
  ["vec.n", "grid.D", "ell.form.s", "ell.form.n", "ell.form.d", "ell.epsden"]

theorem storeCoefficient_spec (B i:ℕ) (gs:List ℚ) (q:ℚ)
    (hi:i < gs.length) (hiB:i < B) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => Represents "ell.coeff" gs σ∧ FractionOutput q σ) (storeCoefficient i)
      (fun _ τ => Represents "ell.coeff" (gs.set i q) τ) 15:=by
  rintro σ ⟨hσg,hσq⟩
  have hr₁:Run B (.assign "vec.i" (.lit i)) σ (σ.setVar "vec.i" i) 2:=
    Run.assign (evalB_lit hiB)
  obtain ⟨τ,hr₂,hτ⟩:=storeReduced_spec B "ell.coeff" gs q i hi h1 hiB hn hd
    (σ.setVar "vec.i" i) ⟨by simpa [Represents] using hσg,by simp,
      by simpa [FractionOutput] using hσq⟩
  exact ⟨τ,hr₁.seq hr₂,hτ⟩

theorem scalar_frames (c:Com)
    (hc:c∈ [alphaFraction,betaFraction,gammaFraction,inflationFraction,diagonalFraction]):
    (∀ x∈ scalarFields,x∉ c.wvars)∧ c.warrs=[]:=by
  simp at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try (intro x hx; simp [scalarFields] at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals simp [alphaFraction,betaFraction,gammaFraction,scaledInverseFraction,inflationFraction,
    diagonalFraction,RamRounding.upperRootFraction,RamSquareRoot.squareRoot,RamSquareRoot.sqrtLoop,
    RamSquareRoot.sqrtStep,RamArithmetic.normalizeFraction,RamArithmetic.gcdLoop,
    RamArithmetic.gcdDoubleStep,RamArithmetic.gcdStep,Com.wvars,Com.warrs]

theorem computeAndStore_spec {B K:ℕ} {P:Env→ Prop} (c:Com) (i:ℕ) (gs:List ℚ) (q:ℚ)
    (hc:c∈ [alphaFraction,betaFraction,gammaFraction,inflationFraction,diagonalFraction])
    (hprod:Spec B P c (fun _ τ => FractionOutput q τ) K)
    (hi:i < gs.length) (hiB:i < B) (h1:1 < B)
    (hn:q.num.natAbs < B) (hd:q.den < B):
    Spec B (fun σ => P σ∧ Represents "ell.coeff" gs σ) (computeAndStore c i)
      (fun σ τ => Represents "ell.coeff" (gs.set i q) τ∧ FieldsAgree scalarFields σ τ∧
        ∀ a∉ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"],τ.arrs a=σ.arrs a)
      (K + 15):=by
  have hproducer:=spec_with_fields scalarFields hprod (scalar_frames c hc).1 (scalar_frames c hc).2
  have hstore:=spec_with_write_frame scalarFields
    (storeCoefficient_spec B i gs q hi hiB h1 hn hd)
    (by
      intro x hx
      simp [scalarFields] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [storeCoefficient,storeReduced,Com.wvars])
  rintro σ ⟨hσP,hσg⟩
  (expose_names;
    (refine let c0:Env→ Prop:=fun (σ':Env) => And (Run B c σ σ' K) (And (FractionOutput q σ') (And (FieldsAgree scalarFields σ σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c1:Nat:=Nat.add K ((15:Nat)); let c2:Env→ Prop:=Represents "ell.coeff" (@List.set Rat gs i q); let c3:Env→ Prop:=(fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree scalarFields σ_1 τ) (∀ a∉ @List.cons String "ell.coeff.s" (@List.cons String "ell.coeff.n" (@List.cons String "ell.coeff.d" (@List.nil String))), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B (computeAndStore c i) σ σ' c1) (c3 σ'); let c5:Prop:= @Exists Env c4; @Exists.casesOn Env c0 (fun (x:@Exists Env c0) => c5) (RunStep.use B P c (fun (σ_1 τ:Env) => And (FractionOutput q τ) (And (FieldsAgree scalarFields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) K hproducer σ ?_) fun (w:Env) (h:And (Run B c σ w K) (And (FractionOutput q w) (And (FieldsAgree scalarFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=And (FractionOutput q w) (And (FieldsAgree scalarFields σ w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B (storeCoefficient i) w σ' ((15:Nat))) (And (c2 σ') (And (FieldsAgree scalarFields w σ') (∀ a∉ Com.warrs (storeCoefficient i), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs w a)))); @And.casesOn (Run B c σ w K) c0_1 (fun (x:And (Run B c σ w K) c0_1) => c5) h fun (left:Run B c σ w K) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => c5) (RunStep.use B (fun (σ_1:Env) => And (Represents "ell.coeff" gs σ_1) (FractionOutput q σ_1)) (storeCoefficient i) (fun (σ_1 τ:Env) => And (c2 τ) (And (FieldsAgree scalarFields σ_1 τ) (∀ a∉ Com.warrs (storeCoefficient i), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((15:Nat)) hstore w ?_) fun (w_1:Env) (h_1:And (Run B (storeCoefficient i) w w_1 ((15:Nat))) (And (c2 w_1) (And (FieldsAgree scalarFields w w_1) (∀ a∉ Com.warrs (storeCoefficient i), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs w a))))) => let c0_2:Prop:=Run B (storeCoefficient i) w w_1 ((15:Nat)); let c1_2:Prop:=And (c2 w_1) (And (FieldsAgree scalarFields w w_1) (∀ a∉ Com.warrs (storeCoefficient i), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs w a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c5) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c4 w_1 (@And.intro (Run B (computeAndStore c i) σ w_1 c1) (c3 w_1) (RunStep.mono B (computeAndStore c i) σ w_1 c1 c1 (RunStep.seq B c (storeCoefficient i) σ w w_1 K ((15:Nat)) left left_1) (?nAX_g4305_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4305_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hproducer hstore hprod
  all_goals simp_all [Represents,FieldsAgree,scalarFields,storeCoefficient,storeReduced,Com.warrs]

theorem scalarInput_frame (n:ℕ) (q:ℚ) (D E:ℕ) (σ τ:Env)
    (hσ:ScalarInput n q D E σ) (hf:FieldsAgree scalarFields σ τ):ScalarInput n q D E τ:=by
  simpa only [ScalarInput,FormOutput,hf "vec.n" (by simp [scalarFields]),
    hf "grid.D" (by simp [scalarFields]),hf "ell.epsden" (by simp [scalarFields]),
    hf "ell.form.s" (by simp [scalarFields]),hf "ell.form.n" (by simp [scalarFields]),
    hf "ell.form.d" (by simp [scalarFields])] using hσ

theorem computeAndStore_input_spec {B K:ℕ} {P:Env→ Prop} (c:Com) (i n D E:ℕ)
    (gs:List ℚ) (q v:ℚ)
    (hc:c∈ [alphaFraction,betaFraction,gammaFraction,inflationFraction,diagonalFraction])
    (hprod:Spec B P c (fun _ τ => FractionOutput v τ) K)
    (hP:∀ σ,ScalarInput n q D E σ→ P σ)
    (hi:i < gs.length) (hiB:i < B) (h1:1 < B)
    (hn:v.num.natAbs < B) (hd:v.den < B):
    Spec B (fun σ => ScalarInput n q D E σ∧ Represents "ell.coeff" gs σ) (computeAndStore c i)
      (fun _ τ => ScalarInput n q D E τ∧ Represents "ell.coeff" (gs.set i v) τ) (K + 15):=by
  intro σ hσ
  obtain ⟨τ,hr,hτg,hf,_⟩:=computeAndStore_spec c i gs v hc hprod hi hiB h1 hn hd
    σ ⟨hP σ hσ.1,hσ.2⟩
  exact ⟨τ,hr,scalarInput_frame n q D E σ τ hσ.1 hf,hτg⟩

set_option maxHeartbeats 0 in
theorem computeCoefficients_spec (B n M C D E:ℕ) (q:ℚ) (hn:2≤ n)
    (hqpos:0 < q) (hq:Height q M) (hnM:n≤ M) (hDM:D≤ M) (hEM:E≤ M)
    (hDpos:0 < D) (hEpos:0 < E) (hnnB:n ^ 2 < B) (hInflB:(E + 1) ^ 2 < B)
    (hPrimB:2 * M ^ 2 + 3 < B)
    (hRootB:(2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B)
    (hCB:C < B) (hcoeff:∀ v∈ coefficients n q D E,Height v C):
    Spec B (fun σ => ScalarInput n q D E σ∧ Represents "ell.coeff" (List.replicate 5 0) σ)
      computeCoefficients
      (fun _ τ => Represents "ell.coeff" (coefficients n q D E) τ∧ ScalarInput n q D E τ)
      (582 * M.size + 687):=by
  have h1:1 < B:=by nlinarith only [hn,hnnB]
  have h4:4 < B:=by nlinarith only [hn,hnnB]
  have hMB:M < B:=by nlinarith only [hPrimB]
  have hnsize:=Nat.size_le_size hnM
  have hDsize:=Nat.size_le_size hDM
  have hEsize:=Nat.size_le_size hEM
  have hα:=hcoeff ((n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1)) (by simp [coefficients])
  have hβ:=hcoeff (2 / (((n:ℚ) + 1) * q)) (by simp [coefficients])
  have hγ:=hcoeff (1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper q D)) (by simp [coefficients])
  have hρ:=hcoeff ((1 + 1 / (E:ℚ)) ^ 2) (by simp [coefficients])
  have hδ:=hcoeff ((n:ℚ) / D) (by simp [coefficients])
  have hαprod:=(alphaFraction_spec B n hn hnnB).mono
    (show 36 * (n ^ 2 - 1).size + 26≤ 72 * M.size + 62 from
      (alphaFraction_cost n).trans (by omega))
  have hβprod:=(betaFraction_spec B n M q hqpos hq hnM hPrimB).mono
    (betaFraction_cost n M q hnM hq)
  have hγprod:=(gammaFraction_spec B n M D q hq hnM hDM hDpos hRootB).mono (gammaFraction_cost M)
  have hρprod:=(inflationFraction_spec B E hEpos hInflB).mono
    (show 36 * (E ^ 2).size + 30≤ 72 * M.size + 66 from
      (inflationFraction_cost E).trans (by omega))
  have hδprod:=(diagonalFraction_spec B n D (hnM.trans_lt hMB) (hDM.trans_lt hMB) hDpos).mono
    (show 36 * D.size + 22≤ 36 * M.size + 22 by omega)
  have hαstore:=computeAndStore_input_spec alphaFraction 0 n D E (List.replicate 5 0) q _ (by simp) hαprod
    (fun _ h => h.2.1) (by simp) (by omega) h1 (hα.1.trans_lt hCB) (hα.2.trans_lt hCB)
  have hβstore:=computeAndStore_input_spec betaFraction 1 n D E
    [(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1),0,0,0,0] q _ (by simp) hβprod
    (fun _ h => ⟨h.1,h.2.1⟩) (by simp) (by omega) h1 (hβ.1.trans_lt hCB) (hβ.2.trans_lt hCB)
  have hγstore:=computeAndStore_input_spec gammaFraction 2 n D E
    [(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1),2 / (((n:ℚ) + 1) * q),0,0,0] q _ (by simp) hγprod
    (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩) (by simp) (by omega) h1 (hγ.1.trans_lt hCB) (hγ.2.trans_lt hCB)
  have hρstore:=computeAndStore_input_spec inflationFraction 3 n D E
    [(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1),2 / (((n:ℚ) + 1) * q),
      1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper q D),0,0] q _ (by simp) hρprod
    (fun _ h => h.2.2.2) (by simp) (by omega) h1 (hρ.1.trans_lt hCB) (hρ.2.trans_lt hCB)
  have hδstore:=computeAndStore_input_spec diagonalFraction 4 n D E
    [(n:ℚ) ^ 2 / ((n:ℚ) ^ 2 - 1),2 / (((n:ℚ) + 1) * q),
      1 / (((n:ℚ) + 1) * RationalRounding.sqrtUpper q D), (1 + 1 / (E:ℚ)) ^ 2,0] q _ (by simp) hδprod
    (fun _ h => ⟨h.2.1,h.2.2.1⟩) (by simp) (by omega) h1 (hδ.1.trans_lt hCB) (hδ.2.trans_lt hCB)
  rintro σ ⟨hσinput,hσg⟩
  (expose_names;
    (refine let c0:Com:=computeAndStore alphaFraction ((0:Nat)); let c1:Env→ Nat→ Prop:=Run B c0 σ; let c2:Nat→ Nat→ Nat:=Nat.add; let c3:Nat→ Nat→ Nat:=Nat.mul; let c4:Nat→ Nat:=c2 (c3 ((72:Nat)) (Nat.size M)); let c5:Nat:=c2 (c4 ((62:Nat))) ((15:Nat)); let c6:List Rat:= @List.replicate Rat ((5:Nat)) (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c7:Rat→ Rat→ Rat:= @HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv); let c8:Rat→ Nat→ Rat:= @HPow.hPow Rat Nat Rat (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid))); let c9:Rat:=c8 (@Nat.cast Rat Rat.instNatCast n) ((2:Nat)); let c10:Rat:=c7 c9 (@HSub.hSub Rat Rat Rat (@instHSub Rat Rat.instSub) c9 (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c11:Env→ Prop:=Represents "ell.coeff" (@List.set Rat c6 ((0:Nat)) c10); let c12:Env→ Prop:=fun (σ':Env) => And (c1 σ' c5) (And (ScalarInput n q D E σ') (c11 σ')); let c13:Nat:=c2 (c3 ((582:Nat)) (Nat.size M)) ((687:Nat)); let c14:Env→ Prop:=Represents "ell.coeff" (coefficients n q D E); let c15:Env→ Prop:=(fun (x τ:Env) => And (c14 τ) (ScalarInput n q D E τ)) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B computeCoefficients σ σ' c13) (c15 σ'); let c17:Prop:= @Exists Env c16; let c18:Env→ Prop:=Represents "ell.coeff" c6; let c19:Com:=computeAndStore betaFraction ((1:Nat)); let c20:Env→ Env→ Nat→ Prop:=Run B c19; let c21:Nat:=c2 (c4 ((66:Nat))) ((15:Nat)); let c22:List Rat→ List Rat:= @List.cons Rat c10; let c23:List Rat→ List Rat:= @List.cons Rat (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))); let c24:List Rat:=c23 (@List.nil Rat); let c25:List Rat:=c23 c24; let c26:List Rat:=c23 c25; let c27:List Rat:=c22 (c23 c26); let c28:Rat→ Rat→ Rat:= @HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd); let c29:Rat→ Rat:= @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (c28 (@Nat.cast Rat Rat.instNatCast n) (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))); let c30:Rat:=c7 (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) (c29 q); let c31:Env→ Prop:=Represents "ell.coeff" (@List.set Rat c27 ((1:Nat)) c30); let c32:Env→ Prop:=Represents "ell.coeff" c27; let c33:Com:=computeAndStore gammaFraction ((2:Nat)); let c34:Env→ Env→ Nat→ Prop:=Run B c33; let c35:Nat:=c2 (c2 (c3 ((330:Nat)) (Nat.size M)) ((396:Nat))) ((15:Nat)); let c36:List Rat→ List Rat:= @List.cons Rat c30; let c37:List Rat:=c22 (c36 c26); let c38:Rat→ Rat:=c7 (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))); let c39:Rat:=c38 (c29 (RationalRounding.sqrtUpper q D)); let c40:Env→ Prop:=Represents "ell.coeff" (@List.set Rat c37 ((2:Nat)) c39); let c41:Env→ Prop:=Represents "ell.coeff" c37; let c42:Com:=computeAndStore inflationFraction ((3:Nat)); let c43:Env→ Env→ Nat→ Prop:=Run B c42; let c44:List Rat→ List Rat:= @List.cons Rat c39; let c45:List Rat:=c22 (c36 (c44 c25)); let c46:Rat:=c8 (c28 (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (c38 (@Nat.cast Rat Rat.instNatCast E))) ((2:Nat)); let c47:Env→ Prop:=Represents "ell.coeff" (@List.set Rat c45 ((3:Nat)) c46); let c48:Env→ Prop:=Represents "ell.coeff" c45; let c49:Com:=computeAndStore diagonalFraction ((4:Nat)); let c50:Env→ Env→ Nat→ Prop:=Run B c49; let c51:Nat:=c2 (c2 (c3 ((36:Nat)) (Nat.size M)) ((22:Nat))) ((15:Nat)); let c52:List Rat:=c22 (c36 (c44 (@List.cons Rat c46 c24))); let c53:Env→ Prop:=Represents "ell.coeff" (@List.set Rat c52 ((4:Nat)) (c7 (@Nat.cast Rat Rat.instNatCast n) (@Nat.cast Rat Rat.instNatCast D))); let c54:Env→ Prop:=Represents "ell.coeff" c52; let c55:Nat→ Nat:=c2 c21; let c56:Nat:=c55 c51; let c57:Nat:=c2 c35 c56; let c58:Nat:=c55 c57; let c59:Com:=Com.seq c42 c49; let c60:Com:=Com.seq c33 c59; @Exists.casesOn Env c12 (fun (x:@Exists Env c12) => c17) (RunStep.use B (fun (σ_1:Env) => And (ScalarInput n q D E σ_1) (c18 σ_1)) c0 (fun (x τ:Env) => And (ScalarInput n q D E τ) (c11 τ)) c5 hαstore σ ?_) fun (w:Env) (h:And (c1 w c5) (And (ScalarInput n q D E w) (c11 w))) => let c0_1:Prop→ Prop:=And (ScalarInput n q D E w); let c1_1:Prop:=c0_1 (c11 w); let c2_1:Env→ Prop:=fun (σ':Env) => And (c20 w σ' c21) (And (ScalarInput n q D E σ') (c31 σ')); @And.casesOn (c1 w c5) c1_1 (fun (x:And (c1 w c5) c1_1) => c17) h fun (left:c1 w c5) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => c17) (RunStep.use B (fun (σ_1:Env) => And (ScalarInput n q D E σ_1) (c32 σ_1)) c19 (fun (x τ:Env) => And (ScalarInput n q D E τ) (c31 τ)) c21 hβstore w ?_) fun (w_1:Env) (h_1:And (c20 w w_1 c21) (And (ScalarInput n q D E w_1) (c31 w_1))) => let c0_2:Prop→ Prop:=And (ScalarInput n q D E w_1); let c1_2:Prop:=c0_2 (c31 w_1); let c2_2:Env→ Prop:=fun (σ':Env) => And (c34 w_1 σ' c35) (And (ScalarInput n q D E σ') (c40 σ')); @And.casesOn (c20 w w_1 c21) c1_2 (fun (x:And (c20 w w_1 c21) c1_2) => c17) h_1 fun (left_1:c20 w w_1 c21) (right_1:c1_2) => @Exists.casesOn Env c2_2 (fun (x:@Exists Env c2_2) => c17) (RunStep.use B (fun (σ_1:Env) => And (ScalarInput n q D E σ_1) (c41 σ_1)) c33 (fun (x τ:Env) => And (ScalarInput n q D E τ) (c40 τ)) c35 hγstore w_1 ?_) fun (w_2:Env) (h_2:And (c34 w_1 w_2 c35) (And (ScalarInput n q D E w_2) (c40 w_2))) => let c0_3:Prop→ Prop:=And (ScalarInput n q D E w_2); let c1_3:Prop:=c0_3 (c40 w_2); let c2_3:Env→ Prop:=fun (σ':Env) => And (c43 w_2 σ' c21) (And (ScalarInput n q D E σ') (c47 σ')); @And.casesOn (c34 w_1 w_2 c35) c1_3 (fun (x:And (c34 w_1 w_2 c35) c1_3) => c17) h_2 fun (left_2:c34 w_1 w_2 c35) (right_2:c1_3) => @Exists.casesOn Env c2_3 (fun (x:@Exists Env c2_3) => c17) (RunStep.use B (fun (σ_1:Env) => And (ScalarInput n q D E σ_1) (c48 σ_1)) c42 (fun (x τ:Env) => And (ScalarInput n q D E τ) (c47 τ)) c21 hρstore w_2 ?_) fun (w_3:Env) (h_3:And (c43 w_2 w_3 c21) (And (ScalarInput n q D E w_3) (c47 w_3))) => let c0_4:Prop→ Prop:=And (ScalarInput n q D E w_3); let c1_4:Prop:=c0_4 (c47 w_3); let c2_4:Env→ Prop:=fun (σ':Env) => And (c50 w_3 σ' c51) (And (ScalarInput n q D E σ') (c53 σ')); @And.casesOn (c43 w_2 w_3 c21) c1_4 (fun (x:And (c43 w_2 w_3 c21) c1_4) => c17) h_3 fun (left_3:c43 w_2 w_3 c21) (right_3:c1_4) => @Exists.casesOn Env c2_4 (fun (x:@Exists Env c2_4) => c17) (RunStep.use B (fun (σ_1:Env) => And (ScalarInput n q D E σ_1) (c54 σ_1)) c49 (fun (x τ:Env) => And (ScalarInput n q D E τ) (c53 τ)) c51 hδstore w_3 ?_) fun (w_4:Env) (h_4:And (c50 w_3 w_4 c51) (And (ScalarInput n q D E w_4) (c53 w_4))) => let c0_5:Prop:=And (ScalarInput n q D E w_4) (c53 w_4); @And.casesOn (c50 w_3 w_4 c51) c0_5 (fun (x:And (c50 w_3 w_4 c51) c0_5) => c17) h_4 fun (left_4:c50 w_3 w_4 c51) (right_4:c0_5) => @Exists.intro Env c16 w_4 (@And.intro (Run B computeCoefficients σ w_4 c13) (c15 w_4) (RunStep.mono B computeCoefficients σ w_4 (c2 c5 c58) c13 (RunStep.seq B c0 (Com.seq c19 c60) σ w w_4 c5 c58 left (RunStep.seq B c19 c60 w w_1 w_4 c21 c57 left_1 (RunStep.seq B c33 c59 w_1 w_2 w_4 c35 c56 left_2 (RunStep.seq B c42 c49 w_2 w_3 w_4 c21 c51 left_3 left_4)))) (?nAX_g4311_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4311_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1); (all_goals try clear h_2); (all_goals try clear left_2); (all_goals try clear h_3); (all_goals try clear left_3); (all_goals try clear h_4); (all_goals try clear left_4))
  all_goals clear hαstore hβstore hγstore hρstore hδstore hαprod hβprod hγprod hρprod hδprod
  all_goals simp_all [coefficients,List.replicate_succ,List.replicate_zero]

end Lax109476Proofs.RamEllipsoidCoefficients

end

theorem solution:∀ (B n M C D E:ℕ) (q:ℚ),
  2≤ n→
    0 < q→
      Lax109476Proofs.RationalArithmeticBounds.Height q M→
        n≤ M→
          D≤ M→
            E≤ M→
              0 < D→
                0 < E→
                  n ^ 2 < B→
                    (E + 1) ^ 2 < B→
                      2 * M ^ 2 + 3 < B→
                        (2 * (M ^ 3 + 2) + 1) ^ 2 + M ^ 3 + 3 < B→
                          C < B→
                            (∀ v∈ Lax109476Proofs.RamEllipsoidCoefficients.coefficients n q D E,
                                Lax109476Proofs.RationalArithmeticBounds.Height v C)→
                              Lax808846Proofs.Reasoning.Spec B
                                (fun (σ:Lax808846Proofs.Imp.Env) =>
                                  Lax109476Proofs.RamEllipsoidCoefficients.ScalarInput n q D E σ∧
                                    Lax109476Proofs.RamRationalArrays.Represents "ell.coeff" (List.replicate 5 0) σ)
                                Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients
                                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                  Lax109476Proofs.RamRationalArrays.Represents "ell.coeff"
                                      (Lax109476Proofs.RamEllipsoidCoefficients.coefficients n q D E) τ∧
                                    Lax109476Proofs.RamEllipsoidCoefficients.ScalarInput n q D E τ)
                                (582 * M.size + 687):= @Lax109476Proofs.RamEllipsoidCoefficients.computeCoefficients_spec
