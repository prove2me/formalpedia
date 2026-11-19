-- Prove2me | solution 1 for Lax455465Proofs.RamDualDistances.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:11:59.397206+00:00
-- url     : https://prove2.me/submissions/739093dc-20b6-47bf-9063-41cb03a2a747

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
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

theorem ite_true (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some true) (h:Run B c σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_true hb h

theorem ite_false (B:ℕ) (b:Cond) (c d:Com) (σ σ':Env) (K:ℕ)
    (hb:b.evalB B σ=some false) (h:Run B d σ σ' K):
    Run B (.ite b c d) σ σ' (1 + b.size + K):=Run.ite_false hb h

theorem mono (B:ℕ) (c:Com) (σ σ':Env) (K K':ℕ)
    (h:Run B c σ σ' K) (hK:K≤ K'):Run B c σ σ' K':=h.mono hK

end RunStep

end Lax808846Proofs.Reasoning
end

section

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def FractionOutput (q:ℚ) (σ:Env):Prop:=
  fractionValue (σ.vars "rat.s") (σ.vars "rat.n") (σ.vars "rat.d")=q∧
    σ.vars "rat.n"=q.num.natAbs∧ σ.vars "rat.d"=q.den∧ σ.vars "rat.s" ≤ 1

def fractionInputs (s₁ n₁ d₁ s₂ n₂ d₂:ℕ) (σ:Env):Prop:=
  σ.vars "left.s"=s₁∧ σ.vars "left.n"=n₁∧ σ.vars "left.d"=d₁∧
    σ.vars "right.s"=s₂∧ σ.vars "right.n"=n₂∧ σ.vars "right.d"=d₂

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

theorem capacity_row {n:ℕ} (u v:Fin n):(rowIndex n (.inl (u,v))).val=u.val * n + v.val:=by
  simp [rowIndex,edgeIndex,finProdFinEquiv,finSumFinEquiv,Equiv.sumCongr]
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

theorem height_mono {M N:ℕ} {q:ℚ} (h:Height M q) (hmn:M≤ N):Height N q:=
  ⟨h.1.trans hmn,h.2.trans hmn⟩

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

namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamFlowData
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

@[simp] theorem length_vector {k:ℕ} (x:Fin k→ ℚ) (hx:∀ i,0≤ x i):
    (vector x hx).length=k:=List.length_ofFn

end Lax455465Proofs.RamOptimalDecode

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

theorem step_le {n:ℕ} (d:Distance n) (p u v:Fin n):step d p u v≤ d u v:=
  min_le_left _ _

theorem nonnegative_step {n:ℕ} (d:Distance n) (p:Fin n) (h:Nonnegative d):
    Nonnegative (step d p):=by
  intro u v
  exact le_min (h u v) (add_nonneg (h u p) (h p v))

theorem nonnegative_iterate {n:ℕ} (d:Distance n) (pivots:List (Fin n))
    (h:Nonnegative d):Nonnegative (iterate d pivots):=by
  induction pivots generalizing d with
  | nil => exact h
  | cons p rest ih => exact ih (step d p) (nonnegative_step d p h)

theorem iterate_le {n:ℕ} (d:Distance n) (pivots:List (Fin n)) (u v:Fin n):
    iterate d pivots u v≤ d u v:=by
  induction pivots generalizing d with
  | nil => exact le_rfl
  | cons p rest ih => exact (ih (step d p)).trans (step_le d p u v)

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

theorem rational_step {n:ℕ} (d:Matrix n) (p:Fin n):
    rational (step d p)=RationalDistances.step (rational d) p:=by
  funext u v
  simp only [rational,step,RationalDistances.step,NNRat.coe_min,NNRat.coe_add]

theorem iterate_append {n:ℕ} (d:Matrix n) (ps qs:List (Fin n)):
    iterate d (ps ++ qs)=iterate (iterate d ps) qs:=by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => exact ih (step d p)

def afterPivots {n:ℕ} (d:Matrix n) (k:ℕ):Matrix n:=
  iterate d ((List.finRange n).take k)

theorem prefix_zero {n:ℕ} (d:Matrix n):afterPivots d 0=d:=rfl

theorem prefix_succ {n:ℕ} (d:Matrix n) (k:ℕ) (hk:k < n):
    afterPivots d (k+1)=step (afterPivots d k) (⟨k,hk⟩:Fin n):=by
  have hi:k < (List.finRange n).length:=by simpa using hk
  simp only [afterPivots,List.take_succ_eq_append_getElem hi,iterate_append,iterate,List.getElem_finRange]
  congr 1

theorem rational_iterate {n:ℕ} (d:Matrix n) (ps:List (Fin n)):
    rational (iterate d ps)=RationalDistances.iterate (rational d) ps:=by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => simpa only [iterate,RationalDistances.iterate,rational_step] using ih (step d p)

end Lax455465Proofs.MetricMatrix

end

section

namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

def Context {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {y:Fin (RamFlowData.rows n)→ ℚ} {hy:∀ i,0≤ y i} (h:Context y hy σ)
    (ha:"flow.dual" ∉ cmd.warrs)
    (hx:∀ x∈ ["metric.n","metric.n2"],x∉ cmd.wvars):Context y hy τ:=by
  simpa only [Context,Prefix,hr.frame_arr "flow.dual" ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp))] using h

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

theorem coefficient_spec (B M:ℕ) {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ)
    (hy:∀ i,0≤ y i) (u v:Fin n) (h2:2 < B) (hM:M < B)
    (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+1 < B)
    (hnum:∀ i, (y i).num.natAbs≤ M) (hden:∀ i, (y i).den≤ M):
    Spec B (fun σ => Context y hy σ∧ σ.vars "metric.entry"=(edgeIndex n (u,v)).val) coefficient
      (fun _ τ => Context y hy τ∧ FractionOutput ((matrix y hy u v:ℚ≥0):ℚ) τ) 28:=by
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨ν,rindex,pindex⟩:=indices_spec B u v hn hn2 σ ⟨hctx.1,hentry⟩
  have hctxν:=frame rindex hctx (by decide) (by decide)
  have hcond:(Cond.eq (.var "metric.u") (.var "metric.v")).evalB B ν=some (decide (u.val=v.val)):=by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨pindex.1.symm,pindex.1 ▸ u.isLt.trans hn⟩)
      (by rw [evalB_var_iff]; exact ⟨pindex.2.symm,pindex.2 ▸ v.isLt.trans hn⟩)]
    congr 1
  by_cases huv:u=v
  · have hv:u.val=v.val:=congrArg Fin.val huv
    obtain ⟨τ,rzero,pzero⟩:=RamFractionPrimitives.zero_spec B (by omega) ν True.intro
    have rbranch:=Run.ite_true (d:=RamUnsignedBuffer.read "flow.dual" "metric.entry") (by simpa only [hv,decide_true] using hcond) rzero
    refine ⟨τ,(rindex.seq rbranch).mono (by dsimp [Cond.size,Expr.size]; omega),frame rzero hctxν (by decide) (by decide),?_⟩
    simpa only [matrix,RationalDistances.zeroDiagonal,if_pos huv,NNRat.coe_mk] using pzero
  · let r:Fin (RamFlowData.rows n):=rowIndex n (.inl (u,v))
    have hrow:r.val=(edgeIndex n (u,v)).val:=by
      simp only [r,FlowLpIndices.capacity_row,FlowLpIndices.edge_value]
    let qs:=RamOptimalDecode.vector y hy
    have hqslen:qs.length=RamFlowData.rows n:=RamOptimalDecode.length_vector y hy
    have hr:r.val < qs.length:=by rw [hqslen]; exact r.isLt
    have hqr:qs[r.val]=(⟨y r,hy r⟩:ℚ≥0):=by
      dsimp only [qs,RamOptimalDecode.vector]
      erw [List.getElem_ofFn]
    have hnq:qs[r.val].num < B:=by
      rw [hqr]
      change (y r).num.natAbs < B
      exact (hnum r).trans_lt hM
    have hdq:qs[r.val].den < B:=by
      rw [hqr]
      change (y r).den < B
      exact (hden r).trans_lt hM
    have heν:ν.vars "metric.entry"=r.val:=by
      rw [hrow]
      exact (rindex.frame_var "metric.entry" (by decide)).trans hentry
    obtain ⟨τ,rread,pread⟩:=RamUnsignedBuffer.read_spec B "flow.dual" "metric.entry" qs r.val hr h2
      (by rw [hrow]; have:=(edgeIndex n (u,v)).isLt; omega) hnq hdq (by decide) ν ⟨hctxν.2.2,heν⟩
    have hv:¬u.val=v.val:=fun h => huv (Fin.ext h)
    have rbranch:=Run.ite_false (c:=RamFractionPrimitives.zero) (by simpa only [hv,decide_false] using hcond) rread
    refine ⟨τ,rindex.seq rbranch,frame rread hctxν (by decide) (by decide),?_⟩
    simpa only [matrix,RationalDistances.zeroDiagonal,if_neg huv,hqr,DirectedFlowDual.length,r] using pread.1

theorem command_spec (B M:ℕ) {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i)
    (h2:2 < B) (hM:M < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ i, (y i).num.natAbs≤ M) (hden:∀ i, (y i).den≤ M):
    Spec B (fun σ => σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ∧
      2*(n*n) < (σ.arrs "metric.old").length) command
      (fun _ τ => Context y hy τ∧ Prefix (RamUnsignedBuffer.encode (values (matrix y hy))) "metric.old" τ)
      (50*(n*n)+12):=by
  let qs:=values (matrix y hy)
  have hlength:qs.length=n*n:=length_values _
  have hvals:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    let uv:=(edgeIndex n).symm (⟨i,by rwa [hlength] at hi⟩:Fin (n*n))
    have hq:qs[i]=matrix y hy uv.1 uv.2:=by simp only [qs,values,List.getElem_ofFn,uv]
    rw [hq]
    unfold matrix RationalDistances.zeroDiagonal
    split_ifs
    · change NNRat.num (0:ℚ≥0) < B∧ NNRat.den (0:ℚ≥0) < B
      simp; omega
    · change (DirectedFlowDual.length y uv.1 uv.2).num.natAbs < B∧
        (DirectedFlowDual.length y uv.1 uv.2).den < B
      exact ⟨(hnum _).trans_lt hM,(hden _).trans_lt hM⟩
  have hloop:=RamUnsignedVector.command_spec B 28 (Context y hy)
    "metric.entry" "metric.n2" "metric.old" "metric.position" qs [] coefficient (by omega)
    (by simp only [List.length_nil,hlength]; omega)
    (fun i hi => (hvals i hi).1) (fun i hi => (hvals i hi).2)
    (fun σ h => by simpa only [hlength] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have he:i < n*n:=by rwa [hlength] at hi
      let uv:=(edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
      have hidx:edgeIndex n uv=(⟨i,he⟩:Fin (n*n)):=(edgeIndex n).apply_symm_apply _
      simpa only [hidx,qs,values,List.getElem_ofFn,uv,Fin.eta] using
        coefficient_spec B M y hy uv.1 uv.2 h2 hM hn hn2 (by omega) hnum hden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hr h => frame hr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hN,hN2,hdual,hroom⟩
  let ν:=((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)).setVar "metric.position" 0
  have rN:Run B (.assign "metric.n" (.var "lp.n")) σ (σ.setVar "metric.n" n) 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hn⟩)
  have rN2:Run B (.assign "metric.n2" (.var "lp.n2")) (σ.setVar "metric.n" n)
      ((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)) 2:=
    Run.assign (by rw [evalB_var_iff]; simpa only [vars_setVar,String.reduceEq,if_false]
      using And.intro hN2.symm (hN2 ▸ hn2))
  have rPos:Run B (.assign "metric.position" (.lit 0)) ((σ.setVar "metric.n" n).setVar "metric.n2" (n*n)) ν 2:=
    Run.assign (evalB_lit (by omega))
  have hsetup:=rN.seq (rN2.seq rPos)
  have hctxν:Context y hy ν:=by
    refine ⟨by simp [ν],by simp [ν],?_⟩
    simpa only [Prefix,ν,arrs_setVar] using hdual
  obtain ⟨τ,hr,hpost⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlength,List.length_nil,Nat.zero_add] using hroom⟩
  refine ⟨τ,?_,hpost.1,?_⟩
  · have rtotal:=hsetup.seq hr
    exact rtotal.mono (by simp only [hlength,Nat.reduceAdd]; omega)
  · simpa only [qs,List.nil_append] using hpost.2.1

end Lax455465Proofs.RamDualDistancesInit

end

section

namespace Lax455465Proofs.RamMetricIndices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning DirectedFlowLP FlowLpIndices

theorem command_spec (B:ℕ) {n:ℕ} (u v p:Fin n) (hn:n < B) (hn2:n*n < B):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.p"=p.val∧
      σ.vars "metric.entry"=(edgeIndex n (u,v)).val) command
      (fun _ τ => τ.vars "metric.a"=(edgeIndex n (u,v)).val∧
        τ.vars "metric.b"=(edgeIndex n (u,p)).val∧
        τ.vars "metric.c"=(edgeIndex n (p,v)).val) 24:=by
  have hidx:(edgeIndex n (u,v)).val < B:=(edgeIndex n (u,v)).isLt.trans hn2
  have hidxb:(edgeIndex n (u,p)).val < B:=(edgeIndex n (u,p)).isLt.trans hn2
  have hidxc:(edgeIndex n (p,v)).val < B:=(edgeIndex n (p,v)).isLt.trans hn2
  have hu:u.val < B:=u.isLt.trans hn
  have hv:v.val < B:=v.isLt.trans hn
  have hp:p.val < B:=p.isLt.trans hn
  have hup:u.val*n < B:=by rw [edge_value] at hidx; omega
  have hpp:p.val*n < B:=by rw [edge_value] at hidxc; omega
  have hdiv:=edge_div u v
  have hmod:=edge_mod u v
  rw [Nat.mod_def] at hmod
  have hb:u.val*n+p.val < B:=by simpa only [edge_value] using hidxb
  have hc:p.val*n+v.val < B:=by simpa only [edge_value] using hidxc
  rintro σ ⟨hnσ,hpσ,heσ⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 n n; let c2:Fin c1→ Nat:= @Fin.val c1; let c3:Type:=Fin c1; let c4:Type:=Equiv (Edge n) c3; let c5:Edge n→ c3:= @DFunLike.coe c4 (Edge n) (fun (x:Edge n) => c3) (@EquivLike.toFunLike c4 (Edge n) c3 (@Equiv.instEquivLike (Edge n) c3)) (edgeIndex n); let c6:Nat:=c2 (c5 (@Prod.mk (Fin n) (Fin n) u v)); let c7:Nat:=c2 (c5 (@Prod.mk (Fin n) (Fin n) u p)); let c8:Nat:=c2 (c5 (@Prod.mk (Fin n) (Fin n) p v)); let c9:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "metric.a") c6) (And (@Eq Nat (Env.vars τ "metric.b") c7) (@Eq Nat (Env.vars τ "metric.c") c8))) σ; let c10:String→ Nat:=Env.vars (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")); let c11:Nat:=c10 "metric.entry"; let c12:Nat:=c10 "metric.n"; let c13:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) c11 c12; let c14:Env:=Env.setVar (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) "metric.u" c13; let c15:String→ Nat:=Env.vars c14; let c16:Nat:=c15 "metric.entry"; let c17:Nat:=c15 "metric.u"; let c18:Nat:=c15 "metric.n"; let c19:Nat:=c0 c17 c18; let c20:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c16 c19; let c21:Env:=Env.setVar c14 "metric.v" c20; let c22:Nat→ Nat→ Nat:=Nat.add; let c23:String→ Nat:=Env.vars c21; let c24:Nat:=c23 "metric.u"; let c25:Nat:=c23 "metric.n"; let c26:Nat:=c0 c24 c25; let c27:Nat:=c23 "metric.p"; let c28:Nat:=c22 c26 c27; let c29:Env:=Env.setVar c21 "metric.b" c28; let c30:String→ Nat:=Env.vars c29; let c31:Nat:=c30 "metric.p"; let c32:Nat:=c30 "metric.n"; let c33:Nat:=c0 c31 c32; let c34:Nat:=c30 "metric.v"; let c35:Nat:=c22 c33 c34; let c36:Env:=Env.setVar c29 "metric.c" c35; let c37:Nat→ Nat:=c22 ((1:Nat)); let c38:Nat:=c37 (Expr.size (Expr.var "metric.entry")); let c39:Nat:=c37 (Expr.size (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n"))); let c40:Expr:=Expr.sub (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")); let c41:Nat:=c37 (Expr.size c40); let c42:Expr:=Expr.add (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) (Expr.var "metric.p"); let c43:Nat:=c37 (Expr.size c42); let c44:Expr:=Expr.add (Expr.mul (Expr.var "metric.p") (Expr.var "metric.n")) (Expr.var "metric.v"); let c45:Nat:=c37 (Expr.size c44); let c46:Nat:=c22 c43 c45; let c47:Nat:=c22 c41 c46; let c48:Nat:=c22 c39 c47; let c49:Com:=Com.assign "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n")); let c50:Com:=Com.assign "metric.v" c40; let c51:Com:=Com.assign "metric.b" c42; let c52:Com:=Com.assign "metric.c" c44; let c53:Com:=Com.seq c51 c52; let c54:Com:=Com.seq c50 c53; let c55:String→ Nat:=Env.vars c36; @Exists.intro Env (fun (σ':Env) => And (Run B command σ σ' ((24:Nat))) (c9 σ')) c36 (@And.intro (Run B command σ c36 ((24:Nat))) (c9 c36) (RunStep.mono B command σ c36 (c22 c38 c48) ((24:Nat)) (RunStep.seq B (Com.assign "metric.a" (Expr.var "metric.entry")) (Com.seq c49 c54) σ (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) c36 c38 c48 (RunStep.assign B σ "metric.a" (Expr.var "metric.entry") (Env.vars σ "metric.entry") (RunStep.eval_var B σ "metric.entry" (?nAX_g6224_0_0_0))) (RunStep.seq B c49 c54 (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) c14 c36 c39 c47 (RunStep.assign B (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) "metric.u" (Expr.div (Expr.var "metric.entry") (Expr.var "metric.n")) c13 (RunStep.eval_div B (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) (Expr.var "metric.entry") (Expr.var "metric.n") c11 c12 (RunStep.eval_var B (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) "metric.entry" (?nAX_g6224_0_0_1)) (RunStep.eval_var B (Env.setVar σ "metric.a" (Env.vars σ "metric.entry")) "metric.n" (?nAX_g6224_0_0_2)) ?_)) (RunStep.seq B c50 c53 c14 c21 c36 c41 c46 (RunStep.assign B c14 "metric.v" c40 c20 (RunStep.eval_sub B c14 (Expr.var "metric.entry") (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) c16 c19 (RunStep.eval_var B c14 "metric.entry" (?nAX_g6224_0_0_3)) (RunStep.eval_mul B c14 (Expr.var "metric.u") (Expr.var "metric.n") c17 c18 (RunStep.eval_var B c14 "metric.u" ?_) (RunStep.eval_var B c14 "metric.n" (?nAX_g6224_0_0_4)) ?_) (?nAX_g6224_0_0_5))) (RunStep.seq B c51 c52 c21 c29 c36 c43 c45 (RunStep.assign B c21 "metric.b" c42 c28 (RunStep.eval_add B c21 (Expr.mul (Expr.var "metric.u") (Expr.var "metric.n")) (Expr.var "metric.p") c26 c27 (RunStep.eval_mul B c21 (Expr.var "metric.u") (Expr.var "metric.n") c24 c25 (RunStep.eval_var B c21 "metric.u" ?_) (RunStep.eval_var B c21 "metric.n" (?nAX_g6224_0_0_6)) ?_) (RunStep.eval_var B c21 "metric.p" (?nAX_g6224_0_0_7)) ?_)) (RunStep.assign B c29 "metric.c" c44 c35 (RunStep.eval_add B c29 (Expr.mul (Expr.var "metric.p") (Expr.var "metric.n")) (Expr.var "metric.v") c33 c34 (RunStep.eval_mul B c29 (Expr.var "metric.p") (Expr.var "metric.n") c31 c32 (RunStep.eval_var B c29 "metric.p" (?nAX_g6224_0_0_8)) (RunStep.eval_var B c29 "metric.n" (?nAX_g6224_0_0_9)) ?_) (RunStep.eval_var B c29 "metric.v" (?nAX_g6224_0_0_10)) ?_)))))) (?nAX_g6224_0_0_11)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6224_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6224_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [edge_value]

end Lax455465Proofs.RamMetricIndices

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

namespace Lax455465Proofs.RamMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

theorem left_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (fun σ => σ.vars "left.s"=0∧ σ.vars "left.n"=q.num∧ σ.vars "left.d"=q.den)
      left (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  have hvalue:fractionValue 0 q.num q.den=(q:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)
  rintro σ ⟨hs,hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n"; let c2:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" c1; let c3:Nat:=Env.vars c2 "left.d"; let c4:Env:=Env.setVar c2 "rat.d" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "left.s")); let c8:Nat:=c6 (Expr.size (Expr.var "left.n")); let c9:Nat:=c6 (Expr.size (Expr.var "left.d")); let c10:Nat:=c5 c8 c9; @Exists.intro Env (fun (σ':Env) => And (Run B left σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B left σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B left σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c4 c7 c10 (RunStep.assign B σ "rat.s" (Expr.var "left.s") (Env.vars σ "left.s") (RunStep.eval_var B σ "left.s" (?nAX_g6232_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) (Env.setVar σ "rat.s" (Env.vars σ "left.s")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "rat.n" (Expr.var "left.n") c1 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "left.s")) "left.n" (?nAX_g6232_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.var "left.d") c3 (RunStep.eval_var B c2 "left.d" (?nAX_g6232_0_0_2))))) (?nAX_g6232_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6232_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6232_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem right_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (fun σ => σ.vars "right.s"=0∧ σ.vars "right.n"=q.num∧ σ.vars "right.d"=q.den)
      right (fun _ τ => FractionOutput (q:ℚ) τ) 6:=by
  have hvalue:fractionValue 0 q.num q.den=(q:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den q)
  rintro σ ⟨hs,hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@NNRat.cast Rat Rat.instNNRatCast q) τ) σ; let c1:Nat:=Env.vars (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "right.n"; let c2:Env:=Env.setVar (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "rat.n" c1; let c3:Nat:=Env.vars c2 "right.d"; let c4:Env:=Env.setVar c2 "rat.d" c3; let c5:Nat→ Nat→ Nat:=Nat.add; let c6:Nat→ Nat:=c5 ((1:Nat)); let c7:Nat:=c6 (Expr.size (Expr.var "right.s")); let c8:Nat:=c6 (Expr.size (Expr.var "right.n")); let c9:Nat:=c6 (Expr.size (Expr.var "right.d")); let c10:Nat:=c5 c8 c9; @Exists.intro Env (fun (σ':Env) => And (Run B right σ σ' ((6:Nat))) (c0 σ')) c4 (@And.intro (Run B right σ c4 ((6:Nat))) (c0 c4) (RunStep.mono B right σ c4 (c5 c7 c10) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.var "right.s")) (Com.seq (Com.assign "rat.n" (Expr.var "right.n")) (Com.assign "rat.d" (Expr.var "right.d"))) σ (Env.setVar σ "rat.s" (Env.vars σ "right.s")) c4 c7 c10 (RunStep.assign B σ "rat.s" (Expr.var "right.s") (Env.vars σ "right.s") (RunStep.eval_var B σ "right.s" (?nAX_g6233_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "right.n")) (Com.assign "rat.d" (Expr.var "right.d")) (Env.setVar σ "rat.s" (Env.vars σ "right.s")) c2 c4 c8 c9 (RunStep.assign B (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "rat.n" (Expr.var "right.n") c1 (RunStep.eval_var B (Env.setVar σ "rat.s" (Env.vars σ "right.s")) "right.n" (?nAX_g6233_0_0_1))) (RunStep.assign B c2 "rat.d" (Expr.var "right.d") c3 (RunStep.eval_var B c2 "right.d" (?nAX_g6233_0_0_2))))) (?nAX_g6233_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6233_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6233_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [FractionOutput,NNRat.natAbs_num_coe,NNRat.den_coe]

theorem command_spec (B M:ℕ) (a b:ℚ≥0) (hB:2*M^2+3 < B)
    (han:a.num≤ M) (had:a.den≤ M) (hbn:b.num≤ M) (hbd:b.den≤ M):
    Spec B (fractionInputs 0 a.num a.den 0 b.num b.den) command
      (fun _ τ => FractionOutput (min (a:ℚ) (b:ℚ)) τ) 50:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have ha:fractionValue 0 a.num a.den=(a:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den a)
  have hb:fractionValue 0 b.num b.den=(b:ℚ):=by
    simp only [fractionValue,show ¬(0:ℕ)=1 by decide,if_false]
    exact congrArg (fun q:ℚ≥0 => (q:ℚ)) (NNRat.num_div_den b)
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
    obtain ⟨τ,hr,ht⟩:=left_spec B a h1 (han.trans_lt hM) (had.trans_lt hM) ν
      ⟨hinputsν.1,hinputsν.2.1,hinputsν.2.2.1⟩
    refine ⟨τ,hcompare.seq (Run.ite_true (by simpa only [hflag,decide_true] using hc) hr),?_⟩
    simpa only [min_eq_left hab] using ht
  · have hflag:¬ν.vars "cmp.le"=1:=fun hf => hab (by simpa only [ha,hb] using hpost.2.mp hf)
    obtain ⟨τ,hr,ht⟩:=right_spec B b h1 (hbn.trans_lt hM) (hbd.trans_lt hM) ν hinputsν.2.2.2
    refine ⟨τ,hcompare.seq (Run.ite_false (by simpa only [hflag,decide_false] using hc) hr),?_⟩
    simpa only [min_eq_right (le_of_not_ge hab)] using ht

end Lax455465Proofs.RamMinimum

end

section

namespace Lax455465Proofs.RamMinPlus

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (qs:List ℚ≥0) (a b c:ℕ) (σ:Env):Prop:=
  Prefix (RamUnsignedBuffer.encode qs) "metric.old" σ∧
    σ.vars "metric.a"=a∧ σ.vars "metric.b"=b∧ σ.vars "metric.c"=c

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {qs:List ℚ≥0} {a b c:ℕ} (h:Context qs a b c σ)
    (ha:"metric.old" ∉ cmd.warrs)
    (hx:∀ x∈ ["metric.a","metric.b","metric.c"],x∉ cmd.wvars):Context qs a b c τ:=by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.a" (hx _ (by simp)),hr.frame_var "metric.b" (hx _ (by simp)),
    hr.frame_var "metric.c" (hx _ (by simp))] using h

theorem restore_spec (B:ℕ) (q:ℚ≥0) (h1:1 < B) (hn:q.num < B) (hd:q.den < B):
    Spec B (fun σ => σ.vars "metric.base.n"=q.num∧ σ.vars "metric.base.d"=q.den)
      restore (fun _ τ => τ.vars "left.s"=0∧ τ.vars "left.n"=q.num∧ τ.vars "left.d"=q.den) 6:=by
  rintro σ ⟨hnσ,hdσ⟩
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => And (@Eq Nat (Env.vars τ "left.s") ((0:Nat))) (And (@Eq Nat (Env.vars τ "left.n") (NNRat.num q)) (@Eq Nat (Env.vars τ "left.d") (NNRat.den q)))) σ; let c1:Env:=Env.setVar σ "left.s" ((0:Nat)); let c2:Nat:=Env.vars c1 "metric.base.n"; let c3:Env:=Env.setVar c1 "left.n" c2; let c4:Nat:=Env.vars c3 "metric.base.d"; let c5:Env:=Env.setVar c3 "left.d" c4; let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat→ Nat:=c6 ((1:Nat)); let c8:Nat:=c7 (Expr.size (Expr.lit ((0:Nat)))); let c9:Nat:=c7 (Expr.size (Expr.var "metric.base.n")); let c10:Nat:=c7 (Expr.size (Expr.var "metric.base.d")); let c11:Nat:=c6 c9 c10; let c12:String→ Nat:=Env.vars c5; @Exists.intro Env (fun (σ':Env) => And (Run B restore σ σ' ((6:Nat))) (c0 σ')) c5 (@And.intro (Run B restore σ c5 ((6:Nat))) (c0 c5) (RunStep.mono B restore σ c5 (c6 c8 c11) ((6:Nat)) (RunStep.seq B (Com.assign "left.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "left.n" (Expr.var "metric.base.n")) (Com.assign "left.d" (Expr.var "metric.base.d"))) σ c1 c5 c8 c11 (RunStep.assign B σ "left.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g6239_0_0_0))) (RunStep.seq B (Com.assign "left.n" (Expr.var "metric.base.n")) (Com.assign "left.d" (Expr.var "metric.base.d")) c1 c3 c5 c9 c10 (RunStep.assign B c1 "left.n" (Expr.var "metric.base.n") c2 (RunStep.eval_var B c1 "metric.base.n" (?nAX_g6239_0_0_1))) (RunStep.assign B c3 "left.d" (Expr.var "metric.base.d") c4 (RunStep.eval_var B c3 "metric.base.d" (?nAX_g6239_0_0_2))))) (?nAX_g6239_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g6239_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6239_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6239_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g6239_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all

theorem command_spec (B H:ℕ) (qs:List ℚ≥0) (a b c:ℕ)
    (ha:a < qs.length) (hb:b < qs.length) (hc:c < qs.length)
    (hB:2*(2*H)^2+3 < B)
    (hia:2*a+1 < B) (hib:2*b+1 < B) (hic:2*c+1 < B)
    (han:qs[a].num≤ H) (had:qs[a].den≤ H)
    (hbn:qs[b].num≤ H) (hbd:qs[b].den≤ H)
    (hcn:qs[c].num≤ H) (hcd:qs[c].den≤ H)
    (hsn:(qs[b]+qs[c]).num≤ 2*H) (hsd:(qs[b]+qs[c]).den≤ 2*H):
    Spec B (Context qs a b c) command
      (fun _ τ => FractionOutput (min (qs[a]:ℚ) ((qs[b]+qs[c]:ℚ≥0):ℚ)) τ)
      (36*(qs[b].den*qs[c].den).size+218):=by
  have hH:H < B:=by nlinarith
  have h2H:2*H < B:=by nlinarith
  have hB':2*H^2+3 < B:=by nlinarith
  have h2:2 < B:=by nlinarith
  rintro σ hctx
  obtain ⟨s1,r1,p1⟩:=RamUnsignedBuffer.read_spec B "metric.old" "metric.a" qs a ha h2 hia
    (han.trans_lt hH) (had.trans_lt hH) (by decide) σ ⟨hctx.1,hctx.2.1⟩
  obtain ⟨s2,r2,p2⟩:=RamUnsignedArithmetic.copy_spec B qs[a] "metric.base" (by omega)
    (han.trans_lt hH) (had.trans_lt hH) (by decide) s1 p1.1
  have ctx2:=frame (r1.seq r2) hctx (by decide) (by decide)
  obtain ⟨s3,r3,p3⟩:=RamUnsignedBuffer.read_spec B "metric.old" "metric.b" qs b hb h2 hib
    (hbn.trans_lt hH) (hbd.trans_lt hH) (by decide) s2 ⟨ctx2.1,ctx2.2.2.1⟩
  obtain ⟨s4,r4,p4⟩:=RamUnsignedArithmetic.copy_spec B qs[b] "left" (by omega)
    (hbn.trans_lt hH) (hbd.trans_lt hH) (by decide) s3 p3.1
  have ctx4:=frame (r3.seq r4) ctx2 (by decide) (by decide)
  obtain ⟨s5,r5,p5⟩:=RamUnsignedBuffer.read_spec B "metric.old" "metric.c" qs c hc h2 hic
    (hcn.trans_lt hH) (hcd.trans_lt hH) (by decide) s4 ⟨ctx4.1,ctx4.2.2.2⟩
  obtain ⟨s6,r6,p6⟩:=RamUnsignedArithmetic.copy_spec B qs[c] "right" (by omega)
    (hcn.trans_lt hH) (hcd.trans_lt hH) (by decide) s5 p5.1
  have pleft6:s6.vars "left.s"=0∧ s6.vars "left.n"=qs[b].num∧ s6.vars "left.d"=qs[b].den:=by
    simpa only [String.reduceAppend,(r5.seq r6).frame_var "left.s" (by decide),(r5.seq r6).frame_var "left.n" (by decide),
      (r5.seq r6).frame_var "left.d" (by decide)] using p4
  obtain ⟨s7,r7,p7⟩:=RamUnsignedArithmetic.add_spec B H qs[b] qs[c] hB' hbn hbd hcn hcd s6
    ⟨pleft6.1,pleft6.2.1,pleft6.2.2,p6⟩
  obtain ⟨s8,r8,p8⟩:=RamUnsignedArithmetic.copy_spec B (qs[b]+qs[c]) "right" (by omega)
    (hsn.trans_lt h2H) (hsd.trans_lt h2H) (by decide) s7 p7
  have rbase:=r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))
  have pbase8:s8.vars "metric.base.n"=qs[a].num∧ s8.vars "metric.base.d"=qs[a].den:=by
    simpa only [String.reduceAppend,rbase.frame_var "metric.base.n" (by decide),rbase.frame_var "metric.base.d" (by decide)] using p2.2
  obtain ⟨s9,r9,p9⟩:=restore_spec B qs[a] (by omega) (han.trans_lt hH) (had.trans_lt hH) s8 pbase8
  have pright9:s9.vars "right.s"=0∧ s9.vars "right.n"=(qs[b]+qs[c]).num∧
      s9.vars "right.d"=(qs[b]+qs[c]).den:=by
    simpa only [String.reduceAppend,r9.frame_var "right.s" (by decide),r9.frame_var "right.n" (by decide),
      r9.frame_var "right.d" (by decide)] using p8
  obtain ⟨τ,r10,p10⟩:=RamMinimum.command_spec B (2*H) qs[a] (qs[b]+qs[c]) hB
    (by omega) (by omega) hsn hsd s9 ⟨p9.1,p9.2.1,p9.2.2,pright9⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq r10))))))))).mono
    (by omega),p10⟩

end Lax455465Proofs.RamMinPlus

end

section

namespace Lax455465Proofs.RamMetricPivot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat

def Context {n:ℕ} (p:Fin n) (d:Matrix n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧ σ.vars "metric.p"=p.val∧
    Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {p:Fin n} {d:Matrix n} (h:Context p d σ)
    (ha:"metric.old" ∉ cmd.warrs)
    (hx:∀ x∈ ["metric.n","metric.n2","metric.p"],x∉ cmd.wvars):Context p d τ:=by
  simpa only [Context,Prefix,hr.frame_arr "metric.old" ha,
    hr.frame_var "metric.n" (hx _ (by simp)),hr.frame_var "metric.n2" (hx _ (by simp)),
    hr.frame_var "metric.p" (hx _ (by simp))] using h

theorem entry_spec (B H:ℕ) {n:ℕ} (d:Matrix n) (p:Fin n) (e:Fin (n*n))
    (hB:2*(2*H)^2+3 < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+1 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H)
    (hsnum:∀ u v, (d u p+d p v).num≤ 2*H)
    (hsden:∀ u v, (d u p+d p v).den≤ 2*H):
    Spec B (fun σ => Context p d σ∧ σ.vars "metric.entry"=e.val) entry
      (fun _ τ => Context p d τ∧ FractionOutput ((values (MetricMatrix.step d p))[e.val]:ℚ) τ)
      (36*(H*H).size+242):=by
  let u:=((edgeIndex n).symm e).1
  let v:=((edgeIndex n).symm e).2
  let a:=(edgeIndex n (u,v)).val
  let b:=(edgeIndex n (u,p)).val
  let c:=(edgeIndex n (p,v)).val
  have he:edgeIndex n (u,v)=e:=(edgeIndex n).apply_symm_apply e
  have ha:a < (values d).length:=by simpa only [a,length_values] using (edgeIndex n (u,v)).isLt
  have hb:b < (values d).length:=by simpa only [b,length_values] using (edgeIndex n (u,p)).isLt
  have hc:c < (values d).length:=by simpa only [c,length_values] using (edgeIndex n (p,v)).isLt
  have hva:(values d)[a]=d u v:=value_at d u v
  have hvb:(values d)[b]=d u p:=value_at d u p
  have hvc:(values d)[c]=d p v:=value_at d p v
  rintro σ ⟨hctx,hentry⟩
  obtain ⟨ν,rindex,pindex⟩:=RamMetricIndices.command_spec B u v p hn hn2 σ
    ⟨hctx.1,hctx.2.2.1,by simpa only [he] using hentry⟩
  have hctxν:=frame rindex hctx (by decide) (by decide)
  obtain ⟨τ,rmin,pmin⟩:=RamMinPlus.command_spec B H (values d) a b c ha hb hc hB
    (by have:=(edgeIndex n (u,v)).isLt; dsimp only [a]; omega)
    (by have:=(edgeIndex n (u,p)).isLt; dsimp only [b]; omega)
    (by have:=(edgeIndex n (p,v)).isLt; dsimp only [c]; omega)
    (by simpa only [hva] using hnum u v) (by simpa only [hva] using hden u v)
    (by simpa only [hvb] using hnum u p) (by simpa only [hvb] using hden u p)
    (by simpa only [hvc] using hnum p v) (by simpa only [hvc] using hden p v)
    (by simpa only [hvb,hvc] using hsnum u v) (by simpa only [hvb,hvc] using hsden u v) ν
      ⟨hctxν.2.2.2,pindex⟩
  have hcost:36*((values d)[b].den*(values d)[c].den).size+218≤ 36*(H*H).size+218:=by
    have hdprod:(values d)[b].den*(values d)[c].den≤ H*H:=by
      rw [hvb,hvc]; exact Nat.mul_le_mul (hden u p) (hden p v)
    have:=Nat.size_le_size hdprod
    omega
  refine ⟨τ,(rindex.seq rmin).mono (by omega),frame rmin hctxν (by decide) (by decide),?_⟩
  have hout:(values (MetricMatrix.step d p))[e.val]=MetricMatrix.step d p u v:=by
    rw [←he]
    exact value_at _ _ _
  simpa only [hout,MetricMatrix.step,NNRat.coe_min,hva,hvb,hvc] using pmin

theorem command_spec (B H:ℕ) {n:ℕ} (d:Matrix n) (p:Fin n)
    (hB:2*(2*H)^2+3 < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ H) (hden:∀ u v, (d u v).den≤ H)
    (hsnum:∀ u v, (d u p+d p v).num≤ 2*H)
    (hsden:∀ u v, (d u p+d p v).den≤ 2*H)
    (houtnum:∀ u v, (MetricMatrix.step d p u v).num≤ H)
    (houtden:∀ u v, (MetricMatrix.step d p u v).den≤ H):
    Spec B (fun σ => Context p d σ∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => Context p d τ∧ Prefix (RamUnsignedBuffer.encode (values (MetricMatrix.step d p))) "metric.new" τ∧
        τ.vars "metric.position"=2*(n*n)) ((36*(H*H).size+264)*(n*n)+8):=by
  have hH:H < B:=by nlinarith
  let qs:=values (MetricMatrix.step d p)
  have hlength:qs.length=n*n:=length_values _
  have hvals:∀ i, ∀ hi:i < qs.length,
      qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    have he:i < n*n:=by rwa [hlength] at hi
    let uv:=(edgeIndex n).symm (⟨i,he⟩:Fin (n*n))
    have heq:qs[i]=MetricMatrix.step d p uv.1 uv.2:=by
      simp only [qs,values,List.getElem_ofFn,uv]
    rw [heq]
    exact ⟨(houtnum _ _).trans_lt hH,(houtden _ _).trans_lt hH⟩
  have hloop:=RamUnsignedVector.command_spec B (36*(H*H).size+242) (Context p d)
    "metric.entry" "metric.n2" "metric.new" "metric.position" qs [] entry (by nlinarith)
    (by simp only [List.length_nil,hlength]; omega)
    (fun i hi => (hvals i hi).1) (fun i hi => (hvals i hi).2)
    (fun σ h => by simpa only [hlength] using h.2.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (fun i hi => by
      have he:i < n*n:=by rwa [hlength] at hi
      simpa only [qs] using entry_spec B H d p ⟨i,he⟩ hB hn hn2 (by omega) hnum hden hsnum hsden)
    (by decide) (by decide) (by decide) (by decide)
    (fun hr h => frame hr h (by decide) (by decide)) (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "metric.position" 0
  have rzero:Run B (.assign "metric.position" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by nlinarith))
  have hctxν:=frame rzero hctx (by decide) (by decide)
  obtain ⟨τ,hr,hpost⟩:=hloop ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,hlength,List.length_nil,Nat.zero_add] using hroom⟩
  exact ⟨τ,(rzero.seq hr).mono (by simp only [hlength,Nat.add_assoc,Nat.reduceAdd]; omega),hpost.1,
    by simpa only [List.nil_append,qs] using hpost.2.1,
    by simpa only [List.length_nil,Nat.zero_add,hlength] using hpost.2.2⟩

end Lax455465Proofs.RamMetricPivot

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

namespace Lax455465Proofs.RamFloydWarshall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

def Invariant {n:ℕ} (d:Matrix n) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧ σ.vars "metric.words"=2*(n*n)∧
    σ.vars "metric.p" ≤ n∧ Prefix (RamUnsignedBuffer.encode (values (afterPivots d (σ.vars "metric.p")))) "metric.old" σ∧
    2*(n*n)≤ (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length

theorem step_spec (B H:ℕ) {n:ℕ} (d:Matrix n)
    (hB:2*(2*H)^2+3 < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ k≤ n, ∀ u v, (afterPivots d k u v).num≤ H)
    (hden:∀ k≤ n, ∀ u v, (afterPivots d k u v).den≤ H)
    (hsnum:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num≤ 2*H)
    (hsden:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den≤ 2*H):
    Spec B (fun σ => Invariant d σ∧ σ.vars "metric.p" < n) step
      (fun σ τ => Invariant d τ∧ τ.vars "metric.p"=σ.vars "metric.p"+1)
      ((36*(H*H).size+288)*(n*n)+18):=by
  rintro σ ⟨⟨hN,hN2,hwords,hp,hsource,hOldRoom,hNewRoom⟩,hlt⟩
  let k:=σ.vars "metric.p"
  have hk:k < n:=hlt
  let p:Fin n:= ⟨k,hk⟩
  let current:=afterPivots d k
  let next:=MetricMatrix.step current p
  have hnext:next=afterPivots d (k+1):=(prefix_succ d k hk).symm
  obtain ⟨ν,rpivot,ppivot⟩:=RamMetricPivot.command_spec B H current p hB hn hn2 hindex
    (hnum k hp) (hden k hp) (hsnum k hk) (hsden k hk)
    (by intro u v; change (next u v).num≤ H; rw [hnext]; exact hnum (k+1) (by omega) u v)
    (by intro u v; change (next u v).den≤ H; rw [hnext]; exact hden (k+1) (by omega) u v) σ
      ⟨⟨hN,hN2,rfl,hsource⟩,hNewRoom⟩
  let xs:=RamUnsignedBuffer.encode (values next)
  have hxs:xs.length=2*(n*n):=by simp [xs]
  have hH:H < B:=by nlinarith
  have hxwords:∀ x∈ xs,x < B:=by
    intro x hx
    obtain ⟨q,hq,hxq⟩:=List.mem_flatMap.mp hx
    obtain ⟨e,rfl⟩:=List.mem_ofFn.mp hq
    have hv:next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2 =
      afterPivots d (k+1) ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2:=by rw [hnext]
    simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hxq
    rcases hxq with rfl | rfl
    · have hbnd:(next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2).num≤ H:=by
        rw [hv]; exact hnum (k+1) (by omega) _ _
      exact hbnd.trans_lt hH
    · have hbnd:(next ((DirectedFlowLP.edgeIndex n).symm e).1 ((DirectedFlowLP.edgeIndex n).symm e).2).den≤ H:=by
        rw [hv]; exact hden (k+1) (by omega) _ _
      exact hbnd.trans_lt hH
  have hwordsν:ν.vars "metric.words"=xs.length:=by
    simpa only [hxs] using (rpivot.frame_var "metric.words" (by decide)).trans hwords
  have hOldRoomν:xs.length≤ (ν.arrs "metric.old").length:=by
    rw [hxs,RamFrames.run_array_length rpivot "metric.old"]; exact hOldRoom
  obtain ⟨μ,rcopy,pcopy⟩:=RamArrayCopy.command_spec B xs "metric.new" "metric.old" "metric.words"
    (by nlinarith) (by rw [hxs]; omega) hxwords (by decide) (by decide) ν
      ⟨ppivot.2.1,hwordsν,hOldRoomν⟩
  have rp:=rpivot.seq rcopy
  have hpμ:μ.vars "metric.p"=k:=(rp.frame_var "metric.p" (by decide)).trans rfl
  have rnext:Run B (.assign "metric.p" (.add (.var "metric.p") (.lit 1))) μ
      (μ.setVar "metric.p" (k+1)) 4:=Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hpμ.symm,hpμ ▸ (by omega:k < B)⟩)
      (evalB_lit (by nlinarith)) (by dsimp [Bop.apply]; omega))
  have hNμ:μ.vars "metric.n"=n:=(rp.frame_var "metric.n" (by decide)).trans hN
  have hN2μ:μ.vars "metric.n2"=n*n:=(rp.frame_var "metric.n2" (by decide)).trans hN2
  have hwordsμ:μ.vars "metric.words"=2*(n*n):=(rp.frame_var "metric.words" (by decide)).trans hwords
  have hOldRoomμ:2*(n*n)≤ (μ.arrs "metric.old").length:=by rwa [RamFrames.run_array_length rp "metric.old"]
  have hNewRoomμ:2*(n*n) < (μ.arrs "metric.new").length:=by rwa [RamFrames.run_array_length rp "metric.new"]
  refine ⟨μ.setVar "metric.p" (k+1),(rpivot.seq (rcopy.seq rnext)).mono
    (by simp only [hxs]; ring_nf; omega),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hNμ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hN2μ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hwordsμ
    · simp only [vars_setVar,if_true]; omega
    · simpa only [xs,Prefix,vars_setVar,if_true,arrs_setVar,hnext] using pcopy.2
    · simpa only [arrs_setVar] using hOldRoomμ
    · simpa only [arrs_setVar] using hNewRoomμ
  · simp [k]

theorem command_spec (B H:ℕ) {n:ℕ} (d:Matrix n)
    (hB:2*(2*H)^2+3 < B) (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ k≤ n, ∀ u v, (afterPivots d k u v).num≤ H)
    (hden:∀ k≤ n, ∀ u v, (afterPivots d k u v).den≤ H)
    (hsnum:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num≤ 2*H)
    (hsden:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den≤ 2*H):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ∧
      2*(n*n)≤ (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => τ.vars "metric.n"=n∧ τ.vars "metric.n2"=n*n∧
        Prefix (RamUnsignedBuffer.encode (values (iterate d (List.finRange n)))) "metric.old" τ)
      (n*((36*(H*H).size+288)*(n*n)+22)+10):=by
  have hloop:=Spec.forRangeZero "metric.p" "metric.n" (Invariant d) n
    ((36*(H*H).size+288)*(n*n)+18) hn (fun _ h => h.2.2.2.1) (fun _ h => h.1)
    (step_spec B H d hB hn hn2 hindex hnum hden hsnum hsden)
  rintro σ ⟨hN,hN2,hprefix,hOldRoom,hNewRoom⟩
  let ν:=σ.setVar "metric.words" (2*(n*n))
  have rwords:Run B (.assign "metric.words" (.mul (.lit 2) (.var "metric.n2"))) σ ν 4:=Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (by nlinarith))
      (by rw [evalB_var_iff]; exact ⟨hN2.symm,hN2 ▸ hn2⟩) (by dsimp [Bop.apply]; omega))
  have hinit:Invariant d (ν.setVar "metric.p" 0):=by
    refine ⟨?_,?_,?_,by simp,?_,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN2
    · simp [ν]
    · simpa only [Prefix,vars_setVar,if_true,prefix_zero,ν,arrs_setVar] using hprefix
    · simpa only [ν,arrs_setVar] using hOldRoom
    · simpa only [ν,arrs_setVar] using hNewRoom
  obtain ⟨τ,hr,hpost⟩:=hloop ν hinit
  refine ⟨τ,(rwords.seq hr).mono (by ring_nf; omega),hpost.1.1,hpost.1.2.1,?_⟩
  have htake:(List.finRange n).take n=List.finRange n:=by
    simpa only [List.length_finRange] using (show (List.finRange n).take (List.finRange n).length=List.finRange n from List.take_length)
  simpa only [hpost.2,afterPivots,htake] using hpost.1.2.2.2.2.1

end Lax455465Proofs.RamFloydWarshall

end

section

namespace Lax455465Proofs.MetricHeight

open scoped BigOperators
open RationalDistances DirectedFlowLP

def denominator {n:ℕ} (d:Distance n):ℕ:= ∏ e:Edge n, (d e.1 e.2).den

theorem denominator_pos {n:ℕ} (d:Distance n):0 < denominator d:=by
  apply Finset.prod_pos
  intro e he
  exact Rat.den_pos _

theorem denominator_dvd {n:ℕ} (d:Distance n) (u v:Fin n):
    (d u v).den ∣ denominator d:=Finset.dvd_prod_of_mem _ (Finset.mem_univ (u,v))

theorem step_denominator {n:ℕ} (d:Distance n) (p:Fin n) (D:ℕ)
    (h:∀ u v, (d u v).den ∣ D):∀ u v, (step d p u v).den ∣ D:=by
  intro u v
  by_cases hv:d u v≤ d u p+d p v
  · rw [step,min_eq_left hv]
    exact h u v
  · rw [step,min_eq_right (le_of_not_ge hv)]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h u p) (h p v))

theorem iterate_denominator {n:ℕ} (d:Distance n) (ps:List (Fin n)) (D:ℕ)
    (h:∀ u v, (d u v).den ∣ D):∀ u v, (iterate d ps u v).den ∣ D:=by
  induction ps generalizing d with
  | nil => exact h
  | cons p ps ih => exact ih (step d p) (step_denominator d p D h)

theorem value_bound (q:ℚ) (hq:0≤ q) (M:ℕ) (hnum:q.num.natAbs≤ M):q≤ M:=by
  have hn:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) hn
  have hd:(1:ℚ)≤ q.den:=by exact_mod_cast (Rat.den_pos q)
  rw [←q.num_div_den,←hnQ]
  exact (div_le_self (by positivity) hd).trans (by exact_mod_cast hnum)

theorem height_of_denominator (q:ℚ) (hq:0≤ q) (M D:ℕ)
    (hM:1≤ M) (hD:0 < D) (hden:q.den ∣ D) (hval:q≤ M):
    LpInputSize.Height (M*D) q:=by
  have hd:q.den≤ D:=Nat.le_of_dvd hD hden
  have hn:(q.num.natAbs:ℤ)=q.num:=Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnQ:(q.num.natAbs:ℚ)=(q.num:ℚ):=by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℚ)) hn
  have hdenQ:(0:ℚ) < q.den:=by exact_mod_cast Rat.den_pos q
  have hrepr:(q.num.natAbs:ℚ)=q*(q.den:ℚ):=by
    rw [hnQ]
    exact ((eq_div_iff (ne_of_gt hdenQ)).mp q.num_div_den.symm).symm
  have hbound:(q.num.natAbs:ℚ)≤ (M*D:ℕ):=by
    rw [hrepr,Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hval (le_of_lt hdenQ)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by positivity))
  exact ⟨by exact_mod_cast hbound,hd.trans (by nlinarith)⟩

theorem iterate_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (M:ℕ)
    (hM:1≤ M) (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ M):
    ∀ u v,LpInputSize.Height (M*denominator d) (iterate d ps u v):=by
  intro u v
  apply height_of_denominator _ (nonnegative_iterate d ps hnonneg u v) M (denominator d) hM
    (denominator_pos d) (iterate_denominator d ps _ (denominator_dvd d) u v)
  exact (iterate_le d ps u v).trans (value_bound _ (hnonneg u v) M (hnum u v))

theorem denominator_bound {n:ℕ} (d:Distance n) (w:ℕ)
    (hden:∀ u v, (d u v).den≤ 2^w):denominator d≤ 2^(w*(n*n)):=by
  unfold denominator
  calc
    _≤ ∏ e:Edge n,2^w:=Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun e _ => hden e.1 e.2)
    _=_:=by simp [Edge,Finset.prod_const,Nat.pow_mul]

theorem iterate_word_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (w:ℕ)
    (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ 2^w)
    (hden:∀ u v, (d u v).den≤ 2^w):
    ∀ u v,LpInputSize.Height (2^(w*(n*n+1))) (iterate d ps u v):=by
  intro u v
  have hM:1≤ 2^w:=Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
  apply LpInputSize.height_mono (iterate_height d ps (2^w) hM hnonneg hnum u v)
  calc
    2^w*denominator d≤ 2^w*2^(w*(n*n)):=Nat.mul_le_mul_left _ (denominator_bound d w hden)
    _=_:=by rw [←Nat.pow_add]; congr 1; ring

theorem candidate_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (M:ℕ)
    (hM:1≤ M) (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ M) (u p v:Fin n):
    LpInputSize.Height (2*(M*denominator d))
      (iterate d ps u p+iterate d ps p v):=by
  have hd:=iterate_denominator d ps (denominator d) (denominator_dvd d)
  have hn:=nonnegative_iterate d ps hnonneg
  have hb:∀ a b,iterate d ps a b≤ (M:ℚ):=fun a b =>
    (iterate_le d ps a b).trans (value_bound _ (hnonneg a b) M (hnum a b))
  have h:=height_of_denominator _ (add_nonneg (hn u p) (hn p v)) (2*M) (denominator d)
    (by omega) (denominator_pos d)
    ((Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (hd u p) (hd p v)))
    (by push_cast; linarith [hb u p,hb p v])
  simpa only [Nat.mul_assoc] using h

theorem candidate_word_height {n:ℕ} (d:Distance n) (ps:List (Fin n)) (w:ℕ)
    (hnonneg:Nonnegative d)
    (hnum:∀ u v, (d u v).num.natAbs≤ 2^w)
    (hden:∀ u v, (d u v).den≤ 2^w) (u p v:Fin n):
    LpInputSize.Height (2*2^(w*(n*n+1)))
      (iterate d ps u p+iterate d ps p v):=by
  have hM:1≤ 2^w:=Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
  apply LpInputSize.height_mono (candidate_height d ps (2^w) hM hnonneg hnum u p v)
  apply Nat.mul_le_mul_left 2
  calc
    2^w*denominator d≤ 2^w*2^(w*(n*n)):=Nat.mul_le_mul_left _ (denominator_bound d w hden)
    _=_:=by rw [←Nat.pow_add]; congr 1; ring

end Lax455465Proofs.MetricHeight

end

section

namespace Lax455465Proofs.MetricPrefixBounds

open MetricMatrix
open scoped NNRat

theorem coordinate_height {n:ℕ} (d:Matrix n) (w k:ℕ)
    (hnum:∀ u v, (d u v).num≤ 2^w) (hden:∀ u v, (d u v).den≤ 2^w):
    ∀ u v,LpInputSize.Height (2^(w*(n*n+1))) ((afterPivots d k u v:ℚ≥0):ℚ):=by
  have hcoenum:∀ u v, (rational d u v).num.natAbs≤ 2^w:=by
    simpa only [rational,NNRat.natAbs_num_coe] using hnum
  have hcoeden:∀ u v, (rational d u v).den≤ 2^w:=by
    simpa only [rational,NNRat.den_coe] using hden
  have hh:=MetricHeight.iterate_word_height (rational d) ((List.finRange n).take k) w
    (fun u v => (d u v).property) hcoenum hcoeden
  intro u v
  have heq:=congrFun (congrFun (rational_iterate d ((List.finRange n).take k)) u) v
  simpa only [←heq,afterPivots,rational] using hh u v

theorem candidate_height {n:ℕ} (d:Matrix n) (w k:ℕ)
    (hnum:∀ u v, (d u v).num≤ 2^w) (hden:∀ u v, (d u v).den≤ 2^w)
    (u p v:Fin n):
    LpInputSize.Height (2*2^(w*(n*n+1)))
      ((afterPivots d k u p+afterPivots d k p v:ℚ≥0):ℚ):=by
  have hcoenum:∀ u v, (rational d u v).num.natAbs≤ 2^w:=by
    simpa only [rational,NNRat.natAbs_num_coe] using hnum
  have hcoeden:∀ u v, (rational d u v).den≤ 2^w:=by
    simpa only [rational,NNRat.den_coe] using hden
  have hh:=MetricHeight.candidate_word_height (rational d) ((List.finRange n).take k) w
    (fun u v => (d u v).property) hcoenum hcoeden u p v
  have heq:=rational_iterate d ((List.finRange n).take k)
  have hleft:=congrFun (congrFun heq u) p
  have hright:=congrFun (congrFun heq p) v
  simpa only [←hleft,←hright,afterPivots,rational,NNRat.coe_add] using hh

end Lax455465Proofs.MetricPrefixBounds

end

section

namespace Lax455465Proofs.RamFloydBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

theorem command_spec (B w:ℕ) {n:ℕ} (d:Matrix n)
    (hB:2*(2*2^(w*(n*n+1)))^2+3 < B)
    (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ u v, (d u v).num≤ 2^w) (hden:∀ u v, (d u v).den≤ 2^w):
    Spec B (fun σ => σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (values d)) "metric.old" σ∧
      2*(n*n)≤ (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length)
      RamFloydWarshall.command
      (fun _ τ => τ.vars "metric.n"=n∧ τ.vars "metric.n2"=n*n∧
        Prefix (RamUnsignedBuffer.encode (values (iterate d (List.finRange n)))) "metric.old" τ)
      (n*((72*(w*(n*n+1))+324)*(n*n)+22)+10):=by
  let H:=2^(w*(n*n+1))
  have hpheight:=MetricPrefixBounds.coordinate_height d w
  have hcand:=MetricPrefixBounds.candidate_height d w
  have hnum':∀ k≤ n, ∀ u v, (afterPivots d k u v).num≤ H:=by
    intro k hk u v
    simpa only [LpInputSize.Height,NNRat.natAbs_num_coe] using (hpheight k hnum hden u v).1
  have hden':∀ k≤ n, ∀ u v, (afterPivots d k u v).den≤ H:=by
    intro k hk u v
    simpa only [LpInputSize.Height,NNRat.den_coe] using (hpheight k hnum hden u v).2
  have hsn:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).num≤ 2*H:=by
    intro k hk u v
    simpa only [NNRat.natAbs_num_coe] using (hcand k hnum hden u ⟨k,hk⟩ v).1
  have hsd:∀ k, ∀ hk:k < n, ∀ u v,
      (afterPivots d k u ⟨k,hk⟩+afterPivots d k ⟨k,hk⟩ v).den≤ 2*H:=by
    intro k hk u v
    simpa only [NNRat.den_coe] using (hcand k hnum hden u ⟨k,hk⟩ v).2
  have hrun:=RamFloydWarshall.command_spec B H d hB hn hn2 hindex hnum' hden' hsn hsd
  have hsize:(H*H).size=2*(w*(n*n+1))+1:=by
    dsimp only [H]
    rw [←Nat.pow_add,Nat.size_pow]
    omega
  convert hrun using 1
  rw [hsize]
  ring

end Lax455465Proofs.RamFloydBounds

end

section

namespace Lax455465Proofs.RamDualDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

theorem command_spec (B w:ℕ) {n:ℕ} (y:Fin (RamFlowData.rows n)→ ℚ) (hy:∀ i,0≤ y i)
    (hB:2*(2*2^(w*(n*n+1)))^2+3 < B)
    (hn:n < B) (hn2:n*n < B) (hindex:2*(n*n)+2 < B)
    (hnum:∀ i, (y i).num.natAbs≤ 2^w) (hden:∀ i, (y i).den≤ 2^w):
    Spec B (fun σ => σ.vars "lp.n"=n∧ σ.vars "lp.n2"=n*n∧
      Prefix (RamUnsignedBuffer.encode (RamOptimalDecode.vector y hy)) "flow.dual" σ∧
      2*(n*n) < (σ.arrs "metric.old").length∧ 2*(n*n) < (σ.arrs "metric.new").length) command
      (fun _ τ => τ.vars "metric.n"=n∧ τ.vars "metric.n2"=n*n∧
        Prefix (RamUnsignedBuffer.encode (values (result y hy))) "metric.old" τ)
      (50*(n*n)+12+(n*((72*(w*(n*n+1))+324)*(n*n)+22)+10)):=by
  have hpower:2^w≤ 2^(w*(n*n+1)):=Nat.pow_le_pow_right (by decide) (by nlinarith)
  have h2:2 < B:=by nlinarith
  have hM:2^w < B:=by nlinarith [Nat.two_pow_pos (w*(n*n+1))]
  let d:=RamDualDistancesInit.matrix y hy
  have hinitNum:∀ u v, (d u v).num≤ 2^w:=by
    intro u v
    dsimp only [d,RamDualDistancesInit.matrix,RationalDistances.zeroDiagonal]
    split_ifs
    · change NNRat.num (0:ℚ≥0)≤ 2^w; simp
    · exact hnum _
  have hinitDen:∀ u v, (d u v).den≤ 2^w:=by
    intro u v
    dsimp only [d,RamDualDistancesInit.matrix,RationalDistances.zeroDiagonal]
    split_ifs
    · change NNRat.den (0:ℚ≥0)≤ 2^w
      simpa using Nat.succ_le_iff.mpr (Nat.two_pow_pos w)
    · exact hden _
  rintro σ ⟨hN,hN2,hdual,hOldRoom,hNewRoom⟩
  obtain ⟨ν,rinit,pinit⟩:=RamDualDistancesInit.command_spec B (2^w) y hy h2 hM hn hn2 hindex hnum hden σ
    ⟨hN,hN2,hdual,hOldRoom⟩
  have hOldRoomν:2*(n*n)≤ (ν.arrs "metric.old").length:=by
    rw [RamFrames.run_array_length rinit "metric.old"]; omega
  have hNewRoomν:2*(n*n) < (ν.arrs "metric.new").length:=by rwa [RamFrames.run_array_length rinit "metric.new"]
  obtain ⟨τ,rfloyd,pfloyd⟩:=RamFloydBounds.command_spec B w d hB hn hn2 hindex hinitNum hinitDen ν
    ⟨pinit.1.1,pinit.1.2.1,pinit.2,hOldRoomν,hNewRoomν⟩
  exact ⟨τ,rinit.seq rfloyd,pfloyd⟩

end Lax455465Proofs.RamDualDistances

end

theorem solution:∀ (B w:Nat) {n:Nat} (y:Fin (Lax455465Proofs.RamFlowData.rows n)→ Rat)
  (hy:
    ∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (y i)),
  Nat.lt
      (Nat.add
        (Nat.mul ((2:Nat))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (Nat.mul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat))
                (Nat.mul w
                  (Nat.add
                    (Nat.mul n n)
                    ((1:Nat))))))
            ((2:Nat))))
        ((3:Nat)))
      B→
    Nat.lt n B→
      Nat.lt (Nat.mul n n) B→
        Nat.lt
            (Nat.add
              (Nat.mul
                ((2:Nat))
                (Nat.mul n n))
              ((2:Nat)))
            B→
          (∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
              Nat.le (y i).num.natAbs
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) w))→
            (∀ (i:Fin (Lax455465Proofs.RamFlowData.rows n)),
                Nat.le (y i).den
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) w))→
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (σ.vars "lp.n") n)
                    (And (@Eq Nat (σ.vars "lp.n2") (Nat.mul n n))
                      (And
                        (Lax455465Proofs.RamVirtualState.Prefix
                          (Lax455465Proofs.RamUnsignedBuffer.encode
                            (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y hy))
                          "flow.dual" σ)
                        (And
                          (Nat.lt
                            (Nat.mul
                              ((2:Nat))
                              (Nat.mul n n))
                            (@List.length Nat (σ.arrs "metric.old")))
                          (Nat.lt
                            (Nat.mul
                              ((2:Nat))
                              (Nat.mul n n))
                            (@List.length Nat (σ.arrs "metric.new")))))))
                Lax455465Proofs.RamDualDistances.command
                (fun (x τ:Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (τ.vars "metric.n") n)
                    (And (@Eq Nat (τ.vars "metric.n2") (Nat.mul n n))
                      (Lax455465Proofs.RamVirtualState.Prefix
                        (Lax455465Proofs.RamUnsignedBuffer.encode
                          (@Lax455465Proofs.MetricMatrix.values n (@Lax455465Proofs.RamDualDistances.result n y hy)))
                        "metric.old" τ)))
                (Nat.add
                  (Nat.add
                    (Nat.mul
                      ((50:Nat))
                      (Nat.mul n n))
                    ((12:Nat)))
                  (Nat.add
                    (Nat.mul n
                      (Nat.add
                        (Nat.mul
                          (Nat.add
                            (Nat.mul
                              ((72:Nat))
                              (Nat.mul w
                                (Nat.add
                                  (Nat.mul n n)
                                  ((1:Nat)))))
                            ((324:Nat)))
                          (Nat.mul n n))
                        ((22:Nat))))
                    ((10:Nat)))):= @Lax455465Proofs.RamDualDistances.command_spec
