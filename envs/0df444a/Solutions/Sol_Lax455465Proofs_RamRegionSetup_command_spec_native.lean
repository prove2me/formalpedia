-- Prove2me | solution 1 for Lax455465Proofs.RamRegionSetup.command_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:27:38.8694+00:00
-- url     : https://prove2.me/submissions/40c013b8-6482-4d86-b3e9-702704b0de20

import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.NNRat.BigOperators
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
import Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
import Theorems.Thm_Lax455465Proofs_RamSelectedRegion_command_spec_native

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
namespace Lax455465Proofs.RamSelectedRegion
end Lax455465Proofs.RamSelectedRegion
theorem Lax455465Proofs.RamSelectedRegion.command_spec:∀ (B H:Nat) {n:Nat} (q:Lax455465Proofs.RegionQueryData.Query n) (radii:List NNRat),
  (∀ (i:Nat) (hi:LT.lt i (@List.length NNRat radii)),
      @Lax455465Proofs.RegionQueryHeight.Bounds n
        (@Lax455465Proofs.RadiusSearchData.atRadius n q
          (@GetElem.getElem (List NNRat) Nat NNRat
            (fun (as:List NNRat) (i:Nat) => LT.lt i (@List.length NNRat as))
            (@List.instGetElemNatLtLength NNRat) radii i hi))
        H)→
    LT.lt
        (HAdd.hAdd
          (HMul.hMul ((2:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) H)
              ((2:Nat))))
          ((3:Nat)))
        B→
      LT.lt
          (HAdd.hAdd
            (HMul.hMul ((2:Nat))
              (HMul.hMul n n))
            ((2:Nat)))
          B→
        LT.lt
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat)) n)
              ((2:Nat)))
            B→
          LT.lt
              (HAdd.hAdd
                (HMul.hMul
                  ((2:Nat)) (@List.length NNRat radii))
                ((2:Nat)))
              B→
            Lax808846Proofs.Reasoning.Spec B (@Lax455465Proofs.RamRadiusSearch.Context n q radii)
              Lax455465Proofs.RamSelectedRegion.command
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax455465Proofs.RamRadiusSearch.Context n q radii τ)
                  (And
                    (Lax455465Proofs.RamFind.Matches
                      (Lax455465Proofs.RamFind.first (@Lax455465Proofs.RadiusSearchData.predicate n q radii)
                        (@List.length NNRat radii))
                      τ)
                    (@Lax455465Proofs.RamSelectedRegion.Selected n q radii τ)))
              (HAdd.hAdd
                (HAdd.hAdd
                  (HMul.hMul
                    (HAdd.hAdd (Lax455465Proofs.RamRadiusSearch.queryCost n H)
                      ((38:Nat)))
                    (@List.length NNRat radii))
                  (Lax455465Proofs.RamRadiusSearch.queryCost n H))
                ((40:Nat))):= @Lax455465Proofs.RamSelectedRegion.command_spec_native

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

namespace Lax455465Proofs.FlowLpIndices

open DirectedFlowLP

theorem edge_value {n:ℕ} (s t:Fin n):(edgeIndex n (s,t)).val=s.val * n + t.val:=by
  simp [edgeIndex,finProdFinEquiv]
  ring

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

end Lax455465Proofs.RamUnsignedScalar

end

section

namespace Lax455465Proofs.UnsignedHeight

open LpInputSize
open scoped NNRat

abbrev Bounded (M:ℕ) (q:ℚ≥0):=Height M (q:ℚ)

theorem min_bound {M:ℕ} {a b:ℚ≥0} (ha:Bounded M a) (hb:Bounded M b):
    Bounded M (min a b):=by
  by_cases hab:a≤ b
  · simpa only [min_eq_left hab] using ha
  · simpa only [min_eq_right (le_of_not_ge hab)] using hb

end Lax455465Proofs.UnsignedHeight

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

theorem num_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.num≤ M:=by
  simpa only [NNRat.natAbs_num_coe] using h.1

theorem den_bound {M:ℕ} {q:ℚ≥0} (h:LpInputSize.Height M (q:ℚ)):q.den≤ M:=by
  simpa only [NNRat.den_coe] using h.2

end Lax455465Proofs.RamRegionContext

end

section

namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

theorem storedFrame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {name:String} {q:ℚ≥0} (h:Stored name q σ)
    (hn:name++".n"∉cmd.wvars) (hd:name++".d"∉cmd.wvars):Stored name q τ:=by
  simpa only [Stored,rr.frame_var (name++".n") hn,rr.frame_var (name++".d") hd] using h

end Lax455465Proofs.RamRoundingConstants

end

section

namespace Lax455465Proofs.RadiusData

open LpInputSize
open scoped NNRat

@[simp] theorem length_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0):
    (candidates outDistance inDistance k delta).length=k+1+2*n:=by
  simp [candidates]; omega

theorem height {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k M:ℕ) (delta:ℚ≥0)
    (hM:1≤ M) (hk:k≤ M) (hu:Height M ((delta/(k:ℚ≥0):ℚ≥0):ℚ))
    (hd:Height M (delta:ℚ))
    (ho:∀ v,Height M (outDistance v:ℚ)) (hi:∀ v,Height M (inDistance v:ℚ)):
    ∀ q∈ candidates outDistance inDistance k delta,Height (M*M) (q:ℚ):=by
  intro q hq
  simp only [candidates,List.mem_append] at hq
  rcases hq with (hq|hq)|hq
  · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hq
    have hjk:j≤ k:=by have:=List.mem_range.mp hj; omega
    have hjh:Height M ((j:ℚ≥0):ℚ):=by
      simp only [NNRat.coe_natCast,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
      exact ⟨hjk.trans hk,hM⟩
    simpa only [NNRat.coe_mul] using height_mul hu hjh
  · obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (ho v)) (by nlinarith)
  · obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    exact height_mono (UnsignedHeight.min_bound hd (hi v)) (by nlinarith)

end Lax455465Proofs.RadiusData

end

section

namespace Lax455465Proofs.RadiusLookup
open scoped NNRat

theorem grid_at {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0)
    (j:ℕ) (hj:j < k+1):
    (RadiusData.candidates outDistance inDistance k delta)[j]'(by rw [RadiusData.length_candidates]; omega)=(delta/(k:ℚ≥0))*(j:ℚ≥0):=by
  unfold RadiusData.candidates
  rw [List.getElem_append_left (by simp only [List.length_append,List.length_map,List.length_range,List.length_ofFn]; omega),List.getElem_append_left (by simpa using hj)]
  all_goals simp

theorem out_at {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0)
    (v:Fin n):
    (RadiusData.candidates outDistance inDistance k delta)[k+1+v.val]'(by rw [RadiusData.length_candidates]; have:=v.isLt; omega)=min delta (outDistance v):=by
  unfold RadiusData.candidates
  rw [List.getElem_append_left (by simp),List.getElem_append_right (by simp)]
  all_goals simp

theorem in_at {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0)
    (v:Fin n):
    (RadiusData.candidates outDistance inDistance k delta)[k+1+n+v.val]'(by rw [RadiusData.length_candidates]; have:=v.isLt; omega)=min delta (inDistance v):=by
  unfold RadiusData.candidates
  rw [List.getElem_append_right (by simp)]
  all_goals simp

end Lax455465Proofs.RadiusLookup

end

section

namespace Lax455465Proofs.RamGridRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational
open scoped NNRat

theorem command_spec (B M j:ℕ) (unit:ℚ≥0) (hB:2*M^2+3 < B)
    (hun:unit.num≤ M) (hud:unit.den≤ M) (hj:j≤ M):
    Spec B (fun σ => Stored "round.gridStep" unit σ∧ σ.vars "radius.i"=j)
      command (fun _ τ => FractionOutput ((unit*(j:ℚ≥0):ℚ≥0):ℚ) τ)
      (36*unit.den.size+82):=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  have hM1:1≤ M:=unit.den_pos.trans_le hud
  rintro σ ⟨hu,hi⟩
  obtain ⟨ν,rl,pl⟩:=load_spec B "round.gridStep" unit h1 (hun.trans_lt hM) (hud.trans_lt hM) (by decide) σ hu
  obtain ⟨μ,rc,pc⟩:=RamUnsignedArithmetic.copy_spec B unit "left" h1 (hun.trans_lt hM) (hud.trans_lt hM) (by decide) ν pl
  have hiμ:μ.vars "radius.i"=j:=by
    have rr:=rl.seq rc
    exact (rr.frame_var _ (by decide)).trans hi
  let ξ:=((μ.setVar "right.s" 0).setVar "right.n" j).setVar "right.d" 1
  have rn:Run B indexOperand μ ξ 6:=by
    refine (Run.assign (evalB_lit (by omega))).seq ((Run.assign ?_).seq (Run.assign (evalB_lit h1)))
    rw [evalB_var_iff]
    simpa only [vars_setVar,String.reduceEq,if_false] using And.intro hiμ.symm (hiμ ▸ hj.trans_lt hM)
  have pleft:ξ.vars "left.s"=0∧ ξ.vars "left.n"=unit.num∧ ξ.vars "left.d"=unit.den:=by
    simpa only [rn.frame_var "left.s" (by decide),rn.frame_var "left.n" (by decide),rn.frame_var "left.d" (by decide),String.reduceAppend] using pc
  obtain ⟨τ,rm,pm⟩:=multiplyFraction_spec B M 0 unit.num unit.den 0 j 1 hB
    (by omega) (by omega) hun hud hj hM1 unit.den_pos (by omega) ξ
    ⟨pleft.1,pleft.2.1,pleft.2.2,by simp [ξ],by simp [ξ],by simp [ξ]⟩
  refine ⟨τ,(rl.seq (rc.seq (rn.seq rm))).mono (by simp only [Nat.mul_one]; omega),?_⟩
  have huval:=RamUnsignedArithmetic.value unit
  have hjval:fractionValue 0 j 1=(j:ℚ):=by simp [fractionValue]
  simpa only [NNRat.coe_mul,NNRat.coe_natCast,huval,hjval] using pm

end Lax455465Proofs.RamGridRadius

end

section

namespace Lax455465Proofs.RamEventRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat

theorem command_spec (B M:ℕ) {n:ℕ} (outward:Bool) (distance:Fin n→ ℚ≥0)
    (delta:ℚ≥0) (v:Fin n) (hB:2*M^2+3 < B) (hindex:2*n+2 < B)
    (hdn:delta.num≤ M) (hdd:delta.den≤ M)
    (hvn:(distance v).num≤ M) (hvd:(distance v).den≤ M):
    Spec B (fun σ => Stored "round.delta" delta σ∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn distance)) (RamRootDistances.array outward) σ∧ σ.vars "radius.v"=v.val)
      (command outward) (fun _ τ => FractionOutput ((min delta (distance v):ℚ≥0):ℚ) τ) 82:=by
  have hM:M < B:=by nlinarith
  have h1:1 < B:=by nlinarith
  let qs:=List.ofFn distance
  have hi:v.val < qs.length:=by simpa only [qs,List.length_ofFn] using v.isLt
  have hv:qs[v.val]=distance v:=by simp only [qs,List.getElem_ofFn,Fin.eta]
  rintro σ ⟨hδ,hsource,hindexσ⟩
  obtain ⟨ν,rl,pl⟩:=load_spec B "round.delta" delta h1 (hdn.trans_lt hM) (hdd.trans_lt hM) (by decide) σ hδ
  obtain ⟨μ,rc,pc⟩:=RamUnsignedArithmetic.copy_spec B delta "left" h1 (hdn.trans_lt hM) (hdd.trans_lt hM) (by decide) ν pl
  have hsourceμ:Prefix (RamUnsignedBuffer.encode qs) (RamRootDistances.array outward) μ:=by
    have rr:=rl.seq rc
    simpa only [Prefix,qs,rr.frame_arr (RamRootDistances.array outward) (by change RamRootDistances.array outward∉ ([]:List String); simp)] using hsource
  have hvμ:μ.vars "radius.v"=v.val:=by
    have rr:=rl.seq rc
    exact (rr.frame_var _ (by decide)).trans hindexσ
  obtain ⟨ξ,rv,pv⟩:=RamUnsignedBuffer.read_spec B (RamRootDistances.array outward) "radius.v" qs v.val hi (by omega) (by have:=v.isLt; omega)
    (by rw [hv]; exact hvn.trans_lt hM) (by rw [hv]; exact hvd.trans_lt hM) (by decide) μ ⟨hsourceμ,hvμ⟩
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B (distance v) "right" h1 (hvn.trans_lt hM) (hvd.trans_lt hM) (by decide) ξ (by simpa only [hv] using pv.1)
  have pleft:η.vars "left.s"=0∧ η.vars "left.n"=delta.num∧ η.vars "left.d"=delta.den:=by
    have r:=rv.seq rr
    simpa only [r.frame_var "left.s" (by cases outward <;> decide),r.frame_var "left.n" (by cases outward <;> decide),
      r.frame_var "left.d" (by cases outward <;> decide),String.reduceAppend] using pc
  obtain ⟨τ,rm,pm⟩:=RamMinimum.command_spec B M delta (distance v) hB hdn hdd hvn hvd η
    ⟨pleft.1,pleft.2.1,pleft.2.2,by simpa only [String.reduceAppend] using pr⟩
  exact ⟨τ,rl.seq (rc.seq (rv.seq (rr.seq rm))),by simpa only [NNRat.coe_min] using pm⟩

end Lax455465Proofs.RamEventRadius

end

section

namespace Lax455465Proofs.RamRadiusCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat

structure Source {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0) (σ:Env):Prop where
  nValue:σ.vars "metric.n"=n
  kValue:σ.vars "round.steps"=k
  deltaData:Stored "round.delta" delta σ
  unitData:Stored "round.gridStep" (delta/(k:ℚ≥0)) σ
  outData:Prefix (RamUnsignedBuffer.encode (List.ofFn outDistance)) "region.out" σ
  inData:Prefix (RamUnsignedBuffer.encode (List.ofFn inDistance)) "region.in" σ

structure Context {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0) (σ:Env):Prop where
  source:Source outDistance inDistance k delta σ
  gridCount:σ.vars "radius.gridCount"=k+1
  count:σ.vars "radius.count"=k+1+2*n

def names:List String:= ["metric.n","round.steps","round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d","radius.gridCount","radius.count"]
def arrays:List String:= ["region.out","region.in"]

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (hr:Run B cmd σ τ K)
    {n:ℕ} {outDistance inDistance:Fin n→ ℚ≥0} {k:ℕ} {delta:ℚ≥0}
    (h:Context outDistance inDistance k delta σ)
    (hx:∀ x∈ names,x∉ cmd.wvars) (ha:∀ a∈ arrays,a∉ cmd.warrs):
    Context outDistance inDistance k delta τ:=by
  refine ⟨⟨(hr.frame_var _ (hx _ (by simp [names]))).trans h.source.nValue,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.source.kValue,?_,?_,?_,?_⟩,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.gridCount,
    (hr.frame_var _ (hx _ (by simp [names]))).trans h.count⟩
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.delta.n" (hx _ (by simp [names])),hr.frame_var "round.delta.d" (hx _ (by simp [names]))] using h.source.deltaData
  · simpa only [Stored,String.reduceAppend,hr.frame_var "round.gridStep.n" (hx _ (by simp [names])),hr.frame_var "round.gridStep.d" (hx _ (by simp [names]))] using h.source.unitData
  · simpa only [Prefix,hr.frame_arr "region.out" (ha _ (by simp [arrays]))] using h.source.outData
  · simpa only [Prefix,hr.frame_arr "region.in" (ha _ (by simp [arrays]))] using h.source.inData

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0)
    (i:ℕ) (hi:i< k+1+2*n) (hk:k≤ M) (hB:2*M^2+3 < B) (hcount:k+1+2*n+2 < B)
    (hun:(delta/(k:ℚ≥0)).num≤ M) (hud:(delta/(k:ℚ≥0)).den≤ M)
    (hdn:delta.num≤ M) (hdd:delta.den≤ M)
    (hon:∀ v, (outDistance v).num≤ M) (hod:∀ v, (outDistance v).den≤ M)
    (hin:∀ v, (inDistance v).num≤ M) (hid:∀ v, (inDistance v).den≤ M):
    Spec B (fun σ => Context outDistance inDistance k delta σ∧ σ.vars "radius.i"=i)
      command (fun _ τ => Context outDistance inDistance k delta τ∧
        FractionOutput (((RadiusData.candidates outDistance inDistance k delta)[i]'(by rw [RadiusData.length_candidates]; exact hi):ℚ≥0):ℚ) τ)
      (36*(M^2).size+100):=by
  have hM1:1≤ M:=(delta/(k:ℚ≥0)).den_pos.trans_le hud
  have hiB:i< B:=by omega
  have hnB:n< B:=by omega
  have hgB:k+1< B:=by omega
  rintro σ ⟨hctx,hidx⟩
  have hc:(Cond.lt (.var "radius.i") (.var "radius.gridCount")).evalB B σ=some (decide (i< k+1)):=by
    rw [evalB_condLt (evalB_var (hidx ▸ hiB)) (evalB_var (hctx.gridCount ▸ hgB)),hidx,hctx.gridCount]
  by_cases hg:i< k+1
  · obtain ⟨τ,rg,pg⟩:=RamGridRadius.command_spec B M i (delta/(k:ℚ≥0)) hB hun hud (by omega) σ ⟨hctx.source.unitData,hidx⟩
    have rr:=Run.ite_true (d:=vertex) (by simpa only [hg,decide_true] using hc) rg
    refine ⟨τ,rr.mono ?_,frame rg hctx (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
    · have hsize:(delta/(k:ℚ≥0)).den.size≤ (M^2).size:=Nat.size_le_size (by nlinarith [hud])
      dsimp only [Cond.size,Expr.size]; omega
    · simpa only [RadiusLookup.grid_at outDistance inDistance k delta i hg] using pg
  · let j:=i-(k+1)
    let ν:=σ.setVar "radius.v" j
    have rj:Run B (.assign "radius.v" (.sub (.var "radius.i") (.var "radius.gridCount"))) σ ν 4:=
      Run.assign (evalB_bin (op:=.sub) (m:=i) (n:=k+1)
        (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ hiB⟩)
        (by rw [evalB_var_iff]; exact ⟨hctx.gridCount.symm,hctx.gridCount ▸ hgB⟩) (by dsimp [Bop.apply]; omega))
    have hctxν:=frame rj hctx (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have hj:j<2*n:=by dsimp [j]; omega
    have hjB:j< B:=by omega
    have hv:ν.vars "radius.v"=j:=by simp [ν]
    have hcv:(Cond.lt (.var "radius.v") (.var "metric.n")).evalB B ν=some (decide (j< n)):=by
      rw [evalB_condLt (evalB_var (hv ▸ hjB)) (evalB_var (hctxν.source.nValue ▸ hnB)),hv,hctxν.source.nValue]
    by_cases ho:j< n
    · let v:Fin n:= ⟨j,ho⟩
      obtain ⟨τ,re,pe⟩:=RamEventRadius.command_spec B M true outDistance delta v hB (by omega) hdn hdd (hon v) (hod v) ν
        ⟨hctxν.source.deltaData,hctxν.source.outData,hv⟩
      have rv:=rj.seq (Run.ite_true (d:=.seq (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) (RamEventRadius.command false)) (by simpa only [ho,decide_true] using hcv) re)
      have rr:=Run.ite_false (c:=RamGridRadius.command) (by simpa only [hg,decide_false] using hc) rv
      refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),frame re hctxν (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
      have he:i=k+1+v.val:=by dsimp [v,j]; omega
      simpa only [he,RadiusLookup.out_at] using pe
    · let v:Fin n:= ⟨j-n,by omega⟩
      let μ:=ν.setVar "radius.v" v.val
      have rshift:Run B (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) ν μ 4:=
        Run.assign (evalB_bin (op:=.sub) (m:=j) (n:=n)
          (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ hjB⟩)
          (by rw [evalB_var_iff]; exact ⟨hctxν.source.nValue.symm,hctxν.source.nValue ▸ hnB⟩) (by dsimp [Bop.apply]; omega))
      have hctxμ:=frame rshift hctxν (by dsimp [names]; decide) (by dsimp [arrays]; decide)
      obtain ⟨τ,re,pe⟩:=RamEventRadius.command_spec B M false inDistance delta v hB (by omega) hdn hdd (hin v) (hid v) μ
        ⟨hctxμ.source.deltaData,hctxμ.source.inData,by simp [μ]⟩
      have rv:=rj.seq (Run.ite_false (c:=RamEventRadius.command true) (by simpa only [ho,decide_false] using hcv) (rshift.seq re))
      have rr:=Run.ite_false (c:=RamGridRadius.command) (by simpa only [hg,decide_false] using hc) rv
      refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),frame re hctxμ (by dsimp [names]; decide) (by dsimp [arrays]; decide),?_⟩
      have he:i=k+1+n+v.val:=by dsimp [v,j]; omega
      simpa only [he,RadiusLookup.in_at] using pe

end Lax455465Proofs.RamRadiusCoefficient

end

section

namespace Lax455465Proofs.RamRadiusCandidates

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational RamRadiusCoefficient
open scoped NNRat

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0)
    (hk:k≤ M) (hB:2*M^2+3 < B) (hindex:2*(k+1+2*n)+2 < B)
    (hun:(delta/(k:ℚ≥0)).num≤ M) (hud:(delta/(k:ℚ≥0)).den≤ M)
    (hdn:delta.num≤ M) (hdd:delta.den≤ M)
    (hon:∀ v, (outDistance v).num≤ M) (hod:∀ v, (outDistance v).den≤ M)
    (hin:∀ v, (inDistance v).num≤ M) (hid:∀ v, (inDistance v).den≤ M):
    Spec B (fun σ => Source outDistance inDistance k delta σ∧
      2*(k+1+2*n) < (σ.arrs "region.radii").length) command
      (fun _ τ => Context outDistance inDistance k delta τ∧
        Prefix (RamUnsignedBuffer.encode (RadiusData.candidates outDistance inDistance k delta)) "region.radii" τ)
      ((36*(M^2).size+122)*(k+1+2*n)+18):=by
  have hM1:1≤ M:=(delta/(k:ℚ≥0)).den_pos.trans_le hud
  have h2:2< B:=by nlinarith
  have hnB:n< B:=by omega
  have hkB:k< B:=by omega
  have hgB:k+1< B:=by omega
  have htB:k+1+2*n< B:=by omega
  have hmB:M*M< B:=by nlinarith
  let qs:=RadiusData.candidates outDistance inDistance k delta
  have hlen:qs.length=k+1+2*n:=RadiusData.length_candidates _ _ _ _
  have hheight:∀ q∈ qs,LpInputSize.Height (M*M) (q:ℚ):=by
    apply RadiusData.height outDistance inDistance k M delta hM1 hk
    · exact ⟨by simpa only [NNRat.natAbs_num_coe] using hun,by simpa only [NNRat.den_coe] using hud⟩
    · exact ⟨by simpa only [NNRat.natAbs_num_coe] using hdn,by simpa only [NNRat.den_coe] using hdd⟩
    · intro v; exact ⟨by simpa only [NNRat.natAbs_num_coe] using hon v,by simpa only [NNRat.den_coe] using hod v⟩
    · intro v; exact ⟨by simpa only [NNRat.natAbs_num_coe] using hin v,by simpa only [NNRat.den_coe] using hid v⟩
  have hwords:∀ i, ∀ hi:i< qs.length,qs[i].num< B∧ qs[i].den< B:=by
    intro i hi
    have hh:=hheight qs[i] (List.getElem_mem hi)
    exact ⟨(show qs[i].num≤ M*M by simpa only [NNRat.natAbs_num_coe] using hh.1).trans_lt hmB,
      (show qs[i].den≤ M*M by simpa only [NNRat.den_coe] using hh.2).trans_lt hmB⟩
  have hf:=RamUnsignedVector.command_spec B (36*(M^2).size+100) (Context outDistance inDistance k delta)
    "radius.i" "radius.count" "region.radii" "radius.position" qs [] RamRadiusCoefficient.command (by omega)
    (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hwords i hi).1) (fun i hi => (hwords i hi).2)
    (fun _ h => by simpa only [hlen] using h.count)
    (fun σ j h => by
      refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
      all_goals simpa only [Source,Context,Stored,Prefix,vars_setVar,arrs_setVar,String.reduceAppend,String.reduceEq,if_false] using
        (by first | exact h.source.nValue | exact h.source.kValue | exact h.source.deltaData | exact h.source.unitData | exact h.source.outData | exact h.source.inData | exact h.gridCount | exact h.count))
    (fun i hi => RamRadiusCoefficient.command_spec B M outDistance inDistance k delta i (by rwa [hlen] at hi) hk hB (by omega) hun hud hdn hdd hon hod hin hid)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by dsimp [names]; decide) (by dsimp [arrays]; decide)) (by decide) (by decide)
  rintro σ ⟨hsource,hroom⟩
  let σ₁:=σ.setVar "radius.gridCount" (k+1)
  let σ₂:=σ₁.setVar "radius.count" (k+1+2*n)
  let ν:=σ₂.setVar "radius.position" 0
  have rgrid:Run B (.assign "radius.gridCount" (.add (.var "round.steps") (.lit 1))) σ σ₁ 4:=
    Run.assign (evalB_bin (op:=.add) (m:=k) (n:=1)
      (by rw [evalB_var_iff]; exact ⟨hsource.kValue.symm,hsource.kValue ▸ hkB⟩) (evalB_lit (by omega)) (by dsimp [Bop.apply]; omega))
  have rnσ₁:σ₁.vars "metric.n"=n:=by simpa only [σ₁,vars_setVar,String.reduceEq,if_false] using hsource.nValue
  have rcount:Run B (.assign "radius.count" (.add (.var "radius.gridCount") (.mul (.lit 2) (.var "metric.n")))) σ₁ σ₂ 6:=
    Run.assign (evalB_bin (op:=.add) (m:=k+1) (n:=2*n)
      (by rw [evalB_var_iff]; exact ⟨by simp [σ₁],by simpa only [σ₁,vars_setVar,if_true] using hgB⟩)
      (evalB_bin (op:=.mul) (m:=2) (n:=n) (evalB_lit h2)
        (by rw [evalB_var_iff]; exact ⟨rnσ₁.symm,rnσ₁ ▸ hnB⟩) (by dsimp [Bop.apply]; omega)) (by dsimp [Bop.apply]; exact htB))
  have rpos:Run B (.assign "radius.position" (.lit 0)) σ₂ ν 2:=Run.assign (evalB_lit (by omega))
  have hctxν:Context outDistance inDistance k delta ν:=by
    refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
    · simpa only [ν,σ₂,σ₁,vars_setVar,String.reduceEq,if_false] using hsource.nValue
    · simpa only [ν,σ₂,σ₁,vars_setVar,String.reduceEq,if_false] using hsource.kValue
    · simpa only [Stored,ν,σ₂,σ₁,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hsource.deltaData
    · simpa only [Stored,ν,σ₂,σ₁,vars_setVar,String.reduceAppend,String.reduceEq,if_false] using hsource.unitData
    · simpa only [Prefix,ν,σ₂,σ₁,arrs_setVar] using hsource.outData
    · simpa only [Prefix,ν,σ₂,σ₁,arrs_setVar] using hsource.inData
    · simp [ν,σ₂,σ₁]
    · simp [ν,σ₂]
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,σ₂,σ₁,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,((rgrid.seq (rcount.seq rpos)).seq rr).mono (by simp only [hlen,Nat.add_assoc,Nat.reduceAdd]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamRadiusCandidates

end

section

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionSetup
open RegionQueryData Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def names:List String:= ["metric.n","metric.n2","region.root","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d"]
def arrays:List String:= ["region.weights","region.capacities","metric.old"]

theorem frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {weights:Fin n→ ℚ≥0} {capacity length:MetricMatrix.Matrix n} {root:Fin n}
    {seed beta delta:ℚ≥0} {k:ℕ} (h:Input weights capacity length root seed beta delta k σ)
    (hx:∀ x∈ names,x∉cmd.wvars) (ha:∀ a∈ arrays,a∉cmd.warrs):
    Input weights capacity length root seed beta delta k τ:=by
  refine ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.rootValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · exact RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names]))
  · simpa only [Prefix,rr.frame_arr "region.weights" (ha _ (by simp [arrays]))] using h.weightsData
  · simpa only [Prefix,rr.frame_arr "region.capacities" (ha _ (by simp [arrays]))] using h.capacityData
  · simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData

theorem Room.frame {B K n count:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    (h:Room n count σ):Room n count τ:=by
  exact ⟨by rw [RamFrames.run_array_length rr "region.out"]; exact h.outRoom,
    by rw [RamFrames.run_array_length rr "region.in"]; exact h.inRoom,
    by rw [RamFrames.run_array_length rr "region.radii"]; exact h.radiusRoom,
    by rw [RamFrames.run_array_length rr "region.outMask"]; exact h.outMaskRoom,
    by rw [RamFrames.run_array_length rr "region.inMask"]; exact h.inMaskRoom,
    by rw [RamFrames.run_array_length rr "region.crossing"]; exact h.crossingRoom⟩

set_option maxHeartbeats 0 in

theorem command_spec (B M H:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0)
    (capacity length:MetricMatrix.Matrix n) (root:Fin n) (seed beta delta:ℚ≥0) (k:ℕ)
    (hk:k≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(k+1+2*n)+2< B)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ)) (hu:LpInputSize.Height M ((delta/(k:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ i, ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) k delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) k delta)[i]) H):
    Spec B (fun σ => Input weights capacity length root seed beta delta k σ∧ Room n (k+1+2*n) σ)
      command (fun _ τ => RamRadiusSearch.Context (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) k delta) τ∧
        RamFind.Matches (RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta)
          (RadiusData.candidates (length root) (fun v => length v root) k delta)) (k+1+2*n)) τ∧
        RamSelectedRegion.Selected (query weights capacity length root seed beta)
          (RadiusData.candidates (length root) (fun v => length v root) k delta) τ)
      (cost n k M H):=by
  have hMB:M< B:=by nlinarith
  let q:=query weights capacity length root seed beta
  let radii:=RadiusData.candidates (length root) (fun v => length v root) k delta
  have hlen:radii.length=k+1+2*n:=RadiusData.length_candidates _ _ _ _
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩:=RamRootDistances.command_spec B M true root length hMB (by omega) (by omega) hindex
    (fun u v => RamRegionContext.num_bound (hl u v)) (fun u v => RamRegionContext.den_bound (hl u v)) σ
    ⟨⟨hσ.nValue,hσ.rootValue,hσ.lengthData⟩,hroom.outRoom⟩
  have h1:=frame r1 hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room1:=Room.frame r1 hroom
  obtain ⟨σ2,r2,p2⟩:=RamRootDistances.command_spec B M false root length hMB (by omega) (by omega) hindex
    (fun u v => RamRegionContext.num_bound (hl u v)) (fun u v => RamRegionContext.den_bound (hl u v)) σ1
    ⟨⟨h1.nValue,h1.rootValue,h1.lengthData⟩,room1.inRoom⟩
  have h2:=frame r2 h1 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room2:=Room.frame r2 room1
  have hout2:Prefix (RamUnsignedBuffer.encode (List.ofFn (length root))) "region.out" σ2:=by
    simpa only [RamRootDistances.vector,RamRootDistances.array,if_true,Prefix,r2.frame_arr "region.out" (by decide)] using p1.2
  obtain ⟨σ3,r3,p3⟩:=RamRadiusCandidates.command_spec B M (length root) (fun v => length v root) k delta hk hB hradius
    (RamRegionContext.num_bound hu) (RamRegionContext.den_bound hu)
    (RamRegionContext.num_bound hd) (RamRegionContext.den_bound hd)
    (fun v => RamRegionContext.num_bound (hl root v)) (fun v => RamRegionContext.den_bound (hl root v))
    (fun v => RamRegionContext.num_bound (hl v root)) (fun v => RamRegionContext.den_bound (hl v root)) σ2
    ⟨⟨h2.nValue,h2.stepsValue,h2.deltaData,h2.unitData,hout2,
      by simpa only [RamRootDistances.vector,RamRootDistances.array,Bool.false_eq_true,if_false] using p2.2⟩,room2.radiusRoom⟩
  have h3:=frame r3 h2 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room3:=Room.frame r3 room2
  let σ4:=((σ3.setVar "find.count" (k+1+2*n)).setVar "region.radius.n" 0).setVar "region.radius.d" 1
  have r4:Run B setup σ3 σ4 6:=
    (Run.assign (by rw [evalB_var_iff]; exact ⟨p3.1.count.symm,p3.1.count ▸ (by omega:k+1+2*n< B)⟩)).seq
      ((Run.assign (evalB_lit (by omega))).seq (Run.assign (evalB_lit (by omega))))
  have h4:=frame r4 h3 (by dsimp [names]; decide) (by dsimp [arrays]; decide)
  have room4:=Room.frame r4 room3
  have hctx:RamRadiusSearch.Context q radii σ4:=by
    refine ⟨⟨0,?_⟩,?_,by simp [σ4,hlen],room4.outMaskRoom,room4.inMaskRoom,room4.crossingRoom⟩
    · refine ⟨h4.nValue,h4.n2Value,by simp [RamUnsignedScalar.Stored,RadiusSearchData.atRadius,σ4],
        h4.seedData,h4.betaData,h4.weightsData,h4.capacityData,h4.lengthData,?_,?_⟩
      · have rr:=r3.seq r4
        simpa only [q,query,RadiusSearchData.atRadius,Prefix,rr.frame_arr "region.out" (by decide)] using hout2
      · have rr:=r3.seq r4
        simpa only [q,query,RadiusSearchData.atRadius,RamRootDistances.vector,RamRootDistances.array,Bool.false_eq_true,if_false,
          Prefix,rr.frame_arr "region.in" (by decide)] using p2.2
    · simpa only [radii,Prefix,r4.frame_arr "region.radii" (by decide)] using p3.2
  obtain ⟨τ,r5,p5⟩:=RamSelectedRegion.command_spec B H q radii hb hquery hindex hvertex (by rwa [hlen]) σ4 hctx
  have rr:=r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono (by simp only [hlen,cost]; ring_nf; omega),p5.1,?_,p5.2.2⟩
  simpa only [hlen] using p5.2.1

end Lax455465Proofs.RamRegionSetup

end

theorem solution:∀ (B M H:Nat) {n:Nat} (weights:Fin n→ NNRat) (capacity length:Lax455465Proofs.MetricMatrix.Matrix n)
  (root:Fin n) (seed beta delta:NNRat) (k:Nat),
  Nat.le k M→
    Nat.lt
        (Nat.add
          (Nat.mul ((2:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              ((2:Nat))))
          ((3:Nat)))
        B→
      Nat.lt
          (Nat.add
            (Nat.mul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) H)
                ((2:Nat))))
            ((3:Nat)))
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
            Nat.lt
                (Nat.add
                  (Nat.mul
                    ((2:Nat))
                    (Nat.add
                      (Nat.add k
                        ((1:Nat)))
                      (Nat.mul
                        ((2:Nat)) n)))
                  ((2:Nat)))
                B→
              (∀ (u v:Fin n),Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v)))→
                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta)→
                  Lax455465Proofs.LpInputSize.Height M
                      (@NNRat.cast Rat Rat.instNNRatCast
                        (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                          (@Nat.cast NNRat
                            (@AddMonoidWithOne.toNatCast NNRat
                              (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                  (@Semiring.toNonAssocSemiring NNRat
                                    (@DivisionSemiring.toSemiring NNRat
                                      (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                            k)))→
                    (∀ (i:Nat)
                        (hi:
                          Nat.lt i
                            (@List.length NNRat
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v:Fin n) => length v root)
                                k delta))),
                        @Lax455465Proofs.RegionQueryHeight.Bounds n
                          (@Lax455465Proofs.RadiusSearchData.atRadius n
                            (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                            (@GetElem.getElem (List NNRat) Nat NNRat
                              (fun (as:List NNRat) (i:Nat) => Nat.lt i (@List.length NNRat as))
                              (@List.instGetElemNatLtLength NNRat)
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v:Fin n) => length v root)
                                k delta)
                              i hi))
                          H)→
                      Lax808846Proofs.Reasoning.Spec B
                        (fun (σ:Lax808846Proofs.Imp.Env) =>
                          And (@Lax455465Proofs.RamRegionSetup.Input n weights capacity length root seed beta delta k σ)
                            (Lax455465Proofs.RamRegionSetup.Room n
                              (Nat.add
                                (Nat.add k
                                  ((1:Nat)))
                                (Nat.mul
                                  ((2:Nat)) n))
                              σ))
                        Lax455465Proofs.RamRegionSetup.command
                        (fun (x τ:Lax808846Proofs.Imp.Env) =>
                          And
                            (@Lax455465Proofs.RamRadiusSearch.Context n
                              (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                              (@Lax455465Proofs.RadiusData.candidates n (length root) (fun (v:Fin n) => length v root)
                                k delta)
                              τ)
                            (And
                              (Lax455465Proofs.RamFind.Matches
                                (Lax455465Proofs.RamFind.first
                                  (@Lax455465Proofs.RadiusSearchData.predicate n
                                    (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                                    (@Lax455465Proofs.RadiusData.candidates n (length root)
                                      (fun (v:Fin n) => length v root) k delta))
                                  (Nat.add
                                    (Nat.add k
                                      ((1:Nat)))
                                    (Nat.mul
                                      ((2:Nat)) n)))
                                τ)
                              (@Lax455465Proofs.RamSelectedRegion.Selected n
                                (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                                (@Lax455465Proofs.RadiusData.candidates n (length root)
                                  (fun (v:Fin n) => length v root) k delta)
                                τ)))
                        (Lax455465Proofs.RamRegionSetup.cost n k M H):= @Lax455465Proofs.RamRegionSetup.command_spec
